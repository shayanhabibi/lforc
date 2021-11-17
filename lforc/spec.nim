import wtbanland/atomics

const
  maxThreads*: int = 256
  maxHps*: int = 64
  unmarkMask: uint = high(uint) xor uint(3)

type
  OrcConstants = object
    maxThreads: int
    maxHps: int
    orcSeq: uint
    bretired: uint
    orcZero: uint
    orcCntMask: uint
    orcSeqMask: uint
    maxRetCnt: int

proc initOrcConstants: OrcConstants =
  result = OrcConstants(
    maxThreads: maxThreads,
    maxHps: maxHps,
    orcSeq: uint(1 shl 24),
    bretired: uint(1 shl 23),
    orcZero: uint(1 shl 22),
    maxRetCnt: 1000
  )
  result.orcCntMask = result.orcSeq - 1
  result.orcSeqMask = high(uint) xor result.orcCntMask

const ogc* = initOrcConstants()

template oseq*(x: uint): uint = ogc.orcSeqMask and x
template ocnt*(x: uint): uint = ogc.orcCntMask and x
template hasBitRetire*(x: uint): uint = ogc.bretired and x
template isCounterZero*(x: uint): bool =
  let nretired = high(uint) xor ogc.bretired
  (x and nretired and ogc.orcCntMask) == ogc.orcZero
template getUnmarked*(x: untyped): untyped =
  cast[typeof(x)](cast[uint](x) and unmarkMask)

type
  HpList*[T] = array[ogc.maxThreads, array[ogc.maxHps, Atomic[T]]]
  HandOvers*[T] = array[ogc.maxThreads, array[ogc.maxHps, Atomic[T]]]

  OrcHead = object
    orc: Atomic[uint]

  OrcBase[T] = object
    orc: Atomic[uint]
    obj: T

  OrcAtomic*[T] {.borrow.} = distinct Atomic[T]
  OrcPtr*[T] {.borrow.} = distinct ptr T

  TLInfo* = object
    usedHaz: array[ogc.maxHps, int]
    retireStarted: bool
    retCnt: int
    recursiveList: seq[ptr OrcHead]

  PTPOrcGc = object
    inDestructor: bool
    hp: HpList[ptr OrcHead]
    handOvers: HandOvers[ptr OrcHead]
    maxHps: Atomic[int]
    tl: array[ogc.maxThreads, TLInfo]

var tid {.threadvar.}: int

proc initPTPOrcGc: auto =
  result = PTPOrcGC()

proc destroy(porc: var PTPOrcGc) =
  porc.inDestructor = true
  var maxHps = porc.maxHps.load(moAcq)
  for it in 0..<ogc.maxThreads:
    for ihp in 0..<maxHps:
      var obj: ptr OrcHead = porc.handOvers[it][ihp].load(moRlx)
      if not obj.isNil:
        var lorc: uint = obj[].orc.load(moRlx)
        porc.handOvers[it][ihp].store(nil, moRlx)
        # retire(obj, tid) # FIXME

proc addRetCnt(porc: var PTPOrcGc; tid: int): int {.inline.} =
  inc porc.tl[tid].retCnt
  porc.tl[tid].retCnt

proc resetRetCnt(porc: var PTPOrcGc; tid: int) {.inline.} =
  porc.tl[tid].retCnt = 0

proc getNewIdx(porc: var PTPOrcGc; tid: int, start: int = 1): int =
  var idx = start
  block loop:
    while idx < ogc.maxHps:
      inc idx
      if not porc.tl[tid].usedHaz[idx] != 0:
        inc porc.tl[tid].usedHaz[idx]
        var curMax = porc.maxHps.load(moRlx)
        while curMax <= idx:
          discard porc.maxHps.compareExchange(curMax, idx + 1)
        result = idx
        break loop
    raise newException(ValueError, "ERROR: maxHps is not enough for all the hazard pointers in the algorithm")

proc usingIdx(porc: var PTPOrcGc; tid: int, idx: int) =
  if not idx == 0:
    inc porc.tl[tid].usedHaz[idx]

proc cleanIdx(porc: var PTPOrcGc; tid: int; idx: int): int =
  if idx == 0:
    -1
  else:
    dec porc.tl[tid].usedHaz[idx]
    porc.tl[tid].usedHaz[idx]

proc clear[T](porc: var PTPOrcGc; iptr: T, idx: int, tid: int, linked: bool, reuse: bool) =
  if not reuse and cleanIdx(tid, idx) != 0:
    discard
  elif linked:
    discard
  elif not iptr.isNil:
    # iptr = getUnmarked(iptr) # FIXME
    var lorc: uint = iptr[].orc.load(moAcq)
    if ocnt(lorc) == ogc.orcZero:
      if iptr[].orc.compareExchange(lorc, lorc + ogc.bretired):
        # retire(iptr, tid) # FIXME
        discard

proc getUsedHaz(porc: var PTPOrcGc; tid: int; idx: int): int {.inline.} =
  porc.tl[tid].usedHaz[idx]

proc getProtected[T](porc: var PTPOrcGc; tid: int; index: int; adr: ptr Atomic[T]): T =
  var pub, iptr: T = nil
  while (pub = adr[].load(moRlx); pub) != iptr:
    discard
    # porc.hp[tid][index].store(getUnmarked(pub)) # FIXME
  result = pub

proc protectPtr(porc: var PTPOrcGc; iptr: ptr OrcHead, tid: int, idx: int) =
  porc.hp[tid][idx].store(getUnmarked(iptr), moRel)

# proc initGlobalHpList*(maxThreads, maxHps: static Natural): auto =
#   result = nucleate(GlobalHpList[maxThreads, maxHps])

# proc initGlobalHandOvers*(maxThreads, maxHps: static Natural): auto =
#   result = nucleate(GlobalHandOvers[maxThreads, maxHps])  

# var globalHpList* {.global.}: GlobalHpList[maxThreads, maxHps]
# var globalHandOvers* {.global.}: GlobalHandOvers[maxThreads, maxHps]
# var globalPtp* {.global.}: PassThePointerOrcGc[maxThreads, maxHps]

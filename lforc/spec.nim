import wtbanland/atomics
import lforc/thrregistry

const
  maxThreads*: int = 256
  maxHps*: int = 64

  unmarkMask: uint = high(uint) xor uint(3)
  orcSeq: = (1 shl 24).uint
  bretired: (1 shl 23).uint
  orcZero: (1 shl 22).uint
  orcCntMask: orcSeq - 1
  orcSeqMask: high(uint) xor orcCntMask
  maxRetCnt:

template oseq*(x: uint): uint = orcSeqMask and x
template ocnt*(x: uint): uint = orcCntMask and x
template hasBitRetire*(x: uint): uint = bretired and x
template isCounterZero*(x: uint): bool =
  let nretired = high(uint) xor bretired
  (x and nretired and orcCntMask) == orcZero
template getUnmarked*(x: untyped): untyped =
  cast[typeof(x)](cast[uint](x) and unmarkMask)

type
  HpList*[T] = array[maxThreads, array[maxHps, Atomic[T]]]
  HandOvers*[T] = array[maxThreads, array[maxHps, Atomic[T]]]

  OrcHead = object
    orc: Atomic[uint]

  OrcBase[T] = object
    orc: Atomic[uint]
    obj: T

  OrcAtomic*[T] {.borrow.} = distinct Atomic[T]
  OrcPtr*[T] {.borrow.} = distinct ptr T

  TLInfo* = object
    usedHaz: array[maxHps, int]
    retireStarted: bool
    retCnt: int
    recursiveList: seq[ptr OrcHead]

  PTPOrcGc = object
    inDestructor: bool
    hp: HpList[ptr OrcHead]
    handOvers: HandOvers[ptr OrcHead]
    maxHps: Atomic[int]
    tl: array[maxThreads, TLInfo]

proc initPTPOrcGc: auto =
  result = PTPOrcGC()

template getHeader[T](objPtr: ptr T): ptr OrcHead =
  let backAlign = cast[uint](objPtr) - 8
  cast[ptr OrcHead](backAlign)

template getOrcPtr[T](userPtr: ptr T): ptr OrcBase[T] =
  cast[ptr OrcBase[T]](getHeader userPtr)

template getUserPtr[T](orcPtr: ptr OrcHead | ptr OrcBase[T]): ptr T =
  let alignPtr = cast[uint](orcPtr) + 8
  result = cast[ptr T](alignPtr)

converter toOPtr[T](orcBasePtr: ptr OrcBase[T]): ptr OrcHead = cast[ptr OrcHead](orcBasePtr)
converter toOBasePtr[T](orcPtr: ptr OrcBase): ptr OrcBase[T] = cast[ptr OrcBase[T]](orcPtr)
# converter toUserPtr[T](orcBasePtr: ptr OrcBase[T]): ptr T = orcBasePtr.getUserPtr()

proc createSharedOrc*[T](tipe: typedesc[T], size: Natural): ptr T =
  ## Principal: Allocate shared block with 8 byte header for metadata
  # Issue with this is that sizeof will not correctly indicate the size of the object
  # this also plays issues if the object the person has created is supposed to be
  # cache lined since they will be unaware that the object is not ipsilateral
  let orcPtr = createShared(OrcBase[T])
  result = orcPtr.getUserPtr
  

proc destroy(porc: var PTPOrcGc) =
  porc.inDestructor = true
  var maxHps = porc.maxHps.load(moAcq)
  for it in 0..<maxThreads:
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
    while idx < maxHps:
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
    if ocnt(lorc) == orcZero:
      if iptr[].orc.compareExchange(lorc, lorc + bretired):
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

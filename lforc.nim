import lforc/thrregistry
import lforc/spec
import lforc/ptp
import wtbanland/atomics

## Contains the PTPOrcGC Object and procedures


type
  TLInfo = object
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

var gorc* {.global.}: PTPOrcGc

proc initPTPOrcGc =
  initThreadRegistry()
  gorc = PTPOrcGC()

initPTPOrcGc()

proc createSharedOrc*[T](tipe: typedesc[T], size: Natural): ptr T =
  ## Principal: Allocate shared block with 8 byte header for metadata
  # Issue with this is that sizeof will not correctly indicate the size of the object
  # this also plays issues if the object the person has created is supposed to be
  # cache lined since they will be unaware that the object is not ipsilateral
  let orcPtr = createShared(OrcBase[T])
  result = orcPtr.getUserPtr
  
proc allocateSharedOrc*(size: Natural): pointer =
  let aptr = cast[uint](allocShared(sizeof(size + 8))) + 8'u
  result = cast[pointer](aptr)

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

proc tearDownOrcGc =
  destroy(gorc)


# In terms of optimisation, objects will contain the thread ids themselves
# and may use that instead of fetching the value. Benchmark?
proc addRetCnt(tid: int = tid): int {.inline.} =
  inc gorc.tl[tid].retCnt
  gorc.tl[tid].retCnt

proc resetRetCnt(tid: int = tid) {.inline.} =
  gorc.tl[tid].retCnt = 0

proc getNewIdx(start: int = 1; tid: int = tid): int =
  var idx = start
  block loop:
    while idx < maxHps:
      inc idx
      if not gorc.tl[tid].usedHaz[idx] != 0:
        inc gorc.tl[tid].usedHaz[idx]
        var curMax = gorc.maxHps.load(moRlx)
        while curMax <= idx:
          discard gorc.maxHps.compareExchange(curMax, idx + 1)
        result = idx
        break loop
    raise newException(ValueError, "ERROR: maxHps is not enough for all the hazard pointers in the algorithm")

proc usingIdx(idx: int, tid: int = tid) =
  if not idx == 0:
    inc gorc.tl[tid].usedHaz[idx]

proc cleanIdx(idx: int; tid: int = tid): int =
  if idx == 0:
    -1
  else:
    dec gorc.tl[tid].usedHaz[idx]
    gorc.tl[tid].usedHaz[idx]

proc clear[T](iptr: T, idx: int, tid: int, linked: bool, reuse: bool) =
  if not reuse and cleanIdx(idx, tid) != 0:
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

proc getUsedHaz(idx: int; tid: int = tid): int {.inline.} =
  gorc.tl[tid].usedHaz[idx]

proc getProtected[T](index: int; adr: ptr Atomic[T]; tid: int = tid): T =
  var pub, iptr: T = nil
  while (pub = adr[].load(moRlx); pub) != iptr:
    discard
    # porc.hp[tid][index].store(getUnmarked(pub)) # FIXME
  result = pub

proc protectPtr(iptr: ptr OrcHead, idx: int; tid: int = tid) =
  gorc.hp[tid][idx].store(getUnmarked(iptr), moRel)

proc initOrcPtr[T](pntr: T, tid: int16, idx: int8, linked: bool): OrcPtr[T] =
  OrcPtr[T](pntr, tid, idx, linked)

proc initOrcPtr(porc: var PTPOrcGc): OrcPtr[pointer] =
  result = OrcPtr[pointer](tid: cast[int16](tid))
  result.idx = cast[int8](getNewIdx result.tid)
import lforc/threadreg
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
  OrcPtr*[T] = object
    pntr*: T
    tid*:  int16
    idx*: int8
    lnk*: bool

  OrcUnsafePtr*[T] = object
    pntr*: T

  OrcAtomic*[T] {.borrow.} = distinct Atomic[T]

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
proc addRetCnt(tid: int): int {.inline.} =
  inc gorc.tl[tid].retCnt
  gorc.tl[tid].retCnt

proc resetRetCnt(tid: int) {.inline.} =
  gorc.tl[tid].retCnt = 0

proc getNewIdx(tid: int; start: int = 1): int =
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

proc usingIdx(idx: int; tid: int) =
  if not idx == 0:
    inc gorc.tl[tid].usedHaz[idx]

proc cleanIdx(tid: int; idx: int): int =
  if idx == 0:
    -1
  else:
    dec gorc.tl[tid].usedHaz[idx]
    gorc.tl[tid].usedHaz[idx]

proc clear[T](iptr: T, idx: int, tid: int, linked: bool, reuse: bool) =
  if not reuse and cleanIdx(tid=tid, idx=idx) != 0:
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

proc getUsedHaz(idx: int; tid: int): int {.inline.} =
  gorc.tl[tid].usedHaz[idx]

proc getProtected[T](tid: int; index: int; adr: ptr Atomic[T]): T =
  var pub, iptr: T = nil
  while (pub = adr[].load(moRlx); pub) != iptr:
    discard
    # porc.hp[tid][index].store(getUnmarked(pub)) # FIXME
  result = pub

proc protectPtr(iptr: ptr OrcHead; tid: int; idx: int) =
  gorc.hp[tid][idx].store(getUnmarked(iptr), moRel)

proc initOrcPtr[T](pntr: T, tid: int16, idx: int8, linked: bool): OrcPtr[T] =
  OrcPtr[T](pntr, tid, idx, linked)

proc initOrcPtr(porc: var PTPOrcGc): OrcPtr[pointer] =
  result = OrcPtr[pointer](tid: cast[int16](getTid))
  result.idx = cast[int8](getNewIdx result.tid)

proc `==`[T](x, y: OrcPtr[T] | OrcUnsafePtr[T]): bool =
  x.pntr == y.pntr
proc `==`[T](x: OrcUnsafePtr[T] | OrcPtr[T], y: T): bool =
  x.pntr == y
proc `!=`[T](x, y: OrcPtr[T] | OrcUnsafePtr[T]): bool =
  x.pntr != y.pntr
proc `!=`[T](x: OrcUnsafePtr[T] | OrcPtr[T], y: T): bool =
  x.pntr != y
proc `[]`[T](x: OrcUnsafePtr[T] | OrcPtr[T]): T =
  x.pntr

proc copy[T](x: OrcPtr[T]): var OrcPtr[T] =
  result.tid = x.tid
  result.idx = x.idx
  result.pntr = x.pntr
  result.lnk = x.lnk
  if result.idx == 0:
    result.idx = getNewIdx(tid = result.tid)
    protectPtr(result.pntr, result.tid.int, result.idx.int)
  else:
    usingIdx(x.idx, x.tid)

proc copyMove[T](x: OrcPtr[T]): var OrcPtr[T] =
  result.tid = x.tid
  result.idx = x.idx
  result.pntr = x.pntr
  result.lnk = x.lnk
  if result.idx == 0:
    result.idx = getNewIdx(tid = result.tid)
    protectPtr(result.pntr, result.tid.int, result.idx.int)
  else:
    x.idx = 0

proc copy[T](x: OrcUnsafePtr[T]): var OrcPtr[T] =
  result.tid = getTid()
  result.idx = getNewIdx(result.tid)
  result.pntr = x.pntr
  result.lnk = true
  protectPtr(result.pntr, result.tid, result.idx)

proc `=`[T](x: var OrcPtr[T], y: OrcPtr[T]) =
  var reuseIdx: bool =
    y.idx < x.idx and
    getUsedHaz(x.idx, x.tid) == 1
  clear(x.pntr, x.idx, x.tid, x.lnk, reuseIdx)
  if y.idx < x.idx:
    if not reuseIdx:
      x.idx = getNewIdx(x.tid, y.idx + 1)
    protectPtr(y.pntr, x.tid, x.idx)
  else:
    usingIdx(y.idx, x.tid)
    x.idx = y.idx
  x.pntr = y.pntr
  x.lnk = y.lnk

proc `move=`[T](x: var OrcPtr[T], y: OrcPtr[T]) =
  ## Not sure what to do about this :/
  var reuseIdx: bool =
    y.idx < x.idx and
    getUsedHaz(x.idx, x.tid) == 1
  clear(x.pntr, x.idx, x.tid, x.lnk, reuseIdx)
  if y.idx < x.idx:
    if not reuseIdx:
      x.idx = getNewIdx(x.tid, y.idx + 1)
    protectPtr(y.pntr, x.tid, x.idx)
  else:
    x.idx = y.idx
    y.idx = 0
  x.pntr = y.pntr
  x.lnk = y.lnk

proc `move=`[T](x: var OrcPtr[T], y: OrcUnsafePtr[T]) =
  var reuseIdx: bool = getUsedHaz(x.idx, x.tid) == 1
  clear(x.pntr, x.idx, x.tid, x.lnk, reuseIdx)
  if not reuseIdx:
    x.idx = getNewIdx(x.tid)
  protectPtr(y.pntr, x.tid, x.idx)
  x.pntr = y.pntr
  x.lnk = true

proc incrementOrc(pntr: ptr OrcHead) =
  block:
    if pntr.isNil:
      break
    var lorc: uint = pntr[].orc.fetchAdd(1) + 1
    if ocnt(lorc) != orcZero:
      break
    if pntr[].orc.compareExchange(lorc, lorc + bretired):
      ## retire(pntr) # FIXME IMPL
      break

proc decrementOrc(pntr: ptr OrcHead) =
  block:
    if pntr.isNil:
      break
    let tid = getTid()
    protectPtr(pntr, tid, 0)
    var lorc: uint = pntr[].orc.fetchAdd(orcSeq-1) + orcSeq - 1
    if addRetCnt(tid) == maxRetCnt:
      # retireOne(tid) # FIXME IMPL
      resetRetCnt(tid)
    if ocnt(lorc) != orcZero:
      break
    if pntr[].orc.compareExchange(lorc, lorc + bretired):
      # retire(pntr, tid) # FIXME IMPL
      break

proc initOrcAtomic[T](val: T): OrcAtomic[T] =
  incrementOrc(val)
  result.store(val, moRlx)

proc `=destroy`[T](x: var OrcAtomic[T]) =
  block:
    var pntr = x.load(moRlx)
    if pntr.isNil:
      break
    decrementOrc(pntr)

proc `[]`[T](x: var OrcAtomic[T]): var T =
  x.load()

proc `[]=`[T](x: var OrcAtomic[T], y: T) =
  x.store(y)

proc `=`[T](x: var OrcAtomic[T]; y: OrcAtomic[T]) =
  x.store(y.load())

proc retire(pntr: var ptr OrcHead, tid: int = getTid()) =
  block retire:
    if pntr.isNil:
      break retire
    var rlist = gorc.tl[tid].recursiveList
    if gorc.tl[tid].retireStarted:
      rlist.add(pntr)
      break retire
    if not gorc.inDestructor:
      let lmaxHps = gorc.maxHps.load(moAcq)
      for i in 0..<lmaxHps:
        if gorc.hp[tid][i].load(moRlx) == pntr:
          pntr = gorc.handOvers[tid][i].exchange(pntr)
          break
    var i: int
    gorc.tl[tid].retireStarted = true
    while true:
      while not pntr.isNil:
        var lorc = pntr.orc.load()
        if not isCounterZero(lorc):
          if (lorc = clearBitRetired(pntr, tid); lorc) == 0:
            break
        if tryHandover(pntr):
          continue
import lforc/arith
import lforc/spec
import lforc/threadreg

# Define types
type
  OrcPointer {.borrow.} = distinct pointer
  OrcPtr[T] {.borrow.} = distinct ptr[T]

  SomeOrcPointer[T] = OrcPointer | OrcPtr[T]

converter toPointer*(x: OrcPointer): pointer = cast[pointer](x)
converter toPointer*[T](x: OrcPtr[T]): pointer = cast[pointer](x)
converter toOrcPointer*[T](x: OrcPtr[T]): OrcPointer = cast[OrcPointer](x)
converter toOrcPtr[T: typedesc](x: OrcPointer): OrcPtr[T] = cast[OrcPtr[T]](x)

template orc(x: SomeOrcPointer): ptr int =
  ## Access the orc counter of a OrcPointer
  cast[ptr int](cast[pointer](x) -% 8)

type
  TLInfo = object
    retireStarted: bool
    recursiveList: seq[OrcPointer]
    usedHaz: array[maxHps, int]
    retCnt: int
    pad: array[128, uint8]
  
  PTPOrcGc = object
    inDestructor: bool
    hp {.align: 128.}: array[maxThreads, array[maxHps, OrcPointer]]
    handovers {.align: 128.}: array[maxThreads, array[maxHps, OrcPointer]]
    maxHps {.align: 128.}: uint
    tl {.align: 128.}: array[maxThreads, TLInfo]

  LFOrc = ptr PTPOrcGc


proc initTLInfo(tli: var TLInfo) =
  tli.recursiveList = newSeqOfCap[OrcPointer](maxThreads * maxHps)

proc newLFOrc: LFOrc =
  result = createShared(PTPOrcGc)
  for i in 0..<maxThreads:
    result.tl[i].initTlInfo()
  
proc `=destroy`(x: var PTPOrcGc) =
  discard

var ogc {.global.} = newLFOrc()

proc addRetCnt(tid: int): int {.inline.} =
  inc ogc.tl[tid].retcnt
  ogc.tl[tid].retcnt

proc resetRetCnt(tid: int) {.inline.} =
  ogc.tl[tid].retcnt = 0

proc getNewIdx(tid: int; startIdx: int = 1): int =
  for idx in startIdx..<maxHps:
    if ogc.tl[tid].usedHaz[idx] != 0:
      continue
    inc ogc.tl[tid].usedHaz[idx]

    var curMax: uint = ogc.maxHps.load(Rlx)
    while curMax <= idx.uint:
      discard ogc.maxHps.compareExchange(curMax, (idx + 1).uint, Rlx)
    return idx

proc usingIdx(idx, tid: int) {.inline.} =
  if idx == 0:
    return
  inc ogc.tl[tid].usedHaz[idx]

proc cleanIdx(idx, tid: int): int {.inline.} =
  if idx == 0: return -1
  dec ogc.tl[tid].usedHaz[idx]
  ogc.tl[tid].usedHaz[idx]
    
template clear(pntr: SomeOrcPointer; idx: int; tid: int; linked, reuse: bool) =
  mixin load
  mixin compareExchange
  mixin retire
  block:
    if not reuse and cleanIdx(idx, tid) != 0:
      break
    if linked:
      break
    if not pntr.isNil():
      # pntr = getUnmarked pntr
      var lorc = pntr.orc[].load(Acq)
      if ocnt(lorc) == orcZero:
        if pntr.orc[].compareExchange(lorc, lorc + bretired, SeqCst):
          retire(pntr, tid)

proc getUsedHaz(idx, tid: int): int {.inline.} =
  ogc.tl[tid].usedHaz[idx]

template getProtected(idx: int, addy: typed, tid: int): typed = # REVIEW used in atomic_orc
  var pub, pntr: typeof(addy)
  while (pub = addy.load(SeqCst); pub != pntr):
    ogc.hp[tid][idx].store(getUnmarked(pub))
    pntr = pub
  pub

proc protectPtr(pntr: SomeOrcPointer; tid, idx: int) {.inline.} =
  ogc.hp[tid][idx].store(getUnmarked pntr, Rel)

proc clearBitRetired(pntr: SomeOrcPointer; tid: int): int =
  ogc.hp[tid][0].store(pntr, Rel)
  var lorc = pntr.orc[].fetchSub(bretired)
  if (ocnt(lorc) == orcZero) and pntr.orc[].compareExchange(lorc, int(lorc + bretired)):
    ogc.hp[tid][0].store(nil, Rlx)
    return lorc + bretired
  else:
    ogc.hp[tid][0].store(nil, Rlx)
    return 0

proc tryHandover(pntr: var SomeOrcPointer): bool {.inline.} =
  if ogc.inDestructor: return false
  let lmaxHps = ogc.maxHps.load(Acq)
  for tid in 0..<maxThreads:
    for idx in 0..<lmaxHps:
      if pntr == ogc.hp[tid][idx].load(Acq):
        pntr = ogc.handovers[tid][idx].exchange(pntr)
        return true

proc retire(pntr: var SomeOrcPointer; tid: int) =
  if pntr.isNil():
    return
  var rlist = ogc.tl[tid].recursiveList
  if ogc.tl[tid].retireStarted:
    rlist.add(pntr)
    return
  if not ogc.inDestructor:
    let lmaxHps = ogc.maxHps.load(Acq)
    for i in 0..<lmaxHps:
      if ogc.hp[tid][i].load(Rlx) == pntr:
        pntr = ogc.handovers[tid][i].exchange(pntr, SeqCst)
        break
  ogc.tl[tid].retireStarted = true
  var i: int
  while true:
    while not pntr.isNil():
      var lorc = pntr.orc[].load()
      if not isCounterZero(lorc):
        lorc = clearBitRetired(pntr, tid)
        if lorc == 0: break
      if tryHandover pntr:
        continue
      var lorc2 = pntr.orc[].load(Acq)
      if lorc2 != lorc:
        if not isCounterZero(lorc2):
          if clearBitRetired(pntr, tid) == 0:
            break
        continue
      deallocShared(pntr -% 8)
      break
    if rlist.len == i:
      break
    pntr = rlist[i]
    inc i
  doAssert i == rlist.len
  rlist = @[] # TODO clear seq
  ogc.tl[tid].retireStarted = false


proc retire(pntr: SomeOrcPointer) =
  let tid = getTid
  retire(pntr, tid)

proc retireOne(tid: int) = # REVIEW used in orc_atomic only
  let lmaxHps = ogc.maxHps.load(Acq)
  for idx in 0..<lmaxHps:
    var obj = ogc.handovers[tid][idx].load(Rlx)
    if not obj.isNil() and obj != ogc.hp[tid][idx].load(Rlx):
      obj = ogc.handovers[tid][idx].exchange(nil)
      retire(obj, tid)
      return
  for id in 0..<maxThreads:
    if id == tid: continue
    for idx in 0..<lmaxHps:
      var obj = ogc.handovers[id][idx].load(Acq)
      if not obj.isNil() and obj != ogc.hp[id][idx].load(Acq):
        obj = ogc.handovers[id][idx].exchange(nil)
        retire(obj, tid)
        return

type
  LFPointer = object
    pntr: OrcPointer
    tid: int16
    idx: int8
    lnk: bool
  LFPtr[T] = object
    pntr: OrcPointer
    tid: int16
    idx: int8
    lnk: bool

template copyImpl: untyped {.dirty.} =
  dest.tid = other.tid
  dest.idx = other.idx
  dest.pntr = other.pntr
  dest.lnk = other.lnk
  if dest.idx == 0:
    dest.idx = getNewIdx(dest.tid).int8
    protectPtr(dest.pntr, dest.tid, dest.idx)
  else:
    usingIdx(dest.idx, dest.tid)
  echo "copied"
template sinkImpl: untyped {.dirty.} =
  dest.tid = other.tid
  dest.idx = other.idx
  dest.pntr = other.pntr
  dest.lnk = other.lnk
  if dest.idx == 0:
    dest.idx = getNewIdx(dest.tid).int8
    protectPtr(dest.pntr, dest.tid, dest.idx)
  else:
    other.idx.unsafeAddr()[] = 0
  echo "sunk"
proc `=copy`*[T](dest: var LFPtr[T]; other: LFPtr[T]) =
  copyImpl()
proc `=sink`*[T](dest: var LFPtr[T]; other: LFPtr[T]) =
  sinkImpl()
proc `=copy`*(dest: var LFPointer; other: LFPointer) =
  copyImpl()
proc `=sink`*(dest: var LFPointer; other: LFPointer) =
  sinkImpl()

proc `=destroy`(lfp: var LFPointer) =
  clear(lfp.pntr, lfp.idx, lfp.tid, lfp.lnk, false)
proc `=destroy`*[T](lfp: var LFPtr[T]) =
  clear(lfp.pntr, lfp.idx, lfp.tid, lfp.lnk, false)
  echo "destroy called"

template initLFImplWArgs(): untyped {.dirty.} =
  typeof(result)(pntr: pntr, tid: tid, idx: idx, lnk: linked)
template initLFImpl(): untyped {.dirty.} =
  let tid = getTid
  let newidx = getNewIdx tid
  typeof(result)(lnk: true, tid: tid.int16, idx: newidx.int8)


proc initLFPointer(pntr: OrcPointer; tid: int16; idx: int8; linked: bool): LFPointer =
  initLFImplWArgs()
proc initLFPointer(): LFPointer =
  initLFImpl()
proc initLFPtr[T](pntr: OrcPointer; tid: int16; idx: int8; linked: bool): LFPtr[T] =
  initLFImplWArgs()
proc initLFPtr[T](): LFPtr[T] =
  initLFImpl()



proc newOrc*(tipe: typedesc): LFPtr[tipe] =
  let pntr = cast[OrcPointer](allocShared(sizeof(tipe) + 8) +% 8)
  let tid = getTid()
  result = initLFPtr[tipe](pntr, tid.int16, (getNewIdx tid).int8, false)
  result.pntr.orc[] = orcZero

proc `[]`*[T](lfp: LFPtr[T]): var T =
  cast[ptr T](lfp.pntr)[]
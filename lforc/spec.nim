import wtbanland/atomics

const
  maxThreads*: int = 2
  maxHps*: int = 64
  oseq*: uint = (1 shl 24).uint
  bretire*: uint = (1 shl 23).uint
  orcZero*: uint = (1 shl 22).uint

template ocnt*(x: uint): untyped = (dec oseq) and x

type
  GlobalHpList*[N, L] = array[N, array[L, Atomic[pointer]]]
  GlobalHandOvers*[N, L] = array[N, array[L, Atomic[pointer]]]

  OrcBase* {.inheritable.} = object
    orc: Atomic[uint] # default is orcZero

  OrcAtomic*[T] {.borrow.} = distinct Atomic[T]
  OrcPtr*[T] {.borrow.} = distinct ptr T

  TLInfo* [L] = object
    hpList: array[L, Atomic[ptr OrcBase]]
    handOvers: array[L, Atomic[ptr OrcBase]]
    usedHaz: array[L, int]
    retireStarted: bool
    recursiveList: seq[ptr OrcBase]

  PassThePointerOrcGc[N, L] = object
    tl: array[N, TLInfo[L]]


# proc initGlobalHpList*(maxThreads, maxHps: static Natural): auto =
#   result = nucleate(GlobalHpList[maxThreads, maxHps])

# proc initGlobalHandOvers*(maxThreads, maxHps: static Natural): auto =
#   result = nucleate(GlobalHandOvers[maxThreads, maxHps])  

var globalHpList* {.global.}: GlobalHpList[maxThreads, maxHps]
var globalHandOvers* {.global.}: GlobalHandOvers[maxThreads, maxHps]
var globalPtp* {.global.}: PassThePointerOrcGc[maxThreads, maxHps]

var tid* {.threadvar.}: int

proc incrementOrc[T](iptr: ptr T) =
  block:
    if iptr.isNil:
      break
    var lorc: uint = iptr[].orc.fetchAdd(oseq + 1) + oseq + 1
    if ocnt(lorc) != orcZero:
      break
    if iptr[].orc.compareExchange(lorc, lorc + bretire):
      discard
      # globalPtp.retire(ptr)

proc decrementOrc[T](iptr: ptr T) =
  block:
    if iptr.isNil:
      break
    globalPtp.tl[tid].hpList[0].store(iptr, moRel)
    var lorc: uint = iptr[].orc.fetchAdd(oseq - 1) + oseq - 1
    if ocnt(lorc) != orcZero:
      break
    if iptr[].orc.compareExchange(lorc, lorc + bretire):
      discard
      # globalPtp.retire(ptr)

proc store[T](iptr: ptr T) =
  incrementOrc(iptr)
  var old: ptr T = cast[Atomic[ptr T]](iptr).exchange(iptr, moRlx)
  decrementOrc(old)
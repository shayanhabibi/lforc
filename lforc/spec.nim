import wtbanland/atomics

const
  maxThreads*: int = 256 # Max number of threads allowed
  maxHps*: int = 64 # Max number of hazard pointers per thread

  orcSeq* = (1 shl 24).uint
  bretired* = (1 shl 23).uint
  orcZero* = (1 shl 22).uint
  orcCntMask* = orcSeq - 1
  orcSeqMask* = high(uint) xor orcCntMask
  maxRetCnt* = 1000

  cbretired = high(uint) xor bretired

  unmarkMask: uint = high(uint) xor uint(3)

template oseq*(x: uint): uint = orcSeqMask and x
template ocnt*(x: uint): uint = orcCntMask and x
template hasBitRetire*(x: uint): uint = bretired and x
template isCounterZero*(x: uint): bool =
  (x and cbretired and orcCntMask) == orcZero
template getUnmarked*(x: untyped): untyped =
  cast[typeof(x)](cast[uint](x) and unmarkMask)

type
  HpList*[T] = array[maxThreads, array[maxHps, Atomic[T]]]
  ## Alias for matrix of thread hazard pointers
  HandOvers*[T] = array[maxThreads, array[maxHps, Atomic[T]]]
  ## Alias for matrix of thread handover hazard pointers

  OrcHead* = object
    ## Alias for typeless access to a orc objects header
    orc*: Atomic[uint]

  OrcBase*[T] = object
    ## Object container for an object to be embedded into the obj field with
    ## a orc header
    orc*: Atomic[uint]
    obj*: T

template getHeader*[T](objPtr: ptr T): ptr OrcHead =
  let backAlign = cast[uint](objPtr) - 8
  cast[ptr OrcHead](backAlign)

template getOrcPtr*[T](userPtr: ptr T): ptr OrcBase[T] =
  cast[ptr OrcBase[T]](getHeader userPtr)

template getUserPtr*[T](orcPtr: ptr OrcHead | ptr OrcBase[T]): ptr T =
  let alignPtr = cast[uint](orcPtr) + 8
  result = cast[ptr T](alignPtr)

converter toOHeadPtr*[T](orcBasePtr: var ptr OrcBase[T]): ptr OrcHead =
  ## OrcHeads are simply an alias for a typeless OrcBase, whereby the embedded
  ## object information are not available.
  cast[ptr OrcHead](orcBasePtr)

# converter toOBasePtr*[T](orcPtr: ptr OrcHead): ptr OrcBase[T] =
#   cast[ptr OrcBase[T]](orcPtr)

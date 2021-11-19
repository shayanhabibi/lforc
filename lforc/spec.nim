import wtbanland/atomics

const
  maxThreads*: int = 256
  maxHps*: int = 64

  unmarkMask: uint = high(uint) xor uint(3)
  orcSeq* = (1 shl 24).uint
  bretired* = (1 shl 23).uint
  orcZero* = (1 shl 22).uint
  orcCntMask* = orcSeq - 1
  orcSeqMask* = high(uint) xor orcCntMask
  maxRetCnt* = 1000

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

  OrcHead* = object
    orc*: Atomic[uint]

  OrcBase*[T] = object
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

converter toOPtr[T](orcBasePtr: ptr OrcBase[T]): ptr OrcHead = cast[ptr OrcHead](orcBasePtr)
converter toOBasePtr[T](orcPtr: ptr OrcBase): ptr OrcBase[T] = cast[ptr OrcBase[T]](orcPtr)
# converter toUserPtr[T](orcBasePtr: ptr OrcBase[T]): ptr T = orcBasePtr.getUserPtr()

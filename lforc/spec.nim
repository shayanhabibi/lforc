const
  maxThreads*: int = 256 # Max number of threads allowed
  maxHps*: int = 64 # Max number of hazard pointers per thread

  orcSeq* = 1 shl 24
  bretired* = 1 shl 23
  orcZero* = 1 shl 22
  orcCntMask* = orcSeq - 1
  orcSeqMask* = not orcCntMask
  maxRetCnt* = 1000

  unmarkMask: uint = not 3.uint

template oseq*(x: typed): int = orcSeqMask and x.int
template ocnt*(x: typed): int = orcCntMask and x.int
template hasBitRetire*(x: typed): bool = (bretired and x) != 0
template isCounterZero*(x: typed): bool =
  (x and not(bretired) and orcCntMask) == orcZero
template getUnmarked*(x: untyped): untyped =
  cast[typeof(x)](cast[uint](x) and unmarkMask)

template t[T](x: T): typedesc =
  bind sizeof
  when sizeof(T) == 8: uint64
  elif sizeof(T) == 4: uint32
  elif sizeof(T) == 2: uint16
  elif sizeof(T) == 1: uint8

var
  SeqCst* = ATOMIC_SEQ_CST
  Rlx* = ATOMIC_RELAXED
  Acq* = ATOMIC_ACQUIRE
  Rel* = ATOMIC_RELEASE
  AcqRel* = ATOMIC_ACQ_REL

template load*[T](dest: var T, mem: AtomMemModel = SeqCst): T =
  when T is AtomType:
    dest.addr.atomicLoadN(mem)
  else:
    cast[T](cast[ptr t(T)](dest.addr).atomicLoadN(mem))
template store*[T](dest: var T, val: T, mem: AtomMemModel = SeqCst) =
  when T is AtomType:
    dest.addr.atomicStoreN(val, mem)
  else:
    cast[ptr t(T)](dest.addr).atomicStoreN(cast[t(T)](val), mem)
template fetchAdd*[T](dest: var T, val: SomeInteger, mem: AtomMemModel = SeqCst): T =  
  when T is AtomType:
    dest.addr.atomicFetchAdd(val, mem)
  else:
    cast[T](cast[ptr t(T)](dest.addr).atomicFetchAdd(cast[t(T)](val), mem))
template fetchAdd*[T](dest: T, val: SomeInteger, mem: AtomMemModel = SeqCst): T =
  when T is AtomType:
    dest.unsafeAddr.atomicFetchAdd(val, mem)
  else:
    cast[T](cast[ptr t(T)](dest.unsafeAddr).atomicFetchAdd(cast[t(T)](val), mem))
template fetchSub*[T](dest: var T, val: SomeInteger, mem: AtomMemModel = SeqCst): T =
  when T is AtomType:
    dest.addr.atomicFetchSub(val, mem)
  else:
    cast[T](cast[ptr t(T)](dest.addr).atomicFetchSub(cast[t(T)](val), mem))
template fetchSub*[T](dest: T, val: SomeInteger, mem: AtomMemModel = SeqCst): T =
  when T is AtomType:
    dest.unsafeAddr.atomicFetchSub(val, mem)
  else:
    cast[T](cast[ptr t(T)](dest.unsafeAddr).atomicFetchSub(cast[t(T)](val), mem))
template compareExchange*[T](dest, expected, desired: T; succ, fail: AtomMemModel): bool =
  when T is AtomType:
    dest.unsafeAddr.atomicCompareExchangeN(expected.unsafeAddr, desired, false, succ, fail)
  else:
    cast[ptr t(T)](dest.unsafeAddr).atomicCompareExchangeN(cast[ptr t(T)](expected.unsafeAddr), cast[t(T)](desired), false, succ, fail)
template compareExchangeWeak*[T](dest, expected, desired: T; succ, fail: AtomMemModel): bool =
  when T is AtomType:
    dest.unsafeAddr.atomicCompareExchangeN(expected.unsafeAddr, desired, true, succ, fail)
  else:
    cast[ptr t(T)](dest.unsafeAddr).atomicCompareExchangeN(cast[ptr t(T)](expected.unsafeAddr), cast[t(T)](desired), true, succ, fail)
template compareExchange*[T](dest, expected, desired: T; order: AtomMemModel = SeqCst): bool =
  when T is AtomType:
    dest.unsafeAddr.atomicCompareExchangeN(expected.unsafeAddr, desired, false, order, order)
  else:
    cast[ptr t(T)](dest.unsafeAddr).atomicCompareExchangeN(cast[ptr t(T)](expected.unsafeAddr), cast[t(T)](desired), false, order, order)
template compareExchangeWeak*[T](dest, expected, desired: T; order: AtomMemModel = SeqCst): bool =
  when T is AtomType:
    dest.unsafeAddr.atomicCompareExchangeN(expected.unsafeAddr, desired, true, order, order)
  else:
    cast[ptr t(T)](dest.unsafeAddr).atomicCompareExchangeN(cast[ptr t(T)](expected.unsafeAddr), cast[t(T)](desired), true, order, order)
template exchange*[T](dest: var T; val: T, mem: AtomMemModel = SeqCst): T =
  when T is AtomType:
    dest.unsafeAddr.atomicExchangeN(val, mem)
  else:
    cast[T](cast[ptr t(T)](dest.unsafeAddr).atomicExchangeN(cast[t(T)](val), mem))
template exchange*[T](dest: T; val: T, mem: AtomMemModel = SeqCst): T =
  when T is AtomType:
    dest.unsafeAddr.atomicExchangeN(val, mem)
  else:
    cast[T](cast[ptr t(T)](dest.unsafeAddr).atomicExchangeN(cast[t(T)](val), mem))
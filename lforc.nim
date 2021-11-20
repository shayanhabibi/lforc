## LFOrc
## =====
## 
## LFOrc (Lock-Free Object reference counter) is a memory reclamation algorithm,
## or *garbage collector*, which is used for objects shared across threads
## without the use of locks or other wait bound operations.

import lforc/threadreg
import lforc/spec
import lforc/ptp
import wtbanland/atomics

## Contains the PTPOrcGC Object and procedures


type
  TLInfo = object
    # Thread Local Information object
    usedHaz: array[maxHps, int] # Used hazard pointers
    retireStarted: bool # Whether the thread is retiring a pointer
    retCnt: int # The retire count
    recursiveList: seq[ptr OrcHead] # a list that prevents explosive reclamation
                                    # of cyclical objects
  PTPOrcGc = object
    # The global lforc object
    inDestructor: bool # Whether a lforc thread is in a destructor sequence
    hp: HpList[ptr OrcHead] # matrix of thread hazard pointers
    handOvers: HandOvers[ptr OrcHead] # matrix of thread hand over pointers
    maxHps: Atomic[int] # Max hazard pointers in matrices
    tl: array[maxThreads, TLInfo] # matrix of thread local information objects
  OrcPtr*[T] = object
    # Orc pointer ~ serves like a sharedptr in that it contains the pointer
    # to the object and the meta deta following it
    pntr*: T # 
    tid*:  int16
    idx*: int8
    lnk*: bool

  OrcUnsafePtr*[T] = object
    # Internal Orc Pointer generated initially from loads
    pntr*: T

  OrcAtomic*[T] {.borrow.} = distinct Atomic[T]
  # Replaces std Atomic[T] to be used with orc objects as it will decrement/increment
  # the objects as necessary

# Begin  | Forward decls
# =====================================================
# These decls are probably used pretty frequently but are not
# the main algorithms of interest in the code so are defined at the
# bottom of the file
proc retire(pntr: var ptr OrcHead, tid: int = getTid())
proc initPTPOrcGc()
proc clearBitRetired(pntr: ptr OrcHead, tid: int = getTid()): uint
proc tryHandover(pntr: var ptr OrcHead): bool {.inline.}
proc retireOne(tid: int = getTid())
proc addRetCnt(tid: int): int {.inline.}
proc resetRetCnt(tid: int) {.inline.}

# =====================================================
# End    | Forward decls

proc destroy(porc: var PTPOrcGc) =
  ## Cleans up and destroys the lforc object passed
  porc.inDestructor = true
  var maxHps = porc.maxHps.load(moAcq)
  for it in 0..<maxThreads:
    for ihp in 0..<maxHps:
      var obj: ptr OrcHead = porc.handOvers[it][ihp].load(moRlx)
      if not unlikely obj.isNil:
        var lorc: uint = obj[].orc.load(moRlx)
        porc.handOvers[it][ihp].store(nil, moRlx)
        retire(obj, getTid)

# Global symbol for the lforc object
var gorc* {.global.}: PTPOrcGc
initPTPOrcGc()

proc initPTPOrcGc =
  ## Completes the required initialisation procedures for the functioning
  ## of lforc (ie inits the thread registry and creates the lforc object)
  initThreadRegistry()
  gorc = PTPOrcGC()


proc tearDownOrcGc =
  destroy(gorc)

# REVIEW
proc createSharedOrc*[T](tipe: typedesc[T], size: Natural): ptr T =
  ## Principal: Allocate shared block with 8 byte header for metadata
  # Issue with this is that sizeof will not correctly indicate the size of the object
  # this also plays issues if the object the person has created is supposed to be
  # cache lined since they will be unaware that the object is not ipsilateral
  let orcPtr = createShared(OrcBase[T])
  result = orcPtr.getUserPtr
  
  # REVIEW
proc allocateSharedOrc*(size: Natural): pointer =
  let aptr = cast[uint](allocShared(sizeof(size + 8))) + 8'u
  result = cast[pointer](aptr)

# In terms of optimisation, objects will contain the thread ids themselves
# and may use that instead of fetching the value. Benchmark?
# REVIEW
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

proc usingIdx(idx: int; tid: int = getTid) {.inline.} =
  # NOTE would this be optimised as a template?
  if not idx == 0:
    inc gorc.tl[tid].usedHaz[idx]

proc cleanIdx(tid: int; idx: int): int {.inline.} =
  # NOTE would this be optimised as a template?
  if idx == 0:
    result = -1
  else:
    dec gorc.tl[tid].usedHaz[idx]
    result = gorc.tl[tid].usedHaz[idx]

# NOTE - access to orc field on pntr makes it likely that this is a ptr to orcbase
# or orchead; therefore might as well just directly point to orchead?
# proc clear[T](pntr: T, idx: int, tid: int, linked: bool, reuse: bool) {.inline.} =
#   if not reuse and cleanIdx(tid=tid, idx=idx) != 0:
#     discard
#   elif linked:
#     discard
#   elif not pntr.isNil:
#     pntr = getUnmarked(pntr) # LINK
#     var lorc: uint = pntr[].orc.load(moAcq)
#     if ocnt(lorc) == orcZero:
#       if pntr[].orc.compareExchange(lorc, lorc + bretired):
#         retire(pntr, tid)
#         discard
proc clear(pntr: var ptr OrcHead, idx: int, tid: int, linked: bool, reuse: bool) {.inline.} =
  if not reuse and cleanIdx(tid = tid, idx = idx) != 0:
    discard
  elif linked:
    discard
  elif not pntr.isNil:
    pntr = getUnmarked(pntr) # LINK
    var lorc: uint = pntr.orc.load(moAcq)
    if ocnt(lorc) == orcZero:
      if pntr.orc.compareExchange(lorc, lorc + bretired):
        retire(pntr, tid)

proc getUsedHaz(idx: int; tid: int = getTid): int {.inline.} =
  # NOTE is this optimised if its a template instead?
  result = gorc.tl[tid].usedHaz[idx]

proc getProtected[T](index: int; adr: ptr Atomic[T]; tid: int = getTid): T {.inline.} =
  var pub, pntr: T = nil
  while (pub = adr[].load(moRlx); pub) != pntr:
    gorc.hp[tid][index].store(getUnmarked(pub)) # LINK
    pntr = pub
  result = pub

proc protectPtr(pntr: ptr OrcHead; tid: int; idx: int) {.inline.} =
  gorc.hp[tid][idx].store(getUnmarked(pntr), moRel)

proc initOrcPtr[T](pntr: T, tid: int16, idx: int8, linked: bool): OrcPtr[T] =
  OrcPtr[T](pntr, tid, idx, linked)

proc initOrcPtr(): OrcPtr[ptr OrcHead] =
  result = OrcPtr[ptr OrcHead](tid: cast[int16](getTid))
  result.idx = cast[int8](getNewIdx result.tid)

proc destroy[T](x: var OrcPtr[T]) =
  clear(x.pntr, x.idx, x.tid, x.lnk, false)

proc `==`[T](x, y: OrcPtr[T] | OrcUnsafePtr[T]): bool {.inline.} =
  x.pntr == y.pntr
proc `==`[T](x: OrcUnsafePtr[T] | OrcPtr[T], y: T): bool {.inline.} =
  x.pntr == y
proc `!=`[T](x, y: OrcPtr[T] | OrcUnsafePtr[T]): bool {.inline.} =
  x.pntr != y.pntr
proc `!=`[T](x: OrcUnsafePtr[T] | OrcPtr[T], y: T): bool {.inline.} =
  x.pntr != y
proc `[]`[T](x: OrcUnsafePtr[T] | OrcPtr[T]): T {.inline.} =
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
  # NOTE does this mean I should call a moved on the original?
  # move x
  #[
    // Copy constructor with move semantics (orc-to-orc)
    orc_ptr(orc_ptr&& other) {
        //printf("orc_ptr constructor with move semantics from %p increment on idx=%d\n", other.ptr, other.idx);
        tid = other.tid;
        idx = other.idx;
        ptr = other.ptr;
        lnk = other.lnk;
        if (idx == 0) {
            idx = g_ptp.getNewIdx(tid);
            g_ptp.protect_ptr(ptr, tid, idx);
        } else {
            // other.idx is always 0, it should never enter this branch
            other.idx = 0;
        }
    }
  ]#

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
  # NOTE if this is a move operation, do I perform a move on other? or do i sink y?
  # move y
#[
    // Move assignment operator (orc-to-orc)
    inline orc_ptr& operator=(orc_ptr&& other) {
        PassThePointerOrcGC* ptp = &g_ptp;
        bool reuseIdx = ((other.idx < idx) && (ptp->getUsedHaz(idx, tid) == 1));
        ptp->clear(ptr, idx, tid, lnk, reuseIdx);
        if (other.idx < idx) {
            if (!reuseIdx) idx = ptp->getNewIdx(tid, other.idx+1);
            ptp->protect_ptr(other.ptr, tid, idx);
        } else {
            // Steal the other's reference
            idx = other.idx;
            other.idx = 0;
        }
        ptr = other.ptr;
        lnk = other.lnk;
        return *this;
    }

]#

proc `move=`[T](x: var OrcPtr[T], y: OrcUnsafePtr[T]) =
  var reuseIdx: bool = getUsedHaz(x.idx, x.tid) == 1
  clear(x.pntr, x.idx, x.tid, x.lnk, reuseIdx)
  if not reuseIdx:
    x.idx = getNewIdx(x.tid)
  protectPtr(y.pntr, x.tid, x.idx)
  x.pntr = y.pntr
  x.lnk = true
  # NOTE like before, how is a move assignment in cpp implemented?
  #[
    // Move assignment (internal-to-orc)
    //other comes always from a load and other.idx is 0
    inline orc_ptr& operator=(orc_unsafe_internal_ptr<T>&& other) {
        // This may be called once or twice. If called twice, 'other' is the just-moved-from orc_ptr hp
        //printf("orc_ptr 'move' from %p to %p increment on idx=%d\n", ptr, other.ptr, other.idx);
        bool reuseIdx = (g_ptp.getUsedHaz(idx, tid) == 1);
        g_ptp.clear(ptr, idx, tid, lnk, reuseIdx);
        if (!reuseIdx) idx = g_ptp.getNewIdx(tid);
        g_ptp.protect_ptr(other.ptr, tid, idx);
        ptr = other.ptr;
        lnk = true;
        return *this;
    }
  ]#


proc incrementOrc(pntr: var ptr OrcHead) {.inline.} =
  block:
    pntr = getUnmarked pntr
    if pntr.isNil: # or pntr == T and g_poisoned
      break
    var lorc: uint = pntr.orc.fetchAdd(1) + 1
    if ocnt(lorc) != orcZero:
      break
    if pntr.orc.compareExchange(lorc, lorc + bretired):
      retire(pntr)
      break
#[
// 'T' is typically 'Node*'
template<typename T>
class orc_atomic : public std::atomic<T> {
private:
    static const bool enablePoison = true;  // set to false to disable poisoning

    // Needed by Harris Linked List, Natarajan tree and possibly others
    T getUnmarked(T ptr) { return (T)(((size_t)ptr) & (~3ULL)); }

    // Progress condition: wait-free population oblivious
    inline void incrementOrc(T ptr) {
        ptr = getUnmarked(ptr);
        if (ptr == nullptr || ptr == (T)&g_poisoned) return;
        uint64_t lorc = ptr->_orc.fetch_add(1) + 1;
        if (ocnt(lorc) != ORC_ZERO) return;
        // No need to increment sequence: the faa has done it already
        if (ptr->_orc.compare_exchange_strong(lorc, lorc + BRETIRED)) g_ptp.retire(ptr);
    }
]#

proc decrementOrc(pntr: var ptr OrcHead) {.inline.} =
  block:
    pntr = getUnmarked pntr
    if pntr.isNil:
      break
    let tid = getTid()
    protectPtr(pntr, tid, 0)
    var lorc: uint = pntr.orc.fetchAdd(orcSeq - 1) + orcSeq - 1
    if addRetCnt(tid) == maxRetCnt:
      retireOne(tid)
      resetRetCnt(tid)
    if ocnt(lorc) != orcZero:
      break
    if pntr.orc.compareExchange(lorc, lorc + bretired):
      retire(pntr, tid) # FIXME IMPL
      break

proc initOrcAtomic[T](): OrcAtomic[T] =
  result.store(nil, moRlx)

proc initOrcAtomic[T](pntr: T): OrcAtomic[T] =
  incrementOrc(pntr)
  result.store(pntr, moRlx)

proc destroy[T](x: var OrcAtomic[T]) =
# proc `=destroy`[T](x: var OrcAtomic[T]) =
  block:
    var pntr = x.load(moRlx)
    if pntr.isNil:
      break
    decrementOrc(pntr)


proc `[]`[T](x: var OrcAtomic[T]): var T =
  # TODO this is supposed to be the Cpp equivalent overload of `.` field access
  # for objects within the atomic container
  x.load()

proc `[]=`[T](x: var OrcAtomic[T], y: T) =
  x.store(y)

proc `=`[T](x: var OrcAtomic[T]; y: OrcAtomic[T]) =
  x.store(y.load())

# REVIEW
# =======
# the orcgc atomic shit is a bit confusing; need help
# ====================================================
# proc store[T](oatm: var OrcAtomic[T]; newval: T, order: MemoryOrder = moSequentiallyConsistent) {.inline.} =
#   incrementOrc(newval)
#   var old = cast[Atomic[T]](oatm).exchange(newval, order)
#   decrementOrc(old)

# proc exchange[T](oatm: var OrcAtomic[OrcUnsafePtr[T]], newval: T): var OrcUnsafePtr[T] {.inline.} =
#   incrementOrc(newval)
#   var old = cast[Atomic[T]](oatm).exchange(newval)
#   decrementOrc(old)
#   let tid = getTid
#   result = move old

# proc compareExchange[T](oatm: var OrcAtomic[T]; expected: var T, desired: T): bool {.inline.} =
#   block:
#     if not cast[Atomic[T]](oatm).compareExchange(expected, desired):
#       result = false
#       break
#     incrementOrc(desired)
#     decrementOrc(expected)
#     result = true

# proc compareExchangeWeak[T](oatm: var OrcAtomic[T]; expected: var T, desired: T): bool {.inline.} =
#   block:
#     if not cast[Atomic[T]](oatm).compareExchangeWeak(expected, desired):
#       result = false
#       break
#     incrementOrc desired
#     decrementOrc expected
#     result = true

# proc load[T](oatm: var OrcAtomic[OrcUnsafePtr[T]]; order: MemoryOrder = moSeqCon): OrcUnsafePtr[T] =
#   let tid = getTid
#   var pntr = cast[T](getProtected(0, pntr, tid))
# ====================================================

proc clearBitRetired(pntr: ptr OrcHead, tid: int = getTid()): uint =
  gorc.hp[tid][0].store(pntr, moRel) # REVIEW: see below
  #[
  uint64_t clearBitRetired(orc_base* ptr, int tid) {
    hp[tid][0].store(static_cast<orc_base*>(ptr), std::memory_order_release);
                        ^---- REVIEW nothing is changing here afaict right?
  ]#
  var lorc = pntr.orc.fetchSub(bretired)-bretired
  if ocnt(lorc) == orcZero and pntr.orc.compareExchange(lorc, lorc + bretired):
    gorc.hp[tid][0].store(nil, moRlx)
    result = lorc + bretired
  else:
    gorc.hp[tid][0].store(nil, moRlx)
    result = 0

proc tryHandover(pntr: var ptr OrcHead): bool {.inline.} =
  ## Only called internally from retire()
  block hand_over:
    if gorc.inDestructor: break
    let lmaxHps = gorc.maxHps.load(moAcq)
    for tid in 0..<maxThreads:
      for idx in 0..<lmaxHps:
        if pntr == gorc.hp[tid][idx].load(moAcq):
          pntr = gorc.handOvers[tid][idx].exchange(pntr)
          result = true
          break hand_over

proc retire(pntr: var ptr OrcHead, tid: int = getTid()) =
  block retire:
    if pntr.isNil:
      break retire
    var rlist = gorc.tl[tid].recursiveList
    if gorc.tl[tid].retireStarted:
      rlist.add(pntr)
      break retire

    # NOTE: from original impl
    # If this is being called from the destructor
    # ~PassThePointerOrcGC(), clear out the handovers so we don't leak anything
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
        var lorc2 = pntr.orc.load(moAcq)
        if lorc2 != lorc:
          if not isCounterZero(lorc2):
            if clearBitRetired(pntr, tid) == 0:
              break
          continue
        # `=destroy`(pntr) # FIXME deallocate
        deallocShared(pntr) # REVIEW - if we allocated the original object
                            # correctly then I only have to give the pointer
                            # and not the original type right?
        break
      if rlist.len()==i:
        break
      pntr = rlist[i]
      inc i

    assert i == rlist.len() # NOTE: As per cpp impl
    rlist.setLen(0) # Clearing the sequence
    gorc.tl[tid].retireStarted = false

proc retireOne(tid: int = getTid()) =
  block retire:
    let lmaxHps = gorc.maxHps.load(moAcq)
    for idx in 0..<lmaxHps:
      var obj: ptr OrcHead = gorc.handOvers[tid][idx].load(moRlx)
      if not obj.isNil and obj != gorc.hp[tid][idx].load(moRlx):
        obj = gorc.handOvers[tid][idx].exchange(nil)
        retire(obj, tid)
        break retire
    for id in 0..<maxThreads:
      if likely id != tid:
        for idx in 0..<lmaxHps:
          var obj: ptr OrcHead = gorc.handOvers[id][idx].load(moAcq)
          if not obj.isNil and obj != gorc.hp[id][idx].load(moAcq):
            obj = gorc.handOvers[id][idx].exchange(nil)
            retire(obj, tid)
            break retire
          

proc addRetCnt(tid: int): int {.inline.} =
  # TODO Optimise by turning into template
  inc gorc.tl[tid].retCnt
  result = gorc.tl[tid].retCnt


proc resetRetCnt(tid: int) {.inline.} =
  # TODO Optimise by turning into template
  gorc.tl[tid].retCnt = 0

#[
public:
    // Needed by Harris Linked List (orc_ptr)
    template<typename T> T getUnmarked(T ptr) { return (T)(((size_t)ptr) & (~0x3ULL)); }
};
template<typename T>
struct orc_unsafe_internal_ptr {
    T ptr;

    orc_unsafe_internal_ptr(T ptr) : ptr{ptr} {}

    // Used by Natarajan and maybe Harris
    inline T getUnmarked() const { return (T)(((size_t)ptr) & (~3ULL)); }
    inline T getMarked() const { return (T)(((size_t)ptr) | (3ULL)); }
    inline bool isMarked() const { return getFlag(); }
    inline bool getFlag() const { return (bool)((size_t)ptr & 1); }
    inline bool getTag() const { return (bool)((size_t)ptr & 2); }

    // Equality/Inequality operators
    bool operator == (const orc_unsafe_internal_ptr<T> &rhs) { return ptr == rhs.ptr; }
    bool operator == (const T &rhs) { return ptr == rhs; }
    bool operator != (const orc_unsafe_internal_ptr<T> &rhs) { return ptr != rhs.ptr; }
    bool operator != (const T &rhs) { return ptr != rhs; }
};
ORC_PTR methods
    // Used by Natarajan and maybe Harris
    inline T getUnmarked() const { return (T)(((size_t)ptr) & (~3ULL)); }
    inline T getMarked() const { return (T)(((size_t)ptr) | (3ULL)); }
    inline bool isMarked() const { return getFlag(); }
    inline bool getFlag() const { return (bool)((size_t)ptr & 1); }
    inline bool getTag() const { return (bool)((size_t)ptr & 2); }
    inline void unmark() { ptr = getUnmarked(); }
    inline void swapPtrs(orc_ptr<T>& other) {
        T tmp_ptr = ptr;
        int8_t tmp_idx = idx;
        ptr = other.ptr;
        idx = other.idx;
        other.ptr = tmp_ptr;
        other.idx = tmp_idx;
    }

    // Used by Harris Original and Maged-Harris
    // TODO: change this to return orc_unsafe_internal_ptr<T> instead.
    T setUnmarked(orc_ptr<T>& other) {
        PassThePointerOrcGC* ptp = &g_ptp;
        bool reuseIdx = ((other.idx < idx) && (ptp->getUsedHaz(idx, tid) == 1));
        ptp->clear(ptr, idx, tid, lnk, reuseIdx);
        if(other.idx<idx){
            if (!reuseIdx) idx = ptp->getNewIdx(tid, other.idx+1);
            ptp->protect_ptr(other.ptr, tid, idx);
        }else{
            ptp->usingIdx(other.idx, tid);
            idx = other.idx;
        }
        ptr = g_ptp.getUnmarked(other.ptr);
        lnk = other.lnk;
        return ptr;
    }
    // Used by Harris Original and Maged-Harris
    // TODO: change this to return orc_unsafe_internal_ptr<T> instead.
    T setUnmarked(orc_unsafe_internal_ptr<T>&& other) {
        PassThePointerOrcGC* ptp = &g_ptp;
        bool reuseIdx = (ptp->getUsedHaz(idx, tid) == 1);
        if (!reuseIdx) {
        	ptp->clear(ptr, idx, tid, lnk, reuseIdx);
        	idx = ptp->getNewIdx(tid, 1);
        }
        ptp->protect_ptr(other.ptr, tid, idx);
        ptr = g_ptp.getUnmarked(other.ptr);
        lnk = true;
        return ptr;
    }

LINK - make orc might be required and is not implemented atm
/*
 * make_orc<T> is similar to make_shared<T>
 */
template <typename T, typename... Args>
orc_ptr<T*> make_orc(Args&&... args) {
    const int tid = ThreadRegistry::getTID();
    T* ptr = new T(std::forward<Args>(args)...);
    ptr->_deleter = [](void* obj) { delete static_cast<T*>(obj); };
    g_ptp.protect_ptr(ptr, tid, 0);
    // If the orc_ptr was created by the user, then it is not linked
    return std::move(orc_ptr<T*>(ptr, tid, 0, false));
}

// Just some variable to make a unique pointer
intptr_t g_poisoned = 0;

template<typename T> bool is_poisoned(T ptr) { return (void*)ptr.getUnmarked() == (void*)&g_poisoned; }


]#
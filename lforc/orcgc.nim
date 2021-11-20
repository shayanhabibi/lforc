import lforc/spec
import lforc/threadreg

import wtbanland/atomics

type
  HpList*[T] = array[maxThreads, array[maxHps, Atomic[T]]]
  ## Alias for matrix of thread hazard pointers
  HandOvers*[T] = array[maxThreads, array[maxHps, Atomic[T]]]
  ## Alias for matrix of thread handover hazard pointers
  TLInfo* = object
    # Thread Local Information object
    usedHaz*: array[maxHps, int] # Used hazard pointers
    retireStarted*: bool # Whether the thread is retiring a pointer
    retCnt*: int # The retire count
    recursiveList*: seq[ptr OrcHead] # a list that prevents explosive reclamation
                                    # of cyclical objects
  PTPOrcGc* = object
    # The global lforc object
    inDestructor*: bool # Whether a lforc thread is in a destructor sequence
    hp*: HpList[ptr OrcHead] # matrix of thread hazard pointers
    handOvers*: HandOvers[ptr OrcHead] # matrix of thread hand over pointers
    maxHps*: Atomic[int] # Max hazard pointers in matrices
    tl*: array[maxThreads, TLInfo] # matrix of thread local information objects

## Types of orcptr and its associated accessor procs

import lforc/arith
import std/atomics

type
  OrcPtr*[T] = object
    pntr: ptr T
    tid*:  int16
    idx*: int8
    lnk*: bool
  OrcHead* = object
    ## Alias for typeless access to a orc objects header
    orc*: Atomic[uint]
  OrcBase*[T] = object
    ## Object container for an object to be embedded into the obj field with
    ## a orc header
    orc*: Atomic[uint]
    obj*: T

converter toObj*[T](x: OrcPtr[T]): var T = x.pntr[]

template orc*(pntr: pointer): ptr uint =
  cast[ptr uint](pntr -% 8)

template incOrc*(pntr: pointer): int =
  mixin orc
  pntr.orc.atomicFetchAdd(1, ATOMIC_ACQ_REL).int

template decOrc*(pntr: pointer): int =
  mixin orc
  pntr.orc.atomicFetchSub(1, ATOMIC_ACQ_REL).int

template getOrc*(pntr: pointer): int =
  mixin orc
  pntr.orc.atomicLoadN(ATOMIC_ACQUIRE).int

proc incOrc*(orcPtr: OrcPtr): int {.inline.} = orcPtr.pntr.incOrc
proc decOrc*(orcPtr: OrcPtr): int {.inline.} = orcPtr.pntr.decOrc
proc getOrc*(orcPtr: OrcPtr): int {.inline.} = orcPtr.pntr.getOrc

proc allocOrcPtr*[T](tipe: typedesc[T], size: Natural = 1): OrcPtr[T] {.inline.} =
  result.pntr = cast[ptr T](allocShared0(sizeof(tipe) + 8) +% 8)

proc deallocOrcPtr*(orcPtr: var OrcPtr) {.inline.} =
  deallocShared(orcPtr.pntr.orc)
  orcPtr.pntr = nil

when isMainModule:
  type
    Obj = object
      x: int
  
  var op = allocOrcPtr(Obj)
  echo repr op
  op.pntr.x = 5
  echo repr op
  discard op.incOrc
  discard op.incOrc
  discard op.incOrc
  echo repr op
  echo op.getOrc
  deallocOrcPtr(op)

## Thread Registry
## ===============
## 
## This module uses a minimal memory footprint to achieve recyclable and unique
## thread indexes on a Natural number scale.
## 
## Each thread on closing would be required to call `releaseThreadId()`.
## 
## Unique thread index is accessible by using the `getTid()` proc.
## 
## All operations must be preceded internally by a call to initThreadRegistry()

import wtbanland/atomics
import lforc/spec
import std/bitops

# Registry is unlikely to be required to be cachelined due to the frequency
# of access (unlikely). For the moment however, it will be maintained.
# Therefore, we must ensure it is at least capable of providing up to the
# the number of maxThreads.
# Since a cache lined array can fit up to 64 * 64 (4,096) I don't think
# we'll have a problem anyway. Still though.

# Measure the length required of the thread registry based on the max number
# of threads possible in lforc
const regLen = 64 + 64 * (maxThreads div (64 * 64))
# create the thread registry symbol
var threadRegistry {.global.}: array[regLen, Atomic[uint]]

iterator thrRegIndex: (int, var Atomic[uint]) =
  ## qol iterator for the global thread registry
  for i in 0..<regLen:
    yield (i, threadRegistry[i])

iterator thrReg: var Atomic[uint] =
  ## qol iterator for the global thread registry
  for i in 0..<regLen:
    yield threadRegistry[i]  

proc getOrcThreadId(): int =
  ## Must only be called by a thread once.
  ## Will retrieve a unique index id from the thread registry
  var bitLine: uint
  var fbit: int
  block done:
    for i,r in thrRegIndex():
      # We iterate over 8 byte blocks of bits and perform an atomic load
      bitLine = r.load(moRel)
      # We check to see if the block of bits has any available index values
      # ie bits with a value of 1
      while (fbit = bitLine.firstSetBit(); fbit) != 0:
        # If there is an available index value, then we will do a compare exchange
        # on the 8 byte block to replace the block with one which has that index
        # value flipped (ie set to 0)
        let bitIdx = fbit - 1
        if likely r.compareExchange(bitLine, bitLine xor (1'u shl bitIdx), moAcq): # compareExchange are better supported on architectures than FAA
          # The result is the 0 indexed value for the available index added onto
          # the number of 8 byte blocks that were empty previously multiplied
          # by the number of index values they held each (ie 'number of blocks' x '64')
          result = bitIdx + (i * 64)
          break done
        else:
          # Failure to exchange the block means we have been intercepted by
          # another thread and will have to reload the 8 byte block and try again
          bitLine = r.load(moRlx)
    raise newException(ValueError, "There are no free thread ids; raise the max threadCount")

# Thread local cache of thread id value
var tidValue {.threadvar.}: int

template getTid*: int =
  ## Returns the cached thread unique 0 indexed value or assigns one if it hasn't
  ## yet got one.
  if unlikely(tidValue == 0):
    tidValue = getOrcThreadId() + 1
  tidValue - 1

proc releaseThreadId*() =
  ## If the thread has a local unique 0 indexed index value, then the procedure
  ## will reinsert it into the registry so it can be taken by another thread.
  block:
    if unlikely(tidValue == 0):
      break
    var arrayIdx = getTid div 64
    var idx = getTid mod 64
    var bitLine: uint = threadRegistry[arrayIdx].load(moRel)
    if unlikely((bitLine and (1'u shl idx.uint)) != 0'u):
      raise newException(ValueError, "Wtf happened; how is this even possible lol")
    # compare exchange is better supported
    discard threadRegistry[arrayIdx].compareExchange(bitLine, bitLine or (1'u shl idx.uint), moAcq)

proc initThreadRegistry* =
  ## Must be called by main thread;
  ## will reserve the 0 tid
  assert tidValue == 0, "Thread Registry has already been initiatialised"
  var highnum = high(uint)
  for r in thrReg():
    r.unsafeaddr[].store(highnum)
  assert getTid() == 0,  "Thread Registry has already been initiatialised"

initThreadRegistry()
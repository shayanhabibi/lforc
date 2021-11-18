import wtbanland/atomics
import lforc/spec
import std/bitops

# Registry is unlikely to be required to be cachelined due to the frequency
# of access (unlike). For the moment however, it will be maintained.
# Therefore, we must ensure it is at least capable of providing up to the
# the number of maxThreads.
# Since a cache lined array can fit up to 64 * 64 (4,096) I don't think
# we'll have a problem anyway. Still though.
const regLen = 64 + 64 * (maxThreads div (64 * 64))

var threadRegistry {.global.}: array[regLen, Atomic[uint]]

iterator thrRegIndex: (int, var Atomic[uint]) =
  for i in 0..<regLen:
    yield (i, threadRegistry[i])

iterator thrReg: var Atomic[uint] =
  for i in 0..<regLen:
    yield threadRegistry[i]  

proc getOrcThreadId(): int =
  var bitLine: uint
  var fbit: int
  block done:
    for i,r in thrRegIndex():
      bitLine = r.load(moRel)
      while (fbit = bitLine.firstSetBit(); fbit) != 0:
        let bitIdx = fbit - 1
        if r.compareExchange(bitLine, bitLine xor (1'u shl bitIdx), moAcq): # compareExchange are better supported on architectures than FAA
          result = bitIdx + (i * 64)
          break done
    raise newException(ValueError, "There are no free thread ids; raise the max threadCount")

var tidValue {.threadvar.}: int

template getTid*: int =
  if unlikely(tidValue == 0):
    tidValue = getOrcThreadId() + 1
  tidValue - 1

proc releaseThreadId*() =
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
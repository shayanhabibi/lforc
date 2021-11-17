import wtbanland/atomics
import std/bitops

var threadRegistry {.global.}: array[64, Atomic[uint]]

for r in threadRegistry:
  r.store(high(uint))


proc getOrcThreadId(): int =
  var bitLine: uint
  var fbit: int
  block done:
    for i,r in threadRegistry:
      bitLine = r.load(moRel)
      while (fbit = bitLine.firstSetBit(); fbit) != 0:
        let bitIdx = fbit - 1
        if r.compareExchange(bitLine, bitLine xor (1'u shl bitIdx), moAcq): # compareExchange are better supported on architectures than FAA
          result = bitIdx + (i * 64)
          break done
    raise newException(ValueError, "There are no free thread ids; raise the max threadCount")

var tidValue {.threadvar.}: int = -1

template tid*: int =
  if unlikely(tidValue < 0):
    tidValue = getOrcThreadId()
  tidValue

proc releaseThreadId*() =
  var arrayIdx = tid div 64
  var idx = tid mod 64
  var bitLine: uint = threadRegistry[arrayIdx].load(moRel)
  if unlikely((bitLine and (1'u shl idx.uint)) != 0'u):
    raise newException(ValueError, "Wtf happened; how is this even possible lol")
  # compare exchange is better supported
  discard threadRegistry[arrayIdx].compareExchange(bitLine, bitLine or (1'u shl idx.uint), moAcq)
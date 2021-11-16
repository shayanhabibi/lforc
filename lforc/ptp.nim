import wtbanland/atomics
import lforc/spec

proc handOverOrDelete*(iptr: var pointer, start: int) =
  block cycle:
    for it in start..<maxThreads:
      var idx: int
      while idx < maxHps:
        if globalHpList[it][idx].load(moRlx) == iptr:
          iptr = globalHandOvers[it][idx].exchange(iptr)
          if iptr.isNil():
            break cycle
          if globalHpList[it][idx].load(moRlx) == iptr:
            continue
        inc idx
    discard # Deallocate iptr

proc getProtected*(nptr: ptr Atomic[pointer]; idx: Natural): pointer =
  var pub, iptr: pointer = cast[pointer](0)
  while (pub = nptr[].load(moRlx); pub) != iptr:
    globalHpList[tid][idx].store(pub, moRlx)
    iptr = pub
  result = pub

proc clear*(idx: Natural) =
  globalHpList[tid][idx].store(nil, moRel)
  if not globalHandOvers[tid][idx].load(moRlx).isNil():
    var iptr = globalHandOvers[tid][idx].exchange(nil)
    if not iptr.isNil:
      handOverOrDelete(iptr, tid)

proc retire*(iptr: var pointer) =
  handOverOrDelete(iptr, 0)
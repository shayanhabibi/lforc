## Pointer arithmetic etc

proc `+%`*(x: pointer, y: SomeInteger): pointer = cast[pointer](cast[uint](x) + cast[uint](y))
proc `-%`*(x: pointer, y: SomeInteger): pointer = cast[pointer](cast[uint](x) - cast[uint](y))
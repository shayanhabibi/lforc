import lforc {.all.}

type
  MyObj = object
    field1: int
    field2: int
  MyObj2 = object
    field1: LFPtr[MyObj]
var myobj = newOrc MyObj
myobj[].field1 = 5
var myobj2 = MyObj2()
myobj2.field1 = myobj
echo typeof myobj

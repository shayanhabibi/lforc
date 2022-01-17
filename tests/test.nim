import lforc {.all.}

type
  MyObj = object
    field1: int
    field2: int

var myobj = newOrc MyObj
echo typeof myobj

# LFOrc

Implementation of lock-free OrcGC in pure nim

## Pos

Still in the middle of doing the raw implementations

ThreadIds: since am needing thread ids to be a index of an array, but am unsure of how that will work vis-a-vis threads being deleted/created, I'm making an atomic registry.

The issue will be that thread deallocations will also have to trigger the thread ID release procedure. Doing so would also require the thread to clean up their resources on the orc gc object. **A thread must not release its id until it has
cleared all of its resources on to ptp orc gc object**.

I have decided to use compare exchange operations on the thread ID get and release procedures because they are supported on a wider variety of cpu architectures.

The main thread setting up the GC must call the thread registry init and
ptporcgc init procedures.
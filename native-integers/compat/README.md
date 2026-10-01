`PrimitiveWordAdapters.v` relates the native API to `Gecko.Word`.
It is optional and excluded from the main library, which needs only Corelib
and Stdlib. Compile it with the fork and freshly rebuilt `Gecko.Word`, using
`-Q . Rocq.PrimitiveWords` for this directory.

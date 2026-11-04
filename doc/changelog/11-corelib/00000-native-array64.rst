- **Added:**
  The fork-specific ``Corelib.Array.PrimArray64`` primitive type with unsigned
  64-bit indices and checked persistent operations. ``Corelib.Array.Array64``
  provides slicing, range replacement, overlapping blits, filling, concatenation,
  and traversal operations over eagerly allocated dense storage. Existing
  primitive arrays retain their API and semantics. Rebuild dependencies for
  the fork's new compiled-object format, 90348.

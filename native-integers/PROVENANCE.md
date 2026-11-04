# Native integer source provenance

The Rocq integration and proof library originate in the six-width experiment
at revision `e370c7e7a9d71d3aae5c2a2924bb2b8868dff971`. The historical import
inventory is recorded in `source-manifest.json`; those hashes describe the
original inputs, not the subsequently maintained files.

The C boundary has been replaced with an implementation using the public
OCaml custom-block API. It stores width-distinct payloads with fixed canonical
serialization. Arithmetic uses standard OCaml integers and fixed Int64 limbs.
No compiler runtime implementation is bundled.

Rocq base: `d91dbf084f` (9.3), under the repository LICENSE.
Stdlib revision: `b1c45dfc593b83371bdc996376de5b4ed66c5085`, with its own LICENSE.

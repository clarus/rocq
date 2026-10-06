(************************************************************************)
(* Extraction support for the checked persistent 64-bit array API.      *)
(************************************************************************)

From Corelib.Array Require Import Array64.
From Corelib.extraction Require Import ExtrOcamlBasic.

Extract Constant Word64.word64 => "Primitive_words_runtime.Word64.t".
Extraction Inline Word64.word64.
Extract Constant Word64.eqb => "Primitive_words_runtime.Word64.equal".
Extract Constant Word64.leu => "Primitive_words_runtime.Word64.leb_unsigned".
Extract Constant Word64.add => "Primitive_words_runtime.Word64.add".
Extract Constant Word64.sub => "Primitive_words_runtime.Word64.sub".
Extract Constant Word64.lsr => "Primitive_words_runtime.Word64.shift_right_logical_word".

(** Inline type mappings name the constructor; extraction emits its argument. *)
Extract Constant PrimArray64.array "'a" => "Parray64.t".
Extraction Inline PrimArray64.array.
Extract Constant PrimArray64.empty => "Parray64.empty".
Extract Constant PrimArray64.repeat => "Parray64.repeat".
Extract Constant PrimArray64.length => "Parray64.length".
Extract Constant PrimArray64.get => "Parray64.get".
Extract Constant PrimArray64.set => "Parray64.set".
Extract Constant PrimArray64.slice => "Parray64.slice".
Extract Constant PrimArray64.replace => "Parray64.replace".
Extract Constant PrimArray64.concat => "Parray64.concat".

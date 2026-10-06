From Corelib.Array Require Import PrimArray64.

Open Scope word64_scope.

(* Exercise an eagerly allocated array beyond the legacy 4,194,303-element
   cap. Keep quotation small: this test measures the runtime representation. *)
Example beyond_legacy_cap :
  let a := repeat 4194305 7%nat in
  (length a, get a 4194304, get a 4194305) =
  (4194305%word64, Some 7%nat, @None nat).
Proof. vm_compute; reflexivity. Qed.

Example beyond_legacy_cap_cbv :
  let a := repeat 4194305 7%nat in
  (length a, get a 4194304) = (4194305%word64, Some 7%nat).
Proof. cbv; reflexivity. Qed.

Example beyond_legacy_cap_cbn :
  let a := repeat 4194305 7%nat in
  (length a, get a 4194304) = (4194305%word64, Some 7%nat).
Proof. cbn; reflexivity. Qed.

Example crossing_legacy_cap :
  let a := repeat 4194305 7%nat in
  match set a 4194303 42%nat with
  | Some b =>
      match slice b 4194302 3 with
      | Some s => (get s 0, get s 1, get s 2, get a 4194303)
      | None => (None, None, None, None)
      end
  | None => (None, None, None, None)
  end = (Some 7%nat, Some 42%nat, Some 7%nat, Some 7%nat).
Proof. vm_compute; reflexivity. Qed.

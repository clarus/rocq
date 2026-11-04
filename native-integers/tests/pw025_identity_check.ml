module W64 = Primitive_words_runtime.Word64
module W128 = Primitive_words_runtime.Word128
module W256 = Primitive_words_runtime.Word256

let require condition message = if not condition then failwith message

let () =
  let a128 = W128.of_limbs ~low:0x0123_4567_89ab_cdefL ~high:0x1122_3344_5566_7788L in
  let b128 = W128.of_limbs ~low:0x0123_4567_89ab_cdefL ~high:0x1122_3344_5566_7788L in
  let c128 = W128.of_limbs ~low:0x0123_4567_89ab_cdeeL ~high:0x1122_3344_5566_7788L in
  let a256 = W256.of_limbs ~limb0:1L ~limb1:2L ~limb2:3L ~limb3:4L in
  let b256 = W256.of_limbs ~limb0:1L ~limb1:2L ~limb2:3L ~limb3:4L in
  let c256 = W256.of_limbs ~limb0:1L ~limb1:2L ~limb2:3L ~limb3:5L in
  let t128 x = Constr.mkWord128 x and t256 x = Constr.mkWord256 x in
  require (Constr.equal (t128 a128) (t128 b128)) "Constr Word128 equal";
  require (not (Constr.equal (t128 a128) (t128 c128))) "Constr Word128 unequal";
  require (Constr.equal (t256 a256) (t256 b256)) "Constr Word256 equal";
  require (not (Constr.equal (t256 a256) (t256 c256))) "Constr Word256 unequal";
  require (not (Constr.equal (t128 a128) (t256 a256))) "Constr cross-width unequal";
  require (Termops.ConstrData.compare (t128 a128) (t128 b128) = 0) "Termops Word128 compare";
  require (Termops.ConstrData.compare (t256 a256) (t256 b256) = 0) "Termops Word256 compare";
  require (Termops.ConstrData.hash (t128 a128) = Termops.ConstrData.hash (t128 b128)) "Termops Word128 hash";
  require (Termops.ConstrData.hash (t256 a256) = Termops.ConstrData.hash (t256 b256)) "Termops Word256 hash";
  let const128 x = Vmvalues.Const_val (Vmvalues.val_of_word128 x) in
  let const256 x = Vmvalues.Const_val (Vmvalues.val_of_word256 x) in
  let const64 = Vmvalues.Const_val (Vmvalues.val_of_word64 W64.one) in
  let boxed64 = Vmvalues.Const_val (Obj.magic 1L) in
  require (Vmvalues.eq_structured_constant (const128 a128) (const128 b128))
    "VM Word128 custom equality";
  require (not (Vmvalues.eq_structured_constant (const128 a128) (const128 c128)))
    "VM Word128 custom inequality";
  require (Vmvalues.eq_structured_constant (const256 a256) (const256 b256))
    "VM Word256 custom equality";
  require (not (Vmvalues.eq_structured_constant (const256 a256) (const256 c256)))
    "VM Word256 custom inequality";
  require (not (Vmvalues.eq_structured_constant (const128 a128) (const256 a256)))
    "VM cross-wide custom inequality";
  require (not (Vmvalues.eq_structured_constant (const128 a128) const64))
    "VM Word128 versus Word64 inequality";
  require (not (Vmvalues.eq_structured_constant (const256 a256) boxed64))
    "VM Word256 versus boxed int64 inequality";
  print_endline "PW025 Constr equality/hash and VM custom-discriminator checks passed"

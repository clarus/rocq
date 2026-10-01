open PW032Extracted

let zs = Big_int_Z.string_of_big_int

let emit label index values =
  Printf.printf "%s\t%d\t%s\n" label index
    (String.concat "," (List.map zs values))

let emit_rows label rows = List.iteri (emit label) rows

let () =
  emit_rows "engine" pw032_engine_rows;
  emit_rows "normalized" pw032_normalized_rows;
  emit_rows "conversion" pw032_conversion_rows;
  emit_rows "cross" pw032_cross_rows;
  Printf.printf "polymorphic\t0\t%s\n"
    (String.concat "," (List.map string_of_bool pw032_polymorphic_checks))

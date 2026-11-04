module W = Primitive_words_runtime.Word8
let signed x = if x >= 128 then x - 256 else x
let expect label expected actual =
  if W.to_int actual <> expected land 255 then failwith label
let () =
  for x = 0 to 255 do
    let a = W.of_int x in
    for y = 0 to 255 do
      let b = W.of_int y in
      expect "add" (x + y) (W.add a b);
      expect "sub" (x - y) (W.sub a b);
      expect "mul" (x * y) (W.mul a b);
      expect "divu" (if y = 0 then 0 else x / y) (W.divu_total a b);
      expect "modu" (if y = 0 then x else x mod y) (W.modu_total a b);
      expect "divs" (if y = 0 then 0 else signed x / signed y) (W.divs_total a b);
      expect "rems" (if y = 0 then x else signed x mod signed y) (W.rems_total a b);
      expect "asr" (if y >= 8 then if x >= 128 then 255 else 0 else signed x asr y)
        (W.shift_right_arithmetic a b)
    done
  done;
  let module W = Primitive_words_runtime.Word16 in
  List.iter (fun x -> List.iter (fun y ->
    let a, b = W.of_int x, W.of_int y in
    assert (W.to_int (W.mul a b) = Int64.to_int (Int64.logand (Int64.mul (Int64.of_int x) (Int64.of_int y)) 65535L));
    assert (W.to_int (W.add a b) = (x + y) land 65535)
  ) [0;1;32767;32768;65535]) [0;1;32767;32768;65535];
  print_endline "portable_small_arithmetic=passed"

/* Width-distinct primitive words using the public OCaml custom-block API.
   Arithmetic lives in primitive_words_runtime.ml. */
#include <stdint.h>
#include <string.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/intext.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

_Static_assert(sizeof(uint64_t) == 8, "64-bit limbs required");
_Static_assert(sizeof(uint32_t) == 4, "32-bit words required");

static uint64_t read_limb(value v, unsigned bytes, unsigned index) {
  uint64_t n = 0;
  const unsigned char *p = (const unsigned char *)Data_custom_val(v);
  if (bytes == 1) { uint8_t x; memcpy(&x,p,1); n=x; }
  else if (bytes == 2) { uint16_t x; memcpy(&x,p,2); n=x; }
  else if (bytes == 4) { uint32_t x; memcpy(&x,p,4); n=x; }
  else memcpy(&n,p+8*index,8);
  return n;
}
static void write_limb(void *data, unsigned bytes, unsigned index, uint64_t n) {
  unsigned char *p = data;
  if (bytes == 1) { uint8_t x=(uint8_t)n; memcpy(p,&x,1); }
  else if (bytes == 2) { uint16_t x=(uint16_t)n; memcpy(p,&x,2); }
  else if (bytes == 4) { uint32_t x=(uint32_t)n; memcpy(p,&x,4); }
  else memcpy(p+8*index,&n,8);
}

static int compare_word8(value a, value b) {
  for (unsigned i=1; i>0; --i) {
    uint64_t x=read_limb(a,1,i-1), y=read_limb(b,1,i-1);
    if (x!=y) return x<y ? -1 : 1;
  }
  return 0;
}
static intnat hash_word8(value v) {
  uint32_t h=0;
  for (unsigned i=0;i<1;++i) { uint64_t x=read_limb(v,1,i); h^=(uint32_t)x ^ (uint32_t)(x>>32); }
  return (intnat)h;
}
static void serialize_word8(value v, uintnat *a, uintnat *b) {
  for (unsigned i=1;i>0;--i) caml_serialize_int_1((int8_t)read_limb(v,1,i-1));
  *a=*b=1;
}
static uintnat deserialize_word8(void *p) {
  for (unsigned i=1;i>0;--i) write_limb(p,1,i-1,(uint64_t)caml_deserialize_sint_1());
  return 1;
}
static const struct custom_fixed_length length_word8 = { 1, 1 };
static const struct custom_operations ops_word8 = {
  "_gecko_primitive_words_word8_v1", custom_finalize_default,
  compare_word8, hash_word8, serialize_word8, deserialize_word8,
  custom_compare_ext_default, &length_word8
};
static int valid_word8(value v) {
  return Is_block(v) && Tag_val(v)==Custom_tag &&
    Wosize_val(v)==1+(1+sizeof(value)-1)/sizeof(value) && Custom_ops_val(v)==&ops_word8;
}
CAMLprim value rocq_primitive_word8_register(value u) {
  (void)u; caml_register_custom_operations(&ops_word8); return Val_unit;
}
CAMLprim value rocq_primitive_word8_identifier(value u) {
  (void)u; return caml_copy_string(ops_word8.identifier);
}
CAMLprim value rocq_primitive_word8_is_runtime_value(value v) { return Val_bool(valid_word8(v)); }
CAMLprim value rocq_primitive_word8_of_int8_bytecode(value v0) {
  CAMLparam1(v0); CAMLlocal1(result);
  uint64_t x0=(uint64_t)Int_val(v0);
  result=caml_alloc_custom(&ops_word8,1,0,1);
  write_limb(Data_custom_val(result),1,0,x0);
  CAMLreturn(result);
}
CAMLprim value rocq_primitive_word8_to_int8_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word8(v)) caml_invalid_argument("Primitive word8 runtime value expected");
  int8_t x=(int8_t)read_limb(v,1,0);
  CAMLreturn(Val_int(x));
}

static int compare_word16(value a, value b) {
  for (unsigned i=1; i>0; --i) {
    uint64_t x=read_limb(a,2,i-1), y=read_limb(b,2,i-1);
    if (x!=y) return x<y ? -1 : 1;
  }
  return 0;
}
static intnat hash_word16(value v) {
  uint32_t h=0;
  for (unsigned i=0;i<1;++i) { uint64_t x=read_limb(v,2,i); h^=(uint32_t)x ^ (uint32_t)(x>>32); }
  return (intnat)h;
}
static void serialize_word16(value v, uintnat *a, uintnat *b) {
  for (unsigned i=1;i>0;--i) caml_serialize_int_2((int16_t)read_limb(v,2,i-1));
  *a=*b=2;
}
static uintnat deserialize_word16(void *p) {
  for (unsigned i=1;i>0;--i) write_limb(p,2,i-1,(uint64_t)caml_deserialize_sint_2());
  return 2;
}
static const struct custom_fixed_length length_word16 = { 2, 2 };
static const struct custom_operations ops_word16 = {
  "_gecko_primitive_words_word16_v1", custom_finalize_default,
  compare_word16, hash_word16, serialize_word16, deserialize_word16,
  custom_compare_ext_default, &length_word16
};
static int valid_word16(value v) {
  return Is_block(v) && Tag_val(v)==Custom_tag &&
    Wosize_val(v)==1+(2+sizeof(value)-1)/sizeof(value) && Custom_ops_val(v)==&ops_word16;
}
CAMLprim value rocq_primitive_word16_register(value u) {
  (void)u; caml_register_custom_operations(&ops_word16); return Val_unit;
}
CAMLprim value rocq_primitive_word16_identifier(value u) {
  (void)u; return caml_copy_string(ops_word16.identifier);
}
CAMLprim value rocq_primitive_word16_is_runtime_value(value v) { return Val_bool(valid_word16(v)); }
CAMLprim value rocq_primitive_word16_of_int16_bytecode(value v0) {
  CAMLparam1(v0); CAMLlocal1(result);
  uint64_t x0=(uint64_t)Int_val(v0);
  result=caml_alloc_custom(&ops_word16,2,0,1);
  write_limb(Data_custom_val(result),2,0,x0);
  CAMLreturn(result);
}
CAMLprim value rocq_primitive_word16_to_int16_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word16(v)) caml_invalid_argument("Primitive word16 runtime value expected");
  int16_t x=(int16_t)read_limb(v,2,0);
  CAMLreturn(Val_int(x));
}

static int compare_word32(value a, value b) {
  for (unsigned i=1; i>0; --i) {
    uint64_t x=read_limb(a,4,i-1), y=read_limb(b,4,i-1);
    if (x!=y) return x<y ? -1 : 1;
  }
  return 0;
}
static intnat hash_word32(value v) {
  uint32_t h=0;
  for (unsigned i=0;i<1;++i) { uint64_t x=read_limb(v,4,i); h^=(uint32_t)x ^ (uint32_t)(x>>32); }
  return (intnat)h;
}
static void serialize_word32(value v, uintnat *a, uintnat *b) {
  for (unsigned i=1;i>0;--i) caml_serialize_int_4((int32_t)read_limb(v,4,i-1));
  *a=*b=4;
}
static uintnat deserialize_word32(void *p) {
  for (unsigned i=1;i>0;--i) write_limb(p,4,i-1,(uint64_t)caml_deserialize_sint_4());
  return 4;
}
static const struct custom_fixed_length length_word32 = { 4, 4 };
static const struct custom_operations ops_word32 = {
  "_gecko_primitive_words_word32_v1", custom_finalize_default,
  compare_word32, hash_word32, serialize_word32, deserialize_word32,
  custom_compare_ext_default, &length_word32
};
static int valid_word32(value v) {
  return Is_block(v) && Tag_val(v)==Custom_tag &&
    Wosize_val(v)==1+(4+sizeof(value)-1)/sizeof(value) && Custom_ops_val(v)==&ops_word32;
}
CAMLprim value rocq_primitive_word32_register(value u) {
  (void)u; caml_register_custom_operations(&ops_word32); return Val_unit;
}
CAMLprim value rocq_primitive_word32_identifier(value u) {
  (void)u; return caml_copy_string(ops_word32.identifier);
}
CAMLprim value rocq_primitive_word32_is_runtime_value(value v) { return Val_bool(valid_word32(v)); }
CAMLprim value rocq_primitive_word32_of_int32_bytecode(value v0) {
  CAMLparam1(v0); CAMLlocal1(result);
  uint64_t x0=(uint64_t)Int32_val(v0);
  result=caml_alloc_custom(&ops_word32,4,0,1);
  write_limb(Data_custom_val(result),4,0,x0);
  CAMLreturn(result);
}
CAMLprim value rocq_primitive_word32_to_int32_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word32(v)) caml_invalid_argument("Primitive word32 runtime value expected");
  int32_t x=(int32_t)read_limb(v,4,0);
  CAMLreturn(caml_copy_int32(x));
}

static int compare_word64(value a, value b) {
  for (unsigned i=1; i>0; --i) {
    uint64_t x=read_limb(a,8,i-1), y=read_limb(b,8,i-1);
    if (x!=y) return x<y ? -1 : 1;
  }
  return 0;
}
static intnat hash_word64(value v) {
  uint32_t h=0;
  for (unsigned i=0;i<1;++i) { uint64_t x=read_limb(v,8,i); h^=(uint32_t)x ^ (uint32_t)(x>>32); }
  return (intnat)h;
}
static void serialize_word64(value v, uintnat *a, uintnat *b) {
  for (unsigned i=1;i>0;--i) caml_serialize_int_8((int64_t)read_limb(v,8,i-1));
  *a=*b=8;
}
static uintnat deserialize_word64(void *p) {
  for (unsigned i=1;i>0;--i) write_limb(p,8,i-1,(uint64_t)caml_deserialize_sint_8());
  return 8;
}
static const struct custom_fixed_length length_word64 = { 8, 8 };
static const struct custom_operations ops_word64 = {
  "_gecko_primitive_words_word64_v1", custom_finalize_default,
  compare_word64, hash_word64, serialize_word64, deserialize_word64,
  custom_compare_ext_default, &length_word64
};
static int valid_word64(value v) {
  return Is_block(v) && Tag_val(v)==Custom_tag &&
    Wosize_val(v)==1+(8+sizeof(value)-1)/sizeof(value) && Custom_ops_val(v)==&ops_word64;
}
CAMLprim value rocq_primitive_word64_register(value u) {
  (void)u; caml_register_custom_operations(&ops_word64); return Val_unit;
}
CAMLprim value rocq_primitive_word64_identifier(value u) {
  (void)u; return caml_copy_string(ops_word64.identifier);
}
CAMLprim value rocq_primitive_word64_is_runtime_value(value v) { return Val_bool(valid_word64(v)); }
CAMLprim value rocq_primitive_word64_of_int64_bytecode(value v0) {
  CAMLparam1(v0); CAMLlocal1(result);
  uint64_t x0=(uint64_t)Int64_val(v0);
  result=caml_alloc_custom(&ops_word64,8,0,1);
  write_limb(Data_custom_val(result),8,0,x0);
  CAMLreturn(result);
}
CAMLprim value rocq_primitive_word64_to_int64_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word64(v)) caml_invalid_argument("Primitive word64 runtime value expected");
  int64_t x=(int64_t)read_limb(v,8,0);
  CAMLreturn(caml_copy_int64(x));
}

static int compare_word128(value a, value b) {
  for (unsigned i=2; i>0; --i) {
    uint64_t x=read_limb(a,16,i-1), y=read_limb(b,16,i-1);
    if (x!=y) return x<y ? -1 : 1;
  }
  return 0;
}
static intnat hash_word128(value v) {
  uint32_t h=0;
  for (unsigned i=0;i<2;++i) { uint64_t x=read_limb(v,16,i); h^=(uint32_t)x ^ (uint32_t)(x>>32); }
  return (intnat)h;
}
static void serialize_word128(value v, uintnat *a, uintnat *b) {
  for (unsigned i=2;i>0;--i) caml_serialize_int_8((int64_t)read_limb(v,16,i-1));
  *a=*b=16;
}
static uintnat deserialize_word128(void *p) {
  for (unsigned i=2;i>0;--i) write_limb(p,16,i-1,(uint64_t)caml_deserialize_sint_8());
  return 16;
}
static const struct custom_fixed_length length_word128 = { 16, 16 };
static const struct custom_operations ops_word128 = {
  "_gecko_primitive_words_word128_v1", custom_finalize_default,
  compare_word128, hash_word128, serialize_word128, deserialize_word128,
  custom_compare_ext_default, &length_word128
};
static int valid_word128(value v) {
  return Is_block(v) && Tag_val(v)==Custom_tag &&
    Wosize_val(v)==1+(16+sizeof(value)-1)/sizeof(value) && Custom_ops_val(v)==&ops_word128;
}
CAMLprim value rocq_primitive_word128_register(value u) {
  (void)u; caml_register_custom_operations(&ops_word128); return Val_unit;
}
CAMLprim value rocq_primitive_word128_identifier(value u) {
  (void)u; return caml_copy_string(ops_word128.identifier);
}
CAMLprim value rocq_primitive_word128_is_runtime_value(value v) { return Val_bool(valid_word128(v)); }
CAMLprim value rocq_primitive_word128_of_limbs_bytecode(value v0, value v1) {
  CAMLparam2(v0,v1); CAMLlocal1(result);
  uint64_t x0=(uint64_t)Int64_val(v0);
  uint64_t x1=(uint64_t)Int64_val(v1);
  result=caml_alloc_custom(&ops_word128,16,0,1);
  write_limb(Data_custom_val(result),16,0,x0);
  write_limb(Data_custom_val(result),16,1,x1);
  CAMLreturn(result);
}
CAMLprim value rocq_primitive_word128_low_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word128(v)) caml_invalid_argument("Primitive word128 runtime value expected");
  int64_t x=(int64_t)read_limb(v,16,0);
  CAMLreturn(caml_copy_int64(x));
}
CAMLprim value rocq_primitive_word128_high_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word128(v)) caml_invalid_argument("Primitive word128 runtime value expected");
  int64_t x=(int64_t)read_limb(v,16,1);
  CAMLreturn(caml_copy_int64(x));
}

static int compare_word256(value a, value b) {
  for (unsigned i=4; i>0; --i) {
    uint64_t x=read_limb(a,32,i-1), y=read_limb(b,32,i-1);
    if (x!=y) return x<y ? -1 : 1;
  }
  return 0;
}
static intnat hash_word256(value v) {
  uint32_t h=0;
  for (unsigned i=0;i<4;++i) { uint64_t x=read_limb(v,32,i); h^=(uint32_t)x ^ (uint32_t)(x>>32); }
  return (intnat)h;
}
static void serialize_word256(value v, uintnat *a, uintnat *b) {
  for (unsigned i=4;i>0;--i) caml_serialize_int_8((int64_t)read_limb(v,32,i-1));
  *a=*b=32;
}
static uintnat deserialize_word256(void *p) {
  for (unsigned i=4;i>0;--i) write_limb(p,32,i-1,(uint64_t)caml_deserialize_sint_8());
  return 32;
}
static const struct custom_fixed_length length_word256 = { 32, 32 };
static const struct custom_operations ops_word256 = {
  "_gecko_primitive_words_word256_v1", custom_finalize_default,
  compare_word256, hash_word256, serialize_word256, deserialize_word256,
  custom_compare_ext_default, &length_word256
};
static int valid_word256(value v) {
  return Is_block(v) && Tag_val(v)==Custom_tag &&
    Wosize_val(v)==1+(32+sizeof(value)-1)/sizeof(value) && Custom_ops_val(v)==&ops_word256;
}
CAMLprim value rocq_primitive_word256_register(value u) {
  (void)u; caml_register_custom_operations(&ops_word256); return Val_unit;
}
CAMLprim value rocq_primitive_word256_identifier(value u) {
  (void)u; return caml_copy_string(ops_word256.identifier);
}
CAMLprim value rocq_primitive_word256_is_runtime_value(value v) { return Val_bool(valid_word256(v)); }
CAMLprim value rocq_primitive_word256_of_limbs_bytecode(value v0, value v1, value v2, value v3) {
  CAMLparam4(v0,v1,v2,v3); CAMLlocal1(result);
  uint64_t x0=(uint64_t)Int64_val(v0);
  uint64_t x1=(uint64_t)Int64_val(v1);
  uint64_t x2=(uint64_t)Int64_val(v2);
  uint64_t x3=(uint64_t)Int64_val(v3);
  result=caml_alloc_custom(&ops_word256,32,0,1);
  write_limb(Data_custom_val(result),32,0,x0);
  write_limb(Data_custom_val(result),32,1,x1);
  write_limb(Data_custom_val(result),32,2,x2);
  write_limb(Data_custom_val(result),32,3,x3);
  CAMLreturn(result);
}
CAMLprim value rocq_primitive_word256_limb0_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word256(v)) caml_invalid_argument("Primitive word256 runtime value expected");
  int64_t x=(int64_t)read_limb(v,32,0);
  CAMLreturn(caml_copy_int64(x));
}
CAMLprim value rocq_primitive_word256_limb1_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word256(v)) caml_invalid_argument("Primitive word256 runtime value expected");
  int64_t x=(int64_t)read_limb(v,32,1);
  CAMLreturn(caml_copy_int64(x));
}
CAMLprim value rocq_primitive_word256_limb2_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word256(v)) caml_invalid_argument("Primitive word256 runtime value expected");
  int64_t x=(int64_t)read_limb(v,32,2);
  CAMLreturn(caml_copy_int64(x));
}
CAMLprim value rocq_primitive_word256_limb3_bytecode(value v) {
  CAMLparam1(v);
  if (!valid_word256(v)) caml_invalid_argument("Primitive word256 runtime value expected");
  int64_t x=(int64_t)read_limb(v,32,3);
  CAMLreturn(caml_copy_int64(x));
}

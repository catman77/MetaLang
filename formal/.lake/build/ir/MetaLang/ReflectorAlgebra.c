// Lean compiler output
// Module: MetaLang.ReflectorAlgebra
// Imports: public import Init public import MetaLang.Reflection
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_cFun___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_cFun___closed__0;
static lean_once_cell_t lp_MetaLang_MetaLang_cFun___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_cFun___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_cFun(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_cFun___boxed(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_dFun___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_dFun___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_dFun(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_dFun___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_cOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_cFun___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_cOp___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_cOp___closed__0_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_cOp = (const lean_object*)&lp_MetaLang_MetaLang_cOp___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_dOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_dFun___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_dOp___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_dOp___closed__0_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_dOp = (const lean_object*)&lp_MetaLang_MetaLang_dOp___closed__0_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_inc(x_1);
x_8 = lp_MetaLang_MetaLang_iter___redArg(x_1, x_7, x_3);
lean_dec(x_7);
x_9 = lean_apply_1(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_MetaLang_iter___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_MetaLang_iter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_iter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_MetaLang_iter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_cFun___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_cFun___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_cFun(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_cFun___closed__0, &lp_MetaLang_MetaLang_cFun___closed__0_once, _init_lp_MetaLang_MetaLang_cFun___closed__0);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_cFun___closed__1, &lp_MetaLang_MetaLang_cFun___closed__1_once, _init_lp_MetaLang_MetaLang_cFun___closed__1);
return x_4;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_cFun___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_cFun(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_dFun___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_dFun(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_dFun___closed__0, &lp_MetaLang_MetaLang_dFun___closed__0_once, _init_lp_MetaLang_MetaLang_dFun___closed__0);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_cFun___closed__1, &lp_MetaLang_MetaLang_cFun___closed__1_once, _init_lp_MetaLang_MetaLang_cFun___closed__1);
return x_4;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_dFun___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_dFun(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Reflection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_ReflectorAlgebra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Reflection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

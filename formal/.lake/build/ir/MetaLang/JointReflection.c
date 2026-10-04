// Lean compiler output
// Module: MetaLang.JointReflection
// Imports: public import Init public import MetaLang.ReflectionTheory public import MetaLang.ReflectorAlgebra
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
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_principalClosure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_principalClosure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_principalClosure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Feedback_fC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Feedback_fC___closed__0;
static lean_once_cell_t lp_MetaLang_MetaLang_Feedback_fC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Feedback_fC___closed__1;
static lean_once_cell_t lp_MetaLang_MetaLang_Feedback_fC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Feedback_fC___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fC(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fC___boxed(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Feedback_fD___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Feedback_fD___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fD(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fD___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Feedback_C___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Feedback_fC___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Feedback_C___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Feedback_C___closed__0_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Feedback_C = (const lean_object*)&lp_MetaLang_MetaLang_Feedback_C___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_Feedback_D___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Feedback_fD___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Feedback_D___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Feedback_D___closed__0_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Feedback_D = (const lean_object*)&lp_MetaLang_MetaLang_Feedback_D___closed__0_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_principalClosure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_principalClosure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_principalClosure___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_principalClosure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_MetaLang_principalClosure___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_leftOp___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_leftOp___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_leftOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_leftOp(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_rightOp___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_rightOp___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_rightOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_rightOp(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Feedback_fC___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Feedback_fC___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Feedback_fC___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fC(lean_object* x_1) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
goto block_3;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 1)
{
lean_dec(x_9);
goto block_3;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_6);
if (x_12 == 1)
{
lean_dec(x_11);
goto block_5;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_nat_sub(x_11, x_8);
lean_dec(x_11);
x_14 = lean_nat_dec_eq(x_13, x_6);
if (x_14 == 1)
{
lean_dec(x_13);
goto block_5;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_nat_sub(x_13, x_8);
lean_dec(x_13);
x_16 = lean_nat_dec_eq(x_15, x_6);
lean_dec(x_15);
x_17 = lean_obj_once(&lp_MetaLang_MetaLang_Feedback_fC___closed__2, &lp_MetaLang_MetaLang_Feedback_fC___closed__2_once, _init_lp_MetaLang_MetaLang_Feedback_fC___closed__2);
return x_17;
}
}
}
}
block_3:
{
lean_object* x_2; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_Feedback_fC___closed__0, &lp_MetaLang_MetaLang_Feedback_fC___closed__0_once, _init_lp_MetaLang_MetaLang_Feedback_fC___closed__0);
return x_2;
}
block_5:
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Feedback_fC___closed__1, &lp_MetaLang_MetaLang_Feedback_fC___closed__1_once, _init_lp_MetaLang_MetaLang_Feedback_fC___closed__1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Feedback_fC(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Feedback_fD___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fD(lean_object* x_1) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
goto block_3;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 1)
{
lean_dec(x_9);
goto block_3;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_6);
if (x_12 == 1)
{
lean_dec(x_11);
goto block_3;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_nat_sub(x_11, x_8);
lean_dec(x_11);
x_14 = lean_nat_dec_eq(x_13, x_6);
if (x_14 == 1)
{
lean_dec(x_13);
goto block_5;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_nat_sub(x_13, x_8);
lean_dec(x_13);
x_16 = lean_nat_dec_eq(x_15, x_6);
lean_dec(x_15);
goto block_5;
}
}
}
}
block_3:
{
lean_object* x_2; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_Feedback_fD___closed__0, &lp_MetaLang_MetaLang_Feedback_fD___closed__0_once, _init_lp_MetaLang_MetaLang_Feedback_fD___closed__0);
return x_2;
}
block_5:
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Feedback_fC___closed__2, &lp_MetaLang_MetaLang_Feedback_fC___closed__2_once, _init_lp_MetaLang_MetaLang_Feedback_fC___closed__2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Feedback_fD___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Feedback_fD(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ReflectionTheory(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ReflectorAlgebra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_JointReflection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ReflectionTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ReflectorAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: MetaLang.AlgebraicDescent
// Imports: public import Init public import MetaLang.MeaningAlgebra public import MetaLang.Descent
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
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_NoDescent_opAnd(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_NoDescent_opAnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_var_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_oplus_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_oplus_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ominus_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ominus_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_rho_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_rho_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm_default___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_eval___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_AlgebraicDescent_0__MetaLang_Term_eval_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_AlgebraicDescent_0__MetaLang_Term_eval_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_ProductCounter_crossAtlas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_ProductCounter_crossAtlas___closed__0_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas = (const lean_object*)&lp_MetaLang_MetaLang_ProductCounter_crossAtlas___closed__0_value;
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_NoDescent_opAnd(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_NoDescent_opAnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_MetaLang_MetaLang_NoDescent_opAnd(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Term_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Term_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Term_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Term_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_oplus_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_oplus_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ominus_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_ominus_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_rho_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_rho_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Term_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_instInhabitedTerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_eval___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_inc(x_2);
lean_inc_ref(x_1);
x_9 = lp_MetaLang_MetaLang_Term_eval___redArg(x_1, x_2, x_6);
x_10 = lp_MetaLang_MetaLang_Term_eval___redArg(x_1, x_2, x_7);
x_11 = lean_apply_2(x_8, x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_2);
lean_inc_ref(x_1);
x_15 = lp_MetaLang_MetaLang_Term_eval___redArg(x_1, x_2, x_12);
x_16 = lp_MetaLang_MetaLang_Term_eval___redArg(x_1, x_2, x_13);
x_17 = lean_apply_2(x_14, x_15, x_16);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lp_MetaLang_MetaLang_Term_eval___redArg(x_1, x_2, x_18);
x_21 = lean_apply_1(x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Term_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Term_eval___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_AlgebraicDescent_0__MetaLang_Term_eval_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_3, x_8, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_apply_1(x_5, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_AlgebraicDescent_0__MetaLang_Term_eval_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
x_12 = lean_apply_2(x_5, x_10, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_3);
x_15 = lean_apply_2(x_6, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = lean_apply_1(x_7, x_16);
return x_17;
}
}
}
}
static lean_object* _init_lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_obj_once(&lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___closed__0, &lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___closed__0_once, _init_lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___closed__0);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_MetaLang_ProductCounter_crossAtlas___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_MeaningAlgebra(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Descent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_AlgebraicDescent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_MeaningAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Descent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

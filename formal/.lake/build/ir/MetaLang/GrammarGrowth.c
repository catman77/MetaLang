// Lean compiler output
// Module: MetaLang.GrammarGrowth
// Imports: public import Init public import MetaLang.OperationalAlgebra
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
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__0;
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__1;
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__2;
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__3;
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_GrammarGrowth_decoy(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_GrammarGrowth_decoy___boxed(lean_object*);
static lean_object* _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lp_mathlib_ZMod_commRing(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__0, &lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__0_once, _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__0);
x_2 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__1, &lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__1_once, _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__1);
x_2 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__2, &lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__2_once, _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__2);
x_2 = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_GrammarGrowth_decoy(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
x_2 = x_8;
goto block_7;
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__3, &lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__3_once, _init_lp_MetaLang_MetaLang_GrammarGrowth_decoy___closed__3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lp_mathlib_ZMod_decidableEq(x_3, x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_GrammarGrowth_decoy___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_GrammarGrowth_decoy(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_OperationalAlgebra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_GrammarGrowth(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_OperationalAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

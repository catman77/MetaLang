// Lean compiler output
// Module: MetaLang.LanguageGrowth
// Imports: public import Init public import MetaLang.Gluing public import MetaLang.InternalLanguage
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
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2080___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2080(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2081___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2081(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2082(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2082___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Admissible_witness;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2080___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_apply_2(x_3, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2080(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Growth_TwoStep_m_u2080___lam__0), 5, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2081___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2081(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Growth_TwoStep_m_u2081___lam__0), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Growth_TwoStep_m_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Growth_TwoStep_m_u2082(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Admissible_witness(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Gluing(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_InternalLanguage(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_LanguageGrowth(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Gluing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_InternalLanguage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_MetaLang_MetaLang_Admissible_witness = _init_lp_MetaLang_MetaLang_Admissible_witness();
lean_mark_persistent(lp_MetaLang_MetaLang_Admissible_witness);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

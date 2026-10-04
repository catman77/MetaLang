// Lean compiler output
// Module: MetaLang.Boundary
// Imports: public import Init public import MetaLang.InternalLanguage public import Mathlib
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
lean_object* lp_MetaLang_MetaLang_Machine_transport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_utilityOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_commonCause___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_commonCause___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_commonCause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_commonCause___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_commonCause___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_commonCause___closed__0_value;
static lean_once_cell_t lp_MetaLang_MetaLang_commonCause___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_commonCause___closed__1;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_commonCause;
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_realChannel___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_realChannel___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_realChannel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_realChannel___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_realChannel___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_realChannel___closed__0_value;
static lean_once_cell_t lp_MetaLang_MetaLang_realChannel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_realChannel___closed__1;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_realChannel;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_utilityOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lp_MetaLang_MetaLang_Machine_transport(x_1, x_2, x_4);
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_commonCause___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_commonCause___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_MetaLang_MetaLang_commonCause___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_commonCause___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(lp_MetaLang_MetaLang_commonCause___closed__0));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_commonCause(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_commonCause___closed__1, &lp_MetaLang_MetaLang_commonCause___closed__1_once, _init_lp_MetaLang_MetaLang_commonCause___closed__1);
return x_1;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_realChannel___lam__0(lean_object* x_1, uint8_t x_2) {
_start:
{
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_realChannel___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = lp_MetaLang_MetaLang_realChannel___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_realChannel___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(lp_MetaLang_MetaLang_realChannel___closed__0));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_realChannel(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_realChannel___closed__1, &lp_MetaLang_MetaLang_realChannel___closed__1_once, _init_lp_MetaLang_MetaLang_realChannel___closed__1);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_InternalLanguage(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_Boundary(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_InternalLanguage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_MetaLang_MetaLang_commonCause = _init_lp_MetaLang_MetaLang_commonCause();
lean_mark_persistent(lp_MetaLang_MetaLang_commonCause);
lp_MetaLang_MetaLang_realChannel = _init_lp_MetaLang_MetaLang_realChannel();
lean_mark_persistent(lp_MetaLang_MetaLang_realChannel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: MetaLang.CollapseBridge
// Imports: public import Init public import MetaLang.ASCTopology
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Machine_chainR(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainR___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Machine_chainMachine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Machine_chainT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Machine_chainMachine___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Machine_chainMachine___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_Machine_chainMachine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Machine_chainR___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Machine_chainMachine___closed__1 = (const lean_object*)&lp_MetaLang_MetaLang_Machine_chainMachine___closed__1_value;
static const lean_ctor_object lp_MetaLang_MetaLang_Machine_chainMachine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_MetaLang_MetaLang_Machine_chainMachine___closed__0_value),((lean_object*)&lp_MetaLang_MetaLang_Machine_chainMachine___closed__1_value)}};
static const lean_object* lp_MetaLang_MetaLang_Machine_chainMachine___closed__2 = (const lean_object*)&lp_MetaLang_MetaLang_Machine_chainMachine___closed__2_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Machine_chainMachine = (const lean_object*)&lp_MetaLang_MetaLang_Machine_chainMachine___closed__2_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_unsigned_to_nat(5u);
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Machine_chainT___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Machine_chainT___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainT___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Machine_chainT(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Machine_chainR(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Machine_chainR___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_Machine_chainR(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ASCTopology(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_CollapseBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ASCTopology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

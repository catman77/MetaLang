// Lean compiler output
// Module: MetaLang.AuditM7
// Imports: public import Init public import MetaLang.Audit public import MetaLang.ASCTopology public import MetaLang.CollapseBridge public import MetaLang.RefinementOrder public import MetaLang.Reflection public import MetaLang.ReflectorAlgebra public import MetaLang.ConstraintLogic public import MetaLang.TheorySpace public import MetaLang.Descent
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
static const lean_ctor_object lp_MetaLang_MetaLang_AuditM7_ladderAudit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(3, 3, 3, 3, 3, 3, 3, 3),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_MetaLang_MetaLang_AuditM7_ladderAudit___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_AuditM7_ladderAudit___closed__0_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_AuditM7_ladderAudit = (const lean_object*)&lp_MetaLang_MetaLang_AuditM7_ladderAudit___closed__0_value;
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Audit(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ASCTopology(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_CollapseBridge(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_RefinementOrder(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Reflection(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ReflectorAlgebra(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ConstraintLogic(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_TheorySpace(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Descent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_AuditM7(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Audit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ASCTopology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_CollapseBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_RefinementOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Reflection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ReflectorAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ConstraintLogic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_TheorySpace(builtin);
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

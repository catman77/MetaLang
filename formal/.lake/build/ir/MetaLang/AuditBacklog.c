// Lean compiler output
// Module: MetaLang.AuditBacklog
// Imports: public import Init public import MetaLang.AuditM9 public import MetaLang.AtlasCocycle public import MetaLang.Gluing public import MetaLang.ReflectionTheory public import MetaLang.JointReflection public import MetaLang.ConditionLogic public import MetaLang.FilterLogic public import MetaLang.TheoryPresentation public import MetaLang.BoundaryObject public import MetaLang.GrammarGrowth public import MetaLang.SourceFilterLogic public import MetaLang.LanguageGrowth
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AuditM9(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AtlasCocycle(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Gluing(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ReflectionTheory(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_JointReflection(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ConditionLogic(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_FilterLogic(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_TheoryPresentation(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_BoundaryObject(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_GrammarGrowth(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_SourceFilterLogic(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_LanguageGrowth(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_AuditBacklog(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AuditM9(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AtlasCocycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Gluing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ReflectionTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_JointReflection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ConditionLogic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_FilterLogic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_TheoryPresentation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_BoundaryObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_GrammarGrowth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_SourceFilterLogic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_LanguageGrowth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

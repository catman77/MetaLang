// Lean compiler output
// Module: MetaLang.Countermodels
// Imports: public import Init public import MetaLang.Observer public import MetaLang.Singularity public import MetaLang.ObservationDiagram public import MetaLang.OperationalEquiv public import MetaLang.SelfReference public import MetaLang.Boundary public import MetaLang.SeparationCover
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
lean_object* initialize_MetaLang_MetaLang_Observer(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Singularity(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ObservationDiagram(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_OperationalEquiv(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_SelfReference(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Boundary(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_SeparationCover(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_Countermodels(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Observer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Singularity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_ObservationDiagram(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_OperationalEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_SelfReference(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Boundary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_SeparationCover(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

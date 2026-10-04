// Lean compiler output
// Module: MetaLang
// Imports: public import Init public import MetaLang.Continuation public import MetaLang.Grammar public import MetaLang.Congruence public import MetaLang.InternalLanguage public import MetaLang.Observer public import MetaLang.Singularity public import MetaLang.ObservationDiagram public import MetaLang.Q8D8 public import MetaLang.OperationalEquiv public import MetaLang.SelfReference public import MetaLang.Boundary public import MetaLang.Countermodels public import MetaLang.Audit public import MetaLang.ASCTopology public import MetaLang.CollapseBridge public import MetaLang.RefinementOrder public import MetaLang.Reflection public import MetaLang.ReflectorAlgebra public import MetaLang.ConstraintLogic public import MetaLang.TheorySpace public import MetaLang.Descent public import MetaLang.AuditM7 public import MetaLang.MeaningAlgebra public import MetaLang.AlgebraicDescent public import MetaLang.MeaningWitnesses public import MetaLang.AuditM8 public import MetaLang.Projection public import MetaLang.MultiObserver public import MetaLang.OperationalAlgebra public import MetaLang.AuditM9 public import MetaLang.AtlasCocycle public import MetaLang.AuditBacklog public import MetaLang.Gluing public import MetaLang.ReflectionTheory public import MetaLang.JointReflection public import MetaLang.ConditionLogic public import MetaLang.FilterLogic public import MetaLang.TheoryPresentation public import MetaLang.BoundaryObject public import MetaLang.GrammarGrowth public import MetaLang.SourceFilterLogic public import MetaLang.LanguageGrowth public import MetaLang.SeparationCover
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
lean_object* initialize_MetaLang_MetaLang_Continuation(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Grammar(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Congruence(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_InternalLanguage(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Observer(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Singularity(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ObservationDiagram(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Q8D8(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_OperationalEquiv(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_SelfReference(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Boundary(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Countermodels(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Audit(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ASCTopology(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_CollapseBridge(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_RefinementOrder(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Reflection(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ReflectorAlgebra(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_ConstraintLogic(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_TheorySpace(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Descent(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AuditM7(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_MeaningAlgebra(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AlgebraicDescent(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_MeaningWitnesses(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AuditM8(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Projection(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_MultiObserver(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_OperationalAlgebra(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AuditM9(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AtlasCocycle(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AuditBacklog(uint8_t builtin);
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
lean_object* initialize_MetaLang_MetaLang_SeparationCover(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Continuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Congruence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_InternalLanguage(builtin);
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
res = initialize_MetaLang_MetaLang_Q8D8(builtin);
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
res = initialize_MetaLang_MetaLang_Countermodels(builtin);
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
res = initialize_MetaLang_MetaLang_AuditM7(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_MeaningAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AlgebraicDescent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_MeaningWitnesses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AuditM8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Projection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_MultiObserver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_OperationalAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AuditM9(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AtlasCocycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AuditBacklog(builtin);
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
res = initialize_MetaLang_MetaLang_SeparationCover(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

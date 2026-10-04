// Lean compiler output
// Module: MetaLang.SeparationCover
// Imports: public import Init public import Mathlib.Data.Setoid.Basic public import Mathlib.Data.Fintype.Prod public import Mathlib.Data.Finset.Card public import Mathlib.Data.Finset.Union public import Mathlib.Algebra.Order.BigOperators.Group.Finset public import Mathlib.Data.Nat.Log public import Mathlib.Data.Fintype.Powerset public import Mathlib.Tactic.Ring public import Mathlib.Tactic.NormNum public import Mathlib.Data.Finset.Max public import MetaLang.AlgebraicDescent
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
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_agree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_agree___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Need___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Need___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Need___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Need(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cov(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Covered___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Covered(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_gain___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_gain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bestOf___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bestOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_remaining___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_remaining(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_sig___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_sig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_sig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_sig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witness___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witnessExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witnessExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___closed__0_value;
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_spread___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_spread(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Finset_decidableExistsAndFinset___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableDforallMultiset___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__1___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Solver_gapTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_gapTask___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_gapTask___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_gapTask___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_Solver_gapTask___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_gapTask___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_gapTask___closed__1 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_gapTask___closed__1_value;
static const lean_ctor_object lp_MetaLang_MetaLang_Solver_gapTask___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_MetaLang_MetaLang_Solver_gapTask___closed__0_value),((lean_object*)&lp_MetaLang_MetaLang_Solver_gapTask___closed__1_value)}};
static const lean_object* lp_MetaLang_MetaLang_Solver_gapTask___closed__2 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_gapTask___closed__2_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Solver_gapTask = (const lean_object*)&lp_MetaLang_MetaLang_Solver_gapTask___closed__2_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_scale(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_scale___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Solver_demoObs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Solver_demoObs___closed__0;
static lean_once_cell_t lp_MetaLang_MetaLang_Solver_demoObs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Solver_demoObs___closed__1;
static lean_once_cell_t lp_MetaLang_MetaLang_Solver_demoObs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Solver_demoObs___closed__2;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoObs(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoObs___boxed(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Solver_demoAns___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Solver_demoAns___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoAns(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoAns___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoF(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoF___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoG(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoG___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Fintype_decidableForallFintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Sep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Sep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_SepBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_SepBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockH___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__1___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Solver_idTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_idTask___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_idTask___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_Solver_idTask___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_idTask___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_idTask___closed__1 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__1_value;
static const lean_ctor_object lp_MetaLang_MetaLang_Solver_idTask___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__0_value),((lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__1_value)}};
static const lean_object* lp_MetaLang_MetaLang_Solver_idTask___closed__2 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__2_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Solver_idTask = (const lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__2_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_altTask___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_altTask___lam__1___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Solver_altTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_altTask___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_altTask___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_altTask___closed__0_value;
static const lean_ctor_object lp_MetaLang_MetaLang_Solver_altTask___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_MetaLang_MetaLang_Solver_idTask___closed__0_value),((lean_object*)&lp_MetaLang_MetaLang_Solver_altTask___closed__0_value)}};
static const lean_object* lp_MetaLang_MetaLang_Solver_altTask___closed__1 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_altTask___closed__1_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Solver_altTask = (const lean_object*)&lp_MetaLang_MetaLang_Solver_altTask___closed__1_value;
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__1___boxed(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Solver_bitTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_bitTask___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_bitTask___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_bitTask___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_Solver_bitTask___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Solver_bitTask___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Solver_bitTask___closed__1 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_bitTask___closed__1_value;
static const lean_ctor_object lp_MetaLang_MetaLang_Solver_bitTask___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_MetaLang_MetaLang_Solver_bitTask___closed__0_value),((lean_object*)&lp_MetaLang_MetaLang_Solver_bitTask___closed__1_value)}};
static const lean_object* lp_MetaLang_MetaLang_Solver_bitTask___closed__2 = (const lean_object*)&lp_MetaLang_MetaLang_Solver_bitTask___closed__2_value;
LEAN_EXPORT const lean_object* lp_MetaLang_MetaLang_Solver_bitTask = (const lean_object*)&lp_MetaLang_MetaLang_Solver_bitTask___closed__2_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_hammingBits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_hammingBits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_agree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_agree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_MetaLang_Solver_Task_agree(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Need___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_6 = lean_apply_1(x_3, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Need___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Need___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Need___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_2);
x_4 = lp_mathlib_Multiset_product___redArg(x_2, x_2);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Need(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
lean_inc(x_2);
x_7 = lean_apply_2(x_4, x_2, x_5);
x_8 = lean_apply_2(x_4, x_2, x_6);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_1, x_2);
x_6 = lp_mathlib_Multiset_filter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cov(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc_ref(x_1);
x_4 = l_instDecidableEqProd___redArg(x_1, x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Covered___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Cov), 5, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_2);
x_7 = lp_mathlib_Finset_biUnion___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Covered(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_Covered___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_gain___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(x_1, x_2, x_5);
x_8 = lp_mathlib_Multiset_ndinter___redArg(x_6, x_7, x_4);
x_9 = l_List_lengthTR___redArg(x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_gain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_gain___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bestOf___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_6 = lp_MetaLang_MetaLang_Solver_bestOf___redArg(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_8 = lean_apply_1(x_1, x_4);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_inc_ref(x_1);
x_12 = lean_apply_1(x_1, x_11);
lean_inc(x_4);
x_13 = lean_apply_1(x_1, x_4);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bestOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_MetaLang_Solver_bestOf___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_bestOf_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 1)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
lean_inc_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_4);
x_11 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_gain), 7, 6);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_2);
lean_closure_set(x_11, 5, x_7);
lean_inc(x_5);
x_12 = lp_MetaLang_MetaLang_Solver_bestOf___redArg(x_11, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc_ref(x_2);
x_14 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
lean_inc(x_13);
lean_inc(x_1);
lean_inc_ref(x_4);
x_17 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(x_4, x_1, x_13);
x_18 = lp_mathlib_Multiset_sub___redArg(x_14, x_7, x_17);
lean_inc_ref(x_3);
x_19 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_13, x_8);
x_6 = x_16;
x_7 = x_18;
x_8 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_MetaLang_MetaLang_Solver_greedy___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_2(x_4, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_apply_3(x_5, x_10, x_2, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 1)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_apply_2(x_7, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
x_14 = lean_apply_3(x_8, x_13, x_5, x_6);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_greedy_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_remaining___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 1)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_3);
x_9 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_gain), 7, 6);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_2);
lean_closure_set(x_9, 5, x_6);
lean_inc(x_4);
x_10 = lp_MetaLang_MetaLang_Solver_bestOf___redArg(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc_ref(x_2);
x_12 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
lean_inc(x_1);
lean_inc_ref(x_3);
x_15 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(x_3, x_1, x_11);
x_16 = lp_mathlib_Multiset_sub___redArg(x_12, x_6, x_15);
x_5 = x_14;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_remaining(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_remaining___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_2(x_4, x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_apply_1(x_5, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_apply_2(x_6, x_11, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang___private_MetaLang_SeparationCover_0__MetaLang_Solver_remaining_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 1)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_3);
x_9 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_gain), 7, 6);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_2);
lean_closure_set(x_9, 5, x_6);
lean_inc(x_4);
x_10 = lp_MetaLang_MetaLang_Solver_bestOf___redArg(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = l_List_lengthTR___redArg(x_4);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc_ref(x_2);
x_13 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
x_16 = l_List_lengthTR___redArg(x_4);
lean_inc(x_1);
lean_inc_ref(x_3);
x_17 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(x_3, x_1, x_12);
x_18 = lp_mathlib_Multiset_sub___redArg(x_13, x_6, x_17);
x_19 = lp_MetaLang_MetaLang_Solver_greedyCost___redArg(x_1, x_2, x_3, x_4, x_15, x_18);
lean_dec(x_15);
x_20 = lean_nat_add(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_greedyCost___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_greedyCost___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_greedyCost___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_greedyCost(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_sig___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_4);
lean_inc(x_3);
x_7 = lean_apply_2(x_4, x_3, x_5);
x_8 = lean_apply_2(x_4, x_3, x_6);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_sig___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_sig___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_sig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_sig___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_sig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_sig___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witness(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witness___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_witness(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witnessExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_witnessExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_witnessExt(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockKey___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_5);
x_6 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_7 = lean_unsigned_to_nat(0u);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_2(x_8, x_5, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_blockKey___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_mathlib_Fintype_decidablePiFintype___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__1(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___closed__0));
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_blockKey), 7, 5);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
x_9 = lp_mathlib_Finset_image___redArg(x_7, x_8, x_1);
x_10 = l_List_lengthTR___redArg(x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_nblocks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_nblocks___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_spread___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_6 = lean_apply_1(x_4, x_3);
x_7 = lp_mathlib_Finset_image___redArg(x_5, x_6, x_1);
x_8 = l_List_lengthTR___redArg(x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_spread(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_spread___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_6 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_4, x_2);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_5, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_3, x_1);
x_7 = lp_mathlib_Multiset_filter___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
lean_inc(x_1);
x_6 = lp_MetaLang_MetaLang_Solver_Task_sig___redArg(x_1, x_2, x_5);
x_7 = lp_MetaLang_MetaLang_Solver_Task_sig___redArg(x_1, x_2, x_3);
x_8 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_1);
x_9 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_1, x_2);
lean_inc_ref(x_7);
x_10 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_3, x_7, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_5);
x_13 = lp_mathlib_Finset_decidableExistsAndFinset___redArg(x_6, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_7, 0, x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___lam__0___boxed), 8, 6);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_6);
lean_inc(x_1);
x_9 = lp_mathlib_Multiset_product___redArg(x_1, x_1);
x_10 = lp_mathlib_Multiset_decidableDforallMultiset___redArg(x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableRepresentative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableRepresentative___aux__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableRepresentative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableRepresentative(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_Cov___redArg(x_1, x_2, x_5);
x_7 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_7 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_1, x_2);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_8 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_3, x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_5);
x_11 = lp_mathlib_Finset_decidableExistsAndFinset___redArg(x_4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_5);
lean_closure_set(x_6, 3, x_3);
lean_inc(x_1);
x_7 = lp_mathlib_Multiset_product___redArg(x_1, x_1);
x_8 = lp_mathlib_Multiset_decidableDforallMultiset___redArg(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_decidableSeparable___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableSeparable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableSeparable___aux__1___redArg(x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableSeparable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableSeparable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_Covered___redArg(x_1, x_2, x_3, x_4);
x_8 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc_ref(x_2);
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_1);
lean_inc_ref(x_3);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
lean_closure_set(x_6, 4, x_5);
x_7 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_3, x_1);
x_8 = lp_mathlib_Multiset_attach___redArg(x_7);
x_9 = l_List_decidableBAll___redArg(x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_decidableFeasible___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg(x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableFeasible(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_2);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
lean_inc_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableFeasible___aux__1___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, x_6);
x_8 = lp_MetaLang_MetaLang_Solver_Task_NeedOn___redArg(x_1, x_2, x_3, x_4);
x_9 = lp_mathlib_Multiset_attach___redArg(x_8);
x_10 = l_List_decidableBAll___redArg(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableFeasibleOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___aux__1___redArg(x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableFeasibleOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableFeasibleOn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
x_10 = lean_box(x_9);
return x_10;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0, &lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Solver_gapTask___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_gapTask___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_gapTask___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_scale(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_scale___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_MetaLang_Solver_scale(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoObs(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__0, &lp_MetaLang_MetaLang_Solver_demoObs___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__0);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__1, &lp_MetaLang_MetaLang_Solver_demoObs___closed__1_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__2, &lp_MetaLang_MetaLang_Solver_demoObs___closed__2_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoObs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_demoObs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Solver_demoAns___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoAns(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoAns___closed__0, &lp_MetaLang_MetaLang_Solver_demoAns___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoAns___closed__0);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__1, &lp_MetaLang_MetaLang_Solver_demoObs___closed__1_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__2, &lp_MetaLang_MetaLang_Solver_demoObs___closed__2_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoAns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_demoAns(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoF(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoAns___closed__0, &lp_MetaLang_MetaLang_Solver_demoAns___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoAns___closed__0);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__1, &lp_MetaLang_MetaLang_Solver_demoObs___closed__1_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__2, &lp_MetaLang_MetaLang_Solver_demoObs___closed__2_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoF___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_demoF(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoG(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0, &lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_gapTask___lam__0___closed__0);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__2, &lp_MetaLang_MetaLang_Solver_demoObs___closed__2_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__1, &lp_MetaLang_MetaLang_Solver_demoObs___closed__1_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_demoG___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_demoG(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_5);
x_6 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_5, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_3);
lean_inc(x_5);
x_9 = lean_apply_1(x_4, x_5);
x_10 = lean_apply_1(x_8, x_5);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
x_7 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_1);
x_7 = lp_mathlib_Multiset_filter___redArg(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Consistent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc_ref(x_3);
x_4 = lean_apply_1(x_3, x_1);
x_5 = lean_apply_1(x_3, x_2);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lp_MetaLang_MetaLang_Solver_Task_Consistent___redArg(x_1, x_2, x_3, x_4, x_5);
x_10 = lp_mathlib_Multiset_attach___redArg(x_9);
x_11 = l_List_decidableBAll___redArg(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
lean_closure_set(x_6, 4, x_5);
lean_inc(x_1);
x_7 = lp_mathlib_Multiset_product___redArg(x_1, x_1);
x_8 = lp_mathlib_Multiset_filter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_NeedH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Sep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Cov___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_inc(x_1);
x_5 = lp_mathlib_Multiset_product___redArg(x_1, x_1);
x_6 = lp_mathlib_Multiset_filter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Sep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_Sep___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_SepBy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Sep), 5, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_3);
x_7 = lp_mathlib_Finset_biUnion___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_SepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_SepBy___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockH___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_decidableAllAgree___boxed), 9, 8);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, x_2);
lean_closure_set(x_7, 4, x_3);
lean_closure_set(x_7, 5, x_4);
lean_closure_set(x_7, 6, x_5);
lean_closure_set(x_7, 7, x_6);
x_8 = lp_mathlib_Multiset_filter___redArg(x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_blockH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_Task_blockH___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_SepBy___redArg(x_1, x_2, x_3, x_4);
x_8 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_2);
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Covered___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_7, 0, x_2);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_6);
lean_closure_set(x_8, 4, x_7);
x_9 = lp_MetaLang_MetaLang_Solver_Task_NeedH___redArg(x_1, x_2, x_3, x_4, x_5);
x_10 = lp_mathlib_Multiset_attach___redArg(x_9);
x_11 = l_List_decidableBAll___redArg(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___aux__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_Task_decidableIdentifies(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_constGen___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_constGen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_MetaLang_Solver_constGen(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__0, &lp_MetaLang_MetaLang_Solver_demoObs___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__0);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Solver_idTask___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__0, &lp_MetaLang_MetaLang_Solver_demoObs___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__0);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_idTask___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_idTask___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_altTask___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__0, &lp_MetaLang_MetaLang_Solver_demoObs___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__0);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoAns___closed__0, &lp_MetaLang_MetaLang_Solver_demoAns___closed__0_once, _init_lp_MetaLang_MetaLang_Solver_demoAns___closed__0);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
else
{
return x_5;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_altTask___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_altTask___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_5);
x_6 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_5, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
lean_inc_ref(x_8);
lean_inc(x_5);
x_11 = lean_apply_2(x_8, x_5, x_9);
x_12 = lean_apply_2(x_8, x_5, x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
x_6 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__1(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
x_6 = lp_MetaLang_MetaLang_Solver_Task_Need___redArg(x_4, x_1);
x_7 = lp_mathlib_Multiset_filter___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_AdeqDebt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_MetaLang_MetaLang_Solver_Task_AdeqDebt___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_1);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_Multiset_decidableDforallMultiset___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lp_mathlib_Multiset_filter___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_Task_Cheapest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_MetaLang_Solver_Task_Cheapest___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_7);
x_8 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_7, x_2);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_4);
lean_inc(x_7);
x_9 = lean_apply_2(x_4, x_7, x_5);
x_10 = lean_apply_2(x_4, x_7, x_6);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__0(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
lean_inc(x_9);
x_10 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_9, x_2);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_4);
lean_inc_ref(x_12);
lean_inc(x_5);
x_13 = lean_apply_1(x_12, x_5);
lean_inc(x_9);
x_14 = lean_apply_1(x_12, x_9);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_17, 0, x_6);
lean_closure_set(x_17, 1, x_7);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_11);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_9);
x_18 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_17, x_8);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_box(x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_8);
lean_inc_ref(x_1);
x_9 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(x_9);
x_12 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__1___boxed), 9, 8);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_8);
lean_closure_set(x_12, 5, x_4);
lean_closure_set(x_12, 6, x_5);
lean_closure_set(x_12, 7, x_6);
x_13 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_12, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___lam__2___boxed), 8, 7);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_7);
lean_closure_set(x_8, 5, x_3);
lean_closure_set(x_8, 6, x_1);
x_9 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Solver_decidableExtensional(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lp_MetaLang_MetaLang_Solver_decidableExtensional___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_decidableExtensional___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lp_MetaLang_MetaLang_Solver_decidableExtensional(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Solver_demoObs___closed__1, &lp_MetaLang_MetaLang_Solver_demoObs___closed__1_once, _init_lp_MetaLang_MetaLang_Solver_demoObs___closed__1);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_nat_mod(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_shiftr(x_2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Solver_bitTask___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_bitTask___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_Solver_bitTask___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_hammingBits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_shiftr(x_1, x_4);
x_12 = lean_nat_shiftr(x_2, x_4);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(0u);
x_5 = x_14;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_nat_mod(x_1, x_3);
x_7 = lean_nat_mod(x_2, x_3);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_nat_add(x_5, x_4);
return x_9;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Solver_hammingBits___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_Solver_hammingBits(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Setoid_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Prod(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Union(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Group_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Log(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Powerset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Ring(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_NormNum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Max(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_AlgebraicDescent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_SeparationCover(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Setoid_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Union(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Group_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Powerset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_NormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Max(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_AlgebraicDescent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

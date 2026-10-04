// Lean compiler output
// Module: MetaLang.ConstraintLogic
// Imports: public import Init public import Mathlib
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_mem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_mem___boxed(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_B3_points___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_B3_points___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_points;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_top;
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_isMoore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_isMoore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_isMoore___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_isMoore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_isMoore(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_isMoore___boxed(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_conditions_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_B3_conditions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_B3_conditions___closed__0;
static lean_once_cell_t lp_MetaLang_MetaLang_B3_conditions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_B3_conditions___closed__1;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_conditions;
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hullStep(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_B3_hull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_B3_hull___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_B3_hull___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_B3_hull___closed__0_value;
static lean_once_cell_t lp_MetaLang_MetaLang_B3_hull___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_B3_hull___closed__1;
lean_object* l_Nat_recCompiled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_entails(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_entails___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_conj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_conj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_disj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_disj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_bot;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_topCond;
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impCandidates_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impCandidates(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impCandidates___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impAntichain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impAntichain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_neg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_neg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__0(uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__1(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__2(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_valid(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_valid___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_mimic(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_mimic___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_mem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_nat_shiftr(x_1, x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mod(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_mem___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_MetaLang_B3_mem(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_points___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_List_range(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_points(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_B3_points___closed__0, &lp_MetaLang_MetaLang_B3_points___closed__0_once, _init_lp_MetaLang_MetaLang_B3_points___closed__0);
return x_1;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_top(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(7u);
return x_1;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_isMoore___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_MetaLang_MetaLang_B3_mem(x_1, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_nat_land(x_3, x_4);
x_7 = lp_MetaLang_MetaLang_B3_mem(x_1, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_isMoore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lp_MetaLang_MetaLang_B3_isMoore___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_isMoore___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_MetaLang_MetaLang_B3_mem(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(x_2);
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_B3_isMoore___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_4);
x_8 = l_List_all___redArg(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_isMoore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lp_MetaLang_MetaLang_B3_isMoore___lam__1(x_1, x_5, x_3, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_isMoore(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(7u);
x_3 = lp_MetaLang_MetaLang_B3_mem(x_1, x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lp_MetaLang_MetaLang_B3_points;
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_B3_isMoore___lam__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
x_7 = l_List_all___redArg(x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_isMoore___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_B3_isMoore(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_conditions_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_7 = lp_MetaLang_MetaLang_B3_isMoore(x_5);
if (x_7 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_10);
x_12 = lp_MetaLang_MetaLang_B3_isMoore(x_10);
if (x_12 == 0)
{
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_conditions___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(256u);
x_2 = l_List_range(x_1);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_conditions___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&lp_MetaLang_MetaLang_B3_conditions___closed__0, &lp_MetaLang_MetaLang_B3_conditions___closed__0_once, _init_lp_MetaLang_MetaLang_B3_conditions___closed__0);
x_3 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_conditions_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_conditions(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_B3_conditions___closed__1, &lp_MetaLang_MetaLang_B3_conditions___closed__1_once, _init_lp_MetaLang_MetaLang_B3_conditions___closed__1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_15; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_15 = lp_MetaLang_MetaLang_B3_mem(x_2, x_1);
if (x_15 == 0)
{
x_7 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = lp_MetaLang_MetaLang_B3_mem(x_2, x_5);
x_7 = x_16;
goto block_14;
}
block_14:
{
if (x_7 == 0)
{
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_land(x_1, x_5);
x_11 = lean_nat_shiftl(x_9, x_10);
lean_dec(x_10);
x_12 = lean_nat_lor(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_6;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lp_MetaLang_MetaLang_B3_points;
x_7 = lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__0(x_4, x_1, x_2, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hullStep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_B3_points;
lean_inc(x_1);
x_3 = lp_MetaLang_List_foldl___at___00MetaLang_B3_hullStep_spec__1(x_1, x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_B3_hullStep(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_B3_hull___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_hull___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_shiftl(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = ((lean_object*)(lp_MetaLang_MetaLang_B3_hull___closed__0));
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_B3_hull___closed__1, &lp_MetaLang_MetaLang_B3_hull___closed__1_once, _init_lp_MetaLang_MetaLang_B3_hull___closed__1);
x_4 = lean_nat_lor(x_1, x_3);
x_5 = lean_unsigned_to_nat(4u);
x_6 = l_Nat_recCompiled___redArg(x_4, x_2, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_hull___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_B3_hull(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_B3_entails(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_nat_land(x_1, x_2);
x_4 = lean_nat_dec_eq(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_entails___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_MetaLang_B3_entails(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_conj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_land(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_conj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_B3_conj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_disj(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_lor(x_1, x_2);
x_4 = lp_MetaLang_MetaLang_B3_hull(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_disj___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_B3_disj(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_bot(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_B3_hull___closed__1, &lp_MetaLang_MetaLang_B3_hull___closed__1_once, _init_lp_MetaLang_MetaLang_B3_hull___closed__1);
return x_1;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_B3_topCond(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(255u);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impCandidates_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___redArg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_nat_land(x_1, x_7);
x_10 = lp_MetaLang_MetaLang_B3_entails(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_free_object(x_3);
lean_dec(x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_nat_land(x_1, x_13);
x_16 = lp_MetaLang_MetaLang_B3_entails(x_15, x_2);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_13);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_4);
x_3 = x_14;
x_4 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impCandidates_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impCandidates_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impCandidates(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_MetaLang_MetaLang_B3_conditions;
x_4 = lean_box(0);
x_5 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impCandidates_spec__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impCandidates___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_B3_impCandidates(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_MetaLang_MetaLang_B3_entails(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_1, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___redArg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lp_MetaLang_MetaLang_B3_impCandidates(x_1, x_2);
x_11 = l_List_all___redArg(x_10, x_9);
if (x_11 == 0)
{
lean_free_object(x_3);
lean_dec(x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lp_MetaLang_MetaLang_B3_impCandidates(x_1, x_2);
x_18 = l_List_all___redArg(x_17, x_16);
if (x_18 == 0)
{
lean_dec(x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_4);
x_3 = x_15;
x_4 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impAntichain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_MetaLang_MetaLang_B3_impCandidates(x_1, x_2);
x_4 = lean_box(0);
x_5 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_B3_impAntichain_spec__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_impAntichain___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_B3_impAntichain(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_neg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_B3_bot;
x_3 = lp_MetaLang_MetaLang_B3_impAntichain(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_B3_neg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_B3_neg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_box(x_1);
x_6 = lean_box(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc_ref(x_3);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_box(x_1);
x_10 = lean_box(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_unbox(x_8);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_unbox(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_unbox(x_8);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_4);
x_8 = lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__0(x_5, x_6, x_3, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__1(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_box(x_1);
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
x_7 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_3);
x_6 = lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__1(x_4, x_2, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__2(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__2(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_instDecidableDescends(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___lam__2___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_instDecidableDescends___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_Nuisance_instDecidableDescends(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_valid(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_valid___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_Nuisance_valid(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Nuisance_mimic(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unbox(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_unbox(x_2);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Nuisance_mimic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_Nuisance_mimic(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_ConstraintLogic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_MetaLang_MetaLang_B3_points = _init_lp_MetaLang_MetaLang_B3_points();
lean_mark_persistent(lp_MetaLang_MetaLang_B3_points);
lp_MetaLang_MetaLang_B3_top = _init_lp_MetaLang_MetaLang_B3_top();
lean_mark_persistent(lp_MetaLang_MetaLang_B3_top);
lp_MetaLang_MetaLang_B3_conditions = _init_lp_MetaLang_MetaLang_B3_conditions();
lean_mark_persistent(lp_MetaLang_MetaLang_B3_conditions);
lp_MetaLang_MetaLang_B3_bot = _init_lp_MetaLang_MetaLang_B3_bot();
lean_mark_persistent(lp_MetaLang_MetaLang_B3_bot);
lp_MetaLang_MetaLang_B3_topCond = _init_lp_MetaLang_MetaLang_B3_topCond();
lean_mark_persistent(lp_MetaLang_MetaLang_B3_topCond);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

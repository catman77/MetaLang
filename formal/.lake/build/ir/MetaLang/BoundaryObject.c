// Lean compiler output
// Module: MetaLang.BoundaryObject
// Imports: public import Init public import MetaLang.TheoryPresentation public import MetaLang.Projection
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
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_iterate___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_decidableExistsFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Bool_fintype;
lean_object* lp_mathlib_Finset_powerset___redArg(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0;
uint8_t lp_mathlib_Finset_decidableExistsAndFinset___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_fixCount___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_fixCount___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_Boundary_fixCount___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_Boundary_fixCount___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_Boundary_fixCount___closed__0_value;
static lean_once_cell_t lp_MetaLang_MetaLang_Boundary_fixCount___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___closed__1;
static lean_once_cell_t lp_MetaLang_MetaLang_Boundary_fixCount___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___closed__2;
static lean_once_cell_t lp_MetaLang_MetaLang_Boundary_fixCount___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___closed__3;
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_fixCount(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_cycleCount___lam__0(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_cycleCount___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_cycleCount___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_cycleCount___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_cycleCount(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_signature(lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_Boundary_hiddenPhi___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_Boundary_hiddenPhi___closed__0;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_hiddenPhi(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_boundaryOf___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_boundaryOf___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Finset_instDecidableRelSubset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0(lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Fintype_decidableForallFintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_MetaLang_MetaLang_Boundary_fixCount___closed__0_value)} };
static const lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0(lean_object*, lean_object*);
extern lean_object* lp_MetaLang_MetaLang_fullInterval;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_boundaryOf(lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_inc(x_2);
x_7 = lp_mathlib_Nat_iterate___redArg(x_1, x_6, x_2);
x_8 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_4, x_7, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Nat_decidableExistsFin___redArg(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic(x_1, x_2);
if (x_3 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
lean_inc(x_2);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_4, x_5, x_2);
if (x_6 == 0)
{
return x_3;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_mathlib_Bool_fintype;
x_2 = lp_mathlib_Finset_powerset___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0, &lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0_once, _init_lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0);
x_4 = lp_mathlib_Finset_decidableExistsAndFinset___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_fixCount___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_MetaLang_MetaLang_Boundary_fixCount___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_fixCount___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_fixCount___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Boundary_fixCount___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__1(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__2(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__1, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__1_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__1);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__2, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__2_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__2);
x_2 = lp_mathlib_Finset_powerset___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_fixCount(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = ((lean_object*)(lp_MetaLang_MetaLang_Boundary_fixCount___closed__0));
x_3 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_fixCount___lam__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__3, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__3_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_cycleCount___lam__0(uint8_t x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
if (x_2 == 0)
{
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_cycleCount___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = lp_MetaLang_MetaLang_Boundary_cycleCount___lam__0(x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_cycleCount___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic(x_1, x_2);
if (x_3 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_cycleCount___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
lean_inc(x_2);
x_6 = lean_apply_1(x_1, x_2);
x_7 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_5, x_6, x_2);
if (x_7 == 0)
{
return x_3;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_cycleCount___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_MetaLang_MetaLang_Boundary_cycleCount___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_cycleCount(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_cycleCount___lam__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__3, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__3_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__3);
x_4 = lp_mathlib_Multiset_filter___redArg(x_2, x_3);
x_5 = l_List_lengthTR___redArg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_signature(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lp_MetaLang_MetaLang_Boundary_fixCount(x_1);
x_3 = lp_MetaLang_MetaLang_Boundary_cycleCount(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_Boundary_hiddenPhi___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_hiddenPhi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(lp_MetaLang_MetaLang_Boundary_fixCount___closed__0));
x_3 = lean_box(0);
lean_inc(x_1);
x_4 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_2, x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 1;
x_6 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_hiddenPhi___closed__0, &lp_MetaLang_MetaLang_Boundary_hiddenPhi___closed__0_once, _init_lp_MetaLang_MetaLang_Boundary_hiddenPhi___closed__0);
x_7 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_2, x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_box(x_5);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_Boundary_boundaryOf___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_1);
x_4 = lp_MetaLang_MetaLang_Boundary_instDecidableIsCyclic(x_1, x_3);
if (x_4 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_2, x_5, x_3);
if (x_6 == 0)
{
return x_4;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_boundaryOf___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_Boundary_boundaryOf___lam__2(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_mathlib_Multiset_instDecidableRListOfDecidableEq___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = lp_mathlib_Finset_instDecidableRelSubset___redArg(x_2, x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lp_mathlib_Finset_instDecidableRelSubset___redArg(x_2, x_3, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(lp_MetaLang_MetaLang_Boundary_fixCount___closed__0));
x_3 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0___lam__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__3, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__3_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_box(x_3);
x_7 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_2, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__0(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0(x_3);
x_8 = lp_mathlib_Finset_decidableExistsAndFinset___redArg(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_4);
x_6 = lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__2(x_1, x_2, x_3, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lp_MetaLang_MetaLang_gamma___at___00MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0_spec__0(x_1);
lean_inc(x_6);
x_8 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_2, x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_apply_1(x_3, x_6);
x_11 = lean_box(x_5);
x_12 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_4, x_11, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__3(x_1, x_2, x_3, x_4, x_7, x_6);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__3___boxed), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_7);
x_9 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_6);
x_8 = lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__4(x_1, x_2, x_3, x_4, x_5, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = ((lean_object*)(lp_MetaLang_MetaLang_Boundary_fixCount___closed__0));
x_4 = ((lean_object*)(lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___closed__0));
lean_inc_ref(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0, &lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0_once, _init_lp_MetaLang_MetaLang_Boundary_instDecidableHasNontrivialCycle___closed__0);
x_7 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0___lam__4___boxed), 6, 5);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_6);
x_8 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__2, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__2_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__2);
x_9 = lp_mathlib_Multiset_filter___redArg(x_7, x_8);
x_10 = lp_mathlib_Multiset_filter___redArg(x_5, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_Boundary_boundaryOf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = ((lean_object*)(lp_MetaLang_MetaLang_Boundary_fixCount___closed__0));
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_fixCount___lam__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(lp_MetaLang_MetaLang_Boundary_boundaryOf___lam__2___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lp_MetaLang_MetaLang_fullInterval;
x_6 = lp_MetaLang_MetaLang_istep___at___00MetaLang_Boundary_boundaryOf_spec__0(x_1, x_5);
x_7 = lean_obj_once(&lp_MetaLang_MetaLang_Boundary_fixCount___closed__3, &lp_MetaLang_MetaLang_Boundary_fixCount___closed__3_once, _init_lp_MetaLang_MetaLang_Boundary_fixCount___closed__3);
x_8 = lp_mathlib_Multiset_filter___redArg(x_4, x_7);
x_9 = lp_mathlib_Multiset_filter___redArg(x_3, x_7);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_TheoryPresentation(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Projection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_BoundaryObject(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_TheoryPresentation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Projection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

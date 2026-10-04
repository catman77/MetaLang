// Lean compiler output
// Module: MetaLang.TheorySpace
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_TheorySpace_adm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_TheorySpace_adm___closed__0;
static lean_once_cell_t lp_MetaLang_MetaLang_TheorySpace_adm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_TheorySpace_adm___closed__1;
static lean_once_cell_t lp_MetaLang_MetaLang_TheorySpace_adm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_TheorySpace_adm___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_TheorySpace_adm(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_adm___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_TheorySpace_prov(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_prov___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_TheorySpace_branchCount_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_TheorySpace_branchCount_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__0;
static lean_once_cell_t lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__1;
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_branchCount(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_branchCount___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__2(lean_object*);
static const lean_closure_object lp_MetaLang_MetaLang_trivialDiagonal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_trivialDiagonal___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_trivialDiagonal___closed__0 = (const lean_object*)&lp_MetaLang_MetaLang_trivialDiagonal___closed__0_value;
static const lean_closure_object lp_MetaLang_MetaLang_trivialDiagonal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_trivialDiagonal___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_trivialDiagonal___closed__1 = (const lean_object*)&lp_MetaLang_MetaLang_trivialDiagonal___closed__1_value;
static const lean_closure_object lp_MetaLang_MetaLang_trivialDiagonal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_MetaLang_MetaLang_trivialDiagonal___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_MetaLang_MetaLang_trivialDiagonal___closed__2 = (const lean_object*)&lp_MetaLang_MetaLang_trivialDiagonal___closed__2_value;
static lean_once_cell_t lp_MetaLang_MetaLang_trivialDiagonal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_MetaLang_MetaLang_trivialDiagonal___closed__3;
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal;
static lean_object* _init_lp_MetaLang_MetaLang_TheorySpace_adm___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_TheorySpace_adm___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_TheorySpace_adm___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_TheorySpace_adm(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_TheorySpace_adm___closed__0, &lp_MetaLang_MetaLang_TheorySpace_adm___closed__0_once, _init_lp_MetaLang_MetaLang_TheorySpace_adm___closed__0);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_obj_once(&lp_MetaLang_MetaLang_TheorySpace_adm___closed__1, &lp_MetaLang_MetaLang_TheorySpace_adm___closed__1_once, _init_lp_MetaLang_MetaLang_TheorySpace_adm___closed__1);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_obj_once(&lp_MetaLang_MetaLang_TheorySpace_adm___closed__2, &lp_MetaLang_MetaLang_TheorySpace_adm___closed__2_once, _init_lp_MetaLang_MetaLang_TheorySpace_adm___closed__2);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
return x_8;
}
else
{
if (x_2 == 0)
{
return x_8;
}
else
{
return x_6;
}
}
}
else
{
return x_2;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_adm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = lp_MetaLang_MetaLang_TheorySpace_adm(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_MetaLang_MetaLang_TheorySpace_prov(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_prov___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = lp_MetaLang_MetaLang_TheorySpace_prov(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_TheorySpace_branchCount_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_unbox(x_6);
x_9 = lp_MetaLang_MetaLang_TheorySpace_adm(x_1, x_8);
if (x_9 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_unbox(x_12);
x_15 = lp_MetaLang_MetaLang_TheorySpace_adm(x_1, x_14);
if (x_15 == 0)
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_13;
x_3 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang_List_filterTR_loop___at___00MetaLang_TheorySpace_branchCount_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_TheorySpace_branchCount_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__0(void) {
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
static lean_object* _init_lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__1(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__0, &lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__0_once, _init_lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_branchCount(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_obj_once(&lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__1, &lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__1_once, _init_lp_MetaLang_MetaLang_TheorySpace_branchCount___closed__1);
x_4 = lp_MetaLang_List_filterTR_loop___at___00MetaLang_TheorySpace_branchCount_spec__0(x_1, x_3, x_2);
x_5 = l_List_lengthTR___redArg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_TheorySpace_branchCount___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_MetaLang_MetaLang_TheorySpace_branchCount(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_MetaLang_MetaLang_trivialDiagonal___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_trivialDiagonal___lam__2(lean_object* x_1) {
_start:
{
return x_1;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_trivialDiagonal___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(lp_MetaLang_MetaLang_trivialDiagonal___closed__2));
x_2 = ((lean_object*)(lp_MetaLang_MetaLang_trivialDiagonal___closed__1));
x_3 = ((lean_object*)(lp_MetaLang_MetaLang_trivialDiagonal___closed__0));
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_trivialDiagonal(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_MetaLang_MetaLang_trivialDiagonal___closed__3, &lp_MetaLang_MetaLang_trivialDiagonal___closed__3_once, _init_lp_MetaLang_MetaLang_trivialDiagonal___closed__3);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_TheorySpace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_MetaLang_MetaLang_trivialDiagonal = _init_lp_MetaLang_MetaLang_trivialDiagonal();
lean_mark_persistent(lp_MetaLang_MetaLang_trivialDiagonal);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

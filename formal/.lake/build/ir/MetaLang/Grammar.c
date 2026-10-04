// Lean compiler output
// Module: MetaLang.Grammar
// Imports: public import Init public import MetaLang.Continuation
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
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_ContFilter_comp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_ContFilter_id(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_freeWorld(lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_orderWorld;
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_ContFilter_comp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_ContFilter_id(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_MetaLang_MetaLang_World_freeWorld(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_lp_MetaLang_MetaLang_World_orderWorld(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_box(x_2);
x_10 = lean_apply_3(x_3, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_box(x_2);
x_12 = lean_apply_3(x_4, x_1, x_11, lean_box(0));
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_box(x_2);
x_14 = lean_apply_3(x_4, x_1, x_13, lean_box(0));
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_box(x_2);
x_16 = lean_apply_3(x_4, x_1, x_15, lean_box(0));
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_6);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_box(x_3);
x_11 = lean_apply_3(x_4, x_8, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_box(x_3);
x_13 = lean_apply_3(x_5, x_2, x_12, lean_box(0));
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_box(x_3);
x_15 = lean_apply_3(x_5, x_2, x_14, lean_box(0));
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(x_3);
x_17 = lean_apply_3(x_5, x_2, x_16, lean_box(0));
return x_17;
}
}
}
LEAN_EXPORT lean_object* lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_MetaLang___private_MetaLang_Grammar_0__MetaLang_World_orderStep_match__1_splitter(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_MetaLang_MetaLang_Continuation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MetaLang_MetaLang_Grammar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MetaLang_MetaLang_Continuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_MetaLang_MetaLang_World_orderWorld = _init_lp_MetaLang_MetaLang_World_orderWorld();
lean_mark_persistent(lp_MetaLang_MetaLang_World_orderWorld);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Congruence
// Imports: public import Init public import FullBetaReduction
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
LEAN_EXPORT lean_object* lp_lambda_Congruence_lam__cong(lean_object*, lean_object*, lean_object*);
lean_object* lp_lambda_Lambda_multi__trans___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Congruence_appR__cong(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Congruence_app__cong(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Congruence_appL__cong(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Congruence_appL__cong(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_3);
lean_inc_ref(x_3);
lean_inc_ref(x_11);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_3);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_inc_ref(x_3);
lean_inc_ref(x_11);
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_12);
x_20 = lp_lambda_Congruence_appL__cong(x_11, x_2, x_3, x_13);
lean_ctor_set(x_4, 4, x_20);
lean_ctor_set(x_4, 3, x_19);
lean_ctor_set(x_4, 2, x_18);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
lean_inc_ref(x_3);
lean_inc_ref(x_21);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_3);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_inc_ref(x_3);
lean_inc_ref(x_21);
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_22);
x_28 = lp_lambda_Congruence_appL__cong(x_21, x_2, x_3, x_23);
x_29 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Congruence_appR__cong(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_11);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_19 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
x_20 = lp_lambda_Congruence_appR__cong(x_1, x_11, x_3, x_13);
lean_ctor_set(x_4, 4, x_20);
lean_ctor_set(x_4, 3, x_19);
lean_ctor_set(x_4, 2, x_18);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_21);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
x_27 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
x_28 = lp_lambda_Congruence_appR__cong(x_1, x_21, x_3, x_23);
x_29 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Congruence_app__cong(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_9 = lp_lambda_Congruence_appL__cong(x_1, x_2, x_3, x_5);
x_10 = lp_lambda_Congruence_appR__cong(x_2, x_3, x_4, x_6);
x_11 = lp_lambda_Lambda_multi__trans___redArg(x_7, x_8, x_9, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_lambda_Congruence_lam__cong(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
lean_inc_ref(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
lean_inc_ref(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
lean_inc_ref(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
lean_inc_ref(x_10);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
x_19 = lp_lambda_Congruence_lam__cong(x_10, x_2, x_12);
lean_ctor_set(x_3, 4, x_19);
lean_ctor_set(x_3, 3, x_18);
lean_ctor_set(x_3, 2, x_17);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
lean_inc_ref(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
lean_inc_ref(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_20);
lean_inc_ref(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
lean_inc_ref(x_20);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
x_27 = lp_lambda_Congruence_lam__cong(x_20, x_2, x_22);
x_28 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
return x_28;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lambda_FullBetaReduction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lambda_Congruence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lambda_FullBetaReduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

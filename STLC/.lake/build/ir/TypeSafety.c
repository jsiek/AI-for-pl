// Lean compiler output
// Module: TypeSafety
// Imports: public import Init public import STLC
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
lean_object* lp_stlc_STLC_exts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_preservation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_preservation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_stlc_STLC_subst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_step_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__0___boxed(lean_object*);
lean_object* lp_stlc_STLC_single__subst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_stlc_STLC_ext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_preservation___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx(lean_object*, lean_object*);
static lean_object* lp_stlc_TypeSafety_typing__subst___redArg___closed__0;
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx___redArg___boxed(lean_object*);
static lean_object* lp_stlc_TypeSafety_progress___redArg___closed__0;
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_step_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress__top(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_stlc_STLC_rename(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
lean_inc(x_13);
x_18 = lean_apply_1(x_3, x_13);
lean_inc(x_6);
x_19 = lean_apply_3(x_4, x_13, x_6, x_14);
lean_ctor_set(x_7, 4, x_19);
lean_ctor_set(x_7, 3, x_18);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = lean_ctor_get(x_7, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
lean_inc(x_20);
x_22 = lean_apply_1(x_3, x_20);
lean_inc(x_6);
x_23 = lean_apply_3(x_4, x_20, x_6, x_21);
x_24 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__rename___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 1, x_10);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_ctor_get(x_6, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_inc(x_14);
x_20 = lean_apply_1(x_2, x_14);
lean_inc(x_5);
x_21 = lean_apply_3(x_3, x_14, x_5, x_15);
lean_ctor_set(x_6, 4, x_21);
lean_ctor_set(x_6, 3, x_20);
lean_ctor_set(x_6, 2, x_19);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_box(0);
lean_inc(x_22);
x_25 = lean_apply_1(x_2, x_22);
lean_inc(x_5);
x_26 = lean_apply_3(x_3, x_22, x_5, x_23);
x_27 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_stlc_TypeSafety_typing__rename___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
lean_inc(x_8);
x_12 = lean_apply_1(x_3, x_8);
lean_inc(x_4);
x_13 = lean_apply_3(x_5, x_8, x_4, x_9);
lean_ctor_set(x_6, 3, x_13);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
lean_inc(x_14);
x_16 = lean_apply_1(x_3, x_14);
lean_inc(x_4);
x_17 = lean_apply_3(x_5, x_14, x_4, x_15);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
case 1:
{
uint8_t x_19; 
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
x_24 = lean_ctor_get(x_6, 0);
lean_dec(x_24);
lean_inc_ref(x_3);
lean_inc(x_20);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__rename___redArg___lam__0___boxed), 7, 4);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_20);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_5);
x_26 = lean_alloc_closure((void*)(lp_stlc_STLC_ext___boxed), 2, 1);
lean_closure_set(x_26, 0, x_3);
lean_inc_ref(x_26);
x_27 = lp_stlc_STLC_rename(x_26, x_22);
lean_inc(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_2);
lean_inc(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_2);
lean_inc(x_21);
x_30 = lp_stlc_TypeSafety_typing__rename___redArg(x_28, x_29, x_26, x_21, x_25, x_23);
lean_ctor_set(x_6, 4, x_30);
lean_ctor_set(x_6, 3, x_27);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 4);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
lean_inc_ref(x_3);
lean_inc(x_31);
lean_inc(x_2);
x_35 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__rename___redArg___lam__0___boxed), 7, 4);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_31);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_5);
x_36 = lean_alloc_closure((void*)(lp_stlc_STLC_ext___boxed), 2, 1);
lean_closure_set(x_36, 0, x_3);
lean_inc_ref(x_36);
x_37 = lp_stlc_STLC_rename(x_36, x_33);
lean_inc(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_1);
lean_inc(x_2);
lean_inc(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_2);
lean_inc(x_32);
x_40 = lp_stlc_TypeSafety_typing__rename___redArg(x_38, x_39, x_36, x_32, x_35, x_34);
x_41 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_31);
lean_ctor_set(x_41, 2, x_32);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_40);
return x_41;
}
}
case 2:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_6, 1);
x_44 = lean_ctor_get(x_6, 3);
x_45 = lean_ctor_get(x_6, 4);
x_46 = lean_ctor_get(x_6, 5);
x_47 = lean_ctor_get(x_6, 6);
x_48 = lean_ctor_get(x_6, 2);
lean_dec(x_48);
x_49 = lean_ctor_get(x_6, 0);
lean_dec(x_49);
lean_inc_ref(x_3);
x_50 = lp_stlc_STLC_rename(x_3, x_44);
lean_inc_ref(x_3);
x_51 = lp_stlc_STLC_rename(x_3, x_45);
lean_inc(x_4);
lean_inc(x_43);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_53 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_52, x_5, x_46);
lean_inc(x_43);
lean_inc(x_2);
x_54 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_43, x_5, x_47);
lean_ctor_set(x_6, 6, x_54);
lean_ctor_set(x_6, 5, x_53);
lean_ctor_set(x_6, 4, x_51);
lean_ctor_set(x_6, 3, x_50);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_6, 1);
x_56 = lean_ctor_get(x_6, 3);
x_57 = lean_ctor_get(x_6, 4);
x_58 = lean_ctor_get(x_6, 5);
x_59 = lean_ctor_get(x_6, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
lean_inc_ref(x_3);
x_60 = lp_stlc_STLC_rename(x_3, x_56);
lean_inc_ref(x_3);
x_61 = lp_stlc_STLC_rename(x_3, x_57);
lean_inc(x_4);
lean_inc(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_63 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_62, x_5, x_58);
lean_inc(x_55);
lean_inc(x_2);
x_64 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_55, x_5, x_59);
x_65 = lean_alloc_ctor(2, 7, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_55);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set(x_65, 3, x_60);
lean_ctor_set(x_65, 4, x_61);
lean_ctor_set(x_65, 5, x_63);
lean_ctor_set(x_65, 6, x_64);
return x_65;
}
}
case 3:
{
uint8_t x_66; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_6);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_6, 0);
lean_dec(x_67);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_68; 
lean_dec(x_6);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
}
case 4:
{
uint8_t x_69; 
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_6, 1);
x_71 = lean_ctor_get(x_6, 2);
x_72 = lean_ctor_get(x_6, 0);
lean_dec(x_72);
lean_inc_ref(x_3);
x_73 = lp_stlc_STLC_rename(x_3, x_70);
x_74 = lean_box(0);
lean_inc(x_2);
x_75 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_74, x_5, x_71);
lean_ctor_set(x_6, 2, x_75);
lean_ctor_set(x_6, 1, x_73);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_6, 1);
x_77 = lean_ctor_get(x_6, 2);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_6);
lean_inc_ref(x_3);
x_78 = lp_stlc_STLC_rename(x_3, x_76);
x_79 = lean_box(0);
lean_inc(x_2);
x_80 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_79, x_5, x_77);
x_81 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_80);
return x_81;
}
}
default: 
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_6);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_83 = lean_ctor_get(x_6, 2);
x_84 = lean_ctor_get(x_6, 3);
x_85 = lean_ctor_get(x_6, 4);
x_86 = lean_ctor_get(x_6, 5);
x_87 = lean_ctor_get(x_6, 6);
x_88 = lean_ctor_get(x_6, 7);
x_89 = lean_ctor_get(x_6, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_6, 0);
lean_dec(x_90);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
x_91 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__rename___redArg___lam__1___boxed), 6, 3);
lean_closure_set(x_91, 0, x_2);
lean_closure_set(x_91, 1, x_3);
lean_closure_set(x_91, 2, x_5);
lean_inc_ref(x_3);
x_92 = lp_stlc_STLC_rename(x_3, x_83);
lean_inc_ref(x_3);
x_93 = lp_stlc_STLC_rename(x_3, x_84);
lean_inc_ref(x_3);
x_94 = lean_alloc_closure((void*)(lp_stlc_STLC_ext___boxed), 2, 1);
lean_closure_set(x_94, 0, x_3);
lean_inc_ref(x_94);
x_95 = lp_stlc_STLC_rename(x_94, x_85);
x_96 = lean_box(0);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_97 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_96, x_5, x_86);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_98 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_4, x_5, x_87);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_1);
lean_inc(x_2);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_2);
lean_inc(x_4);
x_101 = lp_stlc_TypeSafety_typing__rename___redArg(x_99, x_100, x_94, x_4, x_91, x_88);
lean_ctor_set(x_6, 7, x_101);
lean_ctor_set(x_6, 6, x_98);
lean_ctor_set(x_6, 5, x_97);
lean_ctor_set(x_6, 4, x_95);
lean_ctor_set(x_6, 3, x_93);
lean_ctor_set(x_6, 2, x_92);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_102 = lean_ctor_get(x_6, 2);
x_103 = lean_ctor_get(x_6, 3);
x_104 = lean_ctor_get(x_6, 4);
x_105 = lean_ctor_get(x_6, 5);
x_106 = lean_ctor_get(x_6, 6);
x_107 = lean_ctor_get(x_6, 7);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
x_108 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__rename___redArg___lam__1___boxed), 6, 3);
lean_closure_set(x_108, 0, x_2);
lean_closure_set(x_108, 1, x_3);
lean_closure_set(x_108, 2, x_5);
lean_inc_ref(x_3);
x_109 = lp_stlc_STLC_rename(x_3, x_102);
lean_inc_ref(x_3);
x_110 = lp_stlc_STLC_rename(x_3, x_103);
lean_inc_ref(x_3);
x_111 = lean_alloc_closure((void*)(lp_stlc_STLC_ext___boxed), 2, 1);
lean_closure_set(x_111, 0, x_3);
lean_inc_ref(x_111);
x_112 = lp_stlc_STLC_rename(x_111, x_104);
x_113 = lean_box(0);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_114 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_113, x_5, x_105);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_115 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_4, x_5, x_106);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_1);
lean_inc(x_2);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_2);
lean_inc(x_4);
x_118 = lp_stlc_TypeSafety_typing__rename___redArg(x_116, x_117, x_111, x_4, x_108, x_107);
x_119 = lean_alloc_ctor(5, 8, 0);
lean_ctor_set(x_119, 0, x_2);
lean_ctor_set(x_119, 1, x_4);
lean_ctor_set(x_119, 2, x_109);
lean_ctor_set(x_119, 3, x_110);
lean_ctor_set(x_119, 4, x_112);
lean_ctor_set(x_119, 5, x_114);
lean_ctor_set(x_119, 6, x_115);
lean_ctor_set(x_119, 7, x_118);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__rename___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__rename(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_stlc_TypeSafety_typing__subst___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_2);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_1);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_8, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_20);
lean_dec_ref(x_8);
lean_inc(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_inc(x_7);
x_22 = lean_apply_3(x_3, x_19, x_7, x_20);
x_23 = lp_stlc_TypeSafety_typing__rename___redArg(x_2, x_21, x_4, x_7, x_5, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_stlc_TypeSafety_typing__subst___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 1, x_10);
lean_ctor_set(x_6, 0, x_1);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_20);
lean_dec_ref(x_6);
x_21 = lean_box(0);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__4), 5, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_1);
lean_inc(x_5);
x_24 = lean_apply_3(x_2, x_19, x_5, x_20);
x_25 = lp_stlc_TypeSafety_typing__rename___redArg(x_1, x_23, x_3, x_5, x_22, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_stlc_TypeSafety_typing__subst___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_lp_stlc_TypeSafety_typing__subst___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
x_9 = lean_apply_3(x_5, x_7, x_4, x_8);
return x_9;
}
case 1:
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 2);
x_13 = lean_ctor_get(x_6, 3);
x_14 = lean_ctor_get(x_6, 4);
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = lp_stlc_TypeSafety_typing__subst___redArg___closed__0;
lean_inc(x_11);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__1), 5, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_11);
lean_inc(x_2);
lean_inc(x_11);
x_18 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__2___boxed), 8, 5);
lean_closure_set(x_18, 0, x_11);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_5);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
x_19 = lean_alloc_closure((void*)(lp_stlc_STLC_exts___boxed), 2, 1);
lean_closure_set(x_19, 0, x_3);
lean_inc_ref(x_19);
x_20 = lp_stlc_STLC_subst(x_19, x_13);
lean_inc(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_2);
lean_inc(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_2);
lean_inc(x_12);
x_23 = lp_stlc_TypeSafety_typing__subst___redArg(x_21, x_22, x_19, x_12, x_18, x_14);
lean_ctor_set(x_6, 4, x_23);
lean_ctor_set(x_6, 3, x_20);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 2);
x_26 = lean_ctor_get(x_6, 3);
x_27 = lean_ctor_get(x_6, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_28 = lp_stlc_TypeSafety_typing__subst___redArg___closed__0;
lean_inc(x_24);
lean_inc(x_2);
x_29 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__1), 5, 2);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_24);
lean_inc(x_2);
lean_inc(x_24);
x_30 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__2___boxed), 8, 5);
lean_closure_set(x_30, 0, x_24);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_5);
lean_closure_set(x_30, 3, x_28);
lean_closure_set(x_30, 4, x_29);
x_31 = lean_alloc_closure((void*)(lp_stlc_STLC_exts___boxed), 2, 1);
lean_closure_set(x_31, 0, x_3);
lean_inc_ref(x_31);
x_32 = lp_stlc_STLC_subst(x_31, x_26);
lean_inc(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_1);
lean_inc(x_2);
lean_inc(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_2);
lean_inc(x_25);
x_35 = lp_stlc_TypeSafety_typing__subst___redArg(x_33, x_34, x_31, x_25, x_30, x_27);
x_36 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_35);
return x_36;
}
}
case 2:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_6, 3);
x_40 = lean_ctor_get(x_6, 4);
x_41 = lean_ctor_get(x_6, 5);
x_42 = lean_ctor_get(x_6, 6);
x_43 = lean_ctor_get(x_6, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
lean_inc_ref(x_3);
x_45 = lp_stlc_STLC_subst(x_3, x_39);
lean_inc_ref(x_3);
x_46 = lp_stlc_STLC_subst(x_3, x_40);
lean_inc(x_4);
lean_inc(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_47, x_5, x_41);
lean_inc(x_38);
lean_inc(x_2);
x_49 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_38, x_5, x_42);
lean_ctor_set(x_6, 6, x_49);
lean_ctor_set(x_6, 5, x_48);
lean_ctor_set(x_6, 4, x_46);
lean_ctor_set(x_6, 3, x_45);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_6, 1);
x_51 = lean_ctor_get(x_6, 3);
x_52 = lean_ctor_get(x_6, 4);
x_53 = lean_ctor_get(x_6, 5);
x_54 = lean_ctor_get(x_6, 6);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_6);
lean_inc_ref(x_3);
x_55 = lp_stlc_STLC_subst(x_3, x_51);
lean_inc_ref(x_3);
x_56 = lp_stlc_STLC_subst(x_3, x_52);
lean_inc(x_4);
lean_inc(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_57, x_5, x_53);
lean_inc(x_50);
lean_inc(x_2);
x_59 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_50, x_5, x_54);
x_60 = lean_alloc_ctor(2, 7, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_60, 2, x_4);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_58);
lean_ctor_set(x_60, 6, x_59);
return x_60;
}
}
case 3:
{
uint8_t x_61; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_6);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_6, 0);
lean_dec(x_62);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_63; 
lean_dec(x_6);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_2);
return x_63;
}
}
case 4:
{
uint8_t x_64; 
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_6);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_6, 1);
x_66 = lean_ctor_get(x_6, 2);
x_67 = lean_ctor_get(x_6, 0);
lean_dec(x_67);
lean_inc_ref(x_3);
x_68 = lp_stlc_STLC_subst(x_3, x_65);
x_69 = lean_box(0);
lean_inc(x_2);
x_70 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_69, x_5, x_66);
lean_ctor_set(x_6, 2, x_70);
lean_ctor_set(x_6, 1, x_68);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_6, 1);
x_72 = lean_ctor_get(x_6, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_6);
lean_inc_ref(x_3);
x_73 = lp_stlc_STLC_subst(x_3, x_71);
x_74 = lean_box(0);
lean_inc(x_2);
x_75 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_74, x_5, x_72);
x_76 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_75);
return x_76;
}
}
default: 
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_6);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_78 = lean_ctor_get(x_6, 2);
x_79 = lean_ctor_get(x_6, 3);
x_80 = lean_ctor_get(x_6, 4);
x_81 = lean_ctor_get(x_6, 5);
x_82 = lean_ctor_get(x_6, 6);
x_83 = lean_ctor_get(x_6, 7);
x_84 = lean_ctor_get(x_6, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_6, 0);
lean_dec(x_85);
x_86 = lp_stlc_TypeSafety_typing__subst___redArg___closed__0;
lean_inc_ref(x_5);
lean_inc(x_2);
x_87 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_87, 0, x_2);
lean_closure_set(x_87, 1, x_5);
lean_closure_set(x_87, 2, x_86);
lean_inc_ref(x_3);
x_88 = lp_stlc_STLC_subst(x_3, x_78);
lean_inc_ref(x_3);
x_89 = lp_stlc_STLC_subst(x_3, x_79);
lean_inc_ref(x_3);
x_90 = lean_alloc_closure((void*)(lp_stlc_STLC_exts___boxed), 2, 1);
lean_closure_set(x_90, 0, x_3);
lean_inc_ref(x_90);
x_91 = lp_stlc_STLC_subst(x_90, x_80);
x_92 = lean_box(0);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_93 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_92, x_5, x_81);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_94 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_4, x_5, x_82);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_1);
lean_inc(x_2);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_2);
lean_inc(x_4);
x_97 = lp_stlc_TypeSafety_typing__subst___redArg(x_95, x_96, x_90, x_4, x_87, x_83);
lean_ctor_set(x_6, 7, x_97);
lean_ctor_set(x_6, 6, x_94);
lean_ctor_set(x_6, 5, x_93);
lean_ctor_set(x_6, 4, x_91);
lean_ctor_set(x_6, 3, x_89);
lean_ctor_set(x_6, 2, x_88);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_6, 2);
x_99 = lean_ctor_get(x_6, 3);
x_100 = lean_ctor_get(x_6, 4);
x_101 = lean_ctor_get(x_6, 5);
x_102 = lean_ctor_get(x_6, 6);
x_103 = lean_ctor_get(x_6, 7);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_6);
x_104 = lp_stlc_TypeSafety_typing__subst___redArg___closed__0;
lean_inc_ref(x_5);
lean_inc(x_2);
x_105 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__subst___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_105, 0, x_2);
lean_closure_set(x_105, 1, x_5);
lean_closure_set(x_105, 2, x_104);
lean_inc_ref(x_3);
x_106 = lp_stlc_STLC_subst(x_3, x_98);
lean_inc_ref(x_3);
x_107 = lp_stlc_STLC_subst(x_3, x_99);
lean_inc_ref(x_3);
x_108 = lean_alloc_closure((void*)(lp_stlc_STLC_exts___boxed), 2, 1);
lean_closure_set(x_108, 0, x_3);
lean_inc_ref(x_108);
x_109 = lp_stlc_STLC_subst(x_108, x_100);
x_110 = lean_box(0);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_111 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_110, x_5, x_101);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_112 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_4, x_5, x_102);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_1);
lean_inc(x_2);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_2);
lean_inc(x_4);
x_115 = lp_stlc_TypeSafety_typing__subst___redArg(x_113, x_114, x_108, x_4, x_105, x_103);
x_116 = lean_alloc_ctor(5, 8, 0);
lean_ctor_set(x_116, 0, x_2);
lean_ctor_set(x_116, 1, x_4);
lean_ctor_set(x_116, 2, x_106);
lean_ctor_set(x_116, 3, x_107);
lean_ctor_set(x_116, 4, x_109);
lean_ctor_set(x_116, 5, x_111);
lean_ctor_set(x_116, 6, x_112);
lean_ctor_set(x_116, 7, x_115);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__subst___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__subst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__subst(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_stlc_TypeSafety_typing__single__subst___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 3);
x_7 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_7);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_typing__single__subst___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__single__subst___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(lp_stlc_TypeSafety_typing__single__subst___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
x_10 = lp_stlc_TypeSafety_typing__subst___redArg(x_9, x_1, x_7, x_2, x_8, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__single__subst___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_typing__single__subst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_stlc_TypeSafety_typing__single__subst(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_preservation___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_ctor_get(x_2, 4);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_inc(x_1);
lean_inc(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_1);
x_16 = lp_stlc_TypeSafety_preservation___redArg(x_15, x_9, x_6);
lean_ctor_set(x_2, 5, x_16);
lean_ctor_set(x_2, 4, x_5);
lean_ctor_set(x_2, 3, x_4);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_ctor_get(x_2, 6);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_20 = lean_box(0);
lean_inc(x_1);
lean_inc(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_1);
x_22 = lp_stlc_TypeSafety_preservation___redArg(x_21, x_18, x_6);
x_23 = lean_alloc_ctor(2, 7, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_1);
lean_ctor_set(x_23, 3, x_4);
lean_ctor_set(x_23, 4, x_5);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_23, 6, x_19);
return x_23;
}
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_26);
lean_dec_ref(x_3);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 6);
x_30 = lean_ctor_get(x_2, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_2, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_inc(x_28);
x_35 = lp_stlc_TypeSafety_preservation___redArg(x_28, x_29, x_26);
lean_ctor_set(x_2, 6, x_35);
lean_ctor_set(x_2, 4, x_25);
lean_ctor_set(x_2, 3, x_24);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 5);
x_38 = lean_ctor_get(x_2, 6);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_39 = lean_box(0);
lean_inc(x_36);
x_40 = lp_stlc_TypeSafety_preservation___redArg(x_36, x_38, x_26);
x_41 = lean_alloc_ctor(2, 7, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_1);
lean_ctor_set(x_41, 3, x_24);
lean_ctor_set(x_41, 4, x_25);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_41, 6, x_40);
return x_41;
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
lean_dec_ref(x_3);
x_45 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_45);
lean_dec_ref(x_2);
x_46 = lean_ctor_get(x_42, 4);
lean_inc_ref(x_46);
lean_dec_ref(x_42);
x_47 = lean_box(0);
x_48 = lp_stlc_TypeSafety_typing__single__subst___redArg(x_47, x_1, x_43, x_44, x_46, x_45);
return x_48;
}
case 3:
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_1);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_50);
lean_dec_ref(x_3);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get(x_2, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_2, 0);
lean_dec(x_54);
x_55 = lean_box(0);
x_56 = lean_box(0);
x_57 = lp_stlc_TypeSafety_preservation___redArg(x_56, x_52, x_50);
lean_ctor_set(x_2, 2, x_57);
lean_ctor_set(x_2, 1, x_49);
lean_ctor_set(x_2, 0, x_55);
return x_2;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = lean_box(0);
x_61 = lp_stlc_TypeSafety_preservation___redArg(x_60, x_58, x_50);
x_62 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_49);
lean_ctor_set(x_62, 2, x_61);
return x_62;
}
}
case 4:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_66);
lean_dec_ref(x_3);
x_67 = !lean_is_exclusive(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_2, 5);
x_69 = lean_ctor_get(x_2, 4);
lean_dec(x_69);
x_70 = lean_ctor_get(x_2, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_2, 2);
lean_dec(x_71);
x_72 = lean_ctor_get(x_2, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = lp_stlc_TypeSafety_preservation___redArg(x_75, x_68, x_66);
lean_ctor_set(x_2, 5, x_76);
lean_ctor_set(x_2, 4, x_65);
lean_ctor_set(x_2, 3, x_64);
lean_ctor_set(x_2, 2, x_63);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_74);
return x_2;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_2, 5);
x_78 = lean_ctor_get(x_2, 6);
x_79 = lean_ctor_get(x_2, 7);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_2);
x_80 = lean_box(0);
x_81 = lean_box(0);
x_82 = lp_stlc_TypeSafety_preservation___redArg(x_81, x_77, x_66);
x_83 = lean_alloc_ctor(5, 8, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_1);
lean_ctor_set(x_83, 2, x_63);
lean_ctor_set(x_83, 3, x_64);
lean_ctor_set(x_83, 4, x_65);
lean_ctor_set(x_83, 5, x_82);
lean_ctor_set(x_83, 6, x_78);
lean_ctor_set(x_83, 7, x_79);
return x_83;
}
}
case 5:
{
lean_object* x_84; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_84 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_84);
lean_dec_ref(x_2);
return x_84;
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_3, 0);
lean_inc(x_86);
lean_dec_ref(x_3);
x_87 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_87);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_85, 2);
lean_inc_ref(x_88);
lean_dec_ref(x_85);
x_89 = lean_box(0);
x_90 = lean_box(0);
x_91 = lp_stlc_TypeSafety_typing__single__subst___redArg(x_89, x_1, x_90, x_86, x_87, x_88);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_preservation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_preservation___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_preservation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_preservation(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_stlc_TypeSafety_ProgressResult_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_stlc_TypeSafety_ProgressResult_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_stlc_TypeSafety_ProgressResult_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_stlc_TypeSafety_ProgressResult_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_step_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_step_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_step_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_ProgressResult_step_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_done_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_done_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_ProgressResult_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_ProgressResult_done_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_ProgressResult_done_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_lp_stlc_TypeSafety_progress___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 2:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
lean_inc(x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_2);
lean_inc(x_9);
x_15 = lp_stlc_TypeSafety_progress___redArg(x_9, x_14, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec_ref(x_13);
lean_dec(x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_10);
lean_inc(x_17);
lean_ctor_set(x_1, 0, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_20);
lean_ctor_set(x_1, 0, x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec_ref(x_15);
lean_inc(x_10);
x_25 = lp_stlc_TypeSafety_progress___redArg(x_10, x_11, x_13);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_inc(x_9);
lean_ctor_set(x_1, 1, x_27);
x_29 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_25, 1, x_29);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
lean_inc(x_30);
lean_inc(x_9);
lean_ctor_set(x_1, 1, x_30);
x_32 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_10);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_24);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_free_object(x_1);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec_ref(x_25);
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_24, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_24, 0);
lean_dec(x_39);
lean_inc(x_10);
lean_inc(x_36);
x_40 = lp_stlc_STLC_single__subst(x_36, x_10);
x_41 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_10);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_24, 1, x_41);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_36);
x_42 = lp_stlc_STLC_single__subst(x_36, x_10);
x_43 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_10);
lean_ctor_set(x_43, 3, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_49);
lean_dec_ref(x_3);
lean_inc(x_47);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_2);
lean_inc(x_45);
x_51 = lp_stlc_TypeSafety_progress___redArg(x_45, x_50, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_49);
lean_dec(x_47);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
lean_inc(x_46);
lean_inc(x_52);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_46);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_53);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec_ref(x_51);
lean_inc(x_46);
x_59 = lp_stlc_TypeSafety_progress___redArg(x_46, x_47, x_49);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
lean_inc(x_60);
lean_inc(x_45);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_45);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_46);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_58);
lean_ctor_set(x_64, 4, x_61);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
lean_dec_ref(x_59);
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
lean_dec(x_45);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
lean_inc(x_46);
lean_inc(x_68);
x_70 = lp_stlc_STLC_single__subst(x_68, x_46);
x_71 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_46);
lean_ctor_set(x_71, 3, x_66);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
case 3:
{
lean_object* x_73; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_73 = lp_stlc_TypeSafety_progress___redArg___closed__0;
return x_73;
}
case 4:
{
uint8_t x_74; 
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_1);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_1, 0);
x_77 = lean_ctor_get(x_3, 2);
x_78 = lean_ctor_get(x_3, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_inc(x_76);
x_81 = lp_stlc_TypeSafety_progress___redArg(x_76, x_80, x_77);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 2, x_84);
lean_ctor_set(x_3, 1, x_83);
lean_ctor_set(x_3, 0, x_76);
lean_ctor_set(x_81, 1, x_3);
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
lean_inc(x_85);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 2, x_86);
lean_ctor_set(x_3, 1, x_85);
lean_ctor_set(x_3, 0, x_76);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_3);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_free_object(x_3);
lean_free_object(x_1);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_81, 0, x_90);
return x_81;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
lean_dec(x_81);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_3, 2);
lean_inc(x_95);
lean_dec(x_3);
x_96 = lean_box(0);
lean_inc(x_94);
x_97 = lp_stlc_TypeSafety_progress___redArg(x_94, x_96, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
lean_inc(x_98);
lean_ctor_set(x_1, 0, x_98);
x_101 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_1);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_103);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
lean_dec(x_1);
x_108 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_108);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_109 = x_3;
} else {
 lean_dec_ref(x_3);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
lean_inc(x_107);
x_111 = lp_stlc_TypeSafety_progress___redArg(x_107, x_110, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc_ref(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
lean_inc(x_112);
x_115 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_115, 0, x_112);
if (lean_is_scalar(x_109)) {
 x_116 = lean_alloc_ctor(3, 3, 0);
} else {
 x_116 = x_109;
 lean_ctor_set_tag(x_116, 3);
}
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_113);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_109);
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set(x_120, 1, x_118);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
default: 
{
uint8_t x_122; 
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_1);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_1, 0);
x_124 = lean_ctor_get(x_1, 1);
x_125 = lean_ctor_get(x_1, 2);
x_126 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_126);
lean_dec_ref(x_3);
x_127 = lean_box(0);
lean_inc(x_123);
x_128 = lp_stlc_TypeSafety_progress___redArg(x_123, x_127, x_126);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_130);
lean_ctor_set(x_1, 0, x_130);
x_132 = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_124);
lean_ctor_set(x_132, 3, x_125);
lean_ctor_set(x_132, 4, x_131);
lean_ctor_set(x_128, 1, x_132);
lean_ctor_set(x_128, 0, x_1);
return x_128;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_128, 0);
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_128);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_133);
lean_ctor_set(x_1, 0, x_133);
x_135 = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(x_135, 0, x_123);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_124);
lean_ctor_set(x_135, 3, x_125);
lean_ctor_set(x_135, 4, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_1);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
else
{
lean_free_object(x_1);
if (lean_obj_tag(x_123) == 3)
{
lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_128);
lean_inc(x_124);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_124);
lean_ctor_set(x_137, 1, x_125);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_128, 0);
lean_inc(x_139);
lean_dec_ref(x_128);
x_140 = lean_ctor_get(x_123, 0);
lean_inc(x_140);
lean_dec_ref(x_123);
x_141 = !lean_is_exclusive(x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_139, 1);
x_143 = lean_ctor_get(x_139, 0);
lean_dec(x_143);
lean_inc(x_140);
lean_inc(x_125);
x_144 = lp_stlc_STLC_single__subst(x_125, x_140);
x_145 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_124);
lean_ctor_set(x_145, 2, x_125);
lean_ctor_set(x_145, 3, x_142);
lean_ctor_set_tag(x_139, 0);
lean_ctor_set(x_139, 1, x_145);
lean_ctor_set(x_139, 0, x_144);
return x_139;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
lean_dec(x_139);
lean_inc(x_140);
lean_inc(x_125);
x_147 = lp_stlc_STLC_single__subst(x_125, x_140);
x_148 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_124);
lean_ctor_set(x_148, 2, x_125);
lean_ctor_set(x_148, 3, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_1, 0);
x_151 = lean_ctor_get(x_1, 1);
x_152 = lean_ctor_get(x_1, 2);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_1);
x_153 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_153);
lean_dec_ref(x_3);
x_154 = lean_box(0);
lean_inc(x_150);
x_155 = lp_stlc_TypeSafety_progress___redArg(x_150, x_154, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc_ref(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_156);
x_159 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_152);
x_160 = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_151);
lean_ctor_set(x_160, 3, x_152);
lean_ctor_set(x_160, 4, x_157);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
else
{
if (lean_obj_tag(x_150) == 3)
{
lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_155);
lean_inc(x_151);
x_162 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_152);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_151);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_155, 0);
lean_inc(x_164);
lean_dec_ref(x_155);
x_165 = lean_ctor_get(x_150, 0);
lean_inc(x_165);
lean_dec_ref(x_150);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
lean_inc(x_165);
lean_inc(x_152);
x_168 = lp_stlc_STLC_single__subst(x_152, x_165);
x_169 = lean_alloc_ctor(6, 4, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_151);
lean_ctor_set(x_169, 2, x_152);
lean_ctor_set(x_169, 3, x_166);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
 lean_ctor_set_tag(x_170, 0);
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_progress___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_stlc_TypeSafety_progress(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_stlc_TypeSafety_progress__top(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_stlc_TypeSafety_progress___redArg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_stlc_STLC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_stlc_TypeSafety(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_stlc_STLC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_stlc_TypeSafety_typing__subst___redArg___closed__0 = _init_lp_stlc_TypeSafety_typing__subst___redArg___closed__0();
lean_mark_persistent(lp_stlc_TypeSafety_typing__subst___redArg___closed__0);
lp_stlc_TypeSafety_progress___redArg___closed__0 = _init_lp_stlc_TypeSafety_progress___redArg___closed__0();
lean_mark_persistent(lp_stlc_TypeSafety_progress___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

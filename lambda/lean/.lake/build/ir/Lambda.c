// Lean compiler output
// Module: Lambda
// Imports: public import Init
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
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_app_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_ext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_lam_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_ext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_lam_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_app_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_rename(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_lam_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_var_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_lambda_Lambda_exts___closed__0;
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_var_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_lambda_Lambda_exts___closed__1;
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_lam_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_subst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_single__subst___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_single__subst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_lam_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_single__subst___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_lambda_Lambda_Term_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lambda_Lambda_Term_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lambda_Lambda_Term_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_lambda_Lambda_Term_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_lam_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_lam_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_lambda_Lambda_Term_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_app_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Term_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Term_app_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_lambda_Lambda_Term_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_ext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_nat_add(x_7, x_5);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_ext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_ext(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_rename(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_alloc_closure((void*)(lp_lambda_Lambda_ext___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lp_lambda_Lambda_rename(x_11, x_10);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_closure((void*)(lp_lambda_Lambda_ext___boxed), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lp_lambda_Lambda_rename(x_14, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
default: 
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_20 = lp_lambda_Lambda_rename(x_1, x_18);
x_21 = lp_lambda_Lambda_rename(x_1, x_19);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc_ref(x_1);
x_24 = lp_lambda_Lambda_rename(x_1, x_22);
x_25 = lp_lambda_Lambda_rename(x_1, x_23);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_lambda_Lambda_exts___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_lambda_Lambda_exts___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_lambda_Lambda_exts___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_lambda_Lambda_exts___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lp_lambda_Lambda_exts___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lp_lambda_Lambda_exts___closed__1;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lp_lambda_Lambda_rename(x_6, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_exts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_exts(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_subst(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_alloc_closure((void*)(lp_lambda_Lambda_exts___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lp_lambda_Lambda_subst(x_7, x_6);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(lp_lambda_Lambda_exts___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lp_lambda_Lambda_subst(x_10, x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
default: 
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_16 = lp_lambda_Lambda_subst(x_1, x_14);
x_17 = lp_lambda_Lambda_subst(x_1, x_15);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
lean_inc_ref(x_1);
x_20 = lp_lambda_Lambda_subst(x_1, x_18);
x_21 = lp_lambda_Lambda_subst(x_1, x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_single__subst___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_inc_ref(x_1);
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
LEAN_EXPORT lean_object* lp_lambda_Lambda_single__subst___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_single__subst___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_single__subst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(lp_lambda_Lambda_single__subst___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lp_lambda_Lambda_subst(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_lambda_Lambda_Value_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Value_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Value_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_lambda_Lambda_Value_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_lambda_Lambda_Value_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Value_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lambda_Lambda_Value_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_var_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lambda_Lambda_Value_var_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_lam_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lambda_Lambda_Value_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_lam_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lambda_Lambda_Value_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lambda_Lambda_Value_lam_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lambda_Lambda_Value_lam_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lambda_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lambda_Lambda_exts___closed__0 = _init_lp_lambda_Lambda_exts___closed__0();
lean_mark_persistent(lp_lambda_Lambda_exts___closed__0);
lp_lambda_Lambda_exts___closed__1 = _init_lp_lambda_Lambda_exts___closed__1();
lean_mark_persistent(lp_lambda_Lambda_exts___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

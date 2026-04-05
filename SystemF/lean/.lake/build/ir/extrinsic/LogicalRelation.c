// Lean compiler output
// Module: extrinsic.LogicalRelation
// Imports: public import Init public import extrinsic.Reduction
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
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_extendRelSub(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_emptyRelEnv___closed__0;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_extendRelSub___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_emptyRelSub___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_emptyRelEnv___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_systemf_Extrinsic_consSub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_emptyRelSub___closed__1;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_emptyRelSub;
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv(lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_extendRelEnv(lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_emptyRelSub___closed__0;
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_emptyRelEnv;
static lean_object* lp_systemf_Extrinsic_emptyRelEnv___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_systemf_Extrinsic_consSubT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_emptyRelSub___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_emptyRelSub___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_emptyRelSub___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_systemf_Extrinsic_emptyRelSub___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_systemf_Extrinsic_emptyRelSub___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_emptyRelSub() {
_start:
{
lean_object* x_1; 
x_1 = lp_systemf_Extrinsic_emptyRelSub___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_extendRelSub___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSubT___boxed), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSubT___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_6);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSubT___boxed), 3, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_9);
x_12 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSubT___boxed), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_extendRelSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf_Extrinsic_extendRelSub___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_emptyRelEnv___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_emptyRelEnv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_emptyRelEnv___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_systemf_Extrinsic_emptyRelEnv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_systemf_Extrinsic_emptyRelEnv___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_emptyRelEnv() {
_start:
{
lean_object* x_1; 
x_1 = lp_systemf_Extrinsic_emptyRelEnv___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_extendRelEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSub___boxed), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSub___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_6);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSub___boxed), 3, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_9);
x_12 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_consSub___boxed), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_systemf_Extrinsic_tailRelEnv___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_systemf_Extrinsic_tailRelEnv___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_tailRelEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_tailRelEnv___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(lp_systemf_Extrinsic_tailRelEnv___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_extendRelSub_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__7_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_6(x_7, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
case 1:
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_14 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
case 2:
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_15 = lean_apply_5(x_9, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_7(x_10, x_16, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_apply_6(x_11, x_19, x_2, x_3, x_4, x_5, x_6);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__7_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__7_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_apply_2(x_5, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_5(x_6, x_1, x_11, x_3, x_4, lean_box(0));
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_apply_5(x_6, x_1, x_2, x_3, x_4, lean_box(0));
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_apply_2(x_6, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_apply_5(x_7, x_2, x_12, x_4, x_5, lean_box(0));
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_apply_5(x_7, x_2, x_3, x_4, x_5, lean_box(0));
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_dec(x_2);
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_apply_2(x_5, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_5(x_6, x_1, x_11, x_3, x_4, lean_box(0));
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_apply_5(x_6, x_1, x_2, x_3, x_4, lean_box(0));
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_LogicalRelation_0__Extrinsic_VRel_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_dec(x_3);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_apply_2(x_6, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_apply_5(x_7, x_2, x_12, x_4, x_5, lean_box(0));
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_apply_5(x_7, x_2, x_3, x_4, x_5, lean_box(0));
return x_14;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Reduction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_systemf_extrinsic_LogicalRelation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_systemf_Extrinsic_emptyRelSub___closed__0 = _init_lp_systemf_Extrinsic_emptyRelSub___closed__0();
lean_mark_persistent(lp_systemf_Extrinsic_emptyRelSub___closed__0);
lp_systemf_Extrinsic_emptyRelSub___closed__1 = _init_lp_systemf_Extrinsic_emptyRelSub___closed__1();
lean_mark_persistent(lp_systemf_Extrinsic_emptyRelSub___closed__1);
lp_systemf_Extrinsic_emptyRelSub = _init_lp_systemf_Extrinsic_emptyRelSub();
lean_mark_persistent(lp_systemf_Extrinsic_emptyRelSub);
lp_systemf_Extrinsic_emptyRelEnv___closed__0 = _init_lp_systemf_Extrinsic_emptyRelEnv___closed__0();
lean_mark_persistent(lp_systemf_Extrinsic_emptyRelEnv___closed__0);
lp_systemf_Extrinsic_emptyRelEnv___closed__1 = _init_lp_systemf_Extrinsic_emptyRelEnv___closed__1();
lean_mark_persistent(lp_systemf_Extrinsic_emptyRelEnv___closed__1);
lp_systemf_Extrinsic_emptyRelEnv = _init_lp_systemf_Extrinsic_emptyRelEnv();
lean_mark_persistent(lp_systemf_Extrinsic_emptyRelEnv);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: extrinsic.Parametricity
// Imports: public import Init public import extrinsic.LogicalRelation
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VBoolRel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VBoolRel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_GRel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VNatRel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_ERel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_GRel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_ERel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VNatRel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VNatRel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 3)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_3(x_6, x_2, x_4, lean_box(0));
return x_12;
}
}
case 4:
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_2);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec_ref(x_4);
x_17 = lean_apply_4(x_7, x_13, x_14, x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec_ref(x_3);
x_20 = lean_apply_5(x_8, x_2, x_18, x_19, x_4, lean_box(0));
return x_20;
}
}
default: 
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_apply_8(x_9, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VNatRel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 3:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_apply_3(x_7, x_3, x_5, lean_box(0));
return x_13;
}
}
case 4:
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_3);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec_ref(x_5);
x_18 = lean_apply_4(x_8, x_14, x_15, x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec_ref(x_4);
x_21 = lean_apply_5(x_9, x_3, x_19, x_20, x_5, lean_box(0));
return x_21;
}
}
default: 
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_apply_8(x_10, x_2, x_3, x_4, x_5, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VBoolRel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = lean_box(3);
x_11 = lean_apply_6(x_7, x_10, x_2, x_3, x_4, lean_box(0), lean_box(0));
return x_11;
}
}
case 2:
{
lean_dec(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_6, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(4);
x_15 = lean_apply_6(x_7, x_14, x_2, x_3, x_4, lean_box(0), lean_box(0));
return x_15;
}
}
default: 
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_apply_6(x_7, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_VBoolRel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_dec(x_7);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_box(3);
x_12 = lean_apply_6(x_8, x_11, x_3, x_4, x_5, lean_box(0), lean_box(0));
return x_12;
}
}
case 2:
{
lean_dec(x_6);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_box(4);
x_16 = lean_apply_6(x_8, x_15, x_3, x_4, x_5, lean_box(0), lean_box(0));
return x_16;
}
}
default: 
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_apply_6(x_8, x_2, x_3, x_4, x_5, lean_box(0), lean_box(0));
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_GRel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
x_6 = lean_apply_2(x_4, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_4(x_5, x_7, x_8, x_2, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_GRel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_GRel_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extT_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_extendRelSub_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_ERel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_Parametricity_0__Extrinsic_ERel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_LogicalRelation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_systemf_extrinsic_Parametricity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_LogicalRelation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

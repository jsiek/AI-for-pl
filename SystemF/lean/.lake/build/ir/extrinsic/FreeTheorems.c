// Lean compiler output
// Module: extrinsic.FreeTheorems
// Imports: public import Init public import extrinsic.Parametricity
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_flip___closed__0;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_flip;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_VRel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_neg___closed__2;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_neg___closed__1;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf_Extrinsic_neg;
static lean_object* lp_systemf_Extrinsic_neg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_VRel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_flip___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_systemf_Extrinsic_flip___closed__2;
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_VRel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_VRel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_extendRelSub_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_lp_systemf_Extrinsic_neg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_neg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(3);
x_2 = lean_box(4);
x_3 = lp_systemf_Extrinsic_neg___closed__0;
x_4 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_lp_systemf_Extrinsic_neg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_systemf_Extrinsic_neg___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_neg() {
_start:
{
lean_object* x_1; 
x_1 = lp_systemf_Extrinsic_neg___closed__2;
return x_1;
}
}
static lean_object* _init_lp_systemf_Extrinsic_flip___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(5);
x_2 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_flip___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(5);
x_2 = lp_systemf_Extrinsic_flip___closed__0;
x_3 = lp_systemf_Extrinsic_neg___closed__0;
x_4 = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_lp_systemf_Extrinsic_flip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_systemf_Extrinsic_flip___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_systemf_Extrinsic_flip() {
_start:
{
lean_object* x_1; 
x_1 = lp_systemf_Extrinsic_flip___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_systemf___private_extrinsic_FreeTheorems_0__Extrinsic_ext_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Parametricity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_systemf_extrinsic_FreeTheorems(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Parametricity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_systemf_Extrinsic_neg___closed__0 = _init_lp_systemf_Extrinsic_neg___closed__0();
lean_mark_persistent(lp_systemf_Extrinsic_neg___closed__0);
lp_systemf_Extrinsic_neg___closed__1 = _init_lp_systemf_Extrinsic_neg___closed__1();
lean_mark_persistent(lp_systemf_Extrinsic_neg___closed__1);
lp_systemf_Extrinsic_neg___closed__2 = _init_lp_systemf_Extrinsic_neg___closed__2();
lean_mark_persistent(lp_systemf_Extrinsic_neg___closed__2);
lp_systemf_Extrinsic_neg = _init_lp_systemf_Extrinsic_neg();
lean_mark_persistent(lp_systemf_Extrinsic_neg);
lp_systemf_Extrinsic_flip___closed__0 = _init_lp_systemf_Extrinsic_flip___closed__0();
lean_mark_persistent(lp_systemf_Extrinsic_flip___closed__0);
lp_systemf_Extrinsic_flip___closed__1 = _init_lp_systemf_Extrinsic_flip___closed__1();
lean_mark_persistent(lp_systemf_Extrinsic_flip___closed__1);
lp_systemf_Extrinsic_flip___closed__2 = _init_lp_systemf_Extrinsic_flip___closed__2();
lean_mark_persistent(lp_systemf_Extrinsic_flip___closed__2);
lp_systemf_Extrinsic_flip = _init_lp_systemf_Extrinsic_flip();
lean_mark_persistent(lp_systemf_Extrinsic_flip);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

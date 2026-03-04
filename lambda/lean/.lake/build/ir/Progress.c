// Lean compiler output
// Module: Progress
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
LEAN_EXPORT lean_object* lp_lambda_Progress_progress(lean_object*);
lean_object* lp_lambda_Lambda_single__subst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lambda_Progress_progress(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 1:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lp_lambda_Progress_progress(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_free_object(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_ctor_set(x_1, 0, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_1);
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_21);
lean_ctor_set(x_1, 0, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
lean_inc(x_26);
lean_ctor_set(x_1, 0, x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
lean_inc_ref(x_32);
x_33 = lp_lambda_Progress_progress(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_39 = x_33;
} else {
 lean_dec_ref(x_33);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
lean_inc(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_39)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_39;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_47);
x_49 = lp_lambda_Progress_progress(x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc_ref(x_48);
x_51 = lp_lambda_Progress_progress(x_48);
if (lean_obj_tag(x_51) == 0)
{
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_50, 1);
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
x_57 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_50, 1, x_57);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
x_60 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_48);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_51, 0, x_61);
return x_51;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_63 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
 x_64 = lean_box(0);
}
lean_inc_ref(x_48);
lean_inc_ref(x_47);
x_65 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_65, 0, x_47);
lean_ctor_set(x_65, 1, x_48);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_inc_ref(x_48);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_51);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_51, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_70);
lean_dec_ref(x_50);
lean_inc_ref(x_48);
lean_inc_ref(x_70);
x_71 = lp_lambda_Lambda_single__subst(x_70, x_48);
x_72 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_48);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_73);
return x_51;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_51);
x_74 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_74);
lean_dec_ref(x_50);
lean_inc_ref(x_48);
lean_inc_ref(x_74);
x_75 = lp_lambda_Lambda_single__subst(x_74, x_48);
x_76 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_48);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_50);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_1, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_1, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_51);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_51, 0);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_inc_ref(x_47);
lean_ctor_set(x_1, 1, x_85);
x_87 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_87, 0, x_47);
lean_ctor_set(x_87, 1, x_48);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set(x_83, 1, x_87);
lean_ctor_set(x_83, 0, x_1);
return x_51;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
lean_inc(x_88);
lean_inc_ref(x_47);
lean_ctor_set(x_1, 1, x_88);
x_90 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_90, 0, x_47);
lean_ctor_set(x_90, 1, x_48);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_51, 0, x_91);
return x_51;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_51, 0);
lean_inc(x_92);
lean_dec(x_51);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
lean_inc(x_93);
lean_inc_ref(x_47);
lean_ctor_set(x_1, 1, x_93);
x_96 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_96, 0, x_47);
lean_ctor_set(x_96, 1, x_48);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_99 = lean_ctor_get(x_51, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_100 = x_51;
} else {
 lean_dec_ref(x_51);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
lean_inc(x_101);
lean_inc_ref(x_47);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_47);
lean_ctor_set(x_104, 1, x_101);
x_105 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_105, 0, x_47);
lean_ctor_set(x_105, 1, x_48);
lean_ctor_set(x_105, 2, x_101);
lean_ctor_set(x_105, 3, x_102);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_inc_ref(x_48);
lean_inc_ref(x_47);
x_108 = !lean_is_exclusive(x_1);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_1, 1);
lean_dec(x_109);
x_110 = lean_ctor_get(x_1, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_49);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_49, 0);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_48);
lean_inc(x_114);
lean_ctor_set(x_1, 0, x_114);
x_116 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_116, 0, x_47);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_48);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_112, 1, x_116);
lean_ctor_set(x_112, 0, x_1);
return x_49;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_112);
lean_inc_ref(x_48);
lean_inc(x_117);
lean_ctor_set(x_1, 0, x_117);
x_119 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_119, 0, x_47);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_119, 2, x_48);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_49, 0, x_120);
return x_49;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_49, 0);
lean_inc(x_121);
lean_dec(x_49);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
lean_inc_ref(x_48);
lean_inc(x_122);
lean_ctor_set(x_1, 0, x_122);
x_125 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_125, 0, x_47);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_48);
lean_ctor_set(x_125, 3, x_123);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_1);
x_128 = lean_ctor_get(x_49, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_129 = x_49;
} else {
 lean_dec_ref(x_49);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_132 = x_128;
} else {
 lean_dec_ref(x_128);
 x_132 = lean_box(0);
}
lean_inc_ref(x_48);
lean_inc(x_130);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_48);
x_134 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_134, 0, x_47);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_48);
lean_ctor_set(x_134, 3, x_131);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_129)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_129;
}
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lambda_FullBetaReduction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lambda_Progress(uint8_t builtin) {
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

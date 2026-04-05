// Lean compiler output
// Module: SystemF
// Imports: public import Init public import extrinsic.Types public import extrinsic.TypeSubst public import extrinsic.Terms public import extrinsic.Reduction public import extrinsic.Progress public import extrinsic.Preservation public import extrinsic.TypeSafety public import extrinsic.Eval public import extrinsic.LogicalRelation public import extrinsic.Parametricity public import extrinsic.FreeTheorems public import extrinsic.Examples
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Types(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_TypeSubst(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Terms(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Reduction(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Progress(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Preservation(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_TypeSafety(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Eval(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_LogicalRelation(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Parametricity(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_FreeTheorems(uint8_t builtin);
lean_object* initialize_systemf_extrinsic_Examples(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_systemf_SystemF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_TypeSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Terms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Progress(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Preservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_TypeSafety(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_LogicalRelation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Parametricity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_FreeTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_systemf_extrinsic_Examples(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

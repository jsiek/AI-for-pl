(* Frozen specs for picol (picol_vst.c).  Do not edit in a run.

   1. The trusted specs approved by the owner (../../libc/TRUSTED_SPECS.md),
      with one body axiom each (as VST's own body_malloc): the trust base.
   2. The specs of the musl functions verified from source
      (../../libc/proofs/): not trusted, proved again inside picol's
      semax_prog.
   3. picol_main's spec (owner, 2026-11-22: every argv, C11 5.1.2.2.1)
      and main's (VST's main_pre; leak-free: main ends with mem_mgr and
      the globals only).
   Each `(* @libc f ... *)` line stands for ../../libc/specs/f.v ...
   (ariadne/targets.py expands it). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ---- 1. Trusted (../../libc/TRUSTED_SPECS.md) -------------------- *)

(* @libc FILE_handle realloc fmt_double strtod fopen fclose fputs fflush fgets fread perror *)

(* exit: VST's own exit_spec (floyd/library.v, axiom body_exit), which
   with_library adds; it is the approved spec (never returns). *)

(* ---- 2. musl, verified from source ---------------------------------- *)

(* @libc strlen strcmp strchr memcpy isupper *)

(* ---- 3. picol_main and main ----------------------------------------- *)

(* argv's strings: ptrs[k] is a writable cstring args[k]. *)
Fixpoint args_pred (args : list (list byte)) (ptrs : list val) : mpred :=
  match args, ptrs with
  | a :: args', p :: ptrs' => sepcon (cstring Ews a p) (args_pred args' ptrs')
  | _, _ => emp
  end.

Definition picol_main_spec :=
 DECLARE _picol_main
 WITH gv : globals, argc : Z, argv : val, args : list (list byte), ptrs : list val
 PRE [ tint, tptr (tptr tschar) ]
   PROP (argc = Zlength args; Zlength ptrs = argc; 0 <= argc <= Int.max_signed)
   PARAMS (Vint (Int.repr argc); argv) GLOBALS (gv)
   SEP (mem_mgr gv; globvars2pred gv (prog_vars prog);
        data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
        args_pred args ptrs)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP (mem_mgr gv; globvars2pred gv (prog_vars prog);
        data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
        args_pred args ptrs).

Definition main_spec :=
 DECLARE _main
 WITH gv : globals
 PRE [ ] main_pre prog tt gv
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP (mem_mgr gv; globvars2pred gv (prog_vars prog); has_ext tt).

(* The frozen entries a run's Gprog must contain (checked by find_id). *)
Definition frozen_specs : funspecs :=
  [realloc_spec; fmt_double_spec; strtod_spec; fopen_spec; fclose_spec;
   fputs_spec; fflush_spec; fgets_spec; fread_spec; perror_spec;
   strlen_spec; strcmp_spec; strchr_spec; memcpy_spec; isupper_spec;
   picol_main_spec; main_spec].

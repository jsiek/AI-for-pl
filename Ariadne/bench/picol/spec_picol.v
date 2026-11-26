(* Frozen specs for picol (picol_vst.c).  Do not edit in a run.

   1. The trusted specs approved by the owner (TRUSTED_SPECS.md), with
      one body axiom each (as VST's own body_malloc): the trust base.
   2. The specs of the musl functions verified from source
      (../../libc/specs/, proved in ../../libc/proofs/): not trusted,
      proved again inside picol's semax_prog.
   3. picol_main's spec (owner, 2026-11-22: every argv, C11 5.1.2.2.1)
      and main's (VST's main_pre; leak-free: main ends with mem_mgr and
      the globals only). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation FILEp := (tptr (Tstruct __IO_FILE noattr)).

(* ---- 1. Trusted ---------------------------------------------------- *)

Parameter FILE_handle : val -> mpred.            (* owning an open stream *)
Axiom FILE_handle_valid : forall f, FILE_handle f |-- valid_pointer f.
Axiom FILE_handle_ptr   : forall f, FILE_handle f |-- !! isptr f.

Definition std_stream (gv : globals) (f : val) : Prop :=
  f = gv ___stdin_FILE \/ f = gv ___stdout_FILE \/ f = gv ___stderr_FILE.

(* `t` and `old` are one WITH component, since old's type depends on t. *)
Definition realloc_spec :=
 DECLARE _realloc
 WITH told : {t : type & list (reptype t)}, p : val, n : Z, m : Z, gv : globals
 PRE [ tptr tvoid, size_t ]
   PROP (0 < m; sizeof (projT1 told) * m <= Ptrofs.max_unsigned;
         p = nullval -> n = 0 /\ projT2 told = [])
   PARAMS (p; Vptrofs (Ptrofs.repr (sizeof (projT1 told) * m))) GLOBALS (gv)
   SEP (mem_mgr gv;
        if eq_dec p nullval then emp
        else malloc_token Ews (tarray (projT1 told) n) p *
             data_at Ews (tarray (projT1 told) n) (projT2 told) p)
 POST [ tptr tvoid ] EX q : val,
   PROP () RETURN (q)
   SEP (mem_mgr gv;
        if eq_dec q nullval then
          (if eq_dec p nullval then emp
           else malloc_token Ews (tarray (projT1 told) n) p *
                data_at Ews (tarray (projT1 told) n) (projT2 told) p)
        else malloc_token Ews (tarray (projT1 told) m) q *
             data_at Ews (tarray (projT1 told) m)
               (sublist 0 (Z.min n m) (projT2 told) ++
                Zrepeat (default_val (projT1 told)) (m - Z.min n m)) q).

Definition fmt_double_spec :=
 DECLARE _fmt_double
 WITH buf : val, n : Z, v : float
 PRE [ tptr tschar, size_t, tdouble ]
   PROP (0 < n <= Ptrofs.max_unsigned)
   PARAMS (buf; Vptrofs (Ptrofs.repr n); Vfloat v)
   SEP (data_at_ Ews (tarray tschar n) buf)
 POST [ tvoid ] EX s : list byte,
   PROP () RETURN ()
   SEP (cstringn Ews s n buf).

Definition strtod_spec :=
 DECLARE _strtod
 WITH sh : share, str : val, s : list byte, endptr : val
 PRE [ tptr tschar, tptr (tptr tschar) ]
   PROP (readable_share sh)
   PARAMS (str; endptr)
   SEP (cstring sh s str;
        if eq_dec endptr nullval then emp else data_at_ Ews (tptr tschar) endptr)
 POST [ tdouble ] EX d : float, EX k : Z,
   PROP (0 <= k <= Zlength s)
   RETURN (Vfloat d)
   SEP (cstring sh s str;
        if eq_dec endptr nullval then emp
        else data_at Ews (tptr tschar) (offset_val k str) endptr).

Definition fopen_spec :=
 DECLARE _fopen
 WITH sh1 : share, sh2 : share, path : val, mode : val, sp : list byte, sm : list byte
 PRE [ tptr tschar, tptr tschar ]
   PROP (readable_share sh1; readable_share sh2)
   PARAMS (path; mode)
   SEP (cstring sh1 sp path; cstring sh2 sm mode)
 POST [ FILEp ] EX f : val,
   PROP () RETURN (f)
   SEP (cstring sh1 sp path; cstring sh2 sm mode;
        if eq_dec f nullval then emp else FILE_handle f).

Definition fclose_spec :=
 DECLARE _fclose
 WITH f : val
 PRE [ FILEp ]
   PROP () PARAMS (f)
   SEP (FILE_handle f)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP ().

Definition fputs_spec :=
 DECLARE _fputs
 WITH sh : share, str : val, s : list byte, f : val, own : bool, gv : globals
 PRE [ tptr tschar, FILEp ]
   PROP (readable_share sh)
   PARAMS (str; f) GLOBALS (gv)
   SEP (cstring sh s str;
        if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP (cstring sh s str;
        if own then FILE_handle f else emp).

Definition fflush_spec :=
 DECLARE _fflush
 WITH f : val, own : bool, gv : globals
 PRE [ FILEp ]
   PROP ()
   PARAMS (f) GLOBALS (gv)
   SEP (if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP (if own then FILE_handle f else emp).

Definition fgets_spec :=
 DECLARE _fgets
 WITH buf : val, n : Z, f : val, own : bool, gv : globals
 PRE [ tptr tschar, tint, FILEp ]
   PROP (0 < n <= Int.max_signed)
   PARAMS (buf; Vint (Int.repr n); f) GLOBALS (gv)
   SEP (data_at_ Ews (tarray tschar n) buf;
        if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ tptr tschar ] EX r : val,
   PROP () RETURN (r)
   SEP (if eq_dec r nullval then data_at_ Ews (tarray tschar n) buf
        else !! (r = buf) && EX s : list byte, cstringn Ews s n buf;
        if own then FILE_handle f else emp).

Definition fread_spec :=
 DECLARE _fread
 WITH buf : val, size : Z, nmemb : Z, f : val, own : bool, gv : globals
 PRE [ tptr tvoid, size_t, size_t, FILEp ]
   PROP (0 < size; 0 <= nmemb; size * nmemb <= Ptrofs.max_unsigned)
   PARAMS (buf; Vptrofs (Ptrofs.repr size); Vptrofs (Ptrofs.repr nmemb); f)
   GLOBALS (gv)
   SEP (data_at_ Ews (tarray tschar (size * nmemb)) buf;
        if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ size_t ] EX k : Z, EX bytes : list byte,
   PROP (0 <= k <= nmemb; Zlength bytes = (k * size)%Z)
   RETURN (Vptrofs (Ptrofs.repr k))
   SEP (data_at Ews (tarray tschar (size * nmemb))
          (map Vbyte bytes ++ Zrepeat Vundef (size * (nmemb - k))) buf;
        if own then FILE_handle f else emp).

Definition perror_spec :=
 DECLARE _perror
 WITH sh : share, str : val, s : list byte
 PRE [ tptr tschar ]
   PROP (readable_share sh)
   PARAMS (str)
   SEP (cstring sh s str)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (cstring sh s str).

(* exit: VST's own exit_spec (floyd/library.v, axiom body_exit), which
   with_library adds; it is the approved spec (never returns). *)

Axiom body_realloc : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "realloc"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr cc_default)) (snd realloc_spec).
Axiom body_fmt_double : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fmt_double"
    (mksignature (AST.Xptr :: AST.Xlong :: AST.Xfloat :: nil) AST.Xvoid cc_default))
    (snd fmt_double_spec).
Axiom body_strtod : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "strtod"
    (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xfloat cc_default)) (snd strtod_spec).
Axiom body_fopen : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fopen"
    (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xptr cc_default)) (snd fopen_spec).
Axiom body_fclose : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fclose"
    (mksignature (AST.Xptr :: nil) AST.Xint cc_default)) (snd fclose_spec).
Axiom body_fputs : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fputs"
    (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint cc_default)) (snd fputs_spec).
Axiom body_fflush : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fflush"
    (mksignature (AST.Xptr :: nil) AST.Xint cc_default)) (snd fflush_spec).
Axiom body_fgets : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fgets"
    (mksignature (AST.Xptr :: AST.Xint :: AST.Xptr :: nil) AST.Xptr cc_default))
    (snd fgets_spec).
Axiom body_fread : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fread"
    (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: AST.Xptr :: nil) AST.Xlong
       cc_default)) (snd fread_spec).
Axiom body_perror : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "perror"
    (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default)) (snd perror_spec).

(* ---- 2. musl, verified from source ---------------------------------- *)

Definition strlen_spec :=
 DECLARE _strlen
  WITH sh: share, s : list byte, str: val
  PRE [ tptr tschar ]
    PROP (readable_share sh)
    PARAMS (str)
    SEP (cstring sh s str)
  POST [ size_t ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
    SEP (cstring sh s str).

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH sh1: share, sh2: share, str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (readable_share sh1; readable_share sh2)
    PARAMS (str1; str2)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    RETURN (Vint i)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2).

Definition strchr_spec :=
 DECLARE _strchr
  WITH sh: share, str : val, s : list byte, c : byte
  PRE  [ tptr tschar, tint ]
    PROP (readable_share sh; c <> Byte.zero)
    PARAMS (str; Vbyte c)
    SEP (cstring sh s str)
  POST [ tptr tschar ]
   EX r : val,
    PROP ((exists i, Znth i s = c /\ Forall (fun d => d<>c) (sublist 0 i s)
                     /\ r = offset_val i str)
       \/ (Forall (fun d => d<>c) s /\ r = nullval))
    RETURN (r)
    SEP (cstring sh s str).

Definition memcpy_spec :=
 DECLARE _memcpy
  WITH shd : share, shs : share, dest : val, src : val, n : Z, bytes : list byte
  PRE [ tptr tvoid, tptr tvoid, size_t ]
    PROP (writable_share shd; readable_share shs;
          Zlength bytes = n; n <= Ptrofs.max_unsigned)
    PARAMS (dest; src; Vptrofs (Ptrofs.repr n))
    SEP (data_at_ shd (tarray tschar n) dest;
         data_at shs (tarray tschar n) (map Vbyte bytes) src)
  POST [ tptr tvoid ]
    PROP ()
    RETURN (dest)
    SEP (data_at shd (tarray tschar n) (map Vbyte bytes) dest;
         data_at shs (tarray tschar n) (map Vbyte bytes) src).

Definition isupper_spec :=
 DECLARE _isupper
  WITH c : Z
  PRE [ tint ]
    PROP (Int.min_signed <= c <= Int.max_signed)
    PARAMS (Vint (Int.repr c))
    SEP ()
  POST [ tint ]
   EX r : int,
    PROP ()
    RETURN (Vint r)
    SEP ().

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

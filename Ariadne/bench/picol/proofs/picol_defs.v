(* Representation predicates, funspecs and Gprog for picol. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol.
#[export] Existing Instance NullExtension.Espec.

Definition t_interp := Tstruct _picolInterp noattr.
Definition t_var := Tstruct _picolVar noattr.
Definition t_cmd := Tstruct _picolCmd noattr.
Definition t_frame := Tstruct _picolCallFrame noattr.
Definition t_parser := Tstruct _picolParser noattr.
Definition t_FILE := Tstruct __IO_FILE noattr.
Definition cmdfun_t := Tfunction (tptr t_interp :: tint :: tptr (tptr tschar) :: tptr t_cmd :: nil) tint cc_default.

(* ---------- global variables (string literals, std streams) ---------- *)

Definition litb (v: globvar type) : list byte :=
  map init_data2byte (sublist 0 (Zlength (gvar_init v) - 1) (gvar_init v)).

Definition lit (gv: globals) (i: ident) (v: globvar type) : mpred :=
  cstring Ers (litb v) (gv i).

(* what xrealloc needs to report out-of-memory *)
Definition Gx (gv: globals) : mpred :=
  (lit gv ___stringlit_1 v___stringlit_1 *
   data_at Ers (tptr t_FILE) (gv ___stderr_FILE) (gv _stderr))%logic.

Definition Gr (gv: globals) : mpred :=
  (lit gv ___stringlit_2 v___stringlit_2 *
  lit gv ___stringlit_3 v___stringlit_3 * lit gv ___stringlit_4 v___stringlit_4 *
  lit gv ___stringlit_5 v___stringlit_5 * lit gv ___stringlit_6 v___stringlit_6 *
  lit gv ___stringlit_7 v___stringlit_7 * lit gv ___stringlit_8 v___stringlit_8 *
  lit gv ___stringlit_9 v___stringlit_9 * lit gv ___stringlit_10 v___stringlit_10 *
  lit gv ___stringlit_11 v___stringlit_11 * lit gv ___stringlit_12 v___stringlit_12 *
  lit gv ___stringlit_13 v___stringlit_13 * lit gv ___stringlit_14 v___stringlit_14 *
  lit gv ___stringlit_15 v___stringlit_15 * lit gv ___stringlit_16 v___stringlit_16 *
  lit gv ___stringlit_17 v___stringlit_17 * lit gv ___stringlit_18 v___stringlit_18 *
  lit gv ___stringlit_19 v___stringlit_19 * lit gv ___stringlit_20 v___stringlit_20 *
  lit gv ___stringlit_21 v___stringlit_21 * lit gv ___stringlit_22 v___stringlit_22 *
  lit gv ___stringlit_23 v___stringlit_23 * lit gv ___stringlit_24 v___stringlit_24 *
  lit gv ___stringlit_25 v___stringlit_25 * lit gv ___stringlit_26 v___stringlit_26 *
  lit gv ___stringlit_27 v___stringlit_27 * lit gv ___stringlit_28 v___stringlit_28 *
  lit gv ___stringlit_29 v___stringlit_29 * lit gv ___stringlit_30 v___stringlit_30 *
  lit gv ___stringlit_31 v___stringlit_31 * lit gv ___stringlit_32 v___stringlit_32 *
  lit gv ___stringlit_33 v___stringlit_33 * lit gv ___stringlit_34 v___stringlit_34 *
  data_at Ers (tptr t_FILE) (gv ___stdin_FILE) (gv _stdin) *
  data_at Ers (tptr t_FILE) (gv ___stdout_FILE) (gv _stdout))%logic.

Definition G (gv: globals) : mpred := (Gx gv * Gr gv)%logic.

Lemma G_fold: forall gv, (Gx gv * Gr gv)%logic |-- G gv.
Proof. intros. unfold G. apply derives_refl. Qed.

(* ---------- heap strings ---------- *)

Definition mstr (s: list byte) (p: val) : mpred :=
  (malloc_token Ews (tarray tschar (Zlength s + 1)) p * cstring Ews s p)%logic.

Definition ostr (o: option (list byte)) (p: val) : mpred :=
  match o with
  | None => !! (p = nullval) && emp
  | Some s => mstr s p
  end.

(* a string in a buffer of n bytes, followed by arbitrary contents *)
Definition strbuf (sh: share) (s: list byte) (n: Z) (p: val) : mpred :=
  EX rest: list val,
   !! (~ In Byte.zero s /\ Zlength s < n /\ Zlength rest = n - Zlength s - 1) &&
   data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero]) ++ rest) p.

(* ---------- linked lists ---------- *)

Definition hdp {A} (ptr: A -> val) (l: list A) (tail: val) : val :=
  match l with [] => tail | a :: _ => ptr a end.

Fixpoint lseg {A} (node: A -> val -> mpred) (ptr: A -> val) (l: list A) (tail: val) : mpred :=
  match l with
  | [] => emp
  | a :: l' => (node a (hdp ptr l' tail) * lseg node ptr l' tail)%logic
  end.

Lemma lseg_app: forall {A} node (ptr: A -> val) l1 l2 tail,
  lseg node ptr (l1 ++ l2) tail = (lseg node ptr l1 (hdp ptr l2 tail) * lseg node ptr l2 tail)%logic.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc. f_equal. f_equal.
    destruct l1; simpl; auto.
Qed.

Record varrec := mkvar { v_ptr: val; v_name: list byte; v_namep: val; v_val: list byte; v_valp: val }.

Definition var_node (r: varrec) (nxt: val) : mpred :=
  (malloc_token Ews (tarray t_var 1) (v_ptr r) *
  data_at Ews t_var (v_namep r, (v_valp r, nxt)) (v_ptr r) *
  mstr (v_name r) (v_namep r) * mstr (v_val r) (v_valp r))%logic.

Record frame := mkframe { f_ptr: val; f_vars: list varrec }.
#[export] Instance Inh_frame : Inhabitant frame := mkframe nullval [].

Definition frame_node (f: frame) (parent: val) : mpred :=
  (malloc_token Ews (tarray t_frame 1) (f_ptr f) *
  data_at Ews t_frame (hdp v_ptr (f_vars f) nullval, parent) (f_ptr f) *
  lseg var_node v_ptr (f_vars f) nullval)%logic.

Record cmdrec := mkcmd { c_ptr: val; c_name: list byte; c_namep: val; c_func: val;
                         c_arg: option (list byte); c_argp: val;
                         c_body: option (list byte); c_bodyp: val }.

Definition cmd_node (c: cmdrec) (nxt: val) : mpred :=
  (malloc_token Ews (tarray t_cmd 1) (c_ptr c) *
  data_at Ews t_cmd (c_namep c, (c_func c, (nxt, (c_argp c, c_bodyp c)))) (c_ptr c) *
  mstr (c_name c) (c_namep c) * ostr (c_arg c) (c_argp c) * ostr (c_body c) (c_bodyp c))%logic.

Record istate := mkist { i_level: Z; i_frames: list frame; i_cmds: list cmdrec;
                         i_result: list byte; i_resultp: val }.

Definition frames_rep (F: list frame) := lseg frame_node f_ptr F nullval.
Definition cmds_rep (C: list cmdrec) := lseg cmd_node c_ptr C nullval.

Definition interp_rep (i: val) (st: istate) : mpred :=
  !! (0 <= i_level st <= 128 /\ i_frames st <> []) &&
  (malloc_token Ews (tarray t_interp 1) i *
   data_at Ews t_interp (Vint (Int.repr (i_level st)),
     (hdp f_ptr (i_frames st) nullval, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i *
   frames_rep (i_frames st) * cmds_rep (i_cmds st) * mstr (i_result st) (i_resultp st))%logic.

Definition set_res (st: istate) (s: list byte) (q: val) : istate :=
  mkist (i_level st) (i_frames st) (i_cmds st) s q.

Definition builtin_addrs (gv: globals) : list val :=
  [gv _picolCommandExpr; gv _picolCommandSet; gv _picolCommandPuts; gv _picolCommandIf;
   gv _picolCommandWhile; gv _picolCommandRetCodes; gv _picolCommandProc; gv _picolCommandReturn].

Definition cmd_ok (gv: globals) (c: cmdrec) : Prop :=
  In (c_func c) (builtin_addrs gv) \/
  (c_func c = gv _picolCommandCallProc /\
   exists a b, c_arg c = Some a /\ c_body c = Some b /\ Zlength b < Int.max_signed).

Definition cmds_ok (gv: globals) (C: list cmdrec) : Prop := Forall (cmd_ok gv) C.

Fixpoint find_cmd (nm: list byte) (C: list cmdrec) : val :=
  match C with
  | [] => nullval
  | c :: C' => if list_eq_dec Byte.eq_dec (c_name c) nm then c_ptr c else find_cmd nm C'
  end.

Fixpoint find_var (nm: list byte) (V: list varrec) : val :=
  match V with
  | [] => nullval
  | r :: V' => if list_eq_dec Byte.eq_dec (v_name r) nm then v_ptr r else find_var nm V'
  end.

Definition args_size (args: list (list byte)) : Z :=
  fold_right (fun a z => Zlength a + 1 + z) 0 args.

(* ---------- parser ---------- *)

Definition ptok (s: list byte) (text st en: val) : Prop :=
  exists a b, 0 <= a <= b /\ b <= Zlength s /\ st = offset_val a text /\ en = offset_val (b - 1) text.

Definition pinv (s: list byte) (text st en: val) (ty: int) : Prop :=
  (st = nullval /\ en = nullval /\ (ty = Int.repr 5 \/ ty = Int.repr 6)) \/ ptok s text st en.

Definition parser_at (p text: val) (s: list byte) (k: Z) (st en: val) (ty iq: int) : mpred :=
  data_at Tsh t_parser
    (text, (offset_val k text, (Vint (Int.repr (Zlength s - k)), (st, (en, (Vint ty, Vint iq)))))) p.

(* ---------- funspecs ---------- *)

Definition xrealloc_spec :=
 DECLARE _xrealloc
 WITH told : {t : type & list (reptype t)}, p : val, n : Z, m : Z, gv : globals
 PRE [ tptr tvoid, size_t ]
   PROP (0 < m; sizeof (projT1 told) * m <= Ptrofs.max_unsigned;
         p = nullval -> n = 0 /\ projT2 told = [])
   PARAMS (p; Vptrofs (Ptrofs.repr (sizeof (projT1 told) * m))) GLOBALS (gv)
   SEP (mem_mgr gv; Gx gv;
        if eq_dec p nullval then emp
        else malloc_token Ews (tarray (projT1 told) n) p *
             data_at Ews (tarray (projT1 told) n) (projT2 told) p)
 POST [ tptr tvoid ] EX q : val,
   PROP () RETURN (q)
   SEP (mem_mgr gv; Gx gv;
        malloc_token Ews (tarray (projT1 told) m) q *
        data_at Ews (tarray (projT1 told) m)
               (sublist 0 (Z.min n m) (projT2 told) ++
                Zrepeat (default_val (projT1 told)) (m - Z.min n m)) q).

Definition xstrdup_spec :=
 DECLARE _xstrdup
 WITH sh: share, s: list byte, str: val, gv: globals
 PRE [ tptr tschar ]
   PROP (readable_share sh)
   PARAMS (str) GLOBALS (gv)
   SEP (mem_mgr gv; Gx gv; cstring sh s str)
 POST [ tptr tschar ] EX q: val,
   PROP () RETURN (q)
   SEP (mem_mgr gv; Gx gv; cstring sh s str; mstr s q).

Definition fmt_append_spec :=
 DECLARE _fmt_append
 WITH sh: share, buf: val, n: Z, pre: list byte, rest: list val, shs: share, s: list byte, sp: val
 PRE [ tptr tschar, size_t, size_t, tptr tschar ]
   PROP (writable_share sh; readable_share shs; 0 <= Zlength pre < n; n <= Ptrofs.max_unsigned;
         ~ In Byte.zero pre; Zlength rest = n - Zlength pre)
   PARAMS (buf; Vptrofs (Ptrofs.repr n); Vptrofs (Ptrofs.repr (Zlength pre)); sp)
   SEP (data_at sh (tarray tschar n) (map Vbyte pre ++ rest) buf; cstring shs s sp)
 POST [ size_t ] EX pre': list byte, EX rest': list val,
   PROP (~ In Byte.zero pre'; Zlength pre <= Zlength pre' < n; Zlength rest' = n - Zlength pre' - 1)
   RETURN (Vptrofs (Ptrofs.repr (Zlength pre')))
   SEP (data_at sh (tarray tschar n) (map Vbyte (pre' ++ [Byte.zero]) ++ rest') buf;
        cstring shs s sp).

Definition fmt_str3_spec :=
 DECLARE _fmt_str3
 WITH sh: share, buf: val, n: Z, sha: share, a: list byte, ap: val,
      shb: share, b: list byte, bp: val, shc: share, c: list byte, cp: val
 PRE [ tptr tschar, size_t, tptr tschar, tptr tschar, tptr tschar ]
   PROP (writable_share sh; readable_share sha; readable_share shb; readable_share shc;
         0 < n <= Ptrofs.max_unsigned)
   PARAMS (buf; Vptrofs (Ptrofs.repr n); ap; bp; cp)
   SEP (data_at_ sh (tarray tschar n) buf; cstring sha a ap; cstring shb b bp; cstring shc c cp)
 POST [ tvoid ] EX s: list byte,
   PROP () RETURN ()
   SEP (strbuf sh s n buf; cstring sha a ap; cstring shb b bp; cstring shc c cp).

Definition fmt_int_spec :=
 DECLARE _fmt_int
 WITH sh: share, buf: val, n: Z, v: Z
 PRE [ tptr tschar, size_t, tint ]
   PROP (writable_share sh; 0 < n <= Ptrofs.max_unsigned; Int.min_signed <= v <= Int.max_signed)
   PARAMS (buf; Vptrofs (Ptrofs.repr n); Vint (Int.repr v))
   SEP (data_at_ sh (tarray tschar n) buf)
 POST [ tvoid ] EX s: list byte,
   PROP () RETURN ()
   SEP (strbuf sh s n buf).

Definition picolInitParser_spec :=
 DECLARE _picolInitParser
 WITH p: val, text: val, sh: share, s: list byte
 PRE [ tptr t_parser, tptr tschar ]
   PROP (readable_share sh; Zlength s <= Int.max_signed)
   PARAMS (p; text)
   SEP (data_at_ Tsh t_parser p; cstring sh s text)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (parser_at p text s 0 nullval nullval (Int.repr 5) (Int.repr 0); cstring sh s text).

Notation parse_pre_post needk := (
 WITH p: val, text: val, sh: share, s: list byte, k: Z, st: val, en: val, ty: int, iq: int
 PRE [ tptr t_parser ]
   PROP (readable_share sh; 0 <= k <= Zlength s; Zlength s <= Int.max_signed;
         if needk then k < Zlength s else True)
   PARAMS (p)
   SEP (parser_at p text s k st en ty iq; cstring sh s text)
 POST [ tint ] EX k': Z, EX st': val, EX en': val, EX ty': int, EX iq': int,
   PROP (0 <= k' <= Zlength s; ptok s text st' en')
   RETURN (Vint (Int.repr 0))
   SEP (parser_at p text s k' st' en' ty' iq'; cstring sh s text)) (only parsing).

Definition picolParseSep_spec := DECLARE _picolParseSep (parse_pre_post false).
Definition picolParseEol_spec := DECLARE _picolParseEol (parse_pre_post false).
Definition picolParseCommand_spec := DECLARE _picolParseCommand (parse_pre_post true).
Definition picolParseVar_spec := DECLARE _picolParseVar (parse_pre_post true).
Definition picolParseBrace_spec := DECLARE _picolParseBrace (parse_pre_post true).
Definition picolParseString_spec := DECLARE _picolParseString (parse_pre_post false).

Definition picolParseComment_spec :=
 DECLARE _picolParseComment
 WITH p: val, text: val, sh: share, s: list byte, k: Z, st: val, en: val, ty: int, iq: int
 PRE [ tptr t_parser ]
   PROP (readable_share sh; 0 <= k <= Zlength s; Zlength s <= Int.max_signed)
   PARAMS (p)
   SEP (parser_at p text s k st en ty iq; cstring sh s text)
 POST [ tint ] EX k': Z,
   PROP (0 <= k' <= Zlength s)
   RETURN (Vint (Int.repr 0))
   SEP (parser_at p text s k' st en ty iq; cstring sh s text).

Definition picolGetToken_spec :=
 DECLARE _picolGetToken
 WITH p: val, text: val, sh: share, s: list byte, k: Z, st: val, en: val, ty: int, iq: int
 PRE [ tptr t_parser ]
   PROP (readable_share sh; 0 <= k <= Zlength s; Zlength s <= Int.max_signed;
         pinv s text st en ty)
   PARAMS (p)
   SEP (parser_at p text s k st en ty iq; cstring sh s text)
 POST [ tint ] EX k': Z, EX st': val, EX en': val, EX ty': int, EX iq': int,
   PROP (0 <= k' <= Zlength s; pinv s text st' en' ty';
         ty' = Int.repr 6 \/ ptok s text st' en')
   RETURN (Vint (Int.repr 0))
   SEP (parser_at p text s k' st' en' ty' iq'; cstring sh s text).

Definition picolInitInterp_spec :=
 DECLARE _picolInitInterp
 WITH gv: globals
 PRE [ ]
   PROP () PARAMS () GLOBALS (gv)
   SEP (mem_mgr gv; G gv)
 POST [ tptr t_interp ] EX i: val, EX st: istate,
   PROP (i_level st = 0; i_cmds st = [])
   RETURN (i)
   SEP (mem_mgr gv; G gv; interp_rep i st).

Definition picolSetResult_spec :=
 DECLARE _picolSetResult
 WITH gv: globals, i: val, lvl: val, cf: val, cmds: val, r: list byte, rp: val,
      sh: share, s: list byte, sp: val
 PRE [ tptr t_interp, tptr tschar ]
   PROP (readable_share sh)
   PARAMS (i; sp) GLOBALS (gv)
   SEP (mem_mgr gv; Gx gv; data_at Ews t_interp (lvl, (cf, (cmds, rp))) i; mstr r rp;
        cstring sh s sp)
 POST [ tvoid ] EX q: val,
   PROP () RETURN ()
   SEP (mem_mgr gv; Gx gv; data_at Ews t_interp (lvl, (cf, (cmds, q))) i; mstr s q;
        cstring sh s sp).

Definition picolGetVar_spec :=
 DECLARE _picolGetVar
 WITH i: val, st: istate, sh: share, nm: list byte, np: val
 PRE [ tptr t_interp, tptr tschar ]
   PROP (readable_share sh)
   PARAMS (i; np)
   SEP (interp_rep i st; cstring sh nm np)
 POST [ tptr t_var ] EX k: Z,
   PROP (0 <= k < Zlength (i_frames st))
   RETURN (find_var nm (f_vars (Znth k (i_frames st))))
   SEP (interp_rep i st; cstring sh nm np).

Definition picolSetVar_spec :=
 DECLARE _picolSetVar
 WITH gv: globals, i: val, st: istate, sh1: share, nm: list byte, np: val,
      sh2: share, x: list byte, xp: val
 PRE [ tptr t_interp, tptr tschar, tptr tschar ]
   PROP (readable_share sh1; readable_share sh2)
   PARAMS (i; np; xp) GLOBALS (gv)
   SEP (mem_mgr gv; Gx gv; interp_rep i st; cstring sh1 nm np; cstring sh2 x xp)
 POST [ tvoid ] EX st': istate,
   PROP (i_level st' = i_level st; i_cmds st' = i_cmds st;
         Zlength (i_frames st') = Zlength (i_frames st))
   RETURN ()
   SEP (mem_mgr gv; Gx gv; interp_rep i st'; cstring sh1 nm np; cstring sh2 x xp).

Definition picolGetCommand_spec :=
 DECLARE _picolGetCommand
 WITH i: val, st: istate, sh: share, nm: list byte, np: val
 PRE [ tptr t_interp, tptr tschar ]
   PROP (readable_share sh)
   PARAMS (i; np)
   SEP (interp_rep i st; cstring sh nm np)
 POST [ tptr t_cmd ]
   PROP ()
   RETURN (find_cmd nm (i_cmds st))
   SEP (interp_rep i st; cstring sh nm np).

Definition picolRegisterCommand_spec :=
 DECLARE _picolRegisterCommand
 WITH gv: globals, i: val, st: istate, sh: share, nm: list byte, np: val, f: val
 PRE [ tptr t_interp, tptr tschar, tptr cmdfun_t ]
   PROP (readable_share sh; In f (builtin_addrs gv) \/ f = gv _picolCommandCallProc;
         cmds_ok gv (i_cmds st))
   PARAMS (i; np; f) GLOBALS (gv)
   SEP (mem_mgr gv; Gx gv; interp_rep i st; cstring sh nm np)
 POST [ tvoid ] EX st': istate, EX C1: list cmdrec, EX r: cmdrec, EX C2: list cmdrec,
   PROP (i_level st' = i_level st; i_frames st' = i_frames st; i_cmds st' = C1 ++ r :: C2;
         Forall (fun c => c_name c <> nm) C1; c_name r = nm; c_func r = f;
         c_arg r = None; c_body r = None; cmds_ok gv (C1 ++ C2))
   RETURN ()
   SEP (mem_mgr gv; Gx gv; interp_rep i st'; cstring sh nm np).

Definition picolEval_spec :=
 DECLARE _picolEval
 WITH gv: globals, i: val, st: istate, sh: share, s: list byte, t: val
 PRE [ tptr t_interp, tptr tschar ]
   PROP (readable_share sh; Zlength s < Int.max_signed; cmds_ok gv (i_cmds st))
   PARAMS (i; t) GLOBALS (gv)
   SEP (mem_mgr gv; G gv; interp_rep i st; cstring sh s t)
 POST [ tint ] EX st': istate, EX r: int,
   PROP (cmds_ok gv (i_cmds st'); i_level st' = i_level st;
         Zlength (i_frames st') = Zlength (i_frames st))
   RETURN (Vint r)
   SEP (mem_mgr gv; G gv; interp_rep i st'; cstring sh s t).

Definition picolExpr_spec :=
 DECLARE _picolExpr
 WITH gv: globals, i: val, lvl: Z, rest: val * (val * val), pp: val, errp: val, e: int,
      sh: share, s: list byte, sp: val, k: Z, prec: Z
 PRE [ tptr t_interp, tptr (tptr tschar), tptr tint, tint ]
   PROP (0 <= lvl <= 128; readable_share sh; 0 <= k <= Zlength s; Int.min_signed <= prec <= Int.max_signed)
   PARAMS (i; pp; errp; Vint (Int.repr prec)) GLOBALS (gv)
   SEP (lit gv ___stringlit_8 v___stringlit_8;
        data_at Ews t_interp (Vint (Int.repr lvl), rest) i;
        data_at Tsh (tptr tschar) (offset_val k sp) pp;
        data_at Tsh tint (Vint e) errp; cstring sh s sp)
 POST [ tdouble ] EX k': Z, EX e': int, EX d: float,
   PROP (0 <= k' <= Zlength s)
   RETURN (Vfloat d)
   SEP (lit gv ___stringlit_8 v___stringlit_8;
        data_at Ews t_interp (Vint (Int.repr lvl), rest) i;
        data_at Tsh (tptr tschar) (offset_val k' sp) pp;
        data_at Tsh tint (Vint e') errp; cstring sh s sp).

Definition picolExprExpansion_spec :=
 DECLARE _picolExprExpansion
 WITH gv: globals, i: val, st: istate, sh: share, s: list byte, sp: val
 PRE [ tptr t_interp, tptr tschar ]
   PROP (readable_share sh; Zlength s + 6 <= Int.max_signed; cmds_ok gv (i_cmds st))
   PARAMS (i; sp) GLOBALS (gv)
   SEP (mem_mgr gv; G gv; interp_rep i st; cstring sh s sp)
 POST [ tint ] EX st': istate, EX r: int,
   PROP (cmds_ok gv (i_cmds st'); i_level st' = i_level st;
         Zlength (i_frames st') = Zlength (i_frames st))
   RETURN (Vint r)
   SEP (mem_mgr gv; G gv; interp_rep i st'; cstring sh s sp).

Definition picolArityErr_spec :=
 DECLARE _picolArityErr
 WITH gv: globals, i: val, st: istate, sh: share, nm: list byte, np: val
 PRE [ tptr t_interp, tptr tschar ]
   PROP (readable_share sh)
   PARAMS (i; np) GLOBALS (gv)
   SEP (mem_mgr gv; G gv; interp_rep i st; cstring sh nm np)
 POST [ tint ] EX s: list byte, EX q: val,
   PROP ()
   RETURN (Vint (Int.repr 1))
   SEP (mem_mgr gv; G gv; interp_rep i (set_res st s q); cstring sh nm np).

(* the commands, all called through c->func *)
Notation cmd_fs extra := (
 WITH gv: globals, i: val, st: istate, argc: Z, argv: val, ptrs: list val,
      args: list (list byte), c: val
 PRE [ tptr t_interp, tint, tptr (tptr tschar), tptr t_cmd ]
   PROP (1 <= argc; Zlength args = argc; Zlength ptrs = argc;
         args_size args <= Int.max_signed - 10;
         cmds_ok gv (i_cmds st); In c (map c_ptr (i_cmds st)); extra gv st c)
   PARAMS (i; Vint (Int.repr argc); argv; c) GLOBALS (gv)
   SEP (mem_mgr gv; G gv; interp_rep i st;
        data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs)
 POST [ tint ] EX st': istate, EX r: int,
   PROP (cmds_ok gv (i_cmds st'); i_level st' = i_level st;
         Zlength (i_frames st') = Zlength (i_frames st))
   RETURN (Vint r)
   SEP (mem_mgr gv; G gv; interp_rep i st';
        data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs)) (only parsing).

Definition no_extra (gv: globals) (st: istate) (c: val) : Prop := True.
Definition proc_extra (gv: globals) (st: istate) (c: val) : Prop :=
  exists r, In r (i_cmds st) /\ c_ptr r = c /\ c_func r = gv _picolCommandCallProc /\
    exists a b, c_arg r = Some a /\ c_body r = Some b /\ Zlength b < Int.max_signed.

Definition picolCommandExpr_spec := DECLARE _picolCommandExpr (cmd_fs no_extra).
Definition picolCommandSet_spec := DECLARE _picolCommandSet (cmd_fs no_extra).
Definition picolCommandPuts_spec := DECLARE _picolCommandPuts (cmd_fs no_extra).
Definition picolCommandIf_spec := DECLARE _picolCommandIf (cmd_fs no_extra).
Definition picolCommandWhile_spec := DECLARE _picolCommandWhile (cmd_fs no_extra).
Definition picolCommandRetCodes_spec := DECLARE _picolCommandRetCodes (cmd_fs no_extra).
Definition picolCommandProc_spec := DECLARE _picolCommandProc (cmd_fs no_extra).
Definition picolCommandReturn_spec := DECLARE _picolCommandReturn (cmd_fs no_extra).
Definition picolCommandCallProc_spec := DECLARE _picolCommandCallProc (cmd_fs proc_extra).

Definition picolDropCallFrame_spec :=
 DECLARE _picolDropCallFrame
 WITH gv: globals, i: val, lvl: val, f: frame, F: list frame, rest: val * val
 PRE [ tptr t_interp ]
   PROP () PARAMS (i) GLOBALS (gv)
   SEP (mem_mgr gv; data_at Ews t_interp (lvl, (f_ptr f, rest)) i; frames_rep (f :: F))
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (mem_mgr gv; data_at Ews t_interp (lvl, (hdp f_ptr F nullval, rest)) i; frames_rep F).

Definition picolFreeInterp_spec :=
 DECLARE _picolFreeInterp
 WITH gv: globals, i: val, st: istate
 PRE [ tptr t_interp ]
   PROP () PARAMS (i) GLOBALS (gv)
   SEP (mem_mgr gv; interp_rep i st)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (mem_mgr gv).

(* a buffer of n bytes owned by the allocator, or NULL *)
Definition obuf (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp
  else (malloc_token Ews (tarray tschar n) p * data_at_ Ews (tarray tschar n) p)%logic.

Definition picolCallProcFail_spec :=
 DECLARE _picolCallProcFail
 WITH gv: globals, i: val, st: istate, f: frame, F: list frame,
      sh: share, s: list byte, bp: val, tp: val, n: Z
 PRE [ tptr t_interp, tptr tschar, tptr tschar ]
   PROP (readable_share sh; i_frames st = f :: F; F <> [])
   PARAMS (i; bp; tp) GLOBALS (gv)
   SEP (mem_mgr gv; Gx gv; interp_rep i st; cstring sh s bp; obuf n tp)
 POST [ tint ] EX q: val,
   PROP ()
   RETURN (Vint (Int.repr 1))
   SEP (mem_mgr gv; Gx gv; interp_rep i (mkist (i_level st) F (i_cmds st) s q);
        cstring sh s bp).

Definition picolRegisterCoreCommands_spec :=
 DECLARE _picolRegisterCoreCommands
 WITH gv: globals, i: val, st: istate
 PRE [ tptr t_interp ]
   PROP (cmds_ok gv (i_cmds st)) PARAMS (i) GLOBALS (gv)
   SEP (mem_mgr gv; G gv; interp_rep i st)
 POST [ tvoid ] EX st': istate,
   PROP (cmds_ok gv (i_cmds st'); i_level st' = i_level st)
   RETURN ()
   SEP (mem_mgr gv; G gv; interp_rep i st').

Definition __strchrnul_spec :=
 DECLARE ___strchrnul
  WITH sh: share, str : val, s : list byte, c : byte
  PRE  [ tptr tschar, tint ]
    PROP (readable_share sh; c <> Byte.zero)
    PARAMS (str; Vbyte c)
    SEP (cstring sh s str)
  POST [ tptr tschar ]
   EX i : Z,
    PROP (0 <= i <= Zlength s;
          Forall (fun d => d<>c) (sublist 0 i s);
          i = Zlength s \/ Znth i s = c)
    RETURN (offset_val i str)
    SEP (cstring sh s str).

Definition __isupper_l_spec :=
 DECLARE ___isupper_l
  WITH c : Z, l : val
  PRE [ tint, tptr (Tstruct ___locale_struct noattr) ]
    PROP (Int.min_signed <= c <= Int.max_signed)
    PARAMS (Vint (Int.repr c); l)
    SEP ()
  POST [ tint ]
   EX r : int,
    PROP ()
    RETURN (Vint r)
    SEP ().

Definition Gprog : funspecs := ltac:(with_library prog [
  realloc_spec; fmt_double_spec; strtod_spec; fopen_spec; fclose_spec;
  fputs_spec; fflush_spec; fgets_spec; fread_spec; perror_spec;
  xrealloc_spec; xstrdup_spec; fmt_append_spec; fmt_str3_spec; fmt_int_spec;
  picolInitParser_spec; picolParseSep_spec; picolParseEol_spec; picolParseCommand_spec;
  picolParseVar_spec; picolParseBrace_spec; picolParseString_spec; picolParseComment_spec;
  picolGetToken_spec; picolInitInterp_spec; picolSetResult_spec; picolGetVar_spec;
  picolSetVar_spec; picolGetCommand_spec; picolRegisterCommand_spec; picolEval_spec;
  picolExpr_spec; picolExprExpansion_spec; picolArityErr_spec; picolCommandExpr_spec;
  picolCommandSet_spec; picolCommandPuts_spec; picolCommandIf_spec; picolCommandWhile_spec;
  picolCommandRetCodes_spec; picolDropCallFrame_spec; picolFreeInterp_spec;
  picolCallProcFail_spec; picolCommandCallProc_spec; picolCommandProc_spec; picolCommandReturn_spec;
  picolRegisterCoreCommands_spec; picol_main_spec;
  strlen_spec; __strchrnul_spec; strchr_spec; strcmp_spec; memcpy_spec; isupper_spec;
  __isupper_l_spec; main_spec]).

(* VST 2.17, progs64/verif_strlib.v, verbatim (strchr calls musl's
   __strchrnul, which calls strlen: a unit with strchr also needs
   strlen.v). *)
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

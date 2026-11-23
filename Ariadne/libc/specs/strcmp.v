(* VST 2.17, progs64/verif_strlib.v, verbatim. *)
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

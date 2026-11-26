(* Ariadne: any int in, some int out, no memory. *)
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

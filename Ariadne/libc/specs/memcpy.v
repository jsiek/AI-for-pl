(* Ariadne: n bytes from src to a separate dest; the contents are copied
   (picol reads the copies as strings).  Separation makes the blocks
   disjoint, as C's restrict requires. *)
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

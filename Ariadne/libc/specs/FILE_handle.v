(* Trusted (owner-approved; ../TRUSTED_SPECS.md): an open stream, two facts
   about it, and musl's three standard streams (the program defines
   __stdin_FILE etc., as picol_vst.c does). *)
Notation FILEp := (tptr (Tstruct __IO_FILE noattr)).

Parameter FILE_handle : val -> mpred.            (* owning an open stream *)
Axiom FILE_handle_valid : forall f, FILE_handle f |-- valid_pointer f.
Axiom FILE_handle_ptr   : forall f, FILE_handle f |-- !! isptr f.

Definition std_stream (gv : globals) (f : val) : Prop :=
  f = gv ___stdin_FILE \/ f = gv ___stdout_FILE \/ f = gv ___stderr_FILE.

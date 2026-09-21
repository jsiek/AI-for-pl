This directory contains several versions of System F.

# extrinsic

Standard System F.

# curry

No type annotations on lambda and type application.  We proved
parametricity first for this version because it was much simpler.
     
# intrinsic

Standard System F with intrinsic typing. The proof of parametricity is
stalled.

# strong

Strong System F (the conversion-boundary calculus): type abstraction
enforced dynamically by seal/unseal boundaries, on the masked-entry
context design.  Type safety is proved.

# strong-rep-var

The two-universe redesign of Strong System F: representation variables
split from ordinary type variables, with lock/unlock putting names in
and out of scope instead of marking them.  Type safety is proved
(progress, preservation, determinism — unconditional, --safe, no
postulates).  See strong-rep-var/notes/PLAN.md for the experiment's
record.

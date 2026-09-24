This directory contains several versions of System F.

# extrinsic

Standard System F. The metatheory includes proofs of type safety and
parametricity.

# curry

No type annotations on lambda and type application.  We proved
parametricity first for this version because it was much simpler.
The metatheory also includes a proof of type safety.
     
# intrinsic

Standard System F with intrinsic typing. Type preservation is built
in. The progress lemma has not been proved. The proof of parametricity
is stalled.

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

# strong-rep-store

A variant of strong-rep-var for design experiments (2026-09-21).  First
change: the VALUE RESTRICTION on type abstraction — `⊢Λ` requires the
body to be a value and the congruence `ξ-Λ` is removed, so nothing
reduces under a type binder.  Everything else is strong-rep-var's; the
whole development, examples included, checks.  See the first section of
strong-rep-store/README.md. Type safety is proved.

# strong-rep-nu

A variant of strong-rep-store (2026-09-24) exploring a GTPLC-style `ν`
term with a Conversion in place of a coercion: type application
elaborates to `ν`, moving `TyBeta`'s reveal to compile time.  See
strong-rep-nu/notes/notes.md. Type safety is proved.

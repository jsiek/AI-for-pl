Rigid source-consistency ground-cast helper blocker

Command:

  agda -i GTSFImp -v0 GTSFImp/proof/ImprecisionConsistency.agda

After restricting `consistent-common-lowerᵐ` and the self-occurrence
preservation lemmas to `RigidFree`, the next exposed failure is:

  GTSFImp/proof/ImprecisionConsistency.agda:1234,59-65
  (zero ∈ᵗ A) !=< (RigidFree c)
  when checking that the expression zero∈B has type RigidFree c

This is not just an omitted argument.  The caller is
`ground-cast-target⊑`, whose current unrestricted statement is:

  Ground G
  -> NonStar B
  -> ν ⊢ B ∼ G
  -> μ ⊢ A ⊑ B
  -> μ ⊢ A ⊑ ★
  -> μ ⊢ A ⊑ G

The old proof used self-mode occurrence preservation in the universal-ground
case:

  ν ⊢ `∀ B ∼ `∀ ★
  μ ⊢ `∀ A ⊑ `∀ B
  μ ⊢ `∀ A ⊑ ★
  --------------------------------
  μ ⊢ `∀ A ⊑ `∀ ★

It ruled out the `∀⊑` star proof by transporting `zero ∈ᵗ B` across
`extᵐ ν ⊢ B ∼ ★`, reaching an impossible occurrence in `★`.  Rigid gates make
that occurrence loss real.

Concrete rigid shape:

  A = B = ＇ zero ⇒ ★
  μ = idᵐ
  ν = idᶜ

  extᵐ ν ⊢ A ∼ ★
    by first showing
      extᵐ ν ⊢ A ∼ ★ ⇒ ★
    where the domain uses the rigid projection
      flipᵐ (extᵐ ν) ⊢ ★ ∼ ＇ zero
    and then tagging the arrow ground to `★`.

Then:

  idᵐ ⊢ `∀ A ⊑ `∀ B
    by `∀⊑∀ (⇒⊑⇒ X⊑X ★⊑★)`

  idᵐ ⊢ `∀ A ⊑ ★
    by `∀⊑ nonvar-fun (∈-fun-left var-∈)
         (⇒⊑★ (X⊑★ refl) ★⊑★)`

But the old conclusion would require:

  idᵐ ⊢ `∀ (＇ zero ⇒ ★) ⊑ `∀ ★

There is no imprecision clause for this without a rigid crossing in
imprecision.  The `∀⊑∀` route would need:

  extᵐ idᵐ ⊢ ＇ zero ⇒ ★ ⊑ ★

which requires `extᵐ idᵐ zero ≡ X⊑★`, false.  The `∀⊑` route to
target ``∀ ★` would need:

  instᵐ idᵐ ⊢ ＇ zero ⇒ ★ ⊑ `∀ ★

which the function source cannot produce.

So the unrestricted `ground-cast-target⊑` statement is false after rigid
source-consistency gates.  A repair needs one of these larger statement
changes:

- add a `RigidFree`/no-rigid premise to `ground-cast-target⊑` and its mirror
  `ground-cast-source⊑`;
- or replace the conclusion with a rigid-obstruction disjunct and make callers
  discharge that disjunct from their own safety premises.

Both routes affect DGG-facing helpers (`ground-cast-source⊑` is imported by
inversion files), so this is outside the lower-bound-cluster repair unless the
public helper shape is explicitly approved.

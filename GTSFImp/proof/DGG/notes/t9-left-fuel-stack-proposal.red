T9 proposal: left value catch-up fuel stack

Date: 2026-08-17

Reason
------

The right M6 stack is organized around target casts embedded in the CTI2
derivation.  For left catch-up, the reducing side is source, so the fuel
predicate must track source cast heads instead.  Source casts may produce a
related value or source blame.  Source `β-inst` allocates on the left and has
the same cast-size decrease problem as target `β-inst`, but the result must
return `ParkedEvolve χsᴸ []`.

Before context
--------------

Live right-side definitions:

```agda
TargetCastBound : ℕ → W ∣ γ ⊢² M ⊑ M″ ∶ q → Set

ValueCatchupRightAt fuel =
  Value M
  → (rel : W ∣ γ ⊢² M ⊑ M″ ∶ q)
  → TargetCastBound fuel rel
  → ...
```

Target casts are charged at:

```agda
TargetCastBound fuel (cast⊑cast² c c′ rel q) =
  castSize c′ < fuel × TargetCastBound fuel rel

TargetCastBound fuel (⊑cast² c′ rel q) =
  castSize c′ < fuel × TargetCastBound fuel rel
```

After context
-------------

Add left-side counterparts under `proof/DGG/Catchup/`, without modifying the
existing right-side modules:

  `LeftValueCatchupDef.agda`
  `LeftFuelKnotProof.agda`

The public top-down surface remains `CatchupToLessPrecise`.

Proposed statement
------------------

```agda
module proof.DGG.Catchup.LeftValueCatchupDef where

open import Data.Nat using (ℕ; _<_)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.ValueCatchupRightDef
  using (castSize)
open import proof.DGG.Catchup.LeftBoundaryCatchupDef
  using (LeftCatchupResult)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupBoundaryKind; same-boundary)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

SourceCastBound : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → ℕ
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
  → Set
SourceCastBound fuel (CTI2.x⊑x² x∈) = ⊤
SourceCastBound fuel (CTI2.ƛ⊑ƛ² rel) = SourceCastBound fuel rel
SourceCastBound fuel (CTI2.·⊑·² rel₁ rel₂) =
  SourceCastBound fuel rel₁ × SourceCastBound fuel rel₂
SourceCastBound fuel (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.•⊑•² p∀ rel q r) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.•⊑² p∀ rel q r) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.κ⊑κ² κ p) = ⊤
SourceCastBound fuel (CTI2.cast⊑cast² c c′ rel q) =
  castSize c < fuel × SourceCastBound fuel rel
SourceCastBound fuel (CTI2.⊑cast² c′ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.⊑reveal² mono rb sameγ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.⊑conceal² mono rb sameγ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.cast⊑² c rel q) =
  castSize c < fuel × SourceCastBound fuel rel
SourceCastBound fuel (CTI2.reveal⊑² mono rb sameγ c⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.conceal⊑² partner mono rb sameγ c⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.conceal⊑conceal² partner mono rb sameγ c⊢ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.packaged-seal-star² partner mono rb sameγ c⊢ c′⊢
      rel pkg-rel q) =
  SourceCastBound fuel rel × SourceCastBound fuel pkg-rel
SourceCastBound fuel (CTI2.blame⊑² M′⊢ p) = ⊤
SourceCastBound fuel (CTI2.⊕⊑⊕² op rel₁ rel₂ r) =
  SourceCastBound fuel rel₁ × SourceCastBound fuel rel₂

LeftValueCatchupAt : ℕ → Set₁
LeftValueCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ q)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M} {V′ = V′} {A = A} {B = B}
```

This is the closed same-boundary specialization.  The actual implementation
should likely use the boundary-general worker from
`t9-left-boundary-catchup-proposal.red`:

```agda
LeftValueCatchupBoundaryAt : ℕ → Set₁
```

whose arguments include `ParkedWorld W`, `CatchupBoundary ... W Wᵖ`,
`Wᵖ ∣ [] ⊢² M ⊑ V′ ∶ q`, `Value V′`, and
`SourceCastBound fuel rel`.

Fuel knot proposal
------------------

```agda
LeftExtraCastAt : ℕ → Set₁
LeftInstCatchupAt : ℕ → Set₁

record LeftFuelKnot (fuel : ℕ) : Set₁ where
  field
    left-extra-cast-at : LeftExtraCastAt fuel
    left-inst-catchup-at : LeftInstCatchupAt fuel
    left-value-catchup-at : LeftValueCatchupAt fuel

record LeftFuelStepSurface (fuel : ℕ) : Set₁ where
  field
    smaller-left-extra :
      ∀ {m} → m < fuel → LeftExtraCastAt m
    smaller-left-inst :
      ∀ {m} → m < fuel → LeftInstCatchupAt m
    smaller-left-value :
      ∀ {m} → m < fuel → LeftValueCatchupAt m
```

Strict-decrease inputs mirror the right stack but apply to source casts:

```agda
source-ground-other-decreaseᵀ : Set
source-project-expand-decreaseᵀ : Set
source-inst-alloc-decreaseᵀ : Set
```

The existing arithmetic lemmas may be reusable because `castSize` is
side-independent.  The operational packages and endpoint relation
reconstruction are not reusable as-is.

Blocked branches covered
------------------------

This fuel stack is needed by:

  * `cast⊑²`,
  * `cast⊑cast²`,
  * source `β-inst`,
  * source `β-gen` residual casts exposed by `•⊑²`,
  * recursive source casts under `reveal⊑²`, `conceal⊑²`, and paired wrappers.

Not covered
-----------

This does not by itself solve boundary replay for source and target
conversion wrappers.  That is the separate boundary proposal.

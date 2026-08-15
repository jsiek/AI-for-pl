module CTIOccInversionCatchupScratch where

-- File Charter:
--   * Notes-only S-OCC pre-flight V1 scratch.
--   * Tests whether the generated-name target projection catch-up case can be
--     recovered from CTI inversion plus the occupancy-gated partner relation,
--     with no CatchupCast-family premise in the new statements below.
--   * Also records the ground-tag projection analogue and the replacement
--     surface an M6-style consumer would receive from inversion.
--     No live CTI2 or proof file is edited.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Types
open import Consistency using
  (Env∼; ★∼X; _⊢_∼_; _⊢_∼★; _⊢★∼_; ★∼Xᵍ; ★∼ι;
   id; idᵍ; _!; ？_)
open import Imprecision
open import CastTerms using (Term; Value; $; _⟨_⟩; _↓_; _《_》; inj; seal)
open import Reduction using
  (StoreChanges; keep; _∷_; []; _—↠[_]_; _—→[_]⟨_⟩_; _∎[];
   pure-step; tag-untag)
open import Primitives using (κℕ)

import CTITighteningNarrowScratch as N
open import CTITighteningOccScratch
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_⊑ᵂ⟨_⟩_)
import proof.Imprecision as PI

------------------------------------------------------------------------
-- Local values and projection routes
------------------------------------------------------------------------

source-base-valueᴼ : Value N.base-source
source-base-valueᴼ = $ (κℕ 0) 《 inj 》

source-sealed-valueᴼ : Value N.source-sealed
source-sealed-valueᴼ = source-base-valueᴼ ↓ seal

rawℕᴼ : Term 1
rawℕᴼ = $ (κℕ 0)

rawℕ-valueᴼ : Value rawℕᴼ
rawℕ-valueᴼ = $ (κℕ 0)

target-Y-projection-routeᴼ :
  N.target-name-tagged ⟨ N.Y? ⟩ —↠[ keep ∷ [] ] N.target-sealed
target-Y-projection-routeᴼ =
  N.target-name-tagged ⟨ N.Y? ⟩
  —→[ keep ]⟨ pure-step (tag-untag N.target-sealed-value) ⟩
  N.target-sealed ∎[]

target-Y-projection-route-valueᴼ : ∀ {μ : Env∼ 1} {V}
    {Y∼★ : μ ⊢ (＇ Fin.zero) ∼★}
  → (vV : Value V)
  → V ⟨ _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = Y∼★ ⦄
        (idᵍ (＇ Fin.zero)) ⟩
      ⟨ N.Y? ⟩
    —↠[ keep ∷ [] ] V
target-Y-projection-route-valueᴼ vV =
  _
  —→[ keep ]⟨
    pure-step
      (tag-untag {μ = _} {ν = N.target-env-project}
        {G = ＇ Fin.zero}
        ⦃ Gᵍ = ＇ Fin.zero ⦄
        ⦃ G∼★ = _ ⦄
        ⦃ ★∼G = ★∼Xᵍ refl ⦄
        vV)
  ⟩
  _ ∎[]

ℕ⊑★ᴼ : (‵ `ℕ) ⊑ᵂ⟨ N.W ⟩ ★
ℕ⊑★ᴼ = ι⊑★

ℕ⊑ℕᴼ : (‵ `ℕ) ⊑ᵂ⟨ N.W ⟩ (‵ `ℕ)
ℕ⊑ℕᴼ = ι⊑ι

record ProjectionCatchupResultᴼ
    (M′ : Term 1)
    (q : (＇ Fin.zero) ⊑ᵂ⟨ N.W ⟩ (＇ Fin.zero)) : Set where
  constructor projection-catchup-resultᴼ
  field
    V′ : Term 1
    value′ : Value V′
    steps : M′ ⟨ N.Y? ⟩ —↠[ keep ∷ [] ] V′
    residual : N.W ∣ [] ⊢ᴼ[ aligned-occ ]
      N.source-sealed ⊑ V′ ∶ q

open ProjectionCatchupResultᴼ public

⊢ᴼ-retarget : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {occ : CellOccupancy} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ p
  → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ q
⊢ᴼ-retarget {W = W} {γ = γ} {occ = occ} {M = M}
    {M′ = M′} {p = p} {q = q} d =
  subst (λ r → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ r)
    (PI.⊑-unique p q) d

------------------------------------------------------------------------
-- Generated-name input inversion
------------------------------------------------------------------------

-- The input to a successful generated `Y?` projection must be the matching
-- `Y!` tag.  The proof first peels the target cast and then reuses the
-- residual premise exposed by inversion.

base-source-to-target-sealed-emptyᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.base-source ⊑ N.target-sealed ∶ N.qXY
  → ⊥
base-source-to-target-sealed-emptyᴼ ()

raw-source-to-target-name-tagged-emptyᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    rawℕᴼ ⊑ N.target-name-tagged ∶ ℕ⊑★ᴼ
  → ⊥
raw-source-to-target-name-tagged-emptyᴼ (⊑castᴼ () _)

base-source-to-target-name-tagged-emptyᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.base-source ⊑ N.target-name-tagged ∶ ★⊑★
  → ⊥
base-source-to-target-name-tagged-emptyᴼ (cast⊑castᴼ () _)
base-source-to-target-name-tagged-emptyᴼ (⊑castᴼ () _)
base-source-to-target-name-tagged-emptyᴼ
    (cast⊑ᴼ (N.source-widen-base-to★ _ p≡ q≡) prem)
    rewrite p≡ | q≡ =
  raw-source-to-target-name-tagged-emptyᴼ (⊢ᴼ-retarget prem)

aligned-Y-tag-input-inversionᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
      N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
  → Value N.target-name-tagged
  → ProjectionCatchupResultᴼ N.target-name-tagged N.qXY
aligned-Y-tag-input-inversionᴼ
    (⊑castᴼ
      (N.target-widen-var-to★ {X = Fin.zero} {Y = Fin.zero}
        (N.shape-tag N.shape-idˣ) _ q≡)
      prem)
    _
    rewrite q≡ =
  projection-catchup-resultᴼ
    N.target-sealed
    N.target-sealed-value
    target-Y-projection-routeᴼ
    (⊢ᴼ-retarget prem)
aligned-Y-tag-input-inversionᴼ
    (conceal⊑ᴼ (seal-partner-okᴼ partner) _ prem _) vM′ =
  ⊥-elim (partner-empty partner (⊢ᴼ-retarget prem) vM′)
  where
    partner-empty : ∀ {Xᴿ?}
      → SealPartnerOKᴼ N.W aligned-occ Fin.zero
          N.base-source ★ Xᴿ? N.target-name-tagged
      → N.W ∣ [] ⊢ᴼ[ aligned-occ ]
          N.base-source ⊑ N.target-name-tagged ∶ ★⊑★
      → Value N.target-name-tagged
      → ⊥
    partner-empty (star-rep-targetᴼ no-target _) _ _ =
      aligned-no-target-empty no-target
    partner-empty (plain-targetᴼ ()) _ _
    partner-empty (name-protected-targetᴼ _) prem _ =
      base-source-to-target-name-tagged-emptyᴼ (⊢ᴼ-retarget prem)

generated-Y-projection-catchupᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
      N.source-sealed ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
  → Value N.source-sealed
  → Value N.target-name-tagged
  → ProjectionCatchupResultᴼ N.target-name-tagged N.qXY
generated-Y-projection-catchupᴼ
    (⊑castᴼ (N.target-narrow-★-to-var _ _ p≡) prem) _ vM′
    rewrite p≡ =
  aligned-Y-tag-input-inversionᴼ (⊢ᴼ-retarget prem) vM′

generated-Y-projection-siteᴼ :
  ProjectionCatchupResultᴼ N.target-name-tagged N.qXY
generated-Y-projection-siteᴼ =
  generated-Y-projection-catchupᴼ
    matching-projectionᴼ source-sealed-valueᴼ
    (N.target-sealed-value 《 inj 》)

------------------------------------------------------------------------
-- Ground-tag projection
------------------------------------------------------------------------

base-project-envᴼ : Env∼ 1
base-project-envᴼ _ = ★∼X

ℕ?ᴼ : base-project-envᴼ ⊢ ★ ∼ (‵ `ℕ)
ℕ?ᴼ = ？ (idᵍ (‵ `ℕ))

ℕ?-shapeᴼ : N.narrowing N.⊢ᶜ ℕ?ᴼ ⦂ N.tagˢ (‵ `ℕ)
ℕ?-shapeᴼ = N.shape-project N.shape-idι

ground-ℕ-projection-routeᴼ :
  N.base-target ⟨ ℕ?ᴼ ⟩ —↠[ keep ∷ [] ] rawℕᴼ
ground-ℕ-projection-routeᴼ =
  N.base-target ⟨ ℕ?ᴼ ⟩
  —→[ keep ]⟨ pure-step (tag-untag rawℕ-valueᴼ) ⟩
  rawℕᴼ ∎[]

ground-ℕ-projection-route-valueᴼ : ∀ {μ : Env∼ 1} {V}
    {ℕ∼★ : μ ⊢ (‵ `ℕ) ∼★}
  → (vV : Value V)
  → V ⟨ _! ⦃ Gᵍ = ‵ `ℕ ⦄ ⦃ G∼★ = ℕ∼★ ⦄
        (idᵍ (‵ `ℕ)) ⟩
      ⟨ ℕ?ᴼ ⟩
    —↠[ keep ∷ [] ] V
ground-ℕ-projection-route-valueᴼ vV =
  _
  —→[ keep ]⟨
    pure-step
      (tag-untag {μ = _} {ν = base-project-envᴼ}
        {G = ‵ `ℕ}
        ⦃ Gᵍ = ‵ `ℕ ⦄
        ⦃ G∼★ = _ ⦄
        ⦃ ★∼G = ★∼ι ⦄
        vV)
  ⟩
  _ ∎[]

record GroundProjectionCatchupResultᴼ (M′ : Term 1) : Set where
  constructor ground-projection-catchup-resultᴼ
  field
    V′ : Term 1
    value′ : Value V′
    steps : M′ ⟨ ℕ?ᴼ ⟩ —↠[ keep ∷ [] ] V′
    residual : N.W ∣ [] ⊢ᴼ[ aligned-occ ]
      rawℕᴼ ⊑ V′ ∶ ℕ⊑ℕᴼ

open GroundProjectionCatchupResultᴼ public

ground-ℕ-tag-input-inversionᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
      rawℕᴼ ⊑ N.base-target ∶ ℕ⊑★ᴼ
  → Value N.base-target
  → GroundProjectionCatchupResultᴼ N.base-target
ground-ℕ-tag-input-inversionᴼ
    (⊑castᴼ
      (N.target-widen-base-to★ (N.shape-tag N.shape-idι) p≡ q≡)
      prem)
    _
    rewrite p≡ | q≡ =
  ground-projection-catchup-resultᴼ
    rawℕᴼ
    rawℕ-valueᴼ
    ground-ℕ-projection-routeᴼ
    prem

ground-ℕ-projection-catchupᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
      rawℕᴼ ⊑ N.base-target ⟨ ℕ?ᴼ ⟩ ∶ ℕ⊑ℕᴼ
  → Value rawℕᴼ
  → Value N.base-target
  → GroundProjectionCatchupResultᴼ N.base-target
ground-ℕ-projection-catchupᴼ
    (⊑castᴼ (N.target-narrow-★-to-base _ p≡ q≡) prem) _ vM′
    rewrite p≡ | q≡ =
  ground-ℕ-tag-input-inversionᴼ prem vM′

ground-ℕ-projection-siteᴼ :
  GroundProjectionCatchupResultᴼ N.base-target
ground-ℕ-projection-siteᴼ =
  ground-ℕ-projection-catchupᴼ
    (⊑castᴼ (N.target-narrow-★-to-base ℕ?-shapeᴼ refl refl)
      aligned-target-one-sided-baseᴼ)
    ($ (κℕ 0))
    N.base-target-value

------------------------------------------------------------------------
-- Mini replacement for the old extra-cast-right fuel knot
------------------------------------------------------------------------

-- This is the consumer-facing shape: a target projection branch receives the
-- recursive CTI premise exposed by inversion and the concrete cancellation
-- route, instead of a separate catch-up embedding witness.

record ExtraCastRightProjectionInputᴼ
    (M M′ : Term 1)
    (p : (＇ Fin.zero) ⊑ᵂ⟨ N.W ⟩ ★)
    (q : (＇ Fin.zero) ⊑ᵂ⟨ N.W ⟩ (＇ Fin.zero)) : Set where
  constructor extra-cast-right-projection-inputᴼ
  field
    premise : N.W ∣ [] ⊢ᴼ[ aligned-occ ] M ⊑ M′ ∶ p
    source-value : Value M
    target-value : Value M′
    projection-result : ProjectionCatchupResultᴼ M′ q

open ExtraCastRightProjectionInputᴼ public

extra-cast-right-generated-Y-input-siteᴼ :
  ExtraCastRightProjectionInputᴼ
    N.source-sealed N.target-name-tagged N.X⊑★W N.qXY
extra-cast-right-generated-Y-input-siteᴼ =
  extra-cast-right-projection-inputᴼ
    matching-inputᴼ
    source-sealed-valueᴼ
    (N.target-sealed-value 《 inj 》)
    generated-Y-projection-siteᴼ

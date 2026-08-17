module ValueCatchupProvenanceGapScratch where

-- File Charter:
--   * Notes pre-flight for the M6 driver statement; not imported.
--   * Machine-checks that the design-scratch ValueCatchupRight² surface
--     (arbitrary CastColumn, NO per-cast CatchupCast provenance) is FALSE:
--     the QHUNT projection-mismatch package feeds it the singleton column
--     `Y?` and the target reduct blames instead of reaching a value.
--   * Consequence: the M6 driver must thread catch-up provenance through
--     the column; the fuel surface ValueCatchupRightAt inherits the same
--     requirement. The CatchupCast premise on ExtraCastRight² is doing
--     real work and must not be dropped one level up.
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/ValueCatchupProvenanceGapScratch.agda`.

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Types
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using (StoreChanges; _—↠[_]_)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

open import ProjectionMismatchStarRepScratch using
  (Y?; probe-q; input-relation; source-value; target-tagged-value;
   mismatch-no-value-reduct)

infixr 5 _▻ᶜ_

data CastColumn {Δ : TyCtx} : Ty Δ → Ty Δ → Set where
  []ᶜ : ∀ {A} → CastColumn A A
  _▻ᶜ_ : ∀ {A B C} {μ : Env∼ Δ}
    → μ ⊢ A ∼ B
    → CastColumn B C
    → CastColumn A C

applyColumn : ∀ {Δ} {A B : Ty Δ}
  → Term Δ
  → CastColumn A B
  → Term Δ
applyColumn M []ᶜ = M
applyColumn M (c ▻ᶜ κ) = applyColumn (M ⟨ c ⟩) κ

-- The design-scratch driver surface, verbatim from
-- notes/M6DriverDesignScratch.agda.
ValueCatchupRight² : Set
ValueCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (κ : CastColumn B B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (applyColumn M′ κ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))

value-catchup-unrestricted-contradiction :
  ValueCatchupRight² → ⊥
value-catchup-unrestricted-contradiction vcr
    with vcr input-relation source-value target-tagged-value
      (Y? ▻ᶜ []ᶜ) probe-q
value-catchup-unrestricted-contradiction vcr
    | Δᴿ′ , χs , Δ′ , W′ , ext , N′ , vN′ , M↠N′ , M⊑N′ =
  mismatch-no-value-reduct M↠N′ vN′

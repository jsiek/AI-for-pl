module proof.DGG.Catchup.StructuralTargetPeelSupportProof where

-- File Charter:
--   * Provides local value/step impossibility lemmas used by target-trace
--     peel proofs.
--   * Does not change the reduction relation; it only inverts existing
--     value and store-step constructors.

open import Data.Empty using (⊥)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty)
open import CastTerms using
  (Term; Value; ƛ_; Λ_; $; _《_》; _↑_; _↓_; _⟨_⟩; _⦂∀_[_])
import CastTerms as CT
open import Reduction using
  (StoreChange; _—→_; _—→[_]_; pure-step; β-id; ground; expand;
   tag-untag; tag-untag-bad; blame-bot-intro; id-reveal;
   id-conceal; conceal-reveal; blame-reveal; blame-conceal;
   β-inst; ξ-⟨⟩; ξ-reveal; ξ-conceal)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


no-value-type-app : ∀ {Δ} {M : Term Δ} {A : Ty (suc Δ)}
    {B : Ty Δ}
  → Value (M ⦂∀ A [ B ])
  → ⊥
no-value-type-app ()


no-value-blame : ∀ {Δ} → Value (CT.blame {Δ}) → ⊥
no-value-blame ()


no-value-apply-spine : ∀ {Δ} {M : Term Δ} {A B : Ty Δ}
    (spine : InstantiationSpine A B)
  → (Value M → ⊥)
  → Value (applyInstantiationSpine M spine)
  → ⊥
no-value-apply-spine []ⁱ noM vM = noM vM
no-value-apply-spine (type-transport-frame eq ▻ⁱ spine) noM v =
  no-value-apply-spine spine noM v
no-value-apply-spine (name-type-app-frame B X eqA eqC ▻ⁱ spine)
    noM v =
  no-value-apply-spine spine no-value-type-app v
no-value-apply-spine (cast-frame c ▻ⁱ spine) noM v =
  no-value-apply-spine spine noCast v
  where
  noCast : Value (_ ⟨ c ⟩) → ⊥
  noCast (vM 《 inert 》) = noM vM
no-value-apply-spine (reveal-frame c ▻ⁱ spine) noM v =
  no-value-apply-spine spine noReveal v
  where
  noReveal : Value (_ ↑ c) → ⊥
  noReveal (vM ↑ reveal-value) = noM vM
no-value-apply-spine (conceal-frame c ▻ⁱ spine) noM v =
  no-value-apply-spine spine noConceal v
  where
  noConceal : Value (_ ↓ c) → ⊥
  noConceal (vM ↓ conceal-value) = noM vM


value-no-pure-step : ∀ {Δ} {V N : Term Δ}
  → Value V
  → V —→ N
  → ⊥
value-no-pure-step (ƛ N) ()
value-no-pure-step (Λ vV) ()
value-no-pure-step ($ k) ()
value-no-pure-step (vV 《 CT.inj 》) (ground v _≢_) = _≢_ refl
value-no-pure-step (vV ↑ CT.fun) blame-reveal =
  no-value-blame vV
value-no-pure-step (vV ↑ CT.all) blame-reveal =
  no-value-blame vV
value-no-pure-step (vV ↓ CT.seal) blame-conceal =
  no-value-blame vV
value-no-pure-step (vV ↓ CT.fun) blame-conceal =
  no-value-blame vV
value-no-pure-step (vV ↓ CT.all) blame-conceal =
  no-value-blame vV


value-no-step : ∀ {Δ Δ′} {V : Term Δ} {N : Term Δ′}
    {χ : StoreChange Δ Δ′}
  → Value V
  → V —→[ χ ] N
  → ⊥
value-no-step vV (pure-step step) = value-no-pure-step vV step
value-no-step (vV 《 () 》) (β-inst v B≢★)
value-no-step (vV 《 CT.inj 》) (ξ-⟨⟩ step refl) =
  value-no-step vV step
value-no-step (vV 《 CT.fun 》) (ξ-⟨⟩ step refl) =
  value-no-step vV step
value-no-step (vV 《 CT.all 》) (ξ-⟨⟩ step refl) =
  value-no-step vV step
value-no-step (vV 《 CT.genᵥ A≢★ safe 》) (ξ-⟨⟩ step refl) =
  value-no-step vV step
value-no-step (vV ↑ CT.fun) (ξ-reveal step refl) =
  value-no-step vV step
value-no-step (vV ↑ CT.all) (ξ-reveal step refl) =
  value-no-step vV step
value-no-step (vV ↓ CT.seal) (ξ-conceal step refl) =
  value-no-step vV step
value-no-step (vV ↓ CT.fun) (ξ-conceal step refl) =
  value-no-step vV step
value-no-step (vV ↓ CT.all) (ξ-conceal step refl) =
  value-no-step vV step

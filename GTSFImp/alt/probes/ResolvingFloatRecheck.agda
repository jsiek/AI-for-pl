module alt.probes.ResolvingFloatRecheck where

-- File Charter:
--   * Rechecks ladder entry 7 against σ-indexed telescopes and anchor-directed
--     `rep?`.  Its historical contractum still refutes, but reveal-polarity
--     SCWRAP now fires first because the reveal-headed lambda is not a value.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; sym; trans)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst using (rep?-here)

------------------------------------------------------------------------
-- The retired resolving float, stated only as a probe relation
------------------------------------------------------------------------

infix 2 _⊢_—float-reveal→_

data _⊢_—float-reveal→_ : ∀ {Θ Δ σ}
    → TyEnv Θ Δ σ → Term Θ Δ → Term Θ Δ → Set where
  resolving-float-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term (suc Θ) (suc Δ)} {A : Ty (suc Δ)}
      {Y : TyVar (suc Δ)} {α : TyVar Θ} {C : Ty Δ} {c : Reveal}
    → rep? Ψ α ≡ just C
    → Value M
      ------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ↑[ Y ≔ α ] c —float-reveal→
        ν[ substᵗ (resolveSubᵗ Y C) A ]
          (M ↑[ Y ≔ suc α ] c)

------------------------------------------------------------------------
-- Original ladder-7 configuration under the current telescope
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

bad-Ψ : TyEnv 1 zero Vec.[]
bad-Ψ = ∅ ,:= ℕᵗ

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

outerEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
outerEnv = bad-Ψ ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩

bodyEnv : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
bodyEnv = outerEnv ,:= ＇ zero

own-anchor-fresh : zero {n = 1} ∉ᵛ (just (suc zero) Vec.∷ Vec.[])
own-anchor-fresh zero ()

bad-M : Term 2 1
bad-M =
  (ƛ ＇ zero ˙ $ (κℕ zero))
    ↑[ zero ≔ zero ] (seal ↦↑ id↑)

bad-M-not-value : ¬ Value bad-M
bad-M-not-value (reveal-fun Vᵛ nonλ) = nonλ refl

own-anchor-rep : rep? bodyEnv zero ≡ just (＇ zero)
own-anchor-rep = refl

bad-M-typed : bodyEnv ∣ [] ⊢ bad-M ⦂ ＇ zero ⇒ ℕᵗ
bad-M-typed =
  ⊢reveal {fresh = own-anchor-fresh} own-anchor-rep
    (⊢↑-⇒ ⊢seal (⊢id↑ (‵ `ℕ))) (⊢ƛ (⊢$ (κℕ zero)))

bad-redex : Term 1 zero
bad-redex =
  (ν[ ＇ zero ] bad-M)
    ↑[ zero ≔ zero ] (seal ↦↑ id↑)

bad-redex-typed : bad-Ψ ∣ [] ⊢ bad-redex ⦂ ℕᵗ ⇒ ℕᵗ
bad-redex-typed =
  ⊢reveal {fresh = empty-fresh} (rep?-here {Ψ = bad-Ψ})
    (⊢↑-⇒ ⊢seal (⊢id↑ (‵ `ℕ))) (⊢ν bad-M-typed)

bad-contractum : Term 1 zero
bad-contractum =
  ν[ ℕᵗ ] (bad-M ↑[ zero ≔ suc zero ] (seal ↦↑ id↑))

bad-float-shape-refuted :
  ¬ (bad-Ψ ⊢ bad-redex —float-reveal→ bad-contractum)
bad-float-shape-refuted
    (resolving-float-reveal rep-eq Mᵛ) = bad-M-not-value Mᵛ

bad-M-contractum : Term 2 1
bad-M-contractum =
  ƛ ＇ zero ˙
    ((($ (κℕ zero)) [ (` zero) ↓[ zero ≔ zero ] seal ])
      ↑[ zero ≔ zero ] id↑)

bad-M-scwrap : bodyEnv ⊢ bad-M —→ bad-M-contractum
bad-M-scwrap = SCWRAP refl

------------------------------------------------------------------------
-- The current lookup still leaves the contractum untypable
------------------------------------------------------------------------

seal-source : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↓[ X ⦂ R ] seal ⦂ A ↝ B
  → A ≡ R
seal-source ⊢seal = refl

seal-target : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↓[ X ⦂ R ] seal ⦂ A ↝ B
  → B ≡ ＇ X
seal-target ⊢seal = refl

var-base-impossible : _≡_ {A = Ty 2} (＇ suc zero) ℕᵗ → ⊥
var-base-impossible ()

contractum-own-anchor-rep : ∀
    {fresh : suc zero ∉ᵛ Vec.[]}
  → rep? ((bad-Ψ ,:= ℕᵗ) ,begin[ zero ≔ suc zero ]⟨ fresh ⟩) zero
      ≡ just ℕᵗ
contractum-own-anchor-rep = refl

bad-contractum-untypable :
  bad-Ψ ∣ [] ⊢ bad-contractum ⦂ ℕᵗ ⇒ ℕᵗ
  → ⊥
bad-contractum-untypable
    (⊢ν (⊢reveal {fresh = outer-fresh} outer-eq
      (⊢↑-⇒ outer-c⊢ outer-d⊢)
      (⊢reveal inner-eq (⊢↑-⇒ inner-c⊢ inner-d⊢)
        (⊢ƛ (⊢$ κ))))) =
  var-base-impossible
    (trans (sym (cong (renameᵗ suc) (seal-target outer-c⊢)))
      (trans (seal-source inner-c⊢)
        (cong (wkᵗ zero)
          (just-injective
            (trans (sym inner-eq)
              (contractum-own-anchor-rep {fresh = outer-fresh}))))))

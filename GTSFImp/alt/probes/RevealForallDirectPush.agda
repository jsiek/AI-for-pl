module alt.probes.RevealForallDirectPush where

-- File Charter:
--   * Refutes the direct `β-reveal-∀` push when its reused raw conversion
--     contains identity leaves at the instantiated universal variable.
--   * The redex is closed and typed, and takes the proposed step, but the
--     contractum is not typable at the preserved type.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx using (Z)
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst using (rep?-here)

------------------------------------------------------------------------
-- The proposed direct push, kept local because it refutes preservation
------------------------------------------------------------------------

infix 2 _⊢_—direct-reveal-∀→_

data _⊢_—direct-reveal-∀→_ : ∀ {Θ Δ σ}
    → TyEnv Θ Δ σ → Term Θ Δ → Term Θ Δ → Set where
  direct-β-reveal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {A : Ty Δ} {B : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Result V
      ------------------------------------------------------------
    → Ψ ⊢ (V ↑[ X ≔ α ] `∀↑ c) ⦂∀ B [ A ]
        —direct-reveal-∀→
        (V ⦂∀
          (src↑ (suc X) c (renameᵗ (extᵗ (punchIn X)) B))
          [ wkᵗ X A ]) ↑[ X ≔ α ] c

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

Ψ₀ : TyEnv 1 zero Vec.[]
Ψ₀ = ∅ ,:= ℕᵗ

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

Ψ₁ : TyEnv 1 1 (just zero Vec.∷ Vec.[])
Ψ₁ = Ψ₀ ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩

identityBody : ∀ {Δ} → Ty (suc Δ)
identityBody = ＇ zero ⇒ ＇ zero

argumentTy : Ty zero
argumentTy = (ℕᵗ ⇒ ℕᵗ)

inner : Term 1 1
inner = Λ (ƛ ＇ zero ˙ ` zero)

inner-value : Value inner
inner-value = Λ (ƛ ＇ zero ˙ ` zero)

inner-result : Result inner
inner-result = result-val inner-value

inner-typed : Ψ₁ ∣ [] ⊢ inner ⦂ `∀ identityBody
inner-typed = ⊢Λ (⊢ƛ (⊢` Z))

shape : Reveal
shape = id↓ ↦↑ id↑

boundary-typed :
  ⊢↑[ zero {n = zero} ⦂ wkᵗ zero (ℕᵗ {Δ = zero}) ] `∀↑ shape
    ⦂ `∀ (identityBody {Δ = 1})
    ↝ wkᵗ zero (`∀ (identityBody {Δ = zero}))
boundary-typed =
  ⊢↑-∀ (⊢↑-⇒ (⊢id↓ (＇ zero)) (⊢id↑ (＇ zero)))

redex : Term 1 zero
redex =
  (inner ↑[ zero ≔ zero ] `∀↑ shape)
    ⦂∀ identityBody [ argumentTy ]

contractum : Term 1 zero
contractum =
  (inner ⦂∀ identityBody [ wkᵗ zero argumentTy ])
    ↑[ zero ≔ zero ] shape

redex-typed : Ψ₀ ∣ [] ⊢ redex ⦂ argumentTy ⇒ argumentTy
redex-typed =
  ⊢⦂∀ (⊢reveal (rep?-here {Ψ = Ψ₀}) boundary-typed inner-typed)

direct-step : Ψ₀ ⊢ redex —direct-reveal-∀→ contractum
direct-step = direct-β-reveal-∀ inner-result

function-not-atom : ∀ {Δ} → Atom {Δ} (ℕᵗ ⇒ ℕᵗ) → ⊥
function-not-atom ()

contractum-untypable :
  Ψ₀ ∣ [] ⊢ contractum ⦂ argumentTy ⇒ argumentTy
  → ⊥
contractum-untypable
    (⊢reveal rep-eq (⊢↑-⇒ (⊢id↓ atom) right-typed)
      (⊢⦂∀ inner-typed′)) =
  function-not-atom atom

direct-push-counterexample :
  (Ψ₀ ∣ [] ⊢ redex ⦂ argumentTy ⇒ argumentTy)
  × ((Ψ₀ ⊢ redex —direct-reveal-∀→ contractum)
    × (Ψ₀ ∣ [] ⊢ contractum ⦂ argumentTy ⇒ argumentTy → ⊥))
direct-push-counterexample =
  redex-typed , direct-step , contractum-untypable

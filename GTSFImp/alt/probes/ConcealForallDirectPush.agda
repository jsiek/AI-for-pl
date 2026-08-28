module alt.probes.ConcealForallDirectPush where

-- File Charter:
--   * Refutes the expanded direct `β-conceal-∀` push when its type argument
--     is the live crossing itself.
--   * Identity expansion makes structural identity shapes, but it does not
--     mediate the resolved representation-to-crossing endpoint change.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

------------------------------------------------------------------------
-- The proposed direct push, local because it refutes preservation
------------------------------------------------------------------------

infix 2 _⊢_—direct-conceal-∀→_

data _⊢_—direct-conceal-∀→_ : ∀ {Θ Δ σ}
    → TyEnv Θ (suc Δ) σ
    → Term Θ (suc Δ) → Term Θ (suc Δ) → Set where
  direct-β-conceal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ Δ} {A : Ty (suc Δ)} {B : Ty (suc (suc Δ))}
      {C₀ : Ty Δ} {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → rep? (Ψ ,end[ X ]) α ≡ just C₀
    → Result V
      ------------------------------------------------------------
    → Ψ ⊢ (V ↓[ X ≔ α ] `∀↓ c) ⦂∀ B [ A ]
        —direct-conceal-∀→
        (V ⦂∀
          (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀))
            (src↓ (suc X) (⇑ᵗ (wkᵗ X C₀)) c B))
          [ substᵗ (resolveSubᵗ X C₀) A ])
            ↓[ X ≔ α ] expand↓ (B [ A ]ᵗ) c

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

base-Ψ : TyEnv 1 zero Vec.[]
base-Ψ = ∅ ,:= ℕᵗ

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

live-Ψ : TyEnv 1 1 (just zero Vec.∷ Vec.[])
live-Ψ = base-Ψ ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩

identityBody : ∀ {Δ} → Ty (suc Δ)
identityBody = ＇ zero ⇒ ＇ zero

inner : Term 1 zero
inner = Λ (ƛ ＇ zero ˙ ` zero)

inner-result : Result inner
inner-result =
  result-val (Λ (result-val (ƛ ＇ zero ˙ ` zero)))

inner-typed : live-Ψ ,end[ zero ] ∣ [] ⊢ inner ⦂ `∀ identityBody
inner-typed =
  ⊢Λ (body-result (result-val (ƛ ＇ zero ˙ ` zero)))
    (⊢ƛ (⊢` Z))

shape : Conceal
shape = id↑ ↦↓ id↓

boundary-typed :
  ⊢↓[ zero {n = zero} ⦂ wkᵗ zero (ℕᵗ {Δ = zero}) ] `∀↓ shape
    ⦂ wkᵗ zero (`∀ (identityBody {Δ = zero}))
    ↝ `∀ (identityBody {Δ = 1})
boundary-typed =
  ⊢↓-∀ (⊢↓-⇒ (⊢id↑ (＇ zero)) (⊢id↓ (＇ zero)))

redex : Term 1 1
redex =
  (inner ↓[ zero ≔ zero ] `∀↓ shape)
    ⦂∀ identityBody [ ＇ zero ]

contractum : Term 1 1
contractum =
  (inner ⦂∀ identityBody [ ℕᵗ ])
    ↓[ zero ≔ zero ] shape

redex-typed : live-Ψ ∣ [] ⊢ redex ⦂ ＇ zero ⇒ ＇ zero
redex-typed =
  ⊢⦂∀ (⊢conceal refl refl boundary-typed inner-typed)

direct-step : live-Ψ ⊢ redex —direct-conceal-∀→ contractum
direct-step = direct-β-conceal-∀ refl inner-result

contractum-untypable :
  live-Ψ ∣ [] ⊢ contractum ⦂ ＇ zero ⇒ ＇ zero
  → ⊥
contractum-untypable
    (⊢conceal tyVar-eq rep-eq (⊢↓-⇒ () right-typed)
      (⊢⦂∀ inner-typed′))

direct-push-counterexample :
  (live-Ψ ∣ [] ⊢ redex ⦂ ＇ zero ⇒ ＇ zero)
  × ((live-Ψ ⊢ redex —direct-conceal-∀→ contractum)
    × (live-Ψ ∣ [] ⊢ contractum ⦂ ＇ zero ⇒ ＇ zero → ⊥))
direct-push-counterexample =
  redex-typed , direct-step , contractum-untypable

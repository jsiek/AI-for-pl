module DynamicGradualGuarantee where

-- File Charter:
--   * States the dynamic gradual guarantee for closed extrinsic-inst
--   * `PolyUpDown` terms.
--   * Derives Part 1 from the fundamental theorem in `Parametricity.agda`.
--   * Keeps the catchup argument explicit, indexed by the observed number of
--   * right-hand reduction steps.

open import Data.List using (List; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
  using (∃; ∃-syntax; _×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Imprecision
open import UpDown using (Label; Up; Down)
open import Terms
  using
    ( Term
    ; blame
    ; substᵗᵐ
    ; $
    ; κℕ
    ; _·_
    ; _⦂∀_[_]
    ; _⊕[_]_
    ; _up_
    ; _down_
    )
open import TermPrecision
open import TermProperties using (substˣ-term)
open import ReductionFresh
  using
    ( Value
    ; ƛ_⇒_
    ; $
    ; Λ_
    ; _up_
    ; _down_
    ; _—→_
    ; β
    ; β-up-∀
    ; β-up-↦
    ; β-down-↦
    ; id-up
    ; id-down
    ; seal-unseal
    ; tag-untag-ok
    ; tag-untag-bad
    ; β-up-；
    ; β-down-；
    ; δ-⊕
    ; blame-·₁
    ; blame-·₂
    ; blame-·α
    ; blame-up
    ; blame-down
    ; blame-⊕₁
    ; blame-⊕₂
    ; tag
    ; seal
    ; _↦_
    ; ∀ᵖ
    ; ν_
    ; id-step
    ; β-Λ
    ; β-down-∀
    ; β-down-ν
    ; β-up-ν
    ; ξ-·₁
    ; ξ-·₂
    ; ξ-·α
    ; ξ-up
    ; ξ-down
    ; ξ-⊕₁
    ; ξ-⊕₂
    ; value-no-step
    ; _∣_—→_∣_
    ; _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    )
open import LogicalRelationDownward
open import Parametricity using (fundamental)
open import EvalPartialFresh
  using
    ( Step
    ; step?
    ; value?
    ; tyEq?
    ; app-redex?
    ; blame?
    ; nothing≢just
    ; target
    ; step?-complete
    ; step-deterministic
    )

closeˡ : Term → Term
closeˡ M = substᵗᵐ (leftᵗ ∅ρ) (substˣ-term (leftˣ ∅γ) M)

closeʳ : Term → Term
closeʳ M = substᵗᵐ (rightᵗ ∅ρ) (substˣ-term (rightˣ ∅γ) M)

steps :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  ℕ
steps (_ ∎) = zero
steps (_ —→⟨ _ ⟩ M↠N) = suc (steps M↠N)

Blame : Term → Set
Blame M = ∃[ ℓ ] (M ≡ blame ℓ)

Blames : Store → Term → Set
Blames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

Converges : Store → Term → Set
Converges Σ M =
  ∃[ Σ′ ] ∃[ W ] ((Σ ∣ M —↠ Σ′ ∣ W) × (Value W ⊎ Blame W))

Diverges : Store → Term → Set
Diverges Σ M = ¬ Converges Σ M

DivergeOrBlame : Store → Term → Set
DivergeOrBlame Σ M′ =
  (∀ Σ′ N′ →
     (Σ ∣ M′ —↠ Σ′ ∣ N′) →
     Blame N′ ⊎
     (∃[ Σ″ ] ∃[ N″ ] (Σ′ ∣ N′ —→ Σ″ ∣ N″)))

value-up-↦-inv :
  ∀ {V : Term} {p : Down} {q : Up} →
  Value (V up (p UpDown.↦ q)) →
  Value V
value-up-↦-inv (_up_ vV (_↦_ {p = p} {q = q})) = vV

value-down-↦-inv :
  ∀ {V : Term} {p : Up} {q : Down} →
  Value (V down (p UpDown.↦ q)) →
  Value V
value-down-↦-inv (_down_ vV (_↦_ {p = p} {q = q})) = vV

value-up-∀-inv :
  ∀ {V : Term} {p : Up} →
  Value (V up (UpDown.∀ᵖ p)) →
  Value V
value-up-∀-inv (_up_ vV (∀ᵖ {p = p})) = vV

value-down-∀-inv :
  ∀ {V : Term} {p : Down} →
  Value (V down (UpDown.∀ᵖ p)) →
  Value V
value-down-∀-inv (_down_ vV (∀ᵖ {p = p})) = vV

value-down-ν-inv :
  ∀ {V : Term} {p : Down} →
  Value (V down (UpDown.ν p)) →
  Value V
value-down-ν-inv (_down_ vV (ν_ {p = p})) = vV

value-down-seal-inv :
  ∀ {V : Term} {α : Seal} →
  Value (V down (UpDown.seal α)) →
  Value V
value-down-seal-inv (_down_ vV (seal {α = α})) = vV

value-—↠-refl :
  ∀ {Σ Σ′ : Store} {V N : Term} →
  Value V →
  Σ ∣ V —↠ Σ′ ∣ N →
  (Σ ≡ Σ′) × (V ≡ N)
value-—↠-refl vV (_ ∎) = refl , refl
value-—↠-refl vV (_ —→⟨ V→N ⟩ N↠W) =
  ⊥-elim (value-no-step vV V→N)

blame-no-step :
  ∀ {Σ Σ′ : Store} {ℓ : Label} {N : Term} →
  Σ ∣ blame ℓ —→ Σ′ ∣ N →
  ⊥
blame-no-step {Σ = Σ} red with step?-complete red
... | s , eq , tgt = nothing≢just eq

blame-—↠-refl :
  ∀ {Σ Σ′ : Store} {ℓ : Label} {N : Term} →
  Σ ∣ blame ℓ —↠ Σ′ ∣ N →
  (Σ ≡ Σ′) × (blame ℓ ≡ N)
blame-—↠-refl (_ ∎) = refl , refl
blame-—↠-refl (_ —→⟨ red ⟩ rest) = ⊥-elim (blame-no-step red)

value≢blame :
  ∀ {V : Term} {ℓ : Label} →
  Value V →
  V ≡ blame ℓ →
  ⊥
value≢blame (ƛ A ⇒ N) ()
value≢blame ($ κ) ()
value≢blame (Λ N) ()
value≢blame (_up_ vV tag) ()
value≢blame (_up_ vV (_↦_ {p = p} {q = q})) ()
value≢blame (_up_ vV (∀ᵖ {p = p})) ()
value≢blame (_down_ vV seal) ()
value≢blame (_down_ vV (_↦_ {p = p} {q = q})) ()
value≢blame (_down_ vV (∀ᵖ {p = p})) ()
value≢blame (_down_ vV (ν_ {p = p})) ()

value-vs-blame :
  ∀ {Σ Σᵥ Σᵦ : Store} {M V : Term} {ℓ : Label} →
  Value V →
  Σ ∣ M —↠ Σᵥ ∣ V →
  Σ ∣ M —↠ Σᵦ ∣ blame ℓ →
  ⊥
value-vs-blame vV (_ ∎) M↠blame with value-—↠-refl vV M↠blame
... | refl , V≡blame = value≢blame vV V≡blame
value-vs-blame vV (_ —→⟨ M→M₁ ⟩ M₁↠V) (_ ∎) =
  blame-no-step M→M₁
value-vs-blame vV (_ —→⟨ M→M₁ ⟩ M₁↠V)
  (_ —→⟨ M→M₂ ⟩ M₂↠blame)
  with step-deterministic M→M₁ M→M₂
... | refl , refl = value-vs-blame vV M₁↠V M₂↠blame

blame-or-step :
  ∀ {Σ Σ′ Σᵦ : Store} {M N : Term} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ M —↠ Σᵦ ∣ blame ℓ →
  Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σ′ ∣ N —→ Σ″ ∣ N″))
blame-or-step (_ ∎) (_ ∎) = inj₁ (_ , refl)
blame-or-step (_ ∎) (_ —→⟨ M→M₁ ⟩ M₁↠blame) =
  inj₂ (_ , _ , M→M₁)
blame-or-step (_ —→⟨ M→N ⟩ N↠N′) (_ ∎) =
  ⊥-elim (blame-no-step M→N)
blame-or-step (_ —→⟨ M→N₁ ⟩ N₁↠N′)
  (_ —→⟨ M→N₂ ⟩ N₂↠blame)
  with step-deterministic M→N₁ M→N₂
... | refl , refl = blame-or-step N₁↠N′ N₂↠blame

right-catchup :
  ∀ {Σˡ₀ Σʳ₀ Σʳ′ A B} {p : A ⊑ B} (k : ℕ) {η₀ : List SealRel}
    {Mˡ Mʳ V′} →
  Value V′ →
  (Mʳ↠V′ : Σʳ₀ ∣ Mʳ —↠ Σʳ′ ∣ V′) →
  ℰ (substᴿ-⊑ ∅ρ p) (steps Mʳ↠V′ + suc k) ≽
    (mkWorld Σˡ₀ Σʳ₀ η₀) Mˡ Mʳ →
  ∃[ Σˡ′ ] ∃[ V ]
    Value V ×
    (Σˡ₀ ∣ Mˡ —↠ Σˡ′ ∣ V) ×
    𝒱 (substᴿ-⊑ ∅ρ p) k ≽ (mkWorld Σˡ′ Σʳ′ η₀) V V′
right-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV′ (_ ∎) rel
  with observeℰ≽ {n = k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≽-stepʳ Σʳ₁ Mʳ₁ Mʳ→Mʳ₁ rel′ =
  ⊥-elim (value-no-step vV′ Mʳ→Mʳ₁)
... | obs≽-blameʳ Σʳᵇ ℓ Mʳ↠blame =
  ⊥-elim (value-vs-blame vV′ (_ ∎) Mʳ↠blame)
... | obs≽-value vMʳ Σˡ′ V Mˡ↠V Vrel =
  Σˡ′ , V ,
  𝒱-left-value {p = substᴿ-⊑ ∅ρ p} {n = k} {dir = ≽}
    {w = mkWorld Σˡ′ Σʳ₀ η₀} Vrel ,
  Mˡ↠V , Vrel
right-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV′ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠V′) rel
  with observeℰ≽ {n = steps Mʳ₁↠V′ + suc k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≽-stepʳ Σʳ₁ Mʳ₁′ Mʳ→Mʳ₁′ rel′
  with step-deterministic Mʳ→Mʳ₁ Mʳ→Mʳ₁′
right-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV′ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠V′) rel
  | obs≽-stepʳ Σʳ₁ Mʳ₁′ Mʳ→Mʳ₁′ rel′
  | refl , refl =
  right-catchup {A = A} {B = B} {p = p} k {η₀ = η₀} vV′ Mʳ₁↠V′ rel′
right-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV′ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠V′) rel
  | obs≽-blameʳ Σʳᵇ ℓ Mʳ↠blame =
  ⊥-elim
    (value-vs-blame vV′ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠V′)
      Mʳ↠blame)
right-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV′ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠V′) rel
  | obs≽-value vMʳ Σˡ′ V Mˡ↠V Vrel =
  ⊥-elim (value-no-step vMʳ Mʳ→Mʳ₁)

left-catchup-or-blame :
  ∀ {Σˡ₀ Σʳ₀ Σˡ′ A B} {p : A ⊑ B} (k : ℕ) {η₀ : List SealRel}
    {Mˡ Mʳ V} →
  Value V →
  (Mˡ↠V : Σˡ₀ ∣ Mˡ —↠ Σˡ′ ∣ V) →
  ℰ (substᴿ-⊑ ∅ρ p) (steps Mˡ↠V + suc k) ≼
    (mkWorld Σˡ₀ Σʳ₀ η₀) Mˡ Mʳ →
  (∃[ Σʳ′ ] ∃[ V′ ]
     Value V′ ×
     (Σʳ₀ ∣ Mʳ —↠ Σʳ′ ∣ V′) ×
     𝒱 (substᴿ-⊑ ∅ρ p) k ≼ (mkWorld Σˡ′ Σʳ′ η₀) V V′)
  ⊎ Blames Σʳ₀ Mʳ
left-catchup-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV (_ ∎) rel
  with observeℰ≼ {n = k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≼-stepˡ Σˡ₁ Mˡ₁ Mˡ→Mˡ₁ rel′ =
  ⊥-elim (value-no-step vV Mˡ→Mˡ₁)
... | obs≼-blameʳ Σʳᵇ ℓ Mʳ↠blame =
  inj₂ (Σʳᵇ , ℓ , Mʳ↠blame)
... | obs≼-value vMˡ Σʳ′ V′ Mʳ↠V′ Vrel =
  inj₁
    (Σʳ′ , V′ ,
     𝒱-right-value {p = substᴿ-⊑ ∅ρ p} {n = k} {dir = ≼}
       {w = mkWorld Σˡ₀ Σʳ′ η₀} Vrel ,
     Mʳ↠V′ , Vrel)
left-catchup-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠V) rel
  with observeℰ≼ {n = steps Mˡ₁↠V + suc k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≼-stepˡ Σˡ₁ Mˡ₁′ Mˡ→Mˡ₁′ rel′
  with step-deterministic Mˡ→Mˡ₁ Mˡ→Mˡ₁′
left-catchup-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠V) rel
  | obs≼-stepˡ Σˡ₁ Mˡ₁′ Mˡ→Mˡ₁′ rel′
  | refl , refl =
  left-catchup-or-blame {A = A} {B = B} {p = p} k {η₀ = η₀} vV Mˡ₁↠V rel′
left-catchup-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠V) rel
  | obs≼-blameʳ Σʳᵇ ℓ Mʳ↠blame =
  inj₂ (Σʳᵇ , ℓ , Mʳ↠blame)
left-catchup-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} vV (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠V) rel
  | obs≼-value vMˡ Σʳ′ V′ Mʳ↠V′ Vrel =
  ⊥-elim (value-no-step vMˡ Mˡ→Mˡ₁)

left-blame-catchup :
  ∀ {Σˡ₀ Σʳ₀ Σˡ′ A B} {p : A ⊑ B} (k : ℕ) {η₀ : List SealRel}
    {Mˡ Mʳ} {ℓ : Label} →
  (Mˡ↠blame : Σˡ₀ ∣ Mˡ —↠ Σˡ′ ∣ blame ℓ) →
  ℰ (substᴿ-⊑ ∅ρ p) (steps Mˡ↠blame + suc k) ≼
    (mkWorld Σˡ₀ Σʳ₀ η₀) Mˡ Mʳ →
  Blames Σʳ₀ Mʳ
left-blame-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} (_ ∎) rel
  with observeℰ≼ {n = k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≼-stepˡ Σˡ₁ Mˡ₁ Mˡ→Mˡ₁ rel′ =
  ⊥-elim (blame-no-step Mˡ→Mˡ₁)
... | obs≼-blameʳ Σʳᵇ ℓʳ Mʳ↠blame =
  Σʳᵇ , ℓʳ , Mʳ↠blame
... | obs≼-value vMˡ Σʳ′ V′ Mʳ↠V′ Vrel =
  ⊥-elim (value≢blame vMˡ refl)
left-blame-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠blame) rel
  with observeℰ≼ {n = steps Mˡ₁↠blame + suc k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≼-stepˡ Σˡ₁ Mˡ₁′ Mˡ→Mˡ₁′ rel′
  with step-deterministic Mˡ→Mˡ₁ Mˡ→Mˡ₁′
left-blame-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠blame) rel
  | obs≼-stepˡ Σˡ₁ Mˡ₁′ Mˡ→Mˡ₁′ rel′
  | refl , refl =
  left-blame-catchup {A = A} {B = B} {p = p} k {η₀ = η₀} Mˡ₁↠blame rel′
left-blame-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠blame) rel
  | obs≼-blameʳ Σʳᵇ ℓʳ Mʳ↠blame =
  Σʳᵇ , ℓʳ , Mʳ↠blame
left-blame-catchup {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠blame) rel
  | obs≼-value vMˡ Σʳ′ V′ Mʳ↠V′ Vrel =
  ⊥-elim (value-no-step vMˡ Mˡ→Mˡ₁)

right-diverge-or-blame :
  ∀ {Σˡ₀ Σʳ₀ Σʳ′ A B} {p : A ⊑ B} (k : ℕ) {η₀ : List SealRel}
    {Mˡ Mʳ Nʳ} →
  Diverges Σˡ₀ Mˡ →
  (Mʳ↠Nʳ : Σʳ₀ ∣ Mʳ —↠ Σʳ′ ∣ Nʳ) →
  ℰ (substᴿ-⊑ ∅ρ p) (steps Mʳ↠Nʳ + suc k) ≽
    (mkWorld Σˡ₀ Σʳ₀ η₀) Mˡ Mʳ →
  Blame Nʳ ⊎
  (∃[ Σʳ″ ] ∃[ Nʳ″ ] (Σʳ′ ∣ Nʳ —→ Σʳ″ ∣ Nʳ″))
right-diverge-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} div (_ ∎) rel
  with observeℰ≽ {n = k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≽-stepʳ Σʳ₁ Mʳ₁ Mʳ→Mʳ₁ rel′ =
  inj₂ (Σʳ₁ , Mʳ₁ , Mʳ→Mʳ₁)
... | obs≽-blameʳ Σʳᵇ ℓ Mʳ↠blame =
  blame-or-step (_ ∎) Mʳ↠blame
... | obs≽-value vMʳ Σˡ′ Vˡ Mˡ↠Vˡ Vrel =
  ⊥-elim
    (div
      (Σˡ′ , Vˡ ,
       (Mˡ↠Vˡ ,
        inj₁
          (𝒱-left-value {p = substᴿ-⊑ ∅ρ p} {n = k} {dir = ≽}
             {w = mkWorld Σˡ′ Σʳ₀ η₀} Vrel))))
right-diverge-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} div (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Nʳ) rel
  with observeℰ≽ {n = steps Mʳ₁↠Nʳ + suc k} {w = mkWorld Σˡ₀ Σʳ₀ η₀} rel
... | obs≽-stepʳ Σʳ₁ Mʳ₁′ Mʳ→Mʳ₁′ rel′
  with step-deterministic Mʳ→Mʳ₁ Mʳ→Mʳ₁′
right-diverge-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} div (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Nʳ) rel
  | obs≽-stepʳ Σʳ₁ Mʳ₁′ Mʳ→Mʳ₁′ rel′
  | refl , refl =
  right-diverge-or-blame {A = A} {B = B} {p = p} k {η₀ = η₀} div Mʳ₁↠Nʳ rel′
right-diverge-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} div (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Nʳ) rel
  | obs≽-blameʳ Σʳᵇ ℓ Mʳ↠blame =
  blame-or-step (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Nʳ) Mʳ↠blame
right-diverge-or-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p}
  k {η₀ = η₀} div (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Nʳ) rel
  | obs≽-value vMʳ Σˡ′ Vˡ Mˡ↠Vˡ Vrel =
  ⊥-elim (value-no-step vMʳ Mʳ→Mʳ₁)

dynamic-gradual-guarantee-part1 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     ∃[ Σˡ′ ] ∃[ V ]
       Value V ×
       (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
       𝒱 (substᴿ-⊑ ∅ρ p) 1 ≽ (mkWorld Σˡ′ Σʳ′ []) V V′)
dynamic-gradual-guarantee-part1
  {Σ = Σ} {M = M} {M′ = M′} {A = A} {B = B} {p = p}
  rel {Σʳ′} {V′} vV′ M′↠V′ =
  right-catchup {Σˡ₀ = Σ} {Σʳ₀ = Σ} {A = A} {B = B} {p = p}
    1 {Mˡ = closeˡ M} {Mʳ = closeʳ M′} vV′ M′↠V′
    (fundamental {A = A} {B = B} {p = p} ≽ rel
      (steps M′↠V′ + suc (suc zero))
      (mkWorld Σ Σ [])
      ∅ρ
      ∅γ
      (lift tt))

dynamic-gradual-guarantee-part2 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (Diverges Σ (closeʳ M′) → Diverges Σ (closeˡ M))
dynamic-gradual-guarantee-part2
  {Σ = Σ} {M = M} {M′ = M′} {A = A} {B = B} {p = p}
  rel divʳ (Σˡ′ , W , M↠W , convW) with convW
... | inj₁ vW with left-catchup-or-blame
  {Σˡ₀ = Σ} {Σʳ₀ = Σ} {A = A} {B = B} {p = p}
  1 {Mˡ = closeˡ M} {Mʳ = closeʳ M′} vW M↠W
  (fundamental {A = A} {B = B} {p = p} ≼ rel
    (steps M↠W + suc (suc zero))
    (mkWorld Σ Σ [])
    ∅ρ
    ∅γ
    (lift tt))
... | inj₁ (Σʳ′ , V′ , vV′ , M′↠V′ , Vrel) =
  divʳ (Σʳ′ , V′ , (M′↠V′ , inj₁ vV′))
... | inj₂ (Σʳᵇ , ℓʳ , M′↠blame) =
  divʳ (Σʳᵇ , blame ℓʳ , (M′↠blame , inj₂ (ℓʳ , refl)))
dynamic-gradual-guarantee-part2
  {Σ = Σ} {M = M} {M′ = M′} {A = A} {B = B} {p = p}
  rel divʳ (Σˡ′ , W , M↠W , convW) | inj₂ (ℓˡ , refl)
  with left-blame-catchup
  {Σˡ₀ = Σ} {Σʳ₀ = Σ} {A = A} {B = B} {p = p}
  1 {Mˡ = closeˡ M} {Mʳ = closeʳ M′} {ℓ = ℓˡ} M↠W
  (fundamental {A = A} {B = B} {p = p} ≼ rel
    (steps M↠W + suc (suc zero))
    (mkWorld Σ Σ [])
    ∅ρ
    ∅γ
    (lift tt))
... | Σʳᵇ , ℓʳ , M′↠blame =
  divʳ (Σʳᵇ , blame ℓʳ , (M′↠blame , inj₂ (ℓʳ , refl)))

dynamic-gradual-guarantee-part3 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     (∃[ Σʳ′ ] ∃[ V′ ]
        Value V′ ×
        (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
        𝒱 (substᴿ-⊑ ∅ρ p) 1 ≼ (mkWorld Σˡ′ Σʳ′ []) V V′)
     ⊎ Blames Σ (closeʳ M′))
dynamic-gradual-guarantee-part3
  {Σ = Σ} {M = M} {M′ = M′} {A = A} {B = B} {p = p}
  rel {Σˡ′} {V} vV M↠V =
  left-catchup-or-blame {Σˡ₀ = Σ} {Σʳ₀ = Σ} {A = A} {B = B} {p = p}
    1 {Mˡ = closeˡ M} {Mʳ = closeʳ M′} vV M↠V
    (fundamental {A = A} {B = B} {p = p} ≼ rel
      (steps M↠V + suc (suc zero))
      (mkWorld Σ Σ [])
      ∅ρ
      ∅γ
      (lift tt))

dynamic-gradual-guarantee-part4 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (Diverges Σ (closeˡ M) → DivergeOrBlame Σ (closeʳ M′))
dynamic-gradual-guarantee-part4
  {Σ = Σ} {M = M} {M′ = M′} {A = A} {B = B} {p = p}
  rel div Σʳ′ N′ M′↠N′ =
  right-diverge-or-blame {Σˡ₀ = Σ} {Σʳ₀ = Σ} {A = A} {B = B} {p = p}
    0 {Mˡ = closeˡ M} {Mʳ = closeʳ M′} div M′↠N′
    (fundamental {A = A} {B = B} {p = p} ≽ rel
      (steps M′↠N′ + suc zero)
      (mkWorld Σ Σ [])
      ∅ρ
      ∅γ
      (lift tt))

dynamic-gradual-guarantee :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  -- Part 1
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     ∃[ Σˡ′ ] ∃[ V ]
       Value V ×
       (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
       𝒱 (substᴿ-⊑ ∅ρ p) 1 ≽ (mkWorld Σˡ′ Σʳ′ []) V V′)
  ×
  -- Part 2
  (Diverges Σ (closeʳ M′) → Diverges Σ (closeˡ M))
  ×
  -- Part 3
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     (∃[ Σʳ′ ] ∃[ V′ ]
        Value V′ ×
        (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
        𝒱 (substᴿ-⊑ ∅ρ p) 1 ≼ (mkWorld Σˡ′ Σʳ′ []) V V′)
     ⊎ Blames Σ (closeʳ M′))
  ×
  -- Part 4
  (Diverges Σ (closeˡ M) → DivergeOrBlame Σ (closeʳ M′))
dynamic-gradual-guarantee rel =
  dynamic-gradual-guarantee-part1 rel ,
  (dynamic-gradual-guarantee-part2 rel ,
   (dynamic-gradual-guarantee-part3 rel , dynamic-gradual-guarantee-part4 rel))

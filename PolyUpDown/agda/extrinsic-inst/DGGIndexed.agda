module DGGIndexed where

-- File Charter:
--   * States the dynamic gradual guarantee for closed extrinsic-inst
--     `PolyUpDown` terms using the indexed logical relation.
--   * Postulates the closed fundamental theorem while
--     `ParametricityIndexed.agda` is still under development.
--   * Uses the corrected imprecision orientation: the public theorem takes
--     `M ⊑ M′`, so `M` is less imprecise/more precise and `M′` is
--     more imprecise/less precise.

open import Data.List using (List; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; <′-base)
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
open import Store using (StoreWf; ⊆ˢ-refl)
open import ImprecisionIndexed
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
open import TermImprecisionIndexed
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
    ; multi-trans
    )
open import LogicalRelationIndexed
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
closeˡ M = substᵗᵐ (leftᵗ ∅ρ) M

closeʳ : Term → Term
closeʳ M = substᵗᵐ (rightᵗ ∅ρ) M

closed-RelWf :
  ∀ {Ψ Σ} {wfΣ : StoreWf 0 Ψ Σ} →
  RelWf (mkWorld Ψ Ψ Σ Σ wfΣ wfΣ []) ∅ρ
closed-RelWf .RelWf.νenv⊆η = η-done
closed-RelWf .RelWf.νenvˡ-wf = lift tt
closed-RelWf .RelWf.νenvʳ-wf = lift tt
closed-RelWf .RelWf.leftᵗ-wf ()
closed-RelWf .RelWf.rightᵗ-wf ()

postulate
  fundamental :
    ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    (dir : Dir) →
    (wfΣ : StoreWf 0 Ψ Σ) →
    ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ M′ ⦂ p →
    (n : ℕ) →
    ℰ ∅ρ p n dir (mkWorld Ψ Ψ Σ Σ wfΣ wfΣ []) (closeˡ M) (closeʳ M′)

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
  ∀ {V : Term} {α : Seal} {p : Down} →
  Value (V down (UpDown.seal p α)) →
  Value V
value-down-seal-inv (_down_ vV (seal {p = p} {α = α})) = vV

value-—↠-refl :
  ∀ {Σ Σ′ : Store} {V N : Term} →
  Value V →
  Σ ∣ V —↠ Σ′ ∣ N →
  (Σ ≡ Σ′) × (V ≡ N)
value-—↠-refl vV (_ ∎) = refl , refl
value-—↠-refl vV (_ —→⟨ V→N ⟩ N↠W) =
  ⊥-elim (value-no-step vV V→N)

↠-refl :
  ∀ {Σ : Store} {M : Term} →
  Σ ∣ M —↠ Σ ∣ M
↠-refl = _ ∎

transport-𝒱 :
  ∀ {A B} {p : [] ⊢ A ⊑ᵢ B} {k : ℕ} {dir : Dir}
    {w w′ : World} {V V′ W W′ : Term} →
  w ≡ w′ →
  V ≡ W →
  V′ ≡ W′ →
  𝒱 ∅ρ p k dir w V V′ →
  𝒱 ∅ρ p k dir w′ W W′
transport-𝒱 refl refl refl Vrel = Vrel

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

right-value-implies-left-value-or-blame :
  ∀ {Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ Σʳ′ Mˡ Mʳ Vʳ A B}
    {p : [] ⊢ A ⊑ᵢ B} {η₀ : List SealRel}
    {wfΣˡ₀ : StoreWf 0 Ψˡ₀ Σˡ₀}
    {wfΣʳ₀ : StoreWf 0 Ψʳ₀ Σʳ₀} →
  Value Vʳ →
  (Mʳ↠Vʳ : Σʳ₀ ∣ Mʳ —↠ Σʳ′ ∣ Vʳ) →
  ℰ ∅ρ p (steps Mʳ↠Vʳ + suc (suc zero)) ≽
    (mkWorld Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ wfΣˡ₀ wfΣʳ₀ η₀) Mˡ Mʳ →
  (Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
    Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Vˡ ∈ Term ]
    ((Value Vˡ × (Σˡ₀ ∣ Mˡ —↠ Σˡ′ ∣ Vˡ)) ×
     𝒱 ∅ρ p 1 ≽
       (mkWorld Ψˡ′ Ψʳ′ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ η₀) Vˡ Vʳ))
  ⊎ Blames Σˡ₀ Mˡ
right-value-implies-left-value-or-blame
    {Ψʳ₀ = Ψʳ₀} {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀}
    {Σʳ′ = Σʳ₀} {Vʳ = Vʳ} {p = p} {η₀ = η₀}
    {wfΣʳ₀ = wfΣʳ₀} vVʳ (Vʳ ∎) rel
    with proj₂ rel
... | inj₁ (Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁ , Mʳ→Mʳ₁ ,
            Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁ , Mˡ↠Mˡ₁ , rel′) =
  ⊥-elim (value-no-step vVʳ Mʳ→Mʳ₁)
... | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓ , Mˡ↠blame)) =
  inj₂ (Σˡᵇ , ℓ , Mˡ↠blame)
... | inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ , Mˡ↠Vˡ , Vrel)) =
  inj₁
    (Ψʳ₀ , wfΣʳ₀ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ ,
     ((proj₁ (proj₁ Vrel) , Mˡ↠Vˡ) , Vrel))
right-value-implies-left-value-or-blame
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    vVʳ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Vʳ) rel
    with proj₂ rel
... | inj₁ (Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁′ , Mʳ→Mʳ₁′ ,
            Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁ , Mˡ↠Mˡ₁ , rel′)
    with step-deterministic Mʳ→Mʳ₁ Mʳ→Mʳ₁′
... | refl , refl
    with right-value-implies-left-value-or-blame vVʳ Mʳ₁↠Vʳ rel′
... | inj₁ (Ψʳ′ , wfΣʳ′ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ ,
            ((vVˡ , Mˡ₁↠Vˡ) , Vrel)) =
  inj₁
    (Ψʳ′ , wfΣʳ′ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ ,
     ((vVˡ , multi-trans Mˡ↠Mˡ₁ Mˡ₁↠Vˡ) , Vrel))
... | inj₂ (Σˡᵇ , ℓ , Mˡ₁↠blame) =
  inj₂ (Σˡᵇ , ℓ , multi-trans Mˡ↠Mˡ₁ Mˡ₁↠blame)
right-value-implies-left-value-or-blame
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    vVʳ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Vʳ) rel
    | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓ , Mˡ↠blame)) =
  inj₂ (Σˡᵇ , ℓ , Mˡ↠blame)
right-value-implies-left-value-or-blame
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    vVʳ (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠Vʳ) rel
    | inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ , Mˡ↠Vˡ , Vrel)) =
  ⊥-elim (value-no-step vMʳ Mʳ→Mʳ₁)

left-value-implies-right-value :
  ∀ {Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ Σˡ′ Mˡ Mʳ Vˡ A B}
    {p : [] ⊢ A ⊑ᵢ B} {η₀ : List SealRel}
    {wfΣˡ₀ : StoreWf 0 Ψˡ₀ Σˡ₀}
    {wfΣʳ₀ : StoreWf 0 Ψʳ₀ Σʳ₀} →
  Value Vˡ →
  (Mˡ↠Vˡ : Σˡ₀ ∣ Mˡ —↠ Σˡ′ ∣ Vˡ) →
  ℰ ∅ρ p (steps Mˡ↠Vˡ + suc (suc zero)) ≼
    (mkWorld Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ wfΣˡ₀ wfΣʳ₀ η₀) Mˡ Mʳ →
  Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
    Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ] Σ[ Vʳ ∈ Term ]
    (Value Vʳ × (Σʳ₀ ∣ Mʳ —↠ Σʳ′ ∣ Vʳ) ×
     𝒱 ∅ρ p 1 ≼
       (mkWorld Ψˡ′ Ψʳ′ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ η₀) Vˡ Vʳ)
left-value-implies-right-value
    {Ψˡ₀ = Ψˡ₀} {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀}
    {Σˡ′ = Σˡ₀} {Vˡ = Vˡ} {p = p} {η₀ = η₀}
    {wfΣˡ₀ = wfΣˡ₀} vVˡ (Vˡ ∎) rel
    with proj₂ rel
... | inj₁ (Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁ , Mˡ→Mˡ₁ ,
            Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁ , Mʳ↠Mʳ₁ , rel′) =
  ⊥-elim (value-no-step vVˡ Mˡ→Mˡ₁)
... | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓ , Mˡ↠blame)) =
  ⊥-elim (value-vs-blame vVˡ (↠-refl {Σ = Σˡ₀} {M = Vˡ}) Mˡ↠blame)
... | inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ , Mʳ↠Vʳ , Vrel)) =
  Ψˡ₀ , wfΣˡ₀ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ ,
  (proj₁ (proj₂ (proj₁ Vrel)) , Mʳ↠Vʳ , Vrel)
left-value-implies-right-value
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    vVˡ (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Vˡ) rel
    with proj₂ rel
... | inj₁ (Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁′ , Mˡ→Mˡ₁′ ,
            Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁ , Mʳ↠Mʳ₁ , rel′)
    with step-deterministic Mˡ→Mˡ₁ Mˡ→Mˡ₁′
... | refl , refl
    with left-value-implies-right-value vVˡ Mˡ₁↠Vˡ rel′
... | Ψˡ′ , wfΣˡ′ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ ,
      (vVʳ , Mʳ₁↠Vʳ , Vrel) =
  Ψˡ′ , wfΣˡ′ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ ,
  (vVʳ , multi-trans Mʳ↠Mʳ₁ Mʳ₁↠Vʳ , Vrel)
left-value-implies-right-value
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    vVˡ (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Vˡ) rel
    | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓ , Mˡ↠blame)) =
  ⊥-elim
    (value-vs-blame vVˡ (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Vˡ) Mˡ↠blame)
left-value-implies-right-value
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    vVˡ (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Vˡ) rel
    | inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ , Mʳ↠Vʳ , Vrel)) =
  ⊥-elim (value-no-step vMˡ Mˡ→Mˡ₁)

right-diverges-implies-left-blame-or-step :
  ∀ {Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ Σˡ′ Mˡ Mʳ Nˡ A B}
    {p : [] ⊢ A ⊑ᵢ B} {η₀ : List SealRel}
    {wfΣˡ₀ : StoreWf 0 Ψˡ₀ Σˡ₀}
    {wfΣʳ₀ : StoreWf 0 Ψʳ₀ Σʳ₀} →
  Diverges Σʳ₀ Mʳ →
  (Mˡ↠Nˡ : Σˡ₀ ∣ Mˡ —↠ Σˡ′ ∣ Nˡ) →
  ℰ ∅ρ p (steps Mˡ↠Nˡ + suc zero) ≼
    (mkWorld Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ wfΣˡ₀ wfΣʳ₀ η₀) Mˡ Mʳ →
  Blame Nˡ ⊎
  (∃[ Σˡ″ ] ∃[ Nˡ″ ] (Σˡ′ ∣ Nˡ —→ Σˡ″ ∣ Nˡ″))
right-diverges-implies-left-blame-or-step {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀}
    div (Nˡ ∎) rel
    with proj₂ rel
... | inj₁ (Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁ , Mˡ→Mˡ₁ ,
            Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁ , Mʳ↠Mʳ₁ , rel′) =
  inj₂ (Σˡ₁ , Mˡ₁ , Mˡ→Mˡ₁)
... | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓ , Mˡ↠blame)) =
  blame-or-step (↠-refl {Σ = Σˡ₀} {M = Nˡ}) Mˡ↠blame
... | inj₂ (inj₂
      (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ , Mʳ↠Vʳ , lift (_ , vVʳ , _))) =
  ⊥-elim (div (Σʳ′ , Vʳ , (Mʳ↠Vʳ , inj₁ vVʳ)))
right-diverges-implies-left-blame-or-step
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    div (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Nˡ) rel
    with proj₂ rel
... | inj₁ (Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁′ , Mˡ→Mˡ₁′ ,
            Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁ , Mʳ↠Mʳ₁ , rel′)
    with step-deterministic Mˡ→Mˡ₁ Mˡ→Mˡ₁′
... | refl , refl =
  right-diverges-implies-left-blame-or-step
    (λ { (Σʳ′ , Vʳ , Mʳ₁↠Vʳ , conv) →
      div (Σʳ′ , Vʳ , multi-trans Mʳ↠Mʳ₁ Mʳ₁↠Vʳ , conv) })
    Mˡ₁↠Nˡ
    rel′
right-diverges-implies-left-blame-or-step
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    div (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Nˡ) rel
    | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓ , Mˡ↠blame)) =
  blame-or-step (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Nˡ) Mˡ↠blame
right-diverges-implies-left-blame-or-step
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    div (_ —→⟨ Mˡ→Mˡ₁ ⟩ Mˡ₁↠Nˡ) rel
    | inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Vʳ , Mʳ↠Vʳ , Vrel)) =
  ⊥-elim (value-no-step vMˡ Mˡ→Mˡ₁)

right-blame-implies-left-blame :
  ∀ {Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ Σʳ′ Mˡ Mʳ A B}
    {p : [] ⊢ A ⊑ᵢ B} {η₀ : List SealRel}
    {wfΣˡ₀ : StoreWf 0 Ψˡ₀ Σˡ₀}
    {wfΣʳ₀ : StoreWf 0 Ψʳ₀ Σʳ₀} {ℓ : Label} →
  (Mʳ↠blame : Σʳ₀ ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ) →
  ℰ ∅ρ p (steps Mʳ↠blame + suc zero) ≽
    (mkWorld Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ wfΣˡ₀ wfΣʳ₀ η₀) Mˡ Mʳ →
  Blames Σˡ₀ Mˡ
right-blame-implies-left-blame {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀}
    (blame ℓ ∎) rel
    with proj₂ rel
... | inj₁ (Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁ , Mʳ→Mʳ₁ ,
            Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁ , Mˡ↠Mˡ₁ , rel′) =
  ⊥-elim (blame-no-step Mʳ→Mʳ₁)
... | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓˡ , Mˡ↠blame)) =
  Σˡᵇ , ℓˡ , Mˡ↠blame
... | inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ , Mˡ↠Vˡ , Vrel)) =
  ⊥-elim (value≢blame vMʳ refl)
right-blame-implies-left-blame
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠blame) rel
    with proj₂ rel
... | inj₁ (Σʳ₁ , Ψʳ₁ , wfΣʳ₁ , Mʳ₁′ , Mʳ→Mʳ₁′ ,
            Σˡ₁ , Ψˡ₁ , wfΣˡ₁ , Mˡ₁ , Mˡ↠Mˡ₁ , rel′)
    with step-deterministic Mʳ→Mʳ₁ Mʳ→Mʳ₁′
... | refl , refl
    with right-blame-implies-left-blame Mʳ₁↠blame rel′
... | Σˡᵇ , ℓˡ , Mˡ₁↠blame =
  Σˡᵇ , ℓˡ , multi-trans Mˡ↠Mˡ₁ Mˡ₁↠blame
right-blame-implies-left-blame
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠blame) rel
    | inj₂ (inj₁ (Σˡᵇ , Ψˡᵇ , wfΣˡᵇ , ℓˡ , Mˡ↠blame)) =
  Σˡᵇ , ℓˡ , Mˡ↠blame
right-blame-implies-left-blame
    {Σˡ₀ = Σˡ₀} {Σʳ₀ = Σʳ₀} {A = A} {B = B} {p = p} {η₀ = η₀}
    (_ —→⟨ Mʳ→Mʳ₁ ⟩ Mʳ₁↠blame) rel
    | inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ , Mˡ↠Vˡ , Vrel)) =
  ⊥-elim (value-no-step vMʳ Mʳ→Mʳ₁)

right-converges-implies-left-converges :
  ∀ {Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ Mˡ Mʳ A B}
    {p : [] ⊢ A ⊑ᵢ B} {η₀ : List SealRel}
    {wfΣˡ₀ : StoreWf 0 Ψˡ₀ Σˡ₀}
    {wfΣʳ₀ : StoreWf 0 Ψʳ₀ Σʳ₀} →
  Converges Σʳ₀ Mʳ →
  (∀ n → ℰ ∅ρ p n ≽
    (mkWorld Ψˡ₀ Ψʳ₀ Σˡ₀ Σʳ₀ wfΣˡ₀ wfΣʳ₀ η₀) Mˡ Mʳ) →
  Converges Σˡ₀ Mˡ
right-converges-implies-left-converges
    {Σˡ₀ = Σˡ₀} (Σʳ′ , Vʳ , Mʳ↠Vʳ , inj₁ vVʳ) rel =
  result (right-value-implies-left-value-or-blame vVʳ Mʳ↠Vʳ
    (rel (steps Mʳ↠Vʳ + suc (suc zero))))
  where
  result :
    _ →
    Converges Σˡ₀ _
  result
      (inj₁
        (Ψʳ′ , wfΣʳ′ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Vˡ ,
         ((vVˡ , Mˡ↠Vˡ) , Vrel))) =
    Σˡ′ , Vˡ , Mˡ↠Vˡ , inj₁ vVˡ
  result (inj₂ (Σˡᵇ , ℓ , Mˡ↠blame)) =
    Σˡᵇ , blame ℓ , Mˡ↠blame , inj₂ (ℓ , refl)
right-converges-implies-left-converges
    {Σˡ₀ = Σˡ₀} (Σʳ′ , .(blame ℓ) , Mʳ↠blame , inj₂ (ℓ , refl)) rel
    with right-blame-implies-left-blame Mʳ↠blame
      (rel (steps Mʳ↠blame + suc zero))
... | Σˡᵇ , ℓˡ , Mˡ↠blame =
  Σˡᵇ , blame ℓˡ , Mˡ↠blame , inj₂ (ℓˡ , refl)

dynamic-gradual-guarantee-part1 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σˡ′ Vˡ} →
     Value Vˡ →
     (M↠Vˡ : Σ ∣ closeˡ M —↠ Σˡ′ ∣ Vˡ) →
     Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
       Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ]
       Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ] Σ[ Vʳ ∈ Term ]
       (Value Vʳ × (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ Vʳ) ×
        𝒱 ∅ρ p 1 ≼
          (mkWorld Ψˡ′ Ψʳ′ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ []) Vˡ Vʳ))
dynamic-gradual-guarantee-part1 wfΣ rel vVˡ M↠Vˡ =
  left-value-implies-right-value vVˡ M↠Vˡ
    (fundamental ≼ wfΣ rel (steps M↠Vˡ + suc (suc zero)))

dynamic-gradual-guarantee-part2 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ M′ ⦂ p →
  (Diverges Σ (closeˡ M) → Diverges Σ (closeʳ M′))
dynamic-gradual-guarantee-part2 wfΣ rel divˡ convʳ =
  divˡ (right-converges-implies-left-converges convʳ
    (λ n → fundamental ≽ wfΣ rel n))

dynamic-gradual-guarantee-part3 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σʳ′ Vʳ} →
     Value Vʳ →
     (M′↠Vʳ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ Vʳ) →
     (Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
       Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
       Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Vˡ ∈ Term ]
       ((Value Vˡ × (Σ ∣ closeˡ M —↠ Σˡ′ ∣ Vˡ)) ×
        𝒱 ∅ρ p 1 ≽
          (mkWorld Ψˡ′ Ψʳ′ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ []) Vˡ Vʳ))
     ⊎ Blames Σ (closeˡ M))
dynamic-gradual-guarantee-part3 wfΣ rel vVʳ M′↠Vʳ =
  right-value-implies-left-value-or-blame vVʳ M′↠Vʳ
    (fundamental ≽ wfΣ rel (steps M′↠Vʳ + suc (suc zero)))

dynamic-gradual-guarantee-part4 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ M′ ⦂ p →
  (Diverges Σ (closeʳ M′) → DivergeOrBlame Σ (closeˡ M))
dynamic-gradual-guarantee-part4 wfΣ rel divʳ Σˡ′ Nˡ M↠Nˡ =
  right-diverges-implies-left-blame-or-step divʳ M↠Nˡ
    (fundamental ≼ wfΣ rel (steps M↠Nˡ + suc zero))

dynamic-gradual-guarantee :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σˡ′ Vˡ} →
     Value Vˡ →
     (M↠Vˡ : Σ ∣ closeˡ M —↠ Σˡ′ ∣ Vˡ) →
     Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
       Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ]
       Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ] Σ[ Vʳ ∈ Term ]
       (Value Vʳ × (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ Vʳ) ×
        𝒱 ∅ρ p 1 ≼
          (mkWorld Ψˡ′ Ψʳ′ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ []) Vˡ Vʳ))
  ×
  (Diverges Σ (closeˡ M) → Diverges Σ (closeʳ M′))
  ×
  (∀ {Σʳ′ Vʳ} →
     Value Vʳ →
     (M′↠Vʳ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ Vʳ) →
     (Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
       Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
       Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Vˡ ∈ Term ]
       ((Value Vˡ × (Σ ∣ closeˡ M —↠ Σˡ′ ∣ Vˡ)) ×
        𝒱 ∅ρ p 1 ≽
          (mkWorld Ψˡ′ Ψʳ′ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ []) Vˡ Vʳ))
     ⊎ Blames Σ (closeˡ M))
  ×
  (Diverges Σ (closeʳ M′) → DivergeOrBlame Σ (closeˡ M))
dynamic-gradual-guarantee wfΣ rel =
  dynamic-gradual-guarantee-part1 wfΣ rel ,
  (dynamic-gradual-guarantee-part2 wfΣ rel ,
   (dynamic-gradual-guarantee-part3 wfΣ rel ,
    dynamic-gradual-guarantee-part4 wfΣ rel))

module Progress where

-- File Charter:
--   * Progress witnesses and canonical-form lemmas for closed PolyUpDown terms.
--   * Theorems that analyze closed values by result type and connect them to
--     one-step reduction.
-- Note to self:
--   * Keep value definitions and reduction rules in `Reduction.agda`.
--   * If a lemma mainly restructures terms or stores rather than proving
--     progress/canonical forms, move it to the owning module instead.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Fin.Subset using (_∈_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Vec as Vec using (Vec; _∷_)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import UpDown
open import Terms
open import Reduction

------------------------------------------------------------------------
-- Progress witness (for closed terms)
------------------------------------------------------------------------

data Progress
  {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) : Set where
  done  : Value M → Progress M
  step  :
    ∀ {Ψ′}{Σ′ : Store 0 Ψ′}
      {ρ : Renameˢ Ψ Ψ′}
      {N : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    M —→[ ρ ] N →
    Progress M
  crash : Σ[ ℓ ∈ Label ] (M ≡ blame ℓ) → Progress M

------------------------------------------------------------------------
-- Canonical views of values
------------------------------------------------------------------------

data FunView
  {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)) : Set where
  fv-ƛ :
    ∀ {N : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B} →
    V ≡ (ƛ A ⇒ N) →
    FunView V

  fv-up-↦ :
    ∀ {A′ B′ : Ty Δ Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A′ ⇒ B′)}
      {p : Σ ∣ every Ψ ∣ every Ψ ⊢ A ⊒ A′}
      {q : Σ ∣ every Ψ ∣ every Ψ ⊢ B′ ⊑ B} →
    Value W →
    V ≡ (W at[ up ] (p ↦ q)) →
    FunView V

  fv-down-↦ :
    ∀ {A′ B′ : Ty Δ Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A′ ⇒ B′)}
      {p : Σ ∣ every Ψ ∣ every Ψ ⊢ A ⊑ A′}
      {q : Σ ∣ every Ψ ∣ every Ψ ⊢ B′ ⊒ B} →
    Value W →
    V ≡ (W at[ down ] (p ↦ q)) →
    FunView V

canonical-⇒ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
  Value V →
  FunView V
canonical-⇒ V-ƛ = fv-ƛ refl
canonical-⇒ {V = $ (κℕ n) ()} _
canonical-⇒ (V-at-up-↦ vW) = fv-up-↦ vW refl
canonical-⇒ (V-at-down-↦ vW) = fv-down-↦ vW refl

data AllView
  {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
  {A : Ty (suc Δ) Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)) : Set where
  av-Λ :
    ∀ {N : (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ A} →
    V ≡ Λ N →
    AllView V

  av-up-∀ :
    ∀ {A′ : Ty (suc Δ) Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A′)}
      {p : ⟰ᵗ Σ ∣ every Ψ ∣ every Ψ ⊢ A′ ⊑ A} →
    Value W →
    V ≡ (W at[ up ] (∀ᵖ p)) →
    AllView V

  av-down-∀ :
    ∀ {A′ : Ty (suc Δ) Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A′)}
      {p : ⟰ᵗ Σ ∣ every Ψ ∣ every Ψ ⊢ A′ ⊒ A} →
    Value W →
    V ≡ (W at[ down ] (∀ᵖ p)) →
    AllView V

  av-down-ν :
    ∀ {B : Ty Δ Ψ}
      {p : ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (false Vec.∷ every Ψ) ∣ (true Vec.∷ every Ψ) ⊢ ⇑ˢ B ⊒ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value W →
    V ≡ (W at[ down ] (ν p)) →
    AllView V

canonical-∀ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {A : Ty (suc Δ) Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
  Value V →
  AllView V
canonical-∀ V-Λ = av-Λ refl
canonical-∀ (V-at-up-∀ vW) = av-up-∀ vW refl
canonical-∀ (V-at-down-∀ vW) = av-down-∀ vW refl
canonical-∀ (V-at-down-ν vW) = av-down-ν vW refl
canonical-∀ {V = $ (κℕ n) ()} _

data NatView
  {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)) : Set where
  nv-const :
    ∀ {n : ℕ} →
    V ≡ $ (κℕ n) refl →
    NatView V

canonical-ℕ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)} →
  Value V →
  NatView V
canonical-ℕ {V = $ (κℕ n) eq} v with eq
... | refl = nv-const refl

data StarView
  {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ★) : Set where
  sv-up-tag :
    ∀ {G : Ty Δ Ψ}
      {g : Ground G}
      {gok : ⊢ g ok every Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G} →
    Value W →
    V ≡ (W at[ up ] (tag g gok)) →
    StarView V

canonical-★ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ★} →
  Value V →
  StarView V
canonical-★ (V-at-up-tag vW) = sv-up-tag vW refl
canonical-★ {V = $ (κℕ n) ()} _

data SealView
  {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
  {α : Seal Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ｀ α) : Set where
  sv-down-seal :
    ∀ {A : Ty Δ Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {h : Σ ∋ˢ α ⦂ A} →
      {α∈Φ : ⌊ α ⌋ ∈ every Ψ} →
    Value W →
    V ≡ (W at[ down ] (seal h α∈Φ)) →
    SealView V

canonical-｀ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {α : Seal Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ｀ α} →
  Value V →
  SealView V
canonical-｀ (V-at-down-seal vW) = sv-down-seal vW refl
canonical-｀ {V = $ (κℕ n) ()} _

projGround-progress :
  ∀ {Ψ}{Σ : Store 0 Ψ}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ★}
    {G : Ty 0 Ψ}
    {g′ : Ground G}
    {gok′ : ⊢ g′ ok every Ψ}
    {ℓ : Label} →
  Value M →
  Progress (M at[ down ] (untag g′ gok′ ℓ))
projGround-progress {g′ = g′} vM with canonical-★ vM
... | sv-up-tag {g = g} {gok = gok} vW refl with g ≟Ground g′
...   | yes refl = step at-up-tag-at-down-untag
...   | no neq = step (at-up-tag-at-down-untag-bad neq)

unseal-progress :
  ∀ {Ψ}{Σ : Store 0 Ψ}
    {A : Ty 0 Ψ}
    {α : Seal Ψ}
    {h : Σ ∋ˢ α ⦂ A}
    {α∈Φ : ⌊ α ⌋ ∈ every Ψ}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ｀ α} →
  Uniqueˢ Σ →
  Value M →
  Progress (M at[ up ] (unseal h α∈Φ))
unseal-progress {h = h} uΣ vM with canonical-｀ vM
... | sv-down-seal {h = h′} vW refl = step (at-down-seal-at-up-unseal uΣ)

------------------------------------------------------------------------
-- Progress (closed terms)
------------------------------------------------------------------------

progress :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  Uniqueˢ Σ →
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  Progress M
progress uΣ (` ())
progress uΣ (ƛ A ⇒ N) = done V-ƛ
progress uΣ (L · M) with progress uΣ L
... | step {ρ = ρ} {N = L′} L→L′ =
      step (ξ-·₁ (store-growth L→L′) L→L′)
... | crash (ℓ , refl) = step (blame-·₁ {ℓ = ℓ})
... | done vL with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
        step (ξ-·₂ vL (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-·₂ {ℓ = ℓ} vL)
...   | done vM with canonical-⇒ vL
...     | fv-ƛ refl = step (β vM)
...     | fv-up-↦ vW refl = step β-at-up-↦
...     | fv-down-↦ vW refl = step β-at-down-↦
progress uΣ (Λ N) = done V-Λ
progress uΣ ((M • α [ h ]) eq) with eq
... | refl with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
          step (ξ-·α (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-·α {ℓ = ℓ})
...   | done vM with canonical-∀ vM
...     | av-Λ refl = step β-Λ
...     | av-up-∀ vW refl = step β-at-up-∀
...     | av-down-∀ vW refl = step β-at-down-∀
...     | av-down-ν vW refl = step β-at-down-ν
progress uΣ (ν:= A ∙ N) = step β-ν
progress uΣ ($ κ eq) with eq
... | refl = done V-const
progress uΣ (L ⊕[ op ] M) with progress uΣ L
... | step {ρ = ρ} {N = L′} L→L′ =
      step (ξ-⊕₁ (store-growth L→L′) L→L′)
... | crash (ℓ , refl) = step (blame-⊕₁ {ℓ = ℓ})
... | done vL with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
        step (ξ-⊕₂ vL (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-⊕₂ {ℓ = ℓ} vL)
...   | done vM with canonical-ℕ vL | canonical-ℕ vM
...     | nv-const refl | nv-const refl with op
...       | addℕ = step δ-⊕
progress uΣ (M at[ up ] p) with progress uΣ M
... | step {ρ = ρ} {N = M′} M→M′ =
      step (ξ-at-up (store-growth M→M′) M→M′)
... | crash (ℓ , refl) = step (blame-at {ℓ = ℓ})
... | done vM with p
...   | tag g gok = done (V-at-up-tag vM)
...   | unseal h α∈Φ = unseal-progress uΣ vM
...   | p ↦ q = done (V-at-up-↦ vM)
...   | ∀ᵖ p = done (V-at-up-∀ vM)
...   | ν p = step β-at-up-ν
...   | id = step at-id-up
...   | p ； q = step β-at-up-；
progress uΣ (M at[ down ] p) with progress uΣ M
... | step {ρ = ρ} {N = M′} M→M′ =
      step (ξ-at-down (store-growth M→M′) M→M′)
... | crash (ℓ , refl) = step (blame-at {ℓ = ℓ})
... | done vM with p
...   | untag g gok ℓ = projGround-progress vM
...   | seal h α∈Φ = done (V-at-down-seal vM)
...   | p ↦ q = done (V-at-down-↦ vM)
...   | ∀ᵖ p = done (V-at-down-∀ vM)
...   | ν p = done (V-at-down-ν vM)
...   | id = step at-id-down
...   | p ； q = step β-at-down-；
progress uΣ (blame ℓ) = crash (ℓ , refl)

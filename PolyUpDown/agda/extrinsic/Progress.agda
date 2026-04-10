module Progress where

-- File Charter:
--   * Progress witnesses and canonical-form lemmas for closed extrinsic PolyUpDown terms.
--   * Connects closed typing derivations to either values, blame, or one store-threaded step.
-- Note to self:
--   * Keep reduction rules/value definitions in `Reduction.agda`.
--   * Keep preservation lemmas in `Preservation.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ; _,_)
open import Data.List using ([])
open import Relation.Nullary using (yes; no)

open import Types
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties
open import Reduction

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Σ : Store} (M : Term) : Set where
  done : Value M → Progress M
  step :
    ∀ {Σ′ : Store}{ρ : Renameˢ}{N : Term} →
    Σ ∣ M —→[ ρ ] Σ′ ∣ N →
    Progress M
  crash :
    Sigma.Σ Label (λ ℓ → M ≡ blame ℓ) →
    Progress M

------------------------------------------------------------------------
-- Canonical views
------------------------------------------------------------------------

data FunView (V : Term) : Set where
  fv-ƛ :
    ∀ {A : Ty}{N : Term} →
    V ≡ (ƛ A ⇒ N) →
    FunView V

  fv-up-↦ :
    ∀ {W : Term}{p : Down}{q : Up} →
    Value W →
    V ≡ (W up (p ↦ q)) →
    FunView V

  fv-down-↦ :
    ∀ {W : Term}{p : Up}{q : Down} →
    Value W →
    V ≡ (W down (p ↦ q)) →
    FunView V

canonical-⇒ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B : Ty} →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ (A ⇒ B) →
  FunView V
canonical-⇒ (ƛ A ⇒ N) (⊢ƛ wfA N⊢) = fv-ƛ refl
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ (_up_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢up {p = p ↦ q} W⊢ (wt-↦ p⊢ q⊢)) =
  fv-up-↦ vW refl
canonical-⇒ (_down_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down {p = p ↦ q} W⊢ (wt-↦ p⊢ q⊢)) =
  fv-down-↦ vW refl

data AllView (V : Term) : Set where
  av-Λ :
    ∀ {N : Term} →
    V ≡ (Λ N) →
    AllView V

  av-up-∀ :
    ∀ {W : Term}{p : Up} →
    Value W →
    V ≡ (W up (∀ᵖ p)) →
    AllView V

  av-down-∀ :
    ∀ {W : Term}{p : Down} →
    Value W →
    V ≡ (W down (∀ᵖ p)) →
    AllView V

  av-down-ν :
    ∀ {W : Term}{p : Down} →
    Value W →
    V ≡ (W down (ν p)) →
    AllView V

canonical-∀ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A : Ty} →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ (`∀ A) →
  AllView V
canonical-∀ (Λ N) (⊢Λ N⊢) = av-Λ refl
canonical-∀ ($ (κℕ n)) ()
canonical-∀ (_up_ {V = W} vW (∀ᵖ {p = p}))
  (⊢up {p = ∀ᵖ p} W⊢ (wt-∀ p⊢)) =
  av-up-∀ vW refl
canonical-∀ (_down_ {V = W} vW (∀ᵖ {p = p}))
  (⊢down {p = ∀ᵖ p} W⊢ (wt-∀ p⊢)) =
  av-down-∀ vW refl
canonical-∀ (_down_ {V = W} vW (ν_ {p = p}))
  (⊢down {p = ν p} W⊢ (wt-ν p⊢)) =
  av-down-ν vW refl

data NatView (V : Term) : Set where
  nv-const :
    ∀ {n} →
    V ≡ $ (κℕ n) →
    NatView V

canonical-ℕ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term} →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ (‵ `ℕ) →
  NatView V
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ (_up_ {V = W} vW tag)
  (⊢up {p = tag G} W⊢ ())
canonical-ℕ (_up_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢up {p = p ↦ q} W⊢ ())
canonical-ℕ (_up_ {V = W} vW (∀ᵖ {p = p}))
  (⊢up {p = ∀ᵖ p} W⊢ ())
canonical-ℕ (_down_ {V = W} vW seal)
  (⊢down {p = seal α} W⊢ ())
canonical-ℕ (_down_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down {p = p ↦ q} W⊢ ())
canonical-ℕ (_down_ {V = W} vW (∀ᵖ {p = p}))
  (⊢down {p = ∀ᵖ p} W⊢ ())
canonical-ℕ (_down_ {V = W} vW (ν_ {p = p}))
  (⊢down {p = ν p} W⊢ ())

data StarView (V : Term) : Set where
  sv-up-tag :
    ∀ {W : Term}{G : Ty}{g : Ground G} →
    Value W →
    V ≡ (W up (tag G)) →
    StarView V

canonical-★ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term} →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ ★ →
  StarView V
canonical-★ (_up_ {V = W} vW tag)
  (⊢up {p = tag G} W⊢ (wt-tag g gok)) =
  sv-up-tag {g = g} vW refl
canonical-★ ($ (κℕ n)) ()
canonical-★ (_down_ {V = W} vW seal)
  (⊢down {p = seal α} W⊢ ())
canonical-★ (_down_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down {p = p ↦ q} W⊢ ())
canonical-★ (_down_ {V = W} vW (∀ᵖ {p = p}))
  (⊢down {p = ∀ᵖ p} W⊢ ())
canonical-★ (_down_ {V = W} vW (ν_ {p = p}))
  (⊢down {p = ν p} W⊢ ())

data SealView {α : Seal} (V : Term) : Set where
  sv-down-seal :
    ∀ {W : Term} →
    Value W →
    V ≡ (W down (seal α)) →
    SealView V

canonical-｀ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}
    {α : Seal}{V : Term} →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ (｀ α) →
  SealView {α = α} V
canonical-｀ (_down_ {V = W} vW seal)
  (⊢down {p = seal α} W⊢ (wt-seal h α∈)) =
  sv-down-seal vW refl
canonical-｀ ($ (κℕ n)) ()
canonical-｀ (_up_ {V = W} vW tag)
  (⊢up {p = tag G} W⊢ ())
canonical-｀ (_up_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢up {p = p ↦ q} W⊢ ())
canonical-｀ (_up_ {V = W} vW (∀ᵖ {p = p}))
  (⊢up {p = ∀ᵖ p} W⊢ ())

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

projGround-progress :
  ∀ {Ψ}{Σ : Store}
    {M : Term}
    {G : Ty}
    {g′ : Ground G}
    {gok′ : ⊢ g′ ok (every Ψ)}
    {ℓ : Label} →
  Value M →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ ★ →
  Progress {Σ = Σ} (M down (untag G ℓ))
projGround-progress {g′ = g′} vM M⊢ with canonical-★ vM M⊢
... | sv-up-tag {g = g} vW refl with g ≟Ground g′
...   | yes refl = step (id-step tag-untag-ok)
...   | no neq = step (id-step (tag-untag-bad neq))

unseal-progress :
  ∀ {Ψ}{Σ : Store}
    {α : Seal}
    {M : Term} →
  Value M →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ (｀ α) →
  Progress {Σ = Σ} (M up (unseal α))
unseal-progress vM M⊢ with canonical-｀ vM M⊢
... | sv-down-seal vW refl = step (id-step seal-unseal)

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A →
  Progress {Σ = Σ} M
progress (⊢` ())
progress (⊢ƛ {M = N} {A = A} wfA N⊢) = done (ƛ A ⇒ N)
progress (⊢· {L = L} {M = M} L⊢ M⊢) with progress L⊢
... | step L→L′ = step (ξ-·₁ L→L′)
... | crash (ℓ , refl) = step (id-step blame-·₁)
... | done vL with progress M⊢
...   | step M→M′ = step (ξ-·₂ vL M→M′)
...   | crash (ℓ , refl) = step (id-step (blame-·₂ vL))
...   | done vM with canonical-⇒ vL L⊢
...     | fv-ƛ refl = step (id-step (β vM))
...     | fv-up-↦ vW refl = step (id-step β-up-↦)
...     | fv-down-↦ vW refl = step (id-step β-down-↦)
progress (⊢Λ {M = N} N⊢) = done (Λ N)
progress (⊢• {M = M} {A = A} {α = α} M⊢ α∈ h) with progress M⊢
... | step M→M′ = step (ξ-·α M→M′)
... | crash (ℓ , refl) = step (id-step blame-·α)
... | done vM with canonical-∀ vM M⊢
...   | av-Λ refl = step (id-step β-Λ)
...   | av-up-∀ vW refl = step (id-step β-up-∀)
...   | av-down-∀ vW refl = step (id-step β-down-∀)
...   | av-down-ν vW refl = step (id-step β-down-ν)
progress (⊢ν wfA M⊢) = step β-ν
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) with progress L⊢
... | step L→L′ = step (ξ-⊕₁ L→L′)
... | crash (ℓ , refl) = step (id-step blame-⊕₁)
... | done vL with progress M⊢
...   | step M→M′ = step (ξ-⊕₂ vL M→M′)
...   | crash (ℓ , refl) = step (id-step (blame-⊕₂ vL))
...   | done vM with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
...     | nv-const refl | nv-const refl with op
...       | addℕ = step (id-step δ-⊕)
progress (⊢up {M = M} {p = p} M⊢ hp) with progress M⊢
... | step M→M′ = step (ξ-up M→M′)
... | crash (ℓ , refl) = step (id-step blame-up)
... | done vM with p | hp
...   | tag G | wt-tag g gok = done (vM up tag)
...   | unseal α | wt-unseal h α∈ = unseal-progress vM M⊢
...   | p ↦ q | wt-↦ p⊢ q⊢ = done (vM up (_↦_ {p = p} {q = q}))
...   | ∀ᵖ p | wt-∀ p⊢ = done (vM up (∀ᵖ {p = p}))
...   | ν p | wt-ν p⊢ = step (id-step β-up-ν)
...   | id A | wt-id wfA = step (id-step id-up)
...   | p ； q | wt-； p⊢ q⊢ = step (id-step β-up-；)
progress (⊢down {M = M} {p = p} M⊢ hp) with progress M⊢
... | step M→M′ = step (ξ-down M→M′)
... | crash (ℓ , refl) = step (id-step blame-down)
... | done vM with p | hp
...   | untag G ℓ | wt-untag g′ gok′ .ℓ =
        projGround-progress {G = G} {g′ = g′} {gok′ = gok′} {ℓ = ℓ} vM M⊢
...   | seal α | wt-seal h α∈ = done (vM down seal)
...   | p ↦ q | wt-↦ p⊢ q⊢ = done (vM down (_↦_ {p = p} {q = q}))
...   | ∀ᵖ p | wt-∀ p⊢ = done (vM down (∀ᵖ {p = p}))
...   | ν p | wt-ν p⊢ = done (vM down (ν_ {p = p}))
...   | id A | wt-id wfA = step (id-step id-down)
...   | p ； q | wt-； p⊢ q⊢ = step (id-step β-down-；)
progress (⊢blame ℓ) = crash (ℓ , refl)

module ProgressFresh where

-- File Charter:
--   * Progress witnesses and canonical-form lemmas for closed extrinsic-inst
--   * PolyUpDown terms.
--   * Connects closed typing derivations to either values, blame, or one
--   * store-threaded reduction step for `ReductionFresh`.
-- Note to self:
--   * Keep raw reduction rules/value definitions in `Reduction.agda`.
--   * Keep fresh-store reduction rules in `ReductionFresh.agda`.
--   * Keep preservation/safety lemmas in `PreservationFresh.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ; _,_)
open import Data.List using (List; [])
open import Relation.Nullary using (yes; no)

open import Types
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties
open import Reduction
import ReductionFresh as Fresh

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Σ : Store} (M : Term) : Set where
  done : Value M → Progress M
  step :
    ∀ {Σ′ : Store}{N : Term} →
    Fresh._∣_—→_∣_ Σ M Σ′ N →
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
  (⊢up Φ W⊢ (wt-↦ {p = p} {q = q} p⊢ q⊢)) =
  fv-up-↦ vW refl
canonical-⇒ (_down_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down Φ W⊢ (wt-↦ {p = p} {q = q} p⊢ q⊢)) =
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
  (⊢up Φ W⊢ (wt-∀ {p = p} p⊢)) =
  av-up-∀ vW refl
canonical-∀ (_down_ {V = W} vW (∀ᵖ {p = p}))
  (⊢down Φ W⊢ (wt-∀ {p = p} p⊢)) =
  av-down-∀ vW refl
canonical-∀ (_down_ {V = W} vW (ν_ {p = p}))
  (⊢down Φ W⊢ (wt-ν {p = p} p⊢)) =
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
  (⊢up Φ W⊢ ())
canonical-ℕ (_up_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢up Φ W⊢ ())
canonical-ℕ (_up_ {V = W} vW (∀ᵖ {p = p}))
  (⊢up Φ W⊢ ())
canonical-ℕ (_down_ {V = W} vW seal)
  (⊢down Φ W⊢ ())
canonical-ℕ (_down_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down Φ W⊢ ())
canonical-ℕ (_down_ {V = W} vW (∀ᵖ {p = p}))
  (⊢down Φ W⊢ ())
canonical-ℕ (_down_ {V = W} vW (ν_ {p = p}))
  (⊢down Φ W⊢ ())

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
  (⊢up Φ W⊢ (wt-tag {G = G} g gok)) =
  sv-up-tag {g = g} vW refl
canonical-★ ($ (κℕ n)) ()
canonical-★ (_down_ {V = W} vW seal)
  (⊢down Φ W⊢ ())
canonical-★ (_down_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down Φ W⊢ ())
canonical-★ (_down_ {V = W} vW (∀ᵖ {p = p}))
  (⊢down Φ W⊢ ())
canonical-★ (_down_ {V = W} vW (ν_ {p = p}))
  (⊢down Φ W⊢ ())

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
  (⊢down Φ W⊢ (wt-seal {α = α} h α∈)) =
  sv-down-seal vW refl
canonical-｀ (_down_ {V = W} vW seal)
  (⊢down Φ W⊢ (wt-seal★ {α = α} h α∈)) =
  sv-down-seal vW refl
canonical-｀ ($ (κℕ n)) ()
canonical-｀ (_up_ {V = W} vW tag)
  (⊢up Φ W⊢ ())
canonical-｀ (_up_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢up Φ W⊢ ())
canonical-｀ (_up_ {V = W} vW (∀ᵖ {p = p}))
  (⊢up Φ W⊢ ())

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

projGround-progress :
  ∀ {Ψ}{Σ : Store}
    {M : Term}
    {Φ : List CastPerm}
    {G : Ty}
    {g′ : Ground G}
    {gok′ : ⊢ g′ ok Φ}
    {ℓ : Label} →
  Value M →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ ★ →
  Progress {Σ = Σ} (M down (untag G ℓ))
projGround-progress {g′ = g′} vM M⊢ with canonical-★ vM M⊢
... | sv-up-tag {g = g} vW refl with g ≟Ground g′
...   | yes refl = step (Fresh.id-step (tag-untag-ok vW))
...   | no neq = step (Fresh.id-step (tag-untag-bad vW neq))

unseal-progress :
  ∀ {Ψ}{Σ : Store}
    {α : Seal}
    {M : Term} →
  Value M →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ (｀ α) →
  Progress {Σ = Σ} (M up (unseal α))
unseal-progress vM M⊢ with canonical-｀ vM M⊢
... | sv-down-seal vW refl = step (Fresh.id-step (seal-unseal vW))

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
... | step L→L′ = step (Fresh.ξ-·₁ L→L′)
... | crash (ℓ , refl) = step (Fresh.id-step blame-·₁)
... | done vL with progress M⊢
...   | step M→M′ = step (Fresh.ξ-·₂ vL M→M′)
...   | crash (ℓ , refl) = step (Fresh.id-step (blame-·₂ vL))
...   | done vM with canonical-⇒ vL L⊢
...     | fv-ƛ refl = step (Fresh.id-step (β vM))
...     | fv-up-↦ vW refl = step (Fresh.id-step (β-up-↦ vW vM))
...     | fv-down-↦ vW refl = step (Fresh.id-step (β-down-↦ vW vM))
progress (⊢Λ {M = N} N⊢) = done (Λ N)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfT) with progress M⊢
... | step M→M′ = step (Fresh.ξ-·α M→M′)
... | crash (ℓ , refl) = step (Fresh.id-step blame-·α)
... | done vM with canonical-∀ vM M⊢
...   | av-Λ refl = step Fresh.β-Λ
...   | av-up-∀ vW refl = step (Fresh.id-step (β-up-∀ vW))
...   | av-down-∀ vW refl = step (Fresh.β-down-∀ vW)
...   | av-down-ν vW refl = step (Fresh.β-down-ν vW)
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) with progress L⊢
... | step L→L′ = step (Fresh.ξ-⊕₁ L→L′)
... | crash (ℓ , refl) = step (Fresh.id-step blame-⊕₁)
... | done vL with progress M⊢
...   | step M→M′ = step (Fresh.ξ-⊕₂ vL M→M′)
...   | crash (ℓ , refl) = step (Fresh.id-step (blame-⊕₂ vL))
...   | done vM with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
...     | nv-const refl | nv-const refl with op
...       | addℕ = step (Fresh.id-step δ-⊕)
progress (⊢up {M = M} {p = p} Φ M⊢ hp) with progress M⊢
... | step M→M′ = step (Fresh.ξ-up M→M′)
... | crash (ℓ , refl) = step (Fresh.id-step blame-up)
... | done vM with p | hp
...   | tag G | wt-tag g gok = done (vM up tag)
...   | unseal α | wt-unseal h α∈ = unseal-progress vM M⊢
...   | unseal α | wt-unseal★ h α∈ = unseal-progress vM M⊢
...   | p ↦ q | wt-↦ p⊢ q⊢ = done (vM up (_↦_ {p = p} {q = q}))
...   | ∀ᵖ p | wt-∀ p⊢ = done (vM up (∀ᵖ {p = p}))
...   | ν p | wt-ν p⊢ = step (Fresh.β-up-ν vM)
...   | id A | wt-id wfA = step (Fresh.id-step (id-up vM))
...   | p ； q | wt-； p⊢ q⊢ = step (Fresh.id-step (β-up-； vM))
progress (⊢down {M = M} {p = p} Φ M⊢ hp) with progress M⊢
... | step M→M′ = step (Fresh.ξ-down M→M′)
... | crash (ℓ , refl) = step (Fresh.id-step blame-down)
... | done vM with p | hp
...   | untag G ℓ | wt-untag g′ gok′ .ℓ =
        projGround-progress {G = G} {g′ = g′} {gok′ = gok′} {ℓ = ℓ} vM M⊢
...   | seal α | wt-seal h α∈ = done (vM down seal)
...   | seal α | wt-seal★ h α∈ = done (vM down seal)
...   | p ↦ q | wt-↦ p⊢ q⊢ = done (vM down (_↦_ {p = p} {q = q}))
...   | ∀ᵖ p | wt-∀ p⊢ = done (vM down (∀ᵖ {p = p}))
...   | ν p | wt-ν p⊢ = done (vM down (ν_ {p = p}))
...   | id A | wt-id wfA = step (Fresh.id-step (id-down vM))
...   | p ； q | wt-； p⊢ q⊢ = step (Fresh.id-step (β-down-； vM))
progress (⊢blame ℓ) = crash (ℓ , refl)

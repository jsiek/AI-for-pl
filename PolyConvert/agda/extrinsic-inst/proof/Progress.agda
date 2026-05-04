module proof.Progress where

-- File Charter:
--   * Canonical-form lemmas and progress for closed PolyConvert terms.
--   * Produces values, blame crashes, or one store-threaded reduction step.
--   * This proof depends on the top-level language, conversion, and reduction
--     definitions, but is kept out of the public definition layer.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.Product as Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Types
open import Imprecision
open import Conversion
open import Terms
open import Reduction

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Σ : Store} (M : Term) : Set where
  done : Value M → Progress M
  step :
    ∀ {Σ′ : Store}{N : Term} →
    Σ ∣ M —→ Σ′ ∣ N →
    Progress M
  crash :
    Product.Σ Label (λ ℓ → M ≡ blame ℓ) →
    Progress M

------------------------------------------------------------------------
-- Local decidable type equality
------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
＇ X ≟Ty ＇ Y with X ≟ Y
＇ X ≟Ty ＇ Y | yes X≡Y = yes (cong ＇_ X≡Y)
＇ X ≟Ty ＇ Y | no X≢Y = no (λ { refl → X≢Y refl })
＇ X ≟Ty ｀ α′ = no (λ ())
＇ X ≟Ty ‵ ι = no (λ ())
＇ X ≟Ty ★ = no (λ ())
＇ X ≟Ty (A ⇒ B) = no (λ ())
＇ X ≟Ty `∀ B = no (λ ())
｀ α ≟Ty ＇ Y = no (λ ())
｀ α ≟Ty ｀ α′ with α ≟ α′
｀ α ≟Ty ｀ α′ | yes α≡α′ = yes (cong ｀_ α≡α′)
｀ α ≟Ty ｀ α′ | no α≢α′ = no (λ { refl → α≢α′ refl })
｀ α ≟Ty ‵ ι = no (λ ())
｀ α ≟Ty ★ = no (λ ())
｀ α ≟Ty (A ⇒ B) = no (λ ())
｀ α ≟Ty `∀ B = no (λ ())
‵ ι ≟Ty ＇ Y = no (λ ())
‵ ι ≟Ty ｀ α′ = no (λ ())
‵ `ℕ ≟Ty ‵ `ℕ = yes refl
‵ `ℕ ≟Ty ‵ `𝔹 = no (λ ())
‵ `𝔹 ≟Ty ‵ `ℕ = no (λ ())
‵ `𝔹 ≟Ty ‵ `𝔹 = yes refl
‵ ι ≟Ty ★ = no (λ ())
‵ ι ≟Ty (A ⇒ B) = no (λ ())
‵ ι ≟Ty `∀ B = no (λ ())
★ ≟Ty ＇ Y = no (λ ())
★ ≟Ty ｀ α′ = no (λ ())
★ ≟Ty ‵ ι = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (A ⇒ B) = no (λ ())
★ ≟Ty `∀ B = no (λ ())
(A ⇒ B) ≟Ty ＇ Y = no (λ ())
(A ⇒ B) ≟Ty ｀ α′ = no (λ ())
(A ⇒ B) ≟Ty ‵ ι = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (A′ ⇒ B′) with A ≟Ty A′ | B ≟Ty B′
(A ⇒ B) ≟Ty (A′ ⇒ B′) | yes A≡A′ | yes B≡B′ =
  yes (cong₂ _⇒_ A≡A′ B≡B′)
(A ⇒ B) ≟Ty (A′ ⇒ B′) | no A≢A′ | _ =
  no (λ { refl → A≢A′ refl })
(A ⇒ B) ≟Ty (A′ ⇒ B′) | yes A≡A′ | no B≢B′ =
  no (λ { refl → B≢B′ refl })
(A ⇒ B) ≟Ty `∀ C = no (λ ())
`∀ A ≟Ty ＇ Y = no (λ ())
`∀ A ≟Ty ｀ α′ = no (λ ())
`∀ A ≟Ty ‵ ι = no (λ ())
`∀ A ≟Ty ★ = no (λ ())
`∀ A ≟Ty (B ⇒ C) = no (λ ())
`∀ A ≟Ty `∀ B with A ≟Ty B
`∀ A ≟Ty `∀ B | yes A≡B = yes (cong `∀ A≡B)
`∀ A ≟Ty `∀ B | no A≢B = no (λ { refl → A≢B refl })

------------------------------------------------------------------------
-- Canonical views
------------------------------------------------------------------------

data FunView (V : Term) : Set where
  fv-ƛ :
    ∀ {A : Ty}{N : Term} →
    V ≡ (ƛ A ⇒ N) →
    FunView V

  fv-⇑↦ :
    ∀ {W : Term}{p q : Imp} →
    Value W →
    V ≡ (W ⇑ (A⇒B⊑A′⇒B′ p q)) →
    FunView V

  fv-⇓↦ :
    ∀ {W : Term}{p q : Imp} →
    Value W →
    V ≡ (W ⇓ (A⇒B⊑A′⇒B′ p q)) →
    FunView V

  fv-↑↦ :
    ∀ {W : Term}{p : Conv↓}{q : Conv↑} →
    Value W →
    V ≡ (W ↑ (↑-⇒ p q)) →
    FunView V

  fv-↓↦ :
    ∀ {W : Term}{p : Conv↑}{q : Conv↓} →
    Value W →
    V ≡ (W ↓ (↓-⇒ p q)) →
    FunView V

canonical-⇒ :
  ∀ {Ψ}{Σ : Store}{V : Term}{A B : Ty} →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ V ⦂ (A ⇒ B) →
  FunView V
canonical-⇒ (ƛ A ⇒ N) (⊢ƛ wfA N⊢) = fv-ƛ refl
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ (Λ N) ()
canonical-⇒ (_⇑_ {V = W} vW tagν) (⊢up () W⊢)
canonical-⇒ (_⇑_ {V = W} vW tag) (⊢up () W⊢)
canonical-⇒ (_⇑_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢up (⊑-⇒ p⊢ q⊢) W⊢) =
  fv-⇑↦ vW refl
canonical-⇒ (_⇑_ {V = W} vW `∀) (⊢up () W⊢)
canonical-⇒ (_⇓_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢down (⊑-⇒ p⊢ q⊢) W⊢) =
  fv-⇓↦ vW refl
canonical-⇒ (_⇓_ {V = W} vW `∀) (⊢down () W⊢)
canonical-⇒ (_⇓_ {V = W} vW (ν_ {B = B} {p = p})) (⊢down () W⊢)
canonical-⇒ (_↑_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢reveal (⊢↑-⇒ p⊢ q⊢) W⊢) =
  fv-↑↦ vW refl
canonical-⇒ (_↑_ {V = W} vW `∀) (⊢reveal () W⊢)
canonical-⇒ (_↓_ {V = W} vW seal) (⊢conceal () W⊢)
canonical-⇒ (_↓_ {V = W} vW (_↦_ {p = p} {q = q}))
  (⊢conceal (⊢↓-⇒ p⊢ q⊢) W⊢) =
  fv-↓↦ vW refl
canonical-⇒ (_↓_ {V = W} vW `∀) (⊢conceal () W⊢)

data AllView (V : Term) : Set where
  av-Λ :
    ∀ {N : Term} →
    V ≡ (Λ N) →
    AllView V

  av-⇑∀ :
    ∀ {W : Term}{p : Imp} →
    Value W →
    V ≡ (W ⇑ (`∀A⊑∀B p)) →
    AllView V

  av-⇓∀ :
    ∀ {W : Term}{p : Imp} →
    Value W →
    V ≡ (W ⇓ (`∀A⊑∀B p)) →
    AllView V

  av-⇓ν :
    ∀ {W : Term}{B : Ty}{p : Imp} →
    Value W →
    V ≡ (W ⇓ (`∀A⊑B B p)) →
    AllView V

  av-↑∀ :
    ∀ {W : Term}{c : Conv↑} →
    Value W →
    V ≡ (W ↑ (↑-∀ c)) →
    AllView V

  av-↓∀ :
    ∀ {W : Term}{c : Conv↓} →
    Value W →
    V ≡ (W ↓ (↓-∀ c)) →
    AllView V

canonical-∀ :
  ∀ {Ψ}{Σ : Store}{V : Term}{A : Ty} →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ V ⦂ (`∀ A) →
  AllView V
canonical-∀ (ƛ A ⇒ N) ()
canonical-∀ ($ (κℕ n)) ()
canonical-∀ (Λ N) (⊢Λ vN N⊢) = av-Λ refl
canonical-∀ (_⇑_ {V = W} vW tagν) (⊢up () W⊢)
canonical-∀ (_⇑_ {V = W} vW tag) (⊢up () W⊢)
canonical-∀ (_⇑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢up () W⊢)
canonical-∀ (_⇑_ {V = W} vW (`∀ {p = p})) (⊢up (⊑-∀ p⊢) W⊢) =
  av-⇑∀ vW refl
canonical-∀ (_⇓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢down () W⊢)
canonical-∀ (_⇓_ {V = W} vW (`∀ {p = p})) (⊢down (⊑-∀ p⊢) W⊢) =
  av-⇓∀ vW refl
canonical-∀ (_⇓_ {V = W} vW (ν_ {B = B} {p = p}))
  (⊢down (⊑-ν wfB occ p⊢) W⊢) =
  av-⇓ν vW refl
canonical-∀ (_↑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢reveal () W⊢)
canonical-∀ (_↑_ {V = W} vW (`∀ {c = c}))
  (⊢reveal (⊢↑-∀ c⊢) W⊢) =
  av-↑∀ vW refl
canonical-∀ (_↓_ {V = W} vW seal) (⊢conceal () W⊢)
canonical-∀ (_↓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢conceal () W⊢)
canonical-∀ (_↓_ {V = W} vW (`∀ {c = c}))
  (⊢conceal (⊢↓-∀ c⊢) W⊢) =
  av-↓∀ vW refl

data NatView (V : Term) : Set where
  nv-const :
    ∀ {n : ℕ} →
    V ≡ $ (κℕ n) →
    NatView V

canonical-ℕ :
  ∀ {Ψ}{Σ : Store}{V : Term} →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ V ⦂ (‵ `ℕ) →
  NatView V
canonical-ℕ (ƛ A ⇒ N) ()
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ (Λ N) ()
canonical-ℕ (_⇑_ {V = W} vW tagν) (⊢up () W⊢)
canonical-ℕ (_⇑_ {V = W} vW tag) (⊢up () W⊢)
canonical-ℕ (_⇑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢up () W⊢)
canonical-ℕ (_⇑_ {V = W} vW `∀) (⊢up () W⊢)
canonical-ℕ (_⇓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢down () W⊢)
canonical-ℕ (_⇓_ {V = W} vW `∀) (⊢down () W⊢)
canonical-ℕ (_⇓_ {V = W} vW (ν_ {B = B} {p = p})) (⊢down () W⊢)
canonical-ℕ (_↑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢reveal () W⊢)
canonical-ℕ (_↑_ {V = W} vW `∀) (⊢reveal () W⊢)
canonical-ℕ (_↓_ {V = W} vW seal) (⊢conceal () W⊢)
canonical-ℕ (_↓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢conceal () W⊢)
canonical-ℕ (_↓_ {V = W} vW `∀) (⊢conceal () W⊢)

data StarView (V : Term) : Set where
  sv-⇑tag :
    ∀ {W : Term}{p : Imp} →
    Value W →
    V ≡ (W ⇑ (A⊑★ p)) →
    StarView V

canonical-★ :
  ∀ {Ψ}{Σ : Store}{V : Term} →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ V ⦂ ★ →
  StarView V
canonical-★ (ƛ A ⇒ N) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ (Λ N) ()
canonical-★ (_⇑_ {V = W} vW tagν) (⊢up (⊑-★ν ()) W⊢)
canonical-★ (_⇑_ {V = W} vW tag) (⊢up (⊑-★ g p⊢) W⊢) =
  sv-⇑tag vW refl
canonical-★ (_⇑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢up () W⊢)
canonical-★ (_⇑_ {V = W} vW `∀) (⊢up () W⊢)
canonical-★ (_⇓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢down () W⊢)
canonical-★ (_⇓_ {V = W} vW `∀) (⊢down () W⊢)
canonical-★ (_⇓_ {V = W} vW (ν_ {B = B} {p = p})) (⊢down () W⊢)
canonical-★ (_↑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢reveal () W⊢)
canonical-★ (_↑_ {V = W} vW `∀) (⊢reveal () W⊢)
canonical-★ (_↓_ {V = W} vW seal) (⊢conceal () W⊢)
canonical-★ (_↓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢conceal () W⊢)
canonical-★ (_↓_ {V = W} vW `∀) (⊢conceal () W⊢)

data SealView {α : Seal} (V : Term) : Set where
  sv-↓seal :
    ∀ {W : Term} →
    Value W →
    V ≡ (W ↓ (↓-seal α)) →
    SealView V

canonical-｀ :
  ∀ {Ψ}{Σ : Store}{V : Term}{α : Seal} →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ V ⦂ (｀ α) →
  SealView {α = α} V
canonical-｀ (ƛ A ⇒ N) ()
canonical-｀ ($ (κℕ n)) ()
canonical-｀ (Λ N) ()
canonical-｀ (_⇑_ {V = W} vW tagν) (⊢up () W⊢)
canonical-｀ (_⇑_ {V = W} vW tag) (⊢up () W⊢)
canonical-｀ (_⇑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢up () W⊢)
canonical-｀ (_⇑_ {V = W} vW `∀) (⊢up () W⊢)
canonical-｀ (_⇓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢down () W⊢)
canonical-｀ (_⇓_ {V = W} vW `∀) (⊢down () W⊢)
canonical-｀ (_⇓_ {V = W} vW (ν_ {B = B} {p = p})) (⊢down () W⊢)
canonical-｀ (_↑_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢reveal () W⊢)
canonical-｀ (_↑_ {V = W} vW `∀) (⊢reveal () W⊢)
canonical-｀ (_↓_ {V = W} vW seal) (⊢conceal (⊢↓-seal h) W⊢) =
  sv-↓seal vW refl
canonical-｀ (_↓_ {V = W} vW (_↦_ {p = p} {q = q})) (⊢conceal () W⊢)
canonical-｀ (_↓_ {V = W} vW `∀) (⊢conceal () W⊢)

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

untag-progress :
  ∀ {Ψ}{Σ : Store}{M : Term}{q : Imp} →
  Value M →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ ★ →
  Progress {Σ = Σ} (M ⇓ (A⊑★ q))
untag-progress {q = q} vM M⊢ with canonical-★ vM M⊢
... | sv-⇑tag {p = p} vW refl with tgt⊑ p ≟Ty tgt⊑ q
untag-progress {q = q} vM M⊢ | sv-⇑tag {p = p} vW refl | yes eq =
  step (pure-step (tag-untag-ok vW eq))
untag-progress {q = q} vM M⊢ | sv-⇑tag {p = p} vW refl | no neq =
  step (pure-step (tag-untag-bad {ℓ = 0} vW neq))

unseal-progress :
  ∀ {Ψ}{Σ : Store}{α : Seal}{M : Term} →
  Value M →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ (｀ α) →
  Progress {Σ = Σ} (M ↑ (↑-unseal α))
unseal-progress vM M⊢ with canonical-｀ vM M⊢
... | sv-↓seal vW refl = step (pure-step (seal-unseal vW))

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
progress (⊢· {L = L} {M = M} L⊢ M⊢) | step L→L′ =
  step (ξ-·₁ L→L′)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-·₁)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL with progress M⊢
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-·₂ vL M→M′)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | crash (ℓ , refl) =
  step (pure-step (blame-·₂ vL))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    with canonical-⇒ vL L⊢
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-ƛ refl =
  step (pure-step (β vM))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-⇑↦ vW refl =
  step (pure-step (β-up-↦ vW vM))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-⇓↦ vW refl =
  step (pure-step (β-down-↦ vW vM))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-↑↦ vW refl =
  step (pure-step (β-reveal-↦ vW vM))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-↓↦ vW refl =
  step (pure-step (β-conceal-↦ vW vM))
progress (⊢Λ {M = N} vN N⊢) = done (Λ N)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) with progress M⊢
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | step M→M′ =
  step (ξ-·α M→M′)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | crash (ℓ , refl) =
  step (pure-step blame-·α)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    with canonical-∀ vM M⊢
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    | av-Λ refl =
  step β-Λ
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    | av-⇑∀ vW refl =
  step (pure-step (β-up-∀ vW))
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    | av-⇓∀ vW refl =
  step (β-down-∀ vW)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    | av-⇓ν vW refl =
  step (β-down-ν vW)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    | av-↑∀ vW refl =
  step (β-reveal-∀ vW)
progress (⊢• {M = M} {B = B} {T = T} M⊢ wfB wfT) | done vM
    | av-↓∀ vW refl =
  step (β-conceal-∀ vW)
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) with progress L⊢
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | crash (ℓ , refl) =
  step (pure-step blame-⊕₁)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL with progress M⊢
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | crash (ℓ , refl) =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | done vM
    with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
progress (⊢⊕ {L = L} {M = M} L⊢ addℕ M⊢) | done vL | done vM
    | nv-const refl | nv-const refl =
  step (pure-step δ-⊕)
progress (⊢up {M = M} {p = p} p⊢ M⊢) with progress M⊢
progress (⊢up {M = M} {p = p} p⊢ M⊢) | step M→M′ =
  step (ξ-⇑ M→M′)
progress (⊢up {M = M} {p = p} p⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-up)
progress (⊢up {M = M} {p = ★⊑★} ⊑-★★ M⊢) | done vM =
  step (pure-step (id-up-★ vM))
progress (⊢up {M = M} {p = X⊑★ X} (⊑-★ν ()) M⊢) | done vM
progress (⊢up {M = M} {p = A⊑★ p} (⊑-★ g p⊢) M⊢) | done vM =
  done (vM ⇑ tag)
progress (⊢up {M = M} {p = X⊑X X} (⊑-＇ ()) M⊢) | done vM
progress (⊢up {M = M} {p = α⊑α α} (⊑-｀ wfα) M⊢) | done vM =
  step (pure-step (id-up-｀ vM))
progress (⊢up {M = M} {p = ι⊑ι ι} ⊑-‵ M⊢) | done vM =
  step (pure-step (id-up-‵ vM))
progress (⊢up {M = M} {p = A⇒B⊑A′⇒B′ p q} (⊑-⇒ p⊢ q⊢) M⊢)
    | done vM =
  done (vM ⇑ (_↦_ {p = p} {q = q}))
progress (⊢up {M = M} {p = `∀A⊑∀B p} (⊑-∀ p⊢) M⊢) | done vM =
  done (vM ⇑ (`∀ {p = p}))
progress (⊢up {M = M} {p = `∀A⊑B B p} (⊑-ν wfB occ p⊢) M⊢)
    | done vM =
  step (β-up-ν vM)
progress (⊢down {M = M} {p = p} p⊢ M⊢) with progress M⊢
progress (⊢down {M = M} {p = p} p⊢ M⊢) | step M→M′ =
  step (ξ-⇓ M→M′)
progress (⊢down {M = M} {p = p} p⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-down)
progress (⊢down {M = M} {p = ★⊑★} ⊑-★★ M⊢) | done vM =
  step (pure-step (id-down-★ vM))
progress (⊢down {M = M} {p = X⊑★ X} (⊑-★ν ()) M⊢) | done vM
progress (⊢down {M = M} {p = A⊑★ p} (⊑-★ g p⊢) M⊢) | done vM =
  untag-progress {q = p} vM M⊢
progress (⊢down {M = M} {p = X⊑X X} (⊑-＇ ()) M⊢) | done vM
progress (⊢down {M = M} {p = α⊑α α} (⊑-｀ wfα) M⊢) | done vM =
  step (pure-step (id-down-｀ vM))
progress (⊢down {M = M} {p = ι⊑ι ι} ⊑-‵ M⊢) | done vM =
  step (pure-step (id-down-‵ vM))
progress
  (⊢down {M = M} {p = A⇒B⊑A′⇒B′ p q} (⊑-⇒ p⊢ q⊢) M⊢)
  | done vM =
  done (vM ⇓ (_↦_ {p = p} {q = q}))
progress (⊢down {M = M} {p = `∀A⊑∀B p} (⊑-∀ p⊢) M⊢) | done vM =
  done (vM ⇓ (`∀ {p = p}))
progress (⊢down {M = M} {p = `∀A⊑B B p} (⊑-ν wfB occ p⊢) M⊢)
    | done vM =
  done (vM ⇓ (ν_ {B = B} {p = p}))
progress (⊢reveal {M = M} {c = c} c⊢ M⊢) with progress M⊢
progress (⊢reveal {M = M} {c = c} c⊢ M⊢) | step M→M′ =
  step (ξ-↑ M→M′)
progress (⊢reveal {M = M} {c = c} c⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-reveal)
progress (⊢reveal {M = M} {c = ↑-unseal α} (⊢↑-unseal h) M⊢)
    | done vM =
  unseal-progress vM M⊢
progress (⊢reveal {M = M} {c = ↑-⇒ p q} (⊢↑-⇒ p⊢ q⊢) M⊢)
    | done vM =
  done (vM ↑ (_↦_ {p = p} {q = q}))
progress (⊢reveal {M = M} {c = ↑-∀ c} (⊢↑-∀ c⊢) M⊢) | done vM =
  done (vM ↑ (`∀ {c = c}))
progress (⊢reveal {M = M} {c = ↑-id A} (⊢↑-id wfA) M⊢) | done vM =
  step (pure-step (id-reveal vM))
progress (⊢conceal {M = M} {c = c} c⊢ M⊢) with progress M⊢
progress (⊢conceal {M = M} {c = c} c⊢ M⊢) | step M→M′ =
  step (ξ-↓ M→M′)
progress (⊢conceal {M = M} {c = c} c⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-conceal)
progress (⊢conceal {M = M} {c = ↓-seal α} (⊢↓-seal h) M⊢) | done vM =
  done (vM ↓ seal)
progress (⊢conceal {M = M} {c = ↓-⇒ p q} (⊢↓-⇒ p⊢ q⊢) M⊢)
    | done vM =
  done (vM ↓ (_↦_ {p = p} {q = q}))
progress (⊢conceal {M = M} {c = ↓-∀ c} (⊢↓-∀ c⊢) M⊢) | done vM =
  done (vM ↓ (`∀ {c = c}))
progress (⊢conceal {M = M} {c = ↓-id A} (⊢↓-id wfA) M⊢) | done vM =
  step (pure-step (id-conceal vM))
progress (⊢blame ℓ) = crash (ℓ , refl)

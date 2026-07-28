module proof.Core.Properties.NuImprecisionBinderPermutationProperties where

-- File Charter:
--   * Canonical adjacent-binder permutation algebra for well-formed indexed
--     type imprecision.
--   * Permutes paired universal binders and mixed universal/source-only
--     binders, including occurrence evidence needed by source-only `ν`.
--   * Contains no endpoint-MLB selection, term relation, or simulation result.

open import Data.Empty using (⊥-elim)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc)
open import Data.Nat.Base using (z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.Core.Properties.ImprecisionProperties using
  ( idᵢ-var-identity
  ; ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; un⇑ᴸᵢ-ˣ∈
  ; no-⇑ᴸᵢ-zero-left
  )
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf-ext
  ; occurs-zero-rename-ext
  ; rename-cong
  ; renameᵗ-compose
  ; renameᵗ-id
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties

swap01ᵢ : Renameᵗ
swap01ᵢ zero = suc zero
swap01ᵢ (suc zero) = zero
swap01ᵢ (suc (suc X)) = suc (suc X)

swap01-involutiveᵢ : ∀ X → swap01ᵢ (swap01ᵢ X) ≡ X
swap01-involutiveᵢ zero = refl
swap01-involutiveᵢ (suc zero) = refl
swap01-involutiveᵢ (suc (suc X)) = refl

ext-swap01-involutiveᵢ :
  ∀ X → extᵗ swap01ᵢ (extᵗ swap01ᵢ X) ≡ X
ext-swap01-involutiveᵢ zero = refl
ext-swap01-involutiveᵢ (suc X) = cong suc (swap01-involutiveᵢ X)

renameᵗ-swap01-involutiveᵢ :
  ∀ A → renameᵗ swap01ᵢ (renameᵗ swap01ᵢ A) ≡ A
renameᵗ-swap01-involutiveᵢ A =
  trans
    (renameᵗ-compose swap01ᵢ swap01ᵢ A)
    (trans (rename-cong swap01-involutiveᵢ A) (renameᵗ-id A))

renameᵗ-ext-swap01-involutiveᵢ :
  ∀ A →
  renameᵗ (extᵗ swap01ᵢ) (renameᵗ (extᵗ swap01ᵢ) A) ≡ A
renameᵗ-ext-swap01-involutiveᵢ A =
  trans
    (renameᵗ-compose (extᵗ swap01ᵢ) (extᵗ swap01ᵢ) A)
    (trans (rename-cong ext-swap01-involutiveᵢ A) (renameᵗ-id A))

swap01-pres-<ᵢ :
  ∀ {Δ X} →
  X < suc (suc Δ) →
  swap01ᵢ X < suc (suc Δ)
swap01-pres-<ᵢ {X = zero} z<s = s<s z<s
swap01-pres-<ᵢ {X = suc zero} (s<s z<s) = z<s
swap01-pres-<ᵢ {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s (s<s X<Δ)

rename-assm²-swapRight∀∀ᵢ :
  ∀ {Φ a} →
  a ∈ ∀ᵢᶜ (∀ᵢᶜ Φ) →
  rename-assm²ᵢ (λ X → X) swap01ᵢ a ∈ swapRight∀∀ᵢ Φ
rename-assm²-swapRight∀∀ᵢ {a = zero ˣ⊑★} =
  λ { (here ()) ; (there a∈) → ⊥-elim (no-⇑ᵢ-zero-star a∈) }
rename-assm²-swapRight∀∀ᵢ {a = suc zero ˣ⊑★}
    (here ())
rename-assm²-swapRight∀∀ᵢ {a = suc zero ˣ⊑★}
    (there a∈) =
  ⊥-elim (no-∀ctx-zero-starᵢ (un⇑ᵢ-★∈ a∈))
rename-assm²-swapRight∀∀ᵢ {a = suc (suc X) ˣ⊑★}
    (here ())
rename-assm²-swapRight∀∀ᵢ {a = suc (suc X) ˣ⊑★}
    (there (here ()))
rename-assm²-swapRight∀∀ᵢ {a = suc (suc X) ˣ⊑★}
    (there (there a∈)) =
  there (there a∈)
rename-assm²-swapRight∀∀ᵢ {a = zero ˣ⊑ˣ zero}
    (here refl) =
  here refl
rename-assm²-swapRight∀∀ᵢ {a = zero ˣ⊑ˣ zero}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-swapRight∀∀ᵢ {a = zero ˣ⊑ˣ suc Y}
    (here ())
rename-assm²-swapRight∀∀ᵢ {a = zero ˣ⊑ˣ suc Y}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-swapRight∀∀ᵢ {a = suc zero ˣ⊑ˣ zero}
    (here ())
rename-assm²-swapRight∀∀ᵢ {a = suc zero ˣ⊑ˣ zero}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-swapRight∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc zero} (here ())
rename-assm²-swapRight∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc zero} (there a∈) =
  there (here refl)
rename-assm²-swapRight∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc (suc Y)} (here ())
rename-assm²-swapRight∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc (suc Y)} (there a∈) =
  ⊥-elim (no-∀ctx-zero-leftᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ zero} (here ())
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc zero} (here ())
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc zero} (there a∈) =
  ⊥-elim (no-∀ctx-zero-rightᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc (suc Y)} (here ())
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc (suc Y)}
    (there (here ()))
rename-assm²-swapRight∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc (suc Y)}
    (there (there a∈)) =
  there (there a∈)

⊑-swapRight01∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ A ⊑ B ⊣ suc (suc Δᴿ) →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ A ⊑ renameᵗ swap01ᵢ B ⊣ suc (suc Δᴿ)
⊑-swapRight01∀∀ᵢ {A = A} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ renameᵗ swap01ᵢ _ ⊣ _)
    (renameᵗ-id A)
    (⊑-renameᵗ²ᵢ
      { ρ = λ X → X }
      { σ = swap01ᵢ }
      rename-assm²-swapRight∀∀ᵢ
      (λ X<Δ → X<Δ)
      swap01-pres-<ᵢ
      p)

rename-assm²-swapLeft∀∀ᵢ :
  ∀ {Φ a} →
  a ∈ ∀ᵢᶜ (∀ᵢᶜ Φ) →
  rename-assm²ᵢ swap01ᵢ (λ X → X) a ∈ swapRight∀∀ᵢ Φ
rename-assm²-swapLeft∀∀ᵢ {a = zero ˣ⊑★} =
  λ { (here ()) ; (there a∈) → ⊥-elim (no-⇑ᵢ-zero-star a∈) }
rename-assm²-swapLeft∀∀ᵢ {a = suc zero ˣ⊑★}
    (here ())
rename-assm²-swapLeft∀∀ᵢ {a = suc zero ˣ⊑★}
    (there a∈) =
  ⊥-elim (no-∀ctx-zero-starᵢ (un⇑ᵢ-★∈ a∈))
rename-assm²-swapLeft∀∀ᵢ {a = suc (suc X) ˣ⊑★}
    (here ())
rename-assm²-swapLeft∀∀ᵢ {a = suc (suc X) ˣ⊑★}
    (there (here ()))
rename-assm²-swapLeft∀∀ᵢ {a = suc (suc X) ˣ⊑★}
    (there (there a∈)) =
  there (there a∈)
rename-assm²-swapLeft∀∀ᵢ {a = zero ˣ⊑ˣ zero}
    (here refl) =
  there (here refl)
rename-assm²-swapLeft∀∀ᵢ {a = zero ˣ⊑ˣ zero}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-swapLeft∀∀ᵢ {a = zero ˣ⊑ˣ suc Y}
    (here ())
rename-assm²-swapLeft∀∀ᵢ {a = zero ˣ⊑ˣ suc Y}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-swapLeft∀∀ᵢ {a = suc zero ˣ⊑ˣ zero}
    (here ())
rename-assm²-swapLeft∀∀ᵢ {a = suc zero ˣ⊑ˣ zero}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-swapLeft∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc zero} (here ())
rename-assm²-swapLeft∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc zero} (there a∈) =
  here refl
rename-assm²-swapLeft∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc (suc Y)} (here ())
rename-assm²-swapLeft∀∀ᵢ
    {a = suc zero ˣ⊑ˣ suc (suc Y)} (there a∈) =
  ⊥-elim (no-∀ctx-zero-leftᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ zero} (here ())
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc zero} (here ())
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc zero} (there a∈) =
  ⊥-elim (no-∀ctx-zero-rightᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc (suc Y)} (here ())
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc (suc Y)}
    (there (here ()))
rename-assm²-swapLeft∀∀ᵢ
    {a = suc (suc X) ˣ⊑ˣ suc (suc Y)}
    (there (there a∈)) =
  there (there a∈)

⊑-swapLeft01∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ A ⊑ B ⊣ suc (suc Δᴿ) →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ renameᵗ swap01ᵢ A ⊑ B ⊣ suc (suc Δᴿ)
⊑-swapLeft01∀∀ᵢ {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ renameᵗ swap01ᵢ _ ⊑ T ⊣ _)
    (renameᵗ-id B)
    (⊑-renameᵗ²ᵢ
      { ρ = swap01ᵢ }
      { σ = λ X → X }
      rename-assm²-swapLeft∀∀ᵢ
      swap01-pres-<ᵢ
      (λ X<Δ → X<Δ)
      p)

renameᵗ-swap01-liftᵢ :
  ∀ B →
  renameᵗ swap01ᵢ (⇑ᵗ B) ≡ renameᵗ (extᵗ suc) B
renameᵗ-swap01-liftᵢ B =
  trans
    (renameᵗ-compose suc swap01ᵢ B)
    (rename-cong
      (λ { zero → refl ; (suc X) → refl })
      B)

swap01ᵢ-after-suc :
  ∀ X → swap01ᵢ (suc X) ≡ extᵗ suc X
swap01ᵢ-after-suc zero = refl
swap01ᵢ-after-suc (suc X) = refl

rename-assm²-congᵢ :
  ∀ {τ τ′ σ σ′ a} →
  (∀ X → τ X ≡ τ′ X) →
  (∀ X → σ X ≡ σ′ X) →
  rename-assm²ᵢ τ σ a ≡ rename-assm²ᵢ τ′ σ′ a
rename-assm²-congᵢ {a = X ˣ⊑★} eqτ eqσ =
  cong (λ Y → Y ˣ⊑★) (eqτ X)
rename-assm²-congᵢ {a = X ˣ⊑ˣ Y} eqτ eqσ =
  cong₂ _ˣ⊑ˣ_ (eqτ X) (eqσ Y)

rename-assm²-composeᵢ :
  ∀ τ σ υ ω a →
  rename-assm²ᵢ υ ω (rename-assm²ᵢ τ σ a) ≡
    rename-assm²ᵢ (λ X → υ (τ X)) (λ X → ω (σ X)) a
rename-assm²-composeᵢ τ σ υ ω (X ˣ⊑★) = refl
rename-assm²-composeᵢ τ σ υ ω (X ˣ⊑ˣ Y) = refl

rename-assm²-crossed-right∀∀ᵢ :
  ∀ {Φ a} →
  a ∈ ∀ᵢᶜ Φ →
  rename-assm²ᵢ suc (extᵗ suc) a ∈ swapRight∀∀ᵢ Φ
rename-assm²-crossed-right∀∀ᵢ {a = a} a∈ =
  subst (_∈ swapRight∀∀ᵢ _)
    (trans
      (rename-assm²-composeᵢ suc suc (λ X → X) swap01ᵢ a)
      (rename-assm²-congᵢ (λ X → refl) swap01ᵢ-after-suc))
    (rename-assm²-swapRight∀∀ᵢ (rename-assm²-∀ᵢ a∈))

rename-assm²-crossed-left∀∀ᵢ :
  ∀ {Φ a} →
  a ∈ ∀ᵢᶜ Φ →
  rename-assm²ᵢ (extᵗ suc) suc a ∈ swapRight∀∀ᵢ Φ
rename-assm²-crossed-left∀∀ᵢ {a = a} a∈ =
  subst (_∈ swapRight∀∀ᵢ _)
    (trans
      (rename-assm²-composeᵢ suc suc swap01ᵢ (λ X → X) a)
      (rename-assm²-congᵢ swap01ᵢ-after-suc (λ X → refl)))
    (rename-assm²-swapLeft∀∀ᵢ (rename-assm²-∀ᵢ a∈))

renameᵗ-swap01-double-liftᵢ :
  ∀ B →
  renameᵗ swap01ᵢ (⇑ᵗ (⇑ᵗ B)) ≡ ⇑ᵗ (⇑ᵗ B)
renameᵗ-swap01-double-liftᵢ B =
  trans
    (cong (renameᵗ swap01ᵢ) (renameᵗ-compose suc suc B))
    (trans
      (renameᵗ-compose (λ X → suc (suc X)) swap01ᵢ B)
      (trans
        (rename-cong (λ X → refl) B)
        (sym (renameᵗ-compose suc suc B))))

rename-assm²-crossed-double∀∀ᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → suc (suc X)) (λ X → suc (suc X)) a
    ∈ swapRight∀∀ᵢ Φ
rename-assm²-crossed-double∀∀ᵢ {a = X ˣ⊑★} a∈ =
  rename-assm²-swapRight∀∀ᵢ
    (rename-assm²-∀ᵢ (rename-assm²-∀ᵢ a∈))
rename-assm²-crossed-double∀∀ᵢ {a = X ˣ⊑ˣ Y} a∈ =
  rename-assm²-swapRight∀∀ᵢ
    (rename-assm²-∀ᵢ (rename-assm²-∀ᵢ a∈))

⊑-crossed-body-lift∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ A ⊑ renameᵗ (extᵗ suc) B ⊣ suc (suc Δᴿ)
⊑-crossed-body-lift∀∀ᵢ p =
  ⊑-renameᵗ²ᵢ
    rename-assm²-crossed-right∀∀ᵢ
    (λ X<Δ → s<s X<Δ)
    (TyRenameWf-ext (λ X<Δ → s<s X<Δ)) p

⊑-crossed-left-body-lift∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ renameᵗ (extᵗ suc) A ⊑ ⇑ᵗ B ⊣ suc (suc Δᴿ)
⊑-crossed-left-body-lift∀∀ᵢ p =
  ⊑-renameᵗ²ᵢ
    rename-assm²-crossed-left∀∀ᵢ
    (TyRenameWf-ext (λ X<Δ → s<s X<Δ))
    (λ X<Δ → s<s X<Δ) p

⊑-crossed-double-lift∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ (⇑ᵗ A) ⊑ ⇑ᵗ (⇑ᵗ B) ⊣ suc (suc Δᴿ)
⊑-crossed-double-lift∀∀ᵢ {A = A} {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ ⇑ᵗ (⇑ᵗ A) ⊑ T ⊣ _)
    (sym (renameᵗ-compose suc suc B))
    (subst
      (λ S → _ ∣ _ ⊢ S ⊑
        renameᵗ (λ X → suc (suc X)) B ⊣ _)
      (sym (renameᵗ-compose suc suc A))
      (⊑-renameᵗ²ᵢ
        rename-assm²-crossed-double∀∀ᵢ
        (λ X<Δ → s<s (s<s X<Δ))
        (λ X<Δ → s<s (s<s X<Δ)) p))

rename-assm²-swap∀∀ᵢ :
  ∀ {Φ a} →
  a ∈ ∀ᵢᶜ (∀ᵢᶜ Φ) →
  rename-assm²ᵢ swap01ᵢ swap01ᵢ a ∈ ∀ᵢᶜ (∀ᵢᶜ Φ)
rename-assm²-swap∀∀ᵢ {a = zero ˣ⊑★} =
  λ { (here ()) ; (there a∈) → ⊥-elim (no-⇑ᵢ-zero-star a∈) }
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑★} (here ())
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-∀ctx-zero-starᵢ (un⇑ᵢ-★∈ a∈))
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑★} (here ())
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑★} (there a∈) =
  there a∈
rename-assm²-swap∀∀ᵢ {a = zero ˣ⊑ˣ zero} (here refl) =
  there (⇑ᵢ-ˣ∈ (here refl))
rename-assm²-swap∀∀ᵢ {a = zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-swap∀∀ᵢ {a = zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-swap∀∀ᵢ {a = zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑ˣ zero} (here ())
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑ˣ suc zero} (here ())
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑ˣ suc zero} (there a∈) =
  here refl
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑ˣ suc (suc Y)} (here ())
rename-assm²-swap∀∀ᵢ {a = suc zero ˣ⊑ˣ suc (suc Y)}
    (there a∈) =
  ⊥-elim (no-∀ctx-zero-leftᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑ˣ zero} (here ())
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑ˣ zero}
    (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑ˣ suc zero} (here ())
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑ˣ suc zero}
    (there a∈) =
  ⊥-elim (no-∀ctx-zero-rightᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑ˣ suc (suc Y)}
    (here ())
rename-assm²-swap∀∀ᵢ {a = suc (suc X) ˣ⊑ˣ suc (suc Y)}
    (there a∈) =
  there a∈

⊑-swap01∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (∀ᵢᶜ Φ)
    ∣ suc (suc Δᴸ) ⊢ A ⊑ B ⊣ suc (suc Δᴿ) →
  ∀ᵢᶜ (∀ᵢᶜ Φ)
    ∣ suc (suc Δᴸ)
    ⊢ renameᵗ swap01ᵢ A ⊑ renameᵗ swap01ᵢ B
    ⊣ suc (suc Δᴿ)
⊑-swap01∀∀ᵢ =
  ⊑-renameᵗ²ᵢ
    {ρ = swap01ᵢ}
    {σ = swap01ᵢ}
    rename-assm²-swap∀∀ᵢ
    swap01-pres-<ᵢ
    swap01-pres-<ᵢ

⊑-swap01∀∀-under∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ A ⊑ B ⊣ suc (suc (suc Δᴿ)) →
  ∀ᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ renameᵗ (extᵗ swap01ᵢ) A ⊑ renameᵗ (extᵗ swap01ᵢ) B
    ⊣ suc (suc (suc Δᴿ))
⊑-swap01∀∀-under∀ᵢ =
  ⊑-renameᵗ²ᵢ
    {ρ = extᵗ swap01ᵢ}
    {σ = extᵗ swap01ᵢ}
    (rename-assm²-⇑ᵢ rename-assm²-swap∀∀ᵢ)
    (TyRenameWf-ext swap01-pres-<ᵢ)
    (TyRenameWf-ext swap01-pres-<ᵢ)

⊑-swap01∀∀-underνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  νᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ A ⊑ B ⊣ suc (suc Δᴿ) →
  νᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ renameᵗ (extᵗ swap01ᵢ) A ⊑ renameᵗ swap01ᵢ B
    ⊣ suc (suc Δᴿ)
⊑-swap01∀∀-underνᵢ =
  ⊑-renameᵗ²ᵢ
    {ρ = extᵗ swap01ᵢ}
    {σ = swap01ᵢ}
    (rename-assm²-⇑ᴸᵢ rename-assm²-swap∀∀ᵢ)
    (TyRenameWf-ext swap01-pres-<ᵢ)
    swap01-pres-<ᵢ

⊑-unswap01∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (∀ᵢᶜ Φ)
    ∣ suc (suc Δᴸ)
    ⊢ renameᵗ swap01ᵢ A ⊑ renameᵗ swap01ᵢ B
    ⊣ suc (suc Δᴿ) →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ) ⊢ A ⊑ B ⊣ suc (suc Δᴿ)
⊑-unswap01∀∀ᵢ {A = A} {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ B ⊣ _)
    (renameᵗ-swap01-involutiveᵢ A)
    (subst
      (λ T →
        _ ∣ _ ⊢ renameᵗ swap01ᵢ (renameᵗ swap01ᵢ A) ⊑ T ⊣ _)
      (renameᵗ-swap01-involutiveᵢ B)
      (⊑-swap01∀∀ᵢ p))

⊑-unswap01∀∀-under∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ renameᵗ (extᵗ swap01ᵢ) A
      ⊑ renameᵗ (extᵗ swap01ᵢ) B
    ⊣ suc (suc (suc Δᴿ)) →
  ∀ᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ A ⊑ B ⊣ suc (suc (suc Δᴿ))
⊑-unswap01∀∀-under∀ᵢ {A = A} {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ B ⊣ _)
    (renameᵗ-ext-swap01-involutiveᵢ A)
    (subst
      (λ T →
        _ ∣ _ ⊢ renameᵗ (extᵗ swap01ᵢ)
          (renameᵗ (extᵗ swap01ᵢ) A) ⊑ T ⊣ _)
      (renameᵗ-ext-swap01-involutiveᵢ B)
      (⊑-swap01∀∀-under∀ᵢ p))

⊑-unswap01∀∀-underνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  νᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ renameᵗ (extᵗ swap01ᵢ) A ⊑ renameᵗ swap01ᵢ B
    ⊣ suc (suc Δᴿ) →
  νᵢᶜ (∀ᵢᶜ (∀ᵢᶜ Φ))
    ∣ suc (suc (suc Δᴸ))
    ⊢ A ⊑ B ⊣ suc (suc Δᴿ)
⊑-unswap01∀∀-underνᵢ {A = A} {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ B ⊣ _)
    (renameᵗ-ext-swap01-involutiveᵢ A)
    (subst
      (λ T →
        _ ∣ _ ⊢ renameᵗ (extᵗ swap01ᵢ)
          (renameᵗ (extᵗ swap01ᵢ) A) ⊑ T ⊣ _)
      (renameᵗ-swap01-involutiveᵢ B)
      (⊑-swap01∀∀-underνᵢ p))

swapAtᵢ : TyVar → Renameᵗ
swapAtᵢ zero = swap01ᵢ
swapAtᵢ (suc k) zero = zero
swapAtᵢ (suc k) (suc X) = suc (swapAtᵢ k X)

swapAt-sucᵢ : ∀ k → swapAtᵢ k (suc k) ≡ k
swapAt-sucᵢ zero = refl
swapAt-sucᵢ (suc k) = cong suc (swapAt-sucᵢ k)

swapAt-ext-renameᵢ :
  ∀ k A →
  renameᵗ (extᵗ (swapAtᵢ k)) A ≡ renameᵗ (swapAtᵢ (suc k)) A
swapAt-ext-renameᵢ k A =
  rename-cong
    {ρ = extᵗ (swapAtᵢ k)}
    {ρ′ = swapAtᵢ (suc k)}
    (λ { zero → refl ; (suc X) → refl })
    A

occurs-swapAt-leftᵢ :
  ∀ k A →
  occurs (suc k) A ≡ true →
  occurs k (renameᵗ (swapAtᵢ k) A) ≡ true
occurs-swapAt-leftᵢ k (＇ Y) occ with suc k ≟ Y
occurs-swapAt-leftᵢ k (＇ .(suc k)) occ | yes refl
    rewrite swapAt-sucᵢ k =
  occurs-var-reflᵢ k
occurs-swapAt-leftᵢ k (＇ Y) () | no neq
occurs-swapAt-leftᵢ k (‵ ι) ()
occurs-swapAt-leftᵢ k ★ ()
occurs-swapAt-leftᵢ k (A ⇒ B) occ with occurs (suc k) A in occA
occurs-swapAt-leftᵢ k (A ⇒ B) occ | true =
  ∨-true-leftᵢ (occurs-swapAt-leftᵢ k A occA)
occurs-swapAt-leftᵢ k (A ⇒ B) occ | false =
  ∨-true-rightᵢ (occurs-swapAt-leftᵢ k B occ)
occurs-swapAt-leftᵢ k (`∀ A) occ
    rewrite swapAt-ext-renameᵢ k A =
  occurs-swapAt-leftᵢ (suc k) A occ

occurs-swap01-leftᵢ :
  ∀ A →
  occurs (suc zero) A ≡ true →
  occurs zero (renameᵗ swap01ᵢ A) ≡ true
occurs-swap01-leftᵢ = occurs-swapAt-leftᵢ zero

removeAt-swapAt-varᵢ :
  ∀ k X →
  occurs k (＇ X) ≡ false →
  removeAtᵗ k (swapAtᵢ (suc k) X) ≡ swapAtᵢ k (removeAtᵗ k X)
removeAt-swapAt-varᵢ zero zero ()
removeAt-swapAt-varᵢ zero (suc zero) occ = refl
removeAt-swapAt-varᵢ zero (suc (suc X)) occ = refl
removeAt-swapAt-varᵢ (suc k) zero occ = refl
removeAt-swapAt-varᵢ (suc k) (suc X) occ =
  cong suc
    (removeAt-swapAt-varᵢ k X (occurs-suc-falseᵢ k X occ))

removeAt-swapAt-freshᵢ :
  ∀ k A →
  occurs k A ≡ false →
  renameᵗ (removeAtᵗ k) (renameᵗ (swapAtᵢ (suc k)) A)
  ≡ renameᵗ (swapAtᵢ k) (renameᵗ (removeAtᵗ k) A)
removeAt-swapAt-freshᵢ k (＇ X) occ =
  cong ＇_ (removeAt-swapAt-varᵢ k X occ)
removeAt-swapAt-freshᵢ k (‵ ι) occ = refl
removeAt-swapAt-freshᵢ k ★ occ = refl
removeAt-swapAt-freshᵢ k (A ⇒ B) occ =
  cong₂ _⇒_
    (removeAt-swapAt-freshᵢ k A (∨-false-leftᵢ occ))
    (removeAt-swapAt-freshᵢ k B (∨-false-rightᵢ occ))
removeAt-swapAt-freshᵢ k (`∀ A) occ =
  cong `∀
    (trans
      (cong (renameᵗ (removeAtᵗ (suc k)))
        (swapAt-ext-renameᵢ (suc k) A))
      (trans
        (removeAt-swapAt-freshᵢ (suc k) A occ)
        (sym
          (swapAt-ext-renameᵢ k
            (renameᵗ (removeAtᵗ (suc k)) A)))))

unν-suc-starᵢ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ νᵢᶜ Φ →
  (X ˣ⊑★) ∈ Φ
unν-suc-starᵢ (here ())
unν-suc-starᵢ (there x∈) = un⇑ᴸᵢ-★∈ x∈

unν-suc-varᵢ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ Y) ∈ νᵢᶜ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
unν-suc-varᵢ (here ())
unν-suc-varᵢ (there x∈) = un⇑ᴸᵢ-ˣ∈ x∈

rename-assm²-∀ν-to-ν∀ᵢ :
  ∀ {Φ a} →
  a ∈ ∀ᵢᶜ (νᵢᶜ Φ) →
  rename-assm²ᵢ swap01ᵢ (λ X → X) a ∈ νᵢᶜ (∀ᵢᶜ Φ)
rename-assm²-∀ν-to-ν∀ᵢ {a = zero ˣ⊑★} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-star a∈)
rename-assm²-∀ν-to-ν∀ᵢ {a = zero ˣ⊑ˣ zero} (here refl) =
  there (⇑ᴸᵢ-ˣ∈ (here refl))
rename-assm²-∀ν-to-ν∀ᵢ {a = zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-∀ν-to-ν∀ᵢ {a = zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-∀ν-to-ν∀ᵢ {a = suc zero ˣ⊑★} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = suc zero ˣ⊑★} (there a∈) =
  here refl
rename-assm²-∀ν-to-ν∀ᵢ {Φ = Φ} {a = suc (suc X) ˣ⊑★}
    (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = suc (suc X) ˣ⊑★} (there a∈) =
  there
    (⇑ᴸᵢ-★∈
      (there (⇑ᵢ-★∈ (unν-suc-starᵢ (un⇑ᵢ-★∈ a∈)))))
rename-assm²-∀ν-to-ν∀ᵢ {a = suc zero ˣ⊑ˣ zero} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = suc zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-∀ν-to-ν∀ᵢ {a = suc zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = suc zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-νctx-zero-varᵢ (un⇑ᵢ-ˣ∈ a∈))
rename-assm²-∀ν-to-ν∀ᵢ {a = suc (suc X) ˣ⊑ˣ zero} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = suc (suc X) ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-∀ν-to-ν∀ᵢ {a = suc (suc X) ˣ⊑ˣ suc Y} (here ())
rename-assm²-∀ν-to-ν∀ᵢ {a = suc (suc X) ˣ⊑ˣ suc Y} (there a∈) =
  there
    (⇑ᴸᵢ-ˣ∈
      (there (⇑ᵢ-ˣ∈ (unν-suc-varᵢ (un⇑ᵢ-ˣ∈ a∈)))))

⊑-∀ν-to-ν∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ (νᵢᶜ Φ) ∣ suc (suc Δᴸ) ⊢ A ⊑ B ⊣ suc Δᴿ →
  νᵢᶜ (∀ᵢᶜ Φ)
    ∣ suc (suc Δᴸ) ⊢ renameᵗ swap01ᵢ A ⊑ B ⊣ suc Δᴿ
⊑-∀ν-to-ν∀ᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} p =
  subst
    (λ B′ →
      νᵢᶜ (∀ᵢᶜ Φ)
        ∣ suc (suc Δᴸ) ⊢ renameᵗ swap01ᵢ A ⊑ B′ ⊣ suc Δᴿ)
    (renameᵗ-id B)
    (⊑-renameᵗ²ᵢ
      {ρ = swap01ᵢ}
      {σ = λ X → X}
      rename-assm²-∀ν-to-ν∀ᵢ
      swap01-pres-<ᵢ
      (λ Y<Δ → Y<Δ)
      p)

rename-assm²-ν∀-to-∀νᵢ :
  ∀ {Φ a} →
  a ∈ νᵢᶜ (∀ᵢᶜ Φ) →
  rename-assm²ᵢ swap01ᵢ (λ X → X) a ∈ ∀ᵢᶜ (νᵢᶜ Φ)
rename-assm²-ν∀-to-∀νᵢ {a = zero ˣ⊑★} (here refl) =
  there (⇑ᵢ-★∈ (here refl))
rename-assm²-ν∀-to-∀νᵢ {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑★} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-∀ctx-zero-starᵢ (un⇑ᴸᵢ-★∈ a∈))
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑★} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑★} (there a∈)
    with un⇑ᴸᵢ-★∈ a∈
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑★} (there a∈)
    | here ()
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑★} (there a∈)
    | there x∈ =
  there
    (⇑ᵢ-★∈
      (there (⇑ᴸᵢ-★∈ (un⇑ᵢ-★∈ x∈))))
rename-assm²-ν∀-to-∀νᵢ {a = zero ˣ⊑ˣ zero} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
rename-assm²-ν∀-to-∀νᵢ {a = zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ zero} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ zero} (there a∈)
    with un⇑ᴸᵢ-ˣ∈ a∈
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ zero} (there a∈)
    | here refl = here refl
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ zero} (there a∈)
    | there x∈ = ⊥-elim (no-⇑ᵢ-zero-left x∈)
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ suc Y} (there a∈)
    with un⇑ᴸᵢ-ˣ∈ a∈
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ suc Y} (there a∈)
    | here ()
rename-assm²-ν∀-to-∀νᵢ {a = suc zero ˣ⊑ˣ suc Y} (there a∈)
    | there x∈ = ⊥-elim (no-⇑ᵢ-zero-left x∈)
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑ˣ zero} (here ())
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑ˣ zero} (there a∈)
    with un⇑ᴸᵢ-ˣ∈ a∈
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑ˣ zero} (there a∈)
    | here ()
rename-assm²-ν∀-to-∀νᵢ {a = suc (suc X) ˣ⊑ˣ zero} (there a∈)
    | there x∈ = ⊥-elim (no-⇑ᵢ-zero-right x∈)
rename-assm²-ν∀-to-∀νᵢ
    {a = suc (suc X) ˣ⊑ˣ suc Y} (here ())
rename-assm²-ν∀-to-∀νᵢ
    {a = suc (suc X) ˣ⊑ˣ suc Y} (there a∈)
    with un⇑ᴸᵢ-ˣ∈ a∈
rename-assm²-ν∀-to-∀νᵢ
    {a = suc (suc X) ˣ⊑ˣ suc Y} (there a∈)
    | here ()
rename-assm²-ν∀-to-∀νᵢ
    {a = suc (suc X) ˣ⊑ˣ suc Y} (there a∈)
    | there x∈ =
  there
    (⇑ᵢ-ˣ∈
      (there (⇑ᴸᵢ-ˣ∈ (un⇑ᵢ-ˣ∈ x∈))))

⊑-ν∀-to-∀νᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  νᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ) ⊢ A ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ (νᵢᶜ Φ)
    ∣ suc (suc Δᴸ) ⊢ renameᵗ swap01ᵢ A ⊑ B ⊣ suc Δᴿ
⊑-ν∀-to-∀νᵢ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  subst
    (λ B′ →
      ∀ᵢᶜ (νᵢᶜ Φ)
        ∣ suc (suc Δᴸ) ⊢ renameᵗ swap01ᵢ A ⊑ B′ ⊣ suc Δᴿ)
    (renameᵗ-id B)
    (⊑-renameᵗ²ᵢ
      {ρ = swap01ᵢ}
      {σ = λ X → X}
      rename-assm²-ν∀-to-∀νᵢ
      swap01-pres-<ᵢ
      (λ Y<Δ → Y<Δ)
      p)

nonVar-swap01-from-forallᵢ :
  ∀ {Δ C} →
  occurs zero (`∀ C) ≡ true →
  idᵢ (suc Δ) ∣ suc Δ ⊢
    `∀ C ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δ →
  NonVar (renameᵗ swap01ᵢ C)
nonVar-swap01-from-forallᵢ {C = ＇ zero} () p
nonVar-swap01-from-forallᵢ {C = ＇ (suc zero)} occ
    (∀ⁱ (idˣ x∈ X<Δᴸ Y<Δᴿ))
    with idᵢ-var-identity x∈
nonVar-swap01-from-forallᵢ {C = ＇ (suc zero)} occ
    (∀ⁱ (idˣ x∈ X<Δᴸ Y<Δᴿ)) | ()
nonVar-swap01-from-forallᵢ {C = ＇ (suc zero)} occ
    (ν () occC p)
nonVar-swap01-from-forallᵢ {C = ＇ (suc (suc X))} () p
nonVar-swap01-from-forallᵢ {C = ‵ ι} () p
nonVar-swap01-from-forallᵢ {C = ★} () p
nonVar-swap01-from-forallᵢ {C = A ⇒ B} occ p = nonvar-fun
nonVar-swap01-from-forallᵢ {C = `∀ A} occ p = nonvar-all

νlower-∀shape-body-lowerᵢ :
  ∀ {Φ Δᶜ C D} →
  occurs zero (`∀ C) ≡ true →
  ∀ᵢᶜ (νᵢᶜ Φ) ∣ suc (suc Δᶜ) ⊢ C ⊑ D ⊣ suc Δᶜ →
  idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢
    `∀ C ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ →
  ∀ᵢᶜ Φ ∣ suc Δᶜ
    ⊢ `∀ (renameᵗ swap01ᵢ C) ⊑ D ⊣ suc Δᶜ
νlower-∀shape-body-lowerᵢ {C = C} occC C⊑D body-coh =
  ν (nonVar-swap01-from-forallᵢ occC body-coh)
    (occurs-swap01-leftᵢ C occC) (⊑-∀ν-to-ν∀ᵢ C⊑D)

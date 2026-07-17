module proof.MaximalLowerBoundsWf where

-- File Charter:
--   * Indexed maximal-lower-bound proof boundary for GTSF consistency.
--   * Uses `ImprecisionWf` directly, so polymorphic `ν` cases have the
--     left-only context shape required by the Nu-term imprecision relation.
--   * Does not assume greatest lower bounds exist.  The application-cast proof
--     should consume a separate coherence theorem for the canonical maximal
--     lower-bound selector.

open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc)
open import Data.Nat.Base using (z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (¬_; no; yes)

open import Types
import Imprecision as Imp
open import Imprecision using (idᵢ)
open import ImprecisionWf
import proof.ImprecisionProperties as ImpProps
open import proof.ImprecisionProperties using
  ( idᵢ-lookup
  ; idᵢ-var-identity
  ; idᵢ-no-star
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
open import proof.TypeProperties using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; extNᵗ
  ; occurs-raise-fresh
  ; occurs-suc-var
  ; occurs-zero-rename-ext
  ; rename-cong
  ; rename-raise-ext
  ; renameᵗ-compose
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-id
  ; renameᵗ-single-suc-cancel
  ; singleRenameᵗ-Wf-<
  )

∨-true-leftᵢ : ∀ {b c} → b ≡ true → b ∨ c ≡ true
∨-true-leftᵢ {b = true} refl = refl
∨-true-leftᵢ {b = false} ()

∨-true-rightᵢ : ∀ {b c} → c ≡ true → b ∨ c ≡ true
∨-true-rightᵢ {b = false} refl = refl
∨-true-rightᵢ {b = true} _ = refl

∨-false-leftᵢ : ∀ {b c} → b ∨ c ≡ false → b ≡ false
∨-false-leftᵢ {b = false} refl = refl
∨-false-leftᵢ {b = true} ()

∨-false-rightᵢ : ∀ {b c} → b ∨ c ≡ false → c ≡ false
∨-false-rightᵢ {b = false} refl = refl
∨-false-rightᵢ {b = true} ()

∨-falseᵢ : ∀ {b c} → b ≡ false → c ≡ false → b ∨ c ≡ false
∨-falseᵢ {b = false} {c = false} refl refl = refl
∨-falseᵢ {b = false} {c = true} refl ()
∨-falseᵢ {b = true} {c = false} ()
∨-falseᵢ {b = true} {c = true} ()

false≠trueᵢ : false ≡ true → ⊥
false≠trueᵢ ()

∀-injectiveᵢ : ∀ {A B} → `∀ A ≡ `∀ B → A ≡ B
∀-injectiveᵢ refl = refl

non∀-∀-eqᵢ : ∀ {A B} → Non∀ A → A ≡ `∀ B → ⊥
non∀-∀-eqᵢ non∀-＇ ()
non∀-∀-eqᵢ non∀-‵ ()
non∀-∀-eqᵢ non∀-★ ()
non∀-∀-eqᵢ non∀-⇒ ()

occurs-var-reflᵢ : ∀ X → occurs X (＇ X) ≡ true
occurs-var-reflᵢ X with X ≟ X
occurs-var-reflᵢ X | yes refl = refl
occurs-var-reflᵢ X | no X≢X = ⊥-elim (X≢X refl)

occurs-suc-falseᵢ :
  ∀ X Y →
  occurs (suc X) (＇ suc Y) ≡ false →
  occurs X (＇ Y) ≡ false
occurs-suc-falseᵢ X Y occ =
  trans (occurs-suc-var X Y) occ

removeAtᵗ : TyVar → Renameᵗ
removeAtᵗ k = extNᵗ k (singleRenameᵗ zero)

removeAt-raiseᵢ : ∀ k X → removeAtᵗ k (raiseVarFrom k X) ≡ X
removeAt-raiseᵢ zero X = refl
removeAt-raiseᵢ (suc k) zero = refl
removeAt-raiseᵢ (suc k) (suc X) =
  cong suc (removeAt-raiseᵢ k X)

raise-removeAt-varᵢ :
  ∀ k X →
  occurs k (＇ X) ≡ false →
  raiseVarFrom k (removeAtᵗ k X) ≡ X
raise-removeAt-varᵢ zero zero ()
raise-removeAt-varᵢ zero (suc X) occ = refl
raise-removeAt-varᵢ (suc k) zero occ = refl
raise-removeAt-varᵢ (suc k) (suc X) occ =
  cong suc (raise-removeAt-varᵢ k X (occurs-suc-falseᵢ k X occ))

raise-removeAt-freshᵢ :
  ∀ k A →
  occurs k A ≡ false →
  renameᵗ (raiseVarFrom k) (renameᵗ (removeAtᵗ k) A) ≡ A
raise-removeAt-freshᵢ k (＇ X) occ =
  cong ＇_ (raise-removeAt-varᵢ k X occ)
raise-removeAt-freshᵢ k (‵ ι) occ = refl
raise-removeAt-freshᵢ k ★ occ = refl
raise-removeAt-freshᵢ k (A ⇒ B) occ =
  cong₂ _⇒_
    (raise-removeAt-freshᵢ k A (∨-false-leftᵢ occ))
    (raise-removeAt-freshᵢ k B (∨-false-rightᵢ occ))
raise-removeAt-freshᵢ k (`∀ A) occ
    rewrite rename-raise-ext k (renameᵗ (removeAtᵗ (suc k)) A)
          | raise-removeAt-freshᵢ (suc k) A occ =
  refl

occurs-removeAt-raiseᵢ :
  ∀ k X A →
  occurs (raiseVarFrom k X) A ≡ true →
  occurs X (renameᵗ (removeAtᵗ k) A) ≡ true
occurs-removeAt-raiseᵢ k X (＇_ Y) occ
    with raiseVarFrom k X ≟ Y
occurs-removeAt-raiseᵢ k X (＇_ Y) occ | yes eq
    rewrite sym eq | removeAt-raiseᵢ k X =
  occurs-var-reflᵢ X
occurs-removeAt-raiseᵢ k X (＇_ Y) () | no neq
occurs-removeAt-raiseᵢ k X (‵ ι) ()
occurs-removeAt-raiseᵢ k X ★ ()
occurs-removeAt-raiseᵢ k X (A ⇒ B) occ
    with occurs (raiseVarFrom k X) A in occA
occurs-removeAt-raiseᵢ k X (A ⇒ B) occ | true =
  ∨-true-leftᵢ (occurs-removeAt-raiseᵢ k X A occA)
occurs-removeAt-raiseᵢ k X (A ⇒ B) occ | false =
  ∨-true-rightᵢ (occurs-removeAt-raiseᵢ k X B occ)
occurs-removeAt-raiseᵢ k X (`∀ A) occ =
  occurs-removeAt-raiseᵢ (suc k) (suc X) A occ

∀ᵢᶜ : ImpCtx → ImpCtx
∀ᵢᶜ Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ

νᵢᶜ : ImpCtx → ImpCtx
νᵢᶜ Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ

⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-ˣ∈ {Φ = []} ()
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ x∈)
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ x∈)

⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-★∈ {Φ = []} ()
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-★∈ x∈)
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-★∈ x∈)

un⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᴸᵢ-★∈ {Φ = []} ()
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)

no-⇑ᴸᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-star {Φ = []} ()
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈

no-νctx-zero-varᵢ :
  ∀ {Φ X} →
  (zero ˣ⊑ˣ X) ∈ νᵢᶜ Φ →
  ⊥
no-νctx-zero-varᵢ (here ())
no-νctx-zero-varᵢ (there x∈) = no-⇑ᴸᵢ-zero-left x∈

no-∀ctx-zero-starᵢ :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ∀ᵢᶜ Φ →
  ⊥
no-∀ctx-zero-starᵢ (here ())
no-∀ctx-zero-starᵢ (there x∈) = no-⇑ᵢ-zero-star x∈

no-∀ctx-zero-leftᵢ :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ suc Y) ∈ ∀ᵢᶜ Φ →
  ⊥
no-∀ctx-zero-leftᵢ (here ())
no-∀ctx-zero-leftᵢ (there x∈) = no-⇑ᵢ-zero-left x∈

no-∀ctx-zero-rightᵢ :
  ∀ {Φ X} →
  (suc X ˣ⊑ˣ zero) ∈ ∀ᵢᶜ Φ →
  ⊥
no-∀ctx-zero-rightᵢ (here ())
no-∀ctx-zero-rightᵢ (there x∈) = no-⇑ᵢ-zero-right x∈

no-occurs-base-lowerᵢ :
  ∀ {Φ Δᴸ Δᴿ A ι} →
  occurs zero A ≡ true →
  Φ ∣ Δᴸ ⊢ A ⊑ ‵ ι ⊣ Δᴿ →
  ⊥
no-occurs-base-lowerᵢ () idι
no-occurs-base-lowerᵢ occ (ν occA p) =
  no-occurs-base-lowerᵢ occA p

no-occurs-var-lower-νctxᵢ :
  ∀ {Φ Δᴸ Δᴿ A X} →
  occurs zero A ≡ true →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ ＇ X ⊣ Δᴿ →
  ⊥
no-occurs-var-lower-νctxᵢ {A = ＇ zero} occ (idˣ x∈ _ _) =
  no-νctx-zero-varᵢ x∈
no-occurs-var-lower-νctxᵢ {A = ＇ suc X} () (idˣ x∈ _ _)
no-occurs-var-lower-νctxᵢ occ (ν occA p) =
  no-occurs-var-lower-νctxᵢ occA p

rename-assm²ᵢ : Renameᵗ → Renameᵗ → ImpAssm → ImpAssm
rename-assm²ᵢ ρ σ (X ˣ⊑★) = ρ X ˣ⊑★
rename-assm²ᵢ ρ σ (X ˣ⊑ˣ Y) = ρ X ˣ⊑ˣ σ Y

rename-assm²-⇑ᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ ∀ᵢᶜ Φ →
  rename-assm²ᵢ (extᵗ ρ) (extᵗ σ) a ∈ ∀ᵢᶜ Ψ
rename-assm²-⇑ᵢ h {a = zero ˣ⊑★} (here ())
rename-assm²-⇑ᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-star a∈)
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑★} (here ())
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᵢ-★∈ (h (un⇑ᵢ-★∈ a∈)))
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ zero} (here refl) = here refl
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ suc Y} (here ())
rename-assm²-⇑ᵢ h {a = zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (here ())
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (here ())
rename-assm²-⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (there a∈) =
  there (⇑ᵢ-ˣ∈ (h (un⇑ᵢ-ˣ∈ a∈)))

rename-assm²-⇑ᴸᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ νᵢᶜ Φ →
  rename-assm²ᵢ (extᵗ ρ) σ a ∈ νᵢᶜ Ψ
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑★} (here refl) = here refl
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑★} (here ())
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᴸᵢ-★∈ (h (un⇑ᴸᵢ-★∈ a∈)))
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸᵢ h {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸᵢ h {a = suc X ˣ⊑ˣ Y} (there a∈) =
  there (⇑ᴸᵢ-ˣ∈ (h (un⇑ᴸᵢ-ˣ∈ a∈)))

rename-assm²-★⇑ᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ (zero ˣ⊑★) ∷ ⇑ᵢ Φ →
  rename-assm²ᵢ (extᵗ ρ) (extᵗ σ) a ∈ (zero ˣ⊑★) ∷ ⇑ᵢ Ψ
rename-assm²-★⇑ᵢ h {a = zero ˣ⊑★} (here refl) = here refl
rename-assm²-★⇑ᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-star a∈)
rename-assm²-★⇑ᵢ h {a = suc X ˣ⊑★} (here ())
rename-assm²-★⇑ᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᵢ-★∈ (h (un⇑ᵢ-★∈ a∈)))
rename-assm²-★⇑ᵢ h {a = zero ˣ⊑ˣ Y} (here ())
rename-assm²-★⇑ᵢ h {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
rename-assm²-★⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (here ())
rename-assm²-★⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
rename-assm²-★⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (here ())
rename-assm²-★⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (there a∈) =
  there (⇑ᵢ-ˣ∈ (h (un⇑ᵢ-ˣ∈ a∈)))

⊑-renameᵗ²ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρ σ A B} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ ρ σ a ∈ Ψ) →
  TyRenameWf Δᴸ Δᴸ′ ρ →
  TyRenameWf Δᴿ Δᴿ′ σ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ′ ⊢ renameᵗ ρ A ⊑ renameᵗ σ B ⊣ Δᴿ′
⊑-renameᵗ²ᵢ h hρ hσ id★ = id★
⊑-renameᵗ²ᵢ h hρ hσ (idˣ x∈ X<Δᴸ Y<Δᴿ) =
  idˣ (h x∈) (hρ X<Δᴸ) (hσ Y<Δᴿ)
⊑-renameᵗ²ᵢ h hρ hσ idι = idι
⊑-renameᵗ²ᵢ h hρ hσ (p ↦ q) =
  ⊑-renameᵗ²ᵢ h hρ hσ p ↦ ⊑-renameᵗ²ᵢ h hρ hσ q
⊑-renameᵗ²ᵢ {ρ = ρ} {σ = σ} h hρ hσ (∀ⁱ p) =
  ∀ⁱ (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ h)
        (TyRenameWf-ext hρ)
        (TyRenameWf-ext hσ)
        p)
⊑-renameᵗ²ᵢ h hρ hσ (tag ι) = tag ι
⊑-renameᵗ²ᵢ h hρ hσ (tag_⇛_ p q) =
  tag_⇛_ (⊑-renameᵗ²ᵢ h hρ hσ p) (⊑-renameᵗ²ᵢ h hρ hσ q)
⊑-renameᵗ²ᵢ h hρ hσ (tagˣ x∈ X<Δᴸ) =
  tagˣ (h x∈) (hρ X<Δᴸ)
⊑-renameᵗ²ᵢ {ρ = ρ} h hρ hσ (ν {A = A} occA p) =
  ν (trans (occurs-zero-rename-ext ρ A) occA)
    (⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ h)
      (TyRenameWf-ext hρ)
      hσ
      p)

rename-assm²-source-νᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ suc (λ X → X) a ∈ νᵢᶜ Φ
rename-assm²-source-νᵢ {a = X ˣ⊑★} x∈ =
  there (⇑ᴸᵢ-★∈ x∈)
rename-assm²-source-νᵢ {a = X ˣ⊑ˣ Y} x∈ =
  there (⇑ᴸᵢ-ˣ∈ x∈)

rename-assm²-∀ᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ suc suc a ∈ ∀ᵢᶜ Φ
rename-assm²-∀ᵢ {a = X ˣ⊑★} x∈ = there (⇑ᵢ-★∈ x∈)
rename-assm²-∀ᵢ {a = X ˣ⊑ˣ Y} x∈ = there (⇑ᵢ-ˣ∈ x∈)

⊑-lift∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
⊑-lift∀ᵢ =
  ⊑-renameᵗ²ᵢ
    {ρ = suc}
    {σ = suc}
    rename-assm²-∀ᵢ
    (λ X<Δ → s<s X<Δ)
    (λ Y<Δ → s<s Y<Δ)

rename-assm²-open-shiftᵢ :
  ∀ {Φ a α β} →
  a ∈ ⇑ᵢ Φ →
  rename-assm²ᵢ (singleRenameᵗ α) (singleRenameᵗ β) a ∈ Φ
rename-assm²-open-shiftᵢ {Φ = []} ()
rename-assm²-open-shiftᵢ {Φ = (X ˣ⊑★) ∷ Φ} (here refl) =
  here refl
rename-assm²-open-shiftᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl) =
  here refl
rename-assm²-open-shiftᵢ {Φ = (X ˣ⊑★) ∷ Φ} (there a∈) =
  there (rename-assm²-open-shiftᵢ a∈)
rename-assm²-open-shiftᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (there a∈) =
  there (rename-assm²-open-shiftᵢ a∈)

rename-assm²-open∀ᵢ :
  ∀ {Φ a α β} →
  (α ˣ⊑ˣ β) ∈ Φ →
  a ∈ ∀ᵢᶜ Φ →
  rename-assm²ᵢ (singleRenameᵗ α) (singleRenameᵗ β) a ∈ Φ
rename-assm²-open∀ᵢ α⊑β (here refl) = α⊑β
rename-assm²-open∀ᵢ α⊑β (there a∈) =
  rename-assm²-open-shiftᵢ a∈

⊑-open∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B α β} →
  (α ˣ⊑ˣ β) ∈ Φ →
  α < Δᴸ →
  β < Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ α ]ᴿ ⊑ B [ β ]ᴿ ⊣ Δᴿ
⊑-open∀ᵢ α⊑β α<Δᴸ β<Δᴿ p =
  ⊑-renameᵗ²ᵢ
    (rename-assm²-open∀ᵢ α⊑β)
    (singleRenameᵗ-Wf-< α<Δᴸ)
    (singleRenameᵗ-Wf-< β<Δᴿ)
    p

⊑-source-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ B ⊣ Δᴿ
⊑-source-liftνᵢ {A = A} {B = B} p =
  subst
    (λ B′ → _ ∣ _ ⊢ ⇑ᵗ A ⊑ B′ ⊣ _)
    (renameᵗ-id B)
    (⊑-renameᵗ²ᵢ
      {ρ = suc}
      {σ = λ X → X}
      rename-assm²-source-νᵢ
      (λ X<Δ → s<s X<Δ)
      (λ Y<Δ → Y<Δ)
      p)

rename-assm²-target-rightᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → X) suc a ∈ ⇑ᴿᵢ Φ
rename-assm²-target-rightᵢ {Φ = []} ()
rename-assm²-target-rightᵢ {Φ = (X ˣ⊑★) ∷ Φ} (here refl) =
  here refl
rename-assm²-target-rightᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl) =
  here refl
rename-assm²-target-rightᵢ {Φ = (X ˣ⊑★) ∷ Φ} (there a∈) =
  there (rename-assm²-target-rightᵢ a∈)
rename-assm²-target-rightᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (there a∈) =
  there (rename-assm²-target-rightᵢ a∈)

⊑-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
⊑-target-lift-rightᵢ {A = A} {B = B} p =
  subst
    (λ A′ → ⇑ᴿᵢ _ ∣ _ ⊢ A′ ⊑ ⇑ᵗ B ⊣ _)
    (renameᵗ-id A)
    (⊑-renameᵗ²ᵢ
      {ρ = λ X → X}
      {σ = suc}
      rename-assm²-target-rightᵢ
      (λ X<Δ → X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p)

νᵣᵢ : Renameᵗ → Renameᵗ
νᵣᵢ ρ X = suc (ρ X)

record ComposeCtxᵢ
    (ρ : Renameᵗ) (Δᴸ : TyCtx)
    (Φᴸ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    compose-map-varᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      X ≡ ρ Y

    compose-var-varᵢ :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑ˣ Z) ∈ Φᴿ →
      (X ˣ⊑ˣ Z) ∈ Φᴼ

    compose-var-starᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑★) ∈ Φᴿ →
      (X ˣ⊑★) ∈ Φᴼ

    compose-star-leftᵢ :
      ∀ {X} →
      X < Δᴸ →
      (X ˣ⊑★) ∈ Φᴸ →
      (X ˣ⊑★) ∈ Φᴼ

open ComposeCtxᵢ

compose-idᵢ :
  ∀ Δ →
  ComposeCtxᵢ (λ X → X) Δ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ)
compose-idᵢ Δ .compose-map-varᵢ x∈ = idᵢ-var-identity x∈
compose-idᵢ Δ .compose-var-varᵢ x∈ y∈ =
  subst
    (λ Z → (_ ˣ⊑ˣ Z) ∈ idᵢ Δ)
    (idᵢ-var-identity y∈)
    x∈
compose-idᵢ Δ .compose-var-starᵢ x∈ y★∈ =
  ⊥-elim (idᵢ-no-star y★∈)
compose-idᵢ Δ .compose-star-leftᵢ X<Δ x★∈ =
  ⊥-elim (idᵢ-no-star x★∈)

compose-id-leftᵢ :
  ∀ Δ Φ →
  ComposeCtxᵢ (λ X → X) Δ (idᵢ Δ) Φ Φ
compose-id-leftᵢ Δ Φ .compose-map-varᵢ x∈ = idᵢ-var-identity x∈
compose-id-leftᵢ Δ Φ .compose-var-varᵢ x∈ y∈ =
  subst
    (λ X → (X ˣ⊑ˣ _) ∈ Φ)
    (sym (idᵢ-var-identity x∈))
    y∈
compose-id-leftᵢ Δ Φ .compose-var-starᵢ x∈ y★∈ =
  subst
    (λ X → (X ˣ⊑★) ∈ Φ)
    (sym (idᵢ-var-identity x∈))
    y★∈
compose-id-leftᵢ Δ Φ .compose-star-leftᵢ X<Δ x★∈ =
  ⊥-elim (idᵢ-no-star x★∈)

compose-∀∀ᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtxᵢ (extᵗ ρ) (suc Δᴸ) (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (here refl) =
  refl
compose-∀∀ᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = zero} {Y = suc Y}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = suc X} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ᵢ comp .compose-map-varᵢ {X = suc X} {Y = suc Y}
    (there x∈) =
  cong suc (compose-map-varᵢ comp (un⇑ᵢ-ˣ∈ x∈))
compose-∀∀ᵢ comp .compose-var-varᵢ (here refl) (here refl) =
  here refl
compose-∀∀ᵢ comp .compose-var-varᵢ (here refl) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left y∈)
compose-∀∀ᵢ comp .compose-var-varᵢ {X = zero} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-varᵢ {X = zero} {Y = suc Y}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-varᵢ {X = suc X} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ᵢ comp .compose-var-varᵢ
    {X = suc X} {Y = suc Y} {Z = zero}
    (there x∈) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right y∈)
compose-∀∀ᵢ comp .compose-var-varᵢ
    {X = suc X} {Y = suc Y} {Z = suc z}
    (there x∈) (there y∈) =
  there (⇑ᵢ-ˣ∈
    (compose-var-varᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-ˣ∈ y∈)))
compose-∀∀ᵢ comp .compose-var-starᵢ (here refl) (there y★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star y★∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = zero} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = zero} {Y = suc Y}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = suc X} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ᵢ comp .compose-var-starᵢ {X = suc X} {Y = suc Y}
    (there x∈) (there y★∈) =
  there (⇑ᵢ-★∈
    (compose-var-starᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-★∈ y★∈)))
compose-∀∀ᵢ comp .compose-star-leftᵢ {X = zero} z<s
    (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
compose-∀∀ᵢ comp .compose-star-leftᵢ {X = suc X} (s<s X<Δ)
    (there x★∈) =
  there (⇑ᵢ-★∈ (compose-star-leftᵢ comp X<Δ (un⇑ᵢ-★∈ x★∈)))

compose-∀νᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtxᵢ (extᵗ ρ) (suc Δᴸ) (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (νᵢᶜ Φᴼ)
compose-∀νᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (here refl) =
  refl
compose-∀νᵢ comp .compose-map-varᵢ {X = zero} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-map-varᵢ {X = zero} {Y = suc Y}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-map-varᵢ {X = suc X} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀νᵢ comp .compose-map-varᵢ {X = suc X} {Y = suc Y}
    (there x∈) =
  cong suc (compose-map-varᵢ comp (un⇑ᵢ-ˣ∈ x∈))
compose-∀νᵢ comp .compose-var-varᵢ (here refl) (there y∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left y∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = zero} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = zero} {Y = suc Y}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = suc X} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀νᵢ comp .compose-var-varᵢ {X = suc X} {Y = suc Y}
    (there x∈) (there y∈) =
  there (⇑ᴸᵢ-ˣ∈
    (compose-var-varᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-ˣ∈ y∈)))
compose-∀νᵢ comp .compose-var-starᵢ (here refl) (here refl) =
  here refl
compose-∀νᵢ comp .compose-var-starᵢ (here refl) (there y★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star y★∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = zero} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = zero} {Y = suc Y}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = suc X} {Y = zero}
    (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀νᵢ comp .compose-var-starᵢ {X = suc X} {Y = suc Y}
    (there x∈) (there y★∈) =
  there (⇑ᴸᵢ-★∈
    (compose-var-starᵢ comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-★∈ y★∈)))
compose-∀νᵢ comp .compose-star-leftᵢ {X = zero} z<s
    (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
compose-∀νᵢ comp .compose-star-leftᵢ {X = suc X} (s<s X<Δ)
    (there x★∈) =
  there (⇑ᴸᵢ-★∈ (compose-star-leftᵢ comp X<Δ (un⇑ᵢ-★∈ x★∈)))

compose-νidᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtxᵢ (νᵣᵢ ρ) (suc Δᴸ) (νᵢᶜ Φᴸ) Φᴿ (νᵢᶜ Φᴼ)
compose-νidᵢ comp .compose-map-varᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νidᵢ comp .compose-map-varᵢ {X = suc X} (there x∈) =
  cong suc (compose-map-varᵢ comp (un⇑ᴸᵢ-ˣ∈ x∈))
compose-νidᵢ comp .compose-var-varᵢ {X = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νidᵢ comp .compose-var-varᵢ {X = suc X} (there x∈) y∈ =
  there (⇑ᴸᵢ-ˣ∈ (compose-var-varᵢ comp (un⇑ᴸᵢ-ˣ∈ x∈) y∈))
compose-νidᵢ comp .compose-var-starᵢ {X = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νidᵢ comp .compose-var-starᵢ {X = suc X} (there x∈) y★∈ =
  there (⇑ᴸᵢ-★∈ (compose-var-starᵢ comp (un⇑ᴸᵢ-ˣ∈ x∈) y★∈))
compose-νidᵢ comp .compose-star-leftᵢ {X = zero} z<s (here refl) =
  here refl
compose-νidᵢ comp .compose-star-leftᵢ {X = zero} z<s (there x★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x★∈)
compose-νidᵢ comp .compose-star-leftᵢ {X = suc X} (s<s X<Δ)
    (there x★∈) =
  there (⇑ᴸᵢ-★∈ (compose-star-leftᵢ comp X<Δ (un⇑ᴸᵢ-★∈ x★∈)))

occurs-var-backᵢ :
  ∀ (ρ : Renameᵗ) (x : TyVar) {y z} →
  y ≡ ρ z →
  occurs x (＇ z) ≡ true →
  occurs (ρ x) (＇ y) ≡ true
occurs-var-backᵢ ρ x {y} {z} y≡ρz occ with x ≟ z
occurs-var-backᵢ ρ x {y} {.x} y≡ρx occ | yes refl
    rewrite y≡ρx with ρ x ≟ ρ x
occurs-var-backᵢ ρ x {y} {.x} y≡ρx occ | yes refl | yes refl = refl
occurs-var-backᵢ ρ x {y} {.x} y≡ρx occ | yes refl | no ρx≢ρx =
  ⊥-elim (ρx≢ρx refl)
occurs-var-backᵢ ρ x {y} {z} y≡ρz () | no x≢z

occurs-backᵢ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ Δᴹ A B} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  (X : TyVar) →
  Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
  occurs X B ≡ true →
  occurs (ρ X) A ≡ true
occurs-backᵢ comp X id★ ()
occurs-backᵢ comp X (idˣ x∈ _ _) occ =
  occurs-var-backᵢ _ X (compose-map-varᵢ comp x∈) occ
occurs-backᵢ comp X idι ()
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ
    with occurs X B₁ in occ₁
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | true =
  ∨-true-leftᵢ (occurs-backᵢ comp X p occ₁)
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | false
    with occurs X B₂ in occ₂
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | false | true =
  ∨-true-rightᵢ (occurs-backᵢ comp X q occ₂)
occurs-backᵢ {ρ = ρ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    comp X (p ↦ q) occ | false | false =
  ⊥-elim (false≠trueᵢ occ)
occurs-backᵢ comp X (∀ⁱ p) occ =
  occurs-backᵢ (compose-∀∀ᵢ comp) (suc X) p occ
occurs-backᵢ comp X (tag ι) ()
occurs-backᵢ comp X (tag_⇛_ p q) ()
occurs-backᵢ comp X (tagˣ x∈ _) ()
occurs-backᵢ comp X (ν occA p) occ =
  occurs-backᵢ (compose-νidᵢ comp) X p occ

⊑-trans-composeᵢ :
  ∀ {ρ Δᴸ Δᴹ Δᴿ Φᴸ Φᴿ Φᴼ A B C} →
  ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
  Φᴿ ∣ Δᴹ ⊢ B ⊑ C ⊣ Δᴿ →
  Φᴼ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-composeᵢ comp id★ id★ = id★
⊑-trans-composeᵢ comp (idˣ x∈ X<Δ _) (idˣ y∈ _ Z<Δ) =
  idˣ (compose-var-varᵢ comp x∈ y∈) X<Δ Z<Δ
⊑-trans-composeᵢ comp (idˣ x∈ X<Δ _) (tagˣ y★∈ _) =
  tagˣ (compose-var-starᵢ comp x∈ y★∈) X<Δ
⊑-trans-composeᵢ comp idι idι = idι
⊑-trans-composeᵢ comp idι (tag ι) = tag ι
⊑-trans-composeᵢ comp (p₁ ↦ p₂) (q₁ ↦ q₂) =
  ⊑-trans-composeᵢ comp p₁ q₁ ↦ ⊑-trans-composeᵢ comp p₂ q₂
⊑-trans-composeᵢ comp (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  tag_⇛_
    (⊑-trans-composeᵢ comp p₁ q₁)
    (⊑-trans-composeᵢ comp p₂ q₂)
⊑-trans-composeᵢ comp (∀ⁱ p) (∀ⁱ q) =
  ∀ⁱ (⊑-trans-composeᵢ (compose-∀∀ᵢ comp) p q)
⊑-trans-composeᵢ comp (∀ⁱ p) (ν occ q) =
  ν
    (occurs-backᵢ (compose-∀∀ᵢ comp) zero p occ)
    (⊑-trans-composeᵢ (compose-∀νᵢ comp) p q)
⊑-trans-composeᵢ comp (tag ι) id★ = tag ι
⊑-trans-composeᵢ comp (tag p ⇛ q) id★ =
  tag_⇛_
    (⊑-trans-composeᵢ comp p id★)
    (⊑-trans-composeᵢ comp q id★)
⊑-trans-composeᵢ comp (tagˣ x★∈ X<Δ) id★ =
  tagˣ (compose-star-leftᵢ comp X<Δ x★∈) X<Δ
⊑-trans-composeᵢ comp (ν occ p) q =
  ν occ (⊑-trans-composeᵢ (compose-νidᵢ comp) p q)

⊑-trans-idᵢ :
  ∀ {Δ A B C} →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ B ⊑ C ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ A ⊑ C ⊣ Δ
⊑-trans-idᵢ {Δ = Δ} p q =
  ⊑-trans-composeᵢ (compose-idᵢ Δ) p q

⊑-trans-left-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  idᵢ Δᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴸ →
  Φ ∣ Δᴸ ⊢ B ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-left-idᵢ {Φ = Φ} {Δᴸ = Δᴸ} p q =
  ⊑-trans-composeᵢ (compose-id-leftᵢ Δᴸ Φ) p q

⊑-renameᵗ²-oldᵢ :
  ∀ {Φ Ψ ρ σ A B} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ ρ σ a ∈ Ψ) →
  Imp._⊢_⊑_ Φ A B →
  Imp._⊢_⊑_ Ψ (renameᵗ ρ A) (renameᵗ σ B)
⊑-renameᵗ²-oldᵢ h Imp.id★ = Imp.id★
⊑-renameᵗ²-oldᵢ h (Imp.idˣ x∈) = Imp.idˣ (h x∈)
⊑-renameᵗ²-oldᵢ h Imp.idι = Imp.idι
⊑-renameᵗ²-oldᵢ h (p Imp.↦ q) =
  ⊑-renameᵗ²-oldᵢ h p Imp.↦ ⊑-renameᵗ²-oldᵢ h q
⊑-renameᵗ²-oldᵢ h (Imp.∀ⁱ p) =
  Imp.∀ⁱ (⊑-renameᵗ²-oldᵢ (rename-assm²-⇑ᵢ h) p)
⊑-renameᵗ²-oldᵢ h (Imp.tag ι) = Imp.tag ι
⊑-renameᵗ²-oldᵢ h (Imp.tag p ⇛ q) =
  Imp.tag (⊑-renameᵗ²-oldᵢ h p) ⇛ ⊑-renameᵗ²-oldᵢ h q
⊑-renameᵗ²-oldᵢ h (Imp.tagˣ x∈) = Imp.tagˣ (h x∈)
⊑-renameᵗ²-oldᵢ {ρ = ρ} {σ = σ} h
    (Imp.ν {A = A} {B = B} occA p) =
  Imp.ν (trans (occurs-zero-rename-ext ρ A) occA)
    (subst
      (λ B′ →
        Imp._⊢_⊑_ ((zero ˣ⊑★) ∷ ⇑ᵢ _)
          (renameᵗ (extᵗ ρ) A) B′)
      (renameᵗ-ext-suc-comm σ B)
      (⊑-renameᵗ²-oldᵢ
        {ρ = extᵗ ρ}
        {σ = extᵗ σ}
        (rename-assm²-★⇑ᵢ h)
        p))

rename-assm²-⇑ᴸ-to-⇑ᵢ :
  ∀ {Φ a} →
  a ∈ νᵢᶜ Φ →
  rename-assm²ᵢ (λ X → X) suc a ∈ (zero ˣ⊑★) ∷ ⇑ᵢ Φ
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑★} (here refl) = here refl
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑★} (here ())
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᵢ-★∈ (un⇑ᴸᵢ-★∈ a∈))
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑ˣ Y} (there a∈) =
  there (⇑ᵢ-ˣ∈ (un⇑ᴸᵢ-ˣ∈ a∈))

⊑-target-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
⊑-target-liftνᵢ {Φ = Φ} {A = A} {B = B} p =
  subst
    (λ A′ → ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) ∣ _ ⊢ A′ ⊑ ⇑ᵗ B ⊣ _)
    (renameᵗ-id A)
    (⊑-renameᵗ²ᵢ
      {ρ = λ X → X}
      {σ = suc}
      rename-assm²-⇑ᴸ-to-⇑ᵢ
      (λ X<Δ → X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p)

old-target-liftᵢ :
  ∀ {Φ A B} →
  Imp._⊢_⊑_ (νᵢᶜ Φ) A B →
  Imp._⊢_⊑_ ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ B)
old-target-liftᵢ {Φ = Φ} {A = A} {B = B} p =
  subst
    (λ A′ → Imp._⊢_⊑_ ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A′ (⇑ᵗ B))
    (renameᵗ-id A)
    (⊑-renameᵗ²-oldᵢ {ρ = λ X → X} {σ = suc}
      rename-assm²-⇑ᴸ-to-⇑ᵢ p)

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

⊑-crossed-body-lift∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ A ⊑ renameᵗ (extᵗ suc) B ⊣ suc (suc Δᴿ)
⊑-crossed-body-lift∀∀ᵢ {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ ⇑ᵗ _ ⊑ T ⊣ _)
    (renameᵗ-swap01-liftᵢ B)
    (⊑-swapRight01∀∀ᵢ (⊑-lift∀ᵢ p))

⊑-crossed-left-body-lift∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ renameᵗ (extᵗ suc) A ⊑ ⇑ᵗ B ⊣ suc (suc Δᴿ)
⊑-crossed-left-body-lift∀∀ᵢ {A = A} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ ⇑ᵗ _ ⊣ _)
    (renameᵗ-swap01-liftᵢ A)
    (⊑-swapLeft01∀∀ᵢ (⊑-lift∀ᵢ p))

⊑-crossed-double-lift∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ (⇑ᵗ A) ⊑ ⇑ᵗ (⇑ᵗ B) ⊣ suc (suc Δᴿ)
⊑-crossed-double-lift∀∀ᵢ {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ ⇑ᵗ (⇑ᵗ _) ⊑ T ⊣ _)
    (renameᵗ-swap01-double-liftᵢ B)
    (⊑-swapRight01∀∀ᵢ (⊑-lift∀ᵢ (⊑-lift∀ᵢ p)))

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
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ) ⊢ A ⊑ B ⊣ suc (suc Δᴿ) →
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
⊑-∀ν-to-ν∀ᵢ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} p =
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

νlower-∀shape-body-lowerᵢ :
  ∀ {Φ Δᶜ C D} →
  occurs zero (`∀ C) ≡ true →
  ∀ᵢᶜ (νᵢᶜ Φ) ∣ suc (suc Δᶜ) ⊢ C ⊑ D ⊣ suc Δᶜ →
  ∀ᵢᶜ Φ ∣ suc Δᶜ ⊢ `∀ (renameᵗ swap01ᵢ C) ⊑ D ⊣ suc Δᶜ
νlower-∀shape-body-lowerᵢ {C = C} occC C⊑D =
  ν (occurs-swap01-leftᵢ C occC) (⊑-∀ν-to-ν∀ᵢ C⊑D)

⊑-forgetᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Imp._⊢_⊑_ Φ A B
⊑-forgetᵢ id★ = Imp.id★
⊑-forgetᵢ (idˣ x∈ X<Δᴸ Y<Δᴿ) = Imp.idˣ x∈
⊑-forgetᵢ idι = Imp.idι
⊑-forgetᵢ (p ↦ q) = ⊑-forgetᵢ p Imp.↦ ⊑-forgetᵢ q
⊑-forgetᵢ (∀ⁱ p) = Imp.∀ⁱ (⊑-forgetᵢ p)
⊑-forgetᵢ (tag ι) = Imp.tag ι
⊑-forgetᵢ (tag p ⇛ q) = Imp.tag (⊑-forgetᵢ p) ⇛ ⊑-forgetᵢ q
⊑-forgetᵢ (tagˣ x∈ X<Δᴸ) = Imp.tagˣ x∈
⊑-forgetᵢ (ν occA p) = Imp.ν occA (old-target-liftᵢ (⊑-forgetᵢ p))

record DropTargetCtxᵢ (k : TyVar) (Φ Ψ : ImpCtx) : Set where
  field
    drop-varᵗᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ raiseVarFrom k Y) ∈ Φ →
      (X ˣ⊑ˣ Y) ∈ Ψ

    drop-starᵗᵢ :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φ →
      (X ˣ⊑★) ∈ Ψ

open DropTargetCtxᵢ

drop-target-∀ᵢ :
  ∀ {k Φ Ψ} →
  DropTargetCtxᵢ k Φ Ψ →
  DropTargetCtxᵢ (suc k) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = zero} {Y = zero} (here refl) =
  here refl
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = suc X} {Y = suc Y} (there x∈) =
  there (⇑ᵢ-ˣ∈ (drop-varᵗᵢ drop (un⇑ᵢ-ˣ∈ x∈)))
drop-target-∀ᵢ drop .drop-starᵗᵢ (here ())
drop-target-∀ᵢ drop .drop-starᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-∀ᵢ drop .drop-starᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᵢ-★∈ (drop-starᵗᵢ drop (un⇑ᵢ-★∈ x∈)))

drop-target-νᵢ :
  ∀ {k Φ Ψ} →
  DropTargetCtxᵢ k Φ Ψ →
  DropTargetCtxᵢ k (νᵢᶜ Φ) (νᵢᶜ Ψ)
drop-target-νᵢ drop .drop-varᵗᵢ (here ())
drop-target-νᵢ drop .drop-varᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-target-νᵢ drop .drop-varᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ (drop-varᵗᵢ drop (un⇑ᴸᵢ-ˣ∈ x∈)))
drop-target-νᵢ drop .drop-starᵗᵢ (here refl) = here refl
drop-target-νᵢ drop .drop-starᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-target-νᵢ drop .drop-starᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-★∈ (drop-starᵗᵢ drop (un⇑ᴸᵢ-★∈ x∈)))

drop-target-zeroᵢ :
  ∀ {Φ} →
  DropTargetCtxᵢ zero ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) (νᵢᶜ Φ)
drop-target-zeroᵢ .drop-varᵗᵢ (here ())
drop-target-zeroᵢ .drop-varᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-zeroᵢ .drop-varᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ (un⇑ᵢ-ˣ∈ x∈))
drop-target-zeroᵢ .drop-starᵗᵢ (here refl) = here refl
drop-target-zeroᵢ .drop-starᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-zeroᵢ .drop-starᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-★∈ (un⇑ᵢ-★∈ x∈))

mutual
  drop-targetᵢ :
    ∀ {k Φ Ψ Δᴸ Δᴿ A B} →
    WfTy Δᴿ B →
    DropTargetCtxᵢ k Φ Ψ →
    Φ ∣ Δᴸ ⊢ A ⊑ renameᵗ (raiseVarFrom k) B ⊣ suc Δᴿ →
    Ψ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  drop-targetᵢ wf★ drop id★ = id★
  drop-targetᵢ (wfVar Y<Δ) drop (idˣ x∈ X<Δ _) =
    idˣ (drop-varᵗᵢ drop x∈) X<Δ Y<Δ
  drop-targetᵢ wfBase drop idι = idι
  drop-targetᵢ (wf⇒ hA hB) drop (p ↦ q) =
    drop-targetᵢ hA drop p ↦ drop-targetᵢ hB drop q
  drop-targetᵢ {k = k} (wf∀ {A = B} hB) drop (∀ⁱ p)
      rewrite rename-raise-ext k B =
    ∀ⁱ (drop-targetᵢ hB (drop-target-∀ᵢ drop) p)
  drop-targetᵢ wf★ drop (tag ι) = tag ι
  drop-targetᵢ wf★ drop (tag p ⇛ q) =
    tag (drop-targetᵢ wf★ drop p) ⇛ drop-targetᵢ wf★ drop q
  drop-targetᵢ wf★ drop (tagˣ x∈ X<Δ) =
    tagˣ (drop-starᵗᵢ drop x∈) X<Δ
  drop-targetᵢ hB drop (ν occ p) =
    ν occ (drop-targetᵢ hB (drop-target-νᵢ drop) p)

old⊑→wfᵢ :
  ∀ {Δ Φ A B} →
  ImpProps.WfImpCtx Δ Φ →
  Imp._⊢_⊑_ Φ A B →
  Φ ∣ Δ ⊢ A ⊑ B ⊣ Δ
old⊑→wfᵢ hΦ Imp.id★ = id★
old⊑→wfᵢ hΦ (Imp.idˣ x∈) =
  idˣ x∈ (proj₁ (hΦ x∈)) (proj₂ (hΦ x∈))
old⊑→wfᵢ hΦ Imp.idι = idι
old⊑→wfᵢ hΦ (p Imp.↦ q) = old⊑→wfᵢ hΦ p ↦ old⊑→wfᵢ hΦ q
old⊑→wfᵢ hΦ (Imp.∀ⁱ p) =
  ∀ⁱ (old⊑→wfᵢ (ImpProps.∀ᵢ-wf hΦ) p)
old⊑→wfᵢ hΦ (Imp.tag ι) = tag ι
old⊑→wfᵢ hΦ (Imp.tag p ⇛ q) =
  tag (old⊑→wfᵢ hΦ p) ⇛ old⊑→wfᵢ hΦ q
old⊑→wfᵢ hΦ (Imp.tagˣ x∈) = tagˣ x∈ (hΦ x∈)
old⊑→wfᵢ hΦ r@(Imp.ν occ p) =
  ν occ
    (drop-targetᵢ
      (ImpProps.⊑-tgt-wf hΦ r)
      drop-target-zeroᵢ
      (old⊑→wfᵢ (ImpProps.νᵢ-wf hΦ) p))

old⊑→wf-idᵢ :
  ∀ {Δ A B} →
  Imp._⊢_⊑_ (idᵢ Δ) A B →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ
old⊑→wf-idᵢ {Δ = Δ} = old⊑→wfᵢ (ImpProps.idᵢ-wf Δ)

data DropAtᵢ : TyVar → ImpCtx → ImpCtx → Set where
  drop-zeroᵢ :
    ∀ {Φ} →
    DropAtᵢ zero (νᵢᶜ Φ) Φ

  drop-∀ᵢ :
    ∀ {k Φ Ψ} →
    DropAtᵢ k Φ Ψ →
    DropAtᵢ (suc k) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)

  drop-νᵢ :
    ∀ {k Φ Ψ} →
    DropAtᵢ k Φ Ψ →
    DropAtᵢ (suc k) (νᵢᶜ Φ) (νᵢᶜ Ψ)

data DropBothAtᵢ : TyVar → TyVar → ImpCtx → ImpCtx → Set where
  drop-both-zeroᵢ :
    ∀ {Φ} →
    DropBothAtᵢ zero zero (∀ᵢᶜ Φ) Φ

  drop-both-∀ᵢ :
    ∀ {kᴸ kᴿ Φ Ψ} →
    DropBothAtᵢ kᴸ kᴿ Φ Ψ →
    DropBothAtᵢ (suc kᴸ) (suc kᴿ) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)

  drop-both-νᵢ :
    ∀ {kᴸ kᴿ Φ Ψ} →
    DropBothAtᵢ kᴸ kᴿ Φ Ψ →
    DropBothAtᵢ (suc kᴸ) kᴿ (νᵢᶜ Φ) (νᵢᶜ Ψ)

removeAt-Wfᵢ :
  ∀ k {Δ X} →
  k < suc Δ →
  X < suc Δ →
  occurs k (＇ X) ≡ false →
  removeAtᵗ k X < Δ
removeAt-Wfᵢ zero {X = zero} k<Δ X<Δ ()
removeAt-Wfᵢ zero {X = suc X} k<Δ (s<s X<Δ) occ = X<Δ
removeAt-Wfᵢ (suc k) {Δ = zero} (s<s ()) X<Δ occ
removeAt-Wfᵢ (suc k) {Δ = suc Δ} {X = zero} (s<s k<Δ) X<Δ occ =
  z<s
removeAt-Wfᵢ (suc k) {Δ = suc Δ} {X = suc X} (s<s k<Δ)
    (s<s X<Δ) occ =
  s<s (removeAt-Wfᵢ k k<Δ X<Δ (trans (occurs-suc-var k X) occ))

drop-var-memberᵢ :
  ∀ {k Φ Ψ X Y} →
  DropAtᵢ k Φ Ψ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (removeAtᵗ k X ˣ⊑ˣ Y) ∈ Ψ
drop-var-memberᵢ drop-zeroᵢ (here ())
drop-var-memberᵢ {X = zero} drop-zeroᵢ (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-var-memberᵢ {X = suc X} drop-zeroᵢ (there x∈) =
  un⇑ᴸᵢ-ˣ∈ x∈
drop-var-memberᵢ {X = zero} {Y = zero} (drop-∀ᵢ d) (here refl) =
  here refl
drop-var-memberᵢ {X = zero} {Y = suc Y} (drop-∀ᵢ d) (here ())
drop-var-memberᵢ {X = zero} (drop-∀ᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-var-memberᵢ {X = suc X} {Y = zero} (drop-∀ᵢ d) (here ())
drop-var-memberᵢ {X = suc X} {Y = zero} (drop-∀ᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-var-memberᵢ {X = suc X} {Y = suc Y} (drop-∀ᵢ d) (there x∈) =
  there (⇑ᵢ-ˣ∈ (drop-var-memberᵢ d (un⇑ᵢ-ˣ∈ x∈)))
drop-var-memberᵢ (drop-νᵢ d) (here ())
drop-var-memberᵢ {X = zero} (drop-νᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-var-memberᵢ {X = suc X} (drop-νᵢ d) (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ (drop-var-memberᵢ d (un⇑ᴸᵢ-ˣ∈ x∈)))

drop-star-memberᵢ :
  ∀ {k Φ Ψ X} →
  DropAtᵢ k Φ Ψ →
  occurs k (＇ X) ≡ false →
  (X ˣ⊑★) ∈ Φ →
  (removeAtᵗ k X ˣ⊑★) ∈ Ψ
drop-star-memberᵢ {X = zero} drop-zeroᵢ () x∈
drop-star-memberᵢ {X = suc X} drop-zeroᵢ occ (here ())
drop-star-memberᵢ {X = suc X} drop-zeroᵢ occ (there x∈) =
  un⇑ᴸᵢ-★∈ x∈
drop-star-memberᵢ (drop-∀ᵢ d) occ (here ())
drop-star-memberᵢ {X = zero} (drop-∀ᵢ d) occ (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-star-memberᵢ {k = suc k} {X = suc X} (drop-∀ᵢ d) occ
    (there x∈) =
  there
    (⇑ᵢ-★∈
      (drop-star-memberᵢ d
        (trans (occurs-suc-var k X) occ)
        (un⇑ᵢ-★∈ x∈)))
drop-star-memberᵢ {X = zero} (drop-νᵢ d) occ (here refl) = here refl
drop-star-memberᵢ {X = zero} (drop-νᵢ d) occ (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-star-memberᵢ {k = suc k} {X = suc X} (drop-νᵢ d) occ
    (there x∈) =
  there
    (⇑ᴸᵢ-★∈
      (drop-star-memberᵢ d
        (trans (occurs-suc-var k X) occ)
        (un⇑ᴸᵢ-★∈ x∈)))

drop-both-var-memberᵢ :
  ∀ {kᴸ kᴿ Φ Ψ X Y} →
  DropBothAtᵢ kᴸ kᴿ Φ Ψ →
  occurs kᴸ (＇ X) ≡ false →
  occurs kᴿ (＇ Y) ≡ false →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (removeAtᵗ kᴸ X ˣ⊑ˣ removeAtᵗ kᴿ Y) ∈ Ψ
drop-both-var-memberᵢ drop-both-zeroᵢ () occY (here refl)
drop-both-var-memberᵢ {X = zero} drop-both-zeroᵢ occX occY
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-both-var-memberᵢ {X = suc X} {Y = zero} drop-both-zeroᵢ
    occX occY (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-both-var-memberᵢ {X = suc X} {Y = suc Y} drop-both-zeroᵢ
    occX occY (there x∈) =
  un⇑ᵢ-ˣ∈ x∈
drop-both-var-memberᵢ (drop-both-∀ᵢ d) occX occY (here refl) =
  here refl
drop-both-var-memberᵢ {X = zero} (drop-both-∀ᵢ d) occX occY
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-both-var-memberᵢ {X = suc X} {Y = zero} (drop-both-∀ᵢ d)
    occX occY (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-both-var-memberᵢ {kᴸ = suc kᴸ} {kᴿ = suc kᴿ}
    {X = suc X} {Y = suc Y} (drop-both-∀ᵢ d) occX occY
    (there x∈) =
  there
    (⇑ᵢ-ˣ∈
      (drop-both-var-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        (occurs-suc-falseᵢ kᴿ Y occY)
        (un⇑ᵢ-ˣ∈ x∈)))
drop-both-var-memberᵢ (drop-both-νᵢ d) occX occY (here ())
drop-both-var-memberᵢ {X = zero} (drop-both-νᵢ d) occX occY
    (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-both-var-memberᵢ {kᴸ = suc kᴸ} {X = suc X}
    (drop-both-νᵢ d) occX occY (there x∈) =
  there
    (⇑ᴸᵢ-ˣ∈
      (drop-both-var-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        occY
        (un⇑ᴸᵢ-ˣ∈ x∈)))

drop-both-star-memberᵢ :
  ∀ {kᴸ kᴿ Φ Ψ X} →
  DropBothAtᵢ kᴸ kᴿ Φ Ψ →
  occurs kᴸ (＇ X) ≡ false →
  (X ˣ⊑★) ∈ Φ →
  (removeAtᵗ kᴸ X ˣ⊑★) ∈ Ψ
drop-both-star-memberᵢ drop-both-zeroᵢ occX (here ())
drop-both-star-memberᵢ {X = zero} drop-both-zeroᵢ occX (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-both-star-memberᵢ {X = suc X} drop-both-zeroᵢ occX (there x∈) =
  un⇑ᵢ-★∈ x∈
drop-both-star-memberᵢ (drop-both-∀ᵢ d) occX (here ())
drop-both-star-memberᵢ {X = zero} (drop-both-∀ᵢ d) occX
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-both-star-memberᵢ {kᴸ = suc kᴸ} {X = suc X}
    (drop-both-∀ᵢ d) occX (there x∈) =
  there
    (⇑ᵢ-★∈
      (drop-both-star-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        (un⇑ᵢ-★∈ x∈)))
drop-both-star-memberᵢ {X = zero} (drop-both-νᵢ d) occX
    (here refl) =
  here refl
drop-both-star-memberᵢ {X = zero} (drop-both-νᵢ d) occX
    (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-both-star-memberᵢ {kᴸ = suc kᴸ} {X = suc X}
    (drop-both-νᵢ d) occX (there x∈) =
  there
    (⇑ᴸᵢ-★∈
      (drop-both-star-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        (un⇑ᴸᵢ-★∈ x∈)))

open-unused-atᵢ :
  ∀ {k Φ Ψ Δᴸ Δᴿ A B} →
  DropAtᵢ k Φ Ψ →
  k < suc Δᴸ →
  occurs k A ≡ false →
  Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ ⊢ renameᵗ (removeAtᵗ k) A ⊑ B ⊣ Δᴿ
open-unused-atᵢ d k<Δ occ id★ = id★
open-unused-atᵢ d k<Δ occ (idˣ x∈ X<Δ Y<Δ) =
  idˣ (drop-var-memberᵢ d x∈) (removeAt-Wfᵢ _ k<Δ X<Δ occ) Y<Δ
open-unused-atᵢ d k<Δ occ idι = idι
open-unused-atᵢ {k = k} d k<Δ occ (_↦_ {A = A} p q)
    with occurs k A in occA
open-unused-atᵢ {k = k} d k<Δ occ (_↦_ {A = A} p q) | false =
  open-unused-atᵢ d k<Δ occA p ↦ open-unused-atᵢ d k<Δ occ q
open-unused-atᵢ {k = k} d k<Δ () (_↦_ {A = A} p q) | true
open-unused-atᵢ {k = k} d k<Δ occ (∀ⁱ p) =
  ∀ⁱ (open-unused-atᵢ
        (drop-∀ᵢ d)
        (s<s k<Δ)
        occ
        p)
open-unused-atᵢ d k<Δ occ (tag ι) = tag ι
open-unused-atᵢ {k = k} d k<Δ occ (tag_⇛_ {A₁ = A} p q)
    with occurs k A in occA
open-unused-atᵢ {k = k} d k<Δ occ (tag_⇛_ {A₁ = A} p q) | false =
  tag_⇛_ (open-unused-atᵢ d k<Δ occA p)
          (open-unused-atᵢ d k<Δ occ q)
open-unused-atᵢ {k = k} d k<Δ () (tag_⇛_ {A₁ = A} p q) | true
open-unused-atᵢ d k<Δ occ (tagˣ x∈ X<Δ) =
  tagˣ (drop-star-memberᵢ d occ x∈) (removeAt-Wfᵢ _ k<Δ X<Δ occ)
open-unused-atᵢ {k = k} d k<Δ occ (ν {A = A} occA p) =
  ν (trans (occurs-zero-rename-ext (removeAtᵗ k) A) occA)
    (open-unused-atᵢ (drop-νᵢ d) (s<s k<Δ) occ p)

open-unusedᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  occurs zero A ≡ false →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ zero ]ᴿ ⊑ B ⊣ Δᴿ
open-unusedᵢ occ p = open-unused-atᵢ drop-zeroᵢ z<s occ p

open-unused-both-atᵢ :
  ∀ {kᴸ kᴿ Φ Ψ Δᴸ Δᴿ A B} →
  DropBothAtᵢ kᴸ kᴿ Φ Ψ →
  kᴸ < suc Δᴸ →
  kᴿ < suc Δᴿ →
  occurs kᴸ A ≡ false →
  occurs kᴿ B ≡ false →
  Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  Ψ ∣ Δᴸ
    ⊢ renameᵗ (removeAtᵗ kᴸ) A ⊑ renameᵗ (removeAtᵗ kᴿ) B
    ⊣ Δᴿ
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB id★ = id★
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB
    (idˣ x∈ X<Δ Y<Δ) =
  idˣ
    (drop-both-var-memberᵢ d occA occB x∈)
    (removeAt-Wfᵢ _ kᴸ<Δ X<Δ occA)
    (removeAt-Wfᵢ _ kᴿ<Δ Y<Δ occB)
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB idι = idι
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (p ↦ q) =
  open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
    (∨-false-leftᵢ occA)
    (∨-false-leftᵢ occB)
    p
  ↦
  open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
    (∨-false-rightᵢ occA)
    (∨-false-rightᵢ occB)
    q
open-unused-both-atᵢ {kᴸ = kᴸ} {kᴿ = kᴿ} d kᴸ<Δ kᴿ<Δ
    occA occB (∀ⁱ p) =
  ∀ⁱ (open-unused-both-atᵢ
        (drop-both-∀ᵢ d)
        (s<s kᴸ<Δ)
        (s<s kᴿ<Δ)
        occA
        occB
        p)
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (tag ι) = tag ι
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (tag p ⇛ q) =
  tag
    (open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
      (∨-false-leftᵢ occA)
      refl
      p)
  ⇛
  open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
    (∨-false-rightᵢ occA)
    refl
    q
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (tagˣ x∈ X<Δ) =
  tagˣ
    (drop-both-star-memberᵢ d occA x∈)
    (removeAt-Wfᵢ _ kᴸ<Δ X<Δ occA)
open-unused-both-atᵢ {kᴸ = kᴸ} d kᴸ<Δ kᴿ<Δ occA occB
    (ν {A = A} occA′ p) =
  ν (trans (occurs-zero-rename-ext (removeAtᵗ kᴸ) A) occA′)
    (open-unused-both-atᵢ
      (drop-both-νᵢ d)
      (s<s kᴸ<Δ)
      kᴿ<Δ
      occA
      occB
      p)

open-unused-bothᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  occurs zero A ≡ false →
  occurs zero B ≡ false →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ zero ]ᴿ ⊑ B [ zero ]ᴿ ⊣ Δᴿ
open-unused-bothᵢ occA occB p =
  open-unused-both-atᵢ drop-both-zeroᵢ z<s z<s occA occB p

liftˣˣ∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ X Y} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ＇ Y ⊣ Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ ＇ suc X ⊑ ＇ suc Y ⊣ suc Δᴿ
liftˣˣ∀ᵢ (idˣ x⊑y X<Δᴸ Y<Δᴿ) =
  idˣ (there (⇑ᵢ-ˣ∈ x⊑y)) (s<s X<Δᴸ) (s<s Y<Δᴿ)

liftˣ★∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ X} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ ＇ suc X ⊑ ★ ⊣ suc Δᴿ
liftˣ★∀ᵢ (tagˣ x⊑★ X<Δᴸ) =
  tagˣ (there (⇑ᵢ-★∈ x⊑★)) (s<s X<Δᴸ)

liftˣ★∀ᵢ-any :
  ∀ {Φ Δᴸ Δᴿ Δᴼ X} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ ＇ suc X ⊑ ★ ⊣ Δᴼ
liftˣ★∀ᵢ-any (tagˣ x⊑★ X<Δᴸ) =
  tagˣ (there (⇑ᵢ-★∈ x⊑★)) (s<s X<Δᴸ)

liftˣˣνᵢ :
  ∀ {Φ Δᴸ Δᴿ X Y} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ＇ Y ⊣ Δᴿ →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ ＇ suc X ⊑ ＇ Y ⊣ Δᴿ
liftˣˣνᵢ (idˣ x⊑y X<Δᴸ Y<Δᴿ) =
  idˣ (there (⇑ᴸᵢ-ˣ∈ x⊑y)) (s<s X<Δᴸ) Y<Δᴿ

liftˣ★νᵢ :
  ∀ {Φ Δᴸ Δᴿ X} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ ＇ suc X ⊑ ★ ⊣ Δᴿ
liftˣ★νᵢ (tagˣ x⊑★ X<Δᴸ) =
  tagˣ (there (⇑ᴸᵢ-★∈ x⊑★)) (s<s X<Δᴸ)

var-memberᵢ :
  ∀ {Φ Δᴸ Δᴿ X Y} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ＇ Y ⊣ Δᴿ →
  (X ˣ⊑ˣ Y) ∈ Φ
var-memberᵢ (idˣ x∈ _ _) = x∈

star-memberᵢ :
  ∀ {Φ Δᴸ Δᴿ X} →
  Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ →
  (X ˣ⊑★) ∈ Φ
star-memberᵢ (tagˣ x∈ _) = x∈

------------------------------------------------------------------------
-- Maximal lower bounds over indexed imprecision
------------------------------------------------------------------------

CommonLowerBoundᵢ : TyCtx → Ty → Ty → Ty → Set
CommonLowerBoundᵢ Δ A B C =
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ × idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ

StrictlyBelowᵢ : TyCtx → Ty → Ty → Set
StrictlyBelowᵢ Δ C D =
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ ×
  ¬ (idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ)

record MaximalLowerBoundᵢ (Δ : TyCtx) (A B : Ty) : Set where
  field
    lowerᵢ : Ty
    lower-leftᵢ : idᵢ Δ ∣ Δ ⊢ lowerᵢ ⊑ A ⊣ Δ
    lower-rightᵢ : idᵢ Δ ∣ Δ ⊢ lowerᵢ ⊑ B ⊣ Δ
    maximalᵢ :
      ∀ {D} →
      CommonLowerBoundᵢ Δ A B D →
      ¬ StrictlyBelowᵢ Δ lowerᵢ D

open MaximalLowerBoundᵢ public

record ComparableMaximalLowerBoundᵢ (Δ : TyCtx) (A B : Ty) : Set where
  field
    c-lowerᵢ : Ty
    c-lower-leftᵢ : idᵢ Δ ∣ Δ ⊢ c-lowerᵢ ⊑ A ⊣ Δ
    c-lower-rightᵢ : idᵢ Δ ∣ Δ ⊢ c-lowerᵢ ⊑ B ⊣ Δ
    c-comparableᵢ :
      ∀ {D} →
      CommonLowerBoundᵢ Δ A B D →
      idᵢ Δ ∣ Δ ⊢ c-lowerᵢ ⊑ D ⊣ Δ →
      idᵢ Δ ∣ Δ ⊢ D ⊑ c-lowerᵢ ⊣ Δ

open ComparableMaximalLowerBoundᵢ public

comparable⇒maximalᵢ :
  ∀ {Δ A B} →
  ComparableMaximalLowerBoundᵢ Δ A B →
  MaximalLowerBoundᵢ Δ A B
comparable⇒maximalᵢ cb =
  record
    { lowerᵢ = c-lowerᵢ cb
    ; lower-leftᵢ = c-lower-leftᵢ cb
    ; lower-rightᵢ = c-lower-rightᵢ cb
    ; maximalᵢ = λ common (lower⊑D , ¬D⊑lower) →
        ¬D⊑lower (c-comparableᵢ cb common lower⊑D)
    }

------------------------------------------------------------------------
-- Generalized indexed lower bounds
------------------------------------------------------------------------

CommonLowerBoundᶜᵢ :
  ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Ty → Ty → Ty → Set
CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C =
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ × Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ

common-lower-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C} →
  CommonLowerBoundᵢ Δᴸ A B C →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  CommonLowerBoundᶜᵢ Φ Φ Δᴸ Δᴿ Δᴿ A′ B′ C
common-lower-targetᵢ (C⊑A , C⊑B) A⊑A′ B⊑B′ =
  ⊑-trans-left-idᵢ C⊑A A⊑A′ ,
  ⊑-trans-left-idᵢ C⊑B B⊑B′

maximal-lower-target-commonᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  (mlb : MaximalLowerBoundᵢ Δᴸ A B) →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  CommonLowerBoundᶜᵢ Φ Φ Δᴸ Δᴿ Δᴿ A′ B′ (lowerᵢ mlb)
maximal-lower-target-commonᵢ mlb A⊑A′ B⊑B′ =
  common-lower-targetᵢ
    (lower-leftᵢ mlb , lower-rightᵢ mlb)
    A⊑A′
    B⊑B′

StrictlyBelowᶜᵢ : ImpCtx → TyCtx → Ty → Ty → Set
StrictlyBelowᶜᵢ Φ Δ C D =
  Φ ∣ Δ ⊢ C ⊑ D ⊣ Δ × ¬ (Φ ∣ Δ ⊢ D ⊑ C ⊣ Δ)

record MaximalLowerBoundᶜᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B : Ty) : Set where
  field
    lowerᶜᵢ : Ty
    lower-leftᶜᵢ : Φᴸ ∣ Δᶜ ⊢ lowerᶜᵢ ⊑ A ⊣ Δᴸ
    lower-rightᶜᵢ : Φᴿ ∣ Δᶜ ⊢ lowerᶜᵢ ⊑ B ⊣ Δᴿ
    maximalᶜᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
      ¬ StrictlyBelowᶜᵢ Φᴼ Δᶜ lowerᶜᵢ D

open MaximalLowerBoundᶜᵢ public

maximal-idᶜᵢ :
  ∀ {Δ A B} →
  MaximalLowerBoundᵢ Δ A B →
  MaximalLowerBoundᶜᵢ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
maximal-idᶜᵢ mlb =
  record
    { lowerᶜᵢ = lowerᵢ mlb
    ; lower-leftᶜᵢ = lower-leftᵢ mlb
    ; lower-rightᶜᵢ = lower-rightᵢ mlb
    ; maximalᶜᵢ = maximalᵢ mlb
    }

record ComparableMaximalLowerBoundᶜᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B : Ty) : Set where
  field
    cᶜ-lowerᵢ : Ty
    cᶜ-lower-leftᵢ : Φᴸ ∣ Δᶜ ⊢ cᶜ-lowerᵢ ⊑ A ⊣ Δᴸ
    cᶜ-lower-rightᵢ : Φᴿ ∣ Δᶜ ⊢ cᶜ-lowerᵢ ⊑ B ⊣ Δᴿ
    cᶜ-comparableᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
      Φᴼ ∣ Δᶜ ⊢ cᶜ-lowerᵢ ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ cᶜ-lowerᵢ ⊣ Δᶜ

open ComparableMaximalLowerBoundᶜᵢ public

comparable-lower-eqᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  (cb : ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B) →
  cᶜ-lowerᵢ cb ≡ C →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
  Φᴼ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ C ⊣ Δᶜ
comparable-lower-eqᶜᵢ cb eq common lower⊑D =
  subst
    (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    eq
    (cᶜ-comparableᵢ cb common
      (subst (λ T → _ ∣ _ ⊢ T ⊑ _ ⊣ _) (sym eq) lower⊑D))

comparable⇒maximalᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B
comparable⇒maximalᶜᵢ cb =
  record
    { lowerᶜᵢ = cᶜ-lowerᵢ cb
    ; lower-leftᶜᵢ = cᶜ-lower-leftᵢ cb
    ; lower-rightᶜᵢ = cᶜ-lower-rightᵢ cb
    ; maximalᶜᵢ = λ common (lower⊑D , ¬D⊑lower) →
        ¬D⊑lower (cᶜ-comparableᵢ cb common lower⊑D)
    }

comparable-idᶜᵢ :
  ∀ {Δ A B} →
  ComparableMaximalLowerBoundᵢ Δ A B →
  ComparableMaximalLowerBoundᶜᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
comparable-idᶜᵢ cb =
  record
    { cᶜ-lowerᵢ = c-lowerᵢ cb
    ; cᶜ-lower-leftᵢ = c-lower-leftᵢ cb
    ; cᶜ-lower-rightᵢ = c-lower-rightᵢ cb
    ; cᶜ-comparableᵢ = c-comparableᵢ cb
    }

comparable-unidᶜᵢ :
  ∀ {Δ A B} →
  ComparableMaximalLowerBoundᶜᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B →
  ComparableMaximalLowerBoundᵢ Δ A B
comparable-unidᶜᵢ cb =
  record
    { c-lowerᵢ = cᶜ-lowerᵢ cb
    ; c-lower-leftᵢ = cᶜ-lower-leftᵢ cb
    ; c-lower-rightᵢ = cᶜ-lower-rightᵢ cb
    ; c-comparableᵢ = cᶜ-comparableᵢ cb
    }

maximal-unidᶜᵢ :
  ∀ {Δ A B} →
  MaximalLowerBoundᶜᵢ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B →
  MaximalLowerBoundᵢ Δ A B
maximal-unidᶜᵢ mlb =
  record
    { lowerᵢ = lowerᶜᵢ mlb
    ; lower-leftᵢ = lower-leftᶜᵢ mlb
    ; lower-rightᵢ = lower-rightᶜᵢ mlb
    ; maximalᵢ = maximalᶜᵢ mlb
    }

------------------------------------------------------------------------
-- Base, star, variable, and arrow cases
------------------------------------------------------------------------

comparable-star-starᵢ :
  ∀ {Δ} →
  ComparableMaximalLowerBoundᵢ Δ ★ ★
comparable-star-starᵢ =
  record
    { c-lowerᵢ = ★
    ; c-lower-leftᵢ = id★
    ; c-lower-rightᵢ = id★
    ; c-comparableᵢ = λ common id★ → proj₁ common
    }

maximal-star-starᵢ :
  ∀ {Δ} →
  MaximalLowerBoundᵢ Δ ★ ★
maximal-star-starᵢ = comparable⇒maximalᵢ comparable-star-starᵢ

comparable-base-baseᵢ :
  ∀ {Δ ι} →
  ComparableMaximalLowerBoundᵢ Δ (‵ ι) (‵ ι)
comparable-base-baseᵢ =
  record
    { c-lowerᵢ = ‵ _
    ; c-lower-leftᵢ = idι
    ; c-lower-rightᵢ = idι
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Δ ι D} →
      CommonLowerBoundᵢ Δ (‵ ι) (‵ ι) D →
      idᵢ Δ ∣ Δ ⊢ ‵ ι ⊑ D ⊣ Δ →
      idᵢ Δ ∣ Δ ⊢ D ⊑ ‵ ι ⊣ Δ
    comparable common idι = proj₁ common
    comparable (() , _) (tag ι)

maximal-base-baseᵢ :
  ∀ {Δ ι} →
  MaximalLowerBoundᵢ Δ (‵ ι) (‵ ι)
maximal-base-baseᵢ = comparable⇒maximalᵢ comparable-base-baseᵢ

comparable-base-starᵢ :
  ∀ {Δ ι} →
  ComparableMaximalLowerBoundᵢ Δ (‵ ι) ★
comparable-base-starᵢ =
  record
    { c-lowerᵢ = ‵ _
    ; c-lower-leftᵢ = idι
    ; c-lower-rightᵢ = tag _
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Δ ι D} →
      CommonLowerBoundᵢ Δ (‵ ι) ★ D →
      idᵢ Δ ∣ Δ ⊢ ‵ ι ⊑ D ⊣ Δ →
      idᵢ Δ ∣ Δ ⊢ D ⊑ ‵ ι ⊣ Δ
    comparable common idι = proj₁ common
    comparable (() , _) (tag ι)

maximal-base-starᵢ :
  ∀ {Δ ι} →
  MaximalLowerBoundᵢ Δ (‵ ι) ★
maximal-base-starᵢ = comparable⇒maximalᵢ comparable-base-starᵢ

comparable-star-baseᵢ :
  ∀ {Δ ι} →
  ComparableMaximalLowerBoundᵢ Δ ★ (‵ ι)
comparable-star-baseᵢ =
  record
    { c-lowerᵢ = ‵ _
    ; c-lower-leftᵢ = tag _
    ; c-lower-rightᵢ = idι
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Δ ι D} →
      CommonLowerBoundᵢ Δ ★ (‵ ι) D →
      idᵢ Δ ∣ Δ ⊢ ‵ ι ⊑ D ⊣ Δ →
      idᵢ Δ ∣ Δ ⊢ D ⊑ ‵ ι ⊣ Δ
    comparable common idι = proj₂ common
    comparable (_ , ()) (tag ι)

maximal-star-baseᵢ :
  ∀ {Δ ι} →
  MaximalLowerBoundᵢ Δ ★ (‵ ι)
maximal-star-baseᵢ = comparable⇒maximalᵢ comparable-star-baseᵢ

comparable-var-varᵢ :
  ∀ {Δ X} →
  X < Δ →
  ComparableMaximalLowerBoundᵢ Δ (＇ X) (＇ X)
comparable-var-varᵢ {Δ} {X} X<Δ =
  record
    { c-lowerᵢ = ＇ X
    ; c-lower-leftᵢ = idˣ (idᵢ-lookup X<Δ) X<Δ X<Δ
    ; c-lower-rightᵢ = idˣ (idᵢ-lookup X<Δ) X<Δ X<Δ
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᵢ Δ (＇ X) (＇ X) D →
      idᵢ Δ ∣ Δ ⊢ ＇ X ⊑ D ⊣ Δ →
      idᵢ Δ ∣ Δ ⊢ D ⊑ ＇ X ⊣ Δ
    comparable common (idˣ x∈ _ _)
      rewrite idᵢ-var-identity x∈ = proj₁ common
    comparable common (tagˣ x∈ _) = ⊥-elim (idᵢ-no-star x∈)

maximal-var-varᵢ :
  ∀ {Δ X} →
  X < Δ →
  MaximalLowerBoundᵢ Δ (＇ X) (＇ X)
maximal-var-varᵢ X<Δ =
  comparable⇒maximalᵢ (comparable-var-varᵢ X<Δ)

comparable-star-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ ★
comparable-star-starᶜᵢ =
  record
    { cᶜ-lowerᵢ = ★
    ; cᶜ-lower-leftᵢ = id★
    ; cᶜ-lower-rightᵢ = id★
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ ★ D →
      Φᴼ ∣ Δᶜ ⊢ ★ ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᶜ
    comparable common id★ = id★

maximal-star-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ ★
maximal-star-starᶜᵢ = comparable⇒maximalᶜᵢ comparable-star-starᶜᵢ

comparable-base-baseᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι} →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (‵ ι) (‵ ι)
comparable-base-baseᶜᵢ =
  record
    { cᶜ-lowerᵢ = ‵ _
    ; cᶜ-lower-leftᵢ = idι
    ; cᶜ-lower-rightᵢ = idι
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) (‵ ι) D →
      Φᴼ ∣ Δᶜ ⊢ ‵ ι ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ ‵ ι ⊣ Δᶜ
    comparable common idι = idι
    comparable (() , _) (tag ι)

maximal-base-baseᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (‵ ι) (‵ ι)
maximal-base-baseᶜᵢ = comparable⇒maximalᶜᵢ comparable-base-baseᶜᵢ

comparable-base-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (‵ ι) ★
comparable-base-starᶜᵢ =
  record
    { cᶜ-lowerᵢ = ‵ _
    ; cᶜ-lower-leftᵢ = idι
    ; cᶜ-lower-rightᵢ = tag _
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) ★ D →
      Φᴼ ∣ Δᶜ ⊢ ‵ ι ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ ‵ ι ⊣ Δᶜ
    comparable common idι = idι
    comparable (() , _) (tag ι)

maximal-base-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (‵ ι) ★
maximal-base-starᶜᵢ = comparable⇒maximalᶜᵢ comparable-base-starᶜᵢ

comparable-star-baseᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (‵ ι)
comparable-star-baseᶜᵢ =
  record
    { cᶜ-lowerᵢ = ‵ _
    ; cᶜ-lower-leftᵢ = tag _
    ; cᶜ-lower-rightᵢ = idι
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (‵ ι) D →
      Φᴼ ∣ Δᶜ ⊢ ‵ ι ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ ‵ ι ⊣ Δᶜ
    comparable common idι = idι
    comparable (_ , ()) (tag ι)

maximal-star-baseᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ι} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (‵ ι)
maximal-star-baseᶜᵢ = comparable⇒maximalᶜᵢ comparable-star-baseᶜᵢ

------------------------------------------------------------------------
-- Variable lower-bound selectors under indexed contexts
------------------------------------------------------------------------

record MlbVarCtxᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx) : Set where
  field
    mlb-var-varᵢ :
      ∀ {W X Y} →
      Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
      Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
      Σ[ Z ∈ TyVar ]
        (Φᴸ ∣ Δᶜ ⊢ ＇ Z ⊑ ＇ X ⊣ Δᴸ ×
         Φᴿ ∣ Δᶜ ⊢ ＇ Z ⊑ ＇ Y ⊣ Δᴿ ×
         (∀ {W′} →
          Φᴸ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ X ⊣ Δᴸ →
          Φᴿ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ Y ⊣ Δᴿ →
          Φᴼ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ Z ⊣ Δᶜ))

    mlb-var-starᵢ :
      ∀ {W X} →
      Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
      Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ →
      Σ[ Z ∈ TyVar ]
        (Φᴸ ∣ Δᶜ ⊢ ＇ Z ⊑ ＇ X ⊣ Δᴸ ×
         Φᴿ ∣ Δᶜ ⊢ ＇ Z ⊑ ★ ⊣ Δᴿ ×
         (∀ {W′} →
          Φᴸ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ X ⊣ Δᴸ →
          Φᴿ ∣ Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ Δᴿ →
          Φᴼ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ Z ⊣ Δᶜ))

    mlb-star-varᵢ :
      ∀ {W Y} →
      Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ →
      Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
      Σ[ Z ∈ TyVar ]
        (Φᴸ ∣ Δᶜ ⊢ ＇ Z ⊑ ★ ⊣ Δᴸ ×
         Φᴿ ∣ Δᶜ ⊢ ＇ Z ⊑ ＇ Y ⊣ Δᴿ ×
         (∀ {W′} →
          Φᴸ ∣ Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ Δᴸ →
          Φᴿ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ Y ⊣ Δᴿ →
          Φᴼ ∣ Δᶜ ⊢ ＇ W′ ⊑ ＇ Z ⊣ Δᶜ))

open MlbVarCtxᵢ public

MlbVarCtx-idᵢ : ∀ Δ → MlbVarCtxᵢ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ
MlbVarCtx-idᵢ Δ .mlb-var-varᵢ
    {X = X} {Y = Y}
    (idˣ w⊑x W<Δ X<Δ) (idˣ w⊑y _ Y<Δ) =
  X ,
  idˣ (idᵢ-lookup X<Δ) X<Δ X<Δ ,
  idˣ X⊑Y X<Δ Y<Δ ,
  λ D⊑X D⊑Y → D⊑X
  where
    X⊑Y : (X ˣ⊑ˣ Y) ∈ idᵢ Δ
    X⊑Y =
      subst (λ Z → (Z ˣ⊑ˣ Y) ∈ idᵢ Δ)
        (idᵢ-var-identity w⊑x)
        w⊑y
MlbVarCtx-idᵢ Δ .mlb-var-starᵢ
    (idˣ w⊑x W<Δ X<Δ) (tagˣ w⊑★ _) =
  ⊥-elim (idᵢ-no-star w⊑★)
MlbVarCtx-idᵢ Δ .mlb-star-varᵢ
    (tagˣ w⊑★ _) (idˣ w⊑y W<Δ Y<Δ) =
  ⊥-elim (idᵢ-no-star w⊑★)

MlbVarCtx-∀∀ᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  MlbVarCtxᵢ
    (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
    (suc Δᶜ) (suc Δᴸ) (suc Δᴿ)
MlbVarCtx-∀∀ᵢ {Φᴸ} {Φᴿ} {Φᴼ} {Δᶜ} {Δᴸ} {Δᴿ} V .mlb-var-varᵢ
    (idˣ (here refl) z<s z<s) (idˣ (here refl) z<s z<s) =
  zero ,
  idˣ (here refl) z<s z<s ,
  idˣ (here refl) z<s z<s ,
  greatest
  where
    greatest :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᶜ
    greatest (idˣ (here refl) z<s z<s) (idˣ (here refl) z<s z<s) =
      idˣ (here refl) z<s z<s
    greatest (idˣ (here refl) _ _) (idˣ (there w⊑0) _ _) =
      ⊥-elim (no-⇑ᵢ-zero-left w⊑0)
    greatest (idˣ (there w⊑0) _ _) _ =
      ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-varᵢ
    (idˣ (here refl) _ _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-varᵢ
    (idˣ (there w⊑x) _ _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀∀ᵢ V .mlb-var-varᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀∀ᵢ V .mlb-var-varᵢ
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ᵢ V .mlb-var-varᵢ
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-varᵢ
    {W = suc W} {X = suc X} {Y = suc Y}
    (idˣ (there w⊑x) (s<s W<Δᶜ) (s<s X<Δᴸ))
    (idˣ (there w⊑y) _ (s<s Y<Δᴿ)) =
  suc (proj₁ selected) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-varᵢ V
        (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc X ⊣ suc Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc Y ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) (s<s X<Δᴸ))
        (idˣ (there w′⊑y) _ (s<s Y<Δᴿ)) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-starᵢ
    (idˣ (here refl) _ _) (tagˣ (here ()) _)
MlbVarCtx-∀∀ᵢ V .mlb-var-starᵢ
    (idˣ (here refl) _ _) (tagˣ (there w⊑★) _) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀∀ᵢ V .mlb-var-starᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀∀ᵢ V .mlb-var-starᵢ
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-starᵢ
    {W = suc W} {X = suc X}
    (idˣ (there w⊑x) (s<s W<Δᶜ) (s<s X<Δᴸ))
    (tagˣ (there w⊑★) _) =
  suc (proj₁ selected) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ selected)) ,
  liftˣ★∀ᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-starᵢ V
        (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δᶜ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc X ⊣ suc Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) (s<s X<Δᴸ))
        (tagˣ (there w′⊑★) _) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (tagˣ (un⇑ᵢ-★∈ w′⊑★) W′<Δᶜ))
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-star-varᵢ
    (tagˣ (here ()) _) q
MlbVarCtx-∀∀ᵢ V .mlb-star-varᵢ
    (tagˣ (there w⊑★) _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀∀ᵢ V .mlb-star-varᵢ
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀∀ᵢ V .mlb-star-varᵢ
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-star-varᵢ
    {W = suc W} {Y = suc Y}
    (tagˣ (there w⊑★) (s<s W<Δᶜ))
    (idˣ (there w⊑y) _ (s<s Y<Δᴿ)) =
  suc (proj₁ selected) ,
  liftˣ★∀ᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-star-varᵢ V
        (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δᶜ)
        (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ suc Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc Y ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (tagˣ (there w′⊑★) _) q =
      ⊥-elim (no-⇑ᵢ-zero-star w′⊑★)
    greatest′ {W′ = suc W′}
        (tagˣ (there w′⊑★) (s<s W′<Δᶜ))
        (idˣ (there w′⊑y) _ (s<s Y<Δᴿ)) =
      liftˣˣ∀ᵢ
        (greatest
          (tagˣ (un⇑ᵢ-★∈ w′⊑★) W′<Δᶜ)
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))

MlbVarCtx-∀νᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  MlbVarCtxᵢ
    (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
    (suc Δᶜ) (suc Δᴸ) Δᴿ
MlbVarCtx-∀νᵢ V .mlb-var-varᵢ
    (idˣ (here refl) _ _) (idˣ (here ()) _ _)
MlbVarCtx-∀νᵢ V .mlb-var-varᵢ
    (idˣ (here refl) _ _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
MlbVarCtx-∀νᵢ V .mlb-var-varᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀νᵢ V .mlb-var-varᵢ
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀νᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-varᵢ
    {W = suc W} {X = suc X}
    (idˣ (there w⊑x) (s<s W<Δᶜ) (s<s X<Δᴸ))
    (idˣ (there w⊑y) _ Y<Δᴿ) =
  suc (proj₁ selected) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣνᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-varᵢ V
        (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc X ⊣ suc Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) (s<s X<Δᴸ))
        (idˣ (there w′⊑y) _ Y<Δᴿ) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))
MlbVarCtx-∀νᵢ V .mlb-var-starᵢ
    (idˣ (here refl) z<s z<s) (tagˣ (here refl) z<s) =
  zero ,
  idˣ (here refl) z<s z<s ,
  tagˣ (here refl) z<s ,
  greatest
  where
    greatest :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᶜ
    greatest (idˣ (here refl) z<s z<s) (tagˣ (here refl) z<s) =
      idˣ (here refl) z<s z<s
    greatest (idˣ (here refl) _ _) (tagˣ (there w⊑★) _) =
      ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
    greatest (idˣ (there w⊑0) _ _) q =
      ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀νᵢ V .mlb-var-starᵢ
    (idˣ (here refl) _ _) (tagˣ (there w⊑★) _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
MlbVarCtx-∀νᵢ V .mlb-var-starᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
MlbVarCtx-∀νᵢ V .mlb-var-starᵢ
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-∀νᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-starᵢ
    {W = suc W} {X = suc X}
    (idˣ (there w⊑x) (s<s W<Δᶜ) (s<s X<Δᴸ))
    (tagˣ (there w⊑★) _) =
  suc (proj₁ selected) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ selected)) ,
  liftˣ★νᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-starᵢ V
        (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δᶜ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc X ⊣ suc Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) (s<s X<Δᴸ))
        (tagˣ (there w′⊑★) _) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (tagˣ (un⇑ᴸᵢ-★∈ w′⊑★) W′<Δᶜ))
MlbVarCtx-∀νᵢ V .mlb-star-varᵢ
    (tagˣ (here ()) _) q
MlbVarCtx-∀νᵢ V .mlb-star-varᵢ
    p (idˣ (here ()) _ _)
MlbVarCtx-∀νᵢ V .mlb-star-varᵢ
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
MlbVarCtx-∀νᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-star-varᵢ
    {W = suc W}
    (tagˣ (there w⊑★) (s<s W<Δᶜ))
    (idˣ (there w⊑y) _ Y<Δᴿ) =
  suc (proj₁ selected) ,
  liftˣ★∀ᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣνᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-star-varᵢ V
        (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δᶜ)
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ suc Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (tagˣ (there w′⊑★) _) q =
      ⊥-elim (no-⇑ᵢ-zero-star w′⊑★)
    greatest′ {W′ = suc W′}
        (tagˣ (there w′⊑★) (s<s W′<Δᶜ))
        (idˣ (there w′⊑y) _ Y<Δᴿ) =
      liftˣˣ∀ᵢ
        (greatest
          (tagˣ (un⇑ᵢ-★∈ w′⊑★) W′<Δᶜ)
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))

MlbVarCtx-ν∀ᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  MlbVarCtxᵢ
    (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
    (suc Δᶜ) Δᴸ (suc Δᴿ)
MlbVarCtx-ν∀ᵢ V .mlb-var-varᵢ
    (idˣ (here ()) _ _) q
MlbVarCtx-ν∀ᵢ V .mlb-var-varᵢ
    (idˣ (there w⊑x) _ _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ν∀ᵢ V .mlb-var-varᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ν∀ᵢ V .mlb-var-varᵢ
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-ν∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-varᵢ
    {W = suc W} {Y = suc Y}
    (idˣ (there w⊑x) (s<s W<Δᶜ) X<Δᴸ)
    (idˣ (there w⊑y) _ (s<s Y<Δᴿ)) =
  suc (proj₁ selected) ,
  liftˣˣνᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-varᵢ V
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc Y ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) X<Δᴸ)
        (idˣ (there w′⊑y) _ (s<s Y<Δᴿ)) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))
MlbVarCtx-ν∀ᵢ V .mlb-var-starᵢ
    (idˣ (here ()) _ _) q
MlbVarCtx-ν∀ᵢ V .mlb-var-starᵢ
    p (tagˣ (here ()) _)
MlbVarCtx-ν∀ᵢ V .mlb-var-starᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ν∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-starᵢ
    {W = suc W}
    (idˣ (there w⊑x) (s<s W<Δᶜ) X<Δᴸ)
    (tagˣ (there w⊑★) _) =
  suc (proj₁ selected) ,
  liftˣˣνᵢ (proj₁ (proj₂ selected)) ,
  liftˣ★∀ᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-starᵢ V
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δᶜ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) X<Δᴸ)
        (tagˣ (there w′⊑★) _) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (tagˣ (un⇑ᵢ-★∈ w′⊑★) W′<Δᶜ))
MlbVarCtx-ν∀ᵢ V .mlb-star-varᵢ
    (tagˣ (here refl) z<s) (idˣ (here refl) z<s z<s) =
  zero ,
  tagˣ (here refl) z<s ,
  idˣ (here refl) z<s z<s ,
  greatest
  where
    greatest :
      ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ ＇ W ⊑ ＇ zero ⊣ suc Δᶜ
    greatest (tagˣ (here refl) z<s) (idˣ (here refl) z<s z<s) =
      idˣ (here refl) z<s z<s
    greatest (tagˣ (here refl) _) (idˣ (there w⊑0) _ _) =
      ⊥-elim (no-⇑ᵢ-zero-left w⊑0)
    greatest {W = zero} (tagˣ (there w⊑★) _) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
    greatest {W = suc W} p (idˣ (there w⊑0) _ _) =
      ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-ν∀ᵢ V .mlb-star-varᵢ
    (tagˣ (here refl) _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
MlbVarCtx-ν∀ᵢ V .mlb-star-varᵢ
    (tagˣ (there w⊑★) _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
MlbVarCtx-ν∀ᵢ V .mlb-star-varᵢ
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
MlbVarCtx-ν∀ᵢ V .mlb-star-varᵢ
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
MlbVarCtx-ν∀ᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-star-varᵢ
    {W = suc W} {Y = suc Y}
    (tagˣ (there w⊑★) (s<s W<Δᶜ))
    (idˣ (there w⊑y) _ (s<s Y<Δᴿ)) =
  suc (proj₁ selected) ,
  liftˣ★νᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣ∀ᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-star-varᵢ V
        (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δᶜ)
        (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ suc Y ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ {W′ = zero} (tagˣ (there w′⊑★) _) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-star w′⊑★)
    greatest′ {W′ = zero} (tagˣ (here refl) _) (idˣ (there w′⊑y) _ _) =
      ⊥-elim (no-⇑ᵢ-zero-left w′⊑y)
    greatest′ {W′ = suc W′}
        (tagˣ (there w′⊑★) (s<s W′<Δᶜ))
        (idˣ (there w′⊑y) _ (s<s Y<Δᴿ)) =
      liftˣˣ∀ᵢ
        (greatest
          (tagˣ (un⇑ᴸᵢ-★∈ w′⊑★) W′<Δᶜ)
          (idˣ (un⇑ᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))

MlbVarCtx-ννᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  MlbVarCtxᵢ
    (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
    (suc Δᶜ) Δᴸ Δᴿ
MlbVarCtx-ννᵢ V .mlb-var-varᵢ
    (idˣ (here ()) _ _) q
MlbVarCtx-ννᵢ V .mlb-var-varᵢ
    p (idˣ (here ()) _ _)
MlbVarCtx-ννᵢ V .mlb-var-varᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ννᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-varᵢ
    {W = suc W}
    (idˣ (there w⊑x) (s<s W<Δᶜ) X<Δᴸ)
    (idˣ (there w⊑y) _ Y<Δᴿ) =
  suc (proj₁ selected) ,
  liftˣˣνᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣνᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-varᵢ V
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ (idˣ (here ()) _ _) q
    greatest′ p (idˣ (here ()) _ _)
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) X<Δᴸ)
        (idˣ (there w′⊑y) _ Y<Δᴿ) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))
MlbVarCtx-ννᵢ V .mlb-var-starᵢ
    (idˣ (here ()) _ _) q
MlbVarCtx-ννᵢ V .mlb-var-starᵢ
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
MlbVarCtx-ννᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-var-starᵢ
    {W = suc W}
    (idˣ (there w⊑x) (s<s W<Δᶜ) X<Δᴸ)
    (tagˣ (there w⊑★) _) =
  suc (proj₁ selected) ,
  liftˣˣνᵢ (proj₁ (proj₂ selected)) ,
  liftˣ★νᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-var-starᵢ V
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δᶜ X<Δᴸ)
        (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δᶜ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ (idˣ (here ()) _ _) q
    greatest′ {W′ = zero} (idˣ (there w′⊑x) _ _) q =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑x)
    greatest′ {W′ = suc W′}
        (idˣ (there w′⊑x) (s<s W′<Δᶜ) X<Δᴸ)
        (tagˣ (there w′⊑★) _) =
      liftˣˣ∀ᵢ
        (greatest
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑x) W′<Δᶜ X<Δᴸ)
          (tagˣ (un⇑ᴸᵢ-★∈ w′⊑★) W′<Δᶜ))
MlbVarCtx-ννᵢ V .mlb-star-varᵢ
    p (idˣ (here ()) _ _)
MlbVarCtx-ννᵢ V .mlb-star-varᵢ
    {W = zero} p (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
MlbVarCtx-ννᵢ {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    V .mlb-star-varᵢ
    {W = suc W}
    (tagˣ (there w⊑★) (s<s W<Δᶜ))
    (idˣ (there w⊑y) _ Y<Δᴿ) =
  suc (proj₁ selected) ,
  liftˣ★νᵢ (proj₁ (proj₂ selected)) ,
  liftˣˣνᵢ (proj₁ (proj₂ (proj₂ selected))) ,
  greatest′
  where
    selected =
      mlb-star-varᵢ V
        (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δᶜ)
        (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δᶜ Y<Δᴿ)

    greatest = proj₂ (proj₂ (proj₂ selected))

    greatest′ :
      ∀ {W′} →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ★ ⊣ Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ ＇ W′ ⊑ ＇ _ ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ
        ⊢ ＇ W′ ⊑ ＇ suc (proj₁ selected) ⊣ suc Δᶜ
    greatest′ p (idˣ (here ()) _ _)
    greatest′ {W′ = zero} p (idˣ (there w′⊑y) _ _) =
      ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑y)
    greatest′ {W′ = suc W′}
        (tagˣ (there w′⊑★) (s<s W′<Δᶜ))
        (idˣ (there w′⊑y) _ Y<Δᴿ) =
      liftˣˣ∀ᵢ
        (greatest
          (tagˣ (un⇑ᴸᵢ-★∈ w′⊑★) W′<Δᶜ)
          (idˣ (un⇑ᴸᵢ-ˣ∈ w′⊑y) W′<Δᶜ Y<Δᴿ))

data MlbCtxᵢ :
    ImpCtx → ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Set where
  idᵐᵢ :
    ∀ Δ →
    MlbCtxᵢ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ

  lift∀∀ᵐᵢ :
    ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
    MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
    MlbCtxᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ)

  lift∀νᵐᵢ :
    ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
    MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
    MlbCtxᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ

  liftν∀ᵐᵢ :
    ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
    MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
    MlbCtxᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ)

  liftννᵐᵢ :
    ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
    MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
    MlbCtxᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ

MlbCtx-varsᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ
MlbCtx-varsᵢ (idᵐᵢ Δ) = MlbVarCtx-idᵢ Δ
MlbCtx-varsᵢ (lift∀∀ᵐᵢ Ψ) = MlbVarCtx-∀∀ᵢ (MlbCtx-varsᵢ Ψ)
MlbCtx-varsᵢ (lift∀νᵐᵢ Ψ) = MlbVarCtx-∀νᵢ (MlbCtx-varsᵢ Ψ)
MlbCtx-varsᵢ (liftν∀ᵐᵢ Ψ) = MlbVarCtx-ν∀ᵢ (MlbCtx-varsᵢ Ψ)
MlbCtx-varsᵢ (liftννᵐᵢ Ψ) = MlbVarCtx-ννᵢ (MlbCtx-varsᵢ Ψ)

------------------------------------------------------------------------
-- Lower-bound-driven candidate selector
------------------------------------------------------------------------

data MlbModeᵢ : Set where
  bothᵢ : MlbModeᵢ
  leftOnlyᵢ : MlbModeᵢ
  rightOnlyᵢ : MlbModeᵢ
  neitherᵢ : MlbModeᵢ

MlbChoiceCtxᵢ : Set
MlbChoiceCtxᵢ = List MlbModeᵢ

data ModeAtᵢ : MlbChoiceCtxᵢ → TyVar → MlbModeᵢ → Set where
  hereᵐᵢ :
    ∀ {Γ m} →
    ModeAtᵢ (m ∷ Γ) zero m

  thereᵐᵢ :
    ∀ {Γ X m n} →
    ModeAtᵢ Γ X m →
    ModeAtᵢ (n ∷ Γ) (suc X) m

leftChoiceᵢ : MlbChoiceCtxᵢ → ImpCtx
leftChoiceᵢ [] = []
leftChoiceᵢ (bothᵢ ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (leftChoiceᵢ Γ)
leftChoiceᵢ (leftOnlyᵢ ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (leftChoiceᵢ Γ)
leftChoiceᵢ (rightOnlyᵢ ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (leftChoiceᵢ Γ)
leftChoiceᵢ (neitherᵢ ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (leftChoiceᵢ Γ)

rightChoiceᵢ : MlbChoiceCtxᵢ → ImpCtx
rightChoiceᵢ [] = []
rightChoiceᵢ (bothᵢ ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (rightChoiceᵢ Γ)
rightChoiceᵢ (leftOnlyᵢ ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (rightChoiceᵢ Γ)
rightChoiceᵢ (rightOnlyᵢ ∷ Γ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (rightChoiceᵢ Γ)
rightChoiceᵢ (neitherᵢ ∷ Γ) = (zero ˣ⊑★) ∷ ⇑ᴸᵢ (rightChoiceᵢ Γ)

choiceCommonCtxᵢ : MlbChoiceCtxᵢ → TyCtx
choiceCommonCtxᵢ [] = zero
choiceCommonCtxᵢ (_ ∷ Γ) = suc (choiceCommonCtxᵢ Γ)

choiceLeftCtxᵢ : MlbChoiceCtxᵢ → TyCtx
choiceLeftCtxᵢ [] = zero
choiceLeftCtxᵢ (bothᵢ ∷ Γ) = suc (choiceLeftCtxᵢ Γ)
choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ) = suc (choiceLeftCtxᵢ Γ)
choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ) = choiceLeftCtxᵢ Γ
choiceLeftCtxᵢ (neitherᵢ ∷ Γ) = choiceLeftCtxᵢ Γ

choiceRightCtxᵢ : MlbChoiceCtxᵢ → TyCtx
choiceRightCtxᵢ [] = zero
choiceRightCtxᵢ (bothᵢ ∷ Γ) = suc (choiceRightCtxᵢ Γ)
choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ) = choiceRightCtxᵢ Γ
choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ) = suc (choiceRightCtxᵢ Γ)
choiceRightCtxᵢ (neitherᵢ ∷ Γ) = choiceRightCtxᵢ Γ

choice-mlbctxᵢ :
  ∀ Γ →
  MlbCtxᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
choice-mlbctxᵢ [] = idᵐᵢ zero
choice-mlbctxᵢ (bothᵢ ∷ Γ) = lift∀∀ᵐᵢ (choice-mlbctxᵢ Γ)
choice-mlbctxᵢ (leftOnlyᵢ ∷ Γ) = lift∀νᵐᵢ (choice-mlbctxᵢ Γ)
choice-mlbctxᵢ (rightOnlyᵢ ∷ Γ) = liftν∀ᵐᵢ (choice-mlbctxᵢ Γ)
choice-mlbctxᵢ (neitherᵢ ∷ Γ) = liftννᵐᵢ (choice-mlbctxᵢ Γ)

choice-idᵢ : TyCtx → MlbChoiceCtxᵢ
choice-idᵢ zero = []
choice-idᵢ (suc Δ) = bothᵢ ∷ choice-idᵢ Δ

choice-id-commonCtxᵢ : ∀ Δ → choiceCommonCtxᵢ (choice-idᵢ Δ) ≡ Δ
choice-id-commonCtxᵢ zero = refl
choice-id-commonCtxᵢ (suc Δ) = cong suc (choice-id-commonCtxᵢ Δ)

choice-id-leftCtxᵢ : ∀ Δ → choiceLeftCtxᵢ (choice-idᵢ Δ) ≡ Δ
choice-id-leftCtxᵢ zero = refl
choice-id-leftCtxᵢ (suc Δ) = cong suc (choice-id-leftCtxᵢ Δ)

choice-id-rightCtxᵢ : ∀ Δ → choiceRightCtxᵢ (choice-idᵢ Δ) ≡ Δ
choice-id-rightCtxᵢ zero = refl
choice-id-rightCtxᵢ (suc Δ) = cong suc (choice-id-rightCtxᵢ Δ)

leftChoice-idᵢ : ∀ Δ → leftChoiceᵢ (choice-idᵢ Δ) ≡ idᵢ Δ
leftChoice-idᵢ zero = refl
leftChoice-idᵢ (suc Δ) =
  cong (λ Φ → (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (leftChoice-idᵢ Δ)

rightChoice-idᵢ : ∀ Δ → rightChoiceᵢ (choice-idᵢ Δ) ≡ idᵢ Δ
rightChoice-idᵢ zero = refl
rightChoice-idᵢ (suc Δ) =
  cong (λ Φ → (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (rightChoice-idᵢ Δ)

leftChoice-id-proofAtᵢ :
  ∀ {Δ C A} →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ →
  leftChoiceᵢ (choice-idᵢ Δ) ∣ Δ ⊢ C ⊑ A ⊣ Δ
leftChoice-id-proofAtᵢ id★ = id★
leftChoice-id-proofAtᵢ {Δ = Δ} (idˣ x∈ X<Δ Y<Δ) =
  idˣ
    (subst (λ Φ → _ ∈ Φ) (sym (leftChoice-idᵢ Δ)) x∈)
    X<Δ
    Y<Δ
leftChoice-id-proofAtᵢ idι = idι
leftChoice-id-proofAtᵢ (p ↦ q) =
  leftChoice-id-proofAtᵢ p ↦ leftChoice-id-proofAtᵢ q
leftChoice-id-proofAtᵢ (∀ⁱ p) = ∀ⁱ leftChoice-id-proofAtᵢ p
leftChoice-id-proofAtᵢ (tag ι) = tag ι
leftChoice-id-proofAtᵢ (tag p ⇛ q) =
  tag (leftChoice-id-proofAtᵢ p) ⇛ leftChoice-id-proofAtᵢ q
leftChoice-id-proofAtᵢ {Δ = Δ} (tagˣ x∈ X<Δ) =
  tagˣ
    (subst (λ Φ → _ ∈ Φ) (sym (leftChoice-idᵢ Δ)) x∈)
    X<Δ
leftChoice-id-proofAtᵢ {Δ = Δ} (ν {A = A} {B = B} occ p) =
  ν occ
    (subst
      (λ Φ → Φ ∣ suc Δ ⊢ A ⊑ B ⊣ Δ)
      (cong (λ Φ → (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (sym (leftChoice-idᵢ Δ)))
      p)

rightChoice-id-proofAtᵢ :
  ∀ {Δ C B} →
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ →
  rightChoiceᵢ (choice-idᵢ Δ) ∣ Δ ⊢ C ⊑ B ⊣ Δ
rightChoice-id-proofAtᵢ id★ = id★
rightChoice-id-proofAtᵢ {Δ = Δ} (idˣ x∈ X<Δ Y<Δ) =
  idˣ
    (subst (λ Φ → _ ∈ Φ) (sym (rightChoice-idᵢ Δ)) x∈)
    X<Δ
    Y<Δ
rightChoice-id-proofAtᵢ idι = idι
rightChoice-id-proofAtᵢ (p ↦ q) =
  rightChoice-id-proofAtᵢ p ↦ rightChoice-id-proofAtᵢ q
rightChoice-id-proofAtᵢ (∀ⁱ p) = ∀ⁱ rightChoice-id-proofAtᵢ p
rightChoice-id-proofAtᵢ (tag ι) = tag ι
rightChoice-id-proofAtᵢ (tag p ⇛ q) =
  tag (rightChoice-id-proofAtᵢ p) ⇛ rightChoice-id-proofAtᵢ q
rightChoice-id-proofAtᵢ {Δ = Δ} (tagˣ x∈ X<Δ) =
  tagˣ
    (subst (λ Φ → _ ∈ Φ) (sym (rightChoice-idᵢ Δ)) x∈)
    X<Δ
rightChoice-id-proofAtᵢ {Δ = Δ} (ν {A = A} {B = B} occ p) =
  ν occ
    (subst
      (λ Φ → Φ ∣ suc Δ ⊢ A ⊑ B ⊣ Δ)
      (cong (λ Φ → (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (sym (rightChoice-idᵢ Δ)))
      p)

rightChoice-leftOnly-id-proofAtᵢ :
  ∀ {Δ C B} →
  νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ Δ →
  rightChoiceᵢ (leftOnlyᵢ ∷ choice-idᵢ Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ Δ
rightChoice-leftOnly-id-proofAtᵢ {Δ = Δ} {C = C} {B = B} p =
  subst
    (λ Φ → Φ ∣ suc Δ ⊢ C ⊑ B ⊣ Δ)
    (cong (λ Φ → (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (sym (rightChoice-idᵢ Δ)))
    p

leftChoice-rightOnly-id-proofAtᵢ :
  ∀ {Δ C A} →
  νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ Δ →
  leftChoiceᵢ (rightOnlyᵢ ∷ choice-idᵢ Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ Δ
leftChoice-rightOnly-id-proofAtᵢ {Δ = Δ} {C = C} {A = A} p =
  subst
    (λ Φ → Φ ∣ suc Δ ⊢ C ⊑ A ⊣ Δ)
    (cong (λ Φ → (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (sym (leftChoice-idᵢ Δ)))
    p

leftChoice-neither-id-proofAtᵢ :
  ∀ {Δ C A} →
  νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ Δ →
  leftChoiceᵢ (neitherᵢ ∷ choice-idᵢ Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ Δ
leftChoice-neither-id-proofAtᵢ {Δ = Δ} {C = C} {A = A} p =
  subst
    (λ Φ → Φ ∣ suc Δ ⊢ C ⊑ A ⊣ Δ)
    (cong (λ Φ → (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (sym (leftChoice-idᵢ Δ)))
    p

rightChoice-neither-id-proofAtᵢ :
  ∀ {Δ C B} →
  νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ Δ →
  rightChoiceᵢ (neitherᵢ ∷ choice-idᵢ Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ Δ
rightChoice-neither-id-proofAtᵢ {Δ = Δ} {C = C} {B = B} p =
  subst
    (λ Φ → Φ ∣ suc Δ ⊢ C ⊑ B ⊣ Δ)
    (cong (λ Φ → (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (sym (rightChoice-idᵢ Δ)))
    p

leftChoice-id-proofAt⁻ᵢ :
  ∀ {Δ C A} →
  leftChoiceᵢ (choice-idᵢ Δ) ∣ Δ ⊢ C ⊑ A ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ
leftChoice-id-proofAt⁻ᵢ {Δ = Δ} p rewrite leftChoice-idᵢ Δ = p

rightChoice-id-proofAt⁻ᵢ :
  ∀ {Δ C B} →
  rightChoiceᵢ (choice-idᵢ Δ) ∣ Δ ⊢ C ⊑ B ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
rightChoice-id-proofAt⁻ᵢ {Δ = Δ} q rewrite rightChoice-idᵢ Δ = q

leftChoice-id-proofᵢ :
  ∀ {Δ C A} →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ →
  leftChoiceᵢ (choice-idᵢ Δ)
    ∣ choiceCommonCtxᵢ (choice-idᵢ Δ)
    ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (choice-idᵢ Δ)
leftChoice-id-proofᵢ {Δ = Δ} {C = C} {A = A} p =
  subst
    (λ Δᴸ →
      leftChoiceᵢ (choice-idᵢ Δ)
        ∣ choiceCommonCtxᵢ (choice-idᵢ Δ)
        ⊢ C ⊑ A ⊣ Δᴸ)
    (sym (choice-id-leftCtxᵢ Δ))
    (subst
      (λ Δᶜ →
        leftChoiceᵢ (choice-idᵢ Δ) ∣ Δᶜ ⊢ C ⊑ A ⊣ Δ)
      (sym (choice-id-commonCtxᵢ Δ))
      (leftChoice-id-proofAtᵢ p))

rightChoice-id-proofᵢ :
  ∀ {Δ C B} →
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ →
  rightChoiceᵢ (choice-idᵢ Δ)
    ∣ choiceCommonCtxᵢ (choice-idᵢ Δ)
    ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (choice-idᵢ Δ)
rightChoice-id-proofᵢ {Δ = Δ} {C = C} {B = B} q =
  subst
    (λ Δᴿ →
      rightChoiceᵢ (choice-idᵢ Δ)
        ∣ choiceCommonCtxᵢ (choice-idᵢ Δ)
        ⊢ C ⊑ B ⊣ Δᴿ)
    (sym (choice-id-rightCtxᵢ Δ))
    (subst
      (λ Δᶜ →
        rightChoiceᵢ (choice-idᵢ Δ) ∣ Δᶜ ⊢ C ⊑ B ⊣ Δ)
      (sym (choice-id-commonCtxᵢ Δ))
      (rightChoice-id-proofAtᵢ q))

leftChoice-id-proof⁻ᵢ :
  ∀ {Δ C A} →
  leftChoiceᵢ (choice-idᵢ Δ)
    ∣ choiceCommonCtxᵢ (choice-idᵢ Δ)
    ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (choice-idᵢ Δ) →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ
leftChoice-id-proof⁻ᵢ {Δ = Δ} p
    rewrite leftChoice-idᵢ Δ
          | choice-id-commonCtxᵢ Δ
          | choice-id-leftCtxᵢ Δ =
  p

rightChoice-id-proof⁻ᵢ :
  ∀ {Δ C B} →
  rightChoiceᵢ (choice-idᵢ Δ)
    ∣ choiceCommonCtxᵢ (choice-idᵢ Δ)
    ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (choice-idᵢ Δ) →
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
rightChoice-id-proof⁻ᵢ {Δ = Δ} q
    rewrite rightChoice-idᵢ Δ
          | choice-id-commonCtxᵢ Δ
          | choice-id-rightCtxᵢ Δ =
  q

choice-var-varᵢ :
  ∀ Γ {W X Y} →
  (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ →
  (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ →
  TyVar
choice-var-varᵢ [] ()
choice-var-varᵢ (bothᵢ ∷ Γ) (here refl) (here refl) = zero
choice-var-varᵢ (bothᵢ ∷ Γ) (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-var-varᵢ (bothᵢ ∷ Γ) (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-varᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-varᵢ (bothᵢ ∷ Γ) {W = suc W} {X = zero} (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-varᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-varᵢ (bothᵢ ∷ Γ) {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  suc (choice-var-varᵢ Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y))
choice-var-varᵢ (leftOnlyᵢ ∷ Γ) (here refl) (here ())
choice-var-varᵢ (leftOnlyᵢ ∷ Γ) (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-var-varᵢ (leftOnlyᵢ ∷ Γ) (there w⊑x) (here ())
choice-var-varᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-varᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-varᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑y) =
  suc (choice-var-varᵢ Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y))
choice-var-varᵢ (rightOnlyᵢ ∷ Γ) (here ()) q
choice-var-varᵢ (rightOnlyᵢ ∷ Γ) (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-varᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-varᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-varᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  suc (choice-var-varᵢ Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-ˣ∈ w⊑y))
choice-var-varᵢ (neitherᵢ ∷ Γ) (here ()) q
choice-var-varᵢ (neitherᵢ ∷ Γ) p (here ())
choice-var-varᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-varᵢ (neitherᵢ ∷ Γ) {W = suc W} (there w⊑x)
    (there w⊑y) =
  suc (choice-var-varᵢ Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y))

choice-var-var-leftᵢ :
  ∀ Γ {Δᶜ Δᴸ W X Y} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  X < Δᴸ →
  leftChoiceᵢ Γ ∣ Δᶜ
    ⊢ ＇ choice-var-varᵢ Γ w⊑x w⊑y ⊑ ＇ X ⊣ Δᴸ
choice-var-var-leftᵢ [] ()
choice-var-var-leftᵢ (bothᵢ ∷ Γ) (here refl) (here refl) W<Δ X<Δ =
  idˣ (here refl) W<Δ X<Δ
choice-var-var-leftᵢ (bothᵢ ∷ Γ) (here refl) (there w⊑y) W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-var-var-leftᵢ (bothᵢ ∷ Γ) (there w⊑x) (here refl) W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var-leftᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑x) q W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var-leftᵢ (bothᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-var-leftᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-var-var-leftᵢ (bothᵢ ∷ Γ) {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑x) (there w⊑y) (s<s W<Δ) (s<s X<Δ) =
  liftˣˣ∀ᵢ
    (choice-var-var-leftᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ
      X<Δ)
choice-var-var-leftᵢ (leftOnlyᵢ ∷ Γ) (here refl) (here ()) W<Δ X<Δ
choice-var-var-leftᵢ (leftOnlyᵢ ∷ Γ) (here refl) (there w⊑y)
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-var-var-leftᵢ (leftOnlyᵢ ∷ Γ) (there w⊑x) (here ()) W<Δ X<Δ
choice-var-var-leftᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var-leftᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-var-leftᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑y) (s<s W<Δ) (s<s X<Δ) =
  liftˣˣ∀ᵢ
    (choice-var-var-leftᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ
      X<Δ)
choice-var-var-leftᵢ (rightOnlyᵢ ∷ Γ) (here ()) q W<Δ X<Δ
choice-var-var-leftᵢ (rightOnlyᵢ ∷ Γ) (there w⊑x) (here refl)
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var-leftᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var-leftᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-var-var-leftᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑x) (there w⊑y) (s<s W<Δ) X<Δ =
  liftˣˣνᵢ
    (choice-var-var-leftᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ
      X<Δ)
choice-var-var-leftᵢ (neitherᵢ ∷ Γ) (here ()) q W<Δ X<Δ
choice-var-var-leftᵢ (neitherᵢ ∷ Γ) p (here ()) W<Δ X<Δ
choice-var-var-leftᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var-leftᵢ (neitherᵢ ∷ Γ) {W = suc W}
    (there w⊑x) (there w⊑y) (s<s W<Δ) X<Δ =
  liftˣˣνᵢ
    (choice-var-var-leftᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ
      X<Δ)

choice-var-var-rightᵢ :
  ∀ Γ {Δᶜ Δᴿ W X Y} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  Y < Δᴿ →
  rightChoiceᵢ Γ ∣ Δᶜ
    ⊢ ＇ choice-var-varᵢ Γ w⊑x w⊑y ⊑ ＇ Y ⊣ Δᴿ
choice-var-var-rightᵢ [] ()
choice-var-var-rightᵢ (bothᵢ ∷ Γ) (here refl) (here refl) W<Δ Y<Δ =
  idˣ (here refl) W<Δ Y<Δ
choice-var-var-rightᵢ (bothᵢ ∷ Γ) (here refl) (there w⊑y)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-var-var-rightᵢ (bothᵢ ∷ Γ) (there w⊑x) (here refl)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var-rightᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var-rightᵢ (bothᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-var-rightᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-var-var-rightᵢ (bothᵢ ∷ Γ) {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑x) (there w⊑y) (s<s W<Δ) (s<s Y<Δ) =
  liftˣˣ∀ᵢ
    (choice-var-var-rightᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)
choice-var-var-rightᵢ (leftOnlyᵢ ∷ Γ) (here refl) (here ()) W<Δ Y<Δ
choice-var-var-rightᵢ (leftOnlyᵢ ∷ Γ) (here refl) (there w⊑y)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-var-var-rightᵢ (leftOnlyᵢ ∷ Γ) (there w⊑x) (here ()) W<Δ Y<Δ
choice-var-var-rightᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-var-rightᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-var-rightᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑y) (s<s W<Δ) Y<Δ =
  liftˣˣνᵢ
    (choice-var-var-rightᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)
choice-var-var-rightᵢ (rightOnlyᵢ ∷ Γ) (here ()) q W<Δ Y<Δ
choice-var-var-rightᵢ (rightOnlyᵢ ∷ Γ) (there w⊑x) (here refl)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var-rightᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var-rightᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-var-var-rightᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑x) (there w⊑y) (s<s W<Δ) (s<s Y<Δ) =
  liftˣˣ∀ᵢ
    (choice-var-var-rightᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)
choice-var-var-rightᵢ (neitherᵢ ∷ Γ) (here ()) q W<Δ Y<Δ
choice-var-var-rightᵢ (neitherᵢ ∷ Γ) p (here ()) W<Δ Y<Δ
choice-var-var-rightᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-var-rightᵢ (neitherᵢ ∷ Γ) {W = suc W}
    (there w⊑x) (there w⊑y) (s<s W<Δ) Y<Δ =
  liftˣˣνᵢ
    (choice-var-var-rightᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)

choice-var-var-commonᵢ :
  ∀ Γ {Δᶜ Δᴸ Δᴿ W X Y} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  X < Δᴸ →
  Y < Δᴿ →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y)
    (＇ choice-var-varᵢ Γ w⊑x w⊑y)
choice-var-var-commonᵢ Γ w⊑x w⊑y W<Δ X<Δ Y<Δ =
  choice-var-var-leftᵢ Γ w⊑x w⊑y W<Δ X<Δ ,
  choice-var-var-rightᵢ Γ w⊑x w⊑y W<Δ Y<Δ

choice-var-starᵢ :
  ∀ Γ {W X} →
  (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ →
  (W ˣ⊑★) ∈ rightChoiceᵢ Γ →
  TyVar
choice-var-starᵢ [] ()
choice-var-starᵢ (bothᵢ ∷ Γ) (here refl) (here ())
choice-var-starᵢ (bothᵢ ∷ Γ) (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-var-starᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-starᵢ (bothᵢ ∷ Γ) {W = suc W} {X = zero} (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-starᵢ (bothᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) =
  suc (choice-var-starᵢ Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★))
choice-var-starᵢ (leftOnlyᵢ ∷ Γ) (here refl) (here refl) = zero
choice-var-starᵢ (leftOnlyᵢ ∷ Γ) (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-var-starᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-starᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑0) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-var-starᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) =
  suc (choice-var-starᵢ Γ (un⇑ᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★))
choice-var-starᵢ (rightOnlyᵢ ∷ Γ) (here ()) q
choice-var-starᵢ (rightOnlyᵢ ∷ Γ) p (here ())
choice-var-starᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-starᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} (there w⊑x)
    (there w⊑★) =
  suc (choice-var-starᵢ Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᵢ-★∈ w⊑★))
choice-var-starᵢ (neitherᵢ ∷ Γ) (here ()) q
choice-var-starᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑x) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-starᵢ (neitherᵢ ∷ Γ) {W = suc W} (there w⊑x)
    (there w⊑★) =
  suc (choice-var-starᵢ Γ (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★))

choice-var-star-leftᵢ :
  ∀ Γ {Δᶜ Δᴸ W X} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ) →
  (w⊑★ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  X < Δᴸ →
  leftChoiceᵢ Γ ∣ Δᶜ
    ⊢ ＇ choice-var-starᵢ Γ w⊑x w⊑★ ⊑ ＇ X ⊣ Δᴸ
choice-var-star-leftᵢ [] ()
choice-var-star-leftᵢ (bothᵢ ∷ Γ) (here refl) (here ()) W<Δ X<Δ
choice-var-star-leftᵢ (bothᵢ ∷ Γ) (here refl) (there w⊑★)
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-var-star-leftᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-star-leftᵢ (bothᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-star-leftᵢ (bothᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) (s<s W<Δ) (s<s X<Δ) =
  liftˣˣ∀ᵢ
    (choice-var-star-leftᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-★∈ w⊑★)
      W<Δ
      X<Δ)
choice-var-star-leftᵢ (leftOnlyᵢ ∷ Γ) (here refl) (here refl)
    W<Δ X<Δ =
  idˣ (here refl) W<Δ X<Δ
choice-var-star-leftᵢ (leftOnlyᵢ ∷ Γ) (here refl) (there w⊑★)
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-var-star-leftᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-star-leftᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ X<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-star-leftᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) (s<s W<Δ) (s<s X<Δ) =
  liftˣˣ∀ᵢ
    (choice-var-star-leftᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-★∈ w⊑★)
      W<Δ
      X<Δ)
choice-var-star-leftᵢ (rightOnlyᵢ ∷ Γ) (here ()) q W<Δ X<Δ
choice-var-star-leftᵢ (rightOnlyᵢ ∷ Γ) p (here ()) W<Δ X<Δ
choice-var-star-leftᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-star-leftᵢ (rightOnlyᵢ ∷ Γ) {W = suc W}
    (there w⊑x) (there w⊑★) (s<s W<Δ) X<Δ =
  liftˣˣνᵢ
    (choice-var-star-leftᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-★∈ w⊑★)
      W<Δ
      X<Δ)
choice-var-star-leftᵢ (neitherᵢ ∷ Γ) (here ()) q W<Δ X<Δ
choice-var-star-leftᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ X<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-star-leftᵢ (neitherᵢ ∷ Γ) {W = suc W}
    (there w⊑x) (there w⊑★) (s<s W<Δ) X<Δ =
  liftˣˣνᵢ
    (choice-var-star-leftᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-★∈ w⊑★)
      W<Δ
      X<Δ)

choice-var-star-rightᵢ :
  ∀ Γ {Δᶜ Δᴿ W X} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ) →
  (w⊑★ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  rightChoiceᵢ Γ ∣ Δᶜ
    ⊢ ＇ choice-var-starᵢ Γ w⊑x w⊑★ ⊑ ★ ⊣ Δᴿ
choice-var-star-rightᵢ [] ()
choice-var-star-rightᵢ (bothᵢ ∷ Γ) (here refl) (here ()) W<Δ
choice-var-star-rightᵢ (bothᵢ ∷ Γ) (here refl) (there w⊑★) W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-var-star-rightᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑x) q W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-star-rightᵢ (bothᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-star-rightᵢ (bothᵢ ∷ Γ) {Δᶜ = suc Δᶜ} {Δᴿ = Δᴿ}
    {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) (s<s W<Δ) =
  liftˣ★∀ᵢ-any {Δᴸ = Δᶜ} {Δᴿ = Δᴿ} {Δᴼ = Δᴿ}
    (choice-var-star-rightᵢ Γ {Δᶜ = Δᶜ} {Δᴿ = Δᴿ}
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-★∈ w⊑★)
      W<Δ)
choice-var-star-rightᵢ (leftOnlyᵢ ∷ Γ) (here refl) (here refl) W<Δ =
  tagˣ (here refl) W<Δ
choice-var-star-rightᵢ (leftOnlyᵢ ∷ Γ) (here refl) (there w⊑★) W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-var-star-rightᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q
    W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-var-star-rightᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = zero}
    (there w⊑x) q W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-var-star-rightᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} {X = suc X}
    (there w⊑x) (there w⊑★) (s<s W<Δ) =
  liftˣ★νᵢ
    (choice-var-star-rightᵢ Γ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-★∈ w⊑★)
      W<Δ)
choice-var-star-rightᵢ (rightOnlyᵢ ∷ Γ) (here ()) q W<Δ
choice-var-star-rightᵢ (rightOnlyᵢ ∷ Γ) p (here ()) W<Δ
choice-var-star-rightᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑x) q W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-star-rightᵢ (rightOnlyᵢ ∷ Γ) {Δᶜ = suc Δᶜ} {Δᴿ = Δᴿ}
    {W = suc W} (there w⊑x) (there w⊑★) (s<s W<Δ) =
  liftˣ★∀ᵢ-any {Δᴸ = Δᶜ} {Δᴿ = Δᴿ} {Δᴼ = Δᴿ}
    (choice-var-star-rightᵢ Γ {Δᶜ = Δᶜ} {Δᴿ = Δᴿ}
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-★∈ w⊑★)
      W<Δ)
choice-var-star-rightᵢ (neitherᵢ ∷ Γ) (here ()) q W<Δ
choice-var-star-rightᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑x) q W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-var-star-rightᵢ (neitherᵢ ∷ Γ) {W = suc W}
    (there w⊑x) (there w⊑★) (s<s W<Δ) =
  liftˣ★νᵢ
    (choice-var-star-rightᵢ Γ
      (un⇑ᴸᵢ-ˣ∈ w⊑x)
      (un⇑ᴸᵢ-★∈ w⊑★)
      W<Δ)

choice-var-star-commonᵢ :
  ∀ Γ {Δᶜ Δᴸ Δᴿ W X} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ) →
  (w⊑★ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  X < Δᴸ →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    Δᶜ Δᴸ Δᴿ (＇ X) ★
    (＇ choice-var-starᵢ Γ w⊑x w⊑★)
choice-var-star-commonᵢ Γ w⊑x w⊑★ W<Δ X<Δ =
  choice-var-star-leftᵢ Γ w⊑x w⊑★ W<Δ X<Δ ,
  choice-var-star-rightᵢ Γ w⊑x w⊑★ W<Δ

choice-star-varᵢ :
  ∀ Γ {W Y} →
  (W ˣ⊑★) ∈ leftChoiceᵢ Γ →
  (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ →
  TyVar
choice-star-varᵢ [] ()
choice-star-varᵢ (bothᵢ ∷ Γ) (here ()) q
choice-star-varᵢ (bothᵢ ∷ Γ) (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-varᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-varᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-star-varᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) =
  suc (choice-star-varᵢ Γ (un⇑ᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y))
choice-star-varᵢ (leftOnlyᵢ ∷ Γ) (here ()) q
choice-star-varᵢ (leftOnlyᵢ ∷ Γ) p (here ())
choice-star-varᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-varᵢ (leftOnlyᵢ ∷ Γ) {W = suc W} (there w⊑★)
    (there w⊑y) =
  suc (choice-star-varᵢ Γ (un⇑ᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y))
choice-star-varᵢ (rightOnlyᵢ ∷ Γ) (here refl) (here refl) = zero
choice-star-varᵢ (rightOnlyᵢ ∷ Γ) (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-star-varᵢ (rightOnlyᵢ ∷ Γ) (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-varᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-varᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-star-varᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) =
  suc (choice-star-varᵢ Γ (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑y))
choice-star-varᵢ (neitherᵢ ∷ Γ) p (here ())
choice-star-varᵢ (neitherᵢ ∷ Γ) {W = zero} (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-star-varᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑★) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-varᵢ (neitherᵢ ∷ Γ) {W = suc W} (there w⊑★)
    (there w⊑y) =
  suc (choice-star-varᵢ Γ (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y))

choice-star-var-leftᵢ :
  ∀ Γ {Δᶜ Δᴸ W Y} →
  (w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  leftChoiceᵢ Γ ∣ Δᶜ
    ⊢ ＇ choice-star-varᵢ Γ w⊑★ w⊑y ⊑ ★ ⊣ Δᴸ
choice-star-var-leftᵢ [] ()
choice-star-var-leftᵢ (bothᵢ ∷ Γ) (here ()) q W<Δ
choice-star-var-leftᵢ (bothᵢ ∷ Γ) (there w⊑★) (here refl) W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var-leftᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑★) q W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var-leftᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-star-var-leftᵢ (bothᵢ ∷ Γ) {Δᴸ = Δᴸ} {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) (s<s W<Δ) =
  liftˣ★∀ᵢ-any {Δᴿ = Δᴸ} {Δᴼ = Δᴸ}
    (choice-star-var-leftᵢ Γ {Δᴸ = Δᴸ}
      (un⇑ᵢ-★∈ w⊑★)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ)
choice-star-var-leftᵢ (leftOnlyᵢ ∷ Γ) (here ()) q W<Δ
choice-star-var-leftᵢ (leftOnlyᵢ ∷ Γ) p (here ()) W<Δ
choice-star-var-leftᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑★) q W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var-leftᵢ (leftOnlyᵢ ∷ Γ) {Δᴸ = Δᴸ} {W = suc W}
    (there w⊑★) (there w⊑y) (s<s W<Δ) =
  liftˣ★∀ᵢ-any {Δᴿ = Δᴸ} {Δᴼ = Δᴸ}
    (choice-star-var-leftᵢ Γ {Δᴸ = Δᴸ}
      (un⇑ᵢ-★∈ w⊑★)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ)
choice-star-var-leftᵢ (rightOnlyᵢ ∷ Γ) (here refl) (here refl) W<Δ =
  tagˣ (here refl) W<Δ
choice-star-var-leftᵢ (rightOnlyᵢ ∷ Γ) (here refl) (there w⊑y) W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-star-var-leftᵢ (rightOnlyᵢ ∷ Γ) (there w⊑★) (here refl) W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var-leftᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑★) q
    W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var-leftᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-star-var-leftᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) (s<s W<Δ) =
  liftˣ★νᵢ
    (choice-star-var-leftᵢ Γ
      (un⇑ᴸᵢ-★∈ w⊑★)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ)
choice-star-var-leftᵢ (neitherᵢ ∷ Γ) p (here ()) W<Δ
choice-star-var-leftᵢ (neitherᵢ ∷ Γ) {W = zero} (here refl)
    (there w⊑y) W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-star-var-leftᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑★) q W<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var-leftᵢ (neitherᵢ ∷ Γ) {W = suc W}
    (there w⊑★) (there w⊑y) (s<s W<Δ) =
  liftˣ★νᵢ
    (choice-star-var-leftᵢ Γ
      (un⇑ᴸᵢ-★∈ w⊑★)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ)

choice-star-var-rightᵢ :
  ∀ Γ {Δᶜ Δᴿ W Y} →
  (w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  Y < Δᴿ →
  rightChoiceᵢ Γ ∣ Δᶜ
    ⊢ ＇ choice-star-varᵢ Γ w⊑★ w⊑y ⊑ ＇ Y ⊣ Δᴿ
choice-star-var-rightᵢ [] ()
choice-star-var-rightᵢ (bothᵢ ∷ Γ) (here ()) q W<Δ Y<Δ
choice-star-var-rightᵢ (bothᵢ ∷ Γ) (there w⊑★) (here refl)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var-rightᵢ (bothᵢ ∷ Γ) {W = zero} (there w⊑★) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var-rightᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-star-var-rightᵢ (bothᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) (s<s W<Δ) (s<s Y<Δ) =
  liftˣˣ∀ᵢ
    (choice-star-var-rightᵢ Γ
      (un⇑ᵢ-★∈ w⊑★)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)
choice-star-var-rightᵢ (leftOnlyᵢ ∷ Γ) (here ()) q W<Δ Y<Δ
choice-star-var-rightᵢ (leftOnlyᵢ ∷ Γ) p (here ()) W<Δ Y<Δ
choice-star-var-rightᵢ (leftOnlyᵢ ∷ Γ) {W = zero} (there w⊑★) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-star-var-rightᵢ (leftOnlyᵢ ∷ Γ) {W = suc W}
    (there w⊑★) (there w⊑y) (s<s W<Δ) Y<Δ =
  liftˣˣνᵢ
    (choice-star-var-rightᵢ Γ
      (un⇑ᵢ-★∈ w⊑★)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)
choice-star-var-rightᵢ (rightOnlyᵢ ∷ Γ) (here refl) (here refl)
    W<Δ Y<Δ =
  idˣ (here refl) W<Δ Y<Δ
choice-star-var-rightᵢ (rightOnlyᵢ ∷ Γ) (here refl) (there w⊑y)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-star-var-rightᵢ (rightOnlyᵢ ∷ Γ) (there w⊑★) (here refl)
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var-rightᵢ (rightOnlyᵢ ∷ Γ) {W = zero} (there w⊑★) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var-rightᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = zero} p
    (there w⊑y) W<Δ Y<Δ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-star-var-rightᵢ (rightOnlyᵢ ∷ Γ) {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑y) (s<s W<Δ) (s<s Y<Δ) =
  liftˣˣ∀ᵢ
    (choice-star-var-rightᵢ Γ
      (un⇑ᴸᵢ-★∈ w⊑★)
      (un⇑ᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)
choice-star-var-rightᵢ (neitherᵢ ∷ Γ) p (here ()) W<Δ Y<Δ
choice-star-var-rightᵢ (neitherᵢ ∷ Γ) {W = zero} (here refl)
    (there w⊑y) W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-star-var-rightᵢ (neitherᵢ ∷ Γ) {W = zero} (there w⊑★) q
    W<Δ Y<Δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-star-var-rightᵢ (neitherᵢ ∷ Γ) {W = suc W}
    (there w⊑★) (there w⊑y) (s<s W<Δ) Y<Δ =
  liftˣˣνᵢ
    (choice-star-var-rightᵢ Γ
      (un⇑ᴸᵢ-★∈ w⊑★)
      (un⇑ᴸᵢ-ˣ∈ w⊑y)
      W<Δ
      Y<Δ)

choice-star-var-commonᵢ :
  ∀ Γ {Δᶜ Δᴸ Δᴿ W Y} →
  (w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  W < Δᶜ →
  Y < Δᴿ →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    Δᶜ Δᴸ Δᴿ ★ (＇ Y)
    (＇ choice-star-varᵢ Γ w⊑★ w⊑y)
choice-star-var-commonᵢ Γ w⊑★ w⊑y W<Δ Y<Δ =
  choice-star-var-leftᵢ Γ w⊑★ w⊑y W<Δ ,
  choice-star-var-rightᵢ Γ w⊑★ w⊑y W<Δ Y<Δ

rightChoice-no-var-at-leftOnlyᵢ :
  ∀ {Γ X Y} →
  ModeAtᵢ Γ X leftOnlyᵢ →
  (X ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ →
  ⊥
rightChoice-no-var-at-leftOnlyᵢ hereᵐᵢ (here ())
rightChoice-no-var-at-leftOnlyᵢ hereᵐᵢ (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
rightChoice-no-var-at-leftOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (here ())
rightChoice-no-var-at-leftOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = bothᵢ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
rightChoice-no-var-at-leftOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {n = bothᵢ} mode) (there x∈) =
  rightChoice-no-var-at-leftOnlyᵢ mode (un⇑ᵢ-ˣ∈ x∈)
rightChoice-no-var-at-leftOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (here ())
rightChoice-no-var-at-leftOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (there x∈) =
  rightChoice-no-var-at-leftOnlyᵢ mode (un⇑ᴸᵢ-ˣ∈ x∈)
rightChoice-no-var-at-leftOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (here ())
rightChoice-no-var-at-leftOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = rightOnlyᵢ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
rightChoice-no-var-at-leftOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {n = rightOnlyᵢ} mode) (there x∈) =
  rightChoice-no-var-at-leftOnlyᵢ mode (un⇑ᵢ-ˣ∈ x∈)
rightChoice-no-var-at-leftOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (here ())
rightChoice-no-var-at-leftOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (there x∈) =
  rightChoice-no-var-at-leftOnlyᵢ mode (un⇑ᴸᵢ-ˣ∈ x∈)

leftChoice-no-star-at-leftOnlyᵢ :
  ∀ {Γ X} →
  ModeAtᵢ Γ X leftOnlyᵢ →
  (X ˣ⊑★) ∈ leftChoiceᵢ Γ →
  ⊥
leftChoice-no-star-at-leftOnlyᵢ hereᵐᵢ (here ())
leftChoice-no-star-at-leftOnlyᵢ hereᵐᵢ (there x∈) =
  no-⇑ᵢ-zero-star x∈
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (here ())
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (there x∈) =
  leftChoice-no-star-at-leftOnlyᵢ mode (un⇑ᵢ-★∈ x∈)
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (here ())
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (there x∈) =
  leftChoice-no-star-at-leftOnlyᵢ mode (un⇑ᵢ-★∈ x∈)
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (here ())
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (there x∈) =
  leftChoice-no-star-at-leftOnlyᵢ mode (un⇑ᴸᵢ-★∈ x∈)
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (here ())
leftChoice-no-star-at-leftOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (there x∈) =
  leftChoice-no-star-at-leftOnlyᵢ mode (un⇑ᴸᵢ-★∈ x∈)

leftChoice-no-var-at-rightOnlyᵢ :
  ∀ {Γ X Y} →
  ModeAtᵢ Γ X rightOnlyᵢ →
  (X ˣ⊑ˣ Y) ∈ leftChoiceᵢ Γ →
  ⊥
leftChoice-no-var-at-rightOnlyᵢ hereᵐᵢ (here ())
leftChoice-no-var-at-rightOnlyᵢ hereᵐᵢ (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
leftChoice-no-var-at-rightOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (here ())
leftChoice-no-var-at-rightOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = bothᵢ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
leftChoice-no-var-at-rightOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {n = bothᵢ} mode) (there x∈) =
  leftChoice-no-var-at-rightOnlyᵢ mode (un⇑ᵢ-ˣ∈ x∈)
leftChoice-no-var-at-rightOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (here ())
leftChoice-no-var-at-rightOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = leftOnlyᵢ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
leftChoice-no-var-at-rightOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {n = leftOnlyᵢ} mode) (there x∈) =
  leftChoice-no-var-at-rightOnlyᵢ mode (un⇑ᵢ-ˣ∈ x∈)
leftChoice-no-var-at-rightOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (here ())
leftChoice-no-var-at-rightOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (there x∈) =
  leftChoice-no-var-at-rightOnlyᵢ mode (un⇑ᴸᵢ-ˣ∈ x∈)
leftChoice-no-var-at-rightOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (here ())
leftChoice-no-var-at-rightOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (there x∈) =
  leftChoice-no-var-at-rightOnlyᵢ mode (un⇑ᴸᵢ-ˣ∈ x∈)

rightChoice-no-star-at-rightOnlyᵢ :
  ∀ {Γ X} →
  ModeAtᵢ Γ X rightOnlyᵢ →
  (X ˣ⊑★) ∈ rightChoiceᵢ Γ →
  ⊥
rightChoice-no-star-at-rightOnlyᵢ hereᵐᵢ (here ())
rightChoice-no-star-at-rightOnlyᵢ hereᵐᵢ (there x∈) =
  no-⇑ᵢ-zero-star x∈
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (here ())
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (there x∈) =
  rightChoice-no-star-at-rightOnlyᵢ mode (un⇑ᵢ-★∈ x∈)
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (here ())
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (there x∈) =
  rightChoice-no-star-at-rightOnlyᵢ mode (un⇑ᴸᵢ-★∈ x∈)
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (here ())
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (there x∈) =
  rightChoice-no-star-at-rightOnlyᵢ mode (un⇑ᵢ-★∈ x∈)
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (here ())
rightChoice-no-star-at-rightOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (there x∈) =
  rightChoice-no-star-at-rightOnlyᵢ mode (un⇑ᴸᵢ-★∈ x∈)

choice-var-star-occurs-leftOnlyᵢ :
  ∀ {Γ X Y} →
  ModeAtᵢ Γ X leftOnlyᵢ →
  (x⊑y : (X ˣ⊑ˣ Y) ∈ leftChoiceᵢ Γ) →
  (x⊑★ : (X ˣ⊑★) ∈ rightChoiceᵢ Γ) →
  occurs X (＇ choice-var-starᵢ Γ x⊑y x⊑★) ≡ true
choice-var-star-occurs-leftOnlyᵢ hereᵐᵢ (here refl) (here refl) =
  refl
choice-var-star-occurs-leftOnlyᵢ hereᵐᵢ (here refl) (there x⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★)
choice-var-star-occurs-leftOnlyᵢ hereᵐᵢ (there x⊑y) x⊑★ =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
choice-var-star-occurs-leftOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (here ()) x⊑★
choice-var-star-occurs-leftOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = bothᵢ} mode) (there x⊑y) x⊑★ =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
choice-var-star-occurs-leftOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {X = X} {n = bothᵢ} mode) (there x⊑y) (here ())
choice-var-star-occurs-leftOnlyᵢ {Γ = bothᵢ ∷ Γ} {Y = suc Y}
    (thereᵐᵢ {X = X} {n = bothᵢ} mode) (there x⊑y) (there x⊑★) =
  trans (sym (occurs-suc-var X
    (choice-var-starᵢ Γ (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-★∈ x⊑★))))
    (choice-var-star-occurs-leftOnlyᵢ mode
      (un⇑ᵢ-ˣ∈ x⊑y)
      (un⇑ᵢ-★∈ x⊑★))
choice-var-star-occurs-leftOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (here ()) x⊑★
choice-var-star-occurs-leftOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = leftOnlyᵢ} mode) (there x⊑y) x⊑★ =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
choice-var-star-occurs-leftOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {X = X} {n = leftOnlyᵢ} mode) (there x⊑y) (here ())
choice-var-star-occurs-leftOnlyᵢ {Γ = leftOnlyᵢ ∷ Γ} {Y = suc Y}
    (thereᵐᵢ {X = X} {n = leftOnlyᵢ} mode) (there x⊑y) (there x⊑★) =
  trans (sym (occurs-suc-var X
    (choice-var-starᵢ Γ (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-★∈ x⊑★))))
    (choice-var-star-occurs-leftOnlyᵢ mode
      (un⇑ᵢ-ˣ∈ x⊑y)
      (un⇑ᴸᵢ-★∈ x⊑★))
choice-var-star-occurs-leftOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (here ()) x⊑★
choice-var-star-occurs-leftOnlyᵢ
    (thereᵐᵢ {X = X} {n = rightOnlyᵢ} mode) (there x⊑y) (here ())
choice-var-star-occurs-leftOnlyᵢ {Γ = rightOnlyᵢ ∷ Γ}
    (thereᵐᵢ {X = X} {n = rightOnlyᵢ} mode) (there x⊑y) (there x⊑★) =
  trans (sym (occurs-suc-var X
    (choice-var-starᵢ Γ (un⇑ᴸᵢ-ˣ∈ x⊑y) (un⇑ᵢ-★∈ x⊑★))))
    (choice-var-star-occurs-leftOnlyᵢ mode
      (un⇑ᴸᵢ-ˣ∈ x⊑y)
      (un⇑ᵢ-★∈ x⊑★))
choice-var-star-occurs-leftOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (here ()) x⊑★
choice-var-star-occurs-leftOnlyᵢ {Γ = neitherᵢ ∷ Γ}
    (thereᵐᵢ {X = X} {n = neitherᵢ} mode) (there x⊑y) (there x⊑★) =
  trans (sym (occurs-suc-var X
    (choice-var-starᵢ Γ (un⇑ᴸᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-★∈ x⊑★))))
    (choice-var-star-occurs-leftOnlyᵢ mode
      (un⇑ᴸᵢ-ˣ∈ x⊑y)
      (un⇑ᴸᵢ-★∈ x⊑★))

choice-star-var-occurs-rightOnlyᵢ :
  ∀ {Γ X Y} →
  ModeAtᵢ Γ X rightOnlyᵢ →
  (x⊑★ : (X ˣ⊑★) ∈ leftChoiceᵢ Γ) →
  (x⊑y : (X ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ) →
  occurs X (＇ choice-star-varᵢ Γ x⊑★ x⊑y) ≡ true
choice-star-var-occurs-rightOnlyᵢ hereᵐᵢ (here refl) (here refl) =
  refl
choice-star-var-occurs-rightOnlyᵢ hereᵐᵢ (here refl) (there x⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
choice-star-var-occurs-rightOnlyᵢ hereᵐᵢ (there x⊑★) x⊑y =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★)
choice-star-var-occurs-rightOnlyᵢ (thereᵐᵢ {n = bothᵢ} mode)
    (here ()) x⊑y
choice-star-var-occurs-rightOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = bothᵢ} mode) x⊑★ (there x⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
choice-star-var-occurs-rightOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {X = X} {n = bothᵢ} mode) (there x⊑★) (here ())
choice-star-var-occurs-rightOnlyᵢ {Γ = bothᵢ ∷ Γ} {Y = suc Y}
    (thereᵐᵢ {X = X} {n = bothᵢ} mode) (there x⊑★) (there x⊑y) =
  trans (sym (occurs-suc-var X
    (choice-star-varᵢ Γ (un⇑ᵢ-★∈ x⊑★) (un⇑ᵢ-ˣ∈ x⊑y))))
    (choice-star-var-occurs-rightOnlyᵢ mode
      (un⇑ᵢ-★∈ x⊑★)
      (un⇑ᵢ-ˣ∈ x⊑y))
choice-star-var-occurs-rightOnlyᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode)
    (here ()) x⊑y
choice-star-var-occurs-rightOnlyᵢ
    (thereᵐᵢ {X = X} {n = leftOnlyᵢ} mode) (there x⊑★) (here ())
choice-star-var-occurs-rightOnlyᵢ {Γ = leftOnlyᵢ ∷ Γ}
    (thereᵐᵢ {X = X} {n = leftOnlyᵢ} mode) (there x⊑★) (there x⊑y) =
  trans (sym (occurs-suc-var X
    (choice-star-varᵢ Γ (un⇑ᵢ-★∈ x⊑★) (un⇑ᴸᵢ-ˣ∈ x⊑y))))
    (choice-star-var-occurs-rightOnlyᵢ mode
      (un⇑ᵢ-★∈ x⊑★)
      (un⇑ᴸᵢ-ˣ∈ x⊑y))
choice-star-var-occurs-rightOnlyᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode)
    (here ()) x⊑y
choice-star-var-occurs-rightOnlyᵢ {Y = zero}
    (thereᵐᵢ {n = rightOnlyᵢ} mode) x⊑★ (there x⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
choice-star-var-occurs-rightOnlyᵢ {Y = suc Y}
    (thereᵐᵢ {X = X} {n = rightOnlyᵢ} mode) (there x⊑★) (here ())
choice-star-var-occurs-rightOnlyᵢ {Γ = rightOnlyᵢ ∷ Γ} {Y = suc Y}
    (thereᵐᵢ {X = X} {n = rightOnlyᵢ} mode) (there x⊑★) (there x⊑y) =
  trans (sym (occurs-suc-var X
    (choice-star-varᵢ Γ (un⇑ᴸᵢ-★∈ x⊑★) (un⇑ᵢ-ˣ∈ x⊑y))))
    (choice-star-var-occurs-rightOnlyᵢ mode
      (un⇑ᴸᵢ-★∈ x⊑★)
      (un⇑ᵢ-ˣ∈ x⊑y))
choice-star-var-occurs-rightOnlyᵢ (thereᵐᵢ {n = neitherᵢ} mode)
    (there x⊑★) (here ())
choice-star-var-occurs-rightOnlyᵢ {Γ = neitherᵢ ∷ Γ}
    (thereᵐᵢ {X = X} {n = neitherᵢ} mode) (there x⊑★) (there x⊑y) =
  trans (sym (occurs-suc-var X
    (choice-star-varᵢ Γ (un⇑ᴸᵢ-★∈ x⊑★) (un⇑ᴸᵢ-ˣ∈ x⊑y))))
    (choice-star-var-occurs-rightOnlyᵢ mode
      (un⇑ᴸᵢ-★∈ x⊑★)
      (un⇑ᴸᵢ-ˣ∈ x⊑y))

close-neitherᵢ : Ty → Ty
close-neitherᵢ A with occurs zero A
close-neitherᵢ A | true = `∀ A
close-neitherᵢ A | false = A [ zero ]ᴿ

mlb-typeᵢ :
  ∀ {Γ Δᶜ Δᴸ Δᴿ A B C} →
  leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
  rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
  Ty
mlb-typeᵢ {Γ = Γ} id★ id★ = ★
mlb-typeᵢ {Γ = Γ} (idˣ w⊑x _ _) (idˣ w⊑y _ _) =
  ＇ choice-var-varᵢ Γ w⊑x w⊑y
mlb-typeᵢ {Γ = Γ} (idι {ι = ι}) idι = ‵ ι
mlb-typeᵢ {Γ = Γ} idι (tag ι) = ‵ ι
mlb-typeᵢ {Γ = Γ} (p₁ ↦ p₂) (q₁ ↦ q₂) =
  mlb-typeᵢ p₁ q₁ ⇒ mlb-typeᵢ p₂ q₂
mlb-typeᵢ {Γ = Γ} (p₁ ↦ p₂) (tag_⇛_ q₁ q₂) =
  mlb-typeᵢ p₁ q₁ ⇒ mlb-typeᵢ p₂ q₂
mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q) =
  `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (ν occ q) =
  `∀ (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q)
mlb-typeᵢ {Γ = Γ} (tag ι) idι = ‵ ι
mlb-typeᵢ {Γ = Γ} (tag ι) (tag .ι) = ★
mlb-typeᵢ {Γ = Γ} (tag_⇛_ p₁ p₂) (q₁ ↦ q₂) =
  mlb-typeᵢ p₁ q₁ ⇒ mlb-typeᵢ p₂ q₂
mlb-typeᵢ {Γ = Γ} (tag_⇛_ p₁ p₂) (tag_⇛_ q₁ q₂) = ★
mlb-typeᵢ {Γ = Γ} (tagˣ w⊑★ _) (idˣ w⊑y _ _) =
  ＇ choice-star-varᵢ Γ w⊑★ w⊑y
mlb-typeᵢ {Γ = Γ} (tagˣ w⊑★ _) (tagˣ w⊑★′ _) = ★
mlb-typeᵢ {Γ = Γ} (ν occ p) (∀ⁱ q) =
  `∀ (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q)
mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q) =
  close-neitherᵢ (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q)
mlb-typeᵢ {Γ = Γ} (idˣ w⊑x _ _) (tagˣ w⊑★ _) =
  ＇ choice-var-starᵢ Γ w⊑x w⊑★

occurs-var-true→≡ᵢ :
  ∀ {X Y} →
  occurs X (＇ Y) ≡ true →
  Y ≡ X
occurs-var-true→≡ᵢ {X = X} {Y = Y} occ with X ≟ Y
occurs-var-true→≡ᵢ {X = X} {Y = .X} occ | yes refl = refl
occurs-var-true→≡ᵢ {X = X} {Y = Y} () | no neq

close-neither-occursᵢ :
  ∀ {X A} →
  occurs (suc X) A ≡ true →
  occurs X (close-neitherᵢ A) ≡ true
close-neither-occursᵢ {X = X} {A = A} occ with occurs zero A
close-neither-occursᵢ {X = X} {A = A} occ | true = occ
close-neither-occursᵢ {X = X} {A = A} occ | false =
  occurs-removeAt-raiseᵢ zero X A occ

no-occurs-star-leftOnlyAtᵢ :
  ∀ {Γ X Δᶜ Δᴿ C} →
  ModeAtᵢ Γ X leftOnlyᵢ →
  occurs X C ≡ true →
  leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ ★ ⊣ Δᴿ →
  ⊥
no-occurs-star-leftOnlyAtᵢ mode () id★
no-occurs-star-leftOnlyAtᵢ mode () (tag ι)
no-occurs-star-leftOnlyAtᵢ {X = X} mode occ
    (tag_⇛_ {A₁ = C₁} p q)
    with occurs X C₁ in occ₁
no-occurs-star-leftOnlyAtᵢ {X = X} mode occ
    (tag_⇛_ {A₁ = C₁} p q) | true =
  no-occurs-star-leftOnlyAtᵢ mode occ₁ p
no-occurs-star-leftOnlyAtᵢ {X = X} mode occ
    (tag_⇛_ {A₁ = C₁} p q) | false =
  no-occurs-star-leftOnlyAtᵢ mode occ q
no-occurs-star-leftOnlyAtᵢ mode occ (tagˣ x⊑★ X<Δ)
    with occurs-var-true→≡ᵢ occ
no-occurs-star-leftOnlyAtᵢ mode occ (tagˣ x⊑★ X<Δ) | refl =
  leftChoice-no-star-at-leftOnlyᵢ mode x⊑★
no-occurs-star-leftOnlyAtᵢ mode occ (ν occC p) =
  no-occurs-star-leftOnlyAtᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode) occ p

no-occurs-star-rightOnlyAtᵢ :
  ∀ {Γ X Δᶜ Δᴿ C} →
  ModeAtᵢ Γ X rightOnlyᵢ →
  occurs X C ≡ true →
  rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ ★ ⊣ Δᴿ →
  ⊥
no-occurs-star-rightOnlyAtᵢ mode () id★
no-occurs-star-rightOnlyAtᵢ mode () (tag ι)
no-occurs-star-rightOnlyAtᵢ {X = X} mode occ
    (tag_⇛_ {A₁ = C₁} p q)
    with occurs X C₁ in occ₁
no-occurs-star-rightOnlyAtᵢ {X = X} mode occ
    (tag_⇛_ {A₁ = C₁} p q) | true =
  no-occurs-star-rightOnlyAtᵢ mode occ₁ p
no-occurs-star-rightOnlyAtᵢ {X = X} mode occ
    (tag_⇛_ {A₁ = C₁} p q) | false =
  no-occurs-star-rightOnlyAtᵢ mode occ q
no-occurs-star-rightOnlyAtᵢ mode occ (tagˣ x⊑★ X<Δ)
    with occurs-var-true→≡ᵢ occ
no-occurs-star-rightOnlyAtᵢ mode occ (tagˣ x⊑★ X<Δ) | refl =
  rightChoice-no-star-at-rightOnlyᵢ mode x⊑★
no-occurs-star-rightOnlyAtᵢ mode occ (ν occC p) =
  no-occurs-star-rightOnlyAtᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode) occ p

mlb-type-occurs-leftOnlyAtᵢ :
  ∀ {Γ X Δᶜ Δᴸ Δᴿ A B C} →
  ModeAtᵢ Γ X leftOnlyᵢ →
  (p : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ) →
  (q : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ) →
  occurs X C ≡ true →
  occurs X (mlb-typeᵢ {Γ = Γ} p q) ≡ true
mlb-type-occurs-leftOnlyAtᵢ mode id★ id★ ()
mlb-type-occurs-leftOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (idˣ w⊑y _ Y<Δ) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-leftOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (idˣ w⊑y _ Y<Δ) occ | refl =
  ⊥-elim (rightChoice-no-var-at-leftOnlyᵢ mode w⊑y)
mlb-type-occurs-leftOnlyAtᵢ mode idι idι ()
mlb-type-occurs-leftOnlyAtᵢ mode idι (tag ι) ()
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (q₁ ↦ q₂) occ
    with occurs X C₁ in occ₁
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (q₁ ↦ q₂) occ | true =
  ∨-true-leftᵢ (mlb-type-occurs-leftOnlyAtᵢ mode p₁ q₁ occ₁)
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (q₁ ↦ q₂) occ | false =
  ∨-true-rightᵢ (mlb-type-occurs-leftOnlyAtᵢ mode p₂ q₂ occ)
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (tag q₁ ⇛ q₂) occ
    with occurs X C₁ in occ₁
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (tag q₁ ⇛ q₂) occ | true =
  ∨-true-leftᵢ (mlb-type-occurs-leftOnlyAtᵢ mode p₁ q₁ occ₁)
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (tag q₁ ⇛ q₂) occ | false =
  ∨-true-rightᵢ (mlb-type-occurs-leftOnlyAtᵢ mode p₂ q₂ occ)
mlb-type-occurs-leftOnlyAtᵢ mode (∀ⁱ p) (∀ⁱ q) occ =
  mlb-type-occurs-leftOnlyAtᵢ (thereᵐᵢ {n = bothᵢ} mode) p q occ
mlb-type-occurs-leftOnlyAtᵢ mode (∀ⁱ p) (ν occC q) occ =
  mlb-type-occurs-leftOnlyAtᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode) p q occ
mlb-type-occurs-leftOnlyAtᵢ mode (tag ι) idι ()
mlb-type-occurs-leftOnlyAtᵢ mode (tag ι) (tag .ι) ()
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (tag_⇛_ {A₁ = C₁} p₁ p₂) (q₁ ↦ q₂) occ
    with occurs X C₁ in occ₁
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (tag_⇛_ {A₁ = C₁} p₁ p₂) (q₁ ↦ q₂) occ | true =
  ∨-true-leftᵢ (mlb-type-occurs-leftOnlyAtᵢ mode p₁ q₁ occ₁)
mlb-type-occurs-leftOnlyAtᵢ {X = X} mode
    (tag_⇛_ {A₁ = C₁} p₁ p₂) (q₁ ↦ q₂) occ | false =
  ∨-true-rightᵢ (mlb-type-occurs-leftOnlyAtᵢ mode p₂ q₂ occ)
mlb-type-occurs-leftOnlyAtᵢ mode (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ =
  ⊥-elim (no-occurs-star-leftOnlyAtᵢ mode occ (tag p₁ ⇛ p₂))
mlb-type-occurs-leftOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (idˣ w⊑y _ Y<Δ) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-leftOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (idˣ w⊑y _ Y<Δ) occ | refl =
  ⊥-elim (leftChoice-no-star-at-leftOnlyᵢ mode w⊑★)
mlb-type-occurs-leftOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (tagˣ w⊑★′ _) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-leftOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (tagˣ w⊑★′ _) occ | refl =
  ⊥-elim (leftChoice-no-star-at-leftOnlyᵢ mode w⊑★)
mlb-type-occurs-leftOnlyAtᵢ mode (ν occC p) (∀ⁱ q) occ =
  mlb-type-occurs-leftOnlyAtᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode) p q occ
mlb-type-occurs-leftOnlyAtᵢ {Γ = Γ} {X = X} mode
    (ν occC p) (ν occC′ q) occ =
  close-neither-occursᵢ
    {X = X}
    {A = mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q}
    (mlb-type-occurs-leftOnlyAtᵢ (thereᵐᵢ {n = neitherᵢ} mode) p q occ)
mlb-type-occurs-leftOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (tagˣ w⊑★ _) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-leftOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (tagˣ w⊑★ _) occ | refl =
  choice-var-star-occurs-leftOnlyᵢ mode w⊑x w⊑★

mlb-type-occurs-rightOnlyAtᵢ :
  ∀ {Γ X Δᶜ Δᴸ Δᴿ A B C} →
  ModeAtᵢ Γ X rightOnlyᵢ →
  (p : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ) →
  (q : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ) →
  occurs X C ≡ true →
  occurs X (mlb-typeᵢ {Γ = Γ} p q) ≡ true
mlb-type-occurs-rightOnlyAtᵢ mode id★ id★ ()
mlb-type-occurs-rightOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (idˣ w⊑y _ Y<Δ) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-rightOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (idˣ w⊑y _ Y<Δ) occ | refl =
  ⊥-elim (leftChoice-no-var-at-rightOnlyᵢ mode w⊑x)
mlb-type-occurs-rightOnlyAtᵢ mode idι idι ()
mlb-type-occurs-rightOnlyAtᵢ mode idι (tag ι) ()
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (q₁ ↦ q₂) occ
    with occurs X C₁ in occ₁
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (q₁ ↦ q₂) occ | true =
  ∨-true-leftᵢ (mlb-type-occurs-rightOnlyAtᵢ mode p₁ q₁ occ₁)
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (q₁ ↦ q₂) occ | false =
  ∨-true-rightᵢ (mlb-type-occurs-rightOnlyAtᵢ mode p₂ q₂ occ)
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (tag q₁ ⇛ q₂) occ
    with occurs X C₁ in occ₁
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (tag q₁ ⇛ q₂) occ | true =
  ∨-true-leftᵢ (mlb-type-occurs-rightOnlyAtᵢ mode p₁ q₁ occ₁)
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (_↦_ {A = C₁} p₁ p₂) (tag q₁ ⇛ q₂) occ | false =
  ∨-true-rightᵢ (mlb-type-occurs-rightOnlyAtᵢ mode p₂ q₂ occ)
mlb-type-occurs-rightOnlyAtᵢ mode (∀ⁱ p) (∀ⁱ q) occ =
  mlb-type-occurs-rightOnlyAtᵢ (thereᵐᵢ {n = bothᵢ} mode) p q occ
mlb-type-occurs-rightOnlyAtᵢ mode (∀ⁱ p) (ν occC q) occ =
  mlb-type-occurs-rightOnlyAtᵢ (thereᵐᵢ {n = leftOnlyᵢ} mode) p q occ
mlb-type-occurs-rightOnlyAtᵢ mode (tag ι) idι ()
mlb-type-occurs-rightOnlyAtᵢ mode (tag ι) (tag .ι) ()
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (tag_⇛_ {A₁ = C₁} p₁ p₂) (q₁ ↦ q₂) occ
    with occurs X C₁ in occ₁
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (tag_⇛_ {A₁ = C₁} p₁ p₂) (q₁ ↦ q₂) occ | true =
  ∨-true-leftᵢ (mlb-type-occurs-rightOnlyAtᵢ mode p₁ q₁ occ₁)
mlb-type-occurs-rightOnlyAtᵢ {X = X} mode
    (tag_⇛_ {A₁ = C₁} p₁ p₂) (q₁ ↦ q₂) occ | false =
  ∨-true-rightᵢ (mlb-type-occurs-rightOnlyAtᵢ mode p₂ q₂ occ)
mlb-type-occurs-rightOnlyAtᵢ mode (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) occ =
  ⊥-elim (no-occurs-star-rightOnlyAtᵢ mode occ (tag q₁ ⇛ q₂))
mlb-type-occurs-rightOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (idˣ w⊑y _ Y<Δ) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-rightOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (idˣ w⊑y _ Y<Δ) occ | refl =
  choice-star-var-occurs-rightOnlyᵢ mode w⊑★ w⊑y
mlb-type-occurs-rightOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (tagˣ w⊑★′ _) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-rightOnlyAtᵢ mode (tagˣ w⊑★ W<Δ)
    (tagˣ w⊑★′ _) occ | refl =
  ⊥-elim (rightChoice-no-star-at-rightOnlyᵢ mode w⊑★′)
mlb-type-occurs-rightOnlyAtᵢ mode (ν occC p) (∀ⁱ q) occ =
  mlb-type-occurs-rightOnlyAtᵢ (thereᵐᵢ {n = rightOnlyᵢ} mode) p q occ
mlb-type-occurs-rightOnlyAtᵢ {Γ = Γ} {X = X} mode
    (ν occC p) (ν occC′ q) occ =
  close-neither-occursᵢ
    {X = X}
    {A = mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q}
    (mlb-type-occurs-rightOnlyAtᵢ (thereᵐᵢ {n = neitherᵢ} mode) p q occ)
mlb-type-occurs-rightOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (tagˣ w⊑★ _) occ
    with occurs-var-true→≡ᵢ occ
mlb-type-occurs-rightOnlyAtᵢ mode (idˣ w⊑x W<Δ X<Δ)
    (tagˣ w⊑★ _) occ | refl =
  ⊥-elim (rightChoice-no-star-at-rightOnlyᵢ mode w⊑★)

mlb-type-occurs-∀νᵢ :
  ∀ {Γ Δᶜ Δᴸ Δᴿ A B C} →
  (p : leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
    ∣ suc Δᶜ ⊢ C ⊑ A ⊣ suc Δᴸ) →
  (q : rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
    ∣ suc Δᶜ ⊢ C ⊑ B ⊣ Δᴿ) →
  occurs zero C ≡ true →
  occurs zero (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) ≡ true
mlb-type-occurs-∀νᵢ p q occ =
  mlb-type-occurs-leftOnlyAtᵢ hereᵐᵢ p q occ

mlb-type-occurs-ν∀ᵢ :
  ∀ {Γ Δᶜ Δᴸ Δᴿ A B C} →
  (p : leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
    ∣ suc Δᶜ ⊢ C ⊑ A ⊣ Δᴸ) →
  (q : rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
    ∣ suc Δᶜ ⊢ C ⊑ B ⊣ suc Δᴿ) →
  occurs zero C ≡ true →
  occurs zero (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) ≡ true
mlb-type-occurs-ν∀ᵢ p q occ =
  mlb-type-occurs-rightOnlyAtᵢ hereᵐᵢ p q occ

mlb-type-from-lowerᵢ :
  ∀ {Δ A B C} →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ →
  Ty
mlb-type-from-lowerᵢ {Δ = Δ} C⊑A C⊑B =
  mlb-typeᵢ {Γ = choice-idᵢ Δ}
    (leftChoice-id-proofAtᵢ C⊑A)
    (rightChoice-id-proofAtᵢ C⊑B)

mlb-type-choice-id-proof-eqᵢ :
  ∀ {Δ C A B}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  mlb-typeᵢ
    {Γ = choice-idᵢ Δ}
    (leftChoice-id-proofᵢ p)
    (rightChoice-id-proofᵢ q)
    ≡ mlb-type-from-lowerᵢ p q
mlb-type-choice-id-proof-eqᵢ {Δ = Δ}
    rewrite choice-id-commonCtxᵢ Δ
          | choice-id-leftCtxᵢ Δ
          | choice-id-rightCtxᵢ Δ =
  refl

close-neither-true-eqᵢ :
  ∀ {D} →
  occurs zero D ≡ true →
  close-neitherᵢ D ≡ `∀ D
close-neither-true-eqᵢ {D = D} occD with occurs zero D
close-neither-true-eqᵢ {D = D} occD | true = refl
close-neither-true-eqᵢ {D = D} () | false

close-neither-false-eqᵢ :
  ∀ {D} →
  occurs zero D ≡ false →
  close-neitherᵢ D ≡ D [ zero ]ᴿ
close-neither-false-eqᵢ {D = D} occD with occurs zero D
close-neither-false-eqᵢ {D = D} () | true
close-neither-false-eqᵢ {D = D} occD | false = refl

close-neither-swap01ᵢ :
  ∀ A →
  close-neitherᵢ (renameᵗ (extᵗ swap01ᵢ) A)
  ≡ renameᵗ swap01ᵢ (close-neitherᵢ A)
close-neither-swap01ᵢ A
    with occurs zero A in occA
       | occurs zero (renameᵗ (extᵗ swap01ᵢ) A) in occAˢ
close-neither-swap01ᵢ A | true | true = refl
close-neither-swap01ᵢ A | true | false =
  ⊥-elim
    (false≠trueᵢ
      (trans (sym occAˢ)
        (trans (occurs-zero-rename-ext swap01ᵢ A) occA)))
close-neither-swap01ᵢ A | false | true =
  ⊥-elim
    (false≠trueᵢ
      (trans (sym occA)
        (trans (sym (occurs-zero-rename-ext swap01ᵢ A)) occAˢ)))
close-neither-swap01ᵢ A | false | false =
  trans
    (cong (renameᵗ (removeAtᵗ zero)) (swapAt-ext-renameᵢ zero A))
    (removeAt-swapAt-freshᵢ zero A occA)

occurs-zero-under-ext-swap01ᵢ :
  ∀ {A B} →
  A ≡ renameᵗ (extᵗ swap01ᵢ) B →
  occurs zero A ≡ occurs zero B
occurs-zero-under-ext-swap01ᵢ {B = B} eq =
  trans (cong (occurs zero) eq) (occurs-zero-rename-ext swap01ᵢ B)

close-neither-true-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′} →
  occurs zero C ≡ true →
  occurs zero C′ ≡ true →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ close-neitherᵢ C ⊑ close-neitherᵢ C′ ⊣ Δᴿ
close-neither-true-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {C = C} {C′ = C′}
    occC occC′ body-coh =
  subst
    (λ L → Φ ∣ Δᴸ ⊢ L ⊑ close-neitherᵢ C′ ⊣ Δᴿ)
    (sym (close-neither-true-eqᵢ occC))
    (subst
      (λ R → Φ ∣ Δᴸ ⊢ `∀ C ⊑ R ⊣ Δᴿ)
      (sym (close-neither-true-eqᵢ occC′))
      (∀ⁱ body-coh))

close-neither-false-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′} →
  occurs zero C ≡ false →
  occurs zero C′ ≡ false →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ close-neitherᵢ C ⊑ close-neitherᵢ C′ ⊣ Δᴿ
close-neither-false-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {C = C} {C′ = C′}
    occC occC′ body-coh =
  subst
    (λ L → Φ ∣ Δᴸ ⊢ L ⊑ close-neitherᵢ C′ ⊣ Δᴿ)
    (sym (close-neither-false-eqᵢ occC))
    (subst
      (λ R → Φ ∣ Δᴸ ⊢ C [ zero ]ᴿ ⊑ R ⊣ Δᴿ)
      (sym (close-neither-false-eqᵢ occC′))
      (open-unused-bothᵢ occC occC′ body-coh))

close-neither-common-trueᵢ :
  ∀ Γ {Δᶜ Δᴸ Δᴿ A B D} →
  occurs zero D ≡ true →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ (neitherᵢ ∷ Γ)) (rightChoiceᵢ (neitherᵢ ∷ Γ))
    (suc Δᶜ) Δᴸ Δᴿ A B D →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    Δᶜ Δᴸ Δᴿ A B (close-neitherᵢ D)
close-neither-common-trueᵢ Γ {D = D} occD (D⊑A , D⊑B) =
  subst
    (λ E →
      CommonLowerBoundᶜᵢ
        (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
        _ _ _ _ _ E)
    (sym (close-neither-true-eqᵢ occD))
    (ν occD D⊑A , ν occD D⊑B)

close-neither-commonᶜᵢ :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  CommonLowerBoundᶜᵢ
    (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (suc Δᶜ) Δᴸ Δᴿ A B D →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B (close-neitherᵢ D)
close-neither-commonᶜᵢ {D = D} common
    with occurs zero D in occD
close-neither-commonᶜᵢ {D = D} (D⊑A , D⊑B)
    | true =
  ν occD D⊑A , ν occD D⊑B
close-neither-commonᶜᵢ {D = D} (D⊑A , D⊑B)
    | false =
  open-unusedᵢ occD D⊑A ,
  open-unusedᵢ occD D⊑B

close-neither-commonᵢ :
  ∀ Γ {Δᶜ Δᴸ Δᴿ A B D} →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ (neitherᵢ ∷ Γ)) (rightChoiceᵢ (neitherᵢ ∷ Γ))
    (suc Δᶜ) Δᴸ Δᴿ A B D →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    Δᶜ Δᴸ Δᴿ A B (close-neitherᵢ D)
close-neither-commonᵢ Γ {D = D} common
    with occurs zero D in occD
close-neither-commonᵢ Γ {D = D} (D⊑A , D⊑B)
    | true =
  ν occD D⊑A , ν occD D⊑B
close-neither-commonᵢ Γ {D = D} (D⊑A , D⊑B)
    | false =
  open-unusedᵢ occD D⊑A ,
  open-unusedᵢ occD D⊑B

mlb-type-commonᵢ :
  ∀ {Γ Δᶜ Δᴸ Δᴿ A B C} →
  (p : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ) →
  (q : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ) →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    Δᶜ Δᴸ Δᴿ A B (mlb-typeᵢ {Γ = Γ} p q)
mlb-type-commonᵢ id★ id★ = id★ , id★
mlb-type-commonᵢ {Γ = Γ}
    (idˣ w⊑x W<Δ X<Δ) (idˣ w⊑y _ Y<Δ) =
  choice-var-var-commonᵢ Γ w⊑x w⊑y W<Δ X<Δ Y<Δ
mlb-type-commonᵢ idι idι = idι , idι
mlb-type-commonᵢ idι (tag ι) = idι , tag ι
mlb-type-commonᵢ (p₁ ↦ p₂) (q₁ ↦ q₂) =
  proj₁ c₁ ↦ proj₁ c₂ , proj₂ c₁ ↦ proj₂ c₂
  where
    c₁ = mlb-type-commonᵢ p₁ q₁
    c₂ = mlb-type-commonᵢ p₂ q₂
mlb-type-commonᵢ (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  proj₁ c₁ ↦ proj₁ c₂ , tag_⇛_ (proj₂ c₁) (proj₂ c₂)
  where
    c₁ = mlb-type-commonᵢ p₁ q₁
    c₂ = mlb-type-commonᵢ p₂ q₂
mlb-type-commonᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q) =
  ∀ⁱ (proj₁ c) , ∀ⁱ (proj₂ c)
  where
    c = mlb-type-commonᵢ {Γ = bothᵢ ∷ Γ} p q
mlb-type-commonᵢ {Γ = Γ} (∀ⁱ p) (ν occ q) =
  ∀ⁱ (proj₁ c) , ν (mlb-type-occurs-∀νᵢ p q occ) (proj₂ c)
  where
    c = mlb-type-commonᵢ {Γ = leftOnlyᵢ ∷ Γ} p q
mlb-type-commonᵢ (tag ι) idι = tag ι , idι
mlb-type-commonᵢ (tag ι) (tag .ι) = id★ , id★
mlb-type-commonᵢ (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  tag_⇛_ (proj₁ c₁) (proj₁ c₂) , proj₂ c₁ ↦ proj₂ c₂
  where
    c₁ = mlb-type-commonᵢ p₁ q₁
    c₂ = mlb-type-commonᵢ p₂ q₂
mlb-type-commonᵢ (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  id★ , id★
mlb-type-commonᵢ {Γ = Γ}
    (tagˣ w⊑★ W<Δ) (idˣ w⊑y _ Y<Δ) =
  choice-star-var-commonᵢ Γ w⊑★ w⊑y W<Δ Y<Δ
mlb-type-commonᵢ (tagˣ w⊑★ W<Δ) (tagˣ w⊑★′ _) =
  id★ , id★
mlb-type-commonᵢ {Γ = Γ} (ν occ p) (∀ⁱ q) =
  ν (mlb-type-occurs-ν∀ᵢ p q occ) (proj₁ c) , ∀ⁱ (proj₂ c)
  where
    c = mlb-type-commonᵢ {Γ = rightOnlyᵢ ∷ Γ} p q
mlb-type-commonᵢ {Γ = Γ} (ν occ p) (ν occ′ q) =
  close-neither-commonᵢ Γ
    (mlb-type-commonᵢ {Γ = neitherᵢ ∷ Γ} p q)
mlb-type-commonᵢ {Γ = Γ}
    (idˣ w⊑x W<Δ X<Δ) (tagˣ w⊑★ _) =
  choice-var-star-commonᵢ Γ w⊑x w⊑★ W<Δ X<Δ

mlb-type-from-lower-commonᵢ :
  ∀ {Δ A B C} →
  (p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
  (q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ) →
  CommonLowerBoundᵢ Δ A B (mlb-type-from-lowerᵢ p q)
mlb-type-from-lower-commonᵢ {Δ = Δ} p q =
  leftChoice-id-proofAt⁻ᵢ (proj₁ common) ,
  rightChoice-id-proofAt⁻ᵢ (proj₂ common)
  where
    p′ = leftChoice-id-proofAtᵢ p

    q′ = rightChoice-id-proofAtᵢ q

    common = mlb-type-commonᵢ p′ q′

mlb-type-from-lower-common-oldᵢ :
  ∀ {Δ A B C} →
  (p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
  (q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ) →
  Imp._⊢_⊑_ (idᵢ Δ) (mlb-type-from-lowerᵢ p q) A ×
  Imp._⊢_⊑_ (idᵢ Δ) (mlb-type-from-lowerᵢ p q) B
mlb-type-from-lower-common-oldᵢ p q =
  ⊑-forgetᵢ (proj₁ common) , ⊑-forgetᵢ (proj₂ common)
  where
    common = mlb-type-from-lower-commonᵢ p q

comparable-var-varᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X Y} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y)
comparable-var-varᶜᵢ V W⊑X W⊑Y =
  record
    { cᶜ-lowerᵢ = ＇ proj₁ selected
    ; cᶜ-lower-leftᵢ = proj₁ (proj₂ selected)
    ; cᶜ-lower-rightᵢ = proj₁ (proj₂ (proj₂ selected))
    ; cᶜ-comparableᵢ = comparable
    }
  where
    selected = mlb-var-varᵢ V W⊑X W⊑Y
    greatest = proj₂ (proj₂ (proj₂ selected))

    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (＇ _) (＇ _) D →
      _ ∣ _ ⊢ ＇ proj₁ selected ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ ＇ proj₁ selected ⊣ _
    comparable common (idˣ _ _ _) = greatest (proj₁ common) (proj₂ common)
    comparable (() , _) (tagˣ _ _)

maximal-var-varᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X Y} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y)
maximal-var-varᶜᵢ V W⊑X W⊑Y =
  comparable⇒maximalᶜᵢ (comparable-var-varᶜᵢ V W⊑X W⊑Y)

comparable-var-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) ★
comparable-var-starᶜᵢ V W⊑X W⊑★ =
  record
    { cᶜ-lowerᵢ = ＇ proj₁ selected
    ; cᶜ-lower-leftᵢ = proj₁ (proj₂ selected)
    ; cᶜ-lower-rightᵢ = proj₁ (proj₂ (proj₂ selected))
    ; cᶜ-comparableᵢ = comparable
    }
  where
    selected = mlb-var-starᵢ V W⊑X W⊑★
    greatest = proj₂ (proj₂ (proj₂ selected))

    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (＇ _) ★ D →
      _ ∣ _ ⊢ ＇ proj₁ selected ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ ＇ proj₁ selected ⊣ _
    comparable common (idˣ _ _ _) = greatest (proj₁ common) (proj₂ common)
    comparable (() , _) (tagˣ _ _)

maximal-var-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) ★
maximal-var-starᶜᵢ V W⊑X W⊑★ =
  comparable⇒maximalᶜᵢ (comparable-var-starᶜᵢ V W⊑X W⊑★)

comparable-star-varᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W Y} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (＇ Y)
comparable-star-varᶜᵢ V W⊑★ W⊑Y =
  record
    { cᶜ-lowerᵢ = ＇ proj₁ selected
    ; cᶜ-lower-leftᵢ = proj₁ (proj₂ selected)
    ; cᶜ-lower-rightᵢ = proj₁ (proj₂ (proj₂ selected))
    ; cᶜ-comparableᵢ = comparable
    }
  where
    selected = mlb-star-varᵢ V W⊑★ W⊑Y
    greatest = proj₂ (proj₂ (proj₂ selected))

    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ ★ (＇ _) D →
      _ ∣ _ ⊢ ＇ proj₁ selected ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ ＇ proj₁ selected ⊣ _
    comparable common (idˣ _ _ _) = greatest (proj₁ common) (proj₂ common)
    comparable (_ , ()) (tagˣ _ _)

maximal-star-varᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W Y} →
  MlbVarCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (＇ Y)
maximal-star-varᶜᵢ V W⊑★ W⊑Y =
  comparable⇒maximalᶜᵢ (comparable-star-varᶜᵢ V W⊑★ W⊑Y)

comparable-var-varᵐᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X Y} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y)
comparable-var-varᵐᵢ Ψ W⊑X W⊑Y =
  comparable-var-varᶜᵢ (MlbCtx-varsᵢ Ψ) W⊑X W⊑Y

comparable-var-starᵐᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) ★
comparable-var-starᵐᵢ Ψ W⊑X W⊑★ =
  comparable-var-starᶜᵢ (MlbCtx-varsᵢ Ψ) W⊑X W⊑★

comparable-star-varᵐᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W Y} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (＇ Y)
comparable-star-varᵐᵢ Ψ W⊑★ W⊑Y =
  comparable-star-varᶜᵢ (MlbCtx-varsᵢ Ψ) W⊑★ W⊑Y

maximal-var-varᵐᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X Y} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y)
maximal-var-varᵐᵢ Ψ W⊑X W⊑Y =
  maximal-var-varᶜᵢ (MlbCtx-varsᵢ Ψ) W⊑X W⊑Y

maximal-var-starᵐᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W X} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (＇ X) ★
maximal-var-starᵐᵢ Ψ W⊑X W⊑★ =
  maximal-var-starᶜᵢ (MlbCtx-varsᵢ Ψ) W⊑X W⊑★

maximal-star-varᵐᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ W Y} →
  MlbCtxᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (＇ Y)
maximal-star-varᵐᵢ Ψ W⊑★ W⊑Y =
  maximal-star-varᶜᵢ (MlbCtx-varsᵢ Ψ) W⊑★ W⊑Y

comparable-choice-star-starᵢ :
  ∀ Γ →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    ★ ★
comparable-choice-star-starᵢ Γ = comparable-star-starᶜᵢ

comparable-choice-base-baseᵢ :
  ∀ Γ {ι} →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (‵ ι) (‵ ι)
comparable-choice-base-baseᵢ Γ = comparable-base-baseᶜᵢ

comparable-choice-base-starᵢ :
  ∀ Γ {ι} →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (‵ ι) ★
comparable-choice-base-starᵢ Γ = comparable-base-starᶜᵢ

comparable-choice-star-baseᵢ :
  ∀ Γ {ι} →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    ★ (‵ ι)
comparable-choice-star-baseᵢ Γ = comparable-star-baseᶜᵢ

maximal-choice-star-starᵢ :
  ∀ Γ →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    ★ ★
maximal-choice-star-starᵢ Γ =
  comparable⇒maximalᶜᵢ (comparable-choice-star-starᵢ Γ)

maximal-choice-base-baseᵢ :
  ∀ Γ {ι} →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (‵ ι) (‵ ι)
maximal-choice-base-baseᵢ Γ =
  comparable⇒maximalᶜᵢ (comparable-choice-base-baseᵢ Γ)

maximal-choice-base-starᵢ :
  ∀ Γ {ι} →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (‵ ι) ★
maximal-choice-base-starᵢ Γ =
  comparable⇒maximalᶜᵢ (comparable-choice-base-starᵢ Γ)

maximal-choice-star-baseᵢ :
  ∀ Γ {ι} →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    ★ (‵ ι)
maximal-choice-star-baseᵢ Γ =
  comparable⇒maximalᶜᵢ (comparable-choice-star-baseᵢ Γ)

comparable-choice-var-varᵢ :
  ∀ Γ {W X Y} →
  leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ →
  rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (＇ X) (＇ Y)
comparable-choice-var-varᵢ Γ W⊑X W⊑Y =
  comparable-var-varᵐᵢ (choice-mlbctxᵢ Γ) W⊑X W⊑Y

comparable-choice-var-starᵢ :
  ∀ Γ {W X} →
  leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ →
  rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceRightCtxᵢ Γ →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (＇ X) ★
comparable-choice-var-starᵢ Γ W⊑X W⊑★ =
  comparable-var-starᵐᵢ (choice-mlbctxᵢ Γ) W⊑X W⊑★

comparable-choice-star-varᵢ :
  ∀ Γ {W Y} →
  leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceLeftCtxᵢ Γ →
  rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    ★ (＇ Y)
comparable-choice-star-varᵢ Γ W⊑★ W⊑Y =
  comparable-star-varᵐᵢ (choice-mlbctxᵢ Γ) W⊑★ W⊑Y

maximal-choice-var-varᵢ :
  ∀ Γ {W X Y} →
  leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ →
  rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (＇ X) (＇ Y)
maximal-choice-var-varᵢ Γ W⊑X W⊑Y =
  comparable⇒maximalᶜᵢ (comparable-choice-var-varᵢ Γ W⊑X W⊑Y)

maximal-choice-var-starᵢ :
  ∀ Γ {W X} →
  leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ →
  rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceRightCtxᵢ Γ →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (＇ X) ★
maximal-choice-var-starᵢ Γ W⊑X W⊑★ =
  comparable⇒maximalᶜᵢ (comparable-choice-var-starᵢ Γ W⊑X W⊑★)

maximal-choice-star-varᵢ :
  ∀ Γ {W Y} →
  leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceLeftCtxᵢ Γ →
  rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ →
  MaximalLowerBoundᶜᵢ
    (leftChoiceᵢ Γ) (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    ★ (＇ Y)
maximal-choice-star-varᵢ Γ W⊑★ W⊑Y =
  comparable⇒maximalᶜᵢ (comparable-choice-star-varᵢ Γ W⊑★ W⊑Y)

choice-mlbctx-var-var-lowerᵢ :
  ∀ Γ {W X Y} →
  (p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ) →
  (q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ) →
  proj₁ (mlb-var-varᵢ (MlbCtx-varsᵢ (choice-mlbctxᵢ Γ)) p q) ≡
  choice-var-varᵢ Γ
    (var-memberᵢ p)
    (var-memberᵢ q)
choice-mlbctx-var-var-lowerᵢ [] (idˣ () _ _) q
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    (idˣ (here refl) z<s z<s) (idˣ (here refl) z<s z<s) =
  refl
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    (idˣ (here refl) _ _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    (idˣ (there w⊑x) _ _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-var-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {X = suc X} {Y = suc Y}
    (idˣ (there w⊑x) (s<s W<Δ) (s<s X<Δ))
    (idˣ (there w⊑y) _ (s<s Y<Δ)) =
  cong suc
    (choice-mlbctx-var-var-lowerᵢ Γ
      (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))
choice-mlbctx-var-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    (idˣ (here refl) _ _) (idˣ (here ()) _ _)
choice-mlbctx-var-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    (idˣ (here refl) _ _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-mlbctx-var-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    (idˣ (there w⊑x) _ _) (idˣ (here ()) _ _)
choice-mlbctx-var-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-mlbctx-var-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-var-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = suc W} {X = suc X}
    (idˣ (there w⊑x) (s<s W<Δ) (s<s X<Δ))
    (idˣ (there w⊑y) _ Y<Δ) =
  cong suc
    (choice-mlbctx-var-var-lowerᵢ Γ
      (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))
choice-mlbctx-var-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    (idˣ (here ()) _ _) q
choice-mlbctx-var-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    (idˣ (there w⊑x) _ _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-mlbctx-var-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-mlbctx-var-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-var-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = suc W} {Y = suc Y}
    (idˣ (there w⊑x) (s<s W<Δ) X<Δ)
    (idˣ (there w⊑y) _ (s<s Y<Δ)) =
  cong suc
    (choice-mlbctx-var-var-lowerᵢ Γ
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))
choice-mlbctx-var-var-lowerᵢ (neitherᵢ ∷ Γ)
    (idˣ (here ()) _ _) q
choice-mlbctx-var-var-lowerᵢ (neitherᵢ ∷ Γ)
    p (idˣ (here ()) _ _)
choice-mlbctx-var-var-lowerᵢ (neitherᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-mlbctx-var-var-lowerᵢ (neitherᵢ ∷ Γ)
    {W = suc W}
    (idˣ (there w⊑x) (s<s W<Δ) X<Δ)
    (idˣ (there w⊑y) _ Y<Δ) =
  cong suc
    (choice-mlbctx-var-var-lowerᵢ Γ
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))

choice-mlbctx-var-star-lowerᵢ :
  ∀ Γ {W X} →
  (p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ) →
  (q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceRightCtxᵢ Γ) →
  proj₁ (mlb-var-starᵢ (MlbCtx-varsᵢ (choice-mlbctxᵢ Γ)) p q) ≡
  choice-var-starᵢ Γ
    (var-memberᵢ p)
    (star-memberᵢ q)
choice-mlbctx-var-star-lowerᵢ [] (idˣ () _ _) q
choice-mlbctx-var-star-lowerᵢ (bothᵢ ∷ Γ)
    (idˣ (here refl) _ _) (tagˣ (here ()) _)
choice-mlbctx-var-star-lowerᵢ (bothᵢ ∷ Γ)
    (idˣ (here refl) _ _) (tagˣ (there w⊑★) _) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-mlbctx-var-star-lowerᵢ (bothᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-mlbctx-var-star-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-var-star-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {X = suc X}
    (idˣ (there w⊑x) (s<s W<Δ) (s<s X<Δ))
    (tagˣ (there w⊑★) _) =
  cong suc
    (choice-mlbctx-var-star-lowerᵢ Γ
      (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δ))
choice-mlbctx-var-star-lowerᵢ (leftOnlyᵢ ∷ Γ)
    (idˣ (here refl) z<s z<s) (tagˣ (here refl) z<s) =
  refl
choice-mlbctx-var-star-lowerᵢ (leftOnlyᵢ ∷ Γ)
    (idˣ (here refl) _ _) (tagˣ (there w⊑★) _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-mlbctx-var-star-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-mlbctx-var-star-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = suc W} {X = zero} (idˣ (there w⊑0) _ _) q =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-var-star-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = suc W} {X = suc X}
    (idˣ (there w⊑x) (s<s W<Δ) (s<s X<Δ))
    (tagˣ (there w⊑★) _) =
  cong suc
    (choice-mlbctx-var-star-lowerᵢ Γ
      (idˣ (un⇑ᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δ))
choice-mlbctx-var-star-lowerᵢ (rightOnlyᵢ ∷ Γ)
    (idˣ (here ()) _ _) q
choice-mlbctx-var-star-lowerᵢ (rightOnlyᵢ ∷ Γ)
    p (tagˣ (here ()) _)
choice-mlbctx-var-star-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-mlbctx-var-star-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = suc W}
    (idˣ (there w⊑x) (s<s W<Δ) X<Δ)
    (tagˣ (there w⊑★) _) =
  cong suc
    (choice-mlbctx-var-star-lowerᵢ Γ
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δ))
choice-mlbctx-var-star-lowerᵢ (neitherᵢ ∷ Γ)
    (idˣ (here ()) _ _) q
choice-mlbctx-var-star-lowerᵢ (neitherᵢ ∷ Γ)
    {W = zero} (idˣ (there w⊑x) _ _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
choice-mlbctx-var-star-lowerᵢ (neitherᵢ ∷ Γ)
    {W = suc W}
    (idˣ (there w⊑x) (s<s W<Δ) X<Δ)
    (tagˣ (there w⊑★) _) =
  cong suc
    (choice-mlbctx-var-star-lowerᵢ Γ
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑x) W<Δ X<Δ)
      (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δ))

choice-mlbctx-star-var-lowerᵢ :
  ∀ Γ {W Y} →
  (p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceLeftCtxᵢ Γ) →
  (q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ) →
  proj₁ (mlb-star-varᵢ (MlbCtx-varsᵢ (choice-mlbctxᵢ Γ)) p q) ≡
  choice-star-varᵢ Γ
    (star-memberᵢ p)
    (var-memberᵢ q)
choice-mlbctx-star-var-lowerᵢ [] (tagˣ () _) q
choice-mlbctx-star-var-lowerᵢ (bothᵢ ∷ Γ)
    (tagˣ (here ()) _) q
choice-mlbctx-star-var-lowerᵢ (bothᵢ ∷ Γ)
    (tagˣ (there w⊑★) _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-mlbctx-star-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-mlbctx-star-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-star-var-lowerᵢ (bothᵢ ∷ Γ)
    {W = suc W} {Y = suc Y}
    (tagˣ (there w⊑★) (s<s W<Δ))
    (idˣ (there w⊑y) _ (s<s Y<Δ)) =
  cong suc
    (choice-mlbctx-star-var-lowerᵢ Γ
      (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δ)
      (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))
choice-mlbctx-star-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    (tagˣ (here ()) _) q
choice-mlbctx-star-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    p (idˣ (here ()) _ _)
choice-mlbctx-star-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
choice-mlbctx-star-var-lowerᵢ (leftOnlyᵢ ∷ Γ)
    {W = suc W}
    (tagˣ (there w⊑★) (s<s W<Δ))
    (idˣ (there w⊑y) _ Y<Δ) =
  cong suc
    (choice-mlbctx-star-var-lowerᵢ Γ
      (tagˣ (un⇑ᵢ-★∈ w⊑★) W<Δ)
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))
choice-mlbctx-star-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    (tagˣ (here refl) z<s) (idˣ (here refl) z<s z<s) =
  refl
choice-mlbctx-star-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    (tagˣ (here refl) _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-mlbctx-star-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    (tagˣ (there w⊑★) _) (idˣ (here refl) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-mlbctx-star-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-mlbctx-star-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = suc W} {Y = zero} p (idˣ (there w⊑0) _ _) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
choice-mlbctx-star-var-lowerᵢ (rightOnlyᵢ ∷ Γ)
    {W = suc W} {Y = suc Y}
    (tagˣ (there w⊑★) (s<s W<Δ))
    (idˣ (there w⊑y) _ (s<s Y<Δ)) =
  cong suc
    (choice-mlbctx-star-var-lowerᵢ Γ
      (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δ)
      (idˣ (un⇑ᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))
choice-mlbctx-star-var-lowerᵢ (neitherᵢ ∷ Γ)
    p (idˣ (here ()) _ _)
choice-mlbctx-star-var-lowerᵢ (neitherᵢ ∷ Γ)
    {W = zero} (tagˣ (here refl) _) (idˣ (there w⊑y) _ _) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
choice-mlbctx-star-var-lowerᵢ (neitherᵢ ∷ Γ)
    {W = zero} (tagˣ (there w⊑★) _) q =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
choice-mlbctx-star-var-lowerᵢ (neitherᵢ ∷ Γ)
    {W = suc W}
    (tagˣ (there w⊑★) (s<s W<Δ))
    (idˣ (there w⊑y) _ Y<Δ) =
  cong suc
    (choice-mlbctx-star-var-lowerᵢ Γ
      (tagˣ (un⇑ᴸᵢ-★∈ w⊑★) W<Δ)
      (idˣ (un⇑ᴸᵢ-ˣ∈ w⊑y) W<Δ Y<Δ))

comparable-choice-star-star-lowerᵢ :
  ∀ Γ →
  cᶜ-lowerᵢ (comparable-choice-star-starᵢ Γ) ≡
  mlb-typeᵢ
    {Γ = Γ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    id★ id★
comparable-choice-star-star-lowerᵢ Γ = refl

comparable-choice-base-base-lowerᵢ :
  ∀ Γ {ι} →
  cᶜ-lowerᵢ (comparable-choice-base-baseᵢ Γ {ι = ι}) ≡
  mlb-typeᵢ
    {Γ = Γ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    (idι {ι = ι}) idι
comparable-choice-base-base-lowerᵢ Γ = refl

comparable-choice-base-star-lowerᵢ :
  ∀ Γ {ι} →
  cᶜ-lowerᵢ (comparable-choice-base-starᵢ Γ {ι = ι}) ≡
  mlb-typeᵢ
    {Γ = Γ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    (idι {ι = ι}) (tag ι)
comparable-choice-base-star-lowerᵢ Γ = refl

comparable-choice-star-base-lowerᵢ :
  ∀ Γ {ι} →
  cᶜ-lowerᵢ (comparable-choice-star-baseᵢ Γ {ι = ι}) ≡
  mlb-typeᵢ
    {Γ = Γ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    (tag ι) (idι {ι = ι})
comparable-choice-star-base-lowerᵢ Γ = refl

comparable-choice-var-var-lowerᵢ :
  ∀ Γ {W X Y} →
  (p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ) →
  (q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ) →
  cᶜ-lowerᵢ (comparable-choice-var-varᵢ Γ p q) ≡
  mlb-typeᵢ {Γ = Γ} p q
comparable-choice-var-var-lowerᵢ Γ
    (idˣ w⊑x W<Δ X<Δ) (idˣ w⊑y W<Δ′ Y<Δ) =
  cong ＇_
    (choice-mlbctx-var-var-lowerᵢ Γ
      (idˣ w⊑x W<Δ X<Δ)
      (idˣ w⊑y W<Δ′ Y<Δ))

comparable-choice-var-star-lowerᵢ :
  ∀ Γ {W X} →
  (p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ X ⊣ choiceLeftCtxᵢ Γ) →
  (q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceRightCtxᵢ Γ) →
  cᶜ-lowerᵢ (comparable-choice-var-starᵢ Γ p q) ≡
  mlb-typeᵢ {Γ = Γ} p q
comparable-choice-var-star-lowerᵢ Γ
    (idˣ w⊑x W<Δ X<Δ) (tagˣ w⊑★ W<Δ′) =
  cong ＇_
    (choice-mlbctx-var-star-lowerᵢ Γ
      (idˣ w⊑x W<Δ X<Δ)
      (tagˣ w⊑★ W<Δ′))

comparable-choice-star-var-lowerᵢ :
  ∀ Γ {W Y} →
  (p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ★ ⊣ choiceLeftCtxᵢ Γ) →
  (q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
    ⊢ ＇ W ⊑ ＇ Y ⊣ choiceRightCtxᵢ Γ) →
  cᶜ-lowerᵢ (comparable-choice-star-varᵢ Γ p q) ≡
  mlb-typeᵢ {Γ = Γ} p q
comparable-choice-star-var-lowerᵢ Γ
    (tagˣ w⊑★ W<Δ) (idˣ w⊑y W<Δ′ Y<Δ) =
  cong ＇_
    (choice-mlbctx-star-var-lowerᵢ Γ
      (tagˣ w⊑★ W<Δ)
      (idˣ w⊑y W<Δ′ Y<Δ))

comparable-arrow-arrowᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  ComparableMaximalLowerBoundᵢ Δ A₁ B₁ →
  ComparableMaximalLowerBoundᵢ Δ A₂ B₂ →
  ComparableMaximalLowerBoundᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
comparable-arrow-arrowᵢ c₁ c₂ =
  record
    { c-lowerᵢ = c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂
    ; c-lower-leftᵢ = c-lower-leftᵢ c₁ ↦ c-lower-leftᵢ c₂
    ; c-lower-rightᵢ = c-lower-rightᵢ c₁ ↦ c-lower-rightᵢ c₂
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᵢ _ (_ ⇒ _) (_ ⇒ _) D →
      idᵢ _ ∣ _ ⊢ c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂ ⊑ D ⊣ _ →
      idᵢ _ ∣ _ ⊢ D ⊑ c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂ ⊣ _
    comparable ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      c-comparableᵢ c₁ (D₁⊑A₁ , D₁⊑B₁) C₁⊑D₁ ↦
      c-comparableᵢ c₂ (D₂⊑A₂ , D₂⊑B₂) C₂⊑D₂

comparable-star-arrowᵢ :
  ∀ {Δ B₁ B₂} →
  ComparableMaximalLowerBoundᵢ Δ ★ B₁ →
  ComparableMaximalLowerBoundᵢ Δ ★ B₂ →
  ComparableMaximalLowerBoundᵢ Δ ★ (B₁ ⇒ B₂)
comparable-star-arrowᵢ c₁ c₂ =
  record
    { c-lowerᵢ = c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂
    ; c-lower-leftᵢ = tag_⇛_ (c-lower-leftᵢ c₁) (c-lower-leftᵢ c₂)
    ; c-lower-rightᵢ = c-lower-rightᵢ c₁ ↦ c-lower-rightᵢ c₂
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᵢ _ ★ (_ ⇒ _) D →
      idᵢ _ ∣ _ ⊢ c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂ ⊑ D ⊣ _ →
      idᵢ _ ∣ _ ⊢ D ⊑ c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂ ⊣ _
    comparable ((tag_⇛_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      c-comparableᵢ c₁ (D₁⊑★ , D₁⊑B₁) C₁⊑D₁ ↦
      c-comparableᵢ c₂ (D₂⊑★ , D₂⊑B₂) C₂⊑D₂
    comparable (id★ , ()) (tag_⇛_ C₁⊑★ C₂⊑★)

comparable-arrow-starᵢ :
  ∀ {Δ A₁ A₂} →
  ComparableMaximalLowerBoundᵢ Δ A₁ ★ →
  ComparableMaximalLowerBoundᵢ Δ A₂ ★ →
  ComparableMaximalLowerBoundᵢ Δ (A₁ ⇒ A₂) ★
comparable-arrow-starᵢ c₁ c₂ =
  record
    { c-lowerᵢ = c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂
    ; c-lower-leftᵢ = c-lower-leftᵢ c₁ ↦ c-lower-leftᵢ c₂
    ; c-lower-rightᵢ = tag_⇛_ (c-lower-rightᵢ c₁) (c-lower-rightᵢ c₂)
    ; c-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᵢ _ (_ ⇒ _) ★ D →
      idᵢ _ ∣ _ ⊢ c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂ ⊑ D ⊣ _ →
      idᵢ _ ∣ _ ⊢ D ⊑ c-lowerᵢ c₁ ⇒ c-lowerᵢ c₂ ⊣ _
    comparable ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇛_ D₁⊑★ D₂⊑★))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      c-comparableᵢ c₁ (D₁⊑A₁ , D₁⊑★) C₁⊑D₁ ↦
      c-comparableᵢ c₂ (D₂⊑A₂ , D₂⊑★) C₂⊑D₂

maximal-arrow-arrowᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  ComparableMaximalLowerBoundᵢ Δ A₁ B₁ →
  ComparableMaximalLowerBoundᵢ Δ A₂ B₂ →
  MaximalLowerBoundᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrowᵢ c₁ c₂ =
  comparable⇒maximalᵢ (comparable-arrow-arrowᵢ c₁ c₂)

maximal-arrow-arrow-from-maximalᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  MaximalLowerBoundᵢ Δ A₁ B₁ →
  MaximalLowerBoundᵢ Δ A₂ B₂ →
  MaximalLowerBoundᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrow-from-maximalᵢ mlb₁ mlb₂ =
  record
    { lowerᵢ = lowerᵢ mlb₁ ⇒ lowerᵢ mlb₂
    ; lower-leftᵢ = lower-leftᵢ mlb₁ ↦ lower-leftᵢ mlb₂
    ; lower-rightᵢ = lower-rightᵢ mlb₁ ↦ lower-rightᵢ mlb₂
    ; maximalᵢ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᵢ _ (_ ⇒ _) (_ ⇒ _) D →
      ¬ StrictlyBelowᵢ _ (lowerᵢ mlb₁ ⇒ lowerᵢ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᵢ mlb₁ (D₁⊑A₁ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᵢ mlb₂ (D₂⊑A₂ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )

maximal-star-arrow-from-maximalᵢ :
  ∀ {Δ B₁ B₂} →
  MaximalLowerBoundᵢ Δ ★ B₁ →
  MaximalLowerBoundᵢ Δ ★ B₂ →
  MaximalLowerBoundᵢ Δ ★ (B₁ ⇒ B₂)
maximal-star-arrow-from-maximalᵢ mlb₁ mlb₂ =
  record
    { lowerᵢ = lowerᵢ mlb₁ ⇒ lowerᵢ mlb₂
    ; lower-leftᵢ = tag_⇛_ (lower-leftᵢ mlb₁) (lower-leftᵢ mlb₂)
    ; lower-rightᵢ = lower-rightᵢ mlb₁ ↦ lower-rightᵢ mlb₂
    ; maximalᵢ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᵢ _ ★ (_ ⇒ _) D →
      ¬ StrictlyBelowᵢ _ (lowerᵢ mlb₁ ⇒ lowerᵢ mlb₂) D
    maximal′ ((tag_⇛_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᵢ mlb₁ (D₁⊑★ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᵢ mlb₂ (D₂⊑★ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (id★ , ()) ((tag_⇛_ C₁⊑★ C₂⊑★) , ¬D⊑C)

maximal-arrow-star-from-maximalᵢ :
  ∀ {Δ A₁ A₂} →
  MaximalLowerBoundᵢ Δ A₁ ★ →
  MaximalLowerBoundᵢ Δ A₂ ★ →
  MaximalLowerBoundᵢ Δ (A₁ ⇒ A₂) ★
maximal-arrow-star-from-maximalᵢ mlb₁ mlb₂ =
  record
    { lowerᵢ = lowerᵢ mlb₁ ⇒ lowerᵢ mlb₂
    ; lower-leftᵢ = lower-leftᵢ mlb₁ ↦ lower-leftᵢ mlb₂
    ; lower-rightᵢ = tag_⇛_ (lower-rightᵢ mlb₁) (lower-rightᵢ mlb₂)
    ; maximalᵢ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᵢ _ (_ ⇒ _) ★ D →
      ¬ StrictlyBelowᵢ _ (lowerᵢ mlb₁ ⇒ lowerᵢ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇛_ D₁⊑★ D₂⊑★))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᵢ mlb₁ (D₁⊑A₁ , D₁⊑★)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᵢ mlb₂ (D₂⊑A₂ , D₂⊑★)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )

comparable-arrow-arrowᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ A₂ B₁ B₂} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ B₁ →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₂ B₂ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
comparable-arrow-arrowᶜᵢ c₁ c₂ =
  record
    { cᶜ-lowerᵢ = cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂
    ; cᶜ-lower-leftᵢ = cᶜ-lower-leftᵢ c₁ ↦ cᶜ-lower-leftᵢ c₂
    ; cᶜ-lower-rightᵢ = cᶜ-lower-rightᵢ c₁ ↦ cᶜ-lower-rightᵢ c₂
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (_ ⇒ _) (_ ⇒ _) D →
      _ ∣ _ ⊢ cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂ ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂ ⊣ _
    comparable ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      cᶜ-comparableᵢ c₁ (D₁⊑A₁ , D₁⊑B₁) C₁⊑D₁ ↦
      cᶜ-comparableᵢ c₂ (D₂⊑A₂ , D₂⊑B₂) C₂⊑D₂

comparable-star-arrowᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ B₁ B₂} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ B₁ →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ B₂ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (B₁ ⇒ B₂)
comparable-star-arrowᶜᵢ c₁ c₂ =
  record
    { cᶜ-lowerᵢ = cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂
    ; cᶜ-lower-leftᵢ = tag_⇛_ (cᶜ-lower-leftᵢ c₁) (cᶜ-lower-leftᵢ c₂)
    ; cᶜ-lower-rightᵢ = cᶜ-lower-rightᵢ c₁ ↦ cᶜ-lower-rightᵢ c₂
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ ★ (_ ⇒ _) D →
      _ ∣ _ ⊢ cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂ ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂ ⊣ _
    comparable ((tag_⇛_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      cᶜ-comparableᵢ c₁ (D₁⊑★ , D₁⊑B₁) C₁⊑D₁ ↦
      cᶜ-comparableᵢ c₂ (D₂⊑★ , D₂⊑B₂) C₂⊑D₂
    comparable (id★ , ()) (tag_⇛_ C₁⊑★ C₂⊑★)

comparable-arrow-starᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ A₂} →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ ★ →
  ComparableMaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₂ ★ →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) ★
comparable-arrow-starᶜᵢ c₁ c₂ =
  record
    { cᶜ-lowerᵢ = cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂
    ; cᶜ-lower-leftᵢ = cᶜ-lower-leftᵢ c₁ ↦ cᶜ-lower-leftᵢ c₂
    ; cᶜ-lower-rightᵢ = tag_⇛_ (cᶜ-lower-rightᵢ c₁) (cᶜ-lower-rightᵢ c₂)
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (_ ⇒ _) ★ D →
      _ ∣ _ ⊢ cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂ ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ cᶜ-lowerᵢ c₁ ⇒ cᶜ-lowerᵢ c₂ ⊣ _
    comparable ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇛_ D₁⊑★ D₂⊑★))
        (C₁⊑D₁ ↦ C₂⊑D₂) =
      cᶜ-comparableᵢ c₁ (D₁⊑A₁ , D₁⊑★) C₁⊑D₁ ↦
      cᶜ-comparableᵢ c₂ (D₂⊑A₂ , D₂⊑★) C₂⊑D₂

data FirstOrderSelectorᵢ {Γ} :
    ∀ {C A B} →
    leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ →
    rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ →
    Set where
  fo-star-starᵢ :
    FirstOrderSelectorᵢ id★ id★

  fo-var-varᵢ :
    ∀ {W X Y}
      {w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ}
      {w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < choiceCommonCtxᵢ Γ}
      {W<Δ′ : W < choiceCommonCtxᵢ Γ}
      {X<Δ : X < choiceLeftCtxᵢ Γ}
      {Y<Δ : Y < choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ
      (idˣ w⊑x W<Δ X<Δ)
      (idˣ w⊑y W<Δ′ Y<Δ)

  fo-base-baseᵢ :
    ∀ {ι} →
    FirstOrderSelectorᵢ (idι {ι = ι}) idι

  fo-base-starᵢ :
    ∀ {ι} →
    FirstOrderSelectorᵢ (idι {ι = ι}) (tag ι)

  fo-star-baseᵢ :
    ∀ {ι} →
    FirstOrderSelectorᵢ (tag ι) (idι {ι = ι})

  fo-tag-tagᵢ :
    ∀ {ι} →
    FirstOrderSelectorᵢ (tag ι) (tag ι)

  fo-arrow-arrowᵢ :
    ∀ {C₁ C₂ A₁ A₂ B₁ B₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ A₁
        ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ A₂
        ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ B₁
        ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ B₂
        ⊣ choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ p₁ q₁ →
    FirstOrderSelectorᵢ p₂ q₂ →
    FirstOrderSelectorᵢ (p₁ ↦ p₂) (q₁ ↦ q₂)

  fo-arrow-starᵢ :
    ∀ {C₁ C₂ A₁ A₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ A₁
        ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ A₂
        ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ ★
        ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ ★
        ⊣ choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ p₁ q₁ →
    FirstOrderSelectorᵢ p₂ q₂ →
    FirstOrderSelectorᵢ (p₁ ↦ p₂) (tag q₁ ⇛ q₂)

  fo-star-arrowᵢ :
    ∀ {C₁ C₂ B₁ B₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ ★
        ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ ★
        ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ B₁
        ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ B₂
        ⊣ choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ p₁ q₁ →
    FirstOrderSelectorᵢ p₂ q₂ →
    FirstOrderSelectorᵢ (tag p₁ ⇛ p₂) (q₁ ↦ q₂)

  fo-tag-arrow-tag-arrowᵢ :
    ∀ {C₁ C₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ ★
        ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ ★
        ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₁ ⊑ ★
        ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C₂ ⊑ ★
        ⊣ choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂)

  fo-star-varᵢ :
    ∀ {W Y}
      {w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ}
      {w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < choiceCommonCtxᵢ Γ}
      {W<Δ′ : W < choiceCommonCtxᵢ Γ}
      {Y<Δ : Y < choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ
      (tagˣ w⊑★ W<Δ)
      (idˣ w⊑y W<Δ′ Y<Δ)

  fo-tagvar-tagvarᵢ :
    ∀ {W}
      {w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ}
      {w⊑★′ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < choiceCommonCtxᵢ Γ}
      {W<Δ′ : W < choiceCommonCtxᵢ Γ} →
    FirstOrderSelectorᵢ
      (tagˣ w⊑★ W<Δ)
      (tagˣ w⊑★′ W<Δ′)

  fo-var-starᵢ :
    ∀ {W X}
      {w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ}
      {w⊑★ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < choiceCommonCtxᵢ Γ}
      {W<Δ′ : W < choiceCommonCtxᵢ Γ}
      {X<Δ : X < choiceLeftCtxᵢ Γ} →
    FirstOrderSelectorᵢ
      (idˣ w⊑x W<Δ X<Δ)
      (tagˣ w⊑★ W<Δ′)

data FirstOrderSelectorAtᵢ {Γ Δᶜ Δᴸ Δᴿ} :
    ∀ {C A B} →
    leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
    rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
    Set where
  fo-star-star-atᵢ :
    FirstOrderSelectorAtᵢ id★ id★

  fo-var-var-atᵢ :
    ∀ {W X Y}
      {w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ}
      {w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < Δᶜ}
      {W<Δ′ : W < Δᶜ}
      {X<Δ : X < Δᴸ}
      {Y<Δ : Y < Δᴿ} →
    FirstOrderSelectorAtᵢ
      (idˣ w⊑x W<Δ X<Δ)
      (idˣ w⊑y W<Δ′ Y<Δ)

  fo-base-base-atᵢ :
    ∀ {ι} →
    FirstOrderSelectorAtᵢ (idι {ι = ι}) idι

  fo-base-star-atᵢ :
    ∀ {ι} →
    FirstOrderSelectorAtᵢ (idι {ι = ι}) (tag ι)

  fo-star-base-atᵢ :
    ∀ {ι} →
    FirstOrderSelectorAtᵢ (tag ι) (idι {ι = ι})

  fo-tag-tag-atᵢ :
    ∀ {ι} →
    FirstOrderSelectorAtᵢ (tag ι) (tag ι)

  fo-arrow-arrow-atᵢ :
    ∀ {C₁ C₂ A₁ A₂ B₁ B₂}
      {p₁ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ A₁ ⊣ Δᴸ}
      {p₂ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ A₂ ⊣ Δᴸ}
      {q₁ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ B₁ ⊣ Δᴿ}
      {q₂ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ B₂ ⊣ Δᴿ} →
    FirstOrderSelectorAtᵢ p₁ q₁ →
    FirstOrderSelectorAtᵢ p₂ q₂ →
    FirstOrderSelectorAtᵢ (p₁ ↦ p₂) (q₁ ↦ q₂)

  fo-arrow-star-atᵢ :
    ∀ {C₁ C₂ A₁ A₂}
      {p₁ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ A₁ ⊣ Δᴸ}
      {p₂ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ A₂ ⊣ Δᴸ}
      {q₁ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ ★ ⊣ Δᴿ}
      {q₂ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ ★ ⊣ Δᴿ} →
    FirstOrderSelectorAtᵢ p₁ q₁ →
    FirstOrderSelectorAtᵢ p₂ q₂ →
    FirstOrderSelectorAtᵢ (p₁ ↦ p₂) (tag q₁ ⇛ q₂)

  fo-star-arrow-atᵢ :
    ∀ {C₁ C₂ B₁ B₂}
      {p₁ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ ★ ⊣ Δᴸ}
      {p₂ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ ★ ⊣ Δᴸ}
      {q₁ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ B₁ ⊣ Δᴿ}
      {q₂ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ B₂ ⊣ Δᴿ} →
    FirstOrderSelectorAtᵢ p₁ q₁ →
    FirstOrderSelectorAtᵢ p₂ q₂ →
    FirstOrderSelectorAtᵢ (tag p₁ ⇛ p₂) (q₁ ↦ q₂)

  fo-tag-arrow-tag-arrow-atᵢ :
    ∀ {C₁ C₂}
      {p₁ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ ★ ⊣ Δᴸ}
      {p₂ : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ ★ ⊣ Δᴸ}
      {q₁ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₁ ⊑ ★ ⊣ Δᴿ}
      {q₂ : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C₂ ⊑ ★ ⊣ Δᴿ} →
    FirstOrderSelectorAtᵢ (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂)

  fo-star-var-atᵢ :
    ∀ {W Y}
      {w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ}
      {w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < Δᶜ}
      {W<Δ′ : W < Δᶜ}
      {Y<Δ : Y < Δᴿ} →
    FirstOrderSelectorAtᵢ
      (tagˣ w⊑★ W<Δ)
      (idˣ w⊑y W<Δ′ Y<Δ)

  fo-tagvar-tagvar-atᵢ :
    ∀ {W}
      {w⊑★ : (W ˣ⊑★) ∈ leftChoiceᵢ Γ}
      {w⊑★′ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < Δᶜ}
      {W<Δ′ : W < Δᶜ} →
    FirstOrderSelectorAtᵢ
      (tagˣ w⊑★ W<Δ)
      (tagˣ w⊑★′ W<Δ′)

  fo-var-star-atᵢ :
    ∀ {W X}
      {w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ Γ}
      {w⊑★ : (W ˣ⊑★) ∈ rightChoiceᵢ Γ}
      {W<Δ : W < Δᶜ}
      {W<Δ′ : W < Δᶜ}
      {X<Δ : X < Δᴸ} →
    FirstOrderSelectorAtᵢ
      (idˣ w⊑x W<Δ X<Δ)
      (tagˣ w⊑★ W<Δ′)

first-order-selector-atᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorᵢ p q →
  FirstOrderSelectorAtᵢ
    {Γ = Γ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    p
    q
first-order-selector-atᵢ fo-star-starᵢ = fo-star-star-atᵢ
first-order-selector-atᵢ fo-var-varᵢ = fo-var-var-atᵢ
first-order-selector-atᵢ fo-base-baseᵢ = fo-base-base-atᵢ
first-order-selector-atᵢ fo-base-starᵢ = fo-base-star-atᵢ
first-order-selector-atᵢ fo-star-baseᵢ = fo-star-base-atᵢ
first-order-selector-atᵢ fo-tag-tagᵢ = fo-tag-tag-atᵢ
first-order-selector-atᵢ (fo-arrow-arrowᵢ route₁ route₂) =
  fo-arrow-arrow-atᵢ
    (first-order-selector-atᵢ route₁)
    (first-order-selector-atᵢ route₂)
first-order-selector-atᵢ (fo-arrow-starᵢ route₁ route₂) =
  fo-arrow-star-atᵢ
    (first-order-selector-atᵢ route₁)
    (first-order-selector-atᵢ route₂)
first-order-selector-atᵢ (fo-star-arrowᵢ route₁ route₂) =
  fo-star-arrow-atᵢ
    (first-order-selector-atᵢ route₁)
    (first-order-selector-atᵢ route₂)
first-order-selector-atᵢ fo-tag-arrow-tag-arrowᵢ =
  fo-tag-arrow-tag-arrow-atᵢ
first-order-selector-atᵢ fo-star-varᵢ = fo-star-var-atᵢ
first-order-selector-atᵢ fo-tagvar-tagvarᵢ = fo-tagvar-tagvar-atᵢ
first-order-selector-atᵢ fo-var-starᵢ = fo-var-star-atᵢ

first-order-selector-from-atᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorAtᵢ
    {Γ = Γ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    p
    q →
  FirstOrderSelectorᵢ p q
first-order-selector-from-atᵢ fo-star-star-atᵢ = fo-star-starᵢ
first-order-selector-from-atᵢ fo-var-var-atᵢ = fo-var-varᵢ
first-order-selector-from-atᵢ fo-base-base-atᵢ = fo-base-baseᵢ
first-order-selector-from-atᵢ fo-base-star-atᵢ = fo-base-starᵢ
first-order-selector-from-atᵢ fo-star-base-atᵢ = fo-star-baseᵢ
first-order-selector-from-atᵢ fo-tag-tag-atᵢ = fo-tag-tagᵢ
first-order-selector-from-atᵢ (fo-arrow-arrow-atᵢ route₁ route₂) =
  fo-arrow-arrowᵢ
    (first-order-selector-from-atᵢ route₁)
    (first-order-selector-from-atᵢ route₂)
first-order-selector-from-atᵢ (fo-arrow-star-atᵢ route₁ route₂) =
  fo-arrow-starᵢ
    (first-order-selector-from-atᵢ route₁)
    (first-order-selector-from-atᵢ route₂)
first-order-selector-from-atᵢ (fo-star-arrow-atᵢ route₁ route₂) =
  fo-star-arrowᵢ
    (first-order-selector-from-atᵢ route₁)
    (first-order-selector-from-atᵢ route₂)
first-order-selector-from-atᵢ fo-tag-arrow-tag-arrow-atᵢ =
  fo-tag-arrow-tag-arrowᵢ
first-order-selector-from-atᵢ fo-star-var-atᵢ = fo-star-varᵢ
first-order-selector-from-atᵢ fo-tagvar-tagvar-atᵢ =
  fo-tagvar-tagvarᵢ
first-order-selector-from-atᵢ fo-var-star-atᵢ = fo-var-starᵢ

first-order-selector-transport-contextsᵢ :
  ∀ {Γ Δᶜ Δᴸ Δᴿ Εᶜ Εᴸ Εᴿ C A B}
    {p : leftChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ}
    {q : rightChoiceᵢ Γ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ} →
  (eqᶜ : Δᶜ ≡ Εᶜ) →
  (eqᴸ : Δᴸ ≡ Εᴸ) →
  (eqᴿ : Δᴿ ≡ Εᴿ) →
  FirstOrderSelectorAtᵢ p q →
  FirstOrderSelectorAtᵢ
    {Γ = Γ}
    {Δᶜ = Εᶜ}
    {Δᴸ = Εᴸ}
    {Δᴿ = Εᴿ}
    (subst
      (λ Δᴸ′ → leftChoiceᵢ Γ ∣ Εᶜ ⊢ C ⊑ A ⊣ Δᴸ′)
      eqᴸ
      (subst
        (λ Δᶜ′ → leftChoiceᵢ Γ ∣ Δᶜ′ ⊢ C ⊑ A ⊣ Δᴸ)
        eqᶜ
        p))
    (subst
      (λ Δᴿ′ → rightChoiceᵢ Γ ∣ Εᶜ ⊢ C ⊑ B ⊣ Δᴿ′)
      eqᴿ
      (subst
        (λ Δᶜ′ → rightChoiceᵢ Γ ∣ Δᶜ′ ⊢ C ⊑ B ⊣ Δᴿ)
        eqᶜ
        q))
first-order-selector-transport-contextsᵢ refl refl refl route = route

first-order-choice-id-proofᵢ :
  ∀ {Δ C A B}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δ}
    {Δᶜ = Δ}
    {Δᴸ = Δ}
    {Δᴿ = Δ}
    (leftChoice-id-proofAtᵢ p)
    (rightChoice-id-proofAtᵢ q) →
  FirstOrderSelectorᵢ
    (leftChoice-id-proofᵢ p)
    (rightChoice-id-proofᵢ q)
first-order-choice-id-proofᵢ {Δ = Δ} route =
  first-order-selector-from-atᵢ
    (first-order-selector-transport-contextsᵢ
      (sym (choice-id-commonCtxᵢ Δ))
      (sym (choice-id-leftCtxᵢ Δ))
      (sym (choice-id-rightCtxᵢ Δ))
      route)

mlb-type-comparable-first-orderᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorᵢ p q →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} p q
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-star-starᵢ =
  comparable-choice-star-starᵢ Γ , comparable-choice-star-star-lowerᵢ Γ
mlb-type-comparable-first-orderᵢ {Γ = Γ}
    (fo-var-varᵢ {w⊑x = w⊑x} {w⊑y = w⊑y}
      {W<Δ = W<Δ} {W<Δ′ = W<Δ′} {X<Δ = X<Δ} {Y<Δ = Y<Δ}) =
  comparable-choice-var-varᵢ Γ
    (idˣ w⊑x W<Δ X<Δ)
    (idˣ w⊑y W<Δ′ Y<Δ) ,
  comparable-choice-var-var-lowerᵢ Γ
    (idˣ w⊑x W<Δ X<Δ)
    (idˣ w⊑y W<Δ′ Y<Δ)
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-base-baseᵢ =
  comparable-choice-base-baseᵢ Γ , comparable-choice-base-base-lowerᵢ Γ
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-base-starᵢ =
  comparable-choice-base-starᵢ Γ , comparable-choice-base-star-lowerᵢ Γ
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-star-baseᵢ =
  comparable-choice-star-baseᵢ Γ , comparable-choice-star-base-lowerᵢ Γ
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-tag-tagᵢ =
  comparable-choice-star-starᵢ Γ , refl
mlb-type-comparable-first-orderᵢ (fo-arrow-arrowᵢ r₁ r₂)
    with mlb-type-comparable-first-orderᵢ r₁
       | mlb-type-comparable-first-orderᵢ r₂
mlb-type-comparable-first-orderᵢ (fo-arrow-arrowᵢ r₁ r₂)
    | cb₁ , eq₁ | cb₂ , eq₂ =
  comparable-arrow-arrowᶜᵢ cb₁ cb₂ , cong₂ _⇒_ eq₁ eq₂
mlb-type-comparable-first-orderᵢ (fo-arrow-starᵢ r₁ r₂)
    with mlb-type-comparable-first-orderᵢ r₁
       | mlb-type-comparable-first-orderᵢ r₂
mlb-type-comparable-first-orderᵢ (fo-arrow-starᵢ r₁ r₂)
    | cb₁ , eq₁ | cb₂ , eq₂ =
  comparable-arrow-starᶜᵢ cb₁ cb₂ , cong₂ _⇒_ eq₁ eq₂
mlb-type-comparable-first-orderᵢ (fo-star-arrowᵢ r₁ r₂)
    with mlb-type-comparable-first-orderᵢ r₁
       | mlb-type-comparable-first-orderᵢ r₂
mlb-type-comparable-first-orderᵢ (fo-star-arrowᵢ r₁ r₂)
    | cb₁ , eq₁ | cb₂ , eq₂ =
  comparable-star-arrowᶜᵢ cb₁ cb₂ , cong₂ _⇒_ eq₁ eq₂
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-tag-arrow-tag-arrowᵢ =
  comparable-choice-star-starᵢ Γ , refl
mlb-type-comparable-first-orderᵢ {Γ = Γ}
    (fo-star-varᵢ {w⊑★ = w⊑★} {w⊑y = w⊑y}
      {W<Δ = W<Δ} {W<Δ′ = W<Δ′} {Y<Δ = Y<Δ}) =
  comparable-choice-star-varᵢ Γ
    (tagˣ w⊑★ W<Δ)
    (idˣ w⊑y W<Δ′ Y<Δ) ,
  comparable-choice-star-var-lowerᵢ Γ
    (tagˣ w⊑★ W<Δ)
    (idˣ w⊑y W<Δ′ Y<Δ)
mlb-type-comparable-first-orderᵢ {Γ = Γ} fo-tagvar-tagvarᵢ =
  comparable-choice-star-starᵢ Γ , refl
mlb-type-comparable-first-orderᵢ {Γ = Γ}
    (fo-var-starᵢ {w⊑x = w⊑x} {w⊑★ = w⊑★}
      {W<Δ = W<Δ} {W<Δ′ = W<Δ′} {X<Δ = X<Δ}) =
  comparable-choice-var-starᵢ Γ
    (idˣ w⊑x W<Δ X<Δ)
    (tagˣ w⊑★ W<Δ′) ,
  comparable-choice-var-star-lowerᵢ Γ
    (idˣ w⊑x W<Δ X<Δ)
    (tagˣ w⊑★ W<Δ′)

mlb-type-first-order-non∀ᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorᵢ p q →
  Non∀ (mlb-typeᵢ {Γ = Γ} p q)
mlb-type-first-order-non∀ᵢ fo-star-starᵢ = non∀-★
mlb-type-first-order-non∀ᵢ fo-var-varᵢ = non∀-＇
mlb-type-first-order-non∀ᵢ fo-base-baseᵢ = non∀-‵
mlb-type-first-order-non∀ᵢ fo-base-starᵢ = non∀-‵
mlb-type-first-order-non∀ᵢ fo-star-baseᵢ = non∀-‵
mlb-type-first-order-non∀ᵢ fo-tag-tagᵢ = non∀-★
mlb-type-first-order-non∀ᵢ (fo-arrow-arrowᵢ route₁ route₂) = non∀-⇒
mlb-type-first-order-non∀ᵢ (fo-arrow-starᵢ route₁ route₂) = non∀-⇒
mlb-type-first-order-non∀ᵢ (fo-star-arrowᵢ route₁ route₂) = non∀-⇒
mlb-type-first-order-non∀ᵢ fo-tag-arrow-tag-arrowᵢ = non∀-★
mlb-type-first-order-non∀ᵢ fo-star-varᵢ = non∀-＇
mlb-type-first-order-non∀ᵢ fo-tagvar-tagvarᵢ = non∀-★
mlb-type-first-order-non∀ᵢ fo-var-starᵢ = non∀-＇

first-order-left-target-non∀ᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorᵢ p q →
  Non∀ A
first-order-left-target-non∀ᵢ fo-star-starᵢ = non∀-★
first-order-left-target-non∀ᵢ fo-var-varᵢ = non∀-＇
first-order-left-target-non∀ᵢ fo-base-baseᵢ = non∀-‵
first-order-left-target-non∀ᵢ fo-base-starᵢ = non∀-‵
first-order-left-target-non∀ᵢ fo-star-baseᵢ = non∀-★
first-order-left-target-non∀ᵢ fo-tag-tagᵢ = non∀-★
first-order-left-target-non∀ᵢ (fo-arrow-arrowᵢ route₁ route₂) = non∀-⇒
first-order-left-target-non∀ᵢ (fo-arrow-starᵢ route₁ route₂) = non∀-⇒
first-order-left-target-non∀ᵢ (fo-star-arrowᵢ route₁ route₂) = non∀-★
first-order-left-target-non∀ᵢ fo-tag-arrow-tag-arrowᵢ = non∀-★
first-order-left-target-non∀ᵢ fo-star-varᵢ = non∀-★
first-order-left-target-non∀ᵢ fo-tagvar-tagvarᵢ = non∀-★
first-order-left-target-non∀ᵢ fo-var-starᵢ = non∀-＇

first-order-right-target-non∀ᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorᵢ p q →
  Non∀ B
first-order-right-target-non∀ᵢ fo-star-starᵢ = non∀-★
first-order-right-target-non∀ᵢ fo-var-varᵢ = non∀-＇
first-order-right-target-non∀ᵢ fo-base-baseᵢ = non∀-‵
first-order-right-target-non∀ᵢ fo-base-starᵢ = non∀-★
first-order-right-target-non∀ᵢ fo-star-baseᵢ = non∀-‵
first-order-right-target-non∀ᵢ fo-tag-tagᵢ = non∀-★
first-order-right-target-non∀ᵢ (fo-arrow-arrowᵢ route₁ route₂) = non∀-⇒
first-order-right-target-non∀ᵢ (fo-arrow-starᵢ route₁ route₂) = non∀-★
first-order-right-target-non∀ᵢ (fo-star-arrowᵢ route₁ route₂) = non∀-⇒
first-order-right-target-non∀ᵢ fo-tag-arrow-tag-arrowᵢ = non∀-★
first-order-right-target-non∀ᵢ fo-star-varᵢ = non∀-＇
first-order-right-target-non∀ᵢ fo-tagvar-tagvarᵢ = non∀-★
first-order-right-target-non∀ᵢ fo-var-starᵢ = non∀-★

mlb-type-first-order-neither-no-occursᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ false
mlb-type-first-order-neither-no-occursᵢ fo-star-starᵢ = refl
mlb-type-first-order-neither-no-occursᵢ
    (fo-var-varᵢ {W = zero} {w⊑x = w⊑x}) =
  ⊥-elim (no-νctx-zero-varᵢ w⊑x)
mlb-type-first-order-neither-no-occursᵢ
    (fo-var-varᵢ {W = suc W} {w⊑x = there w⊑x}
      {w⊑y = there w⊑y}) =
  refl
mlb-type-first-order-neither-no-occursᵢ fo-base-baseᵢ = refl
mlb-type-first-order-neither-no-occursᵢ fo-base-starᵢ = refl
mlb-type-first-order-neither-no-occursᵢ fo-star-baseᵢ = refl
mlb-type-first-order-neither-no-occursᵢ fo-tag-tagᵢ = refl
mlb-type-first-order-neither-no-occursᵢ
    (fo-arrow-arrowᵢ route₁ route₂)
    rewrite mlb-type-first-order-neither-no-occursᵢ route₁
          | mlb-type-first-order-neither-no-occursᵢ route₂ =
  refl
mlb-type-first-order-neither-no-occursᵢ
    (fo-arrow-starᵢ route₁ route₂)
    rewrite mlb-type-first-order-neither-no-occursᵢ route₁
          | mlb-type-first-order-neither-no-occursᵢ route₂ =
  refl
mlb-type-first-order-neither-no-occursᵢ
    (fo-star-arrowᵢ route₁ route₂)
    rewrite mlb-type-first-order-neither-no-occursᵢ route₁
          | mlb-type-first-order-neither-no-occursᵢ route₂ =
  refl
mlb-type-first-order-neither-no-occursᵢ fo-tag-arrow-tag-arrowᵢ =
  refl
mlb-type-first-order-neither-no-occursᵢ
    (fo-star-varᵢ {W = zero} {w⊑y = w⊑y}) =
  ⊥-elim (no-νctx-zero-varᵢ w⊑y)
mlb-type-first-order-neither-no-occursᵢ
    (fo-star-varᵢ {W = suc W} {w⊑★ = there w⊑★}
      {w⊑y = there w⊑y}) =
  refl
mlb-type-first-order-neither-no-occursᵢ fo-tagvar-tagvarᵢ = refl
mlb-type-first-order-neither-no-occursᵢ
    (fo-var-starᵢ {W = zero} {w⊑x = w⊑x}) =
  ⊥-elim (no-νctx-zero-varᵢ w⊑x)
mlb-type-first-order-neither-no-occursᵢ
    (fo-var-starᵢ {W = suc W} {w⊑x = there w⊑x}
      {w⊑★ = there w⊑★}) =
  refl

mlb-type-first-order-neither-occurs-impossibleᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : FirstOrderSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ true →
  ⊥
mlb-type-first-order-neither-occurs-impossibleᵢ route occ
    with mlb-type-first-order-neither-no-occursᵢ route
mlb-type-first-order-neither-occurs-impossibleᵢ route occ | no-occ =
  false≠trueᵢ (trans (sym no-occ) occ)

mlb-type-maximal-first-orderᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  FirstOrderSelectorᵢ p q →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} p q
mlb-type-maximal-first-orderᵢ route
    with mlb-type-comparable-first-orderᵢ route
mlb-type-maximal-first-orderᵢ route | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

maximal-arrow-arrow-from-maximalᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ A₂ B₁ B₂} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ B₁ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₂ B₂ →
  MaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
maximal-arrow-arrow-from-maximalᶜᵢ mlb₁ mlb₂ =
  record
    { lowerᶜᵢ = lowerᶜᵢ mlb₁ ⇒ lowerᶜᵢ mlb₂
    ; lower-leftᶜᵢ = lower-leftᶜᵢ mlb₁ ↦ lower-leftᶜᵢ mlb₂
    ; lower-rightᶜᵢ = lower-rightᶜᵢ mlb₁ ↦ lower-rightᶜᵢ mlb₂
    ; maximalᶜᵢ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (_ ⇒ _) (_ ⇒ _) D →
      ¬ StrictlyBelowᶜᵢ _ _ (lowerᶜᵢ mlb₁ ⇒ lowerᶜᵢ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜᵢ mlb₁ (D₁⊑A₁ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜᵢ mlb₂ (D₂⊑A₂ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )

maximal-star-arrow-from-maximalᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ B₁ B₂} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ B₁ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ B₂ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ ★ (B₁ ⇒ B₂)
maximal-star-arrow-from-maximalᶜᵢ mlb₁ mlb₂ =
  record
    { lowerᶜᵢ = lowerᶜᵢ mlb₁ ⇒ lowerᶜᵢ mlb₂
    ; lower-leftᶜᵢ = tag_⇛_ (lower-leftᶜᵢ mlb₁) (lower-leftᶜᵢ mlb₂)
    ; lower-rightᶜᵢ = lower-rightᶜᵢ mlb₁ ↦ lower-rightᶜᵢ mlb₂
    ; maximalᶜᵢ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ ★ (_ ⇒ _) D →
      ¬ StrictlyBelowᶜᵢ _ _ (lowerᶜᵢ mlb₁ ⇒ lowerᶜᵢ mlb₂) D
    maximal′ ((tag_⇛_ D₁⊑★ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜᵢ mlb₁ (D₁⊑★ , D₁⊑B₁)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜᵢ mlb₂ (D₂⊑★ , D₂⊑B₂)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )
    maximal′ (id★ , ()) ((tag_⇛_ C₁⊑★ C₂⊑★) , ¬D⊑C)

maximal-arrow-star-from-maximalᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ A₂} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₁ ★ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A₂ ★ →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) ★
maximal-arrow-star-from-maximalᶜᵢ mlb₁ mlb₂ =
  record
    { lowerᶜᵢ = lowerᶜᵢ mlb₁ ⇒ lowerᶜᵢ mlb₂
    ; lower-leftᶜᵢ = lower-leftᶜᵢ mlb₁ ↦ lower-leftᶜᵢ mlb₂
    ; lower-rightᶜᵢ = tag_⇛_ (lower-rightᶜᵢ mlb₁) (lower-rightᶜᵢ mlb₂)
    ; maximalᶜᵢ = maximal′
    }
  where
    maximal′ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (_ ⇒ _) ★ D →
      ¬ StrictlyBelowᶜᵢ _ _ (lowerᶜᵢ mlb₁ ⇒ lowerᶜᵢ mlb₂) D
    maximal′ ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag_⇛_ D₁⊑★ D₂⊑★))
        ((C₁⊑D₁ ↦ C₂⊑D₂) , ¬D⊑C) =
      maximalᶜᵢ mlb₁ (D₁⊑A₁ , D₁⊑★)
        ( C₁⊑D₁
        , λ D₁⊑C₁ →
            maximalᶜᵢ mlb₂ (D₂⊑A₂ , D₂⊑★)
              ( C₂⊑D₂
              , λ D₂⊑C₂ → ¬D⊑C (D₁⊑C₁ ↦ D₂⊑C₂)
              )
        )

------------------------------------------------------------------------
-- Canonical first-order selector and coherence
------------------------------------------------------------------------

data CanonicalLowerᵢ : TyCtx → Ty → Ty → Ty → Set where
  can-star-star :
    ∀ {Δ} →
    CanonicalLowerᵢ Δ ★ ★ ★

  can-base-base :
    ∀ {Δ ι} →
    CanonicalLowerᵢ Δ (‵ ι) (‵ ι) (‵ ι)

  can-base-star :
    ∀ {Δ ι} →
    CanonicalLowerᵢ Δ (‵ ι) ★ (‵ ι)

  can-star-base :
    ∀ {Δ ι} →
    CanonicalLowerᵢ Δ ★ (‵ ι) (‵ ι)

  can-var-var :
    ∀ {Δ X} →
    X < Δ →
    CanonicalLowerᵢ Δ (＇ X) (＇ X) (＇ X)

  can-arrow-arrow :
    ∀ {Δ A₁ A₂ B₁ B₂ C₁ C₂} →
    CanonicalLowerᵢ Δ A₁ B₁ C₁ →
    CanonicalLowerᵢ Δ A₂ B₂ C₂ →
    CanonicalLowerᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) (C₁ ⇒ C₂)

  can-star-arrow :
    ∀ {Δ B₁ B₂ C₁ C₂} →
    CanonicalLowerᵢ Δ ★ B₁ C₁ →
    CanonicalLowerᵢ Δ ★ B₂ C₂ →
    CanonicalLowerᵢ Δ ★ (B₁ ⇒ B₂) (C₁ ⇒ C₂)

  can-arrow-star :
    ∀ {Δ A₁ A₂ C₁ C₂} →
    CanonicalLowerᵢ Δ A₁ ★ C₁ →
    CanonicalLowerᵢ Δ A₂ ★ C₂ →
    CanonicalLowerᵢ Δ (A₁ ⇒ A₂) ★ (C₁ ⇒ C₂)

canonical-lower-leftᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ
canonical-lower-leftᵢ can-star-star = id★
canonical-lower-leftᵢ can-base-base = idι
canonical-lower-leftᵢ can-base-star = idι
canonical-lower-leftᵢ can-star-base = tag _
canonical-lower-leftᵢ (can-var-var X<Δ) = idˣ (idᵢ-lookup X<Δ) X<Δ X<Δ
canonical-lower-leftᵢ (can-arrow-arrow c₁ c₂) =
  canonical-lower-leftᵢ c₁ ↦ canonical-lower-leftᵢ c₂
canonical-lower-leftᵢ (can-star-arrow c₁ c₂) =
  tag_⇛_ (canonical-lower-leftᵢ c₁) (canonical-lower-leftᵢ c₂)
canonical-lower-leftᵢ (can-arrow-star c₁ c₂) =
  canonical-lower-leftᵢ c₁ ↦ canonical-lower-leftᵢ c₂

canonical-lower-rightᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
canonical-lower-rightᵢ can-star-star = id★
canonical-lower-rightᵢ can-base-base = idι
canonical-lower-rightᵢ can-base-star = tag _
canonical-lower-rightᵢ can-star-base = idι
canonical-lower-rightᵢ (can-var-var X<Δ) = idˣ (idᵢ-lookup X<Δ) X<Δ X<Δ
canonical-lower-rightᵢ (can-arrow-arrow c₁ c₂) =
  canonical-lower-rightᵢ c₁ ↦ canonical-lower-rightᵢ c₂
canonical-lower-rightᵢ (can-star-arrow c₁ c₂) =
  canonical-lower-rightᵢ c₁ ↦ canonical-lower-rightᵢ c₂
canonical-lower-rightᵢ (can-arrow-star c₁ c₂) =
  tag_⇛_ (canonical-lower-rightᵢ c₁) (canonical-lower-rightᵢ c₂)

canonical-lower-comparableᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  ComparableMaximalLowerBoundᵢ Δ A B
canonical-lower-comparableᵢ can-star-star = comparable-star-starᵢ
canonical-lower-comparableᵢ can-base-base = comparable-base-baseᵢ
canonical-lower-comparableᵢ can-base-star = comparable-base-starᵢ
canonical-lower-comparableᵢ can-star-base = comparable-star-baseᵢ
canonical-lower-comparableᵢ (can-var-var X<Δ) = comparable-var-varᵢ X<Δ
canonical-lower-comparableᵢ (can-arrow-arrow c₁ c₂) =
  comparable-arrow-arrowᵢ
    (canonical-lower-comparableᵢ c₁)
    (canonical-lower-comparableᵢ c₂)
canonical-lower-comparableᵢ (can-star-arrow c₁ c₂) =
  comparable-star-arrowᵢ
    (canonical-lower-comparableᵢ c₁)
    (canonical-lower-comparableᵢ c₂)
canonical-lower-comparableᵢ (can-arrow-star c₁ c₂) =
  comparable-arrow-starᵢ
    (canonical-lower-comparableᵢ c₁)
    (canonical-lower-comparableᵢ c₂)

canonical-lower-comparable-lowerᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ Δ A B C) →
  c-lowerᵢ (canonical-lower-comparableᵢ can) ≡ C
canonical-lower-comparable-lowerᵢ can-star-star = refl
canonical-lower-comparable-lowerᵢ can-base-base = refl
canonical-lower-comparable-lowerᵢ can-base-star = refl
canonical-lower-comparable-lowerᵢ can-star-base = refl
canonical-lower-comparable-lowerᵢ (can-var-var X<Δ) = refl
canonical-lower-comparable-lowerᵢ (can-arrow-arrow c₁ c₂)
    rewrite canonical-lower-comparable-lowerᵢ c₁
          | canonical-lower-comparable-lowerᵢ c₂ = refl
canonical-lower-comparable-lowerᵢ (can-star-arrow c₁ c₂)
    rewrite canonical-lower-comparable-lowerᵢ c₁
          | canonical-lower-comparable-lowerᵢ c₂ = refl
canonical-lower-comparable-lowerᵢ (can-arrow-star c₁ c₂)
    rewrite canonical-lower-comparable-lowerᵢ c₁
          | canonical-lower-comparable-lowerᵢ c₂ = refl

canonical-lower-maximalᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  MaximalLowerBoundᵢ Δ A B
canonical-lower-maximalᵢ can =
  comparable⇒maximalᵢ (canonical-lower-comparableᵢ can)

canonical-lower-comparable-idᶜᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  ComparableMaximalLowerBoundᶜᵢ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
canonical-lower-comparable-idᶜᵢ can =
  comparable-idᶜᵢ (canonical-lower-comparableᵢ can)

canonical-lower-comparable-id-lowerᶜᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ Δ A B C) →
  cᶜ-lowerᵢ (canonical-lower-comparable-idᶜᵢ can) ≡ C
canonical-lower-comparable-id-lowerᶜᵢ can =
  canonical-lower-comparable-lowerᵢ can

canonical-lower-maximal-lowerᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ Δ A B C) →
  lowerᵢ (canonical-lower-maximalᵢ can) ≡ C
canonical-lower-maximal-lowerᵢ can =
  canonical-lower-comparable-lowerᵢ can

canonical-lower-non∀ᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  Non∀ C
canonical-lower-non∀ᵢ can-star-star = non∀-★
canonical-lower-non∀ᵢ can-base-base = non∀-‵
canonical-lower-non∀ᵢ can-base-star = non∀-‵
canonical-lower-non∀ᵢ can-star-base = non∀-‵
canonical-lower-non∀ᵢ (can-var-var X<Δ) = non∀-＇
canonical-lower-non∀ᵢ (can-arrow-arrow c₁ c₂) = non∀-⇒
canonical-lower-non∀ᵢ (can-star-arrow c₁ c₂) = non∀-⇒
canonical-lower-non∀ᵢ (can-arrow-star c₁ c₂) = non∀-⇒

non∀-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Non∀ A →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Non∀ B
non∀-targetᵢ non∀-★ id★ = non∀-★
non∀-targetᵢ non∀-＇ (idˣ _ _ _) = non∀-＇
non∀-targetᵢ non∀-‵ idι = non∀-‵
non∀-targetᵢ non∀-⇒ (p ↦ q) = non∀-⇒
non∀-targetᵢ non∀-‵ (tag ι) = non∀-★
non∀-targetᵢ non∀-⇒ (tag p ⇛ q) = non∀-★
non∀-targetᵢ non∀-＇ (tagˣ _ _) = non∀-★

non∀-⊑∀-impossibleᵢ :
  ∀ {Φ Δᴸ Δᴿ A C} →
  Non∀ C →
  Φ ∣ Δᴸ ⊢ C ⊑ `∀ A ⊣ Δᴿ →
  ⊥
non∀-⊑∀-impossibleᵢ non∀-＇ ()
non∀-⊑∀-impossibleᵢ non∀-‵ ()
non∀-⊑∀-impossibleᵢ non∀-★ ()
non∀-⊑∀-impossibleᵢ non∀-⇒ ()

canonical-lower-occurs-leftᵢ :
  ∀ {Δ A B C X} →
  CanonicalLowerᵢ Δ A B C →
  occurs X A ≡ true →
  occurs X C ≡ true
canonical-lower-occurs-leftᵢ can-star-star ()
canonical-lower-occurs-leftᵢ can-base-base ()
canonical-lower-occurs-leftᵢ can-base-star ()
canonical-lower-occurs-leftᵢ can-star-base ()
canonical-lower-occurs-leftᵢ (can-var-var X<Δ) occ = occ
canonical-lower-occurs-leftᵢ {X = X}
    (can-arrow-arrow {A₁ = A₁} c₁ c₂) occ
    with occurs X A₁ in occ₁
canonical-lower-occurs-leftᵢ {X = X}
    (can-arrow-arrow {A₁ = A₁} c₁ c₂) occ | true =
  ∨-true-leftᵢ (canonical-lower-occurs-leftᵢ c₁ occ₁)
canonical-lower-occurs-leftᵢ {X = X}
    (can-arrow-arrow {A₁ = A₁} c₁ c₂) occ | false =
  ∨-true-rightᵢ (canonical-lower-occurs-leftᵢ c₂ occ)
canonical-lower-occurs-leftᵢ (can-star-arrow c₁ c₂) ()
canonical-lower-occurs-leftᵢ {X = X}
    (can-arrow-star {A₁ = A₁} c₁ c₂) occ
    with occurs X A₁ in occ₁
canonical-lower-occurs-leftᵢ {X = X}
    (can-arrow-star {A₁ = A₁} c₁ c₂) occ | true =
  ∨-true-leftᵢ (canonical-lower-occurs-leftᵢ c₁ occ₁)
canonical-lower-occurs-leftᵢ {X = X}
    (can-arrow-star {A₁ = A₁} c₁ c₂) occ | false =
  ∨-true-rightᵢ (canonical-lower-occurs-leftᵢ c₂ occ)

canonical-lower-occurs-rightᵢ :
  ∀ {Δ A B C X} →
  CanonicalLowerᵢ Δ A B C →
  occurs X B ≡ true →
  occurs X C ≡ true
canonical-lower-occurs-rightᵢ can-star-star ()
canonical-lower-occurs-rightᵢ can-base-base ()
canonical-lower-occurs-rightᵢ can-base-star ()
canonical-lower-occurs-rightᵢ can-star-base ()
canonical-lower-occurs-rightᵢ (can-var-var X<Δ) occ = occ
canonical-lower-occurs-rightᵢ {X = X}
    (can-arrow-arrow {B₁ = B₁} c₁ c₂) occ
    with occurs X B₁ in occ₁
canonical-lower-occurs-rightᵢ {X = X}
    (can-arrow-arrow {B₁ = B₁} c₁ c₂) occ | true =
  ∨-true-leftᵢ (canonical-lower-occurs-rightᵢ c₁ occ₁)
canonical-lower-occurs-rightᵢ {X = X}
    (can-arrow-arrow {B₁ = B₁} c₁ c₂) occ | false =
  ∨-true-rightᵢ (canonical-lower-occurs-rightᵢ c₂ occ)
canonical-lower-occurs-rightᵢ {X = X}
    (can-star-arrow {B₁ = B₁} c₁ c₂) occ
    with occurs X B₁ in occ₁
canonical-lower-occurs-rightᵢ {X = X}
    (can-star-arrow {B₁ = B₁} c₁ c₂) occ | true =
  ∨-true-leftᵢ (canonical-lower-occurs-rightᵢ c₁ occ₁)
canonical-lower-occurs-rightᵢ {X = X}
    (can-star-arrow {B₁ = B₁} c₁ c₂) occ | false =
  ∨-true-rightᵢ (canonical-lower-occurs-rightᵢ c₂ occ)
canonical-lower-occurs-rightᵢ (can-arrow-star c₁ c₂) ()

canonical-first-order-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  CanonicalLowerᵢ Δᴸ A B C →
  CanonicalLowerᵢ Δᴿ A′ B′ C′ →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ
canonical-first-order-coherenceᵢ can-star-star can-star-star id★ id★ = id★
canonical-first-order-coherenceᵢ can-base-base can-base-base idι idι = idι
canonical-first-order-coherenceᵢ can-base-base can-base-star idι (tag ι) = idι
canonical-first-order-coherenceᵢ can-base-base can-star-base (tag ι) idι = idι
canonical-first-order-coherenceᵢ can-base-base can-star-star (tag ι) (tag .ι) =
  tag ι
canonical-first-order-coherenceᵢ can-base-star can-base-star idι id★ = idι
canonical-first-order-coherenceᵢ can-base-star can-star-star (tag ι) id★ =
  tag ι
canonical-first-order-coherenceᵢ can-star-base can-star-base id★ idι = idι
canonical-first-order-coherenceᵢ can-star-base can-star-star id★ (tag ι) =
  tag ι
canonical-first-order-coherenceᵢ (can-var-var X<Δ) (can-var-var Y<Δ)
    (idˣ x⊑y X<Δᴸ Y<Δᴿ) (idˣ x⊑y′ _ _) =
  idˣ x⊑y X<Δᴸ Y<Δᴿ
canonical-first-order-coherenceᵢ (can-var-var X<Δ) can-star-star
    (tagˣ x⊑★ X<Δᴸ) (tagˣ _ _) =
  tagˣ x⊑★ X<Δᴸ
canonical-first-order-coherenceᵢ (can-arrow-arrow c₁ c₂)
    (can-arrow-arrow c₁′ c₂′)
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  canonical-first-order-coherenceᵢ c₁ c₁′ p₁ q₁ ↦
  canonical-first-order-coherenceᵢ c₂ c₂′ p₂ q₂
canonical-first-order-coherenceᵢ (can-arrow-arrow c₁ c₂)
    (can-arrow-star c₁′ c₂′)
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  canonical-first-order-coherenceᵢ c₁ c₁′ p₁ q₁ ↦
  canonical-first-order-coherenceᵢ c₂ c₂′ p₂ q₂
canonical-first-order-coherenceᵢ (can-arrow-arrow c₁ c₂)
    (can-star-arrow c₁′ c₂′)
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  canonical-first-order-coherenceᵢ c₁ c₁′ p₁ q₁ ↦
  canonical-first-order-coherenceᵢ c₂ c₂′ p₂ q₂
canonical-first-order-coherenceᵢ (can-arrow-arrow c₁ c₂)
    can-star-star
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  tag_⇛_
    (canonical-first-order-coherenceᵢ c₁ can-star-star p₁ q₁)
    (canonical-first-order-coherenceᵢ c₂ can-star-star p₂ q₂)
canonical-first-order-coherenceᵢ (can-star-arrow c₁ c₂)
    (can-star-arrow c₁′ c₂′)
    id★ (q₁ ↦ q₂) =
  canonical-first-order-coherenceᵢ c₁ c₁′ id★ q₁ ↦
  canonical-first-order-coherenceᵢ c₂ c₂′ id★ q₂
canonical-first-order-coherenceᵢ (can-star-arrow c₁ c₂)
    can-star-star
    id★ (tag q₁ ⇛ q₂) =
  tag_⇛_
    (canonical-first-order-coherenceᵢ c₁ can-star-star id★ q₁)
    (canonical-first-order-coherenceᵢ c₂ can-star-star id★ q₂)
canonical-first-order-coherenceᵢ (can-arrow-star c₁ c₂)
    (can-arrow-star c₁′ c₂′)
    (p₁ ↦ p₂) id★ =
  canonical-first-order-coherenceᵢ c₁ c₁′ p₁ id★ ↦
  canonical-first-order-coherenceᵢ c₂ c₂′ p₂ id★
canonical-first-order-coherenceᵢ (can-arrow-star c₁ c₂)
    can-star-star
    (tag p₁ ⇛ p₂) id★ =
  tag_⇛_
    (canonical-first-order-coherenceᵢ c₁ can-star-star p₁ id★)
    (canonical-first-order-coherenceᵢ c₂ can-star-star p₂ id★)

leftChoice-id-no-starᵢ :
  ∀ {Δ W} →
  (W ˣ⊑★) ∈ leftChoiceᵢ (choice-idᵢ Δ) →
  ⊥
leftChoice-id-no-starᵢ {Δ = Δ} w⊑★ =
  idᵢ-no-star
    (subst (λ Φ → _ ∈ Φ) (leftChoice-idᵢ Δ) w⊑★)

rightChoice-id-no-starᵢ :
  ∀ {Δ W} →
  (W ˣ⊑★) ∈ rightChoiceᵢ (choice-idᵢ Δ) →
  ⊥
rightChoice-id-no-starᵢ {Δ = Δ} w⊑★ =
  idᵢ-no-star
    (subst (λ Φ → _ ∈ Φ) (rightChoice-idᵢ Δ) w⊑★)

leftChoice-id-var-identityᵢ :
  ∀ {Δ W X} →
  (W ˣ⊑ˣ X) ∈ leftChoiceᵢ (choice-idᵢ Δ) →
  W ≡ X
leftChoice-id-var-identityᵢ {Δ = Δ} w⊑x =
  idᵢ-var-identity
    (subst (λ Φ → _ ∈ Φ) (leftChoice-idᵢ Δ) w⊑x)

rightChoice-id-var-identityᵢ :
  ∀ {Δ W Y} →
  (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ (choice-idᵢ Δ) →
  W ≡ Y
rightChoice-id-var-identityᵢ {Δ = Δ} w⊑y =
  idᵢ-var-identity
    (subst (λ Φ → _ ∈ Φ) (rightChoice-idᵢ Δ) w⊑y)

choice-id-var-var-selfᵢ :
  ∀ Δ {W X Y} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ (choice-idᵢ Δ)) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ (choice-idᵢ Δ)) →
  choice-var-varᵢ (choice-idᵢ Δ) w⊑x w⊑y ≡ W
choice-id-var-var-selfᵢ zero ()
choice-id-var-var-selfᵢ (suc Δ)
    (here refl) (here refl) =
  refl
choice-id-var-var-selfᵢ (suc Δ)
    (here refl) (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑y)
choice-id-var-var-selfᵢ (suc Δ)
    (there w⊑x) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-id-var-var-selfᵢ (suc Δ)
    {W = zero} (there w⊑x) w⊑y =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑x)
choice-id-var-var-selfᵢ (suc Δ)
    {W = suc W} {X = zero} (there w⊑x) w⊑y =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑x)
choice-id-var-var-selfᵢ (suc Δ)
    {W = suc W} {Y = zero} w⊑x (there w⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑y)
choice-id-var-var-selfᵢ (suc Δ)
    {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑x) (there w⊑y) =
  cong suc
    (choice-id-var-var-selfᵢ Δ
      (un⇑ᵢ-ˣ∈ w⊑x)
      (un⇑ᵢ-ˣ∈ w⊑y))

choice-id-var-var-canonicalᵢ :
  ∀ Δ {W X Y} →
  (w⊑x : (W ˣ⊑ˣ X) ∈ leftChoiceᵢ (choice-idᵢ Δ)) →
  (w⊑y : (W ˣ⊑ˣ Y) ∈ rightChoiceᵢ (choice-idᵢ Δ)) →
  W < Δ →
  CanonicalLowerᵢ Δ (＇ X) (＇ Y)
    (＇ choice-var-varᵢ (choice-idᵢ Δ) w⊑x w⊑y)
choice-id-var-var-canonicalᵢ Δ {W = W} {X = X} {Y = Y}
    w⊑x w⊑y W<Δ =
  subst
    (λ Z → CanonicalLowerᵢ Δ (＇ X) (＇ Y) (＇ Z))
    (sym (choice-id-var-var-selfᵢ Δ w⊑x w⊑y))
    (subst
      (λ Y′ → CanonicalLowerᵢ Δ (＇ X) (＇ Y′) (＇ W))
      (rightChoice-id-var-identityᵢ w⊑y)
      (subst
        (λ X′ → CanonicalLowerᵢ Δ (＇ X′) (＇ W) (＇ W))
        (leftChoice-id-var-identityᵢ w⊑x)
        (can-var-var W<Δ)))

mlb-type-choice-id-first-order-canonicalᵢ :
  ∀ {Δ C A B}
    {p : leftChoiceᵢ (choice-idᵢ Δ) ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : rightChoiceᵢ (choice-idᵢ Δ) ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δ}
    {Δᶜ = Δ}
    {Δᴸ = Δ}
    {Δᴿ = Δ}
    p
    q →
  CanonicalLowerᵢ Δ A B (mlb-typeᵢ {Γ = choice-idᵢ Δ} p q)
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ} fo-star-star-atᵢ
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  can-star-star
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ}
    (fo-var-var-atᵢ {w⊑x = w⊑x} {w⊑y = w⊑y} {W<Δ = W<Δ}) =
  choice-id-var-var-canonicalᵢ Δ w⊑x w⊑y W<Δ
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ} fo-base-base-atᵢ
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  can-base-base
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ} fo-base-star-atᵢ
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  can-base-star
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ} fo-star-base-atᵢ
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  can-star-base
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ} fo-tag-tag-atᵢ
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  can-star-star
mlb-type-choice-id-first-order-canonicalᵢ
    (fo-arrow-arrow-atᵢ route₁ route₂) =
  can-arrow-arrow
    (mlb-type-choice-id-first-order-canonicalᵢ route₁)
    (mlb-type-choice-id-first-order-canonicalᵢ route₂)
mlb-type-choice-id-first-order-canonicalᵢ
    (fo-arrow-star-atᵢ route₁ route₂) =
  can-arrow-star
    (mlb-type-choice-id-first-order-canonicalᵢ route₁)
    (mlb-type-choice-id-first-order-canonicalᵢ route₂)
mlb-type-choice-id-first-order-canonicalᵢ
    (fo-star-arrow-atᵢ route₁ route₂) =
  can-star-arrow
    (mlb-type-choice-id-first-order-canonicalᵢ route₁)
    (mlb-type-choice-id-first-order-canonicalᵢ route₂)
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ}
    fo-tag-arrow-tag-arrow-atᵢ
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  can-star-star
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ}
    (fo-star-var-atᵢ {w⊑★ = w⊑★}) =
  ⊥-elim (leftChoice-id-no-starᵢ w⊑★)
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ}
    (fo-tagvar-tagvar-atᵢ {w⊑★ = w⊑★}) =
  ⊥-elim (leftChoice-id-no-starᵢ w⊑★)
mlb-type-choice-id-first-order-canonicalᵢ {Δ = Δ}
    (fo-var-star-atᵢ {w⊑★ = w⊑★}) =
  ⊥-elim (rightChoice-id-no-starᵢ w⊑★)

mlb-type-from-lower-first-order-canonicalᵢ :
  ∀ {Δ C A B}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δ}
    {Δᶜ = Δ}
    {Δᴸ = Δ}
    {Δᴿ = Δ}
    (leftChoice-id-proofAtᵢ p)
    (rightChoice-id-proofAtᵢ q) →
  CanonicalLowerᵢ Δ A B (mlb-type-from-lowerᵢ p q)
mlb-type-from-lower-first-order-canonicalᵢ {Δ = Δ} {p = p} {q = q}
    route
    rewrite leftChoice-idᵢ Δ | rightChoice-idᵢ Δ =
  mlb-type-choice-id-first-order-canonicalᵢ route

mlb-type-choice-id-first-order-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p :
      leftChoiceᵢ (choice-idᵢ Δᴸ) ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q :
      rightChoiceᵢ (choice-idᵢ Δᴸ) ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ :
      leftChoiceᵢ (choice-idᵢ Δᴿ) ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ :
      rightChoiceᵢ (choice-idᵢ Δᴿ) ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δᴸ}
    {Δᶜ = Δᴸ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴸ}
    p
    q →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δᴿ}
    {Δᶜ = Δᴿ}
    {Δᴸ = Δᴿ}
    {Δᴿ = Δᴿ}
    p′
    q′ →
  Φ ∣ Δᴸ ⊢
    mlb-typeᵢ {Γ = choice-idᵢ Δᴸ} p q
    ⊑ mlb-typeᵢ {Γ = choice-idᵢ Δᴿ} p′ q′
    ⊣ Δᴿ
mlb-type-choice-id-first-order-coherenceᵢ {pA = pA} {pB = pB}
    route route′ =
  canonical-first-order-coherenceᵢ
    (mlb-type-choice-id-first-order-canonicalᵢ route)
    (mlb-type-choice-id-first-order-canonicalᵢ route′)
    pA
    pB

mlb-type-from-lower-first-order-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δᴸ}
    {Δᶜ = Δᴸ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴸ}
    (leftChoice-id-proofAtᵢ p)
    (rightChoice-id-proofAtᵢ q) →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δᴿ}
    {Δᶜ = Δᴿ}
    {Δᴸ = Δᴿ}
    {Δᴿ = Δᴿ}
    (leftChoice-id-proofAtᵢ p′)
    (rightChoice-id-proofAtᵢ q′) →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p q ⊑ mlb-type-from-lowerᵢ p′ q′
    ⊣ Δᴿ
mlb-type-from-lower-first-order-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ =
  mlb-type-choice-id-first-order-coherenceᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = C}
    {C′ = C′}
    {pA = pA}
    {pB = pB}
    {p = leftChoice-id-proofAtᵢ p}
    {q = rightChoice-id-proofAtᵢ q}
    {p′ = leftChoice-id-proofAtᵢ p′}
    {q′ = rightChoice-id-proofAtᵢ q′}
    route
    route′

mlb-type-arrow-arrow-coherenceᵢ :
  ∀ {Φ Γ Γ′ A₁ A₂ A₁′ A₂′ B₁ B₂ B₁′ B₂′ C₁ C₂ C₁′ C₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ A₁′ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ A₂′ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ B₁′ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ B₂′ ⊣ choiceRightCtxᵢ Γ′} →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p₁ q₁
    ⊑ mlb-typeᵢ {Γ = Γ′} p₁′ q₁′
    ⊣ choiceCommonCtxᵢ Γ′ →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p₂ q₂
    ⊑ mlb-typeᵢ {Γ = Γ′} p₂′ q₂′
    ⊣ choiceCommonCtxᵢ Γ′ →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (p₁ ↦ p₂) (q₁ ↦ q₂)
    ⊑ mlb-typeᵢ {Γ = Γ′} (p₁′ ↦ p₂′) (q₁′ ↦ q₂′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-arrow-arrow-coherenceᵢ lower₁ lower₂ =
  lower₁ ↦ lower₂

mlb-type-arrow-star-coherenceᵢ :
  ∀ {Φ Γ Γ′ A₁ A₂ A₁′ A₂′ C₁ C₂ C₁′ C₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ A₁′ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ A₂′ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′} →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p₁ q₁
    ⊑ mlb-typeᵢ {Γ = Γ′} p₁′ q₁′
    ⊣ choiceCommonCtxᵢ Γ′ →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p₂ q₂
    ⊑ mlb-typeᵢ {Γ = Γ′} p₂′ q₂′
    ⊣ choiceCommonCtxᵢ Γ′ →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (p₁ ↦ p₂) (tag q₁ ⇛ q₂)
    ⊑ mlb-typeᵢ {Γ = Γ′} (p₁′ ↦ p₂′) (tag q₁′ ⇛ q₂′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-arrow-star-coherenceᵢ lower₁ lower₂ =
  lower₁ ↦ lower₂

mlb-type-star-arrow-coherenceᵢ :
  ∀ {Φ Γ Γ′ B₁ B₂ B₁′ B₂′ C₁ C₂ C₁′ C₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ B₁′ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ B₂′ ⊣ choiceRightCtxᵢ Γ′} →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p₁ q₁
    ⊑ mlb-typeᵢ {Γ = Γ′} p₁′ q₁′
    ⊣ choiceCommonCtxᵢ Γ′ →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p₂ q₂
    ⊑ mlb-typeᵢ {Γ = Γ′} p₂′ q₂′
    ⊣ choiceCommonCtxᵢ Γ′ →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (tag p₁ ⇛ p₂) (q₁ ↦ q₂)
    ⊑ mlb-typeᵢ {Γ = Γ′} (tag p₁′ ⇛ p₂′) (q₁′ ↦ q₂′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-star-arrow-coherenceᵢ lower₁ lower₂ =
  lower₁ ↦ lower₂

mlb-type-tag-arrow-tag-arrow-coherenceᵢ :
  ∀ {Φ Γ Γ′ C₁ C₂ C₁′ C₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′} →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂)
    ⊑ mlb-typeᵢ {Γ = Γ′} (tag p₁′ ⇛ p₂′) (tag q₁′ ⇛ q₂′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-tag-arrow-tag-arrow-coherenceᵢ = id★

mlb-type-∀∀-coherenceᵢ :
  ∀ {Φ Γ Γ′ A A′ B B′ C C′}
    {p : leftChoiceᵢ (bothᵢ ∷ Γ) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q : rightChoiceᵢ (bothᵢ ∷ Γ) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p′ : leftChoiceᵢ (bothᵢ ∷ Γ′) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ′)
      ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ′)}
    {q′ : rightChoiceᵢ (bothᵢ ∷ Γ′) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ′)
      ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ′)} →
  ∀ᵢᶜ Φ ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ) ⊢
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q
    ⊑ mlb-typeᵢ {Γ = bothᵢ ∷ Γ′} p′ q′
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ′) →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
    ⊑ mlb-typeᵢ {Γ = Γ′} (∀ⁱ p′) (∀ⁱ q′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-∀∀-coherenceᵢ body-coh = ∀ⁱ body-coh

mlb-type-∀ν-coherenceᵢ :
  ∀ {Φ Γ Γ′ A A′ B B′ C C′}
    {p : leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
      ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q : rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
      ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {p′ : leftChoiceᵢ (leftOnlyᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ′)
      ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ′)}
    {q′ : rightChoiceᵢ (leftOnlyᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ′)
      ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C′ ≡ true} →
  ∀ᵢᶜ Φ ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ) ⊢
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q
    ⊑ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ′} p′ q′
    ⊣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ′) →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (ν occ q)
    ⊑ mlb-typeᵢ {Γ = Γ′} (∀ⁱ p′) (ν occ′ q′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-∀ν-coherenceᵢ body-coh = ∀ⁱ body-coh

mlb-type-ν∀-coherenceᵢ :
  ∀ {Φ Γ Γ′ A A′ B B′ C C′}
    {p : leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
      ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q : rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
      ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {p′ : leftChoiceᵢ (rightOnlyᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ′)
      ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ′)}
    {q′ : rightChoiceᵢ (rightOnlyᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ′)
      ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C′ ≡ true} →
  ∀ᵢᶜ Φ ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ) ⊢
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q
    ⊑ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ′} p′ q′
    ⊣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ′) →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (ν occ p) (∀ⁱ q)
    ⊑ mlb-typeᵢ {Γ = Γ′} (ν occ′ p′) (∀ⁱ q′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-ν∀-coherenceᵢ body-coh = ∀ⁱ body-coh

mlb-type-νν-true-coherenceᵢ :
  ∀ {Φ Γ Γ′ A A′ B B′ C C′}
    {p : leftChoiceᵢ (neitherᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
      ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q : rightChoiceᵢ (neitherᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
      ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {p′ : leftChoiceᵢ (neitherᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
      ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ′)}
    {q′ : rightChoiceᵢ (neitherᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
      ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C ≡ true}
    {occᴿ : occurs zero C′ ≡ true}
    {occᴿ′ : occurs zero C′ ≡ true} →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ true →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′) ≡ true →
  ∀ᵢᶜ Φ ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ) ⊢
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q
    ⊑ mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′
    ⊣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′) →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q)
    ⊑ mlb-typeᵢ {Γ = Γ′} (ν occᴿ p′) (ν occᴿ′ q′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-νν-true-coherenceᵢ occ-lower occ-lower′ body-coh =
  close-neither-true-coherenceᵢ occ-lower occ-lower′ body-coh

mlb-type-νν-false-coherenceᵢ :
  ∀ {Φ Γ Γ′ A A′ B B′ C C′}
    {p : leftChoiceᵢ (neitherᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
      ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q : rightChoiceᵢ (neitherᵢ ∷ Γ)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
      ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {p′ : leftChoiceᵢ (neitherᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
      ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ′)}
    {q′ : rightChoiceᵢ (neitherᵢ ∷ Γ′)
      ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
      ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C ≡ true}
    {occᴿ : occurs zero C′ ≡ true}
    {occᴿ′ : occurs zero C′ ≡ true} →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ false →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′) ≡ false →
  ∀ᵢᶜ Φ ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ) ⊢
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q
    ⊑ mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′
    ⊣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′) →
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q)
    ⊑ mlb-typeᵢ {Γ = Γ′} (ν occᴿ p′) (ν occᴿ′ q′)
    ⊣ choiceCommonCtxᵢ Γ′
mlb-type-νν-false-coherenceᵢ occ-lower occ-lower′ body-coh =
  close-neither-false-coherenceᵢ occ-lower occ-lower′ body-coh

mlb-type-from-lower-arrow-arrow-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A₁ A₂ A₁′ A₂′ B₁ B₂ B₁′ B₂′ C₁ C₂ C₁′ C₂′}
    {p₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ A₁ ⊣ Δᴸ}
    {p₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ A₂ ⊣ Δᴸ}
    {q₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ B₁ ⊣ Δᴸ}
    {q₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ B₂ ⊣ Δᴸ}
    {p₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ A₁′ ⊣ Δᴿ}
    {p₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ A₂′ ⊣ Δᴿ}
    {q₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ B₁′ ⊣ Δᴿ}
    {q₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ B₂′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p₁ q₁
    ⊑ mlb-type-from-lowerᵢ p₁′ q₁′
    ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p₂ q₂
    ⊑ mlb-type-from-lowerᵢ p₂′ q₂′
    ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (p₁ ↦ p₂) (q₁ ↦ q₂)
    ⊑ mlb-type-from-lowerᵢ (p₁′ ↦ p₂′) (q₁′ ↦ q₂′)
    ⊣ Δᴿ
mlb-type-from-lower-arrow-arrow-coherenceᵢ lower₁ lower₂ =
  lower₁ ↦ lower₂

mlb-type-from-lower-arrow-star-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A₁ A₂ A₁′ A₂′ C₁ C₂ C₁′ C₂′}
    {p₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ A₁ ⊣ Δᴸ}
    {p₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ A₂ ⊣ Δᴸ}
    {q₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ ★ ⊣ Δᴸ}
    {q₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ ★ ⊣ Δᴸ}
    {p₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ A₁′ ⊣ Δᴿ}
    {p₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ A₂′ ⊣ Δᴿ}
    {q₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ ★ ⊣ Δᴿ}
    {q₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ ★ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p₁ q₁
    ⊑ mlb-type-from-lowerᵢ p₁′ q₁′
    ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p₂ q₂
    ⊑ mlb-type-from-lowerᵢ p₂′ q₂′
    ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (p₁ ↦ p₂) (tag q₁ ⇛ q₂)
    ⊑ mlb-type-from-lowerᵢ (p₁′ ↦ p₂′) (tag q₁′ ⇛ q₂′)
    ⊣ Δᴿ
mlb-type-from-lower-arrow-star-coherenceᵢ lower₁ lower₂ =
  lower₁ ↦ lower₂

mlb-type-from-lower-star-arrow-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ B₁ B₂ B₁′ B₂′ C₁ C₂ C₁′ C₂′}
    {p₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ ★ ⊣ Δᴸ}
    {p₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ ★ ⊣ Δᴸ}
    {q₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ B₁ ⊣ Δᴸ}
    {q₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ B₂ ⊣ Δᴸ}
    {p₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ ★ ⊣ Δᴿ}
    {p₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ ★ ⊣ Δᴿ}
    {q₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ B₁′ ⊣ Δᴿ}
    {q₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ B₂′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p₁ q₁
    ⊑ mlb-type-from-lowerᵢ p₁′ q₁′
    ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ p₂ q₂
    ⊑ mlb-type-from-lowerᵢ p₂′ q₂′
    ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (tag p₁ ⇛ p₂) (q₁ ↦ q₂)
    ⊑ mlb-type-from-lowerᵢ (tag p₁′ ⇛ p₂′) (q₁′ ↦ q₂′)
    ⊣ Δᴿ
mlb-type-from-lower-star-arrow-coherenceᵢ lower₁ lower₂ =
  lower₁ ↦ lower₂

mlb-type-from-lower-tag-arrow-tag-arrow-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ C₁ C₂ C₁′ C₂′}
    {p₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ ★ ⊣ Δᴸ}
    {p₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ ★ ⊣ Δᴸ}
    {q₁ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₁ ⊑ ★ ⊣ Δᴸ}
    {q₂ : idᵢ Δᴸ ∣ Δᴸ ⊢ C₂ ⊑ ★ ⊣ Δᴸ}
    {p₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ ★ ⊣ Δᴿ}
    {p₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ ★ ⊣ Δᴿ}
    {q₁′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₁′ ⊑ ★ ⊣ Δᴿ}
    {q₂′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C₂′ ⊑ ★ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂)
    ⊑ mlb-type-from-lowerᵢ (tag p₁′ ⇛ p₂′) (tag q₁′ ⇛ q₂′)
    ⊣ Δᴿ
mlb-type-from-lower-tag-arrow-tag-arrow-coherenceᵢ = id★

mlb-type-from-lower-∀∀ᵢ :
  ∀ {Δ A B C}
    {p : idᵢ (suc Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ suc Δ}
    {q : idᵢ (suc Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ suc Δ} →
  mlb-type-from-lowerᵢ (∀ⁱ p) (∀ⁱ q) ≡ `∀ (mlb-type-from-lowerᵢ p q)
mlb-type-from-lower-∀∀ᵢ = refl

mlb-type-from-lower-∀∀-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ A′ ⊣ suc Δᴿ}
    {q′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ B′ ⊣ suc Δᴿ} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢
    mlb-type-from-lowerᵢ p q ⊑ mlb-type-from-lowerᵢ p′ q′
    ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (∀ⁱ p) (∀ⁱ q)
    ⊑ mlb-type-from-lowerᵢ (∀ⁱ p′) (∀ⁱ q′)
    ⊣ Δᴿ
mlb-type-from-lower-∀∀-coherenceᵢ body-coh = ∀ⁱ body-coh

mlb-type-from-lower-∀νᵢ :
  ∀ {Δ A B C}
    {p : idᵢ (suc Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ suc Δ}
    {q : νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ Δ}
    {occ : occurs zero C ≡ true} →
  mlb-type-from-lowerᵢ (∀ⁱ p) (ν occ q) ≡
  `∀
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ choice-idᵢ Δ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-leftOnly-id-proofAtᵢ q))
mlb-type-from-lower-∀νᵢ = refl

mlb-type-from-lower-ν∀ᵢ :
  ∀ {Δ A B C}
    {p : νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ (suc Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ suc Δ}
    {occ : occurs zero C ≡ true} →
  mlb-type-from-lowerᵢ (ν occ p) (∀ⁱ q) ≡
  `∀
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ choice-idᵢ Δ}
      (leftChoice-rightOnly-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q))
mlb-type-from-lower-ν∀ᵢ = refl

mlb-type-from-lower-ννᵢ :
  ∀ {Δ A B C}
    {p : νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ A ⊣ Δ}
    {q : νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ C ⊑ B ⊣ Δ}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C ≡ true} →
  mlb-type-from-lowerᵢ (ν occ p) (ν occ′ q) ≡
  close-neitherᵢ
    (mlb-typeᵢ {Γ = neitherᵢ ∷ choice-idᵢ Δ}
      (leftChoice-neither-id-proofAtᵢ p)
      (rightChoice-neither-id-proofAtᵢ q))
mlb-type-from-lower-ννᵢ = refl

mlb-type-from-lower-∀∀-first-order-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ A′ ⊣ suc Δᴿ}
    {q′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ B′ ⊣ suc Δᴿ} →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ (suc Δᴸ)}
    {Δᶜ = suc Δᴸ}
    {Δᴸ = suc Δᴸ}
    {Δᴿ = suc Δᴸ}
    (leftChoice-id-proofAtᵢ p)
    (rightChoice-id-proofAtᵢ q) →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ (suc Δᴿ)}
    {Δᶜ = suc Δᴿ}
    {Δᴸ = suc Δᴿ}
    {Δᴿ = suc Δᴿ}
    (leftChoice-id-proofAtᵢ p′)
    (rightChoice-id-proofAtᵢ q′) →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (∀ⁱ p) (∀ⁱ q)
    ⊑ mlb-type-from-lowerᵢ (∀ⁱ p′) (∀ⁱ q′)
    ⊣ Δᴿ
mlb-type-from-lower-∀∀-first-order-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ =
  ∀ⁱ
    (mlb-type-from-lower-first-order-coherenceᵢ
      {Φ = ∀ᵢᶜ Φ}
      {Δᴸ = suc Δᴸ}
      {Δᴿ = suc Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {C = C}
      {C′ = C′}
      {pA = pA}
      {pB = pB}
      {p = p}
      {q = q}
      {p′ = p′}
      {q′ = q′}
      route
      route′)

canonical-forall-forall-coherence-∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  CanonicalLowerᵢ (suc Δᴸ) A B C →
  CanonicalLowerᵢ (suc Δᴿ) A′ B′ C′ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ
canonical-forall-forall-coherence-∀∀ᵢ can can′ pA pB =
  ∀ⁱ (canonical-first-order-coherenceᵢ can can′ pA pB)

canonical-forall-lower-coherence-occᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  CanonicalLowerᵢ (suc Δᴸ) A B C →
  CanonicalLowerᵢ Δᴿ A′ B′ C′ →
  occurs zero C ≡ true →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ
canonical-forall-lower-coherence-occᵢ can can′ occC pA pB =
  ν occC (canonical-first-order-coherenceᵢ can can′ pA pB)

canonical-forall-lower-coherence-ννᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  CanonicalLowerᵢ (suc Δᴸ) A B C →
  CanonicalLowerᵢ Δᴿ A′ B′ C′ →
  occurs zero A ≡ true →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ
canonical-forall-lower-coherence-ννᵢ can can′ occA pA pB =
  canonical-forall-lower-coherence-occᵢ
    can
    can′
    (canonical-lower-occurs-leftᵢ can occA)
    pA
    pB

mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  occurs zero A ≡ true →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ (suc Δᴸ)}
    {Δᶜ = suc Δᴸ}
    {Δᴸ = suc Δᴸ}
    {Δᴿ = suc Δᴸ}
    (leftChoice-id-proofAtᵢ p)
    (rightChoice-id-proofAtᵢ q) →
  FirstOrderSelectorAtᵢ
    {Γ = choice-idᵢ Δᴿ}
    {Δᶜ = Δᴿ}
    {Δᴸ = Δᴿ}
    {Δᴿ = Δᴿ}
    (leftChoice-id-proofAtᵢ p′)
    (rightChoice-id-proofAtᵢ q′) →
  Φ ∣ Δᴸ ⊢
    mlb-type-from-lowerᵢ (∀ⁱ p) (∀ⁱ q)
    ⊑ mlb-type-from-lowerᵢ p′ q′
    ⊣ Δᴿ
mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    occA route route′
    rewrite mlb-type-from-lower-∀∀ᵢ {p = p} {q = q} =
  canonical-forall-lower-coherence-ννᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    (mlb-type-from-lower-first-order-canonicalᵢ route)
    (mlb-type-from-lower-first-order-canonicalᵢ route′)
    occA
    pA
    pB

------------------------------------------------------------------------
-- Indexed binder support
------------------------------------------------------------------------

data LowerToForallᵢ (Φ : ImpCtx) (Δᶜ Δᴿ : TyCtx) :
    Ty → Ty → Set where
  lower-to-∀ᵢ :
    ∀ {A C} →
    ∀ᵢᶜ Φ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ suc Δᴿ →
    LowerToForallᵢ Φ Δᶜ Δᴿ (`∀ C) A

  lower-to-νᵢ :
    ∀ {A C} →
    occurs zero C ≡ true →
    νᵢᶜ Φ ∣ suc Δᶜ ⊢ C ⊑ `∀ A ⊣ Δᴿ →
    LowerToForallᵢ Φ Δᶜ Δᴿ (`∀ C) A

lower-to-forall-invᵢ :
  ∀ {Φ Δᶜ Δᴿ A C} →
  Φ ∣ Δᶜ ⊢ C ⊑ `∀ A ⊣ Δᴿ →
  LowerToForallᵢ Φ Δᶜ Δᴿ C A
lower-to-forall-invᵢ (∀ⁱ p) = lower-to-∀ᵢ p
lower-to-forall-invᵢ (ν occ p) = lower-to-νᵢ occ p

data ForallSourceLowerᵢ (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (A : Ty) : Ty → Set where
  source-∀lower-∀ᵢ :
    ∀ {B} →
    ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
    ForallSourceLowerᵢ Φ Δᴸ Δᴿ A (`∀ B)

  source-∀lower-νᵢ :
    ∀ {B} →
    occurs zero A ≡ true →
    νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    ForallSourceLowerᵢ Φ Δᴸ Δᴿ A B

forall-source-lower-invᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ →
  ForallSourceLowerᵢ Φ Δᴸ Δᴿ A B
forall-source-lower-invᵢ (∀ⁱ p) = source-∀lower-∀ᵢ p
forall-source-lower-invᵢ (ν occ p) = source-∀lower-νᵢ occ p

source-forall-lower-dispatchᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  (P : Ty → Set) →
  (∀ {C} → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ C ⊣ suc Δᴿ → P (`∀ C)) →
  (∀ {C} →
    occurs zero A ≡ true →
    νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ C ⊣ Δᴿ →
    P C) →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ →
  P B
source-forall-lower-dispatchᵢ P k∀ kν p
    with forall-source-lower-invᵢ p
source-forall-lower-dispatchᵢ P k∀ kν p
    | source-∀lower-∀ᵢ A⊑C =
  k∀ A⊑C
source-forall-lower-dispatchᵢ P k∀ kν p
    | source-∀lower-νᵢ occA A⊑C =
  kν occA A⊑C

forall-source-non∀-νᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Non∀ B →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ →
  Σ[ occ ∈ occurs zero A ≡ true ]
    νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
forall-source-non∀-νᵢ non∀B p
    with forall-source-lower-invᵢ p
forall-source-non∀-νᵢ non∀B p
    | source-∀lower-∀ᵢ q
    with non∀B
forall-source-non∀-νᵢ non∀B p
    | source-∀lower-∀ᵢ q
    | ()
forall-source-non∀-νᵢ non∀B p
    | source-∀lower-νᵢ occ q =
  occ , q

data ForallForallLower²ᵢ
    (Φᴸ Φᴿ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx) :
    Ty → Ty → Ty → Set where
  ff-via-∀∀ᵢ :
    ∀ {A B C} →
    ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ suc Δᴸ →
    ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ B ⊣ suc Δᴿ →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ C) A B

  ff-via-∀νᵢ :
    ∀ {A B C} →
    ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ suc Δᴸ →
    occurs zero C ≡ true →
    νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ `∀ B ⊣ Δᴿ →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ C) A B

  ff-via-ν∀ᵢ :
    ∀ {A B C} →
    occurs zero C ≡ true →
    νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ `∀ A ⊣ Δᴸ →
    ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ B ⊣ suc Δᴿ →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ C) A B

  ff-via-ννᵢ :
    ∀ {A B C} →
    occurs zero C ≡ true →
    νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ `∀ A ⊣ Δᴸ →
    νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ `∀ B ⊣ Δᴿ →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ C) A B

forall-forall-lower²-invᵢ :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ `∀ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ C ⊑ `∀ B ⊣ Δᴿ →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C A B
forall-forall-lower²-invᵢ C⊑∀A C⊑∀B
    with lower-to-forall-invᵢ C⊑∀A
       | lower-to-forall-invᵢ C⊑∀B
forall-forall-lower²-invᵢ C⊑∀A C⊑∀B
    | lower-to-∀ᵢ C⊑A
    | lower-to-∀ᵢ C⊑B =
  ff-via-∀∀ᵢ C⊑A C⊑B
forall-forall-lower²-invᵢ C⊑∀A C⊑∀B
    | lower-to-∀ᵢ C⊑A
    | lower-to-νᵢ occC C⊑∀B′ =
  ff-via-∀νᵢ C⊑A occC C⊑∀B′
forall-forall-lower²-invᵢ C⊑∀A C⊑∀B
    | lower-to-νᵢ occC C⊑∀A′
    | lower-to-∀ᵢ C⊑B =
  ff-via-ν∀ᵢ occC C⊑∀A′ C⊑B
forall-forall-lower²-invᵢ C⊑∀A C⊑∀B
    | lower-to-νᵢ occC C⊑∀A′
    | lower-to-νᵢ occC′ C⊑∀B′ =
  ff-via-ννᵢ occC C⊑∀A′ C⊑∀B′

forall-forall-common-from-lower²ᵢ :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ C A B →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) C
forall-forall-common-from-lower²ᵢ (ff-via-∀∀ᵢ C⊑A C⊑B) =
  ∀ⁱ C⊑A , ∀ⁱ C⊑B
forall-forall-common-from-lower²ᵢ (ff-via-∀νᵢ C⊑A occC C⊑∀B) =
  ∀ⁱ C⊑A , ν occC C⊑∀B
forall-forall-common-from-lower²ᵢ (ff-via-ν∀ᵢ occC C⊑∀A C⊑B) =
  ν occC C⊑∀A , ∀ⁱ C⊑B
forall-forall-common-from-lower²ᵢ (ff-via-ννᵢ occC C⊑∀A C⊑∀B) =
  ν occC C⊑∀A , ν occC C⊑∀B

data NuLowerToForallCommon²ᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Ty → Set where
  νlower-common-∀ᵢ :
    ∀ {D} →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
    LowerToForallᵢ (νᵢᶜ Φᴼ) (suc Δᶜ) Δᶜ C D →
    NuLowerToForallCommon²ᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C (`∀ D)

νlower-to-forall-common²-invᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) D →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  NuLowerToForallCommon²ᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D
νlower-to-forall-common²-invᵢ common C⊑D
    with forall-forall-lower²-invᵢ (proj₁ common) (proj₂ common)
νlower-to-forall-common²-invᵢ common C⊑D
    | ff-via-∀∀ᵢ D⊑A D⊑B =
  νlower-common-∀ᵢ
    (ff-via-∀∀ᵢ D⊑A D⊑B)
    (lower-to-forall-invᵢ C⊑D)
νlower-to-forall-common²-invᵢ common C⊑D
    | ff-via-∀νᵢ D⊑A occD D⊑∀B =
  νlower-common-∀ᵢ
    (ff-via-∀νᵢ D⊑A occD D⊑∀B)
    (lower-to-forall-invᵢ C⊑D)
νlower-to-forall-common²-invᵢ common C⊑D
    | ff-via-ν∀ᵢ occD D⊑∀A D⊑B =
  νlower-common-∀ᵢ
    (ff-via-ν∀ᵢ occD D⊑∀A D⊑B)
    (lower-to-forall-invᵢ C⊑D)
νlower-to-forall-common²-invᵢ common C⊑D
    | ff-via-ννᵢ occD D⊑∀A D⊑∀B =
  νlower-common-∀ᵢ
    (ff-via-ννᵢ occD D⊑∀A D⊑∀B)
    (lower-to-forall-invᵢ C⊑D)

data NuLowerForall²Shapeᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B : Ty) : Ty → Ty → Set where
  νlower-shape-∀ᵢ :
    ∀ {C D} →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
    ∀ᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ D ⊣ suc Δᶜ →
    NuLowerForall²Shapeᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (`∀ C) (`∀ D)

  νlower-shape-νᵢ :
    ∀ {C D} →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
    occurs zero C ≡ true →
    νᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ `∀ D ⊣ Δᶜ →
    NuLowerForall²Shapeᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (`∀ C) (`∀ D)

νlower-forall²-shapeᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) D →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  NuLowerForall²Shapeᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D
νlower-forall²-shapeᵢ common C⊑D
    with νlower-to-forall-common²-invᵢ common C⊑D
νlower-forall²-shapeᵢ common C⊑D
    | νlower-common-∀ᵢ common∀ (lower-to-∀ᵢ C⊑D′) =
  νlower-shape-∀ᵢ common∀ C⊑D′
νlower-forall²-shapeᵢ common C⊑D
    | νlower-common-∀ᵢ common∀ (lower-to-νᵢ occC C⊑∀D′) =
  νlower-shape-νᵢ common∀ occC C⊑∀D′

data NuLowerToLeftForallCommonᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Ty → Set where
  νlower-left-common-∀ᵢ :
    ∀ {D} →
    LowerToForallᵢ Φᴸ Δᶜ Δᴸ (`∀ D) A →
    Φᴿ ∣ Δᶜ ⊢ `∀ D ⊑ B ⊣ Δᴿ →
    LowerToForallᵢ (νᵢᶜ Φᴼ) (suc Δᶜ) Δᶜ C D →
    NuLowerToLeftForallCommonᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C (`∀ D)

νlower-to-left-forall-common-invᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B D →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  NuLowerToLeftForallCommonᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D
νlower-to-left-forall-common-invᵢ common C⊑D
    with lower-to-forall-invᵢ (proj₁ common)
νlower-to-left-forall-common-invᵢ common C⊑D
    | lower-to-∀ᵢ D⊑A =
  νlower-left-common-∀ᵢ
    (lower-to-∀ᵢ D⊑A)
    (proj₂ common)
    (lower-to-forall-invᵢ C⊑D)
νlower-to-left-forall-common-invᵢ common C⊑D
    | lower-to-νᵢ occD D⊑∀A =
  νlower-left-common-∀ᵢ
    (lower-to-νᵢ occD D⊑∀A)
    (proj₂ common)
    (lower-to-forall-invᵢ C⊑D)

data NuLowerToRightForallCommonᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Ty → Set where
  νlower-right-common-∀ᵢ :
    ∀ {D} →
    Φᴸ ∣ Δᶜ ⊢ `∀ D ⊑ A ⊣ Δᴸ →
    LowerToForallᵢ Φᴿ Δᶜ Δᴿ (`∀ D) B →
    LowerToForallᵢ (νᵢᶜ Φᴼ) (suc Δᶜ) Δᶜ C D →
    NuLowerToRightForallCommonᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C (`∀ D)

νlower-to-right-forall-common-invᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) D →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  NuLowerToRightForallCommonᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D
νlower-to-right-forall-common-invᵢ common C⊑D
    with lower-to-forall-invᵢ (proj₂ common)
νlower-to-right-forall-common-invᵢ common C⊑D
    | lower-to-∀ᵢ D⊑B =
  νlower-right-common-∀ᵢ
    (proj₁ common)
    (lower-to-∀ᵢ D⊑B)
    (lower-to-forall-invᵢ C⊑D)
νlower-to-right-forall-common-invᵢ common C⊑D
    | lower-to-νᵢ occD D⊑∀B =
  νlower-right-common-∀ᵢ
    (proj₁ common)
    (lower-to-νᵢ occD D⊑∀B)
    (lower-to-forall-invᵢ C⊑D)

non∀-lower-to-forall-impossibleᵢ :
  ∀ {Φ Δᶜ Δᴿ A C} →
  Non∀ C →
  LowerToForallᵢ Φ Δᶜ Δᴿ C A →
  ⊥
non∀-lower-to-forall-impossibleᵢ () (lower-to-∀ᵢ p)
non∀-lower-to-forall-impossibleᵢ () (lower-to-νᵢ occ p)

record LiftMlb∀∀Supportᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ Δᴼ : TyCtx)
    (A B C : Ty) : Set where
  field
    k∀νᵢ :
      ∀ {D} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ suc Δᴸ →
      occurs zero D ≡ true →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᴼ

    kν∀ᵢ :
      ∀ {D} →
      occurs zero D ≡ true →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ suc Δᴿ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᴼ

    kννᵢ :
      ∀ {D} →
      occurs zero D ≡ true →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᴼ

open LiftMlb∀∀Supportᵢ public

left-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B} →
  LiftMlb∀∀Supportᵢ Φᴸ Φᴿ Φᴸ Δᶜ Δᴸ Δᴿ Δᴸ A B A
left-∀∀-supportᵢ .k∀νᵢ D⊑A occD D⊑∀B = ∀ⁱ D⊑A
left-∀∀-supportᵢ .kν∀ᵢ occD D⊑∀A D⊑B = ν occD D⊑∀A
left-∀∀-supportᵢ .kννᵢ occD D⊑∀A D⊑∀B = ν occD D⊑∀A

right-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B} →
  LiftMlb∀∀Supportᵢ Φᴸ Φᴿ Φᴿ Δᶜ Δᴸ Δᴿ Δᴿ A B B
right-∀∀-supportᵢ .k∀νᵢ D⊑A occD D⊑∀B = ν occD D⊑∀B
right-∀∀-supportᵢ .kν∀ᵢ occD D⊑∀A D⊑B = ∀ⁱ D⊑B
right-∀∀-supportᵢ .kννᵢ occD D⊑∀A D⊑∀B = ν occD D⊑∀B

forall-forall-support-dispatchᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ Δᴼ A B C D} →
  LiftMlb∀∀Supportᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ Δᴼ A B C →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ D A B →
  (∀ {E} →
   ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ E ⊑ A ⊣ suc Δᴸ →
   ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ E ⊑ B ⊣ suc Δᴿ →
   Φᴼ ∣ Δᶜ ⊢ `∀ E ⊑ `∀ C ⊣ Δᴼ) →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᴼ
forall-forall-support-dispatchᵢ support
    (ff-via-∀∀ᵢ E⊑A E⊑B) k∀∀ =
  k∀∀ E⊑A E⊑B
forall-forall-support-dispatchᵢ support
    (ff-via-∀νᵢ E⊑A occE E⊑∀B) k∀∀ =
  k∀νᵢ support E⊑A occE E⊑∀B
forall-forall-support-dispatchᵢ support
    (ff-via-ν∀ᵢ occE E⊑∀A E⊑B) k∀∀ =
  kν∀ᵢ support occE E⊑∀A E⊑B
forall-forall-support-dispatchᵢ support
    (ff-via-ννᵢ occE E⊑∀A E⊑∀B) k∀∀ =
  kννᵢ support occE E⊑∀A E⊑∀B

forall-forall-support-openᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ Δᴼ A B C D} →
  LiftMlb∀∀Supportᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ Δᴼ A B C →
  (∀ {E} →
   ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ E ⊑ A ⊣ suc Δᴸ →
   ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ E ⊑ B ⊣ suc Δᴿ →
   Φᴼ ∣ Δᶜ ⊢ `∀ E ⊑ `∀ C ⊣ Δᴼ) →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᴼ
forall-forall-support-openᵢ support k∀∀ D⊑∀A D⊑∀B =
  forall-forall-support-dispatchᵢ support
    (forall-forall-lower²-invᵢ D⊑∀A D⊑∀B)
    k∀∀

record ForallForallComparableSupportᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Set where
  field
    ∀lower-∀ν-supportᵢ :
      ∀ {D} →
      ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ suc Δᴸ →
      occurs zero D ≡ true →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ

    ∀lower-ν∀-supportᵢ :
      ∀ {D} →
      occurs zero D ≡ true →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
      ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ suc Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ

    ∀lower-νν-supportᵢ :
      ∀ {D} →
      occurs zero D ≡ true →
      νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
      νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ

    νlower-supportᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) D →
      occurs zero C ≡ true →
      νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ

open ForallForallComparableSupportᵢ public

left-endpoint-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Δ A B} →
  ForallForallComparableSupportᵢ Φᴸ Φᴿ Φᴸ Δ Δ Δ A B A
left-endpoint-∀∀-supportᵢ =
  record
    { ∀lower-∀ν-supportᵢ = λ D⊑A occD D⊑∀B A⊑D → ∀ⁱ D⊑A
    ; ∀lower-ν∀-supportᵢ = λ occD D⊑∀A D⊑B A⊑D →
        ν occD D⊑∀A
    ; ∀lower-νν-supportᵢ = λ occD D⊑∀A D⊑∀B A⊑D →
        ν occD D⊑∀A
    ; νlower-supportᵢ = λ common occA A⊑D → proj₁ common
    }

right-endpoint-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Δ A B} →
  ForallForallComparableSupportᵢ Φᴸ Φᴿ Φᴿ Δ Δ Δ A B B
right-endpoint-∀∀-supportᵢ =
  record
    { ∀lower-∀ν-supportᵢ = λ D⊑A occD D⊑∀B B⊑D →
        ν occD D⊑∀B
    ; ∀lower-ν∀-supportᵢ = λ occD D⊑∀A D⊑B B⊑D → ∀ⁱ D⊑B
    ; ∀lower-νν-supportᵢ = λ occD D⊑∀A D⊑∀B B⊑D →
        ν occD D⊑∀B
    ; νlower-supportᵢ = λ common occB B⊑D → proj₂ common
    }

∀lower-∀ν-from-comparableᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  (mixed :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) →
  cᶜ-lowerᵢ mixed ≡ C →
  ∀ {D} →
  ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ suc Δᴸ →
  occurs zero D ≡ true →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ
∀lower-∀ν-from-comparableᵢ mixed eq D⊑A occD D⊑∀B C⊑D =
  ∀ⁱ (comparable-lower-eqᶜᵢ mixed eq (D⊑A , D⊑∀B) C⊑D)

∀lower-ν∀-from-comparableᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  (mixed :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B) →
  cᶜ-lowerᵢ mixed ≡ C →
  ∀ {D} →
  occurs zero D ≡ true →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
  ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ
∀lower-ν∀-from-comparableᵢ mixed eq occD D⊑∀A D⊑B C⊑D =
  ∀ⁱ (comparable-lower-eqᶜᵢ mixed eq (D⊑∀A , D⊑B) C⊑D)

∀lower-νν-from-comparableᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  (mixed :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B)) →
  cᶜ-lowerᵢ mixed ≡ C →
  ∀ {D} →
  occurs zero D ≡ true →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ
∀lower-νν-from-comparableᵢ mixed eq occD D⊑∀A D⊑∀B C⊑D =
  ∀ⁱ (comparable-lower-eqᶜᵢ mixed eq (D⊑∀A , D⊑∀B) C⊑D)

∀∀-support-from-comparablesᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  (mixed∀ν :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) →
  cᶜ-lowerᵢ mixed∀ν ≡ C →
  (mixedν∀ :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B) →
  cᶜ-lowerᵢ mixedν∀ ≡ C →
  (mixedνν :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B)) →
  cᶜ-lowerᵢ mixedνν ≡ C →
  (∀ {D} →
    CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) D →
    occurs zero C ≡ true →
    νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
    Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ) →
  ForallForallComparableSupportᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C
∀∀-support-from-comparablesᵢ
    mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν νlower =
  record
    { ∀lower-∀ν-supportᵢ =
        ∀lower-∀ν-from-comparableᵢ mixed∀ν eq∀ν
    ; ∀lower-ν∀-supportᵢ =
        ∀lower-ν∀-from-comparableᵢ mixedν∀ eqν∀
    ; ∀lower-νν-supportᵢ =
        ∀lower-νν-from-comparableᵢ mixedνν eqνν
    ; νlower-supportᵢ = νlower
    }

forall-forall-lower²-comparable-from-comparablesᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (mixed∀ν :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) →
  cᶜ-lowerᵢ mixed∀ν ≡ cᶜ-lowerᵢ body →
  (mixedν∀ :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B) →
  cᶜ-lowerᵢ mixedν∀ ≡ cᶜ-lowerᵢ body →
  (mixedνν :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B)) →
  cᶜ-lowerᵢ mixedνν ≡ cᶜ-lowerᵢ body →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-lower²-comparable-from-comparablesᶜᵢ {D = D}
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν
    (ff-via-∀∀ᵢ D⊑A D⊑B) lower⊑D =
  ∀ⁱ (cᶜ-comparableᵢ body {D = D} (D⊑A , D⊑B) lower⊑D)
forall-forall-lower²-comparable-from-comparablesᶜᵢ {D = D}
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν
    (ff-via-∀νᵢ D⊑A occD D⊑∀B) lower⊑D =
  ∀lower-∀ν-from-comparableᵢ
    mixed∀ν
    eq∀ν
    D⊑A
    occD
    D⊑∀B
    lower⊑D
forall-forall-lower²-comparable-from-comparablesᶜᵢ {D = D}
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν
    (ff-via-ν∀ᵢ occD D⊑∀A D⊑B) lower⊑D =
  ∀lower-ν∀-from-comparableᵢ
    mixedν∀
    eqν∀
    occD
    D⊑∀A
    D⊑B
    lower⊑D
forall-forall-lower²-comparable-from-comparablesᶜᵢ {D = D}
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν
    (ff-via-ννᵢ occD D⊑∀A D⊑∀B) lower⊑D =
  ∀lower-νν-from-comparableᵢ
    mixedνν
    eqνν
    occD
    D⊑∀A
    D⊑∀B
    lower⊑D

forall-forall-νlower-shape-∀-from-comparablesᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (mixed∀ν :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) →
  cᶜ-lowerᵢ mixed∀ν ≡ cᶜ-lowerᵢ body →
  (mixedν∀ :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B) →
  cᶜ-lowerᵢ mixedν∀ ≡ cᶜ-lowerᵢ body →
  (mixedνν :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B)) →
  cᶜ-lowerᵢ mixedνν ≡ cᶜ-lowerᵢ body →
  cᶜ-lowerᵢ body ≡ `∀ C →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
  occurs zero (`∀ C) ≡ true →
  ∀ᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ D ⊣ suc Δᶜ →
  idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢
    `∀ C ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-νlower-shape-∀-from-comparablesᶜᵢ
    {Φᴼ = Φᴼ} {Δᶜ = Δᶜ} {C = C} {D = D}
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν eq-body
    common∀ occC C⊑D body-coh =
  forall-forall-lower²-comparable-from-comparablesᶜᵢ
    body
    mixed∀ν
    eq∀ν
    mixedν∀
    eqν∀
    mixedνν
    eqνν
    common∀
    (subst
      (λ T → ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ T ⊑ D ⊣ suc Δᶜ)
      (sym eq-body)
      (⊑-trans-left-idᵢ
        body-coh
        (νlower-∀shape-body-lowerᵢ occC C⊑D)))

forall-forall-νlower-from-comparablesᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (mixed∀ν :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) →
  cᶜ-lowerᵢ mixed∀ν ≡ cᶜ-lowerᵢ body →
  (mixedν∀ :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B) →
  cᶜ-lowerᵢ mixedν∀ ≡ cᶜ-lowerᵢ body →
  (mixedνν :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B)) →
  cᶜ-lowerᵢ mixedνν ≡ cᶜ-lowerᵢ body →
  (∀ {C} →
    cᶜ-lowerᵢ body ≡ `∀ C →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢
      `∀ C ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ) →
  (∀ {C D} →
    cᶜ-lowerᵢ body ≡ `∀ C →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
    occurs zero C ≡ true →
    νᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ `∀ D ⊣ Δᶜ →
    Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ) →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) D →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-νlower-from-comparablesᶜᵢ
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν real∀ shapeν
    common occC lower⊑D
    with νlower-forall²-shapeᵢ common lower⊑D
forall-forall-νlower-from-comparablesᶜᵢ
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν real∀ shapeν
    common occC lower⊑D
    | νlower-shape-∀ᵢ common∀ C⊑D =
  forall-forall-νlower-shape-∀-from-comparablesᶜᵢ
    body
    mixed∀ν
    eq∀ν
    mixedν∀
    eqν∀
    mixedνν
    eqνν
    refl
    common∀
    occC
    C⊑D
    (real∀ refl)
forall-forall-νlower-from-comparablesᶜᵢ
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν real∀ shapeν
    common occC lower⊑D
    | νlower-shape-νᵢ common∀ occC′ C⊑∀D =
  shapeν refl common∀ occC′ C⊑∀D

∀∀-support-from-comparables-with-νshapeᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (mixed∀ν :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) →
  cᶜ-lowerᵢ mixed∀ν ≡ cᶜ-lowerᵢ body →
  (mixedν∀ :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B) →
  cᶜ-lowerᵢ mixedν∀ ≡ cᶜ-lowerᵢ body →
  (mixedνν :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B)) →
  cᶜ-lowerᵢ mixedνν ≡ cᶜ-lowerᵢ body →
  (∀ {C} →
    cᶜ-lowerᵢ body ≡ `∀ C →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢
      `∀ C ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ) →
  (∀ {C D} →
    cᶜ-lowerᵢ body ≡ `∀ C →
    ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
    occurs zero C ≡ true →
    νᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ `∀ D ⊣ Δᶜ →
    Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body)
∀∀-support-from-comparables-with-νshapeᵢ
    body mixed∀ν eq∀ν mixedν∀ eqν∀ mixedνν eqνν real∀ shapeν =
  ∀∀-support-from-comparablesᵢ
    mixed∀ν
    eq∀ν
    mixedν∀
    eqν∀
    mixedνν
    eqνν
    (forall-forall-νlower-from-comparablesᶜᵢ
      body
      mixed∀ν
      eq∀ν
      mixedν∀
      eqν∀
      mixedνν
      eqνν
      real∀
      shapeν)

non∀-νlower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  Non∀ C →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) D →
  occurs zero C ≡ true →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ
non∀-νlower-supportᵢ non∀C common occC C⊑D
    with νlower-forall²-shapeᵢ common C⊑D
non∀-νlower-supportᵢ non∀C common occC C⊑D
    | νlower-shape-∀ᵢ common∀ C⊑D′ =
  ⊥-elim
    (non∀-lower-to-forall-impossibleᵢ non∀C (lower-to-∀ᵢ C⊑D′))
non∀-νlower-supportᵢ non∀C common occC C⊑D
    | νlower-shape-νᵢ common∀ occC′ C⊑∀D′ =
  ⊥-elim
    (non∀-lower-to-forall-impossibleᵢ
      non∀C
      (lower-to-νᵢ occC′ C⊑∀D′))

non∀-left-νlower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  Non∀ C →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B D →
  occurs zero C ≡ true →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ
non∀-left-νlower-supportᵢ non∀C common occC C⊑D
    with νlower-to-left-forall-common-invᵢ common C⊑D
non∀-left-νlower-supportᵢ non∀C common occC C⊑D
    | νlower-left-common-∀ᵢ D⊑∀A D⊑B C⊑∀D =
  ⊥-elim (non∀-lower-to-forall-impossibleᵢ non∀C C⊑∀D)

non∀-right-νlower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  Non∀ C →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) D →
  occurs zero C ≡ true →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ
non∀-right-νlower-supportᵢ non∀C common occC C⊑D
    with νlower-to-right-forall-common-invᵢ common C⊑D
non∀-right-νlower-supportᵢ non∀C common occC C⊑D
    | νlower-right-common-∀ᵢ D⊑A D⊑∀B C⊑∀D =
  ⊥-elim (non∀-lower-to-forall-impossibleᵢ non∀C C⊑∀D)

non∀-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  Non∀ C →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C
non∀-∀∀-supportᵢ non∀C =
  record
    { ∀lower-∀ν-supportᵢ = λ D⊑A occD D⊑∀B C⊑D →
        ⊥-elim
          (non∀-⊑∀-impossibleᵢ (non∀-targetᵢ non∀C C⊑D) D⊑∀B)
    ; ∀lower-ν∀-supportᵢ = λ occD D⊑∀A D⊑B C⊑D →
        ⊥-elim
          (non∀-⊑∀-impossibleᵢ (non∀-targetᵢ non∀C C⊑D) D⊑∀A)
    ; ∀lower-νν-supportᵢ = λ occD D⊑∀A D⊑∀B C⊑D →
        ⊥-elim
          (non∀-⊑∀-impossibleᵢ (non∀-targetᵢ non∀C C⊑D) D⊑∀A)
    ; νlower-supportᵢ = non∀-νlower-supportᵢ non∀C
    }

canonical-first-order-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  CanonicalLowerᵢ (suc Δᶜ) A B C →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C
canonical-first-order-∀∀-supportᵢ can =
  non∀-∀∀-supportᵢ (canonical-lower-non∀ᵢ can)

forall-forall-lower²-comparableᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-lower²-comparableᶜᵢ {D = D} body support
    (ff-via-∀∀ᵢ D⊑A D⊑B) lower⊑D =
  ∀ⁱ (cᶜ-comparableᵢ body {D = D} (D⊑A , D⊑B) lower⊑D)
forall-forall-lower²-comparableᶜᵢ {D = D} body support
    (ff-via-∀νᵢ D⊑A occD D⊑∀B) lower⊑D =
  ∀lower-∀ν-supportᵢ support {D = D} D⊑A occD D⊑∀B lower⊑D
forall-forall-lower²-comparableᶜᵢ {D = D} body support
    (ff-via-ν∀ᵢ occD D⊑∀A D⊑B) lower⊑D =
  ∀lower-ν∀-supportᵢ support {D = D} occD D⊑∀A D⊑B lower⊑D
forall-forall-lower²-comparableᶜᵢ {D = D} body support
    (ff-via-ννᵢ occD D⊑∀A D⊑∀B) lower⊑D =
  ∀lower-νν-supportᵢ support {D = D} occD D⊑∀A D⊑∀B lower⊑D

forall-forall-νlower-shape-∀-bridgeᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
  occurs zero (`∀ C) ≡ true →
  ∀ᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ D ⊣ suc Δᶜ →
  idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢
    cᶜ-lowerᵢ body ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-νlower-shape-∀-bridgeᶜᵢ
    body support common∀ occC C⊑D body-coh =
  forall-forall-lower²-comparableᶜᵢ
    body
    support
    common∀
    (⊑-trans-left-idᵢ
      body-coh
      (νlower-∀shape-body-lowerᵢ occC C⊑D))

forall-forall-νlower-shape-∀-coherenceᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  cᶜ-lowerᵢ body ≡ `∀ C →
  ForallForallLower²ᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ D) A B →
  occurs zero (`∀ C) ≡ true →
  ∀ᵢᶜ (νᵢᶜ Φᴼ) ∣ suc (suc Δᶜ) ⊢ C ⊑ D ⊣ suc Δᶜ →
  idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢
    `∀ C ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-νlower-shape-∀-coherenceᶜᵢ
    {Φᴼ = Φᴼ} {Δᶜ = Δᶜ} {C = C} {D = D}
    body support eq common∀ occC C⊑D body-coh =
  forall-forall-νlower-shape-∀-bridgeᶜᵢ
    body
    support
    common∀
    occC
    C⊑D
    (subst
      (λ T →
        idᵢ (suc Δᶜ) ∣ suc Δᶜ
          ⊢ T ⊑ `∀ (renameᵗ swap01ᵢ C) ⊣ suc Δᶜ)
      (sym eq)
      body-coh)

forall-forall-∀lower-comparableᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) (`∀ D) →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-forall-∀lower-comparableᶜᵢ {D = D} body support
    common lower⊑D
    with forall-forall-lower²-invᵢ (proj₁ common) (proj₂ common)
forall-forall-∀lower-comparableᶜᵢ body support common lower⊑D
    | common∀ =
  forall-forall-lower²-comparableᶜᵢ body support common∀ lower⊑D

comparable-forall-forall-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B)
comparable-forall-forall-from-supportᶜᵢ body support =
  record
    { cᶜ-lowerᵢ = `∀ (cᶜ-lowerᵢ body)
    ; cᶜ-lower-leftᵢ = ∀ⁱ (cᶜ-lower-leftᵢ body)
    ; cᶜ-lower-rightᵢ = ∀ⁱ (cᶜ-lower-rightᵢ body)
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (`∀ _) (`∀ _) D →
      _ ∣ _ ⊢ `∀ (cᶜ-lowerᵢ body) ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _
    comparable common lower⊑D =
      source-forall-lower-dispatchᵢ
        (λ D →
          CommonLowerBoundᶜᵢ _ _ _ _ _ (`∀ _) (`∀ _) D →
          _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _)
        (λ C⊑D common′ →
          forall-forall-∀lower-comparableᶜᵢ
            body
            support
            common′
            C⊑D)
        (λ occC C⊑D common′ →
          νlower-supportᵢ support common′ occC C⊑D)
        lower⊑D
        common

maximal-forall-forall-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  ForallForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  MaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B)
maximal-forall-forall-from-supportᶜᵢ body support =
  comparable⇒maximalᶜᵢ
    (comparable-forall-forall-from-supportᶜᵢ body support)

comparable-forall-forall-from-supportᵢ :
  ∀ {Δ A B} →
  (body : ComparableMaximalLowerBoundᵢ (suc Δ) A B) →
  ForallForallComparableSupportᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B (c-lowerᵢ body) →
  ComparableMaximalLowerBoundᵢ Δ (`∀ A) (`∀ B)
comparable-forall-forall-from-supportᵢ body support =
  record
    { c-lowerᵢ = cᶜ-lowerᵢ outer
    ; c-lower-leftᵢ = cᶜ-lower-leftᵢ outer
    ; c-lower-rightᵢ = cᶜ-lower-rightᵢ outer
    ; c-comparableᵢ = cᶜ-comparableᵢ outer
    }
  where
    outer =
      comparable-forall-forall-from-supportᶜᵢ
        (comparable-idᶜᵢ body)
        support

maximal-forall-forall-from-supportᵢ :
  ∀ {Δ A B} →
  (body : ComparableMaximalLowerBoundᵢ (suc Δ) A B) →
  ForallForallComparableSupportᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B (c-lowerᵢ body) →
  MaximalLowerBoundᵢ Δ (`∀ A) (`∀ B)
maximal-forall-forall-from-supportᵢ body support =
  comparable⇒maximalᵢ
    (comparable-forall-forall-from-supportᵢ body support)

canonical-forall-forall-comparableᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ (suc Δ) A B C) →
  ComparableMaximalLowerBoundᵢ Δ (`∀ A) (`∀ B)
canonical-forall-forall-comparableᵢ can =
  comparable-forall-forall-from-supportᵢ
    (canonical-lower-comparableᵢ can)
    (subst
      (λ C →
        ForallForallComparableSupportᵢ
          (idᵢ _) (idᵢ _) (idᵢ _) _ _ _ _ _ C)
      (sym (canonical-lower-comparable-lowerᵢ can))
      (canonical-first-order-∀∀-supportᵢ can))

canonical-forall-forall-comparable-lowerᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ (suc Δ) A B C) →
  c-lowerᵢ (canonical-forall-forall-comparableᵢ can) ≡ `∀ C
canonical-forall-forall-comparable-lowerᵢ can
    rewrite canonical-lower-comparable-lowerᵢ can =
  refl

canonical-forall-forall-maximalᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ (suc Δ) A B C →
  MaximalLowerBoundᵢ Δ (`∀ A) (`∀ B)
canonical-forall-forall-maximalᵢ can =
  comparable⇒maximalᵢ (canonical-forall-forall-comparableᵢ can)

canonical-forall-forall-maximal-lowerᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ (suc Δ) A B C) →
  lowerᵢ (canonical-forall-forall-maximalᵢ can) ≡ `∀ C
canonical-forall-forall-maximal-lowerᵢ can =
  canonical-forall-forall-comparable-lowerᵢ can

mlb-type-comparable-∀∀-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (bothᵢ ∷ Γ))
        (rightChoiceᵢ (bothᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
        (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
        (choiceRightCtxᵢ (bothᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) (`∀ B) ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
mlb-type-comparable-∀∀-supportedᵢ (body , eq) support =
  comparable-forall-forall-from-supportᶜᵢ body support ,
  cong `∀ eq

mlb-type-comparable-∀∀-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (bothᵢ ∷ Γ))
        (rightChoiceᵢ (bothᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
        (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
        (choiceRightCtxᵢ (bothᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) (`∀ B) ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
mlb-type-comparable-∀∀-selected-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    (body , eq) support =
  mlb-type-comparable-∀∀-supportedᵢ
    {p = p}
    {q = q}
    (body , eq)
    (subst
      (λ C →
        ForallForallComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          A B C)
      (sym eq)
      support)

mlb-type-maximal-∀∀-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (bothᵢ ∷ Γ))
        (rightChoiceᵢ (bothᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
        (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
        (choiceRightCtxᵢ (bothᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) (`∀ B) ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
mlb-type-maximal-∀∀-supportedᵢ {p = p} {q = q} body support
    with mlb-type-comparable-∀∀-supportedᵢ {p = p} {q = q} body support
mlb-type-maximal-∀∀-supportedᵢ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

mlb-type-maximal-∀∀-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (bothᵢ ∷ Γ))
        (rightChoiceᵢ (bothᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
        (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
        (choiceRightCtxᵢ (bothᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) (`∀ B) ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
mlb-type-maximal-∀∀-selected-supportᵢ {p = p} {q = q} body support
    with mlb-type-comparable-∀∀-selected-supportᵢ
      {p = p}
      {q = q}
      body
      support
mlb-type-maximal-∀∀-selected-supportᵢ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

record ForallNuComparableSupportᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Set where
  field
    ∀ν-∀lower-supportᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B (`∀ D) →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ

    ∀ν-νlower-supportᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B D →
      occurs zero C ≡ true →
      νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ

open ForallNuComparableSupportᵢ public

left-endpoint-∀ν-supportᵢ :
  ∀ {Φᴸ Φᴿ Δ A B} →
  ForallNuComparableSupportᵢ Φᴸ Φᴿ Φᴸ Δ Δ Δ A B A
left-endpoint-∀ν-supportᵢ =
  record
    { ∀ν-∀lower-supportᵢ = λ common A⊑D → proj₁ common
    ; ∀ν-νlower-supportᵢ = λ common occA A⊑D → proj₁ common
    }

∀ν-∀lower-directᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ suc Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
∀ν-∀lower-directᵢ body D⊑A D⊑B C⊑D =
  ∀ⁱ (cᶜ-comparableᵢ body (D⊑A , D⊑B) C⊑D)

forall-nu-∀lower-comparableᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  ForallNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B (`∀ D) →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
forall-nu-∀lower-comparableᶜᵢ body support
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D =
  ∀ν-∀lower-supportᵢ support (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D
forall-nu-∀lower-comparableᶜᵢ body support
    (∀ⁱ D⊑A , ν occD D⊑B) C⊑D =
  ∀ν-∀lower-directᵢ body D⊑A D⊑B C⊑D
forall-nu-∀lower-comparableᶜᵢ body support
    (ν occD D⊑∀A , ∀ⁱ D⊑B) C⊑D =
  ∀ν-∀lower-supportᵢ support (ν occD D⊑∀A , ∀ⁱ D⊑B) C⊑D
forall-nu-∀lower-comparableᶜᵢ body support
    (ν occD D⊑∀A , ν occD′ D⊑B) C⊑D =
  ∀ν-∀lower-supportᵢ
    support
    (ν occD D⊑∀A , ν occD′ D⊑B)
    C⊑D

non∀-∀ν-∀lower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  Non∀ (cᶜ-lowerᵢ body) →
  Non∀ B →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B (`∀ D) →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
non∀-∀ν-∀lower-supportᵢ body non∀C non∀B
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D
    with non∀B
non∀-∀ν-∀lower-supportᵢ body non∀C non∀B
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D | ()
non∀-∀ν-∀lower-supportᵢ body non∀C non∀B
    (∀ⁱ D⊑A , ν occD D⊑B) C⊑D =
  ∀ν-∀lower-directᵢ body D⊑A D⊑B C⊑D
non∀-∀ν-∀lower-supportᵢ body non∀C non∀B
    (ν occD D⊑∀A , D⊑B) C⊑D =
  ⊥-elim
    (non∀-⊑∀-impossibleᵢ
      (non∀-targetᵢ non∀C C⊑D)
      D⊑∀A)

non∀-∀ν-νlower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  Non∀ (cᶜ-lowerᵢ body) →
  Non∀ B →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B D →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
non∀-∀ν-νlower-supportᵢ body non∀C non∀B common occC C⊑D =
  non∀-left-νlower-supportᵢ non∀C common occC C⊑D

non∀-∀ν-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  Non∀ (cᶜ-lowerᵢ body) →
  Non∀ B →
  ForallNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body)
non∀-∀ν-supportᵢ body non∀C non∀B =
  record
    { ∀ν-∀lower-supportᵢ =
        non∀-∀ν-∀lower-supportᵢ body non∀C non∀B
    ; ∀ν-νlower-supportᵢ =
        non∀-∀ν-νlower-supportᵢ body non∀C non∀B
    }

comparable-forall-nu-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  ForallNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (`∀ A) B
comparable-forall-nu-from-supportᶜᵢ body occC support =
  record
    { cᶜ-lowerᵢ = `∀ (cᶜ-lowerᵢ body)
    ; cᶜ-lower-leftᵢ = ∀ⁱ (cᶜ-lower-leftᵢ body)
    ; cᶜ-lower-rightᵢ = ν occC (cᶜ-lower-rightᵢ body)
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ (`∀ _) _ D →
      _ ∣ _ ⊢ `∀ (cᶜ-lowerᵢ body) ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _
    comparable common lower⊑D =
      source-forall-lower-dispatchᵢ
        (λ D →
          CommonLowerBoundᶜᵢ _ _ _ _ _ (`∀ _) _ D →
          _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _)
        (λ C⊑D common′ →
          forall-nu-∀lower-comparableᶜᵢ body support common′ C⊑D)
        (λ occ C⊑D common′ →
          ∀ν-νlower-supportᵢ support common′ occ C⊑D)
        lower⊑D
        common

maximal-forall-nu-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B) →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  ForallNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  MaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (`∀ A) B
maximal-forall-nu-from-supportᶜᵢ body occC support =
  comparable⇒maximalᶜᵢ
    (comparable-forall-nu-from-supportᶜᵢ body occC support)

record NuForallComparableSupportᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Set where
  field
    ν∀-∀lower-supportᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) (`∀ D) →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ

    ν∀-νlower-supportᵢ :
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) D →
      occurs zero C ≡ true →
      νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ

open NuForallComparableSupportᵢ public

right-endpoint-ν∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Δ A B} →
  NuForallComparableSupportᵢ Φᴸ Φᴿ Φᴿ Δ Δ Δ A B B
right-endpoint-ν∀-supportᵢ =
  record
    { ν∀-∀lower-supportᵢ = λ common B⊑D → proj₂ common
    ; ν∀-νlower-supportᵢ = λ common occB B⊑D → proj₂ common
    }

ν∀-∀lower-directᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
ν∀-∀lower-directᵢ body D⊑A D⊑B C⊑D =
  ∀ⁱ (cᶜ-comparableᵢ body (D⊑A , D⊑B) C⊑D)

nu-forall-∀lower-comparableᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  NuForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) (`∀ D) →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
nu-forall-∀lower-comparableᶜᵢ body support
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D =
  ν∀-∀lower-supportᵢ support (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D
nu-forall-∀lower-comparableᶜᵢ body support
    (∀ⁱ D⊑A , ν occD D⊑∀B) C⊑D =
  ν∀-∀lower-supportᵢ support (∀ⁱ D⊑A , ν occD D⊑∀B) C⊑D
nu-forall-∀lower-comparableᶜᵢ body support
    (ν occD D⊑A , ∀ⁱ D⊑B) C⊑D =
  ν∀-∀lower-directᵢ body D⊑A D⊑B C⊑D
nu-forall-∀lower-comparableᶜᵢ body support
    (ν occD D⊑A , ν occD′ D⊑∀B) C⊑D =
  ν∀-∀lower-supportᵢ
    support
    (ν occD D⊑A , ν occD′ D⊑∀B)
    C⊑D

non∀-ν∀-∀lower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  Non∀ (cᶜ-lowerᵢ body) →
  Non∀ A →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) (`∀ D) →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
non∀-ν∀-∀lower-supportᵢ body non∀C non∀A
    (∀ⁱ D⊑A , D⊑∀B) C⊑D
    with non∀A
non∀-ν∀-∀lower-supportᵢ body non∀C non∀A
    (∀ⁱ D⊑A , D⊑∀B) C⊑D | ()
non∀-ν∀-∀lower-supportᵢ body non∀C non∀A
    (ν occD D⊑A , ∀ⁱ D⊑B) C⊑D =
  ν∀-∀lower-directᵢ body D⊑A D⊑B C⊑D
non∀-ν∀-∀lower-supportᵢ body non∀C non∀A
    (D⊑A , ν occD D⊑∀B) C⊑D =
  ⊥-elim
    (non∀-⊑∀-impossibleᵢ
      (non∀-targetᵢ non∀C C⊑D)
      D⊑∀B)

non∀-ν∀-νlower-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  Non∀ (cᶜ-lowerᵢ body) →
  Non∀ A →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) D →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
non∀-ν∀-νlower-supportᵢ body non∀C non∀A common occC C⊑D =
  non∀-right-νlower-supportᵢ non∀C common occC C⊑D

non∀-ν∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  Non∀ (cᶜ-lowerᵢ body) →
  Non∀ A →
  NuForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body)
non∀-ν∀-supportᵢ body non∀C non∀A =
  record
    { ν∀-∀lower-supportᵢ =
        non∀-ν∀-∀lower-supportᵢ body non∀C non∀A
    ; ν∀-νlower-supportᵢ =
        non∀-ν∀-νlower-supportᵢ body non∀C non∀A
    }

mlb-type-first-order-∀ν-∀lower-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  (route : FirstOrderSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ (leftOnlyᵢ ∷ Γ))
      (rightChoiceᵢ (leftOnlyᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ))
      (choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ))
      (choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ))
      A B) →
  cᶜ-lowerᵢ body ≡ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q →
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (`∀ A) B (`∀ D) →
  ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ))
    ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
    ⊢ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q ⊑ D
    ⊣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ) →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ `∀ D ⊑ `∀ (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q)
    ⊣ choiceCommonCtxᵢ Γ
mlb-type-first-order-∀ν-∀lower-supportᵢ route body eq
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) lower⊑D
    with first-order-right-target-non∀ᵢ route
mlb-type-first-order-∀ν-∀lower-supportᵢ route body eq
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) lower⊑D | ()
mlb-type-first-order-∀ν-∀lower-supportᵢ route body eq
    (∀ⁱ D⊑A , ν occD D⊑B) lower⊑D =
  ∀ⁱ
    (subst
      (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
      eq
      (cᶜ-comparableᵢ body
        (D⊑A , D⊑B)
        (subst
          (λ T → _ ∣ _ ⊢ T ⊑ _ ⊣ _)
          (sym eq)
          lower⊑D)))
mlb-type-first-order-∀ν-∀lower-supportᵢ route body eq
    (ν occD D⊑∀A , D⊑B) lower⊑D =
  ⊥-elim
    (non∀-⊑∀-impossibleᵢ
      (non∀-targetᵢ (mlb-type-first-order-non∀ᵢ route) lower⊑D)
      D⊑∀A)

mlb-type-first-order-∀ν-νlower-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q →
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    (`∀ A) B D →
  occurs zero (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) ≡ true →
  νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ))
    ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
    ⊢ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q ⊑ D
    ⊣ choiceCommonCtxᵢ Γ →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ D ⊑ `∀ (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q)
    ⊣ choiceCommonCtxᵢ Γ
mlb-type-first-order-∀ν-νlower-supportᵢ route common occC lower⊑D
  =
  non∀-left-νlower-supportᵢ
    (mlb-type-first-order-non∀ᵢ route)
    common
    occC
    lower⊑D

mlb-type-first-order-∀ν-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q)
mlb-type-first-order-∀ν-supportᵢ {Γ = Γ} {p = p} {q = q} route
    with mlb-type-comparable-first-orderᵢ
      {Γ = leftOnlyᵢ ∷ Γ} {p = p} {q = q} route
mlb-type-first-order-∀ν-supportᵢ route | body , eq =
  record
    { ∀ν-∀lower-supportᵢ =
        mlb-type-first-order-∀ν-∀lower-supportᵢ route body eq
    ; ∀ν-νlower-supportᵢ =
        mlb-type-first-order-∀ν-νlower-supportᵢ route
    }

mlb-type-first-order-ν∀-∀lower-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  (route : FirstOrderSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ (rightOnlyᵢ ∷ Γ))
      (rightChoiceᵢ (rightOnlyᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ))
      (choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ))
      (choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ))
      A B) →
  cᶜ-lowerᵢ body ≡ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q →
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A (`∀ B) (`∀ D) →
  ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ))
    ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
    ⊢ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q ⊑ D
    ⊣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ) →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ `∀ D ⊑ `∀ (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q)
    ⊣ choiceCommonCtxᵢ Γ
mlb-type-first-order-ν∀-∀lower-supportᵢ route body eq
    (∀ⁱ D⊑A , D⊑∀B) lower⊑D
    with first-order-left-target-non∀ᵢ route
mlb-type-first-order-ν∀-∀lower-supportᵢ route body eq
    (∀ⁱ D⊑A , D⊑∀B) lower⊑D | ()
mlb-type-first-order-ν∀-∀lower-supportᵢ route body eq
    (ν occD D⊑A , ∀ⁱ D⊑B) lower⊑D =
  ∀ⁱ
    (subst
      (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
      eq
      (cᶜ-comparableᵢ body
        (D⊑A , D⊑B)
        (subst
          (λ T → _ ∣ _ ⊢ T ⊑ _ ⊣ _)
          (sym eq)
          lower⊑D)))
mlb-type-first-order-ν∀-∀lower-supportᵢ route body eq
    (D⊑A , ν occD D⊑∀B) lower⊑D =
  ⊥-elim
    (non∀-⊑∀-impossibleᵢ
      (non∀-targetᵢ (mlb-type-first-order-non∀ᵢ route) lower⊑D)
      D⊑∀B)

mlb-type-first-order-ν∀-νlower-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q →
  ∀ {D} →
  CommonLowerBoundᶜᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A (`∀ B) D →
  occurs zero (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) ≡ true →
  νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ))
    ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
    ⊢ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q ⊑ D
    ⊣ choiceCommonCtxᵢ Γ →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ D ⊑ `∀ (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q)
    ⊣ choiceCommonCtxᵢ Γ
mlb-type-first-order-ν∀-νlower-supportᵢ route common occC lower⊑D
  =
  non∀-right-νlower-supportᵢ
    (mlb-type-first-order-non∀ᵢ route)
    common
    occC
    lower⊑D

mlb-type-first-order-ν∀-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q)
mlb-type-first-order-ν∀-supportᵢ {Γ = Γ} {p = p} {q = q} route
    with mlb-type-comparable-first-orderᵢ
      {Γ = rightOnlyᵢ ∷ Γ} {p = p} {q = q} route
mlb-type-first-order-ν∀-supportᵢ route | body , eq =
  record
    { ν∀-∀lower-supportᵢ =
        mlb-type-first-order-ν∀-∀lower-supportᵢ route body eq
    ; ν∀-νlower-supportᵢ =
        mlb-type-first-order-ν∀-νlower-supportᵢ route
    }

comparable-nu-forall-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  NuForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A (`∀ B)
comparable-nu-forall-from-supportᶜᵢ body occC support =
  record
    { cᶜ-lowerᵢ = `∀ (cᶜ-lowerᵢ body)
    ; cᶜ-lower-leftᵢ = ν occC (cᶜ-lower-leftᵢ body)
    ; cᶜ-lower-rightᵢ = ∀ⁱ (cᶜ-lower-rightᵢ body)
    ; cᶜ-comparableᵢ = comparable
    }
  where
    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ _ (`∀ _) D →
      _ ∣ _ ⊢ `∀ (cᶜ-lowerᵢ body) ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _
    comparable common lower⊑D =
      source-forall-lower-dispatchᵢ
        (λ D →
          CommonLowerBoundᶜᵢ _ _ _ _ _ _ (`∀ _) D →
          _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _)
        (λ C⊑D common′ →
          nu-forall-∀lower-comparableᶜᵢ body support common′ C⊑D)
        (λ occ C⊑D common′ →
          ν∀-νlower-supportᵢ support common′ occ C⊑D)
        lower⊑D
        common

maximal-nu-forall-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B) →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  NuForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  MaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A (`∀ B)
maximal-nu-forall-from-supportᶜᵢ body occC support =
  comparable⇒maximalᶜᵢ
    (comparable-nu-forall-from-supportᶜᵢ body occC support)

mlb-type-comparable-∀ν-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) B ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (ν occ q)
mlb-type-comparable-∀ν-supportedᵢ {p = p} {q = q}
    occ (body , eq) support =
  comparable-forall-nu-from-supportᶜᵢ body occ-lower support ,
  cong `∀ eq
  where
    occ-lower =
      subst (λ T → occurs zero T ≡ true)
        (sym eq)
        (mlb-type-occurs-∀νᵢ p q occ)

mlb-type-comparable-∀ν-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) B ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (ν occ q)
mlb-type-comparable-∀ν-selected-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    occ (body , eq) support =
  mlb-type-comparable-∀ν-supportedᵢ
    {p = p}
    {q = q}
    occ
    (body , eq)
    (subst
      (λ C →
        ForallNuComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          A B C)
      (sym eq)
      support)

mlb-type-maximal-∀ν-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) B ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (ν occ q)
mlb-type-maximal-∀ν-supportedᵢ {C = C} {p = p} {q = q}
    occ body support
    with mlb-type-comparable-∀ν-supportedᵢ {C = C} {p = p} {q = q}
      occ
      body
      support
mlb-type-maximal-∀ν-supportedᵢ occ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

mlb-type-maximal-∀ν-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (leftOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      (`∀ A) B ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (ν occ q)
mlb-type-maximal-∀ν-selected-supportᵢ {C = C} {p = p} {q = q}
    occ body support
    with mlb-type-comparable-∀ν-selected-supportᵢ
      {C = C}
      {p = p}
      {q = q}
      occ
      body
      support
mlb-type-maximal-∀ν-selected-supportᵢ occ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

mlb-type-comparable-ν∀-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A (`∀ B) ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (∀ⁱ q)
mlb-type-comparable-ν∀-supportedᵢ {p = p} {q = q}
    occ (body , eq) support =
  comparable-nu-forall-from-supportᶜᵢ body occ-lower support ,
  cong `∀ eq
  where
    occ-lower =
      subst (λ T → occurs zero T ≡ true)
        (sym eq)
        (mlb-type-occurs-ν∀ᵢ p q occ)

mlb-type-comparable-ν∀-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A (`∀ B) ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (∀ⁱ q)
mlb-type-comparable-ν∀-selected-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    occ (body , eq) support =
  mlb-type-comparable-ν∀-supportedᵢ
    {p = p}
    {q = q}
    occ
    (body , eq)
    (subst
      (λ C →
        NuForallComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          A B C)
      (sym eq)
      support)

mlb-type-maximal-ν∀-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A (`∀ B) ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (∀ⁱ q)
mlb-type-maximal-ν∀-supportedᵢ {C = C} {p = p} {q = q}
    occ body support
    with mlb-type-comparable-ν∀-supportedᵢ {C = C} {p = p} {q = q}
      occ
      body
      support
mlb-type-maximal-ν∀-supportedᵢ occ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

mlb-type-maximal-ν∀-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (rightChoiceᵢ (rightOnlyᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ))
        (choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A (`∀ B) ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (∀ⁱ q)
mlb-type-maximal-ν∀-selected-supportᵢ {C = C} {p = p} {q = q}
    occ body support
    with mlb-type-comparable-ν∀-selected-supportᵢ
      {C = C}
      {p = p}
      {q = q}
      occ
      body
      support
mlb-type-maximal-ν∀-selected-supportᵢ occ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

record NuNuComparableSupportᵢ
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B C : Ty) : Set where
  field
    νν-true-∀lower-supportᵢ :
      occurs zero C ≡ true →
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B (`∀ D) →
      ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ C ⊣ Δᶜ

    νν-true-νlower-supportᵢ :
      occurs zero C ≡ true →
      ∀ {D} →
      CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
      occurs zero C ≡ true →
      νᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
      Φᴼ ∣ Δᶜ ⊢ D ⊑ `∀ C ⊣ Δᶜ

open NuNuComparableSupportᵢ public

∀ν-support-from-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (support :
    ForallForallComparableSupportᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body)) →
  ForallNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A (`∀ B) (cᶜ-lowerᵢ body)
∀ν-support-from-∀∀-supportᵢ body support =
  record
    { ∀ν-∀lower-supportᵢ =
        λ common C⊑D →
          forall-forall-∀lower-comparableᶜᵢ body support common C⊑D
    ; ∀ν-νlower-supportᵢ =
        λ common occC C⊑D →
          νlower-supportᵢ support common occC C⊑D
    }

ν∀-support-from-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (support :
    ForallForallComparableSupportᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body)) →
  NuForallComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (`∀ A) B (cᶜ-lowerᵢ body)
ν∀-support-from-∀∀-supportᵢ body support =
  record
    { ν∀-∀lower-supportᵢ =
        λ common C⊑D →
          forall-forall-∀lower-comparableᶜᵢ body support common C⊑D
    ; ν∀-νlower-supportᵢ =
        λ common occC C⊑D →
          νlower-supportᵢ support common occC C⊑D
    }

νν-support-from-∀∀-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) →
  (support :
    ForallForallComparableSupportᵢ
      Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body)) →
  NuNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) (cᶜ-lowerᵢ body)
νν-support-from-∀∀-supportᵢ body support =
  record
    { νν-true-∀lower-supportᵢ =
        λ occC common C⊑D →
          forall-forall-∀lower-comparableᶜᵢ body support common C⊑D
    ; νν-true-νlower-supportᵢ =
        λ occC common occC′ C⊑D →
          νlower-supportᵢ support common occC′ C⊑D
    }

no-occurs-νν-supportᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C} →
  occurs zero C ≡ false →
  NuNuComparableSupportᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B C
no-occurs-νν-supportᵢ no-occ =
  record
    { νν-true-∀lower-supportᵢ =
        λ occC common C⊑D →
          ⊥-elim (false≠trueᵢ (trans (sym no-occ) occC))
    ; νν-true-νlower-supportᵢ =
        λ occC common occC′ C⊑D →
          ⊥-elim (false≠trueᵢ (trans (sym no-occ) occC))
    }

νν-false-support-from-bodyᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ A B) →
  occurs zero (cᶜ-lowerᵢ body) ≡ false →
  ∀ {D} →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
  Φᴼ ∣ Δᶜ ⊢ cᶜ-lowerᵢ body [ zero ]ᴿ ⊑ D ⊣ Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ D ⊑ cᶜ-lowerᵢ body [ zero ]ᴿ ⊣ Δᶜ
νν-false-support-from-bodyᵢ {Φᴼ = Φᴼ} {Δᶜ = Δᶜ}
    body occC {D = D} common lower⊑D =
  subst
    (λ T → Φᴼ ∣ Δᶜ ⊢ T ⊑ cᶜ-lowerᵢ body [ zero ]ᴿ ⊣ Δᶜ)
    (renameᵗ-single-suc-cancel zero D)
    (open-unused-bothᵢ
      (occurs-raise-fresh zero D)
      occC
      (cᶜ-comparableᵢ body inner-common inner-lower⊑D))
  where
    inner-common =
      ⊑-source-liftνᵢ (proj₁ common) ,
      ⊑-source-liftνᵢ (proj₂ common)

    inner-lower⊑D =
      subst
        (λ T → ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ T ⊑ ⇑ᵗ D ⊣ suc Δᶜ)
        (raise-removeAt-freshᵢ zero (cᶜ-lowerᵢ body) occC)
        (⊑-lift∀ᵢ lower⊑D)

νν-true-∀lower-directᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ A B) →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
νν-true-∀lower-directᵢ body D⊑A D⊑B C⊑D =
  ∀ⁱ (cᶜ-comparableᵢ body (D⊑A , D⊑B) C⊑D)

νν-true-∀lower-comparableᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B D} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ A B) →
  NuNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  occurs zero (cᶜ-lowerᵢ body) ≡ true →
  CommonLowerBoundᶜᵢ Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B (`∀ D) →
  ∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ cᶜ-lowerᵢ body ⊑ D ⊣ suc Δᶜ →
  Φᴼ ∣ Δᶜ ⊢ `∀ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ Δᶜ
νν-true-∀lower-comparableᶜᵢ body support occC
    (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D =
  νν-true-∀lower-supportᵢ support occC (∀ⁱ D⊑A , ∀ⁱ D⊑B) C⊑D
νν-true-∀lower-comparableᶜᵢ body support occC
    (∀ⁱ D⊑A , ν occD D⊑B) C⊑D =
  νν-true-∀lower-supportᵢ
    support
    occC
    (∀ⁱ D⊑A , ν occD D⊑B)
    C⊑D
νν-true-∀lower-comparableᶜᵢ body support occC
    (ν occD D⊑A , ∀ⁱ D⊑B) C⊑D =
  νν-true-∀lower-supportᵢ
    support
    occC
    (ν occD D⊑A , ∀ⁱ D⊑B)
    C⊑D
νν-true-∀lower-comparableᶜᵢ body support occC
    (ν occD D⊑A , ν occD′ D⊑B) C⊑D =
  νν-true-∀lower-directᵢ body D⊑A D⊑B C⊑D

comparable-nu-nu-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ A B) →
  NuNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  ComparableMaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B
comparable-nu-nu-from-supportᶜᵢ body support =
  record
    { cᶜ-lowerᵢ = close-neitherᵢ (cᶜ-lowerᵢ body)
    ; cᶜ-lower-leftᵢ = proj₁ common
    ; cᶜ-lower-rightᵢ = proj₂ common
    ; cᶜ-comparableᵢ = comparable
    }
  where
    common =
      close-neither-commonᶜᵢ
        (cᶜ-lower-leftᵢ body , cᶜ-lower-rightᵢ body)

    comparable :
      ∀ {D} →
      CommonLowerBoundᶜᵢ _ _ _ _ _ _ _ D →
      _ ∣ _ ⊢ close-neitherᵢ (cᶜ-lowerᵢ body) ⊑ D ⊣ _ →
      _ ∣ _ ⊢ D ⊑ close-neitherᵢ (cᶜ-lowerᵢ body) ⊣ _
    comparable common′ lower⊑D
        with occurs zero (cᶜ-lowerᵢ body) in occC
    comparable common′ lower⊑D | true =
      source-forall-lower-dispatchᵢ
        (λ D →
          CommonLowerBoundᶜᵢ _ _ _ _ _ _ _ D →
          _ ∣ _ ⊢ D ⊑ `∀ (cᶜ-lowerᵢ body) ⊣ _)
        (λ C⊑D common″ →
          νν-true-∀lower-comparableᶜᵢ
            body
            support
            occC
            common″
            C⊑D)
        (λ occC′ C⊑D common″ →
          νν-true-νlower-supportᵢ
            support
            occC
            common″
            occC′
            C⊑D)
        lower⊑D
        common′
    comparable common′ lower⊑D | false =
      νν-false-support-from-bodyᵢ body occC common′ lower⊑D

maximal-nu-nu-from-supportᶜᵢ :
  ∀ {Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B} →
  (body :
    ComparableMaximalLowerBoundᶜᵢ
      (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
      (suc Δᶜ) Δᴸ Δᴿ A B) →
  NuNuComparableSupportᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B (cᶜ-lowerᵢ body) →
  MaximalLowerBoundᶜᵢ
    Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B
maximal-nu-nu-from-supportᶜᵢ body support =
  comparable⇒maximalᶜᵢ
    (comparable-nu-nu-from-supportᶜᵢ body support)

mlb-type-comparable-νν-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (occ′ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (neitherᵢ ∷ Γ))
        (rightChoiceᵢ (neitherᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (neitherᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (neitherᵢ ∷ Γ))
        (choiceLeftCtxᵢ (neitherᵢ ∷ Γ))
        (choiceRightCtxᵢ (neitherᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  NuNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q)
mlb-type-comparable-νν-supportedᵢ occ occ′ (body , eq) support =
  comparable-nu-nu-from-supportᶜᵢ body support ,
  cong close-neitherᵢ eq

mlb-type-comparable-νν-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (occ′ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (neitherᵢ ∷ Γ))
        (rightChoiceᵢ (neitherᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (neitherᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (neitherᵢ ∷ Γ))
        (choiceLeftCtxᵢ (neitherᵢ ∷ Γ))
        (choiceRightCtxᵢ (neitherᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  NuNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q)
mlb-type-comparable-νν-selected-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    occ occ′ (body , eq) support =
  mlb-type-comparable-νν-supportedᵢ
    {p = p}
    {q = q}
    occ
    occ′
    (body , eq)
    (subst
      (λ C →
        NuNuComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          A B C)
      (sym eq)
      support)

mlb-type-maximal-νν-supportedᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (occ′ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (neitherᵢ ∷ Γ))
        (rightChoiceᵢ (neitherᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (neitherᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (neitherᵢ ∷ Γ))
        (choiceLeftCtxᵢ (neitherᵢ ∷ Γ))
        (choiceRightCtxᵢ (neitherᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  NuNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (cᶜ-lowerᵢ (proj₁ body)) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q)
mlb-type-maximal-νν-supportedᵢ {C = C} {p = p} {q = q}
    occ occ′ body support
    with mlb-type-comparable-νν-supportedᵢ
      {C = C}
      {p = p}
      {q = q}
      occ
      occ′
      body
      support
mlb-type-maximal-νν-supportedᵢ occ occ′ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

mlb-type-maximal-νν-selected-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (occ : occurs zero C ≡ true) →
  (occ′ : occurs zero C ≡ true) →
  (body :
    Σ[ cb ∈
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (neitherᵢ ∷ Γ))
        (rightChoiceᵢ (neitherᵢ ∷ Γ))
        (idᵢ (choiceCommonCtxᵢ (neitherᵢ ∷ Γ)))
        (choiceCommonCtxᵢ (neitherᵢ ∷ Γ))
        (choiceLeftCtxᵢ (neitherᵢ ∷ Γ))
        (choiceRightCtxᵢ (neitherᵢ ∷ Γ))
        A B ]
      cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  NuNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} (ν occ p) (ν occ′ q)
mlb-type-maximal-νν-selected-supportᵢ {C = C} {p = p} {q = q}
    occ occ′ body support
    with mlb-type-comparable-νν-selected-supportᵢ
      {C = C}
      {p = p}
      {q = q}
      occ
      occ′
      body
      support
mlb-type-maximal-νν-selected-supportᵢ occ occ′ body support | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

mlb-type-first-order-νν-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q →
  NuNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q)
mlb-type-first-order-νν-supportᵢ route =
  no-occurs-νν-supportᵢ (mlb-type-first-order-neither-no-occursᵢ route)

data MlbTypeSelectorᵢ {Γ} :
    ∀ {C A B} →
    leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ →
    rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ →
    Set where
  sel-first-orderᵢ :
    ∀ {C A B}
      {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
        ⊣ choiceLeftCtxᵢ Γ}
      {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
        ⊣ choiceRightCtxᵢ Γ} →
    FirstOrderSelectorᵢ p q →
    MlbTypeSelectorᵢ p q

  sel-arrow-arrowᵢ :
    ∀ {C₁ C₂ A₁ A₂ B₁ B₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ Γ} →
    MlbTypeSelectorᵢ p₁ q₁ →
    MlbTypeSelectorᵢ p₂ q₂ →
    MlbTypeSelectorᵢ (p₁ ↦ p₂) (q₁ ↦ q₂)

  sel-arrow-starᵢ :
    ∀ {C₁ C₂ A₁ A₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ Γ} →
    MlbTypeSelectorᵢ p₁ q₁ →
    MlbTypeSelectorᵢ p₂ q₂ →
    MlbTypeSelectorᵢ (p₁ ↦ p₂) (tag q₁ ⇛ q₂)

  sel-star-arrowᵢ :
    ∀ {C₁ C₂ B₁ B₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ Γ} →
    MlbTypeSelectorᵢ p₁ q₁ →
    MlbTypeSelectorᵢ p₂ q₂ →
    MlbTypeSelectorᵢ (tag p₁ ⇛ p₂) (q₁ ↦ q₂)

  sel-tag-arrow-tag-arrowᵢ :
    ∀ {C₁ C₂}
      {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
      {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
      {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
      {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ Γ} →
    MlbTypeSelectorᵢ (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂)

  sel-∀∀ᵢ :
    ∀ {C A B}
      {p :
        leftChoiceᵢ (bothᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
          ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
      {q :
        rightChoiceᵢ (bothᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
          ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
    MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q →
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
    MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)

  sel-∀νᵢ :
    ∀ {C A B}
      {p :
        leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
          ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
      {q :
        rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
          ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
      (occ : occurs zero C ≡ true) →
    MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q →
    ForallNuComparableSupportᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
    MlbTypeSelectorᵢ (∀ⁱ p) (ν occ q)

  sel-ν∀ᵢ :
    ∀ {C A B}
      {p :
        leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
          ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
      {q :
        rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
          ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
      (occ : occurs zero C ≡ true) →
    MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q →
    NuForallComparableSupportᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
    MlbTypeSelectorᵢ (ν occ p) (∀ⁱ q)

  sel-ννᵢ :
    ∀ {C A B}
      {p :
        leftChoiceᵢ (neitherᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
          ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
      {q :
        rightChoiceᵢ (neitherᵢ ∷ Γ)
          ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
          ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
      (occ : occurs zero C ≡ true)
      (occ′ : occurs zero C ≡ true) →
    MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q →
    NuNuComparableSupportᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) →
    MlbTypeSelectorᵢ (ν occ p) (ν occ′ q)

MlbTypeSelectorCoherenceᵢ :
  ∀ (Φ : ImpCtx) {Γ Γ′ C C′ A A′ B B′}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ}
    {p′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′ ⊢ C′ ⊑ A′
      ⊣ choiceLeftCtxᵢ Γ′}
    {q′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′ ⊢ C′ ⊑ B′
      ⊣ choiceRightCtxᵢ Γ′} →
  MlbTypeSelectorᵢ {Γ = Γ} p q →
  MlbTypeSelectorᵢ {Γ = Γ′} p′ q′ →
  Set
MlbTypeSelectorCoherenceᵢ Φ {Γ = Γ} {Γ′ = Γ′} {p = p} {q = q}
    {p′ = p′} {q′ = q′} _ _ =
  Φ ∣ choiceCommonCtxᵢ Γ ⊢
    mlb-typeᵢ {Γ = Γ} p q ⊑ mlb-typeᵢ {Γ = Γ′} p′ q′
    ⊣ choiceCommonCtxᵢ Γ′

record MlbTypeSelectorSwap01ᵢ
    {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) :
    Set where
  field
    selector-swap01-routeᵢ :
      MlbTypeSelectorᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q)

    selector-swap01-lowerᵢ :
      mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q)
      ≡ renameᵗ swap01ᵢ
          (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)

    selector-swap01-coherenceᵢ :
      MlbTypeSelectorCoherenceᵢ
        (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))))
        route
        selector-swap01-routeᵢ

open MlbTypeSelectorSwap01ᵢ public

selector-swap01-lower-atᵢ :
  ∀ {Γ C A B D}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q} →
  MlbTypeSelectorSwap01ᵢ route →
  mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ D →
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀ᵢ p)
    (⊑-swap01∀∀ᵢ q)
  ≡ renameᵗ swap01ᵢ D
selector-swap01-lower-atᵢ swap eq =
  trans (selector-swap01-lowerᵢ swap) (cong (renameᵗ swap01ᵢ) eq)

mlb-type-selector-swap01-star-starᵢ :
  ∀ {Γ} →
  MlbTypeSelectorSwap01ᵢ
    (sel-first-orderᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} fo-star-starᵢ)
mlb-type-selector-swap01-star-starᵢ =
  record
    { selector-swap01-routeᵢ = sel-first-orderᵢ fo-star-starᵢ
    ; selector-swap01-lowerᵢ = refl
    ; selector-swap01-coherenceᵢ = id★
    }

record MlbTypeSelectorSwap01Under∀ᵢ
    {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) :
    Set where
  field
    selector-swap01-under∀-routeᵢ :
      MlbTypeSelectorᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q)

    selector-swap01-under∀-lowerᵢ :
      mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q)
      ≡ renameᵗ (extᵗ swap01ᵢ)
          (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)

    selector-swap01-under∀-coherenceᵢ :
      MlbTypeSelectorCoherenceᵢ
        (∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))))
        route
        selector-swap01-under∀-routeᵢ

open MlbTypeSelectorSwap01Under∀ᵢ public

record MlbTypeSelectorSwap01Under∀νᵢ
    {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q) : Set where
  field
    selector-swap01-under∀ν-routeᵢ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-underνᵢ q)

    selector-swap01-under∀ν-lowerᵢ :
      mlb-typeᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-underνᵢ q)
      ≡ renameᵗ (extᵗ swap01ᵢ)
          (mlb-typeᵢ
            {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
            p q)

    selector-swap01-under∀ν-coherenceᵢ :
      MlbTypeSelectorCoherenceᵢ
        (∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))))
        route
        selector-swap01-under∀ν-routeᵢ

open MlbTypeSelectorSwap01Under∀νᵢ public

record MlbTypeSelectorSwap01Underν∀ᵢ
    {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q) : Set where
  field
    selector-swap01-underν∀-routeᵢ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-underνᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q)

    selector-swap01-underν∀-lowerᵢ :
      mlb-typeᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-underνᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q)
      ≡ renameᵗ (extᵗ swap01ᵢ)
          (mlb-typeᵢ
            {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
            p q)

    selector-swap01-underν∀-coherenceᵢ :
      MlbTypeSelectorCoherenceᵢ
        (∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))))
        route
        selector-swap01-underν∀-routeᵢ

open MlbTypeSelectorSwap01Underν∀ᵢ public

record MlbTypeSelectorSwap01Underννᵢ
    {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q) : Set where
  field
    selector-swap01-underνν-routeᵢ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-underνᵢ p)
        (⊑-swap01∀∀-underνᵢ q)

    selector-swap01-underνν-lowerᵢ :
      mlb-typeᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-underνᵢ p)
        (⊑-swap01∀∀-underνᵢ q)
      ≡ renameᵗ (extᵗ swap01ᵢ)
          (mlb-typeᵢ
            {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
            p q)

    selector-swap01-underνν-coherenceᵢ :
      MlbTypeSelectorCoherenceᵢ
        (∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))))
        route
        selector-swap01-underνν-routeᵢ

open MlbTypeSelectorSwap01Underννᵢ public

selector-swap01-under∀-lower-atᵢ :
  ∀ {Γ C A B D}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {route :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q} →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ D →
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-under∀ᵢ p)
    (⊑-swap01∀∀-under∀ᵢ q)
  ≡ renameᵗ (extᵗ swap01ᵢ) D
selector-swap01-under∀-lower-atᵢ swap eq =
  trans
    (selector-swap01-under∀-lowerᵢ swap)
    (cong (renameᵗ (extᵗ swap01ᵢ)) eq)

selector-swap01-under∀ν-lower-atᵢ :
  ∀ {Γ C A B D}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {route :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q} →
  MlbTypeSelectorSwap01Under∀νᵢ route →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ D →
  mlb-typeᵢ
    {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-under∀ᵢ p)
    (⊑-swap01∀∀-underνᵢ q)
  ≡ renameᵗ (extᵗ swap01ᵢ) D
selector-swap01-under∀ν-lower-atᵢ swap eq =
  trans
    (selector-swap01-under∀ν-lowerᵢ swap)
    (cong (renameᵗ (extᵗ swap01ᵢ)) eq)

selector-swap01-underν∀-lower-atᵢ :
  ∀ {Γ C A B D}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {route :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q} →
  MlbTypeSelectorSwap01Underν∀ᵢ route →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ D →
  mlb-typeᵢ
    {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-underνᵢ p)
    (⊑-swap01∀∀-under∀ᵢ q)
  ≡ renameᵗ (extᵗ swap01ᵢ) D
selector-swap01-underν∀-lower-atᵢ swap eq =
  trans
    (selector-swap01-underν∀-lowerᵢ swap)
    (cong (renameᵗ (extᵗ swap01ᵢ)) eq)

selector-swap01-underνν-lower-atᵢ :
  ∀ {Γ C A B D}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {route :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q} →
  MlbTypeSelectorSwap01Underννᵢ route →
  mlb-typeᵢ {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ D →
  mlb-typeᵢ
    {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-underνᵢ p)
    (⊑-swap01∀∀-underνᵢ q)
  ≡ renameᵗ (extᵗ swap01ᵢ) D
selector-swap01-underνν-lower-atᵢ swap eq =
  trans
    (selector-swap01-underνν-lowerᵢ swap)
    (cong (renameᵗ (extᵗ swap01ᵢ)) eq)

selector-swap01-under∀ν-lower-from-∀∀ᵢ :
  ∀ {Γ C A B C∀ν A∀ν B∀ν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A∀ν
        ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C∀ν ⊑ B∀ν
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (route∀ν :
    MlbTypeSelectorᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p∀ν
      q∀ν) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  MlbTypeSelectorSwap01Under∀νᵢ route∀ν →
  mlb-typeᵢ
    {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    p∀ν
    q∀ν
  ≡
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    p
    q →
  mlb-typeᵢ
    {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-under∀ᵢ p∀ν)
    (⊑-swap01∀∀-underνᵢ q∀ν)
  ≡
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-under∀ᵢ p)
    (⊑-swap01∀∀-under∀ᵢ q)
selector-swap01-under∀ν-lower-from-∀∀ᵢ
    route route∀ν swap swap∀ν eq∀ν =
  trans
    (selector-swap01-under∀ν-lower-atᵢ swap∀ν eq∀ν)
    (sym (selector-swap01-under∀-lowerᵢ swap))

selector-swap01-underν∀-lower-from-∀∀ᵢ :
  ∀ {Γ C A B Cν∀ Aν∀ Bν∀}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ Aν∀
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ Bν∀
        ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (routeν∀ :
    MlbTypeSelectorᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pν∀
      qν∀) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  MlbTypeSelectorSwap01Underν∀ᵢ routeν∀ →
  mlb-typeᵢ
    {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    pν∀
    qν∀
  ≡
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    p
    q →
  mlb-typeᵢ
    {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-underνᵢ pν∀)
    (⊑-swap01∀∀-under∀ᵢ qν∀)
  ≡
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-under∀ᵢ p)
    (⊑-swap01∀∀-under∀ᵢ q)
selector-swap01-underν∀-lower-from-∀∀ᵢ
    route routeν∀ swap swapν∀ eqν∀ =
  trans
    (selector-swap01-underν∀-lower-atᵢ swapν∀ eqν∀)
    (sym (selector-swap01-under∀-lowerᵢ swap))

selector-swap01-underνν-lower-from-∀∀ᵢ :
  ∀ {Γ C A B Cνν Aνν Bνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cνν ⊑ Aνν
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cνν ⊑ Bνν
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (routeνν :
    MlbTypeSelectorᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pνν
      qνν) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  MlbTypeSelectorSwap01Underννᵢ routeνν →
  mlb-typeᵢ
    {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    pνν
    qνν
  ≡
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    p
    q →
  mlb-typeᵢ
    {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-underνᵢ pνν)
    (⊑-swap01∀∀-underνᵢ qνν)
  ≡
  mlb-typeᵢ
    {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
    (⊑-swap01∀∀-under∀ᵢ p)
    (⊑-swap01∀∀-under∀ᵢ q)
selector-swap01-underνν-lower-from-∀∀ᵢ
    route routeνν swap swapνν eqνν =
  trans
    (selector-swap01-underνν-lower-atᵢ swapνν eqνν)
    (sym (selector-swap01-under∀-lowerᵢ swap))

mlb-type-selector-choice-id-first-order-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴸ}
      {Δᶜ = Δᴸ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴸ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q)) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴿ}
      {Δᶜ = Δᴿ}
      {Δᴸ = Δᴿ}
      {Δᴿ = Δᴿ}
      (leftChoice-id-proofAtᵢ p′)
      (rightChoice-id-proofAtᵢ q′)) →
  Φ ∣ choiceCommonCtxᵢ (choice-idᵢ Δᴸ) ⊢
    mlb-typeᵢ
      {Γ = choice-idᵢ Δᴸ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)
    ⊑
    mlb-typeᵢ
      {Γ = choice-idᵢ Δᴿ}
      (leftChoice-id-proofᵢ p′)
      (rightChoice-id-proofᵢ q′)
    ⊣ choiceCommonCtxᵢ (choice-idᵢ Δᴿ)
mlb-type-selector-choice-id-first-order-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ =
  subst
    (λ Δᴿ′ → Φ ∣ choiceCommonCtxᵢ (choice-idᵢ Δᴸ) ⊢
      lowerᴸ ⊑ lowerᴿ ⊣ Δᴿ′)
    (sym (choice-id-commonCtxᵢ Δᴿ))
    (subst
      (λ Δᴸ′ → Φ ∣ Δᴸ′ ⊢ lowerᴸ ⊑ lowerᴿ ⊣ Δᴿ)
      (sym (choice-id-commonCtxᵢ Δᴸ))
      (subst
        (λ R → Φ ∣ Δᴸ ⊢ lowerᴸ ⊑ R ⊣ Δᴿ)
        (sym lowerᴿ-eq)
        (subst
          (λ L → Φ ∣ Δᴸ ⊢ L ⊑ mlb-type-from-lowerᵢ p′ q′ ⊣ Δᴿ)
          (sym lowerᴸ-eq)
          lower⊑lower′)))
  where
    lowerᴸ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴸ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)
    lowerᴿ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴿ}
        (leftChoice-id-proofᵢ p′)
        (rightChoice-id-proofᵢ q′)
    lowerᴸ-eq = mlb-type-choice-id-proof-eqᵢ {p = p} {q = q}
    lowerᴿ-eq = mlb-type-choice-id-proof-eqᵢ {p = p′} {q = q′}
    lower⊑lower′ =
      mlb-type-from-lower-first-order-coherenceᵢ
        {Φ = Φ}
        {Δᴸ = Δᴸ}
        {Δᴿ = Δᴿ}
        {A = A}
        {A′ = A′}
        {B = B}
        {B′ = B′}
        {C = C}
        {C′ = C′}
        {pA = pA}
        {pB = pB}
        {p = p}
        {q = q}
        {p′ = p′}
        {q′ = q′}
        route
        route′

mlb-type-selector-arrow-arrow-coherenceᵢ :
  ∀ {Φ Γ Γ′ C₁ C₂ A₁ A₂ B₁ B₂ C₁′ C₂′ A₁′ A₂′ B₁′ B₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ A₁′ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ A₂′ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ B₁′ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ B₂′ ⊣ choiceRightCtxᵢ Γ′}
    (route₁ : MlbTypeSelectorᵢ {Γ = Γ} p₁ q₁)
    (route₂ : MlbTypeSelectorᵢ {Γ = Γ} p₂ q₂)
    (route₁′ : MlbTypeSelectorᵢ {Γ = Γ′} p₁′ q₁′)
    (route₂′ : MlbTypeSelectorᵢ {Γ = Γ′} p₂′ q₂′) →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₁} {q = q₁} {p′ = p₁′} {q′ = q₁′}
    route₁ route₁′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₂} {q = q₂} {p′ = p₂′} {q′ = q₂′}
    route₂ route₂′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₁ ↦ p₂} {q = q₁ ↦ q₂}
    {p′ = p₁′ ↦ p₂′} {q′ = q₁′ ↦ q₂′}
    (sel-arrow-arrowᵢ route₁ route₂)
    (sel-arrow-arrowᵢ route₁′ route₂′)
mlb-type-selector-arrow-arrow-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}
    route₁ route₂ route₁′ route₂′
    lower₁ lower₂ =
  mlb-type-arrow-arrow-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}
    lower₁
    lower₂

mlb-type-selector-arrow-star-coherenceᵢ :
  ∀ {Φ Γ Γ′ C₁ C₂ A₁ A₂ C₁′ C₂′ A₁′ A₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ A₁′ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ A₂′ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′}
    (route₁ : MlbTypeSelectorᵢ {Γ = Γ} p₁ q₁)
    (route₂ : MlbTypeSelectorᵢ {Γ = Γ} p₂ q₂)
    (route₁′ : MlbTypeSelectorᵢ {Γ = Γ′} p₁′ q₁′)
    (route₂′ : MlbTypeSelectorᵢ {Γ = Γ′} p₂′ q₂′) →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₁} {q = q₁} {p′ = p₁′} {q′ = q₁′}
    route₁ route₁′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₂} {q = q₂} {p′ = p₂′} {q′ = q₂′}
    route₂ route₂′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₁ ↦ p₂} {q = tag q₁ ⇛ q₂}
    {p′ = p₁′ ↦ p₂′} {q′ = tag q₁′ ⇛ q₂′}
    (sel-arrow-starᵢ route₁ route₂)
    (sel-arrow-starᵢ route₁′ route₂′)
mlb-type-selector-arrow-star-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}
    route₁ route₂ route₁′ route₂′
    lower₁ lower₂ =
  mlb-type-arrow-star-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}
    lower₁
    lower₂

mlb-type-selector-star-arrow-coherenceᵢ :
  ∀ {Φ Γ Γ′ C₁ C₂ B₁ B₂ C₁′ C₂′ B₁′ B₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ B₁′ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ B₂′ ⊣ choiceRightCtxᵢ Γ′}
    (route₁ : MlbTypeSelectorᵢ {Γ = Γ} p₁ q₁)
    (route₂ : MlbTypeSelectorᵢ {Γ = Γ} p₂ q₂)
    (route₁′ : MlbTypeSelectorᵢ {Γ = Γ′} p₁′ q₁′)
    (route₂′ : MlbTypeSelectorᵢ {Γ = Γ′} p₂′ q₂′) →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₁} {q = q₁} {p′ = p₁′} {q′ = q₁′}
    route₁ route₁′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = p₂} {q = q₂} {p′ = p₂′} {q′ = q₂′}
    route₂ route₂′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = tag p₁ ⇛ p₂} {q = q₁ ↦ q₂}
    {p′ = tag p₁′ ⇛ p₂′} {q′ = q₁′ ↦ q₂′}
    (sel-star-arrowᵢ route₁ route₂)
    (sel-star-arrowᵢ route₁′ route₂′)
mlb-type-selector-star-arrow-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}
    route₁ route₂ route₁′ route₂′
    lower₁ lower₂ =
  mlb-type-star-arrow-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}
    lower₁
    lower₂

mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ :
  ∀ {Φ Γ Γ′ C₁ C₂ C₁′ C₂′}
    {p₁ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {p₂ : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ}
    {q₁ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {q₂ : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ
      ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ Γ}
    {p₁′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {p₂′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceLeftCtxᵢ Γ′}
    {q₁′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₁′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′}
    {q₂′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′
      ⊢ C₂′ ⊑ ★ ⊣ choiceRightCtxᵢ Γ′} →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = tag p₁ ⇛ p₂} {q = tag q₁ ⇛ q₂}
    {p′ = tag p₁′ ⇛ p₂′} {q′ = tag q₁′ ⇛ q₂′}
    (sel-tag-arrow-tag-arrowᵢ
      {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂})
    (sel-tag-arrow-tag-arrowᵢ
      {p₁ = p₁′} {p₂ = p₂′} {q₁ = q₁′} {q₂ = q₂′})
mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′} =
  mlb-type-tag-arrow-tag-arrow-coherenceᵢ
    {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂}
    {p₁′ = p₁′} {p₂′ = p₂′} {q₁′ = q₁′} {q₂′ = q₂′}

mlb-type-selector-swap01-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p₂ q₂) →
  MlbTypeSelectorSwap01ᵢ route₁ →
  MlbTypeSelectorSwap01ᵢ route₂ →
  MlbTypeSelectorSwap01ᵢ (sel-arrow-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-arrow-arrowᵢ route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-routeᵢ =
        sel-arrow-arrowᵢ
          (selector-swap01-routeᵢ swap₁)
          (selector-swap01-routeᵢ swap₂)
    ; selector-swap01-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-lowerᵢ swap₁)
          (selector-swap01-lowerᵢ swap₂)
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-arrow-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-routeᵢ swap₁)
          (selector-swap01-routeᵢ swap₂)
          (selector-swap01-coherenceᵢ swap₁)
          (selector-swap01-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p₂ q₂) →
  MlbTypeSelectorSwap01ᵢ route₁ →
  MlbTypeSelectorSwap01ᵢ route₂ →
  MlbTypeSelectorSwap01ᵢ (sel-arrow-starᵢ route₁ route₂)
mlb-type-selector-swap01-arrow-starᵢ route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-routeᵢ =
        sel-arrow-starᵢ
          (selector-swap01-routeᵢ swap₁)
          (selector-swap01-routeᵢ swap₂)
    ; selector-swap01-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-lowerᵢ swap₁)
          (selector-swap01-lowerᵢ swap₂)
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-arrow-star-coherenceᵢ
          route₁
          route₂
          (selector-swap01-routeᵢ swap₁)
          (selector-swap01-routeᵢ swap₂)
          (selector-swap01-coherenceᵢ swap₁)
          (selector-swap01-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p₂ q₂) →
  MlbTypeSelectorSwap01ᵢ route₁ →
  MlbTypeSelectorSwap01ᵢ route₂ →
  MlbTypeSelectorSwap01ᵢ (sel-star-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-star-arrowᵢ route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-routeᵢ =
        sel-star-arrowᵢ
          (selector-swap01-routeᵢ swap₁)
          (selector-swap01-routeᵢ swap₂)
    ; selector-swap01-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-lowerᵢ swap₁)
          (selector-swap01-lowerᵢ swap₂)
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-star-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-routeᵢ swap₁)
          (selector-swap01-routeᵢ swap₂)
          (selector-swap01-coherenceᵢ swap₁)
          (selector-swap01-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)} →
  MlbTypeSelectorSwap01ᵢ
    (sel-tag-arrow-tag-arrowᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂})
mlb-type-selector-swap01-tag-arrow-tag-arrowᵢ
    {Γ = Γ} {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂} =
  record
    { selector-swap01-routeᵢ = sel-tag-arrow-tag-arrowᵢ
    ; selector-swap01-lowerᵢ = refl
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ
          {Φ = ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))}
          {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = bothᵢ ∷ bothᵢ ∷ Γ}
          {p₁ = p₁}
          {p₂ = p₂}
          {q₁ = q₁}
          {q₂ = q₂}
          {p₁′ = ⊑-swap01∀∀ᵢ p₁}
          {p₂′ = ⊑-swap01∀∀ᵢ p₂}
          {q₁′ = ⊑-swap01∀∀ᵢ q₁}
          {q₂′ = ⊑-swap01∀∀ᵢ q₂}
    }

mlb-type-selector-swap01-under∀-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p₂ q₂) →
  MlbTypeSelectorSwap01Under∀ᵢ route₁ →
  MlbTypeSelectorSwap01Under∀ᵢ route₂ →
  MlbTypeSelectorSwap01Under∀ᵢ (sel-arrow-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-under∀-arrow-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-under∀-routeᵢ =
        sel-arrow-arrowᵢ
          (selector-swap01-under∀-routeᵢ swap₁)
          (selector-swap01-under∀-routeᵢ swap₂)
    ; selector-swap01-under∀-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-under∀-lowerᵢ swap₁)
          (selector-swap01-under∀-lowerᵢ swap₂)
    ; selector-swap01-under∀-coherenceᵢ =
        mlb-type-selector-arrow-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-under∀-routeᵢ swap₁)
          (selector-swap01-under∀-routeᵢ swap₂)
          (selector-swap01-under∀-coherenceᵢ swap₁)
          (selector-swap01-under∀-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-under∀-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p₂ q₂) →
  MlbTypeSelectorSwap01Under∀ᵢ route₁ →
  MlbTypeSelectorSwap01Under∀ᵢ route₂ →
  MlbTypeSelectorSwap01Under∀ᵢ (sel-arrow-starᵢ route₁ route₂)
mlb-type-selector-swap01-under∀-arrow-starᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-under∀-routeᵢ =
        sel-arrow-starᵢ
          (selector-swap01-under∀-routeᵢ swap₁)
          (selector-swap01-under∀-routeᵢ swap₂)
    ; selector-swap01-under∀-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-under∀-lowerᵢ swap₁)
          (selector-swap01-under∀-lowerᵢ swap₂)
    ; selector-swap01-under∀-coherenceᵢ =
        mlb-type-selector-arrow-star-coherenceᵢ
          route₁
          route₂
          (selector-swap01-under∀-routeᵢ swap₁)
          (selector-swap01-under∀-routeᵢ swap₂)
          (selector-swap01-under∀-coherenceᵢ swap₁)
          (selector-swap01-under∀-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-under∀-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p₂ q₂) →
  MlbTypeSelectorSwap01Under∀ᵢ route₁ →
  MlbTypeSelectorSwap01Under∀ᵢ route₂ →
  MlbTypeSelectorSwap01Under∀ᵢ (sel-star-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-under∀-star-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-under∀-routeᵢ =
        sel-star-arrowᵢ
          (selector-swap01-under∀-routeᵢ swap₁)
          (selector-swap01-under∀-routeᵢ swap₂)
    ; selector-swap01-under∀-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-under∀-lowerᵢ swap₁)
          (selector-swap01-under∀-lowerᵢ swap₂)
    ; selector-swap01-under∀-coherenceᵢ =
        mlb-type-selector-star-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-under∀-routeᵢ swap₁)
          (selector-swap01-under∀-routeᵢ swap₂)
          (selector-swap01-under∀-coherenceᵢ swap₁)
          (selector-swap01-under∀-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-under∀-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  MlbTypeSelectorSwap01Under∀ᵢ
    (sel-tag-arrow-tag-arrowᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂})
mlb-type-selector-swap01-under∀-tag-arrow-tag-arrowᵢ
    {Γ = Γ} {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂} =
  record
    { selector-swap01-under∀-routeᵢ = sel-tag-arrow-tag-arrowᵢ
    ; selector-swap01-under∀-lowerᵢ = refl
    ; selector-swap01-under∀-coherenceᵢ =
        mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ
          {Φ = ∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))))}
          {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {p₁ = p₁}
          {p₂ = p₂}
          {q₁ = q₁}
          {q₂ = q₂}
          {p₁′ = ⊑-swap01∀∀-under∀ᵢ p₁}
          {p₂′ = ⊑-swap01∀∀-under∀ᵢ p₂}
          {q₁′ = ⊑-swap01∀∀-under∀ᵢ q₁}
          {q₂′ = ⊑-swap01∀∀-under∀ᵢ q₂}
    }

mlb-type-selector-swap01-under∀ν-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Under∀νᵢ route₁ →
  MlbTypeSelectorSwap01Under∀νᵢ route₂ →
  MlbTypeSelectorSwap01Under∀νᵢ (sel-arrow-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-under∀ν-arrow-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-under∀ν-routeᵢ =
        sel-arrow-arrowᵢ
          (selector-swap01-under∀ν-routeᵢ swap₁)
          (selector-swap01-under∀ν-routeᵢ swap₂)
    ; selector-swap01-under∀ν-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-under∀ν-lowerᵢ swap₁)
          (selector-swap01-under∀ν-lowerᵢ swap₂)
    ; selector-swap01-under∀ν-coherenceᵢ =
        mlb-type-selector-arrow-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-under∀ν-routeᵢ swap₁)
          (selector-swap01-under∀ν-routeᵢ swap₂)
          (selector-swap01-under∀ν-coherenceᵢ swap₁)
          (selector-swap01-under∀ν-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-under∀ν-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Under∀νᵢ route₁ →
  MlbTypeSelectorSwap01Under∀νᵢ route₂ →
  MlbTypeSelectorSwap01Under∀νᵢ (sel-arrow-starᵢ route₁ route₂)
mlb-type-selector-swap01-under∀ν-arrow-starᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-under∀ν-routeᵢ =
        sel-arrow-starᵢ
          (selector-swap01-under∀ν-routeᵢ swap₁)
          (selector-swap01-under∀ν-routeᵢ swap₂)
    ; selector-swap01-under∀ν-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-under∀ν-lowerᵢ swap₁)
          (selector-swap01-under∀ν-lowerᵢ swap₂)
    ; selector-swap01-under∀ν-coherenceᵢ =
        mlb-type-selector-arrow-star-coherenceᵢ
          route₁
          route₂
          (selector-swap01-under∀ν-routeᵢ swap₁)
          (selector-swap01-under∀ν-routeᵢ swap₂)
          (selector-swap01-under∀ν-coherenceᵢ swap₁)
          (selector-swap01-under∀ν-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-under∀ν-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Under∀νᵢ route₁ →
  MlbTypeSelectorSwap01Under∀νᵢ route₂ →
  MlbTypeSelectorSwap01Under∀νᵢ (sel-star-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-under∀ν-star-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-under∀ν-routeᵢ =
        sel-star-arrowᵢ
          (selector-swap01-under∀ν-routeᵢ swap₁)
          (selector-swap01-under∀ν-routeᵢ swap₂)
    ; selector-swap01-under∀ν-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-under∀ν-lowerᵢ swap₁)
          (selector-swap01-under∀ν-lowerᵢ swap₂)
    ; selector-swap01-under∀ν-coherenceᵢ =
        mlb-type-selector-star-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-under∀ν-routeᵢ swap₁)
          (selector-swap01-under∀ν-routeᵢ swap₂)
          (selector-swap01-under∀ν-coherenceᵢ swap₁)
          (selector-swap01-under∀ν-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-under∀ν-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  MlbTypeSelectorSwap01Under∀νᵢ
    (sel-tag-arrow-tag-arrowᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂})
mlb-type-selector-swap01-under∀ν-tag-arrow-tag-arrowᵢ
    {Γ = Γ} {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂} =
  record
    { selector-swap01-under∀ν-routeᵢ = sel-tag-arrow-tag-arrowᵢ
    ; selector-swap01-under∀ν-lowerᵢ = refl
    ; selector-swap01-under∀ν-coherenceᵢ =
        mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ
          {Φ = ∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))))}
          {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {p₁ = p₁}
          {p₂ = p₂}
          {q₁ = q₁}
          {q₂ = q₂}
          {p₁′ = ⊑-swap01∀∀-under∀ᵢ p₁}
          {p₂′ = ⊑-swap01∀∀-under∀ᵢ p₂}
          {q₁′ = ⊑-swap01∀∀-underνᵢ q₁}
          {q₂′ = ⊑-swap01∀∀-underνᵢ q₂}
    }

mlb-type-selector-swap01-underν∀-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Underν∀ᵢ route₁ →
  MlbTypeSelectorSwap01Underν∀ᵢ route₂ →
  MlbTypeSelectorSwap01Underν∀ᵢ (sel-arrow-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-underν∀-arrow-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-underν∀-routeᵢ =
        sel-arrow-arrowᵢ
          (selector-swap01-underν∀-routeᵢ swap₁)
          (selector-swap01-underν∀-routeᵢ swap₂)
    ; selector-swap01-underν∀-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-underν∀-lowerᵢ swap₁)
          (selector-swap01-underν∀-lowerᵢ swap₂)
    ; selector-swap01-underν∀-coherenceᵢ =
        mlb-type-selector-arrow-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-underν∀-routeᵢ swap₁)
          (selector-swap01-underν∀-routeᵢ swap₂)
          (selector-swap01-underν∀-coherenceᵢ swap₁)
          (selector-swap01-underν∀-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-underν∀-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Underν∀ᵢ route₁ →
  MlbTypeSelectorSwap01Underν∀ᵢ route₂ →
  MlbTypeSelectorSwap01Underν∀ᵢ (sel-arrow-starᵢ route₁ route₂)
mlb-type-selector-swap01-underν∀-arrow-starᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-underν∀-routeᵢ =
        sel-arrow-starᵢ
          (selector-swap01-underν∀-routeᵢ swap₁)
          (selector-swap01-underν∀-routeᵢ swap₂)
    ; selector-swap01-underν∀-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-underν∀-lowerᵢ swap₁)
          (selector-swap01-underν∀-lowerᵢ swap₂)
    ; selector-swap01-underν∀-coherenceᵢ =
        mlb-type-selector-arrow-star-coherenceᵢ
          route₁
          route₂
          (selector-swap01-underν∀-routeᵢ swap₁)
          (selector-swap01-underν∀-routeᵢ swap₂)
          (selector-swap01-underν∀-coherenceᵢ swap₁)
          (selector-swap01-underν∀-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-underν∀-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Underν∀ᵢ route₁ →
  MlbTypeSelectorSwap01Underν∀ᵢ route₂ →
  MlbTypeSelectorSwap01Underν∀ᵢ (sel-star-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-underν∀-star-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-underν∀-routeᵢ =
        sel-star-arrowᵢ
          (selector-swap01-underν∀-routeᵢ swap₁)
          (selector-swap01-underν∀-routeᵢ swap₂)
    ; selector-swap01-underν∀-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-underν∀-lowerᵢ swap₁)
          (selector-swap01-underν∀-lowerᵢ swap₂)
    ; selector-swap01-underν∀-coherenceᵢ =
        mlb-type-selector-star-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-underν∀-routeᵢ swap₁)
          (selector-swap01-underν∀-routeᵢ swap₂)
          (selector-swap01-underν∀-coherenceᵢ swap₁)
          (selector-swap01-underν∀-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-underν∀-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  MlbTypeSelectorSwap01Underν∀ᵢ
    (sel-tag-arrow-tag-arrowᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂})
mlb-type-selector-swap01-underν∀-tag-arrow-tag-arrowᵢ
    {Γ = Γ} {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂} =
  record
    { selector-swap01-underν∀-routeᵢ = sel-tag-arrow-tag-arrowᵢ
    ; selector-swap01-underν∀-lowerᵢ = refl
    ; selector-swap01-underν∀-coherenceᵢ =
        mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ
          {Φ = ∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))))}
          {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {p₁ = p₁}
          {p₂ = p₂}
          {q₁ = q₁}
          {q₂ = q₂}
          {p₁′ = ⊑-swap01∀∀-underνᵢ p₁}
          {p₂′ = ⊑-swap01∀∀-underνᵢ p₂}
          {q₁′ = ⊑-swap01∀∀-under∀ᵢ q₁}
          {q₂′ = ⊑-swap01∀∀-under∀ᵢ q₂}
    }

mlb-type-selector-swap01-underνν-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Underννᵢ route₁ →
  MlbTypeSelectorSwap01Underννᵢ route₂ →
  MlbTypeSelectorSwap01Underννᵢ (sel-arrow-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-underνν-arrow-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-underνν-routeᵢ =
        sel-arrow-arrowᵢ
          (selector-swap01-underνν-routeᵢ swap₁)
          (selector-swap01-underνν-routeᵢ swap₂)
    ; selector-swap01-underνν-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-underνν-lowerᵢ swap₁)
          (selector-swap01-underνν-lowerᵢ swap₂)
    ; selector-swap01-underνν-coherenceᵢ =
        mlb-type-selector-arrow-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-underνν-routeᵢ swap₁)
          (selector-swap01-underνν-routeᵢ swap₂)
          (selector-swap01-underνν-coherenceᵢ swap₁)
          (selector-swap01-underνν-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-underνν-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Underννᵢ route₁ →
  MlbTypeSelectorSwap01Underννᵢ route₂ →
  MlbTypeSelectorSwap01Underννᵢ (sel-arrow-starᵢ route₁ route₂)
mlb-type-selector-swap01-underνν-arrow-starᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-underνν-routeᵢ =
        sel-arrow-starᵢ
          (selector-swap01-underνν-routeᵢ swap₁)
          (selector-swap01-underνν-routeᵢ swap₂)
    ; selector-swap01-underνν-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-underνν-lowerᵢ swap₁)
          (selector-swap01-underνν-lowerᵢ swap₂)
    ; selector-swap01-underνν-coherenceᵢ =
        mlb-type-selector-arrow-star-coherenceᵢ
          route₁
          route₂
          (selector-swap01-underνν-routeᵢ swap₁)
          (selector-swap01-underνν-routeᵢ swap₂)
          (selector-swap01-underνν-coherenceᵢ swap₁)
          (selector-swap01-underνν-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-underνν-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    (route₁ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₁ q₁)
    (route₂ :
      MlbTypeSelectorᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p₂ q₂) →
  MlbTypeSelectorSwap01Underννᵢ route₁ →
  MlbTypeSelectorSwap01Underννᵢ route₂ →
  MlbTypeSelectorSwap01Underννᵢ (sel-star-arrowᵢ route₁ route₂)
mlb-type-selector-swap01-underνν-star-arrowᵢ
    route₁ route₂ swap₁ swap₂ =
  record
    { selector-swap01-underνν-routeᵢ =
        sel-star-arrowᵢ
          (selector-swap01-underνν-routeᵢ swap₁)
          (selector-swap01-underνν-routeᵢ swap₂)
    ; selector-swap01-underνν-lowerᵢ =
        cong₂ _⇒_
          (selector-swap01-underνν-lowerᵢ swap₁)
          (selector-swap01-underνν-lowerᵢ swap₂)
    ; selector-swap01-underνν-coherenceᵢ =
        mlb-type-selector-star-arrow-coherenceᵢ
          route₁
          route₂
          (selector-swap01-underνν-routeᵢ swap₁)
          (selector-swap01-underνν-routeᵢ swap₂)
          (selector-swap01-underνν-coherenceᵢ swap₁)
          (selector-swap01-underνν-coherenceᵢ swap₂)
    }

mlb-type-selector-swap01-underνν-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  MlbTypeSelectorSwap01Underννᵢ
    (sel-tag-arrow-tag-arrowᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂})
mlb-type-selector-swap01-underνν-tag-arrow-tag-arrowᵢ
    {Γ = Γ} {p₁ = p₁} {p₂ = p₂} {q₁ = q₁} {q₂ = q₂} =
  record
    { selector-swap01-underνν-routeᵢ = sel-tag-arrow-tag-arrowᵢ
    ; selector-swap01-underνν-lowerᵢ = refl
    ; selector-swap01-underνν-coherenceᵢ =
        mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ
          {Φ = ∀ᵢᶜ (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))))}
          {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
          {p₁ = p₁}
          {p₂ = p₂}
          {q₁ = q₁}
          {q₂ = q₂}
          {p₁′ = ⊑-swap01∀∀-underνᵢ p₁}
          {p₂′ = ⊑-swap01∀∀-underνᵢ p₂}
          {q₁′ = ⊑-swap01∀∀-underνᵢ q₁}
          {q₂′ = ⊑-swap01∀∀-underνᵢ q₂}
    }

mlb-type-selector-∀∀-coherenceᵢ :
  ∀ {Φ Γ Γ′ C A B C′ A′ B′}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p′ :
      leftChoiceᵢ (bothᵢ ∷ Γ′) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ′)
      ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ′)}
    {q′ :
      rightChoiceᵢ (bothᵢ ∷ Γ′) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ′)
      ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ′)}
    (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q)
    (route′ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ′} p′ q′)
    (support :
      ForallForallComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q))
    (support′ :
      ForallForallComparableSupportᵢ
        (leftChoiceᵢ Γ′)
        (rightChoiceᵢ Γ′)
        (idᵢ (choiceCommonCtxᵢ Γ′))
        (choiceCommonCtxᵢ Γ′)
        (choiceLeftCtxᵢ Γ′)
        (choiceRightCtxᵢ Γ′)
        A′ B′ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ′} p′ q′)) →
  MlbTypeSelectorCoherenceᵢ (∀ᵢᶜ Φ)
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = ∀ⁱ p} {q = ∀ⁱ q} {p′ = ∀ⁱ p′} {q′ = ∀ⁱ q′}
    (sel-∀∀ᵢ route support)
    (sel-∀∀ᵢ route′ support′)
mlb-type-selector-∀∀-coherenceᵢ {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ support support′ body-coh =
  mlb-type-∀∀-coherenceᵢ
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    body-coh

mlb-type-selector-swap01-∀∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  MlbTypeSelectorSwap01ᵢ (sel-∀∀ᵢ route support)
mlb-type-selector-swap01-∀∀ᵢ route support swap supportˢ =
  record
    { selector-swap01-routeᵢ =
        sel-∀∀ᵢ
          (selector-swap01-under∀-routeᵢ swap)
          supportˢ
    ; selector-swap01-lowerᵢ =
        cong `∀ (selector-swap01-under∀-lowerᵢ swap)
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-∀∀-coherenceᵢ
          route
          (selector-swap01-under∀-routeᵢ swap)
          support
          supportˢ
          (selector-swap01-under∀-coherenceᵢ swap)
    }

mlb-type-selector-∀ν-coherenceᵢ :
  ∀ {Φ Γ Γ′ C A B C′ A′ B′}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {p′ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ′)
        ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ′)}
    {q′ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ′)
        ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C′ ≡ true}
    (route : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q)
    (route′ : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ′} p′ q′)
    (support :
      ForallNuComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q))
    (support′ :
      ForallNuComparableSupportᵢ
        (leftChoiceᵢ Γ′)
        (rightChoiceᵢ Γ′)
        (idᵢ (choiceCommonCtxᵢ Γ′))
        (choiceCommonCtxᵢ Γ′)
        (choiceLeftCtxᵢ Γ′)
        (choiceRightCtxᵢ Γ′)
        A′ B′ (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ′} p′ q′)) →
  MlbTypeSelectorCoherenceᵢ (∀ᵢᶜ Φ)
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = ∀ⁱ p} {q = ν occ q} {p′ = ∀ⁱ p′} {q′ = ν occ′ q′}
    (sel-∀νᵢ occ route support)
    (sel-∀νᵢ occ′ route′ support′)
mlb-type-selector-∀ν-coherenceᵢ
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    {occ = occ} {occ′ = occ′}
    route route′ support support′ body-coh =
  mlb-type-∀ν-coherenceᵢ
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    {occ = occ}
    {occ′ = occ′}
    body-coh

mlb-type-selector-swap01-∀νᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ : occurs zero C ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    ForallNuComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q)) →
  MlbTypeSelectorSwap01Under∀νᵢ route →
  (supportˢ :
    ForallNuComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-underνᵢ q))) →
  MlbTypeSelectorSwap01ᵢ (sel-∀νᵢ occ route support)
mlb-type-selector-swap01-∀νᵢ
    {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} route support swap supportˢ =
  record
    { selector-swap01-routeᵢ =
        sel-∀νᵢ
          (trans (occurs-zero-rename-ext swap01ᵢ C) occ)
          (selector-swap01-under∀ν-routeᵢ swap)
          supportˢ
    ; selector-swap01-lowerᵢ =
        cong `∀ (selector-swap01-under∀ν-lowerᵢ swap)
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-∀ν-coherenceᵢ
          {Φ = ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))}
          {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = bothᵢ ∷ bothᵢ ∷ Γ}
          {C = C}
          {A = A}
          {B = B}
          {C′ = renameᵗ (extᵗ swap01ᵢ) C}
          {A′ = renameᵗ (extᵗ swap01ᵢ) A}
          {B′ = renameᵗ swap01ᵢ B}
          {p = p}
          {q = q}
          {p′ = ⊑-swap01∀∀-under∀ᵢ p}
          {q′ = ⊑-swap01∀∀-underνᵢ q}
          {occ = occ}
          {occ′ = trans (occurs-zero-rename-ext swap01ᵢ C) occ}
          route
          (selector-swap01-under∀ν-routeᵢ swap)
          support
          supportˢ
          (selector-swap01-under∀ν-coherenceᵢ swap)
    }

mlb-type-selector-ν∀-coherenceᵢ :
  ∀ {Φ Γ Γ′ C A B C′ A′ B′}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {p′ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ′)
        ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ′)}
    {q′ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ′)
        ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C′ ≡ true}
    (route : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q)
    (route′ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ′} p′ q′)
    (support :
      NuForallComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q))
    (support′ :
      NuForallComparableSupportᵢ
        (leftChoiceᵢ Γ′)
        (rightChoiceᵢ Γ′)
        (idᵢ (choiceCommonCtxᵢ Γ′))
        (choiceCommonCtxᵢ Γ′)
        (choiceLeftCtxᵢ Γ′)
        (choiceRightCtxᵢ Γ′)
        A′ B′ (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ′} p′ q′)) →
  MlbTypeSelectorCoherenceᵢ (∀ᵢᶜ Φ)
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = ν occ p} {q = ∀ⁱ q} {p′ = ν occ′ p′} {q′ = ∀ⁱ q′}
    (sel-ν∀ᵢ occ route support)
    (sel-ν∀ᵢ occ′ route′ support′)
mlb-type-selector-ν∀-coherenceᵢ
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    {occ = occ} {occ′ = occ′}
    route route′ support support′ body-coh =
  mlb-type-ν∀-coherenceᵢ
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    {occ = occ}
    {occ′ = occ′}
    body-coh

mlb-type-selector-swap01-ν∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ : occurs zero C ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    NuForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q)) →
  MlbTypeSelectorSwap01Underν∀ᵢ route →
  (supportˢ :
    NuForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-underνᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  MlbTypeSelectorSwap01ᵢ (sel-ν∀ᵢ occ route support)
mlb-type-selector-swap01-ν∀ᵢ
    {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} route support swap supportˢ =
  record
    { selector-swap01-routeᵢ =
        sel-ν∀ᵢ
          (trans (occurs-zero-rename-ext swap01ᵢ C) occ)
          (selector-swap01-underν∀-routeᵢ swap)
          supportˢ
    ; selector-swap01-lowerᵢ =
        cong `∀ (selector-swap01-underν∀-lowerᵢ swap)
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-ν∀-coherenceᵢ
          {Φ = ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))}
          {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = bothᵢ ∷ bothᵢ ∷ Γ}
          {C = C}
          {A = A}
          {B = B}
          {C′ = renameᵗ (extᵗ swap01ᵢ) C}
          {A′ = renameᵗ swap01ᵢ A}
          {B′ = renameᵗ (extᵗ swap01ᵢ) B}
          {p = p}
          {q = q}
          {p′ = ⊑-swap01∀∀-underνᵢ p}
          {q′ = ⊑-swap01∀∀-under∀ᵢ q}
          {occ = occ}
          {occ′ = trans (occurs-zero-rename-ext swap01ᵢ C) occ}
          route
          (selector-swap01-underν∀-routeᵢ swap)
          support
          supportˢ
          (selector-swap01-underν∀-coherenceᵢ swap)
    }

mlb-type-selector-νν-true-coherenceᵢ :
  ∀ {Φ Γ Γ′ C A B C′ A′ B′}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {p′ :
      leftChoiceᵢ (neitherᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
        ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ′)}
    {q′ :
      rightChoiceᵢ (neitherᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
        ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C ≡ true}
    {occᴿ : occurs zero C′ ≡ true}
    {occᴿ′ : occurs zero C′ ≡ true}
    (route : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q)
    (route′ : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′)
    (support :
      NuNuComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q))
    (support′ :
      NuNuComparableSupportᵢ
        (leftChoiceᵢ Γ′)
        (rightChoiceᵢ Γ′)
        (idᵢ (choiceCommonCtxᵢ Γ′))
        (choiceCommonCtxᵢ Γ′)
        (choiceLeftCtxᵢ Γ′)
        (choiceRightCtxᵢ Γ′)
        A′ B′ (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′)) →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ true →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′) ≡ true →
  MlbTypeSelectorCoherenceᵢ (∀ᵢᶜ Φ)
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = ν occ p} {q = ν occ′ q}
    {p′ = ν occᴿ p′} {q′ = ν occᴿ′ q′}
    (sel-ννᵢ occ occ′ route support)
    (sel-ννᵢ occᴿ occᴿ′ route′ support′)
mlb-type-selector-νν-true-coherenceᵢ
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    {occ = occ} {occ′ = occ′} {occᴿ = occᴿ} {occᴿ′ = occᴿ′}
    route route′ support support′ occ-lower occ-lower′ body-coh =
  mlb-type-νν-true-coherenceᵢ
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    {occ = occ}
    {occ′ = occ′}
    {occᴿ = occᴿ}
    {occᴿ′ = occᴿ′}
    occ-lower
    occ-lower′
    body-coh

mlb-type-selector-νν-false-coherenceᵢ :
  ∀ {Φ Γ Γ′ C A B C′ A′ B′}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {p′ :
      leftChoiceᵢ (neitherᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
        ⊢ C′ ⊑ A′ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ′)}
    {q′ :
      rightChoiceᵢ (neitherᵢ ∷ Γ′)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ′)
        ⊢ C′ ⊑ B′ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ′)}
    {occ : occurs zero C ≡ true}
    {occ′ : occurs zero C ≡ true}
    {occᴿ : occurs zero C′ ≡ true}
    {occᴿ′ : occurs zero C′ ≡ true}
    (route : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q)
    (route′ : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′)
    (support :
      NuNuComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q))
    (support′ :
      NuNuComparableSupportᵢ
        (leftChoiceᵢ Γ′)
        (rightChoiceᵢ Γ′)
        (idᵢ (choiceCommonCtxᵢ Γ′))
        (choiceCommonCtxᵢ Γ′)
        (choiceLeftCtxᵢ Γ′)
        (choiceRightCtxᵢ Γ′)
        A′ B′ (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′)) →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ false →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ′} p′ q′) ≡ false →
  MlbTypeSelectorCoherenceᵢ (∀ᵢᶜ Φ)
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ →
  MlbTypeSelectorCoherenceᵢ Φ
    {p = ν occ p} {q = ν occ′ q}
    {p′ = ν occᴿ p′} {q′ = ν occᴿ′ q′}
    (sel-ννᵢ occ occ′ route support)
    (sel-ννᵢ occᴿ occᴿ′ route′ support′)
mlb-type-selector-νν-false-coherenceᵢ
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    {occ = occ} {occ′ = occ′} {occᴿ = occᴿ} {occᴿ′ = occᴿ′}
    route route′ support support′ occ-lower occ-lower′ body-coh =
  mlb-type-νν-false-coherenceᵢ
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    {occ = occ}
    {occ′ = occ′}
    {occᴿ = occᴿ}
    {occᴿ′ = occᴿ′}
    occ-lower
    occ-lower′
    body-coh

mlb-type-selector-swap01-ννᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ occ′ : occurs zero C ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    NuNuComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p q)) →
  MlbTypeSelectorSwap01Underννᵢ route →
  (supportˢ :
    NuNuComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-underνᵢ p)
        (⊑-swap01∀∀-underνᵢ q))) →
  MlbTypeSelectorSwap01ᵢ (sel-ννᵢ occ occ′ route support)
mlb-type-selector-swap01-ννᵢ
    {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} {occ′ = occ′} route support swap supportˢ
    with occurs zero
      (mlb-typeᵢ {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) in occD
mlb-type-selector-swap01-ννᵢ
    {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} {occ′ = occ′} route support swap supportˢ | true =
  record
    { selector-swap01-routeᵢ =
        sel-ννᵢ
          (trans (occurs-zero-rename-ext swap01ᵢ C) occ)
          (trans (occurs-zero-rename-ext swap01ᵢ C) occ′)
          (selector-swap01-underνν-routeᵢ swap)
          supportˢ
    ; selector-swap01-lowerᵢ =
        trans
          (cong close-neitherᵢ (selector-swap01-underνν-lowerᵢ swap))
          (close-neither-swap01ᵢ
            (mlb-typeᵢ
              {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
              p q))
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-νν-true-coherenceᵢ
          {Φ = ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))}
          {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = bothᵢ ∷ bothᵢ ∷ Γ}
          {C = C}
          {A = A}
          {B = B}
          {C′ = renameᵗ (extᵗ swap01ᵢ) C}
          {A′ = renameᵗ swap01ᵢ A}
          {B′ = renameᵗ swap01ᵢ B}
          {p = p}
          {q = q}
          {p′ = ⊑-swap01∀∀-underνᵢ p}
          {q′ = ⊑-swap01∀∀-underνᵢ q}
          {occ = occ}
          {occ′ = occ′}
          {occᴿ = trans (occurs-zero-rename-ext swap01ᵢ C) occ}
          {occᴿ′ = trans (occurs-zero-rename-ext swap01ᵢ C) occ′}
          route
          (selector-swap01-underνν-routeᵢ swap)
          support
          supportˢ
          occD
          (trans
            (cong (occurs zero) (selector-swap01-underνν-lowerᵢ swap))
            (trans
              (occurs-zero-rename-ext
                swap01ᵢ
                (mlb-typeᵢ
                  {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
                  p q))
              occD))
          (selector-swap01-underνν-coherenceᵢ swap)
    }
mlb-type-selector-swap01-ννᵢ
    {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} {occ′ = occ′} route support swap supportˢ | false =
  record
    { selector-swap01-routeᵢ =
        sel-ννᵢ
          (trans (occurs-zero-rename-ext swap01ᵢ C) occ)
          (trans (occurs-zero-rename-ext swap01ᵢ C) occ′)
          (selector-swap01-underνν-routeᵢ swap)
          supportˢ
    ; selector-swap01-lowerᵢ =
        trans
          (cong close-neitherᵢ (selector-swap01-underνν-lowerᵢ swap))
          (close-neither-swap01ᵢ
            (mlb-typeᵢ
              {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
              p q))
    ; selector-swap01-coherenceᵢ =
        mlb-type-selector-νν-false-coherenceᵢ
          {Φ = ∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))}
          {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
          {Γ′ = bothᵢ ∷ bothᵢ ∷ Γ}
          {C = C}
          {A = A}
          {B = B}
          {C′ = renameᵗ (extᵗ swap01ᵢ) C}
          {A′ = renameᵗ swap01ᵢ A}
          {B′ = renameᵗ swap01ᵢ B}
          {p = p}
          {q = q}
          {p′ = ⊑-swap01∀∀-underνᵢ p}
          {q′ = ⊑-swap01∀∀-underνᵢ q}
          {occ = occ}
          {occ′ = occ′}
          {occᴿ = trans (occurs-zero-rename-ext swap01ᵢ C) occ}
          {occᴿ′ = trans (occurs-zero-rename-ext swap01ᵢ C) occ′}
          route
          (selector-swap01-underνν-routeᵢ swap)
          support
          supportˢ
          occD
          (trans
            (cong (occurs zero) (selector-swap01-underνν-lowerᵢ swap))
            (trans
              (occurs-zero-rename-ext
                swap01ᵢ
                (mlb-typeᵢ
                  {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
                  p q))
              occD))
          (selector-swap01-underνν-coherenceᵢ swap)
    }

mlb-type-first-order-∀∀-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = bothᵢ ∷ Γ} p q →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
mlb-type-first-order-∀∀-supportᵢ route =
  non∀-∀∀-supportᵢ (mlb-type-first-order-non∀ᵢ route)

sel-∀∀-first-orderᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = bothᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-first-orderᵢ route =
  sel-∀∀ᵢ
    (sel-first-orderᵢ route)
    (mlb-type-first-order-∀∀-supportᵢ route)

sel-∀∀-non∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q →
  Non∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-non∀ᵢ route non∀C =
  sel-∀∀ᵢ route (non∀-∀∀-supportᵢ non∀C)

sel-∀∀-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ (∀ⁱ (p₁ ↦ p₂)) (∀ⁱ (q₁ ↦ q₂))
sel-∀∀-arrow-arrowᵢ route₁ route₂ =
  sel-∀∀-non∀ᵢ (sel-arrow-arrowᵢ route₁ route₂) non∀-⇒

sel-∀∀-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ (∀ⁱ (p₁ ↦ p₂)) (∀ⁱ (tag q₁ ⇛ q₂))
sel-∀∀-arrow-starᵢ route₁ route₂ =
  sel-∀∀-non∀ᵢ (sel-arrow-starᵢ route₁ route₂) non∀-⇒

sel-∀∀-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ (∀ⁱ (tag p₁ ⇛ p₂)) (∀ⁱ (q₁ ↦ q₂))
sel-∀∀-star-arrowᵢ route₁ route₂ =
  sel-∀∀-non∀ᵢ (sel-star-arrowᵢ route₁ route₂) non∀-⇒

sel-∀∀-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  MlbTypeSelectorᵢ
    (∀ⁱ (tag p₁ ⇛ p₂))
    (∀ⁱ (tag q₁ ⇛ q₂))
sel-∀∀-tag-arrow-tag-arrowᵢ =
  sel-∀∀-non∀ᵢ sel-tag-arrow-tag-arrowᵢ non∀-★

sel-∀ν-first-orderᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    (occ : occurs zero C ≡ true) →
  FirstOrderSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (∀ⁱ p) (ν occ q)
sel-∀ν-first-orderᵢ occ route =
  sel-∀νᵢ
    occ
    (sel-first-orderᵢ route)
    (mlb-type-first-order-∀ν-supportᵢ route)

sel-ν∀-first-orderᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    (occ : occurs zero C ≡ true) →
  FirstOrderSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (ν occ p) (∀ⁱ q)
sel-ν∀-first-orderᵢ occ route =
  sel-ν∀ᵢ
    occ
    (sel-first-orderᵢ route)
    (mlb-type-first-order-ν∀-supportᵢ route)

sel-νν-first-orderᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    (occ : occurs zero C ≡ true)
    (occ′ : occurs zero C ≡ true) →
  FirstOrderSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (ν occ p) (ν occ′ q)
sel-νν-first-orderᵢ occ occ′ route =
  sel-ννᵢ
    occ
    occ′
    (sel-first-orderᵢ route)
    (mlb-type-first-order-νν-supportᵢ route)

sel-νν-no-occursᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    (occ : occurs zero C ≡ true)
    (occ′ : occurs zero C ≡ true) →
  (route : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p q) →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p q) ≡ false →
  MlbTypeSelectorᵢ (ν occ p) (ν occ′ q)
sel-νν-no-occursᵢ occ occ′ route no-occ =
  sel-ννᵢ
    occ
    occ′
    route
    (no-occurs-νν-supportᵢ no-occ)

mlb-type-comparable-selectorᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  MlbTypeSelectorᵢ p q →
  Σ[ cb ∈
    ComparableMaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    cᶜ-lowerᵢ cb ≡ mlb-typeᵢ {Γ = Γ} p q
mlb-type-comparable-selectorᵢ {Γ = Γ} {C = C} {A = A} {B = B}
    {p = p} {q = q} (sel-first-orderᵢ route) =
  mlb-type-comparable-first-orderᵢ
    {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q} route
mlb-type-comparable-selectorᵢ
    (sel-arrow-arrowᵢ route₁ route₂)
    with mlb-type-comparable-selectorᵢ route₁
       | mlb-type-comparable-selectorᵢ route₂
mlb-type-comparable-selectorᵢ
    (sel-arrow-arrowᵢ route₁ route₂) | cb₁ , eq₁ | cb₂ , eq₂ =
  comparable-arrow-arrowᶜᵢ cb₁ cb₂ , cong₂ _⇒_ eq₁ eq₂
mlb-type-comparable-selectorᵢ
    (sel-arrow-starᵢ route₁ route₂)
    with mlb-type-comparable-selectorᵢ route₁
       | mlb-type-comparable-selectorᵢ route₂
mlb-type-comparable-selectorᵢ
    (sel-arrow-starᵢ route₁ route₂) | cb₁ , eq₁ | cb₂ , eq₂ =
  comparable-arrow-starᶜᵢ cb₁ cb₂ , cong₂ _⇒_ eq₁ eq₂
mlb-type-comparable-selectorᵢ
    (sel-star-arrowᵢ route₁ route₂)
    with mlb-type-comparable-selectorᵢ route₁
       | mlb-type-comparable-selectorᵢ route₂
mlb-type-comparable-selectorᵢ
    (sel-star-arrowᵢ route₁ route₂) | cb₁ , eq₁ | cb₂ , eq₂ =
  comparable-star-arrowᶜᵢ cb₁ cb₂ , cong₂ _⇒_ eq₁ eq₂
mlb-type-comparable-selectorᵢ {Γ = Γ} sel-tag-arrow-tag-arrowᵢ =
  comparable-choice-star-starᵢ Γ , refl
mlb-type-comparable-selectorᵢ {Γ = Γ}
    (sel-∀∀ᵢ {C = C} {A = A} {B = B} {p = p} {q = q}
      route support) =
  mlb-type-comparable-∀∀-selected-supportᵢ
    {Γ = Γ}
    {C = C}
    {A = A}
    {B = B}
    {p = p}
    {q = q}
    (mlb-type-comparable-selectorᵢ
      {Γ = bothᵢ ∷ Γ} {C = C} {A = A} {B = B} {p = p} {q = q}
      route)
    support
mlb-type-comparable-selectorᵢ {Γ = Γ}
    (sel-∀νᵢ {C = C} {A = A} {B = B} {p = p} {q = q}
      occ route support) =
  mlb-type-comparable-∀ν-selected-supportᵢ
    {Γ = Γ}
    {C = C}
    {A = A}
    {B = B}
    {p = p}
    {q = q}
    occ
    (mlb-type-comparable-selectorᵢ
      {Γ = leftOnlyᵢ ∷ Γ} {C = C} {A = A} {B = B}
      {p = p} {q = q} route)
    support
mlb-type-comparable-selectorᵢ {Γ = Γ}
    (sel-ν∀ᵢ {C = C} {A = A} {B = B} {p = p} {q = q}
      occ route support) =
  mlb-type-comparable-ν∀-selected-supportᵢ
    {Γ = Γ}
    {C = C}
    {A = A}
    {B = B}
    {p = p}
    {q = q}
    occ
    (mlb-type-comparable-selectorᵢ
      {Γ = rightOnlyᵢ ∷ Γ} {C = C} {A = A} {B = B}
      {p = p} {q = q} route)
    support
mlb-type-comparable-selectorᵢ {Γ = Γ}
    (sel-ννᵢ {C = C} {A = A} {B = B} {p = p} {q = q}
      occ occ′ route support) =
  mlb-type-comparable-νν-selected-supportᵢ
    {Γ = Γ}
    {C = C}
    {A = A}
    {B = B}
    {p = p}
    {q = q}
    occ
    occ′
    (mlb-type-comparable-selectorᵢ
      {Γ = neitherᵢ ∷ Γ} {C = C} {A = A} {B = B}
      {p = p} {q = q} route)
    support

mlb-type-maximal-selectorᵢ :
  ∀ {Γ C A B}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ} →
  MlbTypeSelectorᵢ p q →
  Σ[ mlb ∈
    MaximalLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (idᵢ (choiceCommonCtxᵢ Γ))
      (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
      A B ]
    lowerᶜᵢ mlb ≡ mlb-typeᵢ {Γ = Γ} p q
mlb-type-maximal-selectorᵢ {Γ = Γ} {C = C} {A = A} {B = B}
    {p = p} {q = q} route
    with mlb-type-comparable-selectorᵢ
      {Γ = Γ} {C = C} {A = A} {B = B} {p = p} {q = q} route
mlb-type-maximal-selectorᵢ route | cb , eq =
  comparable⇒maximalᶜᵢ cb , eq

∀∀-support-from-selector-routesᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡ C →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡ C →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡ C →
  (∀ {D} →
    CommonLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ A) (`∀ B) D →
    occurs zero C ≡ true →
    νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ))
      ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
      ⊢ C ⊑ D ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ D ⊑ `∀ C ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B C
∀∀-support-from-selector-routesᵢ
    {Γ = Γ} {A = A} {B = B}
    {p∀ν = p∀ν} {q∀ν = q∀ν}
    {pν∀ = pν∀} {qν∀ = qν∀}
    {pνν = pνν} {qνν = qνν}
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν νlower
    with mlb-type-comparable-selectorᵢ
      {Γ = leftOnlyᵢ ∷ Γ} {A = A} {B = `∀ B}
      {p = p∀ν} {q = q∀ν} route∀ν
       | mlb-type-comparable-selectorᵢ
      {Γ = rightOnlyᵢ ∷ Γ} {A = `∀ A} {B = B}
      {p = pν∀} {q = qν∀} routeν∀
       | mlb-type-comparable-selectorᵢ
      {Γ = neitherᵢ ∷ Γ} {A = `∀ A} {B = `∀ B}
      {p = pνν} {q = qνν} routeνν
∀∀-support-from-selector-routesᵢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν νlower
    | mixed∀ν , lower∀ν | mixedν∀ , lowerν∀ | mixedνν , lowerνν =
  ∀∀-support-from-comparablesᵢ
    mixed∀ν
    (trans lower∀ν eq∀ν)
    mixedν∀
    (trans lowerν∀ eqν∀)
    mixedνν
    (trans lowerνν eqνν)
    νlower

∀∀-support-from-selector-routes-with-νshapeᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-routes-with-νshapeᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {p∀ν = p∀ν} {q∀ν = q∀ν}
    {pν∀ = pν∀} {qν∀ = qν∀}
    {pνν = pνν} {qνν = qνν}
    route route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν real∀ shapeν
    with mlb-type-comparable-selectorᵢ
      {Γ = bothᵢ ∷ Γ} {A = A} {B = B} {p = p} {q = q} route
       | mlb-type-comparable-selectorᵢ
      {Γ = leftOnlyᵢ ∷ Γ} {A = A} {B = `∀ B}
      {p = p∀ν} {q = q∀ν} route∀ν
       | mlb-type-comparable-selectorᵢ
      {Γ = rightOnlyᵢ ∷ Γ} {A = `∀ A} {B = B}
      {p = pν∀} {q = qν∀} routeν∀
       | mlb-type-comparable-selectorᵢ
      {Γ = neitherᵢ ∷ Γ} {A = `∀ A} {B = `∀ B}
      {p = pνν} {q = qνν} routeνν
∀∀-support-from-selector-routes-with-νshapeᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    route route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν real∀ shapeν
    | body , lower-body | mixed∀ν , lower∀ν
    | mixedν∀ , lowerν∀ | mixedνν , lowerνν =
  subst
    (λ L →
      ForallForallComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B L)
    lower-body
    (∀∀-support-from-comparables-with-νshapeᵢ
      body
      mixed∀ν
      (trans (trans lower∀ν eq∀ν) (sym lower-body))
      mixedν∀
      (trans (trans lowerν∀ eqν∀) (sym lower-body))
      mixedνν
      (trans (trans lowerνν eqνν) (sym lower-body))
      (λ eq →
        real∀ (trans (sym lower-body) eq))
      (λ eq common∀ occD D⊑∀E →
        subst
          (λ L →
            idᵢ (choiceCommonCtxᵢ Γ)
              ∣ choiceCommonCtxᵢ Γ
              ⊢ _ ⊑ `∀ L ⊣ choiceCommonCtxᵢ Γ)
          (sym lower-body)
          (shapeν
            (trans (sym lower-body) eq)
            common∀
            occD
            D⊑∀E)))

∀∀-support-from-selector-route-packages-with-νshapeᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-route-packages-with-νshapeᵢ
    route
    (route∀ν , eq∀ν)
    (routeν∀ , eqν∀)
    (routeνν , eqνν)
    real∀
    shapeν =
  ∀∀-support-from-selector-routes-with-νshapeᵢ
    route
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    real∀
    shapeν

∀∀-real∀-from-non∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  Non∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ∀ {D} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
∀∀-real∀-from-non∀ᵢ non∀C eq =
  ⊥-elim (non∀-∀-eqᵢ non∀C eq)

∀∀-real∀-from-first-orderᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  FirstOrderSelectorᵢ {Γ = bothᵢ ∷ Γ} p q →
  ∀ {D} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
∀∀-real∀-from-first-orderᵢ {Γ = Γ} {p = p} {q = q} route =
  ∀∀-real∀-from-non∀ᵢ {Γ = Γ} {p = p} {q = q}
    (mlb-type-first-order-non∀ᵢ
      {Γ = bothᵢ ∷ Γ}
      {p = p}
      {q = q}
      route)

∀∀-real∀-from-selector-coherenceᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  ∀ {D} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
∀∀-real∀-from-selector-coherenceᵢ
    {Γ = Γ} {p = p} {q = q} {pˢ = pˢ} {qˢ = qˢ}
    route routeˢ eqˢ lower⊑lowerˢ {D = D} eq =
  subst
    (λ R →
      idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ `∀ D ⊑ R ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    (eqˢ eq)
    (subst
      (λ L →
        idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
          ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
          ⊢ L ⊑ mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ
          ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      eq
      lower⊑lowerˢ)

∀∀-real∀-from-renamed-swapped-bodyᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (routeˢ :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      (⊑-swap01∀∀ᵢ p)
      (⊑-swap01∀∀ᵢ q)) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ D →
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      (⊑-swap01∀∀ᵢ p)
      (⊑-swap01∀∀ᵢ q)
      ≡ renameᵗ swap01ᵢ D) →
  MlbTypeSelectorCoherenceᵢ
    (∀ᵢᶜ (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))))
    route
    routeˢ →
  ∀ {D} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
∀∀-real∀-from-renamed-swapped-bodyᵢ
    route support routeˢ supportˢ eqˢ body-coh =
  ∀∀-real∀-from-selector-coherenceᵢ
    (sel-∀∀ᵢ route support)
    (sel-∀∀ᵢ routeˢ supportˢ)
    (λ eq → cong `∀ (eqˢ (∀-injectiveᵢ eq)))
    (mlb-type-selector-∀∀-coherenceᵢ
      route
      routeˢ
      support
      supportˢ
      body-coh)

∀∀-real∀-from-selector-swap01ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  ∀ {D} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
∀∀-real∀-from-selector-swap01ᵢ route support swap supportˢ =
  ∀∀-real∀-from-renamed-swapped-bodyᵢ
    route
    support
    (selector-swap01-routeᵢ swap)
    supportˢ
    (selector-swap01-lower-atᵢ swap)
    (selector-swap01-coherenceᵢ swap)

∀∀-real∀-from-nested-selector-swap01ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  ∀ {D} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
    ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
    ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
∀∀-real∀-from-nested-selector-swap01ᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ =
  ∀∀-real∀-from-selector-swap01ᵢ
    (sel-∀∀ᵢ route support)
    support∀∀
    (mlb-type-selector-swap01-∀∀ᵢ route support swap supportˢ)
    support∀∀ˢ

∀∀-shapeν-from-body-coherenceᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {D E : Ty} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
  idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
    ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ) →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ `∀ E ⊑ `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
    ⊣ choiceCommonCtxᵢ Γ
∀∀-shapeν-from-body-coherenceᵢ {Γ = Γ} {p = p} {q = q}
    {D = D} {E = E} eq E⊑∀D =
  ∀ⁱ
    (subst
      (λ T →
        idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
          ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
          ⊢ E ⊑ T ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (sym eq)
      E⊑∀D)

∀∀-shapeν-from-body-continuationᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ∀ {D E} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
  ForallForallLower²ᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ E)
    A
    B →
  occurs zero D ≡ true →
  νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
    ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ `∀ E ⊑
      `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
    ⊣ choiceCommonCtxᵢ Γ
∀∀-shapeν-from-body-continuationᵢ {Γ = Γ} {p = p} {q = q}
    body-step {D = D} {E = E} eq common∀ occD D⊑∀E =
  ∀∀-shapeν-from-body-coherenceᵢ
    {Γ = Γ}
    {p = p}
    {q = q}
    {D = D}
    {E = E}
    eq
    (body-step eq common∀ occD D⊑∀E)

∀∀-support-from-selector-routes-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-routes-with-bodyνᵢ {p = p} {q = q}
    route route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν real∀ body-step =
  ∀∀-support-from-selector-routes-with-νshapeᵢ
    route
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    real∀
    (∀∀-shapeν-from-body-continuationᵢ {p = p} {q = q} body-step)

sel-∀∀-from-selector-routes-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-routes-with-bodyνᵢ
    route route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν real∀ body-step =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-routes-with-bodyνᵢ
      route
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      real∀
      body-step)

∀∀-support-from-selector-route-packages-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-route-packages-with-bodyνᵢ
    route
    (route∀ν , eq∀ν)
    (routeν∀ , eqν∀)
    (routeνν , eqνν)
    real∀
    body-step =
  ∀∀-support-from-selector-routes-with-bodyνᵢ
    route
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    real∀
    body-step

sel-∀∀-from-selector-route-packages-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-route-packages-with-bodyνᵢ
    route package∀ν packageν∀ packageνν real∀ body-step =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-route-packages-with-bodyνᵢ
      route
      package∀ν
      packageν∀
      packageνν
      real∀
      body-step)

∀∀-polymorphic-shapeν-from-body-continuationᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)} →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ∀ {D E} →
  mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
  ForallForallLower²ᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ E)
    (`∀ A)
    (`∀ B) →
  occurs zero D ≡ true →
  νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
    ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
    ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
  idᵢ (choiceCommonCtxᵢ Γ)
    ∣ choiceCommonCtxᵢ Γ
    ⊢ `∀ E ⊑
      `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
    ⊣ choiceCommonCtxᵢ Γ
∀∀-polymorphic-shapeν-from-body-continuationᵢ {p = p} {q = q}
    body-step =
  ∀∀-shapeν-from-body-continuationᵢ {p = ∀ⁱ p} {q = ∀ⁱ q}
    body-step

∀∀-support-from-selector-routes-with-swappedᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-routes-with-swappedᵢ
    route routeˢ eqˢ lower⊑lowerˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν shapeν =
  ∀∀-support-from-selector-routes-with-νshapeᵢ
    route
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    (∀∀-real∀-from-selector-coherenceᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ)
    shapeν

∀∀-support-from-selector-route-packages-with-swappedᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-route-packages-with-swappedᵢ
    route routeˢ eqˢ lower⊑lowerˢ package∀ν packageν∀ packageνν
    shapeν =
  ∀∀-support-from-selector-route-packages-with-νshapeᵢ
    route
    package∀ν
    packageν∀
    packageνν
    (∀∀-real∀-from-selector-coherenceᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ)
    shapeν

∀∀-support-from-selector-routes-with-swapped-bodyνᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-routes-with-swapped-bodyνᵢ
    {p = p} {q = q} route routeˢ eqˢ lower⊑lowerˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν body-step =
  ∀∀-support-from-selector-routes-with-swappedᵢ
    route
    routeˢ
    eqˢ
    lower⊑lowerˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    (∀∀-shapeν-from-body-continuationᵢ {p = p} {q = q} body-step)

∀∀-support-from-selector-route-packages-with-swapped-bodyνᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
∀∀-support-from-selector-route-packages-with-swapped-bodyνᵢ
    route routeˢ eqˢ lower⊑lowerˢ
    package∀ν packageν∀ packageνν body-step =
  ∀∀-support-from-selector-route-packages-with-bodyνᵢ
    route
    package∀ν
    packageν∀
    packageνν
    (∀∀-real∀-from-selector-coherenceᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ)
    body-step

∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ A)
    (`∀ B)
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ
    route support swap supportˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν shapeν =
  ∀∀-support-from-selector-route-packages-with-νshapeᵢ
    (sel-∀∀ᵢ route support)
    (route∀ν , eq∀ν)
    (routeν∀ , eqν∀)
    (routeνν , eqνν)
    (∀∀-real∀-from-selector-swap01ᵢ route support swap supportˢ)
    shapeν

∀∀-support-from-polymorphic-body-packages-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ A)
    (`∀ B)
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
∀∀-support-from-polymorphic-body-packages-with-swap01ᵢ
    route support swap supportˢ
    (route∀ν , eq∀ν) (routeν∀ , eqν∀) (routeνν , eqνν) shapeν =
  ∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ
    route
    support
    swap
    supportˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    shapeν

sel-∀∀-from-polymorphic-body-packages-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
sel-∀∀-from-polymorphic-body-packages-with-swap01ᵢ
    route support swap supportˢ package∀ν packageν∀ packageνν shapeν =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ route support)
    (∀∀-support-from-polymorphic-body-packages-with-swap01ᵢ
      route
      support
      swap
      supportˢ
      package∀ν
      packageν∀
      packageνν
      shapeν)

∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ A)
    (`∀ B)
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ
    {p = p} {q = q} route support swap supportˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν body-step =
  ∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ
    route
    support
    swap
    supportˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    (∀∀-polymorphic-shapeν-from-body-continuationᵢ {p = p} {q = q}
      body-step)

∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ (`∀ A))
    (`∀ (`∀ B))
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
      (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν shapeν =
  ∀∀-support-from-selector-route-packages-with-νshapeᵢ
    (sel-∀∀ᵢ (sel-∀∀ᵢ route support) support∀∀)
    (route∀ν , eq∀ν)
    (routeν∀ , eqν∀)
    (routeνν , eqνν)
    (∀∀-real∀-from-nested-selector-swap01ᵢ
      route support support∀∀ swap supportˢ support∀∀ˢ)
    shapeν

∀∀-support-from-nested-polymorphic-body-packages-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
      ⊣ choiceCommonCtxᵢ Γ) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ (`∀ A))
    (`∀ (`∀ B))
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
      (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
∀∀-support-from-nested-polymorphic-body-packages-with-swap01ᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    (route∀ν , eq∀ν) (routeν∀ , eqν∀) (routeνν , eqνν) shapeν =
  ∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ
    route
    support
    support∀∀
    swap
    supportˢ
    support∀∀ˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    shapeν

sel-∀∀-from-nested-polymorphic-body-packages-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ (∀ⁱ p))) (∀ⁱ (∀ⁱ (∀ⁱ q)))
sel-∀∀-from-nested-polymorphic-body-packages-with-swap01ᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    package∀ν packageν∀ packageνν shapeν =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ (sel-∀∀ᵢ route support) support∀∀)
    (∀∀-support-from-nested-polymorphic-body-packages-with-swap01ᵢ
      route
      support
      support∀∀
      swap
      supportˢ
      support∀∀ˢ
      package∀ν
      packageν∀
      packageνν
      shapeν)

∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ (`∀ A))
    (`∀ (`∀ B))
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
      (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ
    {p = p} {q = q} route support support∀∀ swap supportˢ support∀∀ˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν body-step =
  ∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ
    route
    support
    support∀∀
    swap
    supportˢ
    support∀∀ˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    eqνν
    (∀∀-polymorphic-shapeν-from-body-continuationᵢ
      {p = ∀ⁱ p}
      {q = ∀ⁱ q}
      body-step)

sel-∀∀-from-nested-polymorphic-body-routes-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ (∀ⁱ p))) (∀ⁱ (∀ⁱ (∀ⁱ q)))
sel-∀∀-from-nested-polymorphic-body-routes-with-swap01ᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν shapeν =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ (sel-∀∀ᵢ route support) support∀∀)
    (∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ
      route
      support
      support∀∀
      swap
      supportˢ
      support∀∀ˢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      shapeν)

sel-∀∀-from-nested-polymorphic-body-routes-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ (∀ⁱ p))) (∀ⁱ (∀ⁱ (∀ⁱ q)))
sel-∀∀-from-nested-polymorphic-body-routes-with-bodyνᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν body-step =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ (sel-∀∀ᵢ route support) support∀∀)
    (∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ
      route
      support
      support∀∀
      swap
      supportˢ
      support∀∀ˢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      body-step)

sel-∀∀-from-polymorphic-body-routes-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
sel-∀∀-from-polymorphic-body-routes-with-swap01ᵢ
    route support swap supportˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν shapeν =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ route support)
    (∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ
      route
      support
      swap
      supportˢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      shapeν)

sel-∀∀-from-polymorphic-body-routes-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
sel-∀∀-from-polymorphic-body-routes-with-bodyνᵢ
    route support swap supportˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν body-step =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ route support)
    (∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ
      route
      support
      swap
      supportˢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      body-step)

∀∀-support-from-polymorphic-body-packages-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ≡ true →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
    ×
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ≡ false →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) [ zero ]ᴿ) →
  occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
    ≡ true →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ A)
    (`∀ B)
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
∀∀-support-from-polymorphic-body-packages-with-bodyνᵢ
    route support swap supportˢ
    (route∀ν , eq∀ν) (routeν∀ , eqν∀) (routeνν , eqνν , _)
    occ-body body-step =
  ∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ
    route
    support
    swap
    supportˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    (eqνν occ-body)
    body-step

sel-∀∀-from-polymorphic-body-packages-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ A)
      (renameᵗ swap01ᵢ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ p)
        (⊑-swap01∀∀ᵢ q))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q)) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ≡ true →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
    ×
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
      ≡ false →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) [ zero ]ᴿ) →
  occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q))
    ≡ true →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ p) (∀ⁱ q) ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ A)
      (`∀ B) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
sel-∀∀-from-polymorphic-body-packages-with-bodyνᵢ
    route support swap supportˢ
    package∀ν packageν∀ packageνν occ-body body-step =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ route support)
    (∀∀-support-from-polymorphic-body-packages-with-bodyνᵢ
      route
      support
      swap
      supportˢ
      package∀ν
      packageν∀
      packageνν
      occ-body
      body-step)

∀∀-support-from-nested-polymorphic-body-packages-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (occurs zero
      (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ≡ true →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ×
    (occurs zero
      (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ≡ false →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) [ zero ]ᴿ) →
  occurs zero
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ≡ true →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ (`∀ A))
    (`∀ (`∀ B))
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
      (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
∀∀-support-from-nested-polymorphic-body-packages-with-bodyνᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    (route∀ν , eq∀ν) (routeν∀ , eqν∀) (routeνν , eqνν , _)
    occ-body body-step =
  ∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ
    route
    support
    support∀∀
    swap
    supportˢ
    support∀∀ˢ
    route∀ν
    eq∀ν
    routeν∀
    eqν∀
    routeνν
    (eqνν occ-body)
    body-step

sel-∀∀-from-nested-polymorphic-body-packages-with-bodyνᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ A) ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ (`∀ B) ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ A))
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ (`∀ (`∀ B))
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (support∀∀ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (`∀ A)
      (`∀ B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (support∀∀ˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ Γ))
      (renameᵗ swap01ᵢ (`∀ A))
      (renameᵗ swap01ᵢ (`∀ B))
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀ᵢ (∀ⁱ p))
        (⊑-swap01∀∀ᵢ (∀ⁱ q)))) →
  Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))) →
  Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    (occurs zero
      (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ≡ true →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ×
    (occurs zero
      (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ≡ false →
      mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ}
          (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)) [ zero ]ᴿ) →
  occurs zero
    (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q)))
    ≡ true →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} (∀ⁱ (∀ⁱ p)) (∀ⁱ (∀ⁱ q))
      ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      (`∀ (`∀ A))
      (`∀ (`∀ B)) →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ (∀ⁱ (∀ⁱ p))) (∀ⁱ (∀ⁱ (∀ⁱ q)))
sel-∀∀-from-nested-polymorphic-body-packages-with-bodyνᵢ
    route support support∀∀ swap supportˢ support∀∀ˢ
    package∀ν packageν∀ packageνν occ-body body-step =
  sel-∀∀ᵢ
    (sel-∀∀ᵢ (sel-∀∀ᵢ route support) support∀∀)
    (∀∀-support-from-nested-polymorphic-body-packages-with-bodyνᵢ
      route
      support
      support∀∀
      swap
      supportˢ
      support∀∀ˢ
      package∀ν
      packageν∀
      packageνν
      occ-body
      body-step)

sel-∀∀-from-selector-routesᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D} →
    CommonLowerBoundᶜᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ A) (`∀ B) D →
    occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ true →
    νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ))
      ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
      ⊢ mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ⊑ D
      ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ D ⊑ `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-routesᵢ
    route route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν νlower =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-routesᵢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      νlower)

sel-∀∀-from-selector-routes-with-νshapeᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-routes-with-νshapeᵢ
    route route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν real∀ shapeν =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-routes-with-νshapeᵢ
      route
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      real∀
      shapeν)

sel-∀∀-from-selector-route-packages-with-νshapeᵢ :
  ∀ {Γ C A B C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
      ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-route-packages-with-νshapeᵢ
    route package∀ν packageν∀ packageνν real∀ shapeν =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-route-packages-with-νshapeᵢ
      route
      package∀ν
      packageν∀
      packageνν
      real∀
      shapeν)

sel-∀∀-from-selector-routes-with-swappedᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-routes-with-swappedᵢ
    route routeˢ eqˢ lower⊑lowerˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν shapeν =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-routes-with-swappedᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      shapeν)

sel-∀∀-from-selector-route-packages-with-swappedᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ Γ)
      ∣ choiceCommonCtxᵢ Γ
      ⊢ `∀ E ⊑
        `∀ (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
      ⊣ choiceCommonCtxᵢ Γ) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-route-packages-with-swappedᵢ
    route routeˢ eqˢ lower⊑lowerˢ package∀ν packageν∀ packageνν
    shapeν =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-route-packages-with-swappedᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ
      package∀ν
      packageν∀
      packageνν
      shapeν)

sel-∀∀-from-selector-routes-with-swapped-bodyνᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-routes-with-swapped-bodyνᵢ
    route routeˢ eqˢ lower⊑lowerˢ
    route∀ν eq∀ν routeν∀ eqν∀ routeνν eqνν body-step =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-routes-with-swapped-bodyνᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ
      route∀ν
      eq∀ν
      routeν∀
      eqν∀
      routeνν
      eqνν
      body-step)

sel-∀∀-from-selector-route-packages-with-swapped-bodyνᵢ :
  ∀ {Γ C A B Cˢ Aˢ Bˢ C∀ν Cν∀ Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pˢ :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Aˢ ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {qˢ :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ Cˢ ⊑ Bˢ ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeˢ : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ) →
  (∀ {D} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} pˢ qˢ ≡
      `∀ (renameᵗ swap01ᵢ D)) →
  MlbTypeSelectorCoherenceᵢ
    (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)))
    route
    routeˢ →
  (Σ[ route∀ν ∈ MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ]
    mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeν∀ ∈ MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ]
    mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (Σ[ routeνν ∈ MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ]
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (∀ {D E} →
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q ≡ `∀ D →
    ForallForallLower²ᵢ
      (leftChoiceᵢ Γ)
      (rightChoiceᵢ Γ)
      (choiceCommonCtxᵢ Γ)
      (choiceLeftCtxᵢ Γ)
      (choiceRightCtxᵢ Γ)
      (`∀ E)
      A
      B →
    occurs zero D ≡ true →
    νᵢᶜ (νᵢᶜ (idᵢ (choiceCommonCtxᵢ Γ)))
      ∣ suc (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ⊢ D ⊑ `∀ E ⊣ choiceCommonCtxᵢ Γ →
    idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ))
      ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
      ⊢ E ⊑ `∀ D ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)) →
  MlbTypeSelectorᵢ (∀ⁱ p) (∀ⁱ q)
sel-∀∀-from-selector-route-packages-with-swapped-bodyνᵢ
    route routeˢ eqˢ lower⊑lowerˢ
    package∀ν packageν∀ packageνν body-step =
  sel-∀∀ᵢ
    route
    (∀∀-support-from-selector-route-packages-with-swapped-bodyνᵢ
      route
      routeˢ
      eqˢ
      lower⊑lowerˢ
      package∀ν
      packageν∀
      packageνν
      body-step)

comparable-choice-id-unidᶜᵢ :
  ∀ {Δ A B} →
  ComparableMaximalLowerBoundᶜᵢ
    (leftChoiceᵢ (choice-idᵢ Δ))
    (rightChoiceᵢ (choice-idᵢ Δ))
    (idᵢ (choiceCommonCtxᵢ (choice-idᵢ Δ)))
    (choiceCommonCtxᵢ (choice-idᵢ Δ))
    (choiceLeftCtxᵢ (choice-idᵢ Δ))
    (choiceRightCtxᵢ (choice-idᵢ Δ))
    A B →
  ComparableMaximalLowerBoundᵢ Δ A B
comparable-choice-id-unidᶜᵢ {Δ = Δ} cb
    rewrite leftChoice-idᵢ Δ
          | rightChoice-idᵢ Δ
          | choice-id-commonCtxᵢ Δ
          | choice-id-leftCtxᵢ Δ
          | choice-id-rightCtxᵢ Δ =
  comparable-unidᶜᵢ cb

comparable-choice-id-unid-lowerᵢ :
  ∀ {Δ A B}
    (cb :
      ComparableMaximalLowerBoundᶜᵢ
        (leftChoiceᵢ (choice-idᵢ Δ))
        (rightChoiceᵢ (choice-idᵢ Δ))
        (idᵢ (choiceCommonCtxᵢ (choice-idᵢ Δ)))
        (choiceCommonCtxᵢ (choice-idᵢ Δ))
        (choiceLeftCtxᵢ (choice-idᵢ Δ))
        (choiceRightCtxᵢ (choice-idᵢ Δ))
        A B) →
  c-lowerᵢ (comparable-choice-id-unidᶜᵢ cb) ≡ cᶜ-lowerᵢ cb
comparable-choice-id-unid-lowerᵢ {Δ = Δ} cb
    rewrite leftChoice-idᵢ Δ
          | rightChoice-idᵢ Δ
          | choice-id-commonCtxᵢ Δ
          | choice-id-leftCtxᵢ Δ
          | choice-id-rightCtxᵢ Δ =
  refl

choice-id-comparable-selectorᵢ :
  ∀ {Δ C A B}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ Δ}
    (leftChoice-id-proofᵢ p)
    (rightChoice-id-proofᵢ q) →
  Σ[ cb ∈ ComparableMaximalLowerBoundᵢ Δ A B ]
    c-lowerᵢ cb ≡
      mlb-typeᵢ
        {Γ = choice-idᵢ Δ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)
choice-id-comparable-selectorᵢ {Δ = Δ} {p = p} {q = q}
    route =
  comparable-choice-id-unidᶜᵢ (proj₁ selected) ,
  subst
    (λ T →
      T ≡
      mlb-typeᵢ
        {Γ = choice-idᵢ Δ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q))
    (sym (comparable-choice-id-unid-lowerᵢ (proj₁ selected)))
    (proj₂ selected)
  where
    selected =
      mlb-type-comparable-selectorᵢ
        {Γ = choice-idᵢ Δ}
        {p = leftChoice-id-proofᵢ p}
        {q = rightChoice-id-proofᵢ q}
        route

choice-id-maximal-selectorᵢ :
  ∀ {Δ C A B}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ Δ}
    (leftChoice-id-proofᵢ p)
    (rightChoice-id-proofᵢ q) →
  Σ[ mlb ∈ MaximalLowerBoundᵢ Δ A B ]
    lowerᵢ mlb ≡
      mlb-typeᵢ
        {Γ = choice-idᵢ Δ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)
choice-id-maximal-selectorᵢ route =
  comparable⇒maximalᵢ (proj₁ selected) , proj₂ selected
  where
    selected = choice-id-comparable-selectorᵢ route

mlb-type-selector-∀ν-support-from-∀∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A (`∀ B) (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
mlb-type-selector-∀ν-support-from-∀∀ᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q} route support
    with mlb-type-comparable-selectorᵢ
      {Γ = bothᵢ ∷ Γ} {A = A} {B = B} {p = p} {q = q} route
mlb-type-selector-∀ν-support-from-∀∀ᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q} route support
    | body , eq =
  subst
    (λ T →
      ForallNuComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A (`∀ B) T)
    eq
    (∀ν-support-from-∀∀-supportᵢ
      body
      (subst
        (λ T →
          ForallForallComparableSupportᵢ
            (leftChoiceᵢ Γ)
            (rightChoiceᵢ Γ)
            (idᵢ (choiceCommonCtxᵢ Γ))
            (choiceCommonCtxᵢ Γ)
            (choiceLeftCtxᵢ Γ)
            (choiceRightCtxᵢ Γ)
            A B T)
        (sym eq)
        support))

mlb-type-selector-ν∀-support-from-∀∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ A) B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
mlb-type-selector-ν∀-support-from-∀∀ᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q} route support
    with mlb-type-comparable-selectorᵢ
      {Γ = bothᵢ ∷ Γ} {A = A} {B = B} {p = p} {q = q} route
mlb-type-selector-ν∀-support-from-∀∀ᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q} route support
    | body , eq =
  subst
    (λ T →
      NuForallComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        (`∀ A) B T)
    eq
    (ν∀-support-from-∀∀-supportᵢ
      body
      (subst
        (λ T →
          ForallForallComparableSupportᵢ
            (leftChoiceᵢ Γ)
            (rightChoiceᵢ Γ)
            (idᵢ (choiceCommonCtxᵢ Γ))
            (choiceCommonCtxᵢ Γ)
            (choiceLeftCtxᵢ Γ)
            (choiceRightCtxᵢ Γ)
            A B T)
        (sym eq)
        support))

mlb-type-selector-νν-support-from-∀∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  NuNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    (`∀ A) (`∀ B) (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q)
mlb-type-selector-νν-support-from-∀∀ᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q} route support
    with mlb-type-comparable-selectorᵢ
      {Γ = bothᵢ ∷ Γ} {A = A} {B = B} {p = p} {q = q} route
mlb-type-selector-νν-support-from-∀∀ᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q} route support
    | body , eq =
  subst
    (λ T →
      NuNuComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        (`∀ A) (`∀ B) T)
    eq
    (νν-support-from-∀∀-supportᵢ
      body
      (subst
        (λ T →
          ForallForallComparableSupportᵢ
            (leftChoiceᵢ Γ)
            (rightChoiceᵢ Γ)
            (idᵢ (choiceCommonCtxᵢ Γ))
            (choiceCommonCtxᵢ Γ)
            (choiceLeftCtxᵢ Γ)
            (choiceRightCtxᵢ Γ)
            A B T)
        (sym eq)
        support))

sel-∀ν-from-∀∀-supportᵢ :
  ∀ {Γ C A B C∀ν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {occ : occurs zero C∀ν ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (∀ⁱ p∀ν) (ν occ q∀ν)
sel-∀ν-from-∀∀-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {p∀ν = p∀ν} {q∀ν = q∀ν} {occ = occ}
    route support route∀ν eq∀ν =
  sel-∀νᵢ
    occ
    route∀ν
    (subst
      (λ T →
        ForallNuComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          A (`∀ B) T)
      (sym eq∀ν)
      (mlb-type-selector-∀ν-support-from-∀∀ᵢ route support))

sel-ν∀-from-∀∀-supportᵢ :
  ∀ {Γ C A B Cν∀}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {occ : occurs zero Cν∀ ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (ν occ pν∀) (∀ⁱ qν∀)
sel-ν∀-from-∀∀-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {pν∀ = pν∀} {qν∀ = qν∀} {occ = occ}
    route support routeν∀ eqν∀ =
  sel-ν∀ᵢ
    occ
    routeν∀
    (subst
      (λ T →
        NuForallComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          (`∀ A) B T)
      (sym eqν∀)
      (mlb-type-selector-ν∀-support-from-∀∀ᵢ route support))

sel-νν-from-∀∀-supportᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  MlbTypeSelectorᵢ (ν occ pνν) (ν occ′ qνν)
sel-νν-from-∀∀-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {pνν = pνν} {qνν = qνν} {occ = occ} {occ′ = occ′}
    route support routeνν eqνν =
  sel-ννᵢ
    occ
    occ′
    routeνν
    (subst
      (λ T →
        NuNuComparableSupportᵢ
          (leftChoiceᵢ Γ)
          (rightChoiceᵢ Γ)
          (idᵢ (choiceCommonCtxᵢ Γ))
          (choiceCommonCtxᵢ Γ)
          (choiceLeftCtxᵢ Γ)
          (choiceRightCtxᵢ Γ)
          (`∀ A) (`∀ B) T)
      (sym eqνν)
      (mlb-type-selector-νν-support-from-∀∀ᵢ route support))

sel-∀ν-from-∀∀-support-lowerᵢ :
  ∀ {Γ C A B C∀ν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {occ : occurs zero C∀ν ≡ true} →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  mlb-typeᵢ {Γ = Γ} (∀ⁱ p∀ν) (ν occ q∀ν) ≡
    mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
sel-∀ν-from-∀∀-support-lowerᵢ eq∀ν = cong `∀ eq∀ν

sel-ν∀-from-∀∀-support-lowerᵢ :
  ∀ {Γ C A B Cν∀}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {occ : occurs zero Cν∀ ≡ true} →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  mlb-typeᵢ {Γ = Γ} (ν occ pν∀) (∀ⁱ qν∀) ≡
    mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
sel-ν∀-from-∀∀-support-lowerᵢ eqν∀ = cong `∀ eqν∀

sel-νν-from-∀∀-support-true-lowerᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (eqνν :
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ true →
  mlb-typeᵢ {Γ = Γ} (ν occ pνν) (ν occ′ qνν) ≡
    mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
sel-νν-from-∀∀-support-true-lowerᵢ eqνν occ-body =
  trans
    (close-neither-true-eqᵢ
      (subst (λ T → occurs zero T ≡ true) (sym eqνν) occ-body))
    (cong `∀ eqνν)

sel-νν-from-∀∀-support-false-lowerᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (eqνν :
    mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
      mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ false →
  mlb-typeᵢ {Γ = Γ} (ν occ pνν) (ν occ′ qνν) ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q [ zero ]ᴿ
sel-νν-from-∀∀-support-false-lowerᵢ eqνν occ-body =
  trans
    (close-neither-false-eqᵢ
      (subst (λ T → occurs zero T ≡ false) (sym eqνν) occ-body))
    (cong (λ T → T [ zero ]ᴿ) eqνν)

sel-∀ν-from-∀∀-support-packageᵢ :
  ∀ {Γ C A B C∀ν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {occ : occurs zero C∀ν ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (route∀ν : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν) →
  mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p∀ν q∀ν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  Σ[ route′ ∈ MlbTypeSelectorᵢ (∀ⁱ p∀ν) (ν occ q∀ν) ]
    mlb-typeᵢ {Γ = Γ} (∀ⁱ p∀ν) (ν occ q∀ν) ≡
      mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
sel-∀ν-from-∀∀-support-packageᵢ
    {Γ = Γ} {p = p} {q = q} {p∀ν = p∀ν} {q∀ν = q∀ν}
    {occ = occ} route support route∀ν eq∀ν =
  sel-∀ν-from-∀∀-supportᵢ {occ = occ} route support route∀ν eq∀ν ,
  sel-∀ν-from-∀∀-support-lowerᵢ
    {Γ = Γ}
    {p = p}
    {q = q}
    {p∀ν = p∀ν}
    {q∀ν = q∀ν}
    {occ = occ}
    eq∀ν

sel-ν∀-from-∀∀-support-packageᵢ :
  ∀ {Γ C A B Cν∀}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {occ : occurs zero Cν∀ ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeν∀ : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀) →
  mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} pν∀ qν∀ ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  Σ[ route′ ∈ MlbTypeSelectorᵢ (ν occ pν∀) (∀ⁱ qν∀) ]
    mlb-typeᵢ {Γ = Γ} (ν occ pν∀) (∀ⁱ qν∀) ≡
      mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q)
sel-ν∀-from-∀∀-support-packageᵢ
    {Γ = Γ} {p = p} {q = q} {pν∀ = pν∀} {qν∀ = qν∀}
    {occ = occ} route support routeν∀ eqν∀ =
  sel-ν∀-from-∀∀-supportᵢ {occ = occ} route support routeν∀ eqν∀ ,
  sel-ν∀-from-∀∀-support-lowerᵢ
    {Γ = Γ}
    {p = p}
    {q = q}
    {pν∀ = pν∀}
    {qν∀ = qν∀}
    {occ = occ}
    eqν∀

sel-νν-from-∀∀-support-true-packageᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  Σ[ route′ ∈ MlbTypeSelectorᵢ (ν occ pνν) (ν occ′ qνν) ]
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ true →
      mlb-typeᵢ {Γ = Γ} (ν occ pνν) (ν occ′ qνν) ≡
        mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q))
sel-νν-from-∀∀-support-true-packageᵢ
    {Γ = Γ} {p = p} {q = q} {pνν = pνν} {qνν = qνν}
    {occ = occ} {occ′ = occ′} route support routeνν eqνν =
  sel-νν-from-∀∀-supportᵢ
    {occ = occ}
    {occ′ = occ′}
    route
    support
    routeνν
    eqνν
  ,
  sel-νν-from-∀∀-support-true-lowerᵢ
    {Γ = Γ}
    {p = p}
    {q = q}
    {pνν = pνν}
    {qνν = qνν}
    {occ = occ}
    {occ′ = occ′}
    eqνν

sel-νν-from-∀∀-support-false-packageᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  Σ[ route′ ∈ MlbTypeSelectorᵢ (ν occ pνν) (ν occ′ qνν) ]
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ false →
      mlb-typeᵢ {Γ = Γ} (ν occ pνν) (ν occ′ qνν) ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q [ zero ]ᴿ)
sel-νν-from-∀∀-support-false-packageᵢ
    {Γ = Γ} {p = p} {q = q} {pνν = pνν} {qνν = qνν}
    {occ = occ} {occ′ = occ′} route support routeνν eqνν =
  sel-νν-from-∀∀-supportᵢ
    {occ = occ}
    {occ′ = occ′}
    route
    support
    routeνν
    eqνν
  ,
  sel-νν-from-∀∀-support-false-lowerᵢ
    {Γ = Γ}
    {p = p}
    {q = q}
    {pνν = pνν}
    {qνν = qνν}
    {occ = occ}
    {occ′ = occ′}
    eqνν

sel-νν-from-∀∀-support-packageᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (route : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ Γ} p q) →
  ForallForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ)
    (choiceLeftCtxᵢ Γ)
    (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) →
  (routeνν : MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν) →
  mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} pνν qνν ≡
    mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q →
  Σ[ route′ ∈ MlbTypeSelectorᵢ (ν occ pνν) (ν occ′ qνν) ]
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ true →
      mlb-typeᵢ {Γ = Γ} (ν occ pνν) (ν occ′ qνν) ≡
        mlb-typeᵢ {Γ = Γ} (∀ⁱ p) (∀ⁱ q))
    ×
    (occurs zero (mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q) ≡ false →
      mlb-typeᵢ {Γ = Γ} (ν occ pνν) (ν occ′ qνν) ≡
        mlb-typeᵢ {Γ = bothᵢ ∷ Γ} p q [ zero ]ᴿ)
sel-νν-from-∀∀-support-packageᵢ
    {Γ = Γ} {p = p} {q = q} {pνν = pνν} {qνν = qνν}
    {occ = occ} {occ′ = occ′} route support routeνν eqνν =
  sel-νν-from-∀∀-supportᵢ
    {occ = occ}
    {occ′ = occ′}
    route
    support
    routeνν
    eqνν
  ,
  ( sel-νν-from-∀∀-support-true-lowerᵢ
      {Γ = Γ}
      {p = p}
      {q = q}
      {pνν = pνν}
      {qνν = qνν}
      {occ = occ}
      {occ′ = occ′}
      eqνν
  , sel-νν-from-∀∀-support-false-lowerᵢ
      {Γ = Γ}
      {p = p}
      {q = q}
      {pνν = pνν}
      {qνν = qνν}
      {occ = occ}
      {occ′ = occ′}
      eqνν
  )

selector-package-lower-transportᵢ :
  ∀ {Γ C A B L L′}
    {p :
      leftChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ Γ}
    {q :
      rightChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ Γ} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    mlb-typeᵢ {Γ = Γ} p q ≡ L →
  L ≡ L′ →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    mlb-typeᵢ {Γ = Γ} p q ≡ L′
selector-package-lower-transportᵢ (route , eq) eq′ =
  route , trans eq eq′

selector-package-true-lower-transportᵢ :
  ∀ {Γ C A B L L′}
    {p :
      leftChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ Γ}
    {q :
      rightChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ Γ} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L) →
  L ≡ L′ →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L′ ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L′)
selector-package-true-lower-transportᵢ (route , eq) eq′ =
  route ,
  λ occ′ → trans (eq (subst (λ T → occurs zero T ≡ true) (sym eq′) occ′))
                 eq′

selector-package-false-lower-transportᵢ :
  ∀ {Γ C A B L L′}
    {p :
      leftChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ Γ}
    {q :
      rightChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ Γ} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L [ zero ]ᴿ) →
  L ≡ L′ →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L′ ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L′ [ zero ]ᴿ)
selector-package-false-lower-transportᵢ (route , eq) eq′ =
  route ,
  λ occ′ →
    trans
      (eq (subst (λ T → occurs zero T ≡ false) (sym eq′) occ′))
      (cong (λ T → T [ zero ]ᴿ) eq′)

selector-package-split-lower-transportᵢ :
  ∀ {Γ C A B L L′}
    {p :
      leftChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ Γ}
    {q :
      rightChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ Γ} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L)
    ×
    (occurs zero L ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L [ zero ]ᴿ) →
  L ≡ L′ →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L′ ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L′)
    ×
    (occurs zero L′ ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L′ [ zero ]ᴿ)
selector-package-split-lower-transportᵢ (route , eqᵗ , eqᶠ) eq′ =
  route ,
  ( (λ occ′ →
      trans (eqᵗ (subst (λ T → occurs zero T ≡ true) (sym eq′) occ′))
            eq′)
  , (λ occ′ →
      trans
        (eqᶠ (subst (λ T → occurs zero T ≡ false) (sym eq′) occ′))
        (cong (λ T → T [ zero ]ᴿ) eq′))
  )

selector-package-split-true-lowerᵢ :
  ∀ {Γ C A B L}
    {p :
      leftChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ Γ}
    {q :
      rightChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ Γ} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L)
    ×
    (occurs zero L ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L [ zero ]ᴿ) →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L)
selector-package-split-true-lowerᵢ (route , eqᵗ , _) = route , eqᵗ

selector-package-split-false-lowerᵢ :
  ∀ {Γ C A B L}
    {p :
      leftChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ Γ}
    {q :
      rightChoiceᵢ Γ
        ∣ choiceCommonCtxᵢ Γ
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ Γ} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ true →
      mlb-typeᵢ {Γ = Γ} p q ≡ L)
    ×
    (occurs zero L ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L [ zero ]ᴿ) →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = Γ} p q ]
    (occurs zero L ≡ false →
      mlb-typeᵢ {Γ = Γ} p q ≡ L [ zero ]ᴿ)
selector-package-split-false-lowerᵢ (route , _ , eqᶠ) = route , eqᶠ

mlb-type-selector-swap01-∀ν-from-∀∀-supportᵢ :
  ∀ {Γ C A B C∀ν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A
        ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ : occurs zero C∀ν ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      {C = C}
      {A = A}
      {B = B}
      p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01Under∀ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (route∀ν :
    MlbTypeSelectorᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p∀ν
      q∀ν) →
  (eq∀ν :
    mlb-typeᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p∀ν
      q∀ν
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p
      q) →
  MlbTypeSelectorSwap01Under∀νᵢ route∀ν →
  MlbTypeSelectorSwap01ᵢ
    (sel-∀ν-from-∀∀-supportᵢ
      {occ = occ}
      route
      support
      route∀ν
      eq∀ν)
mlb-type-selector-swap01-∀ν-from-∀∀-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} route support swap supportˢ route∀ν eq∀ν swap∀ν =
  mlb-type-selector-swap01-∀νᵢ
    route∀ν
    (subst
      (λ T →
        ForallNuComparableSupportᵢ
          (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
          (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          A (`∀ B) T)
      (sym eq∀ν)
      (mlb-type-selector-∀ν-support-from-∀∀ᵢ route support))
    swap∀ν
    (subst
      (λ T →
        ForallNuComparableSupportᵢ
          (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
          (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (renameᵗ (extᵗ swap01ᵢ) A)
          (renameᵗ swap01ᵢ (`∀ B))
          T)
      (sym
        (selector-swap01-under∀ν-lower-from-∀∀ᵢ
          route
          route∀ν
          swap
          swap∀ν
          eq∀ν))
      (mlb-type-selector-∀ν-support-from-∀∀ᵢ
        (selector-swap01-under∀-routeᵢ swap)
        supportˢ))

sel-∀ν-from-∀∀-support-with-swap01ᵢ :
  ∀ {Γ C A B C∀ν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {p∀ν :
      leftChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C∀ν ⊑ A
        ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q∀ν :
      rightChoiceᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C∀ν ⊑ `∀ B
        ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ : occurs zero C∀ν ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (route∀ν :
    MlbTypeSelectorᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p∀ν
      q∀ν) →
  (eq∀ν :
    mlb-typeᵢ
      {Γ = leftOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p∀ν
      q∀ν
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p
      q) →
  MlbTypeSelectorSwap01Under∀νᵢ route∀ν →
  Σ[ route′ ∈
    MlbTypeSelectorᵢ
      (∀ⁱ p∀ν)
      (ν occ q∀ν) ]
    (mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      (∀ⁱ p∀ν)
      (ν occ q∀ν)
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      (∀ⁱ p)
      (∀ⁱ q))
    ×
    MlbTypeSelectorSwap01ᵢ route′
sel-∀ν-from-∀∀-support-with-swap01ᵢ
    {Γ = Γ} {p = p} {q = q} {p∀ν = p∀ν} {q∀ν = q∀ν}
    {occ = occ} route support swap supportˢ route∀ν eq∀ν swap∀ν =
  sel-∀ν-from-∀∀-supportᵢ {occ = occ} route support route∀ν eq∀ν ,
  ( sel-∀ν-from-∀∀-support-lowerᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      {p = p}
      {q = q}
      {p∀ν = p∀ν}
      {q∀ν = q∀ν}
      {occ = occ}
      eq∀ν
  , mlb-type-selector-swap01-∀ν-from-∀∀-supportᵢ
      route
      support
      swap
      supportˢ
      route∀ν
      eq∀ν
      swap∀ν
  )

mlb-type-selector-swap01-ν∀-from-∀∀-supportᵢ :
  ∀ {Γ C A B Cν∀}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B
        ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ : occurs zero Cν∀ ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      {C = C}
      {A = A}
      {B = B}
      p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01Under∀ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (routeν∀ :
    MlbTypeSelectorᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pν∀
      qν∀) →
  (eqν∀ :
    mlb-typeᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pν∀
      qν∀
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p
      q) →
  MlbTypeSelectorSwap01Underν∀ᵢ routeν∀ →
  MlbTypeSelectorSwap01ᵢ
    (sel-ν∀-from-∀∀-supportᵢ
      {occ = occ}
      route
      support
      routeν∀
      eqν∀)
mlb-type-selector-swap01-ν∀-from-∀∀-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} route support swap supportˢ routeν∀ eqν∀ swapν∀ =
  mlb-type-selector-swap01-ν∀ᵢ
    routeν∀
    (subst
      (λ T →
        NuForallComparableSupportᵢ
          (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
          (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (`∀ A) B T)
      (sym eqν∀)
      (mlb-type-selector-ν∀-support-from-∀∀ᵢ route support))
    swapν∀
    (subst
      (λ T →
        NuForallComparableSupportᵢ
          (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
          (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (renameᵗ swap01ᵢ (`∀ A))
          (renameᵗ (extᵗ swap01ᵢ) B)
          T)
      (sym
        (selector-swap01-underν∀-lower-from-∀∀ᵢ
          route
          routeν∀
          swap
          swapν∀
          eqν∀))
      (mlb-type-selector-ν∀-support-from-∀∀ᵢ
        (selector-swap01-under∀-routeᵢ swap)
        supportˢ))

sel-ν∀-from-∀∀-support-with-swap01ᵢ :
  ∀ {Γ C A B Cν∀}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {pν∀ :
      leftChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ `∀ A
        ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {qν∀ :
      rightChoiceᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cν∀ ⊑ B
        ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ : occurs zero Cν∀ ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (routeν∀ :
    MlbTypeSelectorᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pν∀
      qν∀) →
  (eqν∀ :
    mlb-typeᵢ
      {Γ = rightOnlyᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pν∀
      qν∀
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p
      q) →
  MlbTypeSelectorSwap01Underν∀ᵢ routeν∀ →
  Σ[ route′ ∈
    MlbTypeSelectorᵢ
      (ν occ pν∀)
      (∀ⁱ qν∀) ]
    (mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      (ν occ pν∀)
      (∀ⁱ qν∀)
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      (∀ⁱ p)
      (∀ⁱ q))
    ×
    MlbTypeSelectorSwap01ᵢ route′
sel-ν∀-from-∀∀-support-with-swap01ᵢ
    {Γ = Γ} {p = p} {q = q} {pν∀ = pν∀} {qν∀ = qν∀}
    {occ = occ} route support swap supportˢ routeν∀ eqν∀ swapν∀ =
  sel-ν∀-from-∀∀-supportᵢ {occ = occ} route support routeν∀ eqν∀ ,
  ( sel-ν∀-from-∀∀-support-lowerᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
      {p = p}
      {q = q}
      {pν∀ = pν∀}
      {qν∀ = qν∀}
      {occ = occ}
      eqν∀
  , mlb-type-selector-swap01-ν∀-from-∀∀-supportᵢ
      route
      support
      swap
      supportˢ
      routeν∀
      eqν∀
      swapν∀
  )

mlb-type-selector-swap01-νν-from-∀∀-supportᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  (swap : MlbTypeSelectorSwap01Under∀ᵢ route) →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (routeνν :
    MlbTypeSelectorᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pνν
      qνν) →
  (eqνν :
    mlb-typeᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pνν
      qνν
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p
      q) →
  MlbTypeSelectorSwap01Underννᵢ routeνν →
  MlbTypeSelectorSwap01ᵢ
    (sel-νν-from-∀∀-supportᵢ
      {occ = occ}
      {occ′ = occ′}
      route
      support
      routeνν
      eqνν)
mlb-type-selector-swap01-νν-from-∀∀-supportᵢ
    {Γ = Γ} {A = A} {B = B} {p = p} {q = q}
    {occ = occ} {occ′ = occ′}
    route support swap supportˢ routeνν eqνν swapνν =
  mlb-type-selector-swap01-ννᵢ
    routeνν
    (subst
      (λ T →
        NuNuComparableSupportᵢ
          (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
          (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (`∀ A) (`∀ B) T)
      (sym eqνν)
      (mlb-type-selector-νν-support-from-∀∀ᵢ route support))
    swapνν
    (subst
      (λ T →
        NuNuComparableSupportᵢ
          (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
          (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
          (renameᵗ swap01ᵢ (`∀ A))
          (renameᵗ swap01ᵢ (`∀ B))
          T)
      (sym
        (selector-swap01-underνν-lower-from-∀∀ᵢ
          route
          routeνν
          swap
          swapνν
          eqνν))
      (mlb-type-selector-νν-support-from-∀∀ᵢ
        (selector-swap01-under∀-routeᵢ swap)
        supportˢ))

sel-νν-from-∀∀-support-with-swap01ᵢ :
  ∀ {Γ C A B Cνν}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {pνν :
      leftChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ A
        ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {qνν :
      rightChoiceᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ Cνν ⊑ `∀ B
        ⊣ choiceRightCtxᵢ (neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ)}
    {occ occ′ : occurs zero Cνν ≡ true} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p q) →
  (support :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      A B
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)) →
  MlbTypeSelectorSwap01Under∀ᵢ route →
  (supportˢ :
    ForallForallComparableSupportᵢ
      (leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)))
      (choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ))
      (renameᵗ (extᵗ swap01ᵢ) A)
      (renameᵗ (extᵗ swap01ᵢ) B)
      (mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        (⊑-swap01∀∀-under∀ᵢ p)
        (⊑-swap01∀∀-under∀ᵢ q))) →
  (routeνν :
    MlbTypeSelectorᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pνν
      qνν) →
  (eqνν :
    mlb-typeᵢ
      {Γ = neitherᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      pνν
      qνν
    ≡
    mlb-typeᵢ
      {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
      p
      q) →
  MlbTypeSelectorSwap01Underννᵢ routeνν →
  Σ[ route′ ∈
    MlbTypeSelectorᵢ
      (ν occ pνν)
      (ν occ′ qνν) ]
    (occurs zero
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)
    ≡ true →
      mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (ν occ pνν)
        (ν occ′ qνν)
      ≡
      mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (∀ⁱ p)
        (∀ⁱ q))
    ×
    ((occurs zero
      (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ} p q)
    ≡ false →
      mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        (ν occ pνν)
        (ν occ′ qνν)
      ≡
      mlb-typeᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ bothᵢ ∷ Γ}
        p
        q
      [ zero ]ᴿ)
    ×
    MlbTypeSelectorSwap01ᵢ route′)
sel-νν-from-∀∀-support-with-swap01ᵢ
    {Γ = Γ} {p = p} {q = q} {pνν = pνν} {qνν = qνν}
    {occ = occ} {occ′ = occ′}
    route support swap supportˢ routeνν eqνν swapνν =
  sel-νν-from-∀∀-supportᵢ
    {occ = occ}
    {occ′ = occ′}
    route
    support
    routeνν
    eqνν
  ,
  ( (λ occ-body →
      sel-νν-from-∀∀-support-true-lowerᵢ
        {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
        {p = p}
        {q = q}
        {pνν = pνν}
        {qνν = qνν}
        {occ = occ}
        {occ′ = occ′}
        eqνν
        occ-body)
  , ( (λ occ-body →
        sel-νν-from-∀∀-support-false-lowerᵢ
          {Γ = bothᵢ ∷ bothᵢ ∷ Γ}
          {p = p}
          {q = q}
          {pνν = pνν}
          {qνν = qνν}
          {occ = occ}
          {occ′ = occ′}
          eqνν
          occ-body)
    , mlb-type-selector-swap01-νν-from-∀∀-supportᵢ
        route
        support
        swap
        supportˢ
        routeνν
        eqνν
        swapνν
    )
  )

selector-swap01-package-lowerᵢ :
  ∀ {Γ C A B L}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    (mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L) ×
    MlbTypeSelectorSwap01ᵢ route →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L
selector-swap01-package-lowerᵢ (route , eq , _) = route , eq

selector-swap01-package-true-lowerᵢ :
  ∀ {Γ C A B L} {P : Set}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {R : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q → Set} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    (P → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L) ×
    (R route × MlbTypeSelectorSwap01ᵢ route) →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    (P → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L)
selector-swap01-package-true-lowerᵢ (route , eq , _) = route , eq

selector-swap01-package-false-lowerᵢ :
  ∀ {Γ C A B L} {P : Set}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {R : MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q → Set} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    R route ×
    (P → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L) ×
    MlbTypeSelectorSwap01ᵢ route →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    (P → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L)
selector-swap01-package-false-lowerᵢ (route , _ , eq , _) = route , eq

selector-swap01-package-split-lowerᵢ :
  ∀ {Γ C A B L L′} {P Q : Set}
    {p :
      leftChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (bothᵢ ∷ bothᵢ ∷ Γ)} →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    (P → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L) ×
    (Q → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L′) ×
    MlbTypeSelectorSwap01ᵢ route →
  Σ[ route ∈ MlbTypeSelectorᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ]
    (P → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L) ×
    (Q → mlb-typeᵢ {Γ = bothᵢ ∷ bothᵢ ∷ Γ} p q ≡ L′)
selector-swap01-package-split-lowerᵢ (route , eq , eq′ , _) =
  route , eq , eq′

mlb-type-selector-non∀-∀ν-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  Non∀ (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  Non∀ B →
  ForallNuComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q)
mlb-type-selector-non∀-∀ν-supportᵢ {Γ = Γ} {A = A} {B = B}
    {p = p} {q = q} route non∀C non∀B
    with mlb-type-comparable-selectorᵢ
      {Γ = leftOnlyᵢ ∷ Γ} {A = A} {B = B} {p = p} {q = q} route
mlb-type-selector-non∀-∀ν-supportᵢ {Γ = Γ} {A = A} {B = B}
    {p = p} {q = q} route non∀C non∀B | body , eq =
  subst
    (λ T →
      ForallNuComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B T)
    eq
    (non∀-∀ν-supportᵢ
      body
      (subst Non∀ (sym eq) non∀C)
      non∀B)

sel-∀ν-non∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    (occ : occurs zero C ≡ true) →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p q →
  Non∀ (mlb-typeᵢ {Γ = leftOnlyᵢ ∷ Γ} p q) →
  Non∀ B →
  MlbTypeSelectorᵢ (∀ⁱ p) (ν occ q)
sel-∀ν-non∀ᵢ occ route non∀C non∀B =
  sel-∀νᵢ
    occ
    route
    (mlb-type-selector-non∀-∀ν-supportᵢ route non∀C non∀B)

mlb-type-selector-non∀-ν∀-supportᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)} →
  (route : MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  Non∀ (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  Non∀ A →
  NuForallComparableSupportᵢ
    (leftChoiceᵢ Γ)
    (rightChoiceᵢ Γ)
    (idᵢ (choiceCommonCtxᵢ Γ))
    (choiceCommonCtxᵢ Γ) (choiceLeftCtxᵢ Γ) (choiceRightCtxᵢ Γ)
    A B (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q)
mlb-type-selector-non∀-ν∀-supportᵢ {Γ = Γ} {A = A} {B = B}
    {p = p} {q = q} route non∀C non∀A
    with mlb-type-comparable-selectorᵢ
      {Γ = rightOnlyᵢ ∷ Γ} {A = A} {B = B} {p = p} {q = q} route
mlb-type-selector-non∀-ν∀-supportᵢ {Γ = Γ} {A = A} {B = B}
    {p = p} {q = q} route non∀C non∀A | body , eq =
  subst
    (λ T →
      NuForallComparableSupportᵢ
        (leftChoiceᵢ Γ)
        (rightChoiceᵢ Γ)
        (idᵢ (choiceCommonCtxᵢ Γ))
        (choiceCommonCtxᵢ Γ)
        (choiceLeftCtxᵢ Γ)
        (choiceRightCtxᵢ Γ)
        A B T)
    eq
    (non∀-ν∀-supportᵢ
      body
      (subst Non∀ (sym eq) non∀C)
      non∀A)

sel-ν∀-non∀ᵢ :
  ∀ {Γ C A B}
    {p :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ A ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C ⊑ B ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    (occ : occurs zero C ≡ true) →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p q →
  Non∀ (mlb-typeᵢ {Γ = rightOnlyᵢ ∷ Γ} p q) →
  Non∀ A →
  MlbTypeSelectorᵢ (ν occ p) (∀ⁱ q)
sel-ν∀-non∀ᵢ occ route non∀C non∀A =
  sel-ν∀ᵢ
    occ
    route
    (mlb-type-selector-non∀-ν∀-supportᵢ route non∀C non∀A)

sel-∀ν-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ
    (∀ⁱ (p₁ ↦ p₂))
    (ν occ (q₁ ↦ q₂))
sel-∀ν-arrow-arrowᵢ occ route₁ route₂ =
  sel-∀ν-non∀ᵢ
    occ
    (sel-arrow-arrowᵢ route₁ route₂)
    non∀-⇒
    non∀-⇒

sel-ν∀-arrow-arrowᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ
    (ν occ (p₁ ↦ p₂))
    (∀ⁱ (q₁ ↦ q₂))
sel-ν∀-arrow-arrowᵢ occ route₁ route₂ =
  sel-ν∀-non∀ᵢ
    occ
    (sel-arrow-arrowᵢ route₁ route₂)
    non∀-⇒
    non∀-⇒

sel-∀ν-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ
    (∀ⁱ (p₁ ↦ p₂))
    (ν occ (tag q₁ ⇛ q₂))
sel-∀ν-arrow-starᵢ occ route₁ route₂ =
  sel-∀ν-non∀ᵢ
    occ
    (sel-arrow-starᵢ route₁ route₂)
    non∀-⇒
    non∀-★

sel-ν∀-arrow-starᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ
    (ν occ (p₁ ↦ p₂))
    (∀ⁱ (tag q₁ ⇛ q₂))
sel-ν∀-arrow-starᵢ occ route₁ route₂ =
  sel-ν∀-non∀ᵢ
    occ
    (sel-arrow-starᵢ route₁ route₂)
    non∀-⇒
    non∀-⇒

sel-∀ν-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = leftOnlyᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ
    (∀ⁱ (tag p₁ ⇛ p₂))
    (ν occ (q₁ ↦ q₂))
sel-∀ν-star-arrowᵢ occ route₁ route₂ =
  sel-∀ν-non∀ᵢ
    occ
    (sel-star-arrowᵢ route₁ route₂)
    non∀-⇒
    non∀-⇒

sel-ν∀-star-arrowᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = rightOnlyᵢ ∷ Γ} p₂ q₂ →
  MlbTypeSelectorᵢ
    (ν occ (tag p₁ ⇛ p₂))
    (∀ⁱ (q₁ ↦ q₂))
sel-ν∀-star-arrowᵢ occ route₁ route₂ =
  sel-ν∀-non∀ᵢ
    occ
    (sel-star-arrowᵢ route₁ route₂)
    non∀-⇒
    non∀-★

sel-∀ν-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (leftOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (leftOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (leftOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ
    (∀ⁱ (tag p₁ ⇛ p₂))
    (ν occ (tag q₁ ⇛ q₂))
sel-∀ν-tag-arrow-tag-arrowᵢ occ =
  sel-∀ν-non∀ᵢ
    occ
    sel-tag-arrow-tag-arrowᵢ
    non∀-★
    non∀-★

sel-ν∀-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (rightOnlyᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (rightOnlyᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (rightOnlyᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ
    (ν occ (tag p₁ ⇛ p₂))
    (∀ⁱ (tag q₁ ⇛ q₂))
sel-ν∀-tag-arrow-tag-arrowᵢ occ =
  sel-ν∀-non∀ᵢ
    occ
    sel-tag-arrow-tag-arrowᵢ
    non∀-★
    non∀-★

sel-νν-arrow-arrow-no-occᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true)
    (occ′ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p₂ q₂ →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p₁ q₁) ≡ false →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p₂ q₂) ≡ false →
  MlbTypeSelectorᵢ
    (ν occ (p₁ ↦ p₂))
    (ν occ′ (q₁ ↦ q₂))
sel-νν-arrow-arrow-no-occᵢ occ occ′ route₁ route₂ no₁ no₂ =
  sel-νν-no-occursᵢ
    occ
    occ′
    (sel-arrow-arrowᵢ route₁ route₂)
    (∨-falseᵢ no₁ no₂)

sel-νν-arrow-star-no-occᵢ :
  ∀ {Γ C₁ C₂ A₁ A₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ A₁ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ A₂ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true)
    (occ′ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p₂ q₂ →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p₁ q₁) ≡ false →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p₂ q₂) ≡ false →
  MlbTypeSelectorᵢ
    (ν occ (p₁ ↦ p₂))
    (ν occ′ (tag q₁ ⇛ q₂))
sel-νν-arrow-star-no-occᵢ occ occ′ route₁ route₂ no₁ no₂ =
  sel-νν-no-occursᵢ
    occ
    occ′
    (sel-arrow-starᵢ route₁ route₂)
    (∨-falseᵢ no₁ no₂)

sel-νν-star-arrow-no-occᵢ :
  ∀ {Γ C₁ C₂ B₁ B₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ B₁ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ B₂ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true)
    (occ′ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p₁ q₁ →
  MlbTypeSelectorᵢ {Γ = neitherᵢ ∷ Γ} p₂ q₂ →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p₁ q₁) ≡ false →
  occurs zero (mlb-typeᵢ {Γ = neitherᵢ ∷ Γ} p₂ q₂) ≡ false →
  MlbTypeSelectorᵢ
    (ν occ (tag p₁ ⇛ p₂))
    (ν occ′ (q₁ ↦ q₂))
sel-νν-star-arrow-no-occᵢ occ occ′ route₁ route₂ no₁ no₂ =
  sel-νν-no-occursᵢ
    occ
    occ′
    (sel-star-arrowᵢ route₁ route₂)
    (∨-falseᵢ no₁ no₂)

sel-νν-tag-arrow-tag-arrowᵢ :
  ∀ {Γ C₁ C₂}
    {p₁ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {p₂ :
      leftChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceLeftCtxᵢ (neitherᵢ ∷ Γ)}
    {q₁ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₁ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    {q₂ :
      rightChoiceᵢ (neitherᵢ ∷ Γ)
        ∣ choiceCommonCtxᵢ (neitherᵢ ∷ Γ)
        ⊢ C₂ ⊑ ★ ⊣ choiceRightCtxᵢ (neitherᵢ ∷ Γ)}
    (occ : occurs zero (C₁ ⇒ C₂) ≡ true)
    (occ′ : occurs zero (C₁ ⇒ C₂) ≡ true) →
  MlbTypeSelectorᵢ
    (ν occ (tag p₁ ⇛ p₂))
    (ν occ′ (tag q₁ ⇛ q₂))
sel-νν-tag-arrow-tag-arrowᵢ occ occ′ =
  sel-νν-no-occursᵢ
    occ
    occ′
    sel-tag-arrow-tag-arrowᵢ
    refl

------------------------------------------------------------------------
-- Canonical-selector coherence target
------------------------------------------------------------------------

-- This is the theorem shape needed by compiled application casts.  It is not
-- derivable from arbitrary maximal lower bounds alone; it should be proved for
-- the canonical maximal-lower-bound selector.

MaximalLowerBoundCoherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  MaximalLowerBoundᵢ Δᴸ A B →
  MaximalLowerBoundᵢ Δᴿ A′ B′ →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  Set
MaximalLowerBoundCoherenceᵢ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} G G′ _ _ =
  Φ ∣ Δᴸ ⊢ lowerᵢ G ⊑ lowerᵢ G′ ⊣ Δᴿ

MaximalLowerBoundCoherenceᶜᵢ :
  ∀ (Φ : ImpCtx)
    {Φᴸ Φᴿ Φᴼ Φᴸ′ Φᴿ′ Φᴼ′ Δᶜ Δᴸ Δᴿ Δᶜ′ Δᴸ′ Δᴿ′ A A′ B B′} →
  MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B →
  MaximalLowerBoundᶜᵢ Φᴸ′ Φᴿ′ Φᴼ′ Δᶜ′ Δᴸ′ Δᴿ′ A′ B′ →
  Set
MaximalLowerBoundCoherenceᶜᵢ Φ {Δᶜ = Δᶜ} {Δᶜ′ = Δᶜ′} G G′ =
  Φ ∣ Δᶜ ⊢ lowerᶜᵢ G ⊑ lowerᶜᵢ G′ ⊣ Δᶜ′

maximal-lower-coherence-transportᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {G : MaximalLowerBoundᵢ Δᴸ A B}
    {G′ : MaximalLowerBoundᵢ Δᴿ A′ B′} →
  lowerᵢ G ≡ C →
  lowerᵢ G′ ≡ C′ →
  Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ →
  MaximalLowerBoundCoherenceᵢ G G′ pA pB
maximal-lower-coherence-transportᵢ refl refl C⊑C′ = C⊑C′

choice-id-maximal-selector-coherence-transportᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δᴸ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)) →
  (route′ :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δᴿ}
      (leftChoice-id-proofᵢ p′)
      (rightChoice-id-proofᵢ q′)) →
  Φ ∣ Δᴸ ⊢
    mlb-typeᵢ
      {Γ = choice-idᵢ Δᴸ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)
    ⊑
    mlb-typeᵢ
      {Γ = choice-idᵢ Δᴿ}
      (leftChoice-id-proofᵢ p′)
      (rightChoice-id-proofᵢ q′)
    ⊣ Δᴿ →
  MaximalLowerBoundCoherenceᵢ
    (proj₁ (choice-id-maximal-selectorᵢ route))
    (proj₁ (choice-id-maximal-selectorᵢ route′))
    pA
    pB
choice-id-maximal-selector-coherence-transportᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ lower⊑lower′ =
  maximal-lower-coherence-transportᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴸ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)}
    {C′ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴿ}
        (leftChoice-id-proofᵢ p′)
        (rightChoice-id-proofᵢ q′)}
    {pA = pA}
    {pB = pB}
    {G = proj₁ (choice-id-maximal-selectorᵢ route)}
    {G′ = proj₁ (choice-id-maximal-selectorᵢ route′)}
    (proj₂ (choice-id-maximal-selectorᵢ route))
    (proj₂ (choice-id-maximal-selectorᵢ route′))
    lower⊑lower′

choice-id-maximal-selector-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δᴸ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)) →
  (route′ :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δᴿ}
      (leftChoice-id-proofᵢ p′)
      (rightChoice-id-proofᵢ q′)) →
  MlbTypeSelectorCoherenceᵢ Φ route route′ →
  MaximalLowerBoundCoherenceᵢ
    (proj₁ (choice-id-maximal-selectorᵢ route))
    (proj₁ (choice-id-maximal-selectorᵢ route′))
    pA
    pB
choice-id-maximal-selector-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ lower⊑lower′ =
  choice-id-maximal-selector-coherence-transportᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = C}
    {C′ = C′}
    {pA = pA}
    {pB = pB}
    {p = p}
    {q = q}
    {p′ = p′}
    {q′ = q′}
    route
    route′
    (subst
      (λ Δᴿ′ → Φ ∣ Δᴸ ⊢ lowerᴸ ⊑ lowerᴿ ⊣ Δᴿ′)
      (choice-id-commonCtxᵢ Δᴿ)
      (subst
        (λ Δᴸ′ →
          Φ ∣ Δᴸ′ ⊢ lowerᴸ ⊑ lowerᴿ
          ⊣ choiceCommonCtxᵢ (choice-idᵢ Δᴿ))
        (choice-id-commonCtxᵢ Δᴸ)
        lower⊑lower′))
  where
    lowerᴸ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴸ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)
    lowerᴿ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴿ}
        (leftChoice-id-proofᵢ p′)
        (rightChoice-id-proofᵢ q′)

maximal-lower-coherence-transportᶜᵢ :
  ∀ {Φ Φᴸ Φᴿ Φᴼ Φᴸ′ Φᴿ′ Φᴼ′
      Δᶜ Δᴸ Δᴿ Δᶜ′ Δᴸ′ Δᴿ′ A A′ B B′ C C′}
    {G : MaximalLowerBoundᶜᵢ Φᴸ Φᴿ Φᴼ Δᶜ Δᴸ Δᴿ A B}
    {G′ : MaximalLowerBoundᶜᵢ Φᴸ′ Φᴿ′ Φᴼ′
      Δᶜ′ Δᴸ′ Δᴿ′ A′ B′} →
  lowerᶜᵢ G ≡ C →
  lowerᶜᵢ G′ ≡ C′ →
  Φ ∣ Δᶜ ⊢ C ⊑ C′ ⊣ Δᶜ′ →
  MaximalLowerBoundCoherenceᶜᵢ Φ G G′
maximal-lower-coherence-transportᶜᵢ refl refl lower⊑lower′ =
  lower⊑lower′

mlb-type-maximal-selector-coherenceᵢ :
  ∀ {Φ Γ Γ′ C C′ A A′ B B′}
    {p : leftChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ A
      ⊣ choiceLeftCtxᵢ Γ}
    {q : rightChoiceᵢ Γ ∣ choiceCommonCtxᵢ Γ ⊢ C ⊑ B
      ⊣ choiceRightCtxᵢ Γ}
    {p′ : leftChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′ ⊢ C′ ⊑ A′
      ⊣ choiceLeftCtxᵢ Γ′}
    {q′ : rightChoiceᵢ Γ′ ∣ choiceCommonCtxᵢ Γ′ ⊢ C′ ⊑ B′
      ⊣ choiceRightCtxᵢ Γ′} →
  (route : MlbTypeSelectorᵢ {Γ = Γ} p q) →
  (route′ : MlbTypeSelectorᵢ {Γ = Γ′} p′ q′) →
  MlbTypeSelectorCoherenceᵢ Φ route route′ →
  MaximalLowerBoundCoherenceᶜᵢ Φ
    (proj₁ (mlb-type-maximal-selectorᵢ route))
    (proj₁ (mlb-type-maximal-selectorᵢ route′))
mlb-type-maximal-selector-coherenceᵢ
    {Φ = Φ} {Γ = Γ} {Γ′ = Γ′}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ lower⊑lower′ =
  maximal-lower-coherence-transportᶜᵢ
    {Φ = Φ}
    {Δᶜ = choiceCommonCtxᵢ Γ}
    {Δᴸ = choiceLeftCtxᵢ Γ}
    {Δᴿ = choiceRightCtxᵢ Γ}
    {Δᶜ′ = choiceCommonCtxᵢ Γ′}
    {Δᴸ′ = choiceLeftCtxᵢ Γ′}
    {Δᴿ′ = choiceRightCtxᵢ Γ′}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = mlb-typeᵢ {Γ = Γ} p q}
    {C′ = mlb-typeᵢ {Γ = Γ′} p′ q′}
    {G = proj₁ (mlb-type-maximal-selectorᵢ route)}
    {G′ = proj₁ (mlb-type-maximal-selectorᵢ route′)}
    (proj₂ (mlb-type-maximal-selectorᵢ route))
    (proj₂ (mlb-type-maximal-selectorᵢ route′))
    lower⊑lower′

canonical-maximal-lower-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (can : CanonicalLowerᵢ Δᴸ A B C) →
  (can′ : CanonicalLowerᵢ Δᴿ A′ B′ C′) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-lower-maximalᵢ can)
    (canonical-lower-maximalᵢ can′)
    pA
    pB
canonical-maximal-lower-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} can can′
  =
  maximal-lower-coherence-transportᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = C}
    {C′ = C′}
    {pA = pA}
    {pB = pB}
    {G = canonical-lower-maximalᵢ can}
    {G′ = canonical-lower-maximalᵢ can′}
    (canonical-lower-maximal-lowerᵢ can)
    (canonical-lower-maximal-lowerᵢ can′)
    (canonical-first-order-coherenceᵢ can can′ pA pB)

mlb-type-choice-id-first-order-maximal-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p :
      leftChoiceᵢ (choice-idᵢ Δᴸ) ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q :
      rightChoiceᵢ (choice-idᵢ Δᴸ) ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ :
      leftChoiceᵢ (choice-idᵢ Δᴿ) ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ :
      rightChoiceᵢ (choice-idᵢ Δᴿ) ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴸ}
      {Δᶜ = Δᴸ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴸ}
      p
      q) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴿ}
      {Δᶜ = Δᴿ}
      {Δᴸ = Δᴿ}
      {Δᴿ = Δᴿ}
      p′
      q′) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-lower-maximalᵢ
      (mlb-type-choice-id-first-order-canonicalᵢ route))
    (canonical-lower-maximalᵢ
      (mlb-type-choice-id-first-order-canonicalᵢ route′))
    pA
    pB
mlb-type-choice-id-first-order-maximal-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ =
  canonical-maximal-lower-coherenceᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = mlb-typeᵢ {Γ = choice-idᵢ Δᴸ} p q}
    {C′ = mlb-typeᵢ {Γ = choice-idᵢ Δᴿ} p′ q′}
    {pA = pA}
    {pB = pB}
    (mlb-type-choice-id-first-order-canonicalᵢ route)
    (mlb-type-choice-id-first-order-canonicalᵢ route′)

mlb-type-from-lower-first-order-maximal-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
    {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴸ}
      {Δᶜ = Δᴸ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴸ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q)) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴿ}
      {Δᶜ = Δᴿ}
      {Δᴸ = Δᴿ}
      {Δᴿ = Δᴿ}
      (leftChoice-id-proofAtᵢ p′)
      (rightChoice-id-proofAtᵢ q′)) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-lower-maximalᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route))
    (canonical-lower-maximalᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route′))
    pA
    pB
mlb-type-from-lower-first-order-maximal-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ =
  canonical-maximal-lower-coherenceᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {C = mlb-type-from-lowerᵢ p q}
    {C′ = mlb-type-from-lowerᵢ p′ q′}
    {pA = pA}
    {pB = pB}
    (mlb-type-from-lower-first-order-canonicalᵢ
      {Δ = Δᴸ}
      {C = C}
      {A = A}
      {B = B}
      {p = p}
      {q = q}
      route)
    (mlb-type-from-lower-first-order-canonicalᵢ
      {Δ = Δᴿ}
      {C = C′}
      {A = A′}
      {B = B′}
      {p = p′}
      {q = q′}
      route′)

canonical-forall-forall-maximal-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  (can : CanonicalLowerᵢ (suc Δᴸ) A B C) →
  (can′ : CanonicalLowerᵢ (suc Δᴿ) A′ B′ C′) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-forall-forall-maximalᵢ can)
    (canonical-forall-forall-maximalᵢ can′)
    (∀ⁱ pA)
    (∀ⁱ pB)
canonical-forall-forall-maximal-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} can can′
  =
  maximal-lower-coherence-transportᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = `∀ A}
    {A′ = `∀ A′}
    {B = `∀ B}
    {B′ = `∀ B′}
    {C = `∀ C}
    {C′ = `∀ C′}
    {pA = ∀ⁱ pA}
    {pB = ∀ⁱ pB}
    {G = canonical-forall-forall-maximalᵢ can}
    {G′ = canonical-forall-forall-maximalᵢ can′}
    (canonical-forall-forall-maximal-lowerᵢ can)
    (canonical-forall-forall-maximal-lowerᵢ can′)
    (canonical-forall-forall-coherence-∀∀ᵢ can can′ pA pB)

canonical-forall-forall-to-first-order-maximal-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (can : CanonicalLowerᵢ (suc Δᴸ) A B C) →
  (can′ : CanonicalLowerᵢ Δᴿ A′ B′ C′) →
  (occA : occurs zero A ≡ true) →
  (occB : occurs zero B ≡ true) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-forall-forall-maximalᵢ can)
    (canonical-lower-maximalᵢ can′)
    (ν occA pA)
    (ν occB pB)
canonical-forall-forall-to-first-order-maximal-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    {pA = pA} {pB = pB} can can′ occA occB
  =
  maximal-lower-coherence-transportᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = `∀ A}
    {A′ = A′}
    {B = `∀ B}
    {B′ = B′}
    {C = `∀ C}
    {C′ = C′}
    {pA = ν occA pA}
    {pB = ν occB pB}
    {G = canonical-forall-forall-maximalᵢ can}
    {G′ = canonical-lower-maximalᵢ can′}
    (canonical-forall-forall-maximal-lowerᵢ can)
    (canonical-lower-maximal-lowerᵢ can′)
    (canonical-forall-lower-coherence-ννᵢ can can′ occA pA pB)

mlb-type-from-lower-∀∀-first-order-maximal-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ A′ ⊣ suc Δᴿ}
    {q′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ B′ ⊣ suc Δᴿ} →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ (suc Δᴸ)}
      {Δᶜ = suc Δᴸ}
      {Δᴸ = suc Δᴸ}
      {Δᴿ = suc Δᴸ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q)) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ (suc Δᴿ)}
      {Δᶜ = suc Δᴿ}
      {Δᴸ = suc Δᴿ}
      {Δᴿ = suc Δᴿ}
      (leftChoice-id-proofAtᵢ p′)
      (rightChoice-id-proofAtᵢ q′)) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-forall-forall-maximalᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route))
    (canonical-forall-forall-maximalᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route′))
    (∀ⁱ pA)
    (∀ⁱ pB)
mlb-type-from-lower-∀∀-first-order-maximal-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {pA = pA} {pB = pB} route route′ =
  canonical-forall-forall-maximal-coherenceᵢ
    {Φ = Φ}
    {Δᴸ = Δᴸ}
    {Δᴿ = Δᴿ}
    {A = A}
    {A′ = A′}
    {B = B}
    {B′ = B′}
    {pA = pA}
    {pB = pB}
    (mlb-type-from-lower-first-order-canonicalᵢ route)
    (mlb-type-from-lower-first-order-canonicalᵢ route′)

mlb-type-from-lower-∀∀-first-order-target-maximal-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (occA : occurs zero A ≡ true) →
  (occB : occurs zero B ≡ true) →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ (suc Δᴸ)}
      {Δᶜ = suc Δᴸ}
      {Δᴸ = suc Δᴸ}
      {Δᴿ = suc Δᴸ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q)) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴿ}
      {Δᶜ = Δᴿ}
      {Δᴸ = Δᴿ}
      {Δᴿ = Δᴿ}
      (leftChoice-id-proofAtᵢ p′)
      (rightChoice-id-proofAtᵢ q′)) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-forall-forall-maximalᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route))
    (canonical-lower-maximalᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route′))
    (ν occA pA)
    (ν occB pB)
mlb-type-from-lower-∀∀-first-order-target-maximal-coherenceᵢ
    {pA = pA} {pB = pB} occA occB route route′ =
  canonical-forall-forall-to-first-order-maximal-coherenceᵢ
    {pA = pA}
    {pB = pB}
    (mlb-type-from-lower-first-order-canonicalᵢ route)
    (mlb-type-from-lower-first-order-canonicalᵢ route′)
    occA
    occB

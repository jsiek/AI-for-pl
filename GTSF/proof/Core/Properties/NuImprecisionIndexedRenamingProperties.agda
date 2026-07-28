module proof.Core.Properties.NuImprecisionIndexedRenamingProperties where

-- File Charter:
--   * Canonical renaming and binder-lifting metatheory for indexed GTSF
--     type imprecision.
--   * Renames both endpoints and imprecision assumptions in lockstep, and
--     derives the `∀`, source-only `ν`, and target-only binder lifts.
--   * Owns only syntax-directed imprecision transport; maximal-lower-bound
--     selection and coherence remain under `proof.EndpointMLB`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc)
open import Data.Nat.Base using (s<s)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
open import ImprecisionWf
open import proof.Core.Properties.ImprecisionProperties using
  ( idᵢ-var-identity
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
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; extNᵗ
  ; occurs-suc-var
  ; occurs-zero-rename-ext
  ; rename-raise-ext
  ; renameᵗ-id
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
no-occurs-base-lowerᵢ occ (ν _ occA p) =
  no-occurs-base-lowerᵢ occA p

no-occurs-var-lower-νctxᵢ :
  ∀ {Φ Δᴸ Δᴿ A X} →
  occurs zero A ≡ true →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ ＇ X ⊣ Δᴿ →
  ⊥
no-occurs-var-lower-νctxᵢ {A = ＇ zero} occ (idˣ x∈ _ _) =
  no-νctx-zero-varᵢ x∈
no-occurs-var-lower-νctxᵢ {A = ＇ suc X} () (idˣ x∈ _ _)
no-occurs-var-lower-νctxᵢ occ (ν _ occA p) =
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
⊑-renameᵗ²ᵢ {ρ = ρ} h hρ hσ
    (ν {A = A} safe occA p) =
  ν (renameNonVar (extᵗ ρ) safe)
    (trans (occurs-zero-rename-ext ρ A) occA)
    (⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ h)
      (TyRenameWf-ext hρ)
      hσ
      p)

⊑-rename-at²ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A A′ B B′} →
  (assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Θᴸ τ) →
  (hσ : TyRenameWf Δᴿ Θᴿ σ) →
  A′ ≡ renameᵗ τ A →
  B′ ≡ renameᵗ σ B →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Θᴸ ⊢ A′ ⊑ B′ ⊣ Θᴿ
⊑-rename-at²ᵢ assm hτ hσ eqA eqB p =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _) (sym eqB)
    (subst (λ T → _ ∣ _ ⊢ T ⊑ renameᵗ _ _ ⊣ _)
      (sym eqA) (⊑-renameᵗ²ᵢ assm hτ hσ p))

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

module proof.LR.Precision where

-- File Charter:
--   * Two-context precision (`LR.Precision`) is contained in
--     `Imprecision`: `forget` maps a derivation of `Φ ⊢ A ⊑ B` to one of
--     `impEnvᶜ Φ ⊢ A ⊑ B′`, where `B′` is `B` embedded into the left
--     context.  Every rule maps to the `Imprecision` rule of the same
--     name; `X ⊑ Y` maps to `X⊑X`.
--   * The converse, for right types that avoid the left-only variables,
--     is what elaboration uses (`proof.LR.Elaboration`).
--   * Also: `Imprecision` is invariant under pointwise-equal
--     environments.

open import Data.Fin using (zero; suc)
open import Data.Nat using () renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Types
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ)
import Imprecision as I
open import LR.Precision

------------------------------------------------------------------------
-- Environment transport for Imprecision
------------------------------------------------------------------------

private
  ext-pointwise : ∀ {Δ} {μ ν : I.ImpEnv Δ} (v : I.VarImp)
    → (∀ X → μ X ≡ ν X)
    → ∀ X → I.extendᵐ v μ X ≡ I.extendᵐ v ν X
  ext-pointwise v eq zero = refl
  ext-pointwise v eq (suc X) = eq X

imp-transport : ∀ {Δ} {μ ν : I.ImpEnv Δ} {A B : Ty Δ}
  → (∀ X → μ X ≡ ν X)
  → μ I.⊢ A ⊑ B → ν I.⊢ A ⊑ B
imp-transport eq I.★⊑★ = I.★⊑★
imp-transport eq I.ι⊑ι = I.ι⊑ι
imp-transport eq I.X⊑X = I.X⊑X
imp-transport eq (I.⇒⊑⇒ p q) = I.⇒⊑⇒ (imp-transport eq p) (imp-transport eq q)
imp-transport eq (I.∀⊑∀ p) = I.∀⊑∀ (imp-transport (ext-pointwise I.X⊑X eq) p)
imp-transport eq (I.⇒⊑★ p q) = I.⇒⊑★ (imp-transport eq p) (imp-transport eq q)
imp-transport eq I.ι⊑★ = I.ι⊑★
imp-transport eq (I.X⊑★ {X = X} e) = I.X⊑★ (trans (sym (eq X)) e)
imp-transport eq (I.∀⊑ Anv z p) =
  I.∀⊑ Anv z (imp-transport (ext-pointwise I.X⊑★ eq) p)
imp-transport eq I.∀★⊑★ = I.∀★⊑★
imp-transport eq (I.∀⊑★ Ans p) =
  I.∀⊑★ Ans (imp-transport (ext-pointwise I.X⊑X eq) p)
imp-transport eq I.bot-elim = I.bot-elim
imp-transport eq I.bot⊑★ = I.bot⊑★

------------------------------------------------------------------------
-- The correspondence and its embedding
------------------------------------------------------------------------

embed : ∀ {Δ Δ′} → Corr Δ Δ′ → Δ′ ⇒ʳ Δ
embed Φ = toRenameᵗ (embedᶜ Φ)

embed-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y}
  → Φ ∋ X ↔ Y → embed Φ Y ≡ X
embed-pair ↔-here = refl
embed-pair (↔-pair x) = cong suc (embed-pair x)
embed-pair (↔-only x) = cong suc (embed-pair x)
embed-pair (↔-dead x) = cong suc (embed-pair x)

impEnv-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
  → Φ ∋ X only → impEnvᶜ Φ X ≡ I.X⊑★
impEnv-only only-here = refl
impEnv-only (only-pair x) = impEnv-only x
impEnv-only (only-only x) = impEnv-only x
impEnv-only (only-dead x) = impEnv-only x

impEnv-pair : ∀ {Δ Δ′} (Φ : Corr Δ Δ′)
  → ∀ X → impEnvᶜ (pair Φ) X ≡ I.extᵐ (impEnvᶜ Φ) X
impEnv-pair Φ zero = refl
impEnv-pair Φ (suc X) = refl

impEnv-only-ext : ∀ {Δ Δ′} (Φ : Corr Δ Δ′)
  → ∀ X → impEnvᶜ (only Φ) X ≡ I.instᵐ (impEnvᶜ Φ) X
impEnv-only-ext Φ zero = refl
impEnv-only-ext Φ (suc X) = refl

impEnv-dead : ∀ {Δ Δ′} (Φ : Corr Δ Δ′)
  → ∀ X → impEnvᶜ (dead Φ) X ≡ I.extᵐ (impEnvᶜ Φ) X
impEnv-dead Φ zero = refl
impEnv-dead Φ (suc X) = refl

embed-keep : ∀ {Δ Δ′} (Φ : Corr Δ Δ′) (B : Ty (sucℕ Δ′))
  → renameᵗ (embed (pair Φ)) B ≡ renameᵗ (extᵗ (embed Φ)) B
embed-keep Φ B = renameᵗ-cong B pointwise
  where
  pointwise : ∀ X → embed (pair Φ) X ≡ extᵗ (embed Φ) X
  pointwise zero = refl
  pointwise (suc X) = refl

------------------------------------------------------------------------
-- Containment
------------------------------------------------------------------------

forget : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A : Ty Δ} {B : Ty Δ′}
  → Φ ⊢ A ⊑ B
  → impEnvᶜ Φ I.⊢ A ⊑ renameᵗ (embed Φ) B
forget ★⊑★ = I.★⊑★
forget ι⊑ι = I.ι⊑ι
forget (X⊑Y x) rewrite embed-pair x = I.X⊑X
forget (⇒⊑⇒ p q) = I.⇒⊑⇒ (forget p) (forget q)
forget {Φ = Φ} {B = `∀ B} (∀⊑∀ p) =
  I.∀⊑∀ (subst (λ T → _ I.⊢ _ ⊑ T) (embed-keep Φ B)
    (imp-transport (impEnv-pair Φ) (forget p)))
forget (⇒⊑★ p q) = I.⇒⊑★ (forget p) (forget q)
forget ι⊑★ = I.ι⊑★
forget (X⊑★ x) = I.X⊑★ (impEnv-only x)
forget {Φ = Φ} {B = B} (∀⊑ Anv z p) =
  I.∀⊑ Anv z (subst (λ T → _ I.⊢ _ ⊑ T)
    (trans (renameᵗ-cong B (λ X → refl))
      (sym (renameᵗ-comp (embed Φ) suc B)))
    (imp-transport (impEnv-only-ext Φ) (forget p)))
forget ∀★⊑★ = I.∀★⊑★
forget {Φ = Φ} (∀⊑★ Ans p) =
  I.∀⊑★ Ans (imp-transport (impEnv-dead Φ) (forget p))
forget bot-elim = I.bot-elim
forget bot⊑★ = I.bot⊑★

------------------------------------------------------------------------
-- The converse
------------------------------------------------------------------------

-- The right type is the embedding of a type B″ of the right context, so
-- it never mentions a left-only variable.  `back` reads an Imprecision
-- derivation as a two-context one, rule by rule.  Its structural clauses
-- use the equation only through projections, so they compute on any
-- equation proof.

pair-from-embed : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y}
  → embed Φ Y ≡ X → Φ ∋ X ↔ Y
pair-from-embed {Φ = pair Φ} {Y = zero} refl = ↔-here
pair-from-embed {Φ = pair Φ} {Y = suc Y} refl = ↔-pair (pair-from-embed refl)
pair-from-embed {Φ = only Φ} refl = ↔-only (pair-from-embed refl)
pair-from-embed {Φ = dead Φ} refl = ↔-dead (pair-from-embed refl)

only-from-env : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
  → impEnvᶜ Φ X ≡ I.X⊑★ → Φ ∋ X only
only-from-env {Φ = pair Φ} {X = zero} ()
only-from-env {Φ = pair Φ} {X = suc X} e = only-pair (only-from-env e)
only-from-env {Φ = only Φ} {X = zero} e = only-here
only-from-env {Φ = only Φ} {X = suc X} e = only-only (only-from-env e)
only-from-env {Φ = dead Φ} {X = zero} ()
only-from-env {Φ = dead Φ} {X = suc X} e = only-dead (only-from-env e)

⇒-inj₁ : ∀ {Δ} {A B A′ B′ : Ty Δ} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
⇒-inj₁ refl = refl

⇒-inj₂ : ∀ {Δ} {A B A′ B′ : Ty Δ} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
⇒-inj₂ refl = refl

var-inj : ∀ {Δ} {X Y : TyVar Δ} → _≡_ {A = Ty Δ} (＇ X) (＇ Y) → X ≡ Y
var-inj refl = refl

∀-inj : ∀ {Δ} {A B : Ty (sucℕ Δ)} → `∀ A ≡ `∀ B → A ≡ B
∀-inj refl = refl

-- equations for the embedding under binders
embed-under-pair : ∀ {Δ Δ′} (Φ : Corr Δ Δ′) {B : Ty (sucℕ Δ)}
    (B″ : Ty (sucℕ Δ′))
  → `∀ B ≡ renameᵗ (embed Φ) (`∀ B″)
  → B ≡ renameᵗ (embed (pair Φ)) B″
embed-under-pair Φ B″ eq = trans (∀-inj eq) (sym (embed-keep Φ B″))

embed-under-only : ∀ {Δ Δ′} (Φ : Corr Δ Δ′) {B : Ty Δ} (B″ : Ty Δ′)
  → B ≡ renameᵗ (embed Φ) B″
  → ⇑ᵗ B ≡ renameᵗ (embed (only Φ)) B″
embed-under-only Φ B″ eq =
  trans (cong ⇑ᵗ eq)
    (trans (renameᵗ-comp (embed Φ) suc B″)
      (renameᵗ-cong B″ (λ X → refl)))

env-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
  → (∀ X → μ X ≡ impEnvᶜ Φ X)
  → ∀ X → I.extᵐ μ X ≡ impEnvᶜ (pair Φ) X
env-pair eqμ zero = refl
env-pair eqμ (suc X) = eqμ X

env-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
  → (∀ X → μ X ≡ impEnvᶜ Φ X)
  → ∀ X → I.instᵐ μ X ≡ impEnvᶜ (only Φ) X
env-only eqμ zero = refl
env-only eqμ (suc X) = eqμ X

env-dead : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
  → (∀ X → μ X ≡ impEnvᶜ Φ X)
  → ∀ X → I.extᵐ μ X ≡ impEnvᶜ (dead Φ) X
env-dead eqμ zero = refl
env-dead eqμ (suc X) = eqμ X

back : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → (∀ X → μ X ≡ impEnvᶜ Φ X)
  → μ I.⊢ A ⊑ B
  → (B″ : Ty Δ′)
  → B ≡ renameᵗ (embed Φ) B″
  → Φ ⊢ A ⊑ B″
back eqμ I.★⊑★ ★ eq = ★⊑★
back eqμ I.★⊑★ (＇ Y) ()
back eqμ I.★⊑★ (‵ ι) ()
back eqμ I.★⊑★ (B₁ ⇒ B₂) ()
back eqμ I.★⊑★ (`∀ B₀) ()
back eqμ I.ι⊑ι (‵ ι) refl = ι⊑ι
back eqμ I.ι⊑ι (＇ Y) ()
back eqμ I.ι⊑ι ★ ()
back eqμ I.ι⊑ι (B₁ ⇒ B₂) ()
back eqμ I.ι⊑ι (`∀ B₀) ()
back eqμ I.X⊑X (＇ Y) eq = X⊑Y (pair-from-embed (sym (var-inj eq)))
back eqμ I.X⊑X (‵ ι) ()
back eqμ I.X⊑X ★ ()
back eqμ I.X⊑X (B₁ ⇒ B₂) ()
back eqμ I.X⊑X (`∀ B₀) ()
back eqμ (I.⇒⊑⇒ p q) (B₁ ⇒ B₂) eq =
  ⇒⊑⇒ (back eqμ p B₁ (⇒-inj₁ eq)) (back eqμ q B₂ (⇒-inj₂ eq))
back eqμ (I.⇒⊑⇒ p q) (＇ Y) ()
back eqμ (I.⇒⊑⇒ p q) (‵ ι) ()
back eqμ (I.⇒⊑⇒ p q) ★ ()
back eqμ (I.⇒⊑⇒ p q) (`∀ B₀) ()
back {Φ = Φ} eqμ (I.∀⊑∀ p) (`∀ B₀) eq =
  ∀⊑∀ (back (env-pair eqμ) p B₀ (embed-under-pair Φ B₀ eq))
back eqμ (I.∀⊑∀ p) (＇ Y) ()
back eqμ (I.∀⊑∀ p) (‵ ι) ()
back eqμ (I.∀⊑∀ p) ★ ()
back eqμ (I.∀⊑∀ p) (B₁ ⇒ B₂) ()
back eqμ (I.⇒⊑★ p q) ★ eq = ⇒⊑★ (back eqμ p ★ refl) (back eqμ q ★ refl)
back eqμ (I.⇒⊑★ p q) (＇ Y) ()
back eqμ (I.⇒⊑★ p q) (‵ ι) ()
back eqμ (I.⇒⊑★ p q) (B₁ ⇒ B₂) ()
back eqμ (I.⇒⊑★ p q) (`∀ B₀) ()
back eqμ I.ι⊑★ ★ eq = ι⊑★
back eqμ I.ι⊑★ (＇ Y) ()
back eqμ I.ι⊑★ (‵ ι) ()
back eqμ I.ι⊑★ (B₁ ⇒ B₂) ()
back eqμ I.ι⊑★ (`∀ B₀) ()
back eqμ (I.X⊑★ {X = X} e) ★ eq = X⊑★ (only-from-env (trans (sym (eqμ X)) e))
back eqμ (I.X⊑★ e) (＇ Y) ()
back eqμ (I.X⊑★ e) (‵ ι) ()
back eqμ (I.X⊑★ e) (B₁ ⇒ B₂) ()
back eqμ (I.X⊑★ e) (`∀ B₀) ()
back {Φ = Φ} eqμ (I.∀⊑ Anv z p) B″ eq =
  ∀⊑ Anv z (back (env-only eqμ) p B″ (embed-under-only Φ B″ eq))
back eqμ I.∀★⊑★ ★ eq = ∀★⊑★
back eqμ I.∀★⊑★ (＇ Y) ()
back eqμ I.∀★⊑★ (‵ ι) ()
back eqμ I.∀★⊑★ (B₁ ⇒ B₂) ()
back eqμ I.∀★⊑★ (`∀ B₀) ()
back eqμ (I.∀⊑★ Ans p) ★ eq = ∀⊑★ Ans (back (env-dead eqμ) p ★ refl)
back eqμ (I.∀⊑★ Ans p) (＇ Y) ()
back eqμ (I.∀⊑★ Ans p) (‵ ι) ()
back eqμ (I.∀⊑★ Ans p) (B₁ ⇒ B₂) ()
back eqμ (I.∀⊑★ Ans p) (`∀ B₀) ()
back eqμ I.bot-elim (`∀ ★) eq = bot-elim
back eqμ I.bot-elim (`∀ (＇ Y)) ()
back eqμ I.bot-elim (`∀ (‵ ι)) ()
back eqμ I.bot-elim (`∀ (B₁ ⇒ B₂)) ()
back eqμ I.bot-elim (`∀ (`∀ B₀)) ()
back eqμ I.bot-elim (＇ Y) ()
back eqμ I.bot-elim (‵ ι) ()
back eqμ I.bot-elim ★ ()
back eqμ I.bot-elim (B₁ ⇒ B₂) ()
back eqμ I.bot⊑★ ★ eq = bot⊑★
back eqμ I.bot⊑★ (＇ Y) ()
back eqμ I.bot⊑★ (‵ ι) ()
back eqμ I.bot⊑★ (B₁ ⇒ B₂) ()
back eqμ I.bot⊑★ (`∀ B₀) ()

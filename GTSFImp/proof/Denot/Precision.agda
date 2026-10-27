module proof.Denot.Precision where

-- File Charter:
--   * Two-context precision (`Denot.Precision`) is contained in
--     `Imprecision`: `forget` maps a derivation of `Φ ⊢ A ⊑ B` to one of
--     `impEnvᶜ Φ ⊢ A ⊑ B′`, where `B′` is `B` embedded into the left
--     context.  Every rule maps to the `Imprecision` rule of the same
--     name; `X ⊑ Y` maps to `X⊑X`.
--   * The converse, for right types that avoid the left-only variables,
--     is what elaboration uses (`proof.Denot.Elaboration`).
--   * Also: `Imprecision` is invariant under pointwise-equal
--     environments.

open import Data.Fin using (zero; suc)
open import Data.Nat using () renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Types
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ)
import Imprecision as I
open import Denot.Precision

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

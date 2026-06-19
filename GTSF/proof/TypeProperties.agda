module proof.TypeProperties where

-- File Charter:
--   * Proof-only metatheory for the redesigned GTSF type layer.
--   * Establishes congruence/identity laws and well-formedness preservation
--     for telescope-aware renaming and substitution.
--   * Dense-context arithmetic lemmas from the previous design are intentionally
--     absent: regular type variables and seals now live in separate de Bruijn
--     namespaces inside one telescope.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (_∨_)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (_≟_; suc-injective)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types

------------------------------------------------------------------------
-- Congruence and identity for raw renaming/substitution
------------------------------------------------------------------------

rename-cong :
  ∀ {ρ ρ′ : Renameᵗ} {σ σ′ : Renameˢ} →
  (∀ X → ρ X ≡ ρ′ X) →
  (∀ α → σ α ≡ σ′ α) →
  (A : Ty) →
  rename ρ σ A ≡ rename ρ′ σ′ A
rename-cong eqᵗ eqˢ (`X X) = cong `X_ (eqᵗ X)
rename-cong eqᵗ eqˢ (`α α) = cong `α_ (eqˢ α)
rename-cong eqᵗ eqˢ (‵ ι) = refl
rename-cong eqᵗ eqˢ ★ = refl
rename-cong eqᵗ eqˢ (A ⇒ B) =
  cong₂ _⇒_ (rename-cong eqᵗ eqˢ A) (rename-cong eqᵗ eqˢ B)
rename-cong eqᵗ eqˢ (`∀ A) =
  cong `∀
    (rename-cong
      (λ { zero → refl
         ; (suc X) → cong suc (eqᵗ X)})
      eqˢ
      A)

subst-cong :
  ∀ {σ σ′ : Substᵗ} {τ τ′ : Substˢ} →
  (∀ X → σ X ≡ σ′ X) →
  (∀ α → τ α ≡ τ′ α) →
  (A : Ty) →
  subst σ τ A ≡ subst σ′ τ′ A
subst-cong eqᵗ eqˢ (`X X) = eqᵗ X
subst-cong eqᵗ eqˢ (`α α) = eqˢ α
subst-cong eqᵗ eqˢ (‵ ι) = refl
subst-cong eqᵗ eqˢ ★ = refl
subst-cong eqᵗ eqˢ (A ⇒ B) =
  cong₂ _⇒_ (subst-cong eqᵗ eqˢ A) (subst-cong eqᵗ eqˢ B)
subst-cong eqᵗ eqˢ (`∀ A) =
  cong `∀
    (subst-cong
      (λ { zero → refl
         ; (suc X) → cong ⇑ᵗ (eqᵗ X)})
      (λ α → cong ⇑ᵗ (eqˢ α))
      A)

rename-id :
  ∀ A →
  rename idᵗ idˢ A ≡ A
rename-id (`X X) = refl
rename-id (`α α) = refl
rename-id (‵ ι) = refl
rename-id ★ = refl
rename-id (A ⇒ B) = cong₂ _⇒_ (rename-id A) (rename-id B)
rename-id (`∀ A) =
  cong `∀
    (trans
      (rename-cong
        (λ { zero → refl
           ; (suc X) → refl})
        (λ α → refl)
        A)
      (rename-id A))

subst-id :
  ∀ A →
  subst `X_ `α_ A ≡ A
subst-id (`X X) = refl
subst-id (`α α) = refl
subst-id (‵ ι) = refl
subst-id ★ = refl
subst-id (A ⇒ B) = cong₂ _⇒_ (subst-id A) (subst-id B)
subst-id (`∀ A) =
  cong `∀
    (trans
      (subst-cong
        (λ { zero → refl
           ; (suc X) → refl})
        (λ α → refl)
        A)
      (subst-id A))

rename-compose :
  ∀ ρ ρ′ σ σ′ A →
  rename ρ′ σ′ (rename ρ σ A) ≡
  rename (λ X → ρ′ (ρ X)) (λ α → σ′ (σ α)) A
rename-compose ρ ρ′ σ σ′ (`X X) = refl
rename-compose ρ ρ′ σ σ′ (`α α) = refl
rename-compose ρ ρ′ σ σ′ (‵ ι) = refl
rename-compose ρ ρ′ σ σ′ ★ = refl
rename-compose ρ ρ′ σ σ′ (A ⇒ B) =
  cong₂ _⇒_ (rename-compose ρ ρ′ σ σ′ A)
             (rename-compose ρ ρ′ σ σ′ B)
rename-compose ρ ρ′ σ σ′ (`∀ A) =
  cong `∀
    (trans
      (rename-compose (extᵗ ρ) (extᵗ ρ′) σ σ′ A)
      (rename-cong
        (λ { zero → refl
           ; (suc X) → refl})
        (λ α → refl)
        A))

rename-shiftᵗ-comm :
  ∀ ρ σ A →
  ⇑ᵗ (rename ρ σ A) ≡ rename (extᵗ ρ) σ (⇑ᵗ A)
rename-shiftᵗ-comm ρ σ A =
  trans
    (rename-compose ρ suc σ idˢ A)
    (trans
      (rename-cong (λ X → refl) (λ α → refl) A)
      (sym (rename-compose suc (extᵗ ρ) idˢ σ A)))

rename-shiftˢ-comm :
  ∀ ρ σ A →
  ⇑ˢ (rename ρ σ A) ≡ rename ρ (extˢ σ) (⇑ˢ A)
rename-shiftˢ-comm ρ σ A =
  trans
    (rename-compose ρ idᵗ σ suc A)
    (trans
      (rename-cong (λ X → refl) (λ α → refl) A)
      (sym (rename-compose idᵗ ρ suc (extˢ σ) A)))

rename-drop-shiftᵗ :
  ∀ A →
  (⇑ᵗ A) [ zero ]ᴿ ≡ A
rename-drop-shiftᵗ A =
  trans
    (rename-compose suc (singleRenameᵗ zero) idˢ idˢ A)
    (trans (rename-cong (λ X → refl) (λ α → refl) A) (rename-id A))

protectᵗ : TyVar → Renameᵗ → Renameᵗ
protectᵗ zero ρ = extᵗ ρ
protectᵗ (suc X) ρ = extᵗ (protectᵗ X ρ)

protectᵗ-self :
  ∀ X ρ →
  protectᵗ X ρ X ≡ X
protectᵗ-self zero ρ = refl
protectᵗ-self (suc X) ρ = cong suc (protectᵗ-self X ρ)

protectᵗ-hit :
  ∀ X ρ Y →
  X ≡ Y →
  X ≡ protectᵗ X ρ Y
protectᵗ-hit X ρ .X refl = sym (protectᵗ-self X ρ)

protectᵗ-miss :
  ∀ X ρ Y →
  X ≢ Y →
  X ≢ protectᵗ X ρ Y
protectᵗ-miss zero ρ zero X≢Y eq = X≢Y refl
protectᵗ-miss zero ρ (suc Y) X≢Y ()
protectᵗ-miss (suc X) ρ zero X≢Y ()
protectᵗ-miss (suc X) ρ (suc Y) X≢Y eq =
  protectᵗ-miss X ρ Y (λ X≡Y → X≢Y (cong suc X≡Y)) (suc-injective eq)

occursᵗ-var-protect :
  ∀ X ρ Y →
  occursᵗ X (`X (protectᵗ X ρ Y)) ≡ occursᵗ X (`X Y)
occursᵗ-var-protect X ρ Y with X ≟ protectᵗ X ρ Y | X ≟ Y
occursᵗ-var-protect X ρ Y | yes eq-hit | yes eq = refl
occursᵗ-var-protect X ρ Y | yes eq-hit | no neq =
  ⊥-elim (protectᵗ-miss X ρ Y neq eq-hit)
occursᵗ-var-protect X ρ Y | no neq-hit | yes eq =
  ⊥-elim (neq-hit (protectᵗ-hit X ρ Y eq))
occursᵗ-var-protect X ρ Y | no neq-hit | no neq = refl

occursᵗ-protect :
  ∀ X ρ σ A →
  occursᵗ X (rename (protectᵗ X ρ) σ A) ≡ occursᵗ X A
occursᵗ-protect X ρ σ (`X Y) = occursᵗ-var-protect X ρ Y
occursᵗ-protect X ρ σ (`α α) = refl
occursᵗ-protect X ρ σ (‵ ι) = refl
occursᵗ-protect X ρ σ ★ = refl
occursᵗ-protect X ρ σ (A ⇒ B) =
  cong₂ _∨_ (occursᵗ-protect X ρ σ A) (occursᵗ-protect X ρ σ B)
occursᵗ-protect X ρ σ (`∀ A) = occursᵗ-protect (suc X) ρ σ A

occursᵗ-zero-rename-ext :
  ∀ ρ σ A →
  occursᵗ zero (rename (extᵗ ρ) σ A) ≡ occursᵗ zero A
occursᵗ-zero-rename-ext ρ σ A = occursᵗ-protect zero ρ σ A

------------------------------------------------------------------------
-- Well-typed renamings
------------------------------------------------------------------------

idᵗ-renaming :
  ∀ {Γ} →
  TyRenaming Γ Γ
idᵗ-renaming = ty-ren idᵗ (λ h → h)

idˢ-renaming :
  ∀ {Γ} →
  SealRenaming (idᵗ-renaming {Γ})
idˢ-renaming =
  seal-ren idˢ (λ h → h) ren-α
  where
    ren-α :
      ∀ {Γ α A} →
      Γ ∋α α ⦂ A →
      Γ ∋α α ⦂ rename idᵗ idˢ A
    ren-α {Γ} {α} {A} h =
      Eq.subst (λ B → Γ ∋α α ⦂ B) (sym (rename-id A)) h

shiftᵗ-ty-renaming :
  ∀ {Γ} →
  TyRenaming Γ (tyᵉ ∷ Γ)
shiftᵗ-ty-renaming = ty-ren suc Sᵗ-ty

shiftᵗ-seal-renaming :
  ∀ {Γ} →
  SealRenaming (shiftᵗ-ty-renaming {Γ})
shiftᵗ-seal-renaming = seal-ren idˢ Sˢ-ty Sα-ty

shiftˢ-ty-renaming :
  ∀ {Γ A} →
  TyRenaming Γ (sealᵉ A ∷ Γ)
shiftˢ-ty-renaming = ty-ren idᵗ Sᵗ-seal

shiftˢ-seal-renaming :
  ∀ {Γ A} →
  SealRenaming (shiftˢ-ty-renaming {Γ} {A})
shiftˢ-seal-renaming = seal-ren suc Sˢ-seal Sα-seal

shiftˣ-ty-renaming :
  ∀ {Γ A} →
  TyRenaming Γ (termᵉ A ∷ Γ)
shiftˣ-ty-renaming = ty-ren idᵗ Sᵗ-term

shiftˣ-seal-renaming :
  ∀ {Γ A} →
  SealRenaming (shiftˣ-ty-renaming {Γ} {A})
shiftˣ-seal-renaming {Γ} {A} =
  seal-ren idˢ Sˢ-term ren-α
  where
    ren-α :
      ∀ {α B} →
      Γ ∋α α ⦂ B →
      (termᵉ A ∷ Γ) ∋α α ⦂ rename idᵗ idˢ B
    ren-α {α} {B} h =
      Eq.subst (λ C → (termᵉ A ∷ Γ) ∋α α ⦂ C)
        (sym (rename-id B))
        (Sα-term h)

extᵗ-ty-renaming :
  ∀ {Γ Γ′} →
  TyRenaming Γ Γ′ →
  TyRenaming (tyᵉ ∷ Γ) (tyᵉ ∷ Γ′)
extᵗ-ty-renaming ρ =
  ty-ren
    (extᵗ (renᵗ ρ))
    ren-ty
  where
    ren-ty : ∀ {X} → (tyᵉ ∷ _) ∋ᵗ X → (tyᵉ ∷ _) ∋ᵗ extᵗ (renᵗ ρ) X
    ren-ty Zᵗ = Zᵗ
    ren-ty (Sᵗ-ty h) = Sᵗ-ty (renᵗ-wf ρ h)

extᵗ-seal-renaming :
  ∀ {Γ Γ′} {ρ : TyRenaming Γ Γ′} →
  SealRenaming ρ →
  SealRenaming (extᵗ-ty-renaming ρ)
extᵗ-seal-renaming {ρ = ρ} τ =
  seal-ren
    (renˢ τ)
    ren-seal
    ren-α
  where
    ren-seal : ∀ {α} → (tyᵉ ∷ _) ∋ˢ α → (tyᵉ ∷ _) ∋ˢ renˢ τ α
    ren-seal (Sˢ-ty h) = Sˢ-ty (renˢ-wf τ h)

    ren-α :
      ∀ {α A} →
      (tyᵉ ∷ _) ∋α α ⦂ A →
      (tyᵉ ∷ _) ∋α renˢ τ α ⦂ rename (extᵗ (renᵗ ρ)) (renˢ τ) A
    ren-α {α} (Sα-ty {A = A} h) =
      Eq.subst
        (λ B → (tyᵉ ∷ _) ∋α renˢ τ α ⦂ B)
        (rename-shiftᵗ-comm (renᵗ ρ) (renˢ τ) A)
        (Sα-ty (renα-wf τ h))

extˢ-ty-renaming :
  ∀ {Γ Γ′ A} →
  (ρ : TyRenaming Γ Γ′) →
  (τ : SealRenaming ρ) →
  TyRenaming (sealᵉ A ∷ Γ) (sealᵉ (renameʳ ρ τ A) ∷ Γ′)
extˢ-ty-renaming ρ τ =
  ty-ren
    (renᵗ ρ)
    ren-ty
  where
    ren-ty : ∀ {X} → (sealᵉ _ ∷ _) ∋ᵗ X → (sealᵉ _ ∷ _) ∋ᵗ renᵗ ρ X
    ren-ty (Sᵗ-seal h) = Sᵗ-seal (renᵗ-wf ρ h)

extˢ-seal-renaming :
  ∀ {Γ Γ′ A} →
  (ρ : TyRenaming Γ Γ′) →
  (τ : SealRenaming ρ) →
  SealRenaming (extˢ-ty-renaming ρ τ)
extˢ-seal-renaming {Γ} {Γ′} {A} ρ τ =
  seal-ren
    (extˢ (renˢ τ))
    ren-seal
    ren-α
  where
    ren-seal :
      ∀ {α} →
      (sealᵉ A ∷ Γ) ∋ˢ α →
      (sealᵉ (renameʳ ρ τ A) ∷ Γ′) ∋ˢ extˢ (renˢ τ) α
    ren-seal Zˢ = Zˢ
    ren-seal (Sˢ-seal h) = Sˢ-seal (renˢ-wf τ h)

    ren-α :
      ∀ {α B} →
      (sealᵉ A ∷ Γ) ∋α α ⦂ B →
      (sealᵉ (renameʳ ρ τ A) ∷ Γ′) ∋α extˢ (renˢ τ) α
        ⦂ rename (renᵗ ρ) (extˢ (renˢ τ)) B
    ren-α Zα =
      Eq.subst
        (λ B → (sealᵉ (renameʳ ρ τ A) ∷ Γ′) ∋α zero ⦂ B)
        (rename-shiftˢ-comm (renᵗ ρ) (renˢ τ) A)
        Zα
    ren-α {suc α} (Sα-seal {A = B} h) =
      Eq.subst
        (λ C → (sealᵉ (renameʳ ρ τ A) ∷ Γ′) ∋α suc (renˢ τ α) ⦂ C)
        (rename-shiftˢ-comm (renᵗ ρ) (renˢ τ) B)
        (Sα-seal (renα-wf τ h))

extˣ-ty-renaming :
  ∀ {Γ Γ′ A} →
  (ρ : TyRenaming Γ Γ′) →
  (τ : SealRenaming ρ) →
  TyRenaming (termᵉ A ∷ Γ) (termᵉ (renameʳ ρ τ A) ∷ Γ′)
extˣ-ty-renaming ρ τ =
  ty-ren
    (renᵗ ρ)
    ren-ty
  where
    ren-ty : ∀ {X} → (termᵉ _ ∷ _) ∋ᵗ X → (termᵉ _ ∷ _) ∋ᵗ renᵗ ρ X
    ren-ty (Sᵗ-term h) = Sᵗ-term (renᵗ-wf ρ h)

extˣ-seal-renaming :
  ∀ {Γ Γ′ A} →
  (ρ : TyRenaming Γ Γ′) →
  (τ : SealRenaming ρ) →
  SealRenaming (extˣ-ty-renaming ρ τ)
extˣ-seal-renaming {Γ} {Γ′} {A} ρ τ =
  seal-ren
    (renˢ τ)
    ren-seal
    ren-α
  where
    ren-seal :
      ∀ {α} →
      (termᵉ A ∷ Γ) ∋ˢ α →
      (termᵉ (renameʳ ρ τ A) ∷ Γ′) ∋ˢ renˢ τ α
    ren-seal (Sˢ-term h) = Sˢ-term (renˢ-wf τ h)

    ren-α :
      ∀ {α B} →
      (termᵉ A ∷ Γ) ∋α α ⦂ B →
      (termᵉ (renameʳ ρ τ A) ∷ Γ′) ∋α renˢ τ α
        ⦂ rename (renᵗ ρ) (renˢ τ) B
    ren-α (Sα-term h) = Sα-term (renα-wf τ h)

rename-preserves-WfTy :
  ∀ {Γ Γ′ A} →
  (ρ : TyRenaming Γ Γ′) →
  (τ : SealRenaming ρ) →
  WfTy Γ A →
  WfTy Γ′ (renameʳ ρ τ A)
rename-preserves-WfTy ρ τ (wfX h) = wfX (renᵗ-wf ρ h)
rename-preserves-WfTy ρ τ (wfα h) = wfα (renˢ-wf τ h)
rename-preserves-WfTy ρ τ wfBase = wfBase
rename-preserves-WfTy ρ τ wf★ = wf★
rename-preserves-WfTy ρ τ (wf⇒ hA hB) =
  wf⇒ (rename-preserves-WfTy ρ τ hA)
      (rename-preserves-WfTy ρ τ hB)
rename-preserves-WfTy ρ τ (wf∀ hA) =
  wf∀
    (rename-preserves-WfTy
      (extᵗ-ty-renaming ρ)
      (extᵗ-seal-renaming τ)
      hA)

rename-ground :
  ∀ ρ σ {G} →
  Ground G →
  Ground (rename ρ σ G)
rename-ground ρ σ (`α α) = `α (σ α)
rename-ground ρ σ (‵ ι) = ‵ ι
rename-ground ρ σ ★⇒★ = ★⇒★

rename-atom :
  ∀ ρ σ {A} →
  Atom A →
  Atom (rename ρ σ A)
rename-atom ρ σ (`X X) = `X (ρ X)
rename-atom ρ σ (`α α) = `α (σ α)
rename-atom ρ σ (‵ ι) = ‵ ι
rename-atom ρ σ ★ = ★

rename-non∀ :
  ∀ ρ σ {A} →
  Non∀ A →
  Non∀ (rename ρ σ A)
rename-non∀ ρ σ non∀-X = non∀-X
rename-non∀ ρ σ non∀-α = non∀-α
rename-non∀ ρ σ non∀-‵ = non∀-‵
rename-non∀ ρ σ non∀-★ = non∀-★
rename-non∀ ρ σ non∀-⇒ = non∀-⇒

------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

renaming-ty-substitution :
  ∀ {Γ Γ′} →
  TyRenaming Γ Γ′ →
  TySubstitution Γ Γ′
renaming-ty-substitution ρ =
  ty-sub
    (λ X → `X (renᵗ ρ X))
    (λ h → wfX (renᵗ-wf ρ h))

renaming-seal-substitution :
  ∀ {Γ Γ′} {ρ : TyRenaming Γ Γ′} →
  SealRenaming ρ →
  SealSubstitution Γ Γ′
renaming-seal-substitution τ =
  seal-sub
    (λ α → `α (renˢ τ α))
    (λ h → wfα (renˢ-wf τ h))

extᵗ-ty-substitution :
  ∀ {Γ Γ′} →
  TySubstitution Γ Γ′ →
  TySubstitution (tyᵉ ∷ Γ) (tyᵉ ∷ Γ′)
extᵗ-ty-substitution σ =
  ty-sub
    (extSubstᵗ (subᵗ σ))
    sub-ty
  where
    sub-ty : ∀ {X} → (tyᵉ ∷ _) ∋ᵗ X → WfTy (tyᵉ ∷ _) (extSubstᵗ (subᵗ σ) X)
    sub-ty Zᵗ = wfX Zᵗ
    sub-ty (Sᵗ-ty h) =
      rename-preserves-WfTy shiftᵗ-ty-renaming shiftᵗ-seal-renaming
        (subᵗ-wf σ h)

extᵗ-seal-substitution :
  ∀ {Γ Γ′} →
  SealSubstitution Γ Γ′ →
  SealSubstitution (tyᵉ ∷ Γ) (tyᵉ ∷ Γ′)
extᵗ-seal-substitution τ =
  seal-sub
    (liftSubstˢOverTy (subˢ τ))
    sub-seal
  where
    sub-seal :
      ∀ {α} → (tyᵉ ∷ _) ∋ˢ α → WfTy (tyᵉ ∷ _) (liftSubstˢOverTy (subˢ τ) α)
    sub-seal (Sˢ-ty h) =
      rename-preserves-WfTy shiftᵗ-ty-renaming shiftᵗ-seal-renaming
        (subˢ-wf τ h)

extˢ-ty-substitution :
  ∀ {Γ Γ′ A} →
  (σ : TySubstitution Γ Γ′) →
  (τ : SealSubstitution Γ Γ′) →
  TySubstitution (sealᵉ A ∷ Γ) (sealᵉ (substˢᵘᵇ σ τ A) ∷ Γ′)
extˢ-ty-substitution σ τ =
  ty-sub
    (λ X → ⇑ˢ (subᵗ σ X))
    sub-ty
  where
    sub-ty :
      ∀ {X} → (sealᵉ _ ∷ _) ∋ᵗ X → WfTy (sealᵉ _ ∷ _) (⇑ˢ (subᵗ σ X))
    sub-ty (Sᵗ-seal h) =
      rename-preserves-WfTy shiftˢ-ty-renaming shiftˢ-seal-renaming
        (subᵗ-wf σ h)

extˢ-seal-substitution :
  ∀ {Γ Γ′ A} →
  (σ : TySubstitution Γ Γ′) →
  (τ : SealSubstitution Γ Γ′) →
  SealSubstitution (sealᵉ A ∷ Γ) (sealᵉ (substˢᵘᵇ σ τ A) ∷ Γ′)
extˢ-seal-substitution σ τ =
  seal-sub
    (extSubstˢ (subˢ τ))
    sub-seal
  where
    sub-seal :
      ∀ {α} → (sealᵉ _ ∷ _) ∋ˢ α → WfTy (sealᵉ _ ∷ _) (extSubstˢ (subˢ τ) α)
    sub-seal Zˢ = wfα Zˢ
    sub-seal (Sˢ-seal h) =
      rename-preserves-WfTy shiftˢ-ty-renaming shiftˢ-seal-renaming
        (subˢ-wf τ h)

subst-preserves-WfTy :
  ∀ {Γ Γ′ A} →
  (σ : TySubstitution Γ Γ′) →
  (τ : SealSubstitution Γ Γ′) →
  WfTy Γ A →
  WfTy Γ′ (substˢᵘᵇ σ τ A)
subst-preserves-WfTy σ τ (wfX h) = subᵗ-wf σ h
subst-preserves-WfTy σ τ (wfα h) = subˢ-wf τ h
subst-preserves-WfTy σ τ wfBase = wfBase
subst-preserves-WfTy σ τ wf★ = wf★
subst-preserves-WfTy σ τ (wf⇒ hA hB) =
  wf⇒ (subst-preserves-WfTy σ τ hA)
      (subst-preserves-WfTy σ τ hB)
subst-preserves-WfTy σ τ (wf∀ hA) =
  wf∀
    (subst-preserves-WfTy
      (extᵗ-ty-substitution σ)
      (extᵗ-seal-substitution τ)
      hA)

singleTySubstitution :
  ∀ {Γ B} →
  WfTy Γ B →
  TySubstitution (tyᵉ ∷ Γ) Γ
singleTySubstitution hB =
  ty-sub
    (singleTyEnv _)
    sub-ty
  where
    sub-ty : ∀ {X} → (tyᵉ ∷ _) ∋ᵗ X → WfTy _ (singleTyEnv _ X)
    sub-ty Zᵗ = hB
    sub-ty (Sᵗ-ty h) = wfX h

dropTySealSubstitution :
  ∀ {Γ} →
  SealSubstitution (tyᵉ ∷ Γ) Γ
dropTySealSubstitution =
  seal-sub
    `α_
    sub-seal
  where
    sub-seal : ∀ {α} → (tyᵉ ∷ _) ∋ˢ α → WfTy _ (`α α)
    sub-seal (Sˢ-ty h) = wfα h

dropSealTySubstitution :
  ∀ {Γ A} →
  TySubstitution (sealᵉ A ∷ Γ) Γ
dropSealTySubstitution =
  ty-sub
    `X_
    sub-ty
  where
    sub-ty : ∀ {X} → (sealᵉ _ ∷ _) ∋ᵗ X → WfTy _ (`X X)
    sub-ty (Sᵗ-seal h) = wfX h

singleSealSubstitution :
  ∀ {Γ A B} →
  WfTy Γ B →
  SealSubstitution (sealᵉ A ∷ Γ) Γ
singleSealSubstitution hB =
  seal-sub
    (singleSealEnv _)
    sub-seal
  where
    sub-seal : ∀ {α} → (sealᵉ _ ∷ _) ∋ˢ α → WfTy _ (singleSealEnv _ α)
    sub-seal Zˢ = hB
    sub-seal (Sˢ-seal h) = wfα h

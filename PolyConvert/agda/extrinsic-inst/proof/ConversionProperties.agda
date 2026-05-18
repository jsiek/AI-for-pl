module proof.ConversionProperties where

-- File Charter:
--   * Properties of PolyConvert conversion typing.
--   * Includes store lifting for type binders and seal-context/store weakening
--     for upcasts and downcasts.
--   * Includes type-substitution preservation and opening for conversions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; length)
open import Data.Nat using (_≤_; suc)
open import Data.Nat.Properties using (_≟_; n≤1+n)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym)

open import Types
open import proof.TypeProperties
open import Store
open import Conversion
open import proof.StoreProperties using (len<suc-StoreWf)

cong-⊢↑ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{c c′ : Conv↑}{A A′ B B′ : Ty} →
  Σ ≡ Σ′ →
  c ≡ c′ →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ c′ ⦂ A′ ↑ˢ B′
cong-⊢↑ refl refl refl refl c⊢ = c⊢

cong-⊢↓ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{c c′ : Conv↓}{A A′ B B′ : Ty} →
  Σ ≡ Σ′ →
  c ≡ c′ →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ c′ ⦂ A′ ↓ˢ B′
cong-⊢↓ refl refl refl refl c⊢ = c⊢

⟰ᵗ-⊆ˢ :
  ∀ {Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  ⟰ᵗ Σ ⊆ˢ ⟰ᵗ Σ′
⟰ᵗ-⊆ˢ done = done
⟰ᵗ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = α} {A = renameᵗ suc A} (⟰ᵗ-⊆ˢ w)
⟰ᵗ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = α} {A = renameᵗ suc A} (⟰ᵗ-⊆ˢ w)

mutual
  wk-conv↑ :
    ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{c A B} →
    Ψ ≤ Ψ′ →
    Σ ⊆ˢ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    Δ ∣ Ψ′ ∣ Σ′ ⊢ c ⦂ A ↑ˢ B
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-unseal h) =
    ⊢↑-unseal (wkLookupˢ wΣ h)
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-⇒ p⊢ q⊢) =
    ⊢↑-⇒ (wk-conv↓ Ψ≤Ψ′ wΣ p⊢) (wk-conv↑ Ψ≤Ψ′ wΣ q⊢)
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-∀ c⊢) =
    ⊢↑-∀ (wk-conv↑ Ψ≤Ψ′ (⟰ᵗ-⊆ˢ wΣ) c⊢)
  wk-conv↑ Ψ≤Ψ′ wΣ (⊢↑-id wfA) =
    ⊢↑-id (WfTy-weakenˢ wfA Ψ≤Ψ′)

  wk-conv↓ :
    ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{c A B} →
    Ψ ≤ Ψ′ →
    Σ ⊆ˢ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    Δ ∣ Ψ′ ∣ Σ′ ⊢ c ⦂ A ↓ˢ B
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-seal h) =
    ⊢↓-seal (wkLookupˢ wΣ h)
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-⇒ p⊢ q⊢) =
    ⊢↓-⇒ (wk-conv↑ Ψ≤Ψ′ wΣ p⊢) (wk-conv↓ Ψ≤Ψ′ wΣ q⊢)
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-∀ c⊢) =
    ⊢↓-∀ (wk-conv↓ Ψ≤Ψ′ (⟰ᵗ-⊆ˢ wΣ) c⊢)
  wk-conv↓ Ψ≤Ψ′ wΣ (⊢↓-id wfA) =
    ⊢↓-id (WfTy-weakenˢ wfA Ψ≤Ψ′)

mutual
  subst↑-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{σ : Substᵗ}{c : Conv↑}{A B : Ty} →
    TySubstWf Δ Δ′ Ψ σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ⊢ subst↑ σ c ⦂
      substᵗ σ A ↑ˢ substᵗ σ B
  subst↑-wt hσ (⊢↑-unseal h) = ⊢↑-unseal (substLookupᵗ _ h)
  subst↑-wt hσ (⊢↑-⇒ p⊢ q⊢) =
    ⊢↑-⇒ (subst↓-wt hσ p⊢) (subst↑-wt hσ q⊢)
  subst↑-wt {Σ = Σ} {σ = σ} hσ (⊢↑-∀ c⊢) =
    ⊢↑-∀
      (cong-⊢↑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        refl
        (subst↑-wt (TySubstWf-exts hσ) c⊢))
  subst↑-wt hσ (⊢↑-id wfA) =
    ⊢↑-id (substᵗ-preserves-WfTy wfA hσ)

  subst↓-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{σ : Substᵗ}{c : Conv↓}{A B : Ty} →
    TySubstWf Δ Δ′ Ψ σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ⊢ subst↓ σ c ⦂
      substᵗ σ A ↓ˢ substᵗ σ B
  subst↓-wt hσ (⊢↓-seal h) = ⊢↓-seal (substLookupᵗ _ h)
  subst↓-wt hσ (⊢↓-⇒ p⊢ q⊢) =
    ⊢↓-⇒ (subst↑-wt hσ p⊢) (subst↓-wt hσ q⊢)
  subst↓-wt {Σ = Σ} {σ = σ} hσ (⊢↓-∀ c⊢) =
    ⊢↓-∀
      (cong-⊢↓
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        refl
        (subst↓-wt (TySubstWf-exts hσ) c⊢))
  subst↓-wt hσ (⊢↓-id wfA) =
    ⊢↓-id (substᵗ-preserves-WfTy wfA hσ)

openConv↑ :
  ∀ {Δ Ψ}{Σ : Store}{c : Conv↑}{A B T : Ty} →
  suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ↑ˢ B →
  WfTy Δ Ψ T →
  Δ ∣ Ψ ∣ Σ ⊢ subst↑ (singleTyEnv T) c ⦂ A [ T ]ᵗ ↑ˢ B [ T ]ᵗ
openConv↑ {Σ = Σ} {T = T} c⊢ wfT =
  cong-⊢↑
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    refl
    refl
    refl
    (subst↑-wt (singleTyEnv-Wf T wfT) c⊢)

openConv↓ :
  ∀ {Δ Ψ}{Σ : Store}{c : Conv↓}{A B T : Ty} →
  suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ↓ˢ B →
  WfTy Δ Ψ T →
  Δ ∣ Ψ ∣ Σ ⊢ subst↓ (singleTyEnv T) c ⦂ A [ T ]ᵗ ↓ˢ B [ T ]ᵗ
openConv↓ {Σ = Σ} {T = T} c⊢ wfT =
  cong-⊢↓
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    refl
    refl
    refl
    (subst↓-wt (singleTyEnv-Wf T wfT) c⊢)

mutual
  convert↑At-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{X : TyVar}{A T : Ty}{α : Seal} →
    TySubstWf Δ Δ′ Ψ (substVarFrom X (｀ α)) →
    TySubstWf Δ Δ′ Ψ (substVarFrom X T) →
    Σ ∋ˢ α ⦂ substVarFrom X T X →
    WfTy Δ Ψ A →
    Δ′ ∣ Ψ ∣ Σ ⊢ convert↑At X A α ⦂
      substᵗ (substVarFrom X (｀ α)) A ↑ˢ
      substᵗ (substVarFrom X T) A
  convert↑At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    with X ≟ Y
  convert↑At-wt {X = X} hSeal hT hα (wfVar {X = .X} X<Δ)
    | yes refl =
    cong-⊢↑ refl refl (sym (substVarFrom-seal-self X _)) refl
      (⊢↑-unseal hα)
  convert↑At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    | no X≢Y =
    cong-⊢↑ refl refl refl (substVarFrom-≢ X Y (｀ _) _ X≢Y)
      (⊢↑-id (hSeal Y<Δ))
  convert↑At-wt hSeal hT hα (wfSeal α<Ψ) = ⊢↑-id (wfSeal α<Ψ)
  convert↑At-wt hSeal hT hα wfBase = ⊢↑-id wfBase
  convert↑At-wt hSeal hT hα wf★ = ⊢↑-id wf★
  convert↑At-wt hSeal hT hα (wf⇒ wfA wfB) =
    ⊢↑-⇒ (convert↓At-wt hSeal hT hα wfA)
          (convert↑At-wt hSeal hT hα wfB)
  convert↑At-wt hSeal hT hα (wf∀ wfA) =
    ⊢↑-∀
      (convert↑At-wt
        (TySubstWf-exts hSeal)
        (TySubstWf-exts hT)
        (renameLookupᵗ suc hα)
        wfA)

  convert↓At-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{X : TyVar}{A T : Ty}{α : Seal} →
    TySubstWf Δ Δ′ Ψ (substVarFrom X (｀ α)) →
    TySubstWf Δ Δ′ Ψ (substVarFrom X T) →
    Σ ∋ˢ α ⦂ substVarFrom X T X →
    WfTy Δ Ψ A →
    Δ′ ∣ Ψ ∣ Σ ⊢ convert↓At X A α ⦂
      substᵗ (substVarFrom X T) A ↓ˢ
      substᵗ (substVarFrom X (｀ α)) A
  convert↓At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    with X ≟ Y
  convert↓At-wt {X = X} hSeal hT hα (wfVar {X = .X} X<Δ)
    | yes refl =
    cong-⊢↓ refl refl refl (sym (substVarFrom-seal-self X _))
      (⊢↓-seal hα)
  convert↓At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    | no X≢Y =
    cong-⊢↓ refl refl (substVarFrom-≢ X Y (｀ _) _ X≢Y) refl
      (⊢↓-id (hSeal Y<Δ))
  convert↓At-wt hSeal hT hα (wfSeal α<Ψ) = ⊢↓-id (wfSeal α<Ψ)
  convert↓At-wt hSeal hT hα wfBase = ⊢↓-id wfBase
  convert↓At-wt hSeal hT hα wf★ = ⊢↓-id wf★
  convert↓At-wt hSeal hT hα (wf⇒ wfA wfB) =
    ⊢↓-⇒ (convert↑At-wt hSeal hT hα wfA)
          (convert↓At-wt hSeal hT hα wfB)
  convert↓At-wt hSeal hT hα (wf∀ wfA) =
    ⊢↓-∀
      (convert↓At-wt
        (TySubstWf-exts hSeal)
        (TySubstWf-exts hT)
        (renameLookupᵗ suc hα)
        wfA)

convert↑-fresh-wt :
  ∀ {Δ Ψ}{Σ : Store}{A T : Ty} →
  StoreWf Δ Ψ Σ →
  WfTy (suc Δ) Ψ A →
  WfTy Δ Ψ T →
  Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ⊢
    convert↑ A (length Σ) ⦂
    A [ ｀ (length Σ) ]ᵗ ↑ˢ A [ T ]ᵗ
convert↑-fresh-wt wfΣ wfA wfT =
  convert↑At-wt
    (singleTyEnv-Wf (｀ _) (wfSeal (len<suc-StoreWf wfΣ)))
    (singleTyEnv-Wf _ (WfTy-weakenˢ wfT (n≤1+n _)))
    (Z∋ˢ refl refl)
    (WfTy-weakenˢ wfA (n≤1+n _))

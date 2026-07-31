module proof.Preservation where

-- File Charter:
--   * Type preservation for GTPLC one-step and multi-step reduction.
--   * Includes the local store-change transport lemmas needed by reduction.
--   * Depends on term/type substitution, coercion renaming, and store
--     well-formedness preservation.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong₂; sym)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Primitives
open import Terms
open import Reduction
open import proof.TypeInTypeSubst
open import proof.TyStore
open import proof.TypeInCoercionSubst
open import proof.TypeInTermSubst
open import proof.TermInTermSubst

------------------------------------------------------------------------
-- Transport across store changes
------------------------------------------------------------------------

change-wf : ∀ {Δ A χ}
  → WfTy Δ A
  → WfTy (changeTyCtx χ Δ) (changeᵗ χ A)
change-wf {χ = keep} hA = hA
change-wf {χ = bind Aχ} hA =
  renameᵗ-preserves-WfTy hA TyRenameWf-suc

change-typing : ∀ {Δ Σ M A χ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → ⟨ changeTyCtx χ Δ , changeStore χ Σ , [] ⟩
      ⊢ change χ M ⦂ changeᵗ χ A
change-typing {χ = keep} M⊢ = M⊢
change-typing {χ = bind Aχ} M⊢ =
  typing-store-weaken ⊆-drop (typing-shiftᵗ M⊢)

change-coercion-typing : ∀ {μ Δ Σ c A B χ}
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  → ∃[ ν ] (ν ∣ changeTyCtx χ Δ ∣ changeStore χ Σ
      ⊢ changeᶜ χ c ∶ changeᵗ χ A =⇒ changeᵗ χ B)
change-coercion-typing {μ = μ} {χ = keep} c⊢ =
  μ , c⊢
change-coercion-typing {μ = μ} {χ = bind Aχ} c⊢ =
  (λ Y → μ (predᵗ Y)) ,
  coercion-store-weaken ⊆-drop
    (coercion-renameᵗ TyRenameWf-suc
      (modeRename-left-inverse
        {ρ = suc} {ψ = predᵗ} {μ = μ}
        RenameLeftInverse-suc)
      c⊢)

bind-under-binder-coercion-typing : ∀ {μ Δ Σ c Aν Aχ B C}
  → μ ∣ suc Δ ∣ (zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ
      ⊢ c ∶ C =⇒ ⇑ᵗ B
  → ∃[ ν ] (ν ∣ suc (suc Δ)
      ∣ (zero , ⇑ᵗ (⇑ᵗ Aν))
          ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ)
      ⊢ renameᶜ (extᵗ suc) c
        ∶ renameᵗ (extᵗ suc) C =⇒ ⇑ᵗ (⇑ᵗ B))
bind-under-binder-coercion-typing
    {μ = μ} {Δ = Δ} {Σ = Σ} {c = c}
    {Aν = Aν} {Aχ = Aχ} {B = B} {C = C} c⊢ =
  target-mode ,
  subst≡
    (λ T → target-mode ∣ suc (suc Δ)
      ∣ (zero , ⇑ᵗ (⇑ᵗ Aν))
          ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ)
      ⊢ renameᶜ (extᵗ suc) c
        ∶ renameᵗ (extᵗ suc) C =⇒ T)
    (renameᵗ-ext-suc-comm suc B)
    (coercion-store-weaken (⊆-cons ⊆-drop) renamed-store)
  where
    target-mode : ModeEnv
    target-mode Y = μ (extᵗ predᵗ Y)

    renamed-store :
      target-mode ∣ suc (suc Δ)
        ∣ (zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ (⟰ᵗ Σ)
        ⊢ renameᶜ (extᵗ suc) c
          ∶ renameᵗ (extᵗ suc) C
          =⇒ renameᵗ (extᵗ suc) (⇑ᵗ B)
    renamed-store =
      subst≡
        (λ Σ′ → target-mode ∣ suc (suc Δ) ∣ Σ′
          ⊢ renameᶜ (extᵗ suc) c
            ∶ renameᵗ (extᵗ suc) C
            =⇒ renameᵗ (extᵗ suc) (⇑ᵗ B))
        (cong₂ _∷_
          (cong₂ _,_ refl (renameᵗ-ext-suc-comm suc Aν))
          (renameTyStoreᵗ-ext-suc-comm suc Σ))
        (coercion-renameᵗ
          (TyRenameWf-ext TyRenameWf-suc)
          (modeRename-left-inverse
            {ρ = extᵗ suc} {ψ = extᵗ predᵗ} {μ = μ}
            (RenameLeftInverse-ext RenameLeftInverse-suc))
          c⊢)

------------------------------------------------------------------------
-- Pure reduction
------------------------------------------------------------------------

pure-preservation : ∀ {Δ Σ M N A}
  → StoreWf Δ Σ
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → M —→ N
  → ⟨ Δ , Σ , [] ⟩ ⊢ N ⦂ A
pure-preservation wfΣ
    (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ =
  ⊢$ _
pure-preservation wfΣ (⊢· (⊢ƛ hA N⊢) V⊢) (β vV) =
  typing-single-subst N⊢ V⊢
pure-preservation wfΣ (⊢⟨⟩ (cast-id hA) V⊢) (β-id vV) =
  V⊢
pure-preservation wfΣ
    (⊢⟨⟩ (cast-error hA hB) V⊢) (β-error vV) =
  ⊢blame hB
pure-preservation wfΣ
    (⊢⟨⟩ (cast-seq p⊢ q⊢) V⊢) (β-seq vV) =
  ⊢⟨⟩ q⊢ (⊢⟨⟩ p⊢ V⊢)
pure-preservation wfΣ
    (⊢· (⊢⟨⟩ (cast-fun p⊢ q⊢) V⊢) W⊢) (β-↦ vV vW) =
  ⊢⟨⟩ q⊢ (⊢· V⊢ (⊢⟨⟩ p⊢ W⊢))
pure-preservation wfΣ
    (⊢⟨⟩ (cast-inst hB occ c⊢) V⊢) (β-inst vV) =
  ⊢ν wf★ V⊢ c⊢
pure-preservation wfΣ
    (⊢⟨⟩ (cast-untag hG ok G꞉A)
      (⊢⟨⟩ (cast-tag hG′ ok′ G꞉A′) V⊢))
    (tag-untag-ok vV) =
  subst≡ (λ T → ⟨ _ , _ , _ ⟩ ⊢ _ ⦂ T)
    (tagged-unique G꞉A′ G꞉A) V⊢
pure-preservation wfΣ
    (⊢⟨⟩ (cast-untag hH ok H꞉B)
      (⊢⟨⟩ (cast-tag hG ok′ G꞉A) V⊢))
    (tag-untag-bad vV G≢H) =
  ⊢blame (tagged-wf hH H꞉B)
pure-preservation wfΣ
    (⊢⟨⟩ (cast-unseal hB αB∈Σ ok)
      (⊢⟨⟩ (cast-seal hA αA∈Σ ok′) V⊢))
    (seal-unseal vV) =
  subst≡ (λ T → ⟨ _ , _ , _ ⟩ ⊢ _ ⦂ T)
    (unique wfΣ αA∈Σ αB∈Σ) V⊢
pure-preservation wfΣ
    (⊢· (⊢blame (wf⇒ hA hB)) M⊢) blame-·₁ =
  ⊢blame hB
pure-preservation wfΣ
    (⊢· V⊢ (⊢blame hA)) (blame-·₂ vV)
    with typing-wf wfΣ closedCtxWf V⊢
pure-preservation wfΣ
    (⊢· V⊢ (⊢blame hA)) (blame-·₂ vV)
    | wf⇒ hA′ hB =
  ⊢blame hB
pure-preservation wfΣ
    (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wf wfΣ c⊢
pure-preservation wfΣ
    (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ
    (⊢⊕ (⊢blame hA) op M⊢) blame-⊕₁ =
  ⊢blame wfBase
pure-preservation wfΣ
    (⊢⊕ L⊢ op (⊢blame hA)) (blame-⊕₂ vL) =
  ⊢blame wfBase

------------------------------------------------------------------------
-- Store-change reduction
------------------------------------------------------------------------

store-preservation : ∀ {Δ Σ M N A χ}
  → StoreWf Δ Σ
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → M —→[ χ ] N
  → StoreWf (changeTyCtx χ Δ) (changeStore χ Σ)
store-preservation wfΣ M⊢ (pure-step red) = wfΣ
store-preservation wfΣ (⊢ν hA V⊢ c⊢) (ν-step vV) =
  StoreWf-bind wfΣ hA
store-preservation wfΣ (⊢· L⊢ M⊢) (ξ-·₁ red) =
  store-preservation wfΣ L⊢ red
store-preservation wfΣ (⊢· V⊢ M⊢) (ξ-·₂ vV red) =
  store-preservation wfΣ M⊢ red
store-preservation wfΣ (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ red) =
  store-preservation wfΣ M⊢ red
store-preservation wfΣ (⊢ν hA L⊢ c⊢) (ξ-ν red) =
  store-preservation wfΣ L⊢ red
store-preservation wfΣ (⊢ν hA (⊢blame hC) c⊢) blame-ν =
  wfΣ
store-preservation wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red) =
  store-preservation wfΣ L⊢ red
store-preservation wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red) =
  store-preservation wfΣ M⊢ red

preservation : ∀ {Δ Σ M N A χ}
  → StoreWf Δ Σ
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → M —→[ χ ] N
  → ⟨ changeTyCtx χ Δ , changeStore χ Σ , [] ⟩
      ⊢ N ⦂ changeᵗ χ A
preservation wfΣ M⊢ (pure-step red) =
  pure-preservation wfΣ M⊢ red
preservation wfΣ (⊢ν hA V⊢ c⊢) (ν-step vV) =
  ⊢⟨⟩ c⊢ (type-app-typing vV V⊢)
preservation wfΣ (⊢· L⊢ M⊢) (ξ-·₁ {χ = keep} red) =
  ⊢· (preservation wfΣ L⊢ red) (change-typing M⊢)
preservation wfΣ (⊢· L⊢ M⊢) (ξ-·₁ {χ = bind Aχ} red) =
  ⊢· (preservation wfΣ L⊢ red) (change-typing M⊢)
preservation wfΣ (⊢· V⊢ M⊢) (ξ-·₂ {χ = keep} vV red) =
  ⊢· (change-typing V⊢) (preservation wfΣ M⊢ red)
preservation wfΣ
    (⊢· V⊢ M⊢) (ξ-·₂ {χ = bind Aχ} vV red) =
  ⊢· (change-typing V⊢) (preservation wfΣ M⊢ red)
preservation wfΣ
    (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ {χ = χ} red)
    with change-coercion-typing {χ = χ} c⊢
preservation wfΣ
    (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ {χ = χ} red)
    | μ′ , c′⊢ =
  ⊢⟨⟩ c′⊢ (preservation wfΣ M⊢ red)
preservation wfΣ
    (⊢ν hA L⊢ c⊢) (ξ-ν {χ = keep} red) =
  ⊢ν hA (preservation wfΣ L⊢ red) c⊢
preservation wfΣ
    (⊢ν hA L⊢ c⊢) (ξ-ν {χ = bind Aχ} red)
    with bind-under-binder-coercion-typing {Aχ = Aχ} c⊢
preservation wfΣ
    (⊢ν hA L⊢ c⊢) (ξ-ν {χ = bind Aχ} red)
    | μ′ , c′⊢ =
  ⊢ν (change-wf {χ = bind Aχ} hA)
    (preservation wfΣ L⊢ red) c′⊢
preservation wfΣ
    (⊢ν hA (⊢blame hC) c⊢) blame-ν =
  ⊢blame
    (typing-wf wfΣ closedCtxWf
      (⊢ν hA (⊢blame hC) c⊢))
preservation wfΣ
    (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ {χ = keep} red) =
  ⊢⊕ (preservation wfΣ L⊢ red) op (change-typing M⊢)
preservation wfΣ
    (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ {χ = bind Aχ} red) =
  ⊢⊕ (preservation wfΣ L⊢ red) op (change-typing M⊢)
preservation wfΣ
    (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ {χ = keep} vL red) =
  ⊢⊕ (change-typing L⊢) op (preservation wfΣ M⊢ red)
preservation wfΣ
    (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ {χ = bind Aχ} vL red) =
  ⊢⊕ (change-typing L⊢) op (preservation wfΣ M⊢ red)

------------------------------------------------------------------------
-- Multi-step preservation
------------------------------------------------------------------------

multi-preservation : ∀ {Δ Σ M N A χs}
  → StoreWf Δ Σ
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → M —↠[ χs ] N
  → ⟨ changeTyCtxs χs Δ , changeStores χs Σ , [] ⟩
      ⊢ N ⦂ changeTys χs A
multi-preservation wfΣ M⊢ ↠-refl = M⊢
multi-preservation wfΣ M⊢ (↠-step red reds) =
  multi-preservation
    (store-preservation wfΣ M⊢ red)
    (preservation wfΣ M⊢ red)
    reds

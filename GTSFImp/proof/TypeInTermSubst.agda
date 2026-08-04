module proof.TypeInTermSubst where

-- File Charter:
--   * Type-variable renaming and store transport for GTSFImp terms.
--   * Proves that renaming preserves values, conversion typing, and term
--     typing, with both lifted and freshly bound store corollaries.
--   * Supplies store replacement and lookup uniqueness used by preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (suc)
import Data.Nat as Nat
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import TermCtx hiding (_∋_⦂_)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import proof.TypeSafety.Progress using (gen-safe)

------------------------------------------------------------------------
-- Store lookup transport
------------------------------------------------------------------------

StoreRename : ∀ {Δ Δ′}
  → (rho : Δ ⇒ʳ Δ′)
  → TyStore Δ
  → TyStore Δ′
  → Set
StoreRename rho Σ Σ′ = ∀ {X A}
  → Σ ∋ X ⦂ A
  → Σ′ ∋ rho X ⦂ renameᵗ rho A

StoreRename-ext : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′} {Σ Σ′}
  → StoreRename rho Σ Σ′
  → StoreRename (extᵗ rho) (store-lift Σ) (store-lift Σ′)
StoreRename-ext {rho = rho} hΣ (S-lift∋ X∈ eq) =
  S-lift∋ (hΣ X∈)
    (trans (cong (renameᵗ (extᵗ rho)) eq) (renameᵗ-shift rho _))

toRename-keep-eq : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′) X
  → toRenameᵗ (keep rho) X ≡ extᵗ (toRenameᵗ rho) X
toRename-keep-eq rho Fin.zero = refl
toRename-keep-eq rho (Fin.suc X) = refl

StoreRename-keep : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′} {Σ Σ′}
  → StoreRename (toRenameᵗ rho) Σ Σ′
  → StoreRename (toRenameᵗ (keep rho))
      (store-lift Σ) (store-lift Σ′)
StoreRename-keep {rho = rho} hΣ (S-lift∋ X∈ eq) =
  S-lift∋ (hΣ X∈)
    (trans (cong (renameᵗ (toRenameᵗ (keep rho))) eq)
      (trans (renameᵗ-cong _ (toRename-keep-eq rho))
        (renameᵗ-shift (toRenameᵗ rho) _)))

toRename-id-eq : ∀ {Δ} (X : TyVar Δ) → toRenameᵗ id↪ᵗ X ≡ X
toRename-id-eq {Nat.zero} ()
toRename-id-eq {suc Δ} Fin.zero = refl
toRename-id-eq {suc Δ} (Fin.suc X) = cong Fin.suc (toRename-id-eq X)

toRename-wk-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ wk↪ᵗ X ≡ Fin.suc X
toRename-wk-eq X = cong Fin.suc (toRename-id-eq X)

renameᵗ-wk-eq : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ wk↪ᵗ) A ≡ ⇑ᵗ A
renameᵗ-wk-eq A = renameᵗ-cong A toRename-wk-eq

StoreRename-suc-lift : ∀ {Δ} {Σ : TyStore Δ}
  → StoreRename Fin.suc Σ (store-lift Σ)
StoreRename-suc-lift X∈ = S-lift∋ X∈ refl

StoreRename-suc-bind : ∀ {Δ} {Σ : TyStore Δ} {C : Ty Δ}
  → StoreRename Fin.suc Σ (store-bind Σ C)
StoreRename-suc-bind X∈ = S-bind∋ X∈ refl

renameᵗ-pointwise-id : ∀ {Δ} (rho : Δ ⇒ʳ Δ) (A : Ty Δ)
  → (∀ X → rho X ≡ X)
  → renameᵗ rho A ≡ A
renameᵗ-pointwise-id rho (＇ X) eq = cong ＇_ (eq X)
renameᵗ-pointwise-id rho (‵ ι) eq = refl
renameᵗ-pointwise-id rho ★ eq = refl
renameᵗ-pointwise-id rho (A ⇒ B) eq =
  cong₂ _⇒_ (renameᵗ-pointwise-id rho A eq)
    (renameᵗ-pointwise-id rho B eq)
renameᵗ-pointwise-id rho (`∀ A) eq =
  cong `∀ (renameᵗ-pointwise-id (extᵗ rho) A ext-eq)
  where
  ext-eq : ∀ X → extᵗ rho X ≡ X
  ext-eq Fin.zero = refl
  ext-eq (Fin.suc X) = cong Fin.suc (eq X)

renameᵗ-id : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (λ X → X) A ≡ A
renameᵗ-id A = renameᵗ-pointwise-id (λ X → X) A (λ X → refl)

StoreRename-id : ∀ {Δ} {Σ : TyStore Δ}
  → StoreRename (λ X → X) Σ Σ
StoreRename-id {Σ = Σ} {A = A} X∈ =
  subst≡ (λ B → Σ ∋ _ ⦂ B) (sym (renameᵗ-id A)) X∈

storeRename-wk-lift-at : ∀ {Δ} {Σ : TyStore Δ}
    (X : TyVar Δ) (A : Ty Δ)
  → Σ ∋ X ⦂ A
  → store-lift Σ ∋ toRenameᵗ wk↪ᵗ X
      ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A
storeRename-wk-lift-at {Σ = Σ} X A X∈ =
  subst≡ (λ B → store-lift Σ ∋ toRenameᵗ wk↪ᵗ X ⦂ B)
    (sym (renameᵗ-wk-eq A))
    (subst≡ (λ Y → store-lift Σ ∋ Y ⦂ ⇑ᵗ A)
      (sym (toRename-wk-eq X)) (S-lift∋ X∈ refl))

StoreRename-wk-lift : ∀ {Δ} {Σ : TyStore Δ} {X A}
  → Σ ∋ X ⦂ A
  → store-lift Σ ∋ toRenameᵗ wk↪ᵗ X
      ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A
StoreRename-wk-lift X∈ = storeRename-wk-lift-at _ _ X∈

storeRename-wk-bind-at : ∀ {Δ} {Σ : TyStore Δ} (C : Ty Δ)
    (X : TyVar Δ) (A : Ty Δ)
  → Σ ∋ X ⦂ A
  → store-bind Σ C ∋ toRenameᵗ wk↪ᵗ X
      ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A
storeRename-wk-bind-at {Σ = Σ} C X A X∈ =
  subst≡ (λ B → store-bind Σ C ∋ toRenameᵗ wk↪ᵗ X ⦂ B)
    (sym (renameᵗ-wk-eq A))
    (subst≡ (λ Y → store-bind Σ C ∋ Y ⦂ ⇑ᵗ A)
      (sym (toRename-wk-eq X)) (S-bind∋ X∈ refl))

StoreRename-wk-bind : ∀ {Δ} {Σ : TyStore Δ} {C : Ty Δ}
    {X A}
  → Σ ∋ X ⦂ A
  → store-bind Σ C ∋ toRenameᵗ wk↪ᵗ X
      ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A
StoreRename-wk-bind X∈ = storeRename-wk-bind-at _ _ _ X∈

StoreTransport : ∀ {Δ}
  → TyStore Δ
  → TyStore Δ
  → Set
StoreTransport Σ Σ′ = ∀ {X A} → Σ ∋ X ⦂ A → Σ′ ∋ X ⦂ A

StoreTransport-lift : ∀ {Δ} {Σ Σ′ : TyStore Δ}
  → StoreTransport Σ Σ′
  → StoreTransport (store-lift Σ) (store-lift Σ′)
StoreTransport-lift hΣ (S-lift∋ X∈ eq) =
  S-lift∋ (hΣ X∈) eq

StoreTransport-lift-bind : ∀ {Δ} {Σ : TyStore Δ} {C : Ty Δ}
  → StoreTransport (store-lift Σ) (store-bind Σ C)
StoreTransport-lift-bind (S-lift∋ X∈ eq) = S-bind∋ X∈ eq

------------------------------------------------------------------------
-- Conversion typing under renaming and store transport
------------------------------------------------------------------------

mutual
  reveal-renameᵗ : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {A B}
      {c : Conv↑ Δ A B}
    → StoreRename rho Σ Σ′
    → Σ ⊢↑ c
    → Σ′ ⊢↑ rename↑ rho c
  reveal-renameᵗ hΣ (⊢↑-unseal X∈) = ⊢↑-unseal (hΣ X∈)
  reveal-renameᵗ hΣ (⊢↑-⇒ c⊢ d⊢) =
    ⊢↑-⇒ (conceal-renameᵗ hΣ c⊢) (reveal-renameᵗ hΣ d⊢)
  reveal-renameᵗ {rho = rho} hΣ (⊢↑-∀ c⊢) =
    ⊢↑-∀ (reveal-renameᵗ (StoreRename-ext hΣ) c⊢)
  reveal-renameᵗ hΣ ⊢↑-id = ⊢↑-id

  conceal-renameᵗ : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {A B}
      {c : Conv↓ Δ A B}
    → StoreRename rho Σ Σ′
    → Σ ⊢↓ c
    → Σ′ ⊢↓ rename↓ rho c
  conceal-renameᵗ hΣ (⊢↓-seal X∈) = ⊢↓-seal (hΣ X∈)
  conceal-renameᵗ hΣ (⊢↓-⇒ c⊢ d⊢) =
    ⊢↓-⇒ (reveal-renameᵗ hΣ c⊢) (conceal-renameᵗ hΣ d⊢)
  conceal-renameᵗ {rho = rho} hΣ (⊢↓-∀ c⊢) =
    ⊢↓-∀ (conceal-renameᵗ (StoreRename-ext hΣ) c⊢)
  conceal-renameᵗ hΣ ⊢↓-id = ⊢↓-id

reveal-rename-id : ∀ {Δ} {Σ : TyStore Δ} {A B}
    {c : Conv↑ Δ A B}
  → Σ ⊢↑ c
  → Σ ⊢↑ rename↑ (λ X → X) c
reveal-rename-id = reveal-renameᵗ StoreRename-id

conceal-rename-id : ∀ {Δ} {Σ : TyStore Δ} {A B}
    {c : Conv↓ Δ A B}
  → Σ ⊢↓ c
  → Σ ⊢↓ rename↓ (λ X → X) c
conceal-rename-id = conceal-renameᵗ StoreRename-id

mutual
  reveal-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {A B}
      {c : Conv↑ Δ A B}
    → StoreTransport Σ Σ′
    → Σ ⊢↑ c
    → Σ′ ⊢↑ c
  reveal-store-transport hΣ (⊢↑-unseal X∈) = ⊢↑-unseal (hΣ X∈)
  reveal-store-transport hΣ (⊢↑-⇒ c⊢ d⊢) =
    ⊢↑-⇒ (conceal-store-transport hΣ c⊢)
      (reveal-store-transport hΣ d⊢)
  reveal-store-transport hΣ (⊢↑-∀ c⊢) =
    ⊢↑-∀ (reveal-store-transport (StoreTransport-lift hΣ) c⊢)
  reveal-store-transport hΣ ⊢↑-id = ⊢↑-id

  conceal-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {A B}
      {c : Conv↓ Δ A B}
    → StoreTransport Σ Σ′
    → Σ ⊢↓ c
    → Σ′ ⊢↓ c
  conceal-store-transport hΣ (⊢↓-seal X∈) = ⊢↓-seal (hΣ X∈)
  conceal-store-transport hΣ (⊢↓-⇒ c⊢ d⊢) =
    ⊢↓-⇒ (reveal-store-transport hΣ c⊢)
      (conceal-store-transport hΣ d⊢)
  conceal-store-transport hΣ (⊢↓-∀ c⊢) =
    ⊢↓-∀ (conceal-store-transport (StoreTransport-lift hΣ) c⊢)
  conceal-store-transport hΣ ⊢↓-id = ⊢↓-id

------------------------------------------------------------------------
-- Renaming values and type application
------------------------------------------------------------------------

rename-star-injective : ∀ {Δ Δ′} (rho : Δ ⇒ʳ Δ′) {A : Ty Δ}
  → renameᵗ rho A ≡ ★
  → A ≡ ★
rename-star-injective rho {A = ＇ X} ()
rename-star-injective rho {A = ‵ ι} ()
rename-star-injective rho {A = ★} refl = refl
rename-star-injective rho {A = A ⇒ B} ()
rename-star-injective rho {A = `∀ A} ()

rename-occurs : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (rho : Δ ⇒ʳ Δ′)
  → X ∈ᵗ A
  → rho X ∈ᵗ renameᵗ rho A
rename-occurs rho var-∈ = var-∈
rename-occurs rho (∈-fun-left X∈A) = ∈-fun-left (rename-occurs rho X∈A)
rename-occurs {X = X} {A = A ⇒ B} rho (∈-fun-right X∉A X∈B)
    with occurs? (rho X) (renameᵗ rho A)
rename-occurs {X = X} {A = A ⇒ B} rho (∈-fun-right X∉A X∈B)
    | present rhoX∈A = ∈-fun-left rhoX∈A
rename-occurs {X = X} {A = A ⇒ B} rho (∈-fun-right X∉A X∈B)
    | absent rhoX∉A =
  ∈-fun-right rhoX∉A (rename-occurs rho X∈B)
rename-occurs rho (∈-all X∈A) = ∈-all (rename-occurs (extᵗ rho) X∈A)

renameᵗᵐ-preserves-Value : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′) {V}
  → Value V
  → Value (renameᵗᵐ rho V)
renameᵗᵐ-preserves-Value rho (ƛ N) = ƛ _
renameᵗᵐ-preserves-Value rho (Λ vV) =
  Λ (renameᵗᵐ-preserves-Value (keep rho) vV)
renameᵗᵐ-preserves-Value rho ($ κ) = $ κ
renameᵗᵐ-preserves-Value rho
    (vV 《 inj {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Gns = Gns ⦄ 》)
    =
  renameᵗᵐ-preserves-Value rho vV
    《 subst≡ Inert (sym (renameᵐᶜ-idᵍ! rho Gᵍ))
      (inj ⦃ Gᵍ = renameGroundᵐ rho Gᵍ ⦄
        ⦃ G∼★ = rename∼★ᵐ rho G∼★ ⦄
        ⦃ Gns = renameNonStar (toRenameᵗ rho) Gns ⦄) 》
renameᵗᵐ-preserves-Value rho (vV 《 fun 》) =
  renameᵗᵐ-preserves-Value rho vV 《 fun 》
renameᵗᵐ-preserves-Value rho (vV 《 all 》) =
  renameᵗᵐ-preserves-Value rho vV 《 all 》
renameᵗᵐ-preserves-Value rho
    (vV 《 genᵥ {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄ A≠★ safe 》) =
  renameᵗᵐ-preserves-Value rho vV
    《 genᵥ ⦃ Bnv = _ ⦄ ⦃ z∈B = _ ⦄ A′≠★
      (gen-safe _ A′≠★ (renameNonVar _ Bnv)
        (rename-occurs _ z∈B)) 》
  where
  A′≠★ = λ eq → A≠★ (rename-star-injective _ eq)
renameᵗᵐ-preserves-Value rho (vV ↑ fun) =
  renameᵗᵐ-preserves-Value rho vV ↑ fun
renameᵗᵐ-preserves-Value rho (vV ↑ all) =
  renameᵗᵐ-preserves-Value rho vV ↑ all
renameᵗᵐ-preserves-Value rho (vV ↓ seal) =
  renameᵗᵐ-preserves-Value rho vV ↓ seal
renameᵗᵐ-preserves-Value rho (vV ↓ fun) =
  renameᵗᵐ-preserves-Value rho vV ↓ fun
renameᵗᵐ-preserves-Value rho (vV ↓ all) =
  renameᵗᵐ-preserves-Value rho vV ↓ all

renameCtx-shift : ∀ {Δ Δ′} (rho : Δ ⇒ʳ Δ′) Γ
  → renameCtx (extᵗ rho) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx rho Γ)
renameCtx-shift rho [] = refl
renameCtx-shift rho (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-shift rho A) (renameCtx-shift rho Γ)

renameCtx-wk-eq : ∀ {Δ} (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ wk↪ᵗ) Γ ≡ ⇑ᶜ Γ
renameCtx-wk-eq [] = refl
renameCtx-wk-eq (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-wk-eq A) (renameCtx-wk-eq Γ)

renameCtx-keep-shift : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′) Γ
  → renameCtx (toRenameᵗ (keep rho)) (⇑ᶜ Γ) ≡
    ⇑ᶜ (renameCtx (toRenameᵗ rho) Γ)
renameCtx-keep-shift rho [] = refl
renameCtx-keep-shift rho (A ∷ Γ) =
  cong₂ _∷_
    (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq rho))
      (renameᵗ-shift (toRenameᵗ rho) A))
    (renameCtx-keep-shift rho Γ)

rename-openᵗ : ∀ {Δ Δ′} (rho : Δ ⇒ʳ Δ′)
    (B : Ty (suc Δ)) (A : Ty Δ)
  → renameᵗ rho (B [ A ]ᵗ) ≡
    renameᵗ (extᵗ rho) B [ renameᵗ rho A ]ᵗ
rename-openᵗ rho B A =
  trans (renameᵗ-subst rho (singleSubᵗ A) B)
    (trans (substᵗ-cong B env-eq)
      (sym (substᵗ-rename (singleSubᵗ (renameᵗ rho A))
        (extᵗ rho) B)))
  where
  env-eq : ∀ X
    → renameᵗ rho (singleSubᵗ A X) ≡
      singleSubᵗ (renameᵗ rho A) (extᵗ rho X)
  env-eq Fin.zero = refl
  env-eq (Fin.suc X) = refl

------------------------------------------------------------------------
-- Typing under type renaming and store replacement
------------------------------------------------------------------------

typing-renameᵗ : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′}
    {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {Γ M A}
  → StoreRename (toRenameᵗ rho) Σ Σ′
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ′ , Σ′ , renameCtx (toRenameᵗ rho) Γ ⟩
      ⊢ renameᵗᵐ rho M ⦂ renameᵗ (toRenameᵗ rho) A
typing-renameᵗ hΣ (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
typing-renameᵗ hΣ (⊢ƛ M⊢) = ⊢ƛ (typing-renameᵗ hΣ M⊢)
typing-renameᵗ hΣ (⊢· L⊢ M⊢) =
  ⊢· (typing-renameᵗ hΣ L⊢) (typing-renameᵗ hΣ M⊢)
typing-renameᵗ {rho = rho} {Σ′ = Σ′} {Γ = Γ} hΣ (⊢Λ vM M⊢) =
  ⊢Λ (renameᵗᵐ-preserves-Value (keep rho) vM) body⊢
  where
  renamed-body⊢ = typing-renameᵗ (StoreRename-keep hΣ) M⊢

  body-context⊢ =
    subst≡
      (λ Γ′ → ⟨ _ , store-lift Σ′ , Γ′ ⟩
        ⊢ renameᵗᵐ (keep rho) _ ⦂ _)
      (renameCtx-keep-shift rho Γ)
      renamed-body⊢

  body⊢ =
    subst≡ (λ T → _ ⊢ renameᵗᵐ (keep rho) _ ⦂ T)
      (renameᵗ-cong _ (toRename-keep-eq rho)) body-context⊢
typing-renameᵗ {Δ′ = Δ′} {rho = rho} {Σ′ = Σ′} {Γ = Γ} hΣ
    (⊢• {C = C} {A = A} {L = L} L⊢) =
  subst≡
    (λ T → ⟨ Δ′ , Σ′ , renameCtx (toRenameᵗ rho) Γ ⟩
      ⊢ renameᵗᵐ rho L ⦂∀ renameᵗ (toRenameᵗ (keep rho)) C
        [ renameᵗ (toRenameᵗ rho) A ] ⦂ T)
    result-eq (⊢• body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq rho)

  body⊢ =
    subst≡
      (λ T → ⟨ Δ′ , Σ′ , renameCtx (toRenameᵗ rho) Γ ⟩
        ⊢ renameᵗᵐ rho L ⦂ `∀ T)
      (sym body-eq) (typing-renameᵗ hΣ L⊢)

  result-eq =
    trans (cong (λ T → T [ renameᵗ (toRenameᵗ rho) A ]ᵗ) body-eq)
      (sym (rename-openᵗ (toRenameᵗ rho) C A))
typing-renameᵗ {rho = rho} hΣ (⊢$ κ) =
  subst≡ (λ T → _ ⊢ _ ⦂ T)
    (constTy-renameᵗ (toRenameᵗ rho) κ) (⊢$ κ)
typing-renameᵗ hΣ (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (typing-renameᵗ hΣ L⊢) (typing-renameᵗ hΣ M⊢)
typing-renameᵗ hΣ (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (typing-renameᵗ hΣ L⊢) (typing-renameᵗ hΣ M⊢)
typing-renameᵗ {rho = rho} hΣ (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (typing-renameᵗ hΣ M⊢) (renameᵐᶜ rho c)
typing-renameᵗ hΣ (⊢reveal c⊢ M⊢) =
  ⊢reveal (reveal-renameᵗ hΣ c⊢) (typing-renameᵗ hΣ M⊢)
typing-renameᵗ hΣ (⊢conceal c⊢ M⊢) =
  ⊢conceal (conceal-renameᵗ hΣ c⊢) (typing-renameᵗ hΣ M⊢)
typing-renameᵗ hΣ ⊢blame = ⊢blame

typing-shiftᵗ-lift : ∀ {Δ} {Σ : TyStore Δ} {Γ M A}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ suc Δ , store-lift Σ , ⇑ᶜ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ ⇑ᵗ A
typing-shiftᵗ-lift {Σ = Σ} {Γ = Γ} {M = M} {A = A} M⊢ =
  subst≡
    (λ T → ⟨ _ , store-lift Σ , ⇑ᶜ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ T)
    (renameᵗ-wk-eq A)
    (subst≡
      (λ Γ′ → ⟨ _ , store-lift Σ , Γ′ ⟩ ⊢ ⇑ᵗᵐ M ⦂ _)
      (renameCtx-wk-eq Γ) (typing-renameᵗ StoreRename-wk-lift M⊢))

typing-shiftᵗ-bind : ∀ {Δ} {Σ : TyStore Δ} {Γ M A} {C : Ty Δ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ suc Δ , store-bind Σ C , ⇑ᶜ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ ⇑ᵗ A
typing-shiftᵗ-bind {Σ = Σ} {Γ = Γ} {M = M} {A = A} {C = C} M⊢ =
  subst≡
    (λ T → ⟨ _ , store-bind Σ C , ⇑ᶜ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ T)
    (renameᵗ-wk-eq A)
    (subst≡
      (λ Γ′ → ⟨ _ , store-bind Σ C , Γ′ ⟩ ⊢ ⇑ᵗᵐ M ⦂ _)
      (renameCtx-wk-eq Γ) (typing-renameᵗ StoreRename-wk-bind M⊢))

typing-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {Γ M A}
  → StoreTransport Σ Σ′
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ′ , Γ ⟩ ⊢ M ⦂ A
typing-store-transport hΣ (⊢` x∈) = ⊢` x∈
typing-store-transport hΣ (⊢ƛ M⊢) =
  ⊢ƛ (typing-store-transport hΣ M⊢)
typing-store-transport hΣ (⊢· L⊢ M⊢) =
  ⊢· (typing-store-transport hΣ L⊢)
    (typing-store-transport hΣ M⊢)
typing-store-transport hΣ (⊢Λ vM M⊢) =
  ⊢Λ vM (typing-store-transport (StoreTransport-lift hΣ) M⊢)
typing-store-transport hΣ (⊢• L⊢) =
  ⊢• (typing-store-transport hΣ L⊢)
typing-store-transport hΣ (⊢$ κ) = ⊢$ κ
typing-store-transport hΣ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (typing-store-transport hΣ L⊢)
    (typing-store-transport hΣ M⊢)
typing-store-transport hΣ (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (typing-store-transport hΣ M⊢) c
typing-store-transport hΣ (⊢reveal c⊢ M⊢) =
  ⊢reveal (reveal-store-transport hΣ c⊢)
    (typing-store-transport hΣ M⊢)
typing-store-transport hΣ (⊢conceal c⊢ M⊢) =
  ⊢conceal (conceal-store-transport hΣ c⊢)
    (typing-store-transport hΣ M⊢)
typing-store-transport hΣ ⊢blame = ⊢blame

typing-lift-to-bind : ∀ {Δ} {Σ : TyStore Δ} {Γ M A} {C : Ty Δ}
  → ⟨ suc Δ , store-lift Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ suc Δ , store-bind Σ C , Γ ⟩ ⊢ M ⦂ A
typing-lift-to-bind = typing-store-transport StoreTransport-lift-bind

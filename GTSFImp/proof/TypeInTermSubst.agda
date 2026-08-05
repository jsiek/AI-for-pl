module proof.TypeInTermSubst where

-- File Charter:
--   * Type-variable renaming and store transport for GTSFImp terms.
--   * Proves that renaming preserves values, conversion typing, and term
--     typing, with both lifted and freshly bound store corollaries.
--   * Supplies store replacement and lookup uniqueness used by preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
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
open import proof.Consistency using (gen-safe; subst-rename-left-inverse)
open import proof.ImprecisionConsistency using
  (renameᵗ-injective; toRenameᵗ-injective; subst-zero-occurs-exts)
import proof.TypeSafety.Progress as Prog

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

StoreSubst : ∀ {Δ Δ′}
  → (rho : Δ ⇒ʳ Δ′)
  → (sigma : Δ′ ⇒ˢ Δ)
  → TyStore Δ′
  → TyStore Δ
  → Set
StoreSubst rho sigma Σ′ Σ =
  ∀ {X A} → Σ′ ∋ rho X ⦂ A → Σ ∋ X ⦂ substᵗ sigma A

StoreSubst-keep : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′}
    {sigma : Δ′ ⇒ˢ Δ} {Σ′ Σ}
  → StoreSubst (toRenameᵗ rho) sigma Σ′ Σ
  → StoreSubst (toRenameᵗ (keep rho)) (extsᵗ sigma)
      (store-lift Σ′) (store-lift Σ)
StoreSubst-keep hΣ {X = Fin.zero} ()
StoreSubst-keep {sigma = sigma} hΣ {X = Fin.suc X}
    (S-lift∋ {A = A} X∈ eq) =
  S-lift∋ (hΣ X∈)
    (trans (cong (substᵗ (extsᵗ sigma)) eq)
      (substᵗ-shift sigma A))

StoreSubst-ext : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
    {sigma : Δ′ ⇒ˢ Δ} {Σ′ Σ}
  → StoreSubst rho sigma Σ′ Σ
  → StoreSubst (extᵗ rho) (extsᵗ sigma)
      (store-lift Σ′) (store-lift Σ)
StoreSubst-ext hΣ {X = Fin.zero} ()
StoreSubst-ext {sigma = sigma} hΣ {X = Fin.suc X}
    (S-lift∋ {A = A} X∈ eq) =
  S-lift∋ (hΣ X∈)
    (trans (cong (substᵗ (extsᵗ sigma)) eq)
      (substᵗ-shift sigma A))

StoreSubst-wk-lift-at : ∀ {Δ} {Σ : TyStore Δ}
    (X : TyVar Δ) (A : Ty (suc Δ))
  → store-lift Σ ∋ Fin.suc X ⦂ A
  → Σ ∋ X ⦂ A [ ★ ]ᵗ
StoreSubst-wk-lift-at X A (S-lift∋ {A = A′} X∈ eq) =
  subst≡ (λ T → _ ∋ X ⦂ T)
    (sym (trans (cong (λ T → T [ ★ ]ᵗ) eq)
      (shift-openᵗ A′ ★)))
    X∈

StoreSubst-wk-lift : ∀ {Δ} {Σ : TyStore Δ}
  → StoreSubst (toRenameᵗ wk↪ᵗ) (singleSubᵗ ★) (store-lift Σ) Σ
StoreSubst-wk-lift {Σ = Σ} {X = X} {A = A} X∈ =
  StoreSubst-wk-lift-at X A
    (subst≡ (λ Y → store-lift Σ ∋ Y ⦂ A)
      (toRename-wk-eq X) X∈)

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

rename↑-RevealValue-inv : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
    {A B : Ty Δ} {c : Conv↑ Δ A B}
  → RevealValue (rename↑ rho c)
  → RevealValue c
rename↑-RevealValue-inv {c = unseal X R} ()
rename↑-RevealValue-inv {c = c ↦↑ d} fun = fun
rename↑-RevealValue-inv {c = `∀↑ c} all = all
rename↑-RevealValue-inv {c = id↑ A} ()

rename↓-ConcealValue-inv : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
    {A B : Ty Δ} {c : Conv↓ Δ A B}
  → ConcealValue (rename↓ rho c)
  → ConcealValue c
rename↓-ConcealValue-inv {c = seal X R} seal = seal
rename↓-ConcealValue-inv {c = c ↦↓ d} fun = fun
rename↓-ConcealValue-inv {c = `∀↓ c} all = all
rename↓-ConcealValue-inv {c = id↓ A} ()

mutual
  renameᵐᶜ-GenSafe-inv : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′}
      {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → GenSafe (renameᵐᶜ rho c)
    → GenSafe c
  renameᵐᶜ-GenSafe-inv {c = id ★} ()
  renameᵐᶜ-GenSafe-inv {c = id (‵ ι)} ()
  renameᵐᶜ-GenSafe-inv {c = id (＇ X)} ()
  renameᵐᶜ-GenSafe-inv {c = c ↦ d} safe-⇒ = safe-⇒
  renameᵐᶜ-GenSafe-inv {c = ∀ᶜ c} safe-∀ = safe-∀
  renameᵐᶜ-GenSafe-inv {c = _! c} ()
  renameᵐᶜ-GenSafe-inv {c = ？ c} ()
  renameᵐᶜ-GenSafe-inv
      {c = inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★}
      (safe-inst B′≢★) =
    safe-inst B≢★
  renameᵐᶜ-GenSafe-inv
      {c = gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★}
      (safe-gen A′≢★ safe) =
    safe-gen A≢★ (gen-safe c A≢★ Bnv z∈B)
  renameᵐᶜ-GenSafe-inv {c = bot-elim} ()
  renameᵐᶜ-GenSafe-inv {c = bot-intro} ()

  inert-injection-source≡ground : ∀ {Δ} {μ : Env∼ Δ}
      {A G : Ty Δ} {c : μ ⊢ A ∼ G}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Ans : NonStar A ⦄
    → Inert (_! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄)
    → A ≡ G
  inert-injection-source≡ground inj = refl

  renameᵐᶜ-Inert-inv : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′}
      {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → Inert (renameᵐᶜ rho c)
    → Inert c
  renameᵐᶜ-Inert-inv {c = id ★} ()
  renameᵐᶜ-Inert-inv {c = id (‵ ι)} ()
  renameᵐᶜ-Inert-inv {c = id (＇ X)} ()
  renameᵐᶜ-Inert-inv {c = c ↦ d} fun = fun
  renameᵐᶜ-Inert-inv {c = ∀ᶜ c} all = all
  renameᵐᶜ-Inert-inv {rho = rho}
      {c = _! {A = A} {G = G} ⦃ Gᵍ = Gᵍ ⦄
        ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄}
      inert with Prog.to-ground Gᵍ c
  renameᵐᶜ-Inert-inv {c = _! ⦃ Gᵍ = Gᵍ ⦄
        ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄}
      inert | Prog.same =
    inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ Gns = Ans ⦄
  renameᵐᶜ-Inert-inv {rho = rho}
      {c = _! {A = A} {G = G} ⦃ Gᵍ = Gᵍ ⦄
        ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄}
      inert | Prog.other A≢G =
    ⊥-elim (A≢G
      (renameᵗ-injective (toRenameᵗ-injective rho)
        (inert-injection-source≡ground
          ⦃ Gᵍ = renameGroundᵐ rho Gᵍ ⦄
          ⦃ G∼★ = rename∼★ᵐ rho G∼★ ⦄
          ⦃ Ans = renameNonStar (toRenameᵗ rho) Ans ⦄
          inert)))
  renameᵐᶜ-Inert-inv {c = ？ c} ()
  renameᵐᶜ-Inert-inv {c = inst_ c B≢★} ()
  renameᵐᶜ-Inert-inv
      {c = gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★}
      (genᵥ A′≢★ safe) =
    genᵥ A≢★ (gen-safe c A≢★ Bnv z∈B)
  renameᵐᶜ-Inert-inv {c = bot-elim} ()
  renameᵐᶜ-Inert-inv {c = bot-intro} ()

renameᵗᵐ-Value-inv : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′} {V}
  → Value (renameᵗᵐ rho V)
  → Value V
renameᵗᵐ-Value-inv {V = ` x} ()
renameᵗᵐ-Value-inv {V = ƛ N} (ƛ N′) = ƛ N
renameᵗᵐ-Value-inv {V = L · M} ()
renameᵗᵐ-Value-inv {rho = rho} {V = Λ V} (Λ vV) =
  Λ (renameᵗᵐ-Value-inv {rho = keep rho} vV)
renameᵗᵐ-Value-inv {V = M ⦂∀ B [ A ]} ()
renameᵗᵐ-Value-inv {V = $ κ} ($ κ′) = $ κ
renameᵗᵐ-Value-inv {V = L ⊕[ op ] M} ()
renameᵗᵐ-Value-inv {rho = rho} {V = V ⟨ c ⟩} (vV 《 inert 》) =
  renameᵗᵐ-Value-inv {rho = rho} vV
    《 renameᵐᶜ-Inert-inv {rho = rho} inert 》
renameᵗᵐ-Value-inv {rho = rho} {V = V ↑ c} (vV ↑ rv) =
  renameᵗᵐ-Value-inv {rho = rho} vV
    ↑ rename↑-RevealValue-inv rv
renameᵗᵐ-Value-inv {rho = rho} {V = V ↓ c} (vV ↓ cv) =
  renameᵗᵐ-Value-inv {rho = rho} vV
    ↓ rename↓-ConcealValue-inv cv

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

substCtx-shift : ∀ {Δ Δ′} (sigma : Δ ⇒ˢ Δ′) Γ
  → substCtx (extsᵗ sigma) (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx sigma Γ)
substCtx-shift sigma [] = refl
substCtx-shift sigma (A ∷ Γ) =
  cong₂ _∷_ (substᵗ-shift sigma A) (substCtx-shift sigma Γ)

substCtx-open-shift : ∀ {Δ} (Γ : TermCtx Δ)
  → substCtx (singleSubᵗ ★) (⇑ᶜ Γ) ≡ Γ
substCtx-open-shift [] = refl
substCtx-open-shift (A ∷ Γ) =
  cong₂ _∷_ (shift-openᵗ A ★) (substCtx-open-shift Γ)

left-keep : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′}
    {sigma : Δ′ ⇒ˢ Δ}
  → (∀ X → sigma (toRenameᵗ rho X) ≡ ＇ X)
  → ∀ X → extsᵗ sigma (toRenameᵗ (keep rho) X) ≡ ＇ X
left-keep left Fin.zero = refl
left-keep left (Fin.suc X) = cong (renameᵗ Fin.suc) (left X)

left-ext : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′} {sigma : Δ′ ⇒ˢ Δ}
  → (∀ X → sigma (rho X) ≡ ＇ X)
  → ∀ X → extsᵗ sigma (extᵗ rho X) ≡ ＇ X
left-ext left Fin.zero = refl
left-ext left (Fin.suc X) = cong (renameᵗ Fin.suc) (left X)

mutual
  reveal-open-renamed : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
      {sigma : Δ′ ⇒ˢ Δ} {Σ′ Σ A B}
      {c : Conv↑ Δ A B}
    → (left : ∀ X → sigma (rho X) ≡ ＇ X)
    → StoreSubst rho sigma Σ′ Σ
    → Σ′ ⊢↑ rename↑ rho c
    → Σ ⊢↑ c
  reveal-open-renamed {c = unseal X R} left hΣ (⊢↑-unseal X∈) =
    ⊢↑-unseal
      (subst≡ (λ T → _ ∋ X ⦂ T)
        (subst-rename-left-inverse left R) (hΣ X∈))
  reveal-open-renamed {c = c ↦↑ d} left hΣ (⊢↑-⇒ c⊢ d⊢) =
    ⊢↑-⇒ (conceal-open-renamed left hΣ c⊢)
      (reveal-open-renamed left hΣ d⊢)
  reveal-open-renamed {rho = rho} {c = `∀↑ c}
      left hΣ (⊢↑-∀ c⊢) =
    ⊢↑-∀
      (reveal-open-renamed {rho = extᵗ rho} (left-ext left)
        (StoreSubst-ext hΣ) c⊢)
  reveal-open-renamed {c = id↑ A} left hΣ ⊢↑-id = ⊢↑-id

  conceal-open-renamed : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
      {sigma : Δ′ ⇒ˢ Δ} {Σ′ Σ A B}
      {c : Conv↓ Δ A B}
    → (left : ∀ X → sigma (rho X) ≡ ＇ X)
    → StoreSubst rho sigma Σ′ Σ
    → Σ′ ⊢↓ rename↓ rho c
    → Σ ⊢↓ c
  conceal-open-renamed {c = seal X R} left hΣ (⊢↓-seal X∈) =
    ⊢↓-seal
      (subst≡ (λ T → _ ∋ X ⦂ T)
        (subst-rename-left-inverse left R) (hΣ X∈))
  conceal-open-renamed {c = c ↦↓ d} left hΣ (⊢↓-⇒ c⊢ d⊢) =
    ⊢↓-⇒ (reveal-open-renamed left hΣ c⊢)
      (conceal-open-renamed left hΣ d⊢)
  conceal-open-renamed {rho = rho} {c = `∀↓ c}
      left hΣ (⊢↓-∀ c⊢) =
    ⊢↓-∀
      (conceal-open-renamed {rho = extᵗ rho} (left-ext left)
        (StoreSubst-ext hΣ) c⊢)
  conceal-open-renamed {c = id↓ A} left hΣ ⊢↓-id = ⊢↓-id

typing-open-renamed : ∀ {Δ Δ′} {rho : Δ ↪ᵗ Δ′}
    {sigma : Δ′ ⇒ˢ Δ} {Σ′ Σ Γ M A}
  → (left : ∀ X → sigma (toRenameᵗ rho X) ≡ ＇ X)
  → StoreSubst (toRenameᵗ rho) sigma Σ′ Σ
  → ⟨ Δ′ , Σ′ , Γ ⟩ ⊢ renameᵗᵐ rho M ⦂ A
  → ⟨ Δ , Σ , substCtx sigma Γ ⟩ ⊢ M ⦂ substᵗ sigma A
typing-open-renamed {M = ` x} left hΣ (⊢` x∈) =
  ⊢` (substᵗ-∋ _ x∈)
typing-open-renamed {M = ƛ M} left hΣ (⊢ƛ M⊢) =
  ⊢ƛ (typing-open-renamed left hΣ M⊢)
typing-open-renamed {M = L · M} left hΣ (⊢· L⊢ M⊢) =
  ⊢· (typing-open-renamed left hΣ L⊢)
    (typing-open-renamed left hΣ M⊢)
typing-open-renamed {rho = rho} {sigma = sigma} {Σ = Σ} {Γ = Γ}
    {M = Λ M} left hΣ (⊢Λ vM M⊢) =
  ⊢Λ (renameᵗᵐ-Value-inv {rho = keep rho} vM)
    (subst≡ (λ Γ′ → ⟨ _ , store-lift Σ , Γ′ ⟩ ⊢ M ⦂ _)
      (substCtx-shift sigma Γ)
      (typing-open-renamed {rho = keep rho} {sigma = extsᵗ sigma}
        (left-keep left) (StoreSubst-keep hΣ) M⊢))
typing-open-renamed {rho = rho} {sigma = sigma} {Σ = Σ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} left hΣ (⊢• L⊢) =
  subst≡
    (λ T → ⟨ _ , Σ , substCtx sigma Γ ⟩
      ⊢ L ⦂∀ C [ A ] ⦂ T)
    (sym result-eq) (⊢• body⊢)
  where
  body-eq =
    subst-rename-left-inverse (left-keep left) C

  body⊢ =
    subst≡ (λ T → ⟨ _ , Σ , substCtx sigma Γ ⟩ ⊢ L ⦂ T)
      (cong `∀ body-eq) (typing-open-renamed left hΣ L⊢)

  target-open-eq =
    trans
      (cong (λ T → T [ renameᵗ (toRenameᵗ rho) A ]ᵗ)
        (renameᵗ-cong C (toRename-keep-eq rho)))
      (sym (rename-openᵗ (toRenameᵗ rho) C A))

  result-eq =
    trans (cong (substᵗ sigma) target-open-eq)
      (subst-rename-left-inverse left (C [ A ]ᵗ))
typing-open-renamed {M = $ (κℕ n)} left hΣ (⊢$ .(κℕ n)) =
  ⊢$ (κℕ n)
typing-open-renamed {M = $ (κ𝔹 b)} left hΣ (⊢$ .(κ𝔹 b)) =
  ⊢$ (κ𝔹 b)
typing-open-renamed {M = L ⊕[ addℕ ] M} left hΣ (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (typing-open-renamed left hΣ L⊢)
    (typing-open-renamed left hΣ M⊢)
typing-open-renamed {M = L ⊕[ and𝔹 ] M} left hΣ
    (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (typing-open-renamed left hΣ L⊢)
    (typing-open-renamed left hΣ M⊢)
typing-open-renamed {M = _⟨_⟩ M {A = A} {B = B} c}
    left hΣ (⊢⟨⟩ M⊢ c′) =
  subst≡ (λ T → _ ⊢ M ⟨ c ⟩ ⦂ T)
    (sym (subst-rename-left-inverse left B))
    (⊢⟨⟩
      (subst≡ (λ T → _ ⊢ M ⦂ T)
        (subst-rename-left-inverse left A)
        (typing-open-renamed left hΣ M⊢))
      c)
typing-open-renamed {rho = rho} {M = _↑_ M {A = A} {B = B} c}
    left hΣ (⊢reveal c⊢ M⊢) =
  subst≡ (λ T → _ ⊢ M ↑ c ⦂ T)
    (sym (subst-rename-left-inverse left B))
    (⊢reveal
      (reveal-open-renamed {rho = toRenameᵗ rho} left hΣ c⊢)
      (subst≡ (λ T → _ ⊢ M ⦂ T)
        (subst-rename-left-inverse left A)
        (typing-open-renamed left hΣ M⊢)))
typing-open-renamed {rho = rho} {M = _↓_ M {A = A} {B = B} c}
    left hΣ (⊢conceal c⊢ M⊢) =
  subst≡ (λ T → _ ⊢ M ↓ c ⦂ T)
    (sym (subst-rename-left-inverse left B))
    (⊢conceal
      (conceal-open-renamed {rho = toRenameᵗ rho} left hΣ c⊢)
      (subst≡ (λ T → _ ⊢ M ⦂ T)
        (subst-rename-left-inverse left A)
        (typing-open-renamed left hΣ M⊢)))
typing-open-renamed {M = blame} left hΣ ⊢blame = ⊢blame

typing-open-shiftᵗ-lift : ∀ {Δ} {Σ : TyStore Δ} {Γ M A}
  → ⟨ suc Δ , store-lift Σ , ⇑ᶜ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ A
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A [ ★ ]ᵗ
typing-open-shiftᵗ-lift {Γ = Γ} M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (substCtx-open-shift Γ)
    (typing-open-renamed {rho = wk↪ᵗ} {sigma = singleSubᵗ ★}
      (λ X → cong (singleSubᵗ ★) (toRename-wk-eq X))
      StoreSubst-wk-lift M⊢)

typing-shiftᵗ-lift-inv : ∀ {Δ} {Σ : TyStore Δ} {Γ M A}
  → ⟨ suc Δ , store-lift Σ , ⇑ᶜ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ ⇑ᵗ A
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
typing-shiftᵗ-lift-inv {A = A} M⊢ =
  subst≡ (λ T → _ ⊢ _ ⦂ T) (shift-openᵗ A ★)
    (typing-open-shiftᵗ-lift M⊢)

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

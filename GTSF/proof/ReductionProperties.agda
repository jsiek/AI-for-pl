module proof.ReductionProperties where

-- File Charter:
--   * Proof-only metatheory for Nu GTSF reduction.
--   * Multi-step composition, store-change action composition, type-action
--     well-formedness/shape lemmas, and reduction congruence lemmas for
--     contexts that do not involve narrowing/widening.
--   * Narrowing/widening-specific reduction arguments belong in their
--     corresponding proof modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; _≤_; zero; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; suc-injective)
open import Data.Product using (Σ; _×_; _,_; ∃-syntax; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import Coercions
open import Primitives using (Const)
open import NuTerms
open import NuReduction
open import proof.CoercionProperties
  using
    ( renameᶜ-dual-normal
    ; renameᶜ-ext-suc-suc
    ; renameᶜ-open-commute
    ; renameᶜ-preserves-Inert
    ; renameᶜ-reflects-Inert
    )
open import proof.NuTermProperties
  using
    ( renameᵗᵐ-ext-suc-comm
    ; renameᵗᵐ-open-commute
    ; renameᵗᵐ-preserves-Value
    ; renameᵗᵐ-preserves-No•
    )
open import proof.TypeProperties using
  ( TyRenameWf-suc
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-preserves-WfTy
  )

------------------------------------------------------------------------
-- Store-change list views
------------------------------------------------------------------------

-- A plain snoc view was tried first for emitted store-change prefixes, but it
-- loses the information catchup needs: whether the last non-keep change is a
-- binder.  The surviving proofs use `StoreChangesLastBind` instead.

data AllKeep : StoreChanges → Set where
  all-[] :
    AllKeep []
  all-keep : ∀ {χs} →
    AllKeep χs →
    AllKeep (keep ∷ χs)

data StoreChangesLastBind : StoreChanges → Set where
  no-bind : ∀ {χs} →
    AllKeep χs →
    StoreChangesLastBind χs
  last-bind : ∀ χs A keeps →
    AllKeep keeps →
    StoreChangesLastBind (χs ++ bind A ∷ keeps)

storeChangesLastBind : ∀ χs → StoreChangesLastBind χs
storeChangesLastBind [] = no-bind all-[]
storeChangesLastBind (keep ∷ χs)
    with storeChangesLastBind χs
storeChangesLastBind (keep ∷ χs) | no-bind keeps =
  no-bind (all-keep keeps)
storeChangesLastBind (keep ∷ .(χs ++ bind A ∷ keeps))
    | last-bind χs A keeps keeps-ok =
  last-bind (keep ∷ χs) A keeps keeps-ok
storeChangesLastBind (bind A ∷ χs)
    with storeChangesLastBind χs
storeChangesLastBind (bind A ∷ χs) | no-bind keeps =
  last-bind [] A χs keeps
storeChangesLastBind (bind A ∷ .(χs ++ bind B ∷ keeps))
    | last-bind χs B keeps keeps-ok =
  last-bind (bind A ∷ χs) B keeps keeps-ok

applyTyCtx-≤ :
  ∀ χ Δ →
  Δ ≤ applyTyCtx χ Δ
applyTyCtx-≤ keep Δ = ≤-refl
applyTyCtx-≤ (bind A) Δ = n≤1+n Δ

applyTyCtxs-≤ :
  ∀ χs Δ →
  Δ ≤ applyTyCtxs χs Δ
applyTyCtxs-≤ [] Δ = ≤-refl
applyTyCtxs-≤ (χ ∷ χs) Δ =
  ≤-trans (applyTyCtx-≤ χ Δ) (applyTyCtxs-≤ χs (applyTyCtx χ Δ))

------------------------------------------------------------------------
-- Store-change composition
------------------------------------------------------------------------

storeTail : Store → Store
storeTail [] = []
storeTail (_ ∷ Σ) = Σ

storeHead-∷≡ :
  ∀ {x y : TyVar × Ty}{Σ Σ′} →
  x ∷ Σ ≡ y ∷ Σ′ →
  x ≡ y
storeHead-∷≡ refl = refl

storeTail-∷≡ :
  ∀ {x y : TyVar × Ty}{Σ Σ′} →
  x ∷ Σ ≡ y ∷ Σ′ →
  Σ ≡ Σ′
storeTail-∷≡ eq = cong storeTail eq

shiftVar : ℕ → TyVar → TyVar
shiftVar zero X = X
shiftVar (suc n) X = suc (shiftVar n X)

shiftTy : ℕ → Ty → Ty
shiftTy zero A = A
shiftTy (suc n) A = ⇑ᵗ (shiftTy n A)

shiftStore : ℕ → Store → Store
shiftStore zero Σ = Σ
shiftStore (suc n) Σ = ⟰ᵗ (shiftStore n Σ)

shiftStore-empty :
  ∀ n →
  shiftStore n [] ≡ []
shiftStore-empty zero = refl
shiftStore-empty (suc n) rewrite shiftStore-empty n = refl

shiftStore-cons :
  ∀ n α A Σ →
  shiftStore n ((α , A) ∷ Σ) ≡
    (shiftVar n α , shiftTy n A) ∷ shiftStore n Σ
shiftStore-cons zero α A Σ = refl
shiftStore-cons (suc n) α A Σ
    rewrite shiftStore-cons n α A Σ =
  refl

shiftStore-⟰ᵗ :
  ∀ n Σ →
  shiftStore n (⟰ᵗ Σ) ≡ ⟰ᵗ (shiftStore n Σ)
shiftStore-⟰ᵗ zero Σ = refl
shiftStore-⟰ᵗ (suc n) Σ =
  cong ⟰ᵗ (shiftStore-⟰ᵗ n Σ)

renameStoreᵗ-empty-inv :
  ∀ ρ {Σ} →
  renameStoreᵗ ρ Σ ≡ [] →
  Σ ≡ []
renameStoreᵗ-empty-inv ρ {[]} eq = refl
renameStoreᵗ-empty-inv ρ {_ ∷ Σ} ()

⟰ᵗ-empty-inv :
  ∀ {Σ} →
  ⟰ᵗ Σ ≡ [] →
  Σ ≡ []
⟰ᵗ-empty-inv = renameStoreᵗ-empty-inv suc

shiftStore-empty-inv :
  ∀ n {Σ} →
  shiftStore n Σ ≡ [] →
  Σ ≡ []
shiftStore-empty-inv zero eq = eq
shiftStore-empty-inv (suc n) eq =
  shiftStore-empty-inv n (⟰ᵗ-empty-inv eq)

applyStores-++ :
  ∀ χs χs′ Σ →
  applyStores (χs ++ χs′) Σ ≡ applyStores χs′ (applyStores χs Σ)
applyStores-++ [] χs′ Σ = refl
applyStores-++ (χ ∷ χs) χs′ Σ =
  applyStores-++ χs χs′ (applyStore χ Σ)

allKeep-applyStores-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ Σ → applyStores χs Σ ≡ Σ
allKeep-applyStores-id all-[] Σ = refl
allKeep-applyStores-id (all-keep keeps) Σ =
  allKeep-applyStores-id keeps Σ

applyStores-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Σ →
  applyStores (χs ++ bind A ∷ keeps) Σ ≡
    applyStore (bind A) (applyStores χs Σ)
applyStores-last-bind χs A keeps keeps-ok Σ =
  trans
    (applyStores-++ χs (bind A ∷ keeps) Σ)
    (allKeep-applyStores-id keeps-ok
      (applyStore (bind A) (applyStores χs Σ)))

applyStores-last-bind-tail :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Σ →
  storeTail (applyStores (χs ++ bind A ∷ keeps) Σ) ≡
    ⟰ᵗ (applyStores χs Σ)
applyStores-last-bind-tail χs A keeps keeps-ok Σ =
  cong storeTail (applyStores-last-bind χs A keeps keeps-ok Σ)

applyStores-cons≢[] :
  ∀ χs {α A Σ} →
  applyStores χs ((α , A) ∷ Σ) ≢ []
applyStores-cons≢[] [] ()
applyStores-cons≢[] (keep ∷ χs) eq =
  applyStores-cons≢[] χs eq
applyStores-cons≢[] (bind A ∷ χs) eq =
  applyStores-cons≢[] χs eq

applyStores-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ Σ → applyStores χs Σ ≡ Σ
applyStores-empty-id [] eq Σ = refl
applyStores-empty-id (keep ∷ χs) eq Σ =
  applyStores-empty-id χs eq Σ
applyStores-empty-id (bind A ∷ χs) eq Σ =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTyCtxs-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ Δ → applyTyCtxs χs Δ ≡ Δ
applyTyCtxs-empty-id [] eq Δ = refl
applyTyCtxs-empty-id (keep ∷ χs) eq Δ =
  applyTyCtxs-empty-id χs eq Δ
applyTyCtxs-empty-id (bind A ∷ χs) eq Δ =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTys-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ A → applyTys χs A ≡ A
applyTys-empty-id [] eq A = refl
applyTys-empty-id (keep ∷ χs) eq A =
  applyTys-empty-id χs eq A
applyTys-empty-id (bind A ∷ χs) eq B =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTy-★ :
  ∀ χ →
  applyTy χ ★ ≡ ★
applyTy-★ keep = refl
applyTy-★ (bind A) = refl

applyTys-★ :
  ∀ χs →
  applyTys χs ★ ≡ ★
applyTys-★ [] = refl
applyTys-★ (χ ∷ χs) rewrite applyTy-★ χ = applyTys-★ χs

applyTy-ℕ :
  ∀ χ →
  applyTy χ (‵ `ℕ) ≡ ‵ `ℕ
applyTy-ℕ keep = refl
applyTy-ℕ (bind A) = refl

applyTys-ℕ :
  ∀ χs →
  applyTys χs (‵ `ℕ) ≡ ‵ `ℕ
applyTys-ℕ [] = refl
applyTys-ℕ (χ ∷ χs) rewrite applyTy-ℕ χ = applyTys-ℕ χs

applyTys-ℕ-applyTys :
  ∀ χs χs′ →
  applyTys χs′ (applyTys χs (‵ `ℕ)) ≡ ‵ `ℕ
applyTys-ℕ-applyTys χs χs′ =
  trans (cong (applyTys χs′) (applyTys-ℕ χs)) (applyTys-ℕ χs′)

applyTerms-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ M → applyTerms χs M ≡ M
applyTerms-empty-id [] eq M = refl
applyTerms-empty-id (keep ∷ χs) eq M =
  applyTerms-empty-id χs eq M
applyTerms-empty-id (bind A ∷ χs) eq M =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTyCtxs-++ :
  ∀ χs χs′ Δ →
  applyTyCtxs (χs ++ χs′) Δ ≡ applyTyCtxs χs′ (applyTyCtxs χs Δ)
applyTyCtxs-++ [] χs′ Δ = refl
applyTyCtxs-++ (χ ∷ χs) χs′ Δ =
  applyTyCtxs-++ χs χs′ (applyTyCtx χ Δ)

allKeep-applyTyCtxs-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ Δ → applyTyCtxs χs Δ ≡ Δ
allKeep-applyTyCtxs-id all-[] Δ = refl
allKeep-applyTyCtxs-id (all-keep keeps) Δ =
  allKeep-applyTyCtxs-id keeps Δ

applyTyCtxs-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Δ →
  applyTyCtxs (χs ++ bind A ∷ keeps) Δ ≡ suc (applyTyCtxs χs Δ)
applyTyCtxs-last-bind χs A keeps keeps-ok Δ =
  trans
    (applyTyCtxs-++ χs (bind A ∷ keeps) Δ)
    (allKeep-applyTyCtxs-id keeps-ok (suc (applyTyCtxs χs Δ)))

applyTyCtxs-suc :
  ∀ χs Δ →
  applyTyCtxs χs (suc Δ) ≡ suc (applyTyCtxs χs Δ)
applyTyCtxs-suc [] Δ = refl
applyTyCtxs-suc (keep ∷ χs) Δ = applyTyCtxs-suc χs Δ
applyTyCtxs-suc (bind A ∷ χs) Δ = applyTyCtxs-suc χs (suc Δ)

applyTys-++ :
  ∀ χs χs′ A →
  applyTys (χs ++ χs′) A ≡ applyTys χs′ (applyTys χs A)
applyTys-++ [] χs′ A = refl
applyTys-++ (χ ∷ χs) χs′ A =
  applyTys-++ χs χs′ (applyTy χ A)

applyTys-⇒ :
  ∀ χs A B →
  applyTys χs (A ⇒ B) ≡ applyTys χs A ⇒ applyTys χs B
applyTys-⇒ [] A B = refl
applyTys-⇒ (keep ∷ χs) A B = applyTys-⇒ χs A B
applyTys-⇒ (bind C ∷ χs) A B = applyTys-⇒ χs (⇑ᵗ A) (⇑ᵗ B)

wfTy-⇑ :
  ∀ {Δ A} →
  WfTy Δ A →
  WfTy (suc Δ) (⇑ᵗ A)
wfTy-⇑ wf = renameᵗ-preserves-WfTy wf TyRenameWf-suc

wfTy-applyTys :
  ∀ χs {Δ A} →
  WfTy Δ A →
  WfTy (applyTyCtxs χs Δ) (applyTys χs A)
wfTy-applyTys [] wf = wf
wfTy-applyTys (keep ∷ χs) wf = wfTy-applyTys χs wf
wfTy-applyTys (bind X ∷ χs) wf = wfTy-applyTys χs (wfTy-⇑ wf)

allKeep-applyTys-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ A → applyTys χs A ≡ A
allKeep-applyTys-id all-[] A = refl
allKeep-applyTys-id (all-keep keeps) A =
  allKeep-applyTys-id keeps A

applyTys-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ B →
  applyTys (χs ++ bind A ∷ keeps) B ≡ ⇑ᵗ (applyTys χs B)
applyTys-last-bind χs A keeps keeps-ok B =
  trans
    (applyTys-++ χs (bind A ∷ keeps) B)
    (allKeep-applyTys-id keeps-ok (⇑ᵗ (applyTys χs B)))

applyTys-⇑ᵗ :
  ∀ χs A →
  applyTys χs (⇑ᵗ A) ≡ ⇑ᵗ (applyTys χs A)
applyTys-⇑ᵗ [] A = refl
applyTys-⇑ᵗ (keep ∷ χs) A = applyTys-⇑ᵗ χs A
applyTys-⇑ᵗ (bind B ∷ χs) A = applyTys-⇑ᵗ χs (⇑ᵗ A)

applyTyUnderTyBinder : StoreChange → Ty → Ty
applyTyUnderTyBinder keep A = A
applyTyUnderTyBinder (bind B) A = renameᵗ (extᵗ suc) A

applyTysUnderTyBinders : StoreChanges → Ty → Ty
applyTysUnderTyBinders [] A = A
applyTysUnderTyBinders (χ ∷ χs) A =
  applyTysUnderTyBinders χs (applyTyUnderTyBinder χ A)

applyTysUnderTyBinders-++ :
  ∀ χs χs′ A →
  applyTysUnderTyBinders (χs ++ χs′) A ≡
    applyTysUnderTyBinders χs′ (applyTysUnderTyBinders χs A)
applyTysUnderTyBinders-++ [] χs′ A = refl
applyTysUnderTyBinders-++ (χ ∷ χs) χs′ A =
  applyTysUnderTyBinders-++ χs χs′ (applyTyUnderTyBinder χ A)

applyTysUnderTyBinders-⇑ᵗ :
  ∀ χs A →
  applyTysUnderTyBinders χs (⇑ᵗ A) ≡ ⇑ᵗ (applyTys χs A)
applyTysUnderTyBinders-⇑ᵗ [] A = refl
applyTysUnderTyBinders-⇑ᵗ (keep ∷ χs) A =
  applyTysUnderTyBinders-⇑ᵗ χs A
applyTysUnderTyBinders-⇑ᵗ (bind B ∷ χs) A =
  trans
    (cong (applyTysUnderTyBinders χs) (renameᵗ-ext-suc-comm suc A))
    (applyTysUnderTyBinders-⇑ᵗ χs (⇑ᵗ A))

applyTy-∀ :
  ∀ χ A →
  applyTy χ (`∀ A) ≡ `∀ (applyTyUnderTyBinder χ A)
applyTy-∀ keep A = refl
applyTy-∀ (bind B) A = refl

applyTys-∀ :
  ∀ χs A →
  applyTys χs (`∀ A) ≡ `∀ (applyTysUnderTyBinders χs A)
applyTys-∀ [] A = refl
applyTys-∀ (keep ∷ χs) A = applyTys-∀ χs A
applyTys-∀ (bind B ∷ χs) A =
  applyTys-∀ χs (renameᵗ (extᵗ suc) A)

applyTyVar : StoreChange → TyVar → TyVar
applyTyVar keep α = α
applyTyVar (bind A) α = suc α

applyTyVars : StoreChanges → TyVar → TyVar
applyTyVars [] α = α
applyTyVars (χ ∷ χs) α = applyTyVars χs (applyTyVar χ α)

applyTyVars-++ :
  ∀ χs χs′ α →
  applyTyVars (χs ++ χs′) α ≡ applyTyVars χs′ (applyTyVars χs α)
applyTyVars-++ [] χs′ α = refl
applyTyVars-++ (χ ∷ χs) χs′ α =
  applyTyVars-++ χs χs′ (applyTyVar χ α)

applyTerms-++ :
  ∀ χs χs′ M →
  applyTerms (χs ++ χs′) M ≡ applyTerms χs′ (applyTerms χs M)
applyTerms-++ [] χs′ M = refl
applyTerms-++ (χ ∷ χs) χs′ M =
  applyTerms-++ χs χs′ (applyTerm χ M)

allKeep-applyTerms-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ M → applyTerms χs M ≡ M
allKeep-applyTerms-id all-[] M = refl
allKeep-applyTerms-id (all-keep keeps) M =
  allKeep-applyTerms-id keeps M

applyTerms-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ M →
  applyTerms (χs ++ bind A ∷ keeps) M ≡ ⇑ᵗᵐ (applyTerms χs M)
applyTerms-last-bind χs A keeps keeps-ok M =
  trans
    (applyTerms-++ χs (bind A ∷ keeps) M)
    (allKeep-applyTerms-id keeps-ok (⇑ᵗᵐ (applyTerms χs M)))

applyTerms-⇑ᵗᵐ :
  ∀ χs M →
  applyTerms χs (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (applyTerms χs M)
applyTerms-⇑ᵗᵐ [] M = refl
applyTerms-⇑ᵗᵐ (keep ∷ χs) M = applyTerms-⇑ᵗᵐ χs M
applyTerms-⇑ᵗᵐ (bind A ∷ χs) M = applyTerms-⇑ᵗᵐ χs (⇑ᵗᵐ M)

applyTerm-preserves-Value :
  ∀ χ {V} →
  Value V →
  Value (applyTerm χ V)
applyTerm-preserves-Value keep vV = vV
applyTerm-preserves-Value (bind A) vV = renameᵗᵐ-preserves-Value suc vV

applyTerms-preserves-Value :
  ∀ χs {V} →
  Value V →
  Value (applyTerms χs V)
applyTerms-preserves-Value [] vV = vV
applyTerms-preserves-Value (χ ∷ χs) vV =
  applyTerms-preserves-Value χs (applyTerm-preserves-Value χ vV)

applyTerm-preserves-No• :
  ∀ χ {M} →
  No• M →
  No• (applyTerm χ M)
applyTerm-preserves-No• keep noM = noM
applyTerm-preserves-No• (bind A) noM = renameᵗᵐ-preserves-No• suc noM

applyTerms-preserves-No• :
  ∀ χs {M} →
  No• M →
  No• (applyTerms χs M)
applyTerms-preserves-No• [] noM = noM
applyTerms-preserves-No• (χ ∷ χs) noM =
  applyTerms-preserves-No• χs (applyTerm-preserves-No• χ noM)

applyTerms-const :
  ∀ χs κ →
  applyTerms χs ($ κ) ≡ $ κ
applyTerms-const [] κ = refl
applyTerms-const (keep ∷ χs) κ = applyTerms-const χs κ
applyTerms-const (bind A ∷ χs) κ = applyTerms-const χs κ

applyTermUnderTyBinder : StoreChange → Term → Term
applyTermUnderTyBinder keep M = M
applyTermUnderTyBinder (bind A) M = renameᵗᵐ (extᵗ suc) M

applyTermsUnderTyBinders : StoreChanges → Term → Term
applyTermsUnderTyBinders [] M = M
applyTermsUnderTyBinders (χ ∷ χs) M =
  applyTermsUnderTyBinders χs (applyTermUnderTyBinder χ M)

applyTermsUnderTyBinders-⇑ᵗᵐ :
  ∀ χs M →
  applyTermsUnderTyBinders χs (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (applyTerms χs M)
applyTermsUnderTyBinders-⇑ᵗᵐ [] M = refl
applyTermsUnderTyBinders-⇑ᵗᵐ (keep ∷ χs) M =
  applyTermsUnderTyBinders-⇑ᵗᵐ χs M
applyTermsUnderTyBinders-⇑ᵗᵐ (bind B ∷ χs) M =
  trans
    (cong (applyTermsUnderTyBinders χs) (renameᵗᵐ-ext-suc-comm suc M))
    (applyTermsUnderTyBinders-⇑ᵗᵐ χs (⇑ᵗᵐ M))

applyTermsUnderTyBinders-++ :
  ∀ χs χs′ M →
  applyTermsUnderTyBinders (χs ++ χs′) M ≡
    applyTermsUnderTyBinders χs′ (applyTermsUnderTyBinders χs M)
applyTermsUnderTyBinders-++ [] χs′ M = refl
applyTermsUnderTyBinders-++ (χ ∷ χs) χs′ M =
  applyTermsUnderTyBinders-++ χs χs′ (applyTermUnderTyBinder χ M)

applyTermUnderTyBinder-preserves-Value :
  ∀ χ {V} →
  Value V →
  Value (applyTermUnderTyBinder χ V)
applyTermUnderTyBinder-preserves-Value keep vV = vV
applyTermUnderTyBinder-preserves-Value (bind A) vV =
  renameᵗᵐ-preserves-Value (extᵗ suc) vV

applyTermsUnderTyBinders-preserves-Value :
  ∀ χs {V} →
  Value V →
  Value (applyTermsUnderTyBinders χs V)
applyTermsUnderTyBinders-preserves-Value [] vV = vV
applyTermsUnderTyBinders-preserves-Value (χ ∷ χs) vV =
  applyTermsUnderTyBinders-preserves-Value χs
    (applyTermUnderTyBinder-preserves-Value χ vV)

applyTermUnderTyBinder-preserves-No• :
  ∀ χ {M} →
  No• M →
  No• (applyTermUnderTyBinder χ M)
applyTermUnderTyBinder-preserves-No• keep noM = noM
applyTermUnderTyBinder-preserves-No• (bind A) noM =
  renameᵗᵐ-preserves-No• (extᵗ suc) noM

applyTermsUnderTyBinders-preserves-No• :
  ∀ χs {M} →
  No• M →
  No• (applyTermsUnderTyBinders χs M)
applyTermsUnderTyBinders-preserves-No• [] noM = noM
applyTermsUnderTyBinders-preserves-No• (χ ∷ χs) noM =
  applyTermsUnderTyBinders-preserves-No• χs
    (applyTermUnderTyBinder-preserves-No• χ noM)

applyTerms-open :
  ∀ χs M α →
  applyTerms χs (M [ α ]ᵀ) ≡
    applyTermsUnderTyBinders χs M [ applyTyVars χs α ]ᵀ
applyTerms-open [] M α = refl
applyTerms-open (keep ∷ χs) M α = applyTerms-open χs M α
applyTerms-open (bind A ∷ χs) M α =
  trans
    (cong (applyTerms χs) (renameᵗᵐ-open-commute suc M α))
    (applyTerms-open χs (renameᵗᵐ (extᵗ suc) M) (suc α))

applyTerms-last-bind-open :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ M α →
  applyTerms (χs ++ bind A ∷ keeps) (M [ α ]ᵀ) ≡
    applyTerms χs (renameᵗᵐ (extᵗ suc) M [ suc α ]ᵀ)
applyTerms-last-bind-open χs A keeps keeps-ok M α =
  trans
    (applyTerms-last-bind χs A keeps keeps-ok (M [ α ]ᵀ))
    (trans
      (sym (applyTerms-⇑ᵗᵐ χs (M [ α ]ᵀ)))
      (cong (applyTerms χs) (renameᵗᵐ-open-commute suc M α)))

applyTerms-Λ :
  ∀ χs M →
  applyTerms χs (Λ M) ≡ Λ (applyTermsUnderTyBinders χs M)
applyTerms-Λ [] M = refl
applyTerms-Λ (keep ∷ χs) M = applyTerms-Λ χs M
applyTerms-Λ (bind A ∷ χs) M =
  applyTerms-Λ χs (renameᵗᵐ (extᵗ suc) M)

applyTerms-• :
  ∀ χs M →
  applyTerms χs (M •) ≡ applyTerms χs M •
applyTerms-• [] M = refl
applyTerms-• (keep ∷ χs) M = applyTerms-• χs M
applyTerms-• (bind A ∷ χs) M = applyTerms-• χs (⇑ᵗᵐ M)

applyCoercions : StoreChanges → Coercion → Coercion
applyCoercions [] c = c
applyCoercions (χ ∷ χs) c = applyCoercions χs (applyCoercion χ c)

applyCoercions-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ c → applyCoercions χs c ≡ c
applyCoercions-empty-id [] eq c = refl
applyCoercions-empty-id (keep ∷ χs) eq c =
  applyCoercions-empty-id χs eq c
applyCoercions-empty-id (bind A ∷ χs) eq c =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyCoercions-++ :
  ∀ χs χs′ c →
  applyCoercions (χs ++ χs′) c ≡
    applyCoercions χs′ (applyCoercions χs c)
applyCoercions-++ [] χs′ c = refl
applyCoercions-++ (χ ∷ χs) χs′ c =
  applyCoercions-++ χs χs′ (applyCoercion χ c)

allKeep-applyCoercions-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ c → applyCoercions χs c ≡ c
allKeep-applyCoercions-id all-[] c = refl
allKeep-applyCoercions-id (all-keep keeps) c =
  allKeep-applyCoercions-id keeps c

applyCoercions-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ c →
  applyCoercions (χs ++ bind A ∷ keeps) c ≡ ⇑ᶜ (applyCoercions χs c)
applyCoercions-last-bind χs A keeps keeps-ok c =
  trans
    (applyCoercions-++ χs (bind A ∷ keeps) c)
    (allKeep-applyCoercions-id keeps-ok (⇑ᶜ (applyCoercions χs c)))

applyCoercions-⇑ᶜ :
  ∀ χs c →
  applyCoercions χs (⇑ᶜ c) ≡ ⇑ᶜ (applyCoercions χs c)
applyCoercions-⇑ᶜ [] c = refl
applyCoercions-⇑ᶜ (keep ∷ χs) c = applyCoercions-⇑ᶜ χs c
applyCoercions-⇑ᶜ (bind A ∷ χs) c = applyCoercions-⇑ᶜ χs (⇑ᶜ c)

applyCoercion-preserves-Inert :
  ∀ χ {c} →
  Inert c →
  Inert (applyCoercion χ c)
applyCoercion-preserves-Inert keep i = i
applyCoercion-preserves-Inert (bind A) i = renameᶜ-preserves-Inert suc i

applyCoercions-preserves-Inert :
  ∀ χs {c} →
  Inert c →
  Inert (applyCoercions χs c)
applyCoercions-preserves-Inert [] i = i
applyCoercions-preserves-Inert (χ ∷ χs) i =
  applyCoercions-preserves-Inert χs (applyCoercion-preserves-Inert χ i)

applyCoercion-dual :
  ∀ χ c →
  applyCoercion χ (- c) ≡ - applyCoercion χ c
applyCoercion-dual keep c = refl
applyCoercion-dual (bind A) c = renameᶜ-dual-normal suc c

applyCoercions-dual :
  ∀ χs c →
  applyCoercions χs (- c) ≡ - applyCoercions χs c
applyCoercions-dual [] c = refl
applyCoercions-dual (keep ∷ χs) c = applyCoercions-dual χs c
applyCoercions-dual (bind A ∷ χs) c
    rewrite renameᶜ-dual-normal suc c =
  applyCoercions-dual χs (⇑ᶜ c)

applyCoercionUnderTyBinders : StoreChanges → Coercion → Coercion
applyCoercionUnderTyBinders [] c = c
applyCoercionUnderTyBinders (χ ∷ χs) c =
  applyCoercionUnderTyBinders χs (applyCoercionUnderTyBinder χ c)

applyCoercionUnderTyBinder-⇑ᶜ :
  ∀ χ c →
  applyCoercionUnderTyBinder χ (⇑ᶜ c) ≡ ⇑ᶜ (applyCoercion χ c)
applyCoercionUnderTyBinder-⇑ᶜ keep c = refl
applyCoercionUnderTyBinder-⇑ᶜ (bind A) c = renameᶜ-ext-suc-suc c

applyCoercionUnderTyBinder-preserves-Inert :
  ∀ χ {c} →
  Inert c →
  Inert (applyCoercionUnderTyBinder χ c)
applyCoercionUnderTyBinder-preserves-Inert keep i = i
applyCoercionUnderTyBinder-preserves-Inert (bind A) i =
  renameᶜ-preserves-Inert (extᵗ suc) i

applyCoercionUnderTyBinder-reflects-Inert :
  ∀ χ c →
  Inert (applyCoercionUnderTyBinder χ c) →
  Inert c
applyCoercionUnderTyBinder-reflects-Inert keep c i = i
applyCoercionUnderTyBinder-reflects-Inert (bind A) c i =
  renameᶜ-reflects-Inert (extᵗ suc) c i

applyCoercionUnderTyBinders-preserves-Inert :
  ∀ χs {c} →
  Inert c →
  Inert (applyCoercionUnderTyBinders χs c)
applyCoercionUnderTyBinders-preserves-Inert [] i = i
applyCoercionUnderTyBinders-preserves-Inert (χ ∷ χs) i =
  applyCoercionUnderTyBinders-preserves-Inert χs
    (applyCoercionUnderTyBinder-preserves-Inert χ i)

applyCoercionUnderTyBinders-reflects-Inert :
  ∀ χs c →
  Inert (applyCoercionUnderTyBinders χs c) →
  Inert c
applyCoercionUnderTyBinders-reflects-Inert [] c i = i
applyCoercionUnderTyBinders-reflects-Inert (χ ∷ χs) c i =
  applyCoercionUnderTyBinder-reflects-Inert χ c
    (applyCoercionUnderTyBinders-reflects-Inert χs
      (applyCoercionUnderTyBinder χ c) i)

applyCoercionUnderTyBinders-⇑ᶜ :
  ∀ χs c →
  applyCoercionUnderTyBinders χs (⇑ᶜ c) ≡ ⇑ᶜ (applyCoercions χs c)
applyCoercionUnderTyBinders-⇑ᶜ [] c = refl
applyCoercionUnderTyBinders-⇑ᶜ (χ ∷ χs) c =
  trans
    (cong (applyCoercionUnderTyBinders χs)
      (applyCoercionUnderTyBinder-⇑ᶜ χ c))
    (applyCoercionUnderTyBinders-⇑ᶜ χs (applyCoercion χ c))

applyCoercionUnderTyBinders-++ :
  ∀ χs χs′ c →
  applyCoercionUnderTyBinders (χs ++ χs′) c ≡
    applyCoercionUnderTyBinders χs′ (applyCoercionUnderTyBinders χs c)
applyCoercionUnderTyBinders-++ [] χs′ c = refl
applyCoercionUnderTyBinders-++ (χ ∷ χs) χs′ c =
  applyCoercionUnderTyBinders-++ χs χs′
    (applyCoercionUnderTyBinder χ c)

applyTerms-ν :
  ∀ χs A M c →
  applyTerms χs (ν A M c) ≡
    ν (applyTys χs A) (applyTerms χs M)
      (applyCoercionUnderTyBinders χs c)
applyTerms-ν [] A M c = refl
applyTerms-ν (keep ∷ χs) A M c = applyTerms-ν χs A M c
applyTerms-ν (bind B ∷ χs) A M c =
  applyTerms-ν χs (⇑ᵗ A) (⇑ᵗᵐ M) (renameᶜ (extᵗ suc) c)

applyCoercions-open :
  ∀ χs c α →
  applyCoercions χs (c [ α ]ᶜ) ≡
    applyCoercionUnderTyBinders χs c [ applyTyVars χs α ]ᶜ
applyCoercions-open [] c α = refl
applyCoercions-open (keep ∷ χs) c α = applyCoercions-open χs c α
applyCoercions-open (bind A ∷ χs) c α =
  trans
    (cong (applyCoercions χs) (renameᶜ-open-commute suc c α))
    (applyCoercions-open χs (renameᶜ (extᵗ suc) c) (suc α))

applyCoercions-last-bind-open :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ c α →
  applyCoercions (χs ++ bind A ∷ keeps) (c [ α ]ᶜ) ≡
    applyCoercions χs (renameᶜ (extᵗ suc) c [ suc α ]ᶜ)
applyCoercions-last-bind-open χs A keeps keeps-ok c α =
  trans
    (applyCoercions-last-bind χs A keeps keeps-ok (c [ α ]ᶜ))
    (trans
      (sym (applyCoercions-⇑ᶜ χs (c [ α ]ᶜ)))
      (cong (applyCoercions χs) (renameᶜ-open-commute suc c α)))

applyCoercions-∀ :
  ∀ χs c →
  applyCoercions χs (`∀ c) ≡ `∀ (applyCoercionUnderTyBinders χs c)
applyCoercions-∀ [] c = refl
applyCoercions-∀ (keep ∷ χs) c = applyCoercions-∀ χs c
applyCoercions-∀ (bind A ∷ χs) c =
  applyCoercions-∀ χs (renameᶜ (extᵗ suc) c)

applyCoercions-gen :
  ∀ χs A c →
  applyCoercions χs (gen A c) ≡
    gen (applyTys χs A) (applyCoercionUnderTyBinders χs c)
applyCoercions-gen [] A c = refl
applyCoercions-gen (keep ∷ χs) A c = applyCoercions-gen χs A c
applyCoercions-gen (bind B ∷ χs) A c =
  applyCoercions-gen χs (⇑ᵗ A) (renameᶜ (extᵗ suc) c)

applyCoercions-inst :
  ∀ χs A c →
  applyCoercions χs (inst A c) ≡
    inst (applyTys χs A) (applyCoercionUnderTyBinders χs c)
applyCoercions-inst [] A c = refl
applyCoercions-inst (keep ∷ χs) A c = applyCoercions-inst χs A c
applyCoercions-inst (bind B ∷ χs) A c =
  applyCoercions-inst χs (⇑ᵗ A) (renameᶜ (extᵗ suc) c)

applyTerms-cast :
  ∀ χs M c →
  applyTerms χs (M ⟨ c ⟩) ≡ applyTerms χs M ⟨ applyCoercions χs c ⟩
applyTerms-cast [] M c = refl
applyTerms-cast (keep ∷ χs) M c = applyTerms-cast χs M c
applyTerms-cast (bind A ∷ χs) M c =
  applyTerms-cast χs (⇑ᵗᵐ M) (⇑ᶜ c)

applyTerms-cast-dual :
  ∀ χs M c →
  applyTerms χs (M ⟨ - c ⟩) ≡
    applyTerms χs M ⟨ - applyCoercions χs c ⟩
applyTerms-cast-dual χs M c =
  trans (applyTerms-cast χs M (- c))
    (cong (λ d → applyTerms χs M ⟨ d ⟩) (applyCoercions-dual χs c))

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

shiftStoreChange : StoreChange → StoreChange
shiftStoreChange keep = keep
shiftStoreChange (bind A) = bind (⇑ᵗ A)

shiftable-⇑ᵗᵐ :
  ∀ {χ M} →
  Shiftable χ M →
  Shiftable (shiftStoreChange χ) (⇑ᵗᵐ M)
shiftable-⇑ᵗᵐ shift-keep = shift-keep
shiftable-⇑ᵗᵐ (shift-bind noM) =
  shift-bind (renameᵗᵐ-preserves-No• suc noM)

＇-injective :
  ∀ {X Y : TyVar} →
  _≡_ {A = Ty} (＇ X) (＇ Y) →
  X ≡ Y
＇-injective refl = refl

‵-injective :
  ∀ {ι ι′ : Base} →
  _≡_ {A = Ty} (‵ ι) (‵ ι′) →
  ι ≡ ι′
‵-injective refl = refl

⇒-injective-left :
  ∀ {A B C D} →
  A ⇒ B ≡ C ⇒ D →
  A ≡ C
⇒-injective-left refl = refl

⇒-injective-right :
  ∀ {A B C D} →
  A ⇒ B ≡ C ⇒ D →
  B ≡ D
⇒-injective-right refl = refl

∀-injective :
  ∀ {A B : Ty} →
  `∀ A ≡ `∀ B →
  A ≡ B
∀-injective refl = refl

RenameInjective : Renameᵗ → Set
RenameInjective ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

extᵗ-injective :
  ∀ {ρ} →
  RenameInjective ρ →
  RenameInjective (extᵗ ρ)
extᵗ-injective inj {zero} {zero} eq = refl
extᵗ-injective inj {zero} {suc Y} ()
extᵗ-injective inj {suc X} {zero} ()
extᵗ-injective inj {suc X} {suc Y} eq =
  cong suc (inj (suc-injective eq))

renameᵗ-injective :
  ∀ {ρ A B} →
  RenameInjective ρ →
  renameᵗ ρ A ≡ renameᵗ ρ B →
  A ≡ B
renameᵗ-injective {A = ＇ X} {B = ＇ Y} inj eq =
  cong ＇_ (inj (＇-injective eq))
renameᵗ-injective {A = ＇ X} {B = ‵ ι} inj ()
renameᵗ-injective {A = ＇ X} {B = ★} inj ()
renameᵗ-injective {A = ＇ X} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ＇ X} {B = `∀ B} inj ()
renameᵗ-injective {A = ‵ ι} {B = ＇ X} inj ()
renameᵗ-injective {A = ‵ ι} {B = ‵ ι′} inj eq =
  cong ‵_ (‵-injective eq)
renameᵗ-injective {A = ‵ ι} {B = ★} inj ()
renameᵗ-injective {A = ‵ ι} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ‵ ι} {B = `∀ B} inj ()
renameᵗ-injective {A = ★} {B = ＇ X} inj ()
renameᵗ-injective {A = ★} {B = ‵ ι} inj ()
renameᵗ-injective {A = ★} {B = ★} inj eq = refl
renameᵗ-injective {A = ★} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ★} {B = `∀ B} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ＇ X} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ‵ ι} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ★} inj ()
renameᵗ-injective {A = A ⇒ B} {B = C ⇒ D} inj eq =
  cong₂ _⇒_
    (renameᵗ-injective inj (⇒-injective-left eq))
    (renameᵗ-injective inj (⇒-injective-right eq))
renameᵗ-injective {A = A ⇒ B} {B = `∀ C} inj ()
renameᵗ-injective {A = `∀ A} {B = ＇ X} inj ()
renameᵗ-injective {A = `∀ A} {B = ‵ ι} inj ()
renameᵗ-injective {A = `∀ A} {B = ★} inj ()
renameᵗ-injective {A = `∀ A} {B = B ⇒ C} inj ()
renameᵗ-injective {A = `∀ A} {B = `∀ B} inj eq =
  cong `∀ (renameᵗ-injective (extᵗ-injective inj) (∀-injective eq))

pure-rename-step-⇑ᵗᵐ :
  ∀ {M N} →
  M —→ N →
  ∃[ N′ ] (⇑ᵗᵐ M —→ N′)
pure-rename-step-⇑ᵗᵐ δ-⊕ =
  _ , δ-⊕
pure-rename-step-⇑ᵗᵐ (β vV) =
  _ , β (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-Λ• vV) =
  _ , β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vV)
pure-rename-step-⇑ᵗᵐ (β-∀• vV) =
  _ , β-∀• (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-gen• vV) =
  _ , β-gen• (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-id vV) =
  _ , β-id (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-seq vV) =
  _ , β-seq (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-↦ vV vW) =
  _ , β-↦ (renameᵗᵐ-preserves-Value suc vV)
           (renameᵗᵐ-preserves-Value suc vW)
pure-rename-step-⇑ᵗᵐ (β-inst vV) =
  _ , β-inst (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (tag-untag-ok vV) =
  _ , tag-untag-ok (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (tag-untag-bad vV G≢H) =
  _ , tag-untag-bad (renameᵗᵐ-preserves-Value suc vV)
                    (λ eq → G≢H (renameᵗ-injective suc-injective eq))
pure-rename-step-⇑ᵗᵐ (seal-unseal vV) =
  _ , seal-unseal (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ blame-·₁ =
  _ , blame-·₁
pure-rename-step-⇑ᵗᵐ (blame-·₂ vV) =
  _ , blame-·₂ (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ blame-• =
  _ , blame-•
pure-rename-step-⇑ᵗᵐ blame-⟨⟩ =
  _ , blame-⟨⟩
pure-rename-step-⇑ᵗᵐ blame-⊕₁ =
  _ , blame-⊕₁
pure-rename-step-⇑ᵗᵐ (blame-⊕₂ vV) =
  _ , blame-⊕₂ (renameᵗᵐ-preserves-Value suc vV)

type-rename-step-⇑ᵗᵐ-exact :
  ∀ {M N χ} →
  M —→[ χ ] N →
  ∃[ N′ ] (⇑ᵗᵐ M —→[ shiftStoreChange χ ] N′)
type-rename-step-⇑ᵗᵐ-exact (pure-step red)
    with pure-rename-step-⇑ᵗᵐ red
type-rename-step-⇑ᵗᵐ-exact (pure-step red)
    | N′ , red′ =
  N′ , pure-step red′
type-rename-step-⇑ᵗᵐ-exact (ν-step vV noV) =
  _ , ν-step (renameᵗᵐ-preserves-Value suc vV)
             (renameᵗᵐ-preserves-No• suc noV)
type-rename-step-⇑ᵗᵐ-exact (ξ-·₁ red shiftM)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-·₁ red shiftM)
    | L′ , red′ =
  _ , ξ-·₁ red′ (shiftable-⇑ᵗᵐ shiftM)
type-rename-step-⇑ᵗᵐ-exact (ξ-·₂ vV shiftV red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-·₂ vV shiftV red)
    | M′ , red′ =
  _ , ξ-·₂ (renameᵗᵐ-preserves-Value suc vV)
             (shiftable-⇑ᵗᵐ shiftV)
             red′
type-rename-step-⇑ᵗᵐ-exact (ξ-⟨⟩ red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-⟨⟩ red)
    | M′ , red′ =
  _ , ξ-⟨⟩ red′
type-rename-step-⇑ᵗᵐ-exact (ξ-ν red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-ν red)
    | L′ , red′ =
  _ , ξ-ν red′
type-rename-step-⇑ᵗᵐ-exact blame-ν =
  _ , blame-ν
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₁ red shiftM)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₁ red shiftM)
    | L′ , red′ =
  _ , ξ-⊕₁ red′ (shiftable-⇑ᵗᵐ shiftM)
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₂ vV shiftV red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₂ vV shiftV red)
    | M′ , red′ =
  _ , ξ-⊕₂ (renameᵗᵐ-preserves-Value suc vV)
             (shiftable-⇑ᵗᵐ shiftV)
             red′

type-rename-step-⇑ᵗᵐ :
  ∀ {M N χ} →
  M —→[ χ ] N →
  ∃[ χ′ ] ∃[ N′ ] (⇑ᵗᵐ M —→[ χ′ ] N′)
type-rename-step-⇑ᵗᵐ red =
  shiftStoreChange _ , type-rename-step-⇑ᵗᵐ-exact red

↠-trans :
  ∀ {M N P χs χs′} →
  M —↠[ χs ] N →
  N —↠[ χs′ ] P →
  M —↠[ χs ++ χs′ ] P
↠-trans ↠-refl N↠P = N↠P
↠-trans (↠-step M→N N↠P) P↠Q = ↠-step M→N (↠-trans N↠P P↠Q)

applyFrameChanges :
  ∀ {Frame : Set} →
  (StoreChange → Frame → Frame) →
  StoreChanges →
  Frame →
  Frame
applyFrameChanges applyFrame [] F = F
applyFrameChanges applyFrame (χ ∷ χs) F =
  applyFrameChanges applyFrame χs (applyFrame χ F)

frame-↠ :
  ∀ {Frame : Set}
    (plug : Frame → Term → Term)
    (applyFrame : StoreChange → Frame → Frame) →
  (∀ {F M N χ} →
    M —→[ χ ] N →
    plug F M —→[ χ ] plug (applyFrame χ F) N) →
  ∀ {F M N χs} →
  M —↠[ χs ] N →
  plug F M —↠[ χs ] plug (applyFrameChanges applyFrame χs F) N
frame-↠ plug applyFrame lift-step ↠-refl = ↠-refl
frame-↠ plug applyFrame lift-step (↠-step red reds) =
  ↠-step (lift-step red) (frame-↠ plug applyFrame lift-step reds)

shiftable-No• :
  ∀ {χ M} →
  No• M →
  Shiftable χ M
shiftable-No• {χ = keep} noM = shift-keep
shiftable-No• {χ = bind A} noM = shift-bind noM

No•Frame : Set
No•Frame = Σ Term No•

applyNo•Frame : StoreChange → No•Frame → No•Frame
applyNo•Frame χ (M , noM) =
  applyTerm χ M , applyTerm-preserves-No• χ noM

applyNo•Frame-term :
  ∀ χs F →
  proj₁ (applyFrameChanges applyNo•Frame χs F) ≡
    applyTerms χs (proj₁ F)
applyNo•Frame-term [] F = refl
applyNo•Frame-term (χ ∷ χs) (M , noM) =
  applyNo•Frame-term χs
    (applyTerm χ M , applyTerm-preserves-No• χ noM)

ValueFrame : Set
ValueFrame = Σ Term (λ V → Value V × No• V)

applyValueFrame : StoreChange → ValueFrame → ValueFrame
applyValueFrame χ (V , vV , noV) =
  applyTerm χ V ,
  applyTerm-preserves-Value χ vV ,
  applyTerm-preserves-No• χ noV

applyValueFrame-term :
  ∀ χs F →
  proj₁ (applyFrameChanges applyValueFrame χs F) ≡
    applyTerms χs (proj₁ F)
applyValueFrame-term [] F = refl
applyValueFrame-term (χ ∷ χs) (V , vV , noV) =
  applyValueFrame-term χs
    (applyTerm χ V ,
     applyTerm-preserves-Value χ vV ,
     applyTerm-preserves-No• χ noV)

·₁-↠ :
  ∀ {L W M χs} →
  No• M →
  L —↠[ χs ] W →
  L · M —↠[ χs ] W · applyTerms χs M
·₁-↠ {L = L} {W = W} {M = M} {χs = χs} noM L↠W =
  subst
    (λ M′ → L · M —↠[ χs ] W · M′)
    (applyNo•Frame-term χs (M , noM))
    (frame-↠
      (λ { (M′ , noM′) L′ → L′ · M′ })
      applyNo•Frame
      (λ { {F = M′ , noM′} red → ξ-·₁ red (shiftable-No• noM′) })
      {F = M , noM}
      L↠W)

·₂-↠ :
  ∀ {V M W χs} →
  Value V →
  No• V →
  M —↠[ χs ] W →
  V · M —↠[ χs ] applyTerms χs V · W
·₂-↠ {V = V} {M = M} {W = W} {χs = χs} vV noV M↠W =
  subst
    (λ V′ → V · M —↠[ χs ] V′ · W)
    (applyValueFrame-term χs (V , vV , noV))
    (frame-↠
      (λ { (V′ , vV′ , noV′) M′ → V′ · M′ })
      applyValueFrame
      (λ { {F = V′ , vV′ , noV′} red →
        ξ-·₂ vV′ (shiftable-No• noV′) red })
      {F = V , vV , noV}
      M↠W)

⊕₁-↠ :
  ∀ {L W M op χs} →
  No• M →
  L —↠[ χs ] W →
  L ⊕[ op ] M —↠[ χs ] W ⊕[ op ] applyTerms χs M
⊕₁-↠ {L = L} {W = W} {M = M} {op = op} {χs = χs} noM L↠W =
  subst
    (λ M′ → L ⊕[ op ] M —↠[ χs ] W ⊕[ op ] M′)
    (applyNo•Frame-term χs (M , noM))
    (frame-↠
      (λ { (M′ , noM′) L′ → L′ ⊕[ op ] M′ })
      applyNo•Frame
      (λ { {F = M′ , noM′} red → ξ-⊕₁ red (shiftable-No• noM′) })
      {F = M , noM}
      L↠W)

⊕₂-↠ :
  ∀ {V M W op χs} →
  Value V →
  No• V →
  M —↠[ χs ] W →
  V ⊕[ op ] M —↠[ χs ] applyTerms χs V ⊕[ op ] W
⊕₂-↠ {V = V} {M = M} {W = W} {op = op} {χs = χs} vV noV M↠W =
  subst
    (λ V′ → V ⊕[ op ] M —↠[ χs ] V′ ⊕[ op ] W)
    (applyValueFrame-term χs (V , vV , noV))
    (frame-↠
      (λ { (V′ , vV′ , noV′) M′ → V′ ⊕[ op ] M′ })
      applyValueFrame
      (λ { {F = V′ , vV′ , noV′} red →
        ξ-⊕₂ vV′ (shiftable-No• noV′) red })
      {F = V , vV , noV}
      M↠W)

cast-↠ :
  ∀ {M N c χs} →
  M —↠[ χs ] N →
  M ⟨ c ⟩ —↠[ χs ] N ⟨ applyCoercions χs c ⟩
cast-↠ {c = c} ↠-refl = ↠-refl
cast-↠ {c = c} (↠-step {χ = χ} red reds) =
  ↠-step (ξ-⟨⟩ red) (cast-↠ {c = applyCoercion χ c} reds)

cast-dual-↠ :
  ∀ {M N c χs} →
  M —↠[ χs ] N →
  M ⟨ - c ⟩ —↠[ χs ] N ⟨ - applyCoercions χs c ⟩
cast-dual-↠ {M = M} {N = N} {c = c} {χs = χs} M↠N =
  subst (λ d → M ⟨ - c ⟩ —↠[ χs ] N ⟨ d ⟩)
        (applyCoercions-dual χs c)
        (cast-↠ {c = - c} M↠N)

ν-↠ :
  ∀ {M N A c χs} →
  M —↠[ χs ] N →
  ν A M c —↠[ χs ]
    ν (applyTys χs A) N (applyCoercionUnderTyBinders χs c)
ν-↠ {A = A} {c = c} ↠-refl = ↠-refl
ν-↠ {A = A} {c = c} (↠-step {χ = χ} red reds) =
  ↠-step (ξ-ν red)
    (ν-↠ {A = applyTy χ A} {c = applyCoercionUnderTyBinder χ c} reds)

{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}

module proof.Catchup where

-- File Charter:
--   * Home for the GTSF catchup lemma used by the dynamic gradual guarantee.
--   * Uses `proof.CatchupStore` for the stable store-narrowing append helper
--     `combineStoreNrw` and its source-store algebra.
--   * The intended proof follows the cambridge25 "Catchup Lemma" section.
--   * The main statement is the strengthened Agda form needed by DGG: closed
--     source relation, an explicit source value after catchup, and de Bruijn
--     weakening of the unchanged target term/coercion index by the emitted
--     store changes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (≤-refl; m<n⇒m<1+n; suc-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Store using (StoreIncl; StoreIncl-cons; StoreIncl-drop; StoreWfAt)
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import TypeCheck using (value?)
open import Primitives using (κℕ; constTy)
open import proof.NarrowWidenProperties
  using
    ( StoreDetWf
    ; StoreDetWf-⟰ᵗ
    ; StoreUnique
    ; WfTyˢ-⇑ᵗ
    ; WfTyˢ-store-weaken
    ; narrowing-determinedᵐ
    ; widening-determinedᵐ
    ; narrow-⇑ᵗ-ᶜ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤
    ; narrow-⇑ᵗ-any
    ; narrow-drop-star-var
    ; narrow-drop-star
    ; srcStoreⁿ-⊒ˢ
    ; srcStoreⁿ-⇑ˢ
    ; occurs-one-⇑⇑-false
    ; srcStoreⁿ-source-first-one-fresh
    ; WfTyˢ-rename
    ; narrowing-all-gen-overlap⊥
    ; ⇑ˢ-++
    ; ⊒ˢ-⇑ˢ
    ; ⊒ˢ-empty-⇑ˢ
    ; ⊒ˢ-empty-anyᵗ
    )
open import proof.CoercionProperties
  using
    ( coercion-src-tgtᵐ
    ; ModeRename
    ; renameᶜ-cong
    ; renameᶜ-compose
    ; renameᶜ-dual-normal
    ; renameᶜ-ext-suc-comm
    ; renameᶜ-left-inverse
    ; renameᶜ-open-commute
    ; renameᶜ-pred-suc
    ; renameᶜ-preserves-Inert
    ; src-renameᶜ
    ; tgt-renameᶜ
    )
open import proof.NuTermProperties
  using
    ( renameᵗᵐ-cong
    ; renameᵗᵐ-compose
    ; renameᵗᵐ-ext-suc-comm
    ; renameᵗᵐ-left-inverse
    ; renameᵗᵐ-open-commute
    ; renameᵗᵐ-pred-suc
    ; renameᵗᵐ-preserves-No•
    ; renameᵗᵐ-preserves-Value
    ; renameᵗᵐ-reflects-Value
    )
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; predᵗ
    ; rename-cong
    ; renameᵗ-compose
    ; renameᵗ-ext-suc-comm
    ; renameᵗ-pred-suc
    ; renameᵗ-preserves-WfTy
    ; renameStoreᵗ-compose
    )
open import proof.StoreProperties
  using
    ( StoreWfAt-cons
    ; StoreWfAt-rename
    )
open import proof.TermNarrowingProperties
  using
    ( neutral-blame
    ; neutral-source-no-value-target
    ; neutral-`
    ; neutral-·
    ; neutral-⊕
    ; cast-base-empty+
    ; cast-base-empty-
    ; cast-source-value-target-base-empty
    ; lambda-source-value-target-source-value
    ; nu-base-empty
    ; nu-source-value-target-base-empty
    ; remainder-cast
    ; remainder-nu
    ; RuntimeTypeApp
    ; renameᵗᵐ-preserves-RuntimeTypeApp
    ; runtime-type-app-source-no-value-target
    ; shifted-source-remainder
    ; type-app-source-no-value-target
    ; value?-none-no-value
    ; value-target-source-no-active
    ; value-target-source-safe
    )
open import proof.NuPreservation
  using
    ( runtime-⟨⟩
    ; runtime-ν
    ; value-runtime-No•
    )
open import proof.ReductionProperties
  using
    ( applyCoercions
    ; applyCoercions-empty-id
    ; applyCoercions-++
    ; applyCoercions-⇑ᶜ
    ; applyCoercions-dual
    ; applyCoercions-last-bind
    ; applyCoercions-last-bind-open
    ; applyCoercions-open
    ; applyCoercions-∀
    ; applyCoercions-gen
    ; applyCoercions-inst
    ; applyCoercionUnderTyBinders
    ; applyCoercionUnderTyBinders-++
    ; allKeep-applyCoercionUnderTyBinders-id
    ; applyCoercionUnderTyBinders-preserves-Inert
    ; applyStores-empty-id
    ; applyStores-last-bind
    ; applyTerms-++
    ; applyTerms-empty-id
    ; applyTerms-last-bind
    ; applyTerms-last-bind-open
    ; applyTerms-open
    ; applyTerms-Λ
    ; applyTerms-ν
    ; applyTerms-•
    ; applyTerms-cast
    ; applyTerms-cast-dual
    ; applyTermsUnderTyBinders
    ; applyTermsUnderTyBinders-++
    ; allKeep-applyTerms-id
    ; allKeep-applyTermsUnderTyBinders-id
    ; applyTyVars
    ; applyTyCtxs-empty-id
    ; applyTyCtxs-last-bind
    ; applyTyCtxs-suc
    ; applyTys-empty-id
    ; applyTys-⇑ᵗ
    ; applyTys-∀
    ; applyTysUnderTyBinders
    ; applyTys-last-bind
    ; applyTys-★
    ; AllKeep
    ; allKeep-applyCoercions-id
    ; allKeep-applyTyCtxs-id
    ; allKeep-applyStores-id
    ; allKeep-applyTys-id
    ; applyStores-++
    ; RenameInjective
    ; ⟰ᵗ-empty-inv
    ; applyTyCtxs-++
    ; storeHead-∷≡
    ; storeTail-∷≡
    ; storeChangesLastBind
    ; StoreChangesLastBind
    ; no-bind
    ; last-bind
    ; allKeep-ν-no-value
    ; pure-pred-↠-shifted-value
    ; safe-allKeep-value-image
    ; applyTyCtxs-≤
    ; ↠-trans
    ; ↠-split-last-bind
    ; cast-↠
    ; cast-dual-↠
    ; applyCoercionUnderTyBinders-⇑ᶜ
    ; ν-↠
    ; shiftStore
    ; CatchupSafe
    ; safe-allKeep-bind-pred-↠-shifted
    ; shiftStore-empty
    ; shiftStore-empty-inv
    ; shiftStore-cons
    ; shiftStore-⟰ᵗ
    )
open import proof.CatchupStore
  using
    ( combineStoreNrw
    ; combineStoreNrw-⇑ˢ
    ; combineStoreNrw-assoc
    ; combineStoreNrw-empty-⊒ˢ
    ; combineStoreNrw-applyStores
    ; combineStoreNrw-applyStores-store
    )

⊒ˢ-empty-source-head-star :
  ∀ {Δ π α A Σ} →
  Δ ⊢ π ꞉ (α , A) ∷ Σ ⊒ˢ [] →
  A ≡ ★
⊒ˢ-empty-source-head-star (⊒ˢ-left π⊒) = refl

data SourceStarOnly : StoreNrw → Set where
  source-star-[] :
    SourceStarOnly []
  source-star-∷ :
    ∀ {X π} →
    SourceStarOnly π →
    SourceStarOnly ((⊒ X ꞉=☆) ∷ π)

-- Attempt 71.  The empty-target store evidence really does force the emitted
-- prefix to contain only source-star entries.  This rules out a target-side
-- case split as the missing ingredient for the `⊒Λ` last-bind branch: the
-- unsolved step is exchanging the outer target-only binder with this
-- source-star prefix while lowering the de Bruijn indices.
⊒ˢ-empty-source-star-only :
  ∀ {Δ π Σ} →
  Δ ⊢ π ꞉ Σ ⊒ˢ [] →
  SourceStarOnly π
⊒ˢ-empty-source-star-only ⊒ˢ-nil = source-star-[]
⊒ˢ-empty-source-star-only (⊒ˢ-left π⊒) =
  source-star-∷ (⊒ˢ-empty-source-star-only π⊒)

⇑ᵗ-★-inv :
  ∀ {A} →
  ⇑ᵗ A ≡ ★ →
  A ≡ ★
⇑ᵗ-★-inv {A = ＇ X} ()
⇑ᵗ-★-inv {A = ‵ ι} ()
⇑ᵗ-★-inv {A = ★} refl = refl
⇑ᵗ-★-inv {A = A ⇒ B} ()
⇑ᵗ-★-inv {A = `∀ A} ()

last-bind-empty-target-star :
  ∀ {Δ π Π χs A keeps} →
  AllKeep keeps →
  Π ≡ applyStores (χs ++ bind A ∷ keeps) [] →
  Δ ⊢ π ꞉ Π ⊒ˢ [] →
  A ≡ ★
last-bind-empty-target-star {χs = χs} {A = A} {keeps = keeps}
    keeps-ok Π≡ π⊒ =
  ⇑ᵗ-★-inv
    (⊒ˢ-empty-source-head-star
      (subst
        (λ Π → _ ⊢ _ ꞉ Π ⊒ˢ [])
        (trans Π≡ (applyStores-last-bind χs A keeps keeps-ok []))
        π⊒))

last-bind-empty-target-left-tail :
  ∀ {Δ π Π χs A keeps} →
  AllKeep keeps →
  Π ≡ applyStores (χs ++ bind A ∷ keeps) [] →
  Δ ⊢ π ꞉ Π ⊒ˢ [] →
  ∃[ X ] ∃[ π₀ ] (π ≡ (⊒ X ꞉=☆) ∷ π₀) ×
    (X ≡ zero) ×
    Δ ⊢ π₀ ꞉ ⟰ᵗ (applyStores χs []) ⊒ˢ []
last-bind-empty-target-left-tail {χs = χs} {A = A} {keeps = keeps}
    keeps-ok Π≡ ⊒ˢ-nil
    with trans Π≡ (applyStores-last-bind χs A keeps keeps-ok [])
last-bind-empty-target-left-tail keeps-ok Π≡ ⊒ˢ-nil | ()
last-bind-empty-target-left-tail {χs = χs} {A = A} {keeps = keeps}
    keeps-ok Π≡ (⊒ˢ-left {X = X} {σ = π₀} π⊒) =
  let
    full≡ = trans Π≡ (applyStores-last-bind χs A keeps keeps-ok [])
  in
  X , π₀ , refl ,
  cong proj₁ (storeHead-∷≡ full≡) ,
  subst
    (λ Σ → _ ⊢ π₀ ꞉ Σ ⊒ˢ [])
    (storeTail-∷≡ full≡)
    π⊒

⊒ˢ-empty-shift-inv :
  ∀ {Δ π Σ} →
  Δ ⊢ π ꞉ ⟰ᵗ Σ ⊒ˢ [] →
  ∃[ π′ ] (π ≡ ⇑ˢ π′) × Δ ⊢ π′ ꞉ Σ ⊒ˢ []
⊒ˢ-empty-shift-inv {Σ = []} ⊒ˢ-nil =
  [] , refl , ⊒ˢ-nil
⊒ˢ-empty-shift-inv {Σ = (X , ＇ Y) ∷ Σ} ()
⊒ˢ-empty-shift-inv {Σ = (X , ‵ ι) ∷ Σ} ()
⊒ˢ-empty-shift-inv {Σ = (X , ★) ∷ Σ} (⊒ˢ-left π⊒)
    with ⊒ˢ-empty-shift-inv π⊒
⊒ˢ-empty-shift-inv {Σ = (X , ★) ∷ Σ} (⊒ˢ-left π⊒)
    | π′ , π≡ , π′⊒ =
  (⊒ X ꞉=☆) ∷ π′ , cong ((⊒ suc X ꞉=☆) ∷_) π≡ ,
  ⊒ˢ-left π′⊒
⊒ˢ-empty-shift-inv {Σ = (X , A ⇒ B) ∷ Σ} ()
⊒ˢ-empty-shift-inv {Σ = (X , `∀ A) ∷ Σ} ()

last-bind-empty-target-lowered-tail :
  ∀ {Δ π Π χs A keeps} →
  AllKeep keeps →
  Π ≡ applyStores (χs ++ bind A ∷ keeps) [] →
  Δ ⊢ π ꞉ Π ⊒ˢ [] →
  ∃[ π₀ ] (π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀) ×
    Δ ⊢ π₀ ꞉ applyStores χs [] ⊒ˢ []
last-bind-empty-target-lowered-tail {χs = χs} {A = A} {keeps = keeps}
    keeps-ok Π≡ π⊒
    with last-bind-empty-target-left-tail
      {χs = χs} {A = A} {keeps = keeps} keeps-ok Π≡ π⊒
last-bind-empty-target-lowered-tail {χs = χs} keeps-ok Π≡ π⊒
    | X , πtail , π≡ , X≡0 , πtail⊒
    with ⊒ˢ-empty-shift-inv {Σ = applyStores χs []} πtail⊒
last-bind-empty-target-lowered-tail {χs = χs} keeps-ok Π≡ π⊒
    | X , πtail , π≡ , refl , πtail⊒
    | π₀ , πtail≡ , π₀⊒ =
  π₀ , trans π≡ (cong ((⊒ zero ꞉=☆) ∷_) πtail≡) , π₀⊒

combineStoreNrw-source-star-shifted-tail :
  ∀ π σ →
  combineStoreNrw ((⊒ zero ꞉=☆) ∷ ⇑ˢ π) σ ≡
    (⊒ zero ꞉=☆) ∷ ⇑ˢ (combineStoreNrw π σ)
combineStoreNrw-source-star-shifted-tail π σ =
  cong ((⊒ zero ꞉=☆) ∷_) (sym (combineStoreNrw-⇑ˢ π σ))

last-bind-source-first-body :
  ∀ {Δ σ χs A keeps W V p π π₀} →
  AllKeep keeps →
  π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀ →
  Δ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms (χs ++ bind A ∷ keeps) V
      ∶ applyCoercions (χs ++ bind A ∷ keeps) p →
  Δ ∣ (⊒ zero ꞉=☆) ∷
      ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V) ∶ ⇑ᶜ (applyCoercions χs p)
last-bind-source-first-body {σ = σ} {χs = χs} {A = A}
    {keeps = keeps} {V = V} {p = p} {π = π} {π₀ = π₀}
    keeps-ok π≡ body =
  subst
    (λ c → _ ∣ _ ∣ [] ⊢ _ ⊒ ⇑ᵗᵐ (applyTerms χs V) ∶ c)
    (applyCoercions-last-bind χs A keeps keeps-ok p)
    (subst
      (λ T → _ ∣ _ ∣ [] ⊢ _ ⊒ T ∶
        applyCoercions (χs ++ bind A ∷ keeps) p)
      (applyTerms-last-bind χs A keeps keeps-ok V)
      (subst
        (λ σ₀ → _ ∣ σ₀ ∣ [] ⊢ _ ⊒
          applyTerms (χs ++ bind A ∷ keeps) V ∶
          applyCoercions (χs ++ bind A ∷ keeps) p)
        (trans
          (cong
            (λ π′ → combineStoreNrw π′
              ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))
            π≡)
          (combineStoreNrw-source-star-shifted-tail π₀
            ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)))
        body))

source-first-body-empty-tail :
  ∀ {Δ σ π₀ W V p} →
  π₀ ≡ [] →
  Δ ∣ (⊒ zero ꞉=☆) ∷
      ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ V ∶ ⇑ᶜ p →
  Δ ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ V ∶ ⇑ᶜ p
source-first-body-empty-tail refl body = body

last-bind-pred-reduction :
  ∀ {χs Aχ keeps N P Q W} →
  AllKeep χs →
  AllKeep keeps →
  Aχ ≡ ★ →
  CatchupSafe (⇑ᵗᵐ N) →
  (⇑ᵗᵐ N —↠[ χs ] P) →
  (P —→[ bind Aχ ] Q) →
  (Q —↠[ keeps ] W) →
  Value W →
  N —↠[ χs ++ bind ★ ∷ keeps ] renameᵗᵐ predᵗ W
last-bind-pred-reduction {χs = χs} {Aχ = Aχ} {keeps = keeps}
    keepsχ keepsTail Aχ≡★ safe⇑N ⇑N↠P P→Q Q↠W vW =
  subst
    (λ X → _ —↠[ χs ++ bind X ∷ keeps ] _)
    (cong (renameᵗ predᵗ) Aχ≡★)
    (safe-allKeep-bind-pred-↠-shifted
      safe⇑N keepsχ keepsTail ⇑N↠P P→Q Q↠W vW)

⊒ˢ-empty-empty-nil :
  ∀ {Δ π} →
  Δ ⊢ π ꞉ [] ⊒ˢ [] →
  π ≡ []
⊒ˢ-empty-empty-nil ⊒ˢ-nil = refl

allKeep-empty-target-nil :
  ∀ {Δ π Π Π′ χs} →
  AllKeep χs →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ ⊢ π ꞉ Π ⊒ˢ Π′ →
  π ≡ []
allKeep-empty-target-nil {χs = χs} keeps Π≡ Π′≡ π⊒ =
  ⊒ˢ-empty-empty-nil
    (subst
      (λ Π₀ → _ ⊢ _ ꞉ Π₀ ⊒ˢ [])
      (trans Π≡ (allKeep-applyStores-id keeps []))
      (subst (λ Π₀ → _ ⊢ _ ꞉ _ ⊒ˢ Π₀) Π′≡ π⊒))

last-bind-source-first-body-empty-tail :
  ∀ {Δ σ χs A keeps W V p π π₀ Π Π′} →
  AllKeep χs →
  AllKeep keeps →
  π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ ⊢ π₀ ꞉ Π ⊒ˢ Π′ →
  Δ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms (χs ++ bind A ∷ keeps) V
      ∶ applyCoercions (χs ++ bind A ∷ keeps) p →
  Δ ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V) ∶ ⇑ᶜ (applyCoercions χs p)
last-bind-source-first-body-empty-tail
    {σ = σ} {χs = χs} {A = A} {keeps = keeps}
    {V = V} {p = p} {π₀ = π₀}
    keepsχ keepsTail π≡ Π≡ Π′≡ π₀⊒ body =
  source-first-body-empty-tail
    (allKeep-empty-target-nil keepsχ Π≡ Π′≡ π₀⊒)
    (last-bind-source-first-body
      {σ = σ} {χs = χs} {A = A} {keeps = keeps}
      {V = V} {p = p} {π₀ = π₀}
      keepsTail π≡ body)

allKeep-under-binder-value-id :
  ∀ {χs V} →
  AllKeep χs →
  Value V →
  applyTermsUnderTyBinders χs V ≡ V
allKeep-under-binder-value-id keeps vV =
  allKeep-applyTermsUnderTyBinders-id keeps _

allKeep-gen-under-binder-coercion-id :
  ∀ {χs Δ Σ A B p} →
  AllKeep χs →
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  applyCoercionUnderTyBinders χs p ≡ p
allKeep-gen-under-binder-coercion-id keeps pᶜ =
  allKeep-applyCoercionUnderTyBinders-id keeps _

applyTermsUnderTyBinders-last-bind :
  ∀ {χs A keeps M} →
  AllKeep keeps →
  applyTermsUnderTyBinders (χs ++ bind A ∷ keeps) M ≡
    renameᵗᵐ (extᵗ suc) (applyTermsUnderTyBinders χs M)
applyTermsUnderTyBinders-last-bind {χs = χs} {A = A} {keeps = keeps}
    {M = M} keeps-ok =
  trans
    (applyTermsUnderTyBinders-++ χs (bind A ∷ keeps) M)
    (allKeep-applyTermsUnderTyBinders-id keeps-ok
      (renameᵗᵐ (extᵗ suc) (applyTermsUnderTyBinders χs M)))

applyCoercionUnderTyBinders-last-bind :
  ∀ {χs A keeps p} →
  AllKeep keeps →
  applyCoercionUnderTyBinders (χs ++ bind A ∷ keeps) p ≡
    renameᶜ (extᵗ suc) (applyCoercionUnderTyBinders χs p)
applyCoercionUnderTyBinders-last-bind
    {χs = χs} {A = A} {keeps = keeps} {p = p} keeps-ok =
  trans
    (applyCoercionUnderTyBinders-++ χs (bind A ∷ keeps) p)
    (allKeep-applyCoercionUnderTyBinders-id keeps-ok
      (renameᶜ (extᵗ suc) (applyCoercionUnderTyBinders χs p)))

swap01ᵗ : Renameᵗ
swap01ᵗ zero = suc zero
swap01ᵗ (suc zero) = zero
swap01ᵗ (suc (suc X)) = suc (suc X)

swap01ᵗ-after-suc :
  ∀ X →
  swap01ᵗ (suc X) ≡ extᵗ suc X
swap01ᵗ-after-suc zero = refl
swap01ᵗ-after-suc (suc X) = refl

swap01ᵗ-after-suc-suc :
  ∀ X →
  swap01ᵗ (suc (suc X)) ≡ suc (suc X)
swap01ᵗ-after-suc-suc X = refl

swap01ᵗ-involutive :
  ∀ X →
  swap01ᵗ (swap01ᵗ X) ≡ X
swap01ᵗ-involutive zero = refl
swap01ᵗ-involutive (suc zero) = refl
swap01ᵗ-involutive (suc (suc X)) = refl

swap01ᵗ-injective :
  RenameInjective swap01ᵗ
swap01ᵗ-injective {zero} {zero} refl = refl
swap01ᵗ-injective {zero} {suc zero} ()
swap01ᵗ-injective {zero} {suc (suc Y)} ()
swap01ᵗ-injective {suc zero} {zero} ()
swap01ᵗ-injective {suc zero} {suc zero} refl = refl
swap01ᵗ-injective {suc zero} {suc (suc Y)} ()
swap01ᵗ-injective {suc (suc X)} {zero} ()
swap01ᵗ-injective {suc (suc X)} {suc zero} ()
swap01ᵗ-injective {suc (suc X)} {suc (suc .X)} refl = refl

TyRenameWf-swap01 :
  ∀ {Δ} →
  TyRenameWf (suc (suc Δ)) (suc (suc Δ)) swap01ᵗ
TyRenameWf-swap01 {X = zero} z<s = s<s z<s
TyRenameWf-swap01 {X = suc zero} (s<s z<s) = z<s
TyRenameWf-swap01 {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s (s<s X<Δ)

renameᵗ-swap01-⇑ :
  ∀ A →
  renameᵗ swap01ᵗ (⇑ᵗ A) ≡ renameᵗ (extᵗ suc) A
renameᵗ-swap01-⇑ A =
  trans (renameᵗ-compose suc swap01ᵗ A)
    (rename-cong swap01ᵗ-after-suc A)

renameᶜ-swap01-⇑ :
  ∀ c →
  renameᶜ swap01ᵗ (⇑ᶜ c) ≡ renameᶜ (extᵗ suc) c
renameᶜ-swap01-⇑ c =
  trans (renameᶜ-compose suc swap01ᵗ c)
    (renameᶜ-cong swap01ᵗ-after-suc c)

renameᵗᵐ-swap01-⇑ :
  ∀ M →
  renameᵗᵐ swap01ᵗ (⇑ᵗᵐ M) ≡ renameᵗᵐ (extᵗ suc) M
renameᵗᵐ-swap01-⇑ M =
  trans (renameᵗᵐ-compose suc swap01ᵗ M)
    (renameᵗᵐ-cong swap01ᵗ-after-suc M)

renameᵗ-swap01-⇑⇑ :
  ∀ A →
  renameᵗ swap01ᵗ (⇑ᵗ (⇑ᵗ A)) ≡ ⇑ᵗ (⇑ᵗ A)
renameᵗ-swap01-⇑⇑ A =
  trans
    (cong (renameᵗ swap01ᵗ) (renameᵗ-compose suc suc A))
    (trans
      (renameᵗ-compose (λ X → suc (suc X)) swap01ᵗ A)
      (trans
        (rename-cong swap01ᵗ-after-suc-suc A)
        (sym (renameᵗ-compose suc suc A))))

renameᶜ-swap01-⇑⇑ :
  ∀ c →
  renameᶜ swap01ᵗ (⇑ᶜ (⇑ᶜ c)) ≡ ⇑ᶜ (⇑ᶜ c)
renameᶜ-swap01-⇑⇑ c =
  trans
    (cong (renameᶜ swap01ᵗ) (renameᶜ-compose suc suc c))
    (trans
      (renameᶜ-compose (λ X → suc (suc X)) swap01ᵗ c)
      (trans
        (renameᶜ-cong swap01ᵗ-after-suc-suc c)
        (sym (renameᶜ-compose suc suc c))))

renameᵗᵐ-swap01-⇑⇑ :
  ∀ M →
  renameᵗᵐ swap01ᵗ (⇑ᵗᵐ (⇑ᵗᵐ M)) ≡ ⇑ᵗᵐ (⇑ᵗᵐ M)
renameᵗᵐ-swap01-⇑⇑ M =
  trans
    (cong (renameᵗᵐ swap01ᵗ) (renameᵗᵐ-compose suc suc M))
    (trans
      (renameᵗᵐ-compose (λ X → suc (suc X)) swap01ᵗ M)
      (trans
        (renameᵗᵐ-cong swap01ᵗ-after-suc-suc M)
        (sym (renameᵗᵐ-compose suc suc M))))

raise0ᵗ : Renameᵗ
raise0ᵗ X = suc (predᵗ X)

merge01ᵗ : Renameᵗ
merge01ᵗ zero = zero
merge01ᵗ (suc zero) = zero
merge01ᵗ (suc (suc X)) = suc (suc X)

merge01ᵗ-after-suc-suc :
  ∀ X →
  merge01ᵗ (suc (suc X)) ≡ suc (suc X)
merge01ᵗ-after-suc-suc X = refl

TyRenameWf-merge01 :
  ∀ {Δ} →
  TyRenameWf (suc (suc Δ)) (suc (suc Δ)) merge01ᵗ
TyRenameWf-merge01 {X = zero} z<s = z<s
TyRenameWf-merge01 {X = suc zero} (s<s z<s) = z<s
TyRenameWf-merge01 {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s (s<s X<Δ)

merge01ᵗ-after-suc :
  ∀ X →
  merge01ᵗ (suc X) ≡ extᵗ suc X
merge01ᵗ-after-suc zero = refl
merge01ᵗ-after-suc (suc X) = refl

close01ᵗ : Renameᵗ
close01ᵗ zero = zero
close01ᵗ (suc zero) = zero
close01ᵗ (suc (suc X)) = suc (suc (suc X))

close01-open0 :
  ∀ X →
  singleRenameᵗ zero (close01ᵗ X) ≡ merge01ᵗ X
close01-open0 zero = refl
close01-open0 (suc zero) = refl
close01-open0 (suc (suc X)) = refl

close01-open1 :
  ∀ X →
  singleRenameᵗ (suc zero) (close01ᵗ X) ≡ raise0ᵗ X
close01-open1 zero = refl
close01-open1 (suc zero) = refl
close01-open1 (suc (suc X)) = refl

renameᵗ-close01-open0 :
  ∀ A →
  renameᵗ (singleRenameᵗ zero) (renameᵗ close01ᵗ A) ≡
  renameᵗ merge01ᵗ A
renameᵗ-close01-open0 A =
  trans (renameᵗ-compose close01ᵗ (singleRenameᵗ zero) A)
    (rename-cong close01-open0 A)

renameᶜ-close01-open0 :
  ∀ c →
  renameᶜ (singleRenameᵗ zero) (renameᶜ close01ᵗ c) ≡
  renameᶜ merge01ᵗ c
renameᶜ-close01-open0 c =
  trans (renameᶜ-compose close01ᵗ (singleRenameᵗ zero) c)
    (renameᶜ-cong close01-open0 c)

renameᵗᵐ-close01-open0 :
  ∀ M →
  renameᵗᵐ (singleRenameᵗ zero) (renameᵗᵐ close01ᵗ M) ≡
  renameᵗᵐ merge01ᵗ M
renameᵗᵐ-close01-open0 M =
  trans (renameᵗᵐ-compose close01ᵗ (singleRenameᵗ zero) M)
    (renameᵗᵐ-cong close01-open0 M)

renameᵗ-close01-open1 :
  ∀ A →
  renameᵗ (singleRenameᵗ (suc zero)) (renameᵗ close01ᵗ A) ≡
  renameᵗ raise0ᵗ A
renameᵗ-close01-open1 A =
  trans (renameᵗ-compose close01ᵗ (singleRenameᵗ (suc zero)) A)
    (rename-cong close01-open1 A)

renameᶜ-close01-open1 :
  ∀ c →
  renameᶜ (singleRenameᵗ (suc zero)) (renameᶜ close01ᵗ c) ≡
  renameᶜ raise0ᵗ c
renameᶜ-close01-open1 c =
  trans (renameᶜ-compose close01ᵗ (singleRenameᵗ (suc zero)) c)
    (renameᶜ-cong close01-open1 c)

renameᵗᵐ-close01-open1 :
  ∀ M →
  renameᵗᵐ (singleRenameᵗ (suc zero)) (renameᵗᵐ close01ᵗ M) ≡
  renameᵗᵐ raise0ᵗ M
renameᵗᵐ-close01-open1 M =
  trans (renameᵗᵐ-compose close01ᵗ (singleRenameᵗ (suc zero)) M)
    (renameᵗᵐ-cong close01-open1 M)

renameᵗ-merge01-⇑ :
  ∀ A →
  renameᵗ merge01ᵗ (⇑ᵗ A) ≡ renameᵗ (extᵗ suc) A
renameᵗ-merge01-⇑ A =
  trans (renameᵗ-compose suc merge01ᵗ A)
    (rename-cong merge01ᵗ-after-suc A)

renameᶜ-merge01-⇑ :
  ∀ c →
  renameᶜ merge01ᵗ (⇑ᶜ c) ≡ renameᶜ (extᵗ suc) c
renameᶜ-merge01-⇑ c =
  trans (renameᶜ-compose suc merge01ᵗ c)
    (renameᶜ-cong merge01ᵗ-after-suc c)

renameᵗᵐ-merge01-⇑ :
  ∀ M →
  renameᵗᵐ merge01ᵗ (⇑ᵗᵐ M) ≡ renameᵗᵐ (extᵗ suc) M
renameᵗᵐ-merge01-⇑ M =
  trans (renameᵗᵐ-compose suc merge01ᵗ M)
    (renameᵗᵐ-cong merge01ᵗ-after-suc M)

renameᵗ-merge01-⇑⇑ :
  ∀ A →
  renameᵗ merge01ᵗ (⇑ᵗ (⇑ᵗ A)) ≡ ⇑ᵗ (⇑ᵗ A)
renameᵗ-merge01-⇑⇑ A =
  trans
    (cong (renameᵗ merge01ᵗ) (renameᵗ-compose suc suc A))
    (trans
      (renameᵗ-compose (λ X → suc (suc X)) merge01ᵗ A)
      (trans
        (rename-cong merge01ᵗ-after-suc-suc A)
        (sym (renameᵗ-compose suc suc A))))

renameᶜ-merge01-⇑⇑ :
  ∀ c →
  renameᶜ merge01ᵗ (⇑ᶜ (⇑ᶜ c)) ≡ ⇑ᶜ (⇑ᶜ c)
renameᶜ-merge01-⇑⇑ c =
  trans
    (cong (renameᶜ merge01ᵗ) (renameᶜ-compose suc suc c))
    (trans
      (renameᶜ-compose (λ X → suc (suc X)) merge01ᵗ c)
      (trans
        (renameᶜ-cong merge01ᵗ-after-suc-suc c)
        (sym (renameᶜ-compose suc suc c))))

renameᵗᵐ-merge01-⇑⇑ :
  ∀ M →
  renameᵗᵐ merge01ᵗ (⇑ᵗᵐ (⇑ᵗᵐ M)) ≡ ⇑ᵗᵐ (⇑ᵗᵐ M)
renameᵗᵐ-merge01-⇑⇑ M =
  trans
    (cong (renameᵗᵐ merge01ᵗ) (renameᵗᵐ-compose suc suc M))
    (trans
      (renameᵗᵐ-compose (λ X → suc (suc X)) merge01ᵗ M)
      (trans
        (renameᵗᵐ-cong merge01ᵗ-after-suc-suc M)
        (sym (renameᵗᵐ-compose suc suc M))))

raise0ᵗ-after-suc-suc :
  ∀ X →
  raise0ᵗ (suc (suc X)) ≡ suc (suc X)
raise0ᵗ-after-suc-suc X = refl

renameᵗ-raise0-⇑⇑ :
  ∀ A →
  renameᵗ raise0ᵗ (⇑ᵗ (⇑ᵗ A)) ≡ ⇑ᵗ (⇑ᵗ A)
renameᵗ-raise0-⇑⇑ A =
  trans
    (cong (renameᵗ raise0ᵗ) (renameᵗ-compose suc suc A))
    (trans
      (renameᵗ-compose (λ X → suc (suc X)) raise0ᵗ A)
      (trans
        (rename-cong raise0ᵗ-after-suc-suc A)
        (sym (renameᵗ-compose suc suc A))))

renameᶜ-raise0-⇑⇑ :
  ∀ c →
  renameᶜ raise0ᵗ (⇑ᶜ (⇑ᶜ c)) ≡ ⇑ᶜ (⇑ᶜ c)
renameᶜ-raise0-⇑⇑ c =
  trans
    (cong (renameᶜ raise0ᵗ) (renameᶜ-compose suc suc c))
    (trans
      (renameᶜ-compose (λ X → suc (suc X)) raise0ᵗ c)
      (trans
        (renameᶜ-cong raise0ᵗ-after-suc-suc c)
        (sym (renameᶜ-compose suc suc c))))

renameᵗᵐ-raise0-⇑⇑ :
  ∀ M →
  renameᵗᵐ raise0ᵗ (⇑ᵗᵐ (⇑ᵗᵐ M)) ≡ ⇑ᵗᵐ (⇑ᵗᵐ M)
renameᵗᵐ-raise0-⇑⇑ M =
  trans
    (cong (renameᵗᵐ raise0ᵗ) (renameᵗᵐ-compose suc suc M))
    (trans
      (renameᵗᵐ-compose (λ X → suc (suc X)) raise0ᵗ M)
      (trans
        (renameᵗᵐ-cong raise0ᵗ-after-suc-suc M)
        (sym (renameᵗᵐ-compose suc suc M))))

renameᵗ-raise0-swap01-⇑⇑ :
  ∀ A →
  renameᵗ raise0ᵗ (⇑ᵗ (⇑ᵗ A)) ≡
  renameᵗ swap01ᵗ (⇑ᵗ (⇑ᵗ A))
renameᵗ-raise0-swap01-⇑⇑ A =
  trans (renameᵗ-raise0-⇑⇑ A) (sym (renameᵗ-swap01-⇑⇑ A))

renameᶜ-raise0-swap01-⇑⇑ :
  ∀ c →
  renameᶜ raise0ᵗ (⇑ᶜ (⇑ᶜ c)) ≡
  renameᶜ swap01ᵗ (⇑ᶜ (⇑ᶜ c))
renameᶜ-raise0-swap01-⇑⇑ c =
  trans (renameᶜ-raise0-⇑⇑ c) (sym (renameᶜ-swap01-⇑⇑ c))

renameᵗᵐ-raise0-swap01-⇑⇑ :
  ∀ M →
  renameᵗᵐ raise0ᵗ (⇑ᵗᵐ (⇑ᵗᵐ M)) ≡
  renameᵗᵐ swap01ᵗ (⇑ᵗᵐ (⇑ᵗᵐ M))
renameᵗᵐ-raise0-swap01-⇑⇑ M =
  trans (renameᵗᵐ-raise0-⇑⇑ M) (sym (renameᵗᵐ-swap01-⇑⇑ M))

renameStNrw : Renameᵗ → StNrw → StNrw
renameStNrw ρ (X ꞉ p) = ρ X ꞉ renameᶜ ρ p
renameStNrw ρ (X ꞉= A ⊒) = ρ X ꞉= renameᵗ ρ A ⊒
renameStNrw ρ (⊒ X ꞉=☆) = ⊒ ρ X ꞉=☆

renameStoreNrw : Renameᵗ → StoreNrw → StoreNrw
renameStoreNrw ρ [] = []
renameStoreNrw ρ (entry ∷ σ) =
  renameStNrw ρ entry ∷ renameStoreNrw ρ σ

renameCtxNrw : Renameᵗ → CtxNrw → CtxNrw
renameCtxNrw ρ [] = []
renameCtxNrw ρ (p ∷ γ) = renameᶜ ρ p ∷ renameCtxNrw ρ γ

lookup-renameCtxNrw :
  ∀ {ρ γ x p} →
  γ ∋ x ⦂ p →
  renameCtxNrw ρ γ ∋ x ⦂ renameᶜ ρ p
lookup-renameCtxNrw Z = Z
lookup-renameCtxNrw (S x∋p) = S (lookup-renameCtxNrw x∋p)

renameCtxNrw-dual-cons :
  ∀ ρ p γ →
  renameCtxNrw ρ ((- p) ∷ γ) ≡ (- renameᶜ ρ p) ∷ renameCtxNrw ρ γ
renameCtxNrw-dual-cons ρ p γ =
  cong (_∷ renameCtxNrw ρ γ) (renameᶜ-dual-normal ρ p)

-- Attempt 73.  The useful bubble step must first rename a body derivation by
-- `swap01ᵗ` and only then apply adjacent source/target swaps.  The full
-- term-renaming transport is large because opened constructors (`extend`,
-- `split`, `α⊒α`, and `⊒α`) need target/coercion open-commutation, while
-- lambda bodies need the dual-context transport above.  The lookup, store, and
-- dual-context pieces here isolate the non-recursive bookkeeping for that
-- proof.

renameStoreNrw-swap01-⇑ˢ :
  ∀ σ →
  renameStoreNrw swap01ᵗ (⇑ˢ σ) ≡
    renameStoreNrw (extᵗ suc) σ
renameStoreNrw-swap01-⇑ˢ [] = refl
renameStoreNrw-swap01-⇑ˢ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉_ (swap01ᵗ-after-suc X) (renameᶜ-swap01-⇑ p))
    (renameStoreNrw-swap01-⇑ˢ σ)
renameStoreNrw-swap01-⇑ˢ ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉=_⊒ (swap01ᵗ-after-suc X) (renameᵗ-swap01-⇑ A))
    (renameStoreNrw-swap01-⇑ˢ σ)
renameStoreNrw-swap01-⇑ˢ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_
    (cong (λ Y → ⊒ Y ꞉=☆) (swap01ᵗ-after-suc X))
    (renameStoreNrw-swap01-⇑ˢ σ)

renameStoreNrw-swap01-⇑ˢ⇑ˢ :
  ∀ σ →
  renameStoreNrw swap01ᵗ (⇑ˢ (⇑ˢ σ)) ≡ ⇑ˢ (⇑ˢ σ)
renameStoreNrw-swap01-⇑ˢ⇑ˢ [] = refl
renameStoreNrw-swap01-⇑ˢ⇑ˢ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉_ (swap01ᵗ-after-suc-suc X) (renameᶜ-swap01-⇑⇑ p))
    (renameStoreNrw-swap01-⇑ˢ⇑ˢ σ)
renameStoreNrw-swap01-⇑ˢ⇑ˢ ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉=_⊒
      (swap01ᵗ-after-suc-suc X)
      (renameᵗ-swap01-⇑⇑ A))
    (renameStoreNrw-swap01-⇑ˢ⇑ˢ σ)
renameStoreNrw-swap01-⇑ˢ⇑ˢ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_
    (cong (λ Y → ⊒ Y ꞉=☆) (swap01ᵗ-after-suc-suc X))
    (renameStoreNrw-swap01-⇑ˢ⇑ˢ σ)

renameStoreNrw-merge01-⇑ˢ⇑ˢ :
  ∀ σ →
  renameStoreNrw merge01ᵗ (⇑ˢ (⇑ˢ σ)) ≡ ⇑ˢ (⇑ˢ σ)
renameStoreNrw-merge01-⇑ˢ⇑ˢ [] = refl
renameStoreNrw-merge01-⇑ˢ⇑ˢ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉_ (merge01ᵗ-after-suc-suc X) (renameᶜ-merge01-⇑⇑ p))
    (renameStoreNrw-merge01-⇑ˢ⇑ˢ σ)
renameStoreNrw-merge01-⇑ˢ⇑ˢ ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong₂ (λ Y B → Y ꞉= B ⊒)
      (merge01ᵗ-after-suc-suc X)
      (renameᵗ-merge01-⇑⇑ A))
    (renameStoreNrw-merge01-⇑ˢ⇑ˢ σ)
renameStoreNrw-merge01-⇑ˢ⇑ˢ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_
    (cong (λ Y → ⊒ Y ꞉=☆) (merge01ᵗ-after-suc-suc X))
    (renameStoreNrw-merge01-⇑ˢ⇑ˢ σ)

renameStoreNrw-raise0-⇑ˢ⇑ˢ :
  ∀ σ →
  renameStoreNrw raise0ᵗ (⇑ˢ (⇑ˢ σ)) ≡ ⇑ˢ (⇑ˢ σ)
renameStoreNrw-raise0-⇑ˢ⇑ˢ [] = refl
renameStoreNrw-raise0-⇑ˢ⇑ˢ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉_ (raise0ᵗ-after-suc-suc X) (renameᶜ-raise0-⇑⇑ p))
    (renameStoreNrw-raise0-⇑ˢ⇑ˢ σ)
renameStoreNrw-raise0-⇑ˢ⇑ˢ ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉=_⊒
      (raise0ᵗ-after-suc-suc X)
      (renameᵗ-raise0-⇑⇑ A))
    (renameStoreNrw-raise0-⇑ˢ⇑ˢ σ)
renameStoreNrw-raise0-⇑ˢ⇑ˢ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_
    (cong (λ Y → ⊒ Y ꞉=☆) (raise0ᵗ-after-suc-suc X))
    (renameStoreNrw-raise0-⇑ˢ⇑ˢ σ)

-- Attempt 72.  A full source-prefix bubble cannot be expressed by
-- `SourceTargetSwapRels` alone.  For an empty prefix, `swap01ᵗ` makes the
-- outer source-star and target-only entries adjacent and the lemma above
-- normalizes the double-shifted tail.  For a nonempty prefix, however, the
-- target-only entry is buried below the shifted prefix, so every crossing
-- needs its own local `swap01ᵗ` renaming before the adjacent swap.  The next
-- useful relation should combine the local renaming and the swap in one
-- recursive step.

renameCtxNrw-swap01-⇑ᵍ :
  ∀ γ →
  renameCtxNrw swap01ᵗ (⇑ᵍ γ) ≡
    renameCtxNrw (extᵗ suc) γ
renameCtxNrw-swap01-⇑ᵍ [] = refl
renameCtxNrw-swap01-⇑ᵍ (p ∷ γ) =
  cong₂ _∷_ (renameᶜ-swap01-⇑ p) (renameCtxNrw-swap01-⇑ᵍ γ)

srcStoreⁿ-renameStoreNrw :
  ∀ ρ σ →
  srcStoreⁿ (renameStoreNrw ρ σ) ≡ renameStoreᵗ ρ (srcStoreⁿ σ)
srcStoreⁿ-renameStoreNrw ρ [] = refl
srcStoreⁿ-renameStoreNrw ρ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong (λ A → (ρ X , A)) (src-renameᶜ ρ p))
    (srcStoreⁿ-renameStoreNrw ρ σ)
srcStoreⁿ-renameStoreNrw ρ ((X ꞉= A ⊒) ∷ σ) =
  srcStoreⁿ-renameStoreNrw ρ σ
srcStoreⁿ-renameStoreNrw ρ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_ refl (srcStoreⁿ-renameStoreNrw ρ σ)

renameStoreNrw-⇑ˢ :
  ∀ ρ σ →
  renameStoreNrw (extᵗ ρ) (⇑ˢ σ) ≡ ⇑ˢ (renameStoreNrw ρ σ)
renameStoreNrw-⇑ˢ ρ [] = refl
renameStoreNrw-⇑ˢ ρ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong (λ c → suc (ρ X) ꞉ c) (renameᶜ-ext-suc-comm ρ p))
    (renameStoreNrw-⇑ˢ ρ σ)
renameStoreNrw-⇑ˢ ρ ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong (λ B → suc (ρ X) ꞉= B ⊒) (renameᵗ-ext-suc-comm ρ A))
    (renameStoreNrw-⇑ˢ ρ σ)
renameStoreNrw-⇑ˢ ρ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_ refl (renameStoreNrw-⇑ˢ ρ σ)

renameCtxNrw-⇑ᵍ :
  ∀ ρ γ →
  renameCtxNrw (extᵗ ρ) (⇑ᵍ γ) ≡ ⇑ᵍ (renameCtxNrw ρ γ)
renameCtxNrw-⇑ᵍ ρ [] = refl
renameCtxNrw-⇑ᵍ ρ (p ∷ γ) =
  cong₂ _∷_ (renameᶜ-ext-suc-comm ρ p) (renameCtxNrw-⇑ᵍ ρ γ)

modeRename-tag-or-id :
  ∀ ρ →
  ModeRename ρ tag-or-idᵈ tag-or-idᵈ
modeRename-tag-or-id ρ X = refl

renameStoreNrw-coercionᶜ :
  ∀ {Δ Δ′ σ c A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ′ ∣ srcStoreⁿ (renameStoreNrw ρ σ)
    ⊢ renameᶜ ρ c ∶ᶜ renameᵗ ρ A ⊒ renameᵗ ρ B
renameStoreNrw-coercionᶜ {σ = σ} {ρ = ρ} hρ cᶜ =
  subst
    (λ Σ → _ ∣ Σ ⊢ _ ∶ᶜ _ ⊒ _)
    (sym (srcStoreⁿ-renameStoreNrw ρ σ))
    (narrow-renameᵗ hρ (modeRename-tag-or-id ρ) cᶜ)

modeRename-swap01-tag-or-id :
  ModeRename swap01ᵗ tag-or-idᵈ tag-or-idᵈ
modeRename-swap01-tag-or-id =
  modeRename-tag-or-id swap01ᵗ

swap01ᵗMode : ModeEnv → ModeEnv
swap01ᵗMode μ X = μ (swap01ᵗ X)

modeRename-swap01ᵗMode :
  ∀ μ →
  ModeRename swap01ᵗ μ (swap01ᵗMode μ)
modeRename-swap01ᵗMode μ X
    rewrite swap01ᵗ-involutive X
    with μ X
... | id-only = refl
... | tag-or-id = refl
... | seal-or-id = refl

⊒ˢ-rename-swap01ᵗ :
  ∀ {Δ σ Σ Σ′} →
  suc (suc Δ) ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  suc (suc Δ) ⊢ renameStoreNrw swap01ᵗ σ ꞉
    renameStoreᵗ swap01ᵗ Σ ⊒ˢ renameStoreᵗ swap01ᵗ Σ′
⊒ˢ-rename-swap01ᵗ ⊒ˢ-nil = ⊒ˢ-nil
⊒ˢ-rename-swap01ᵗ (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right (renameᵗ-preserves-WfTy hA TyRenameWf-swap01)
    (⊒ˢ-rename-swap01ᵗ σ⊒)
⊒ˢ-rename-swap01ᵗ (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (⊒ˢ-rename-swap01ᵗ σ⊒)
⊒ˢ-rename-swap01ᵗ (⊒ˢ-both hA hA′ (μ , q⊒) σ⊒) =
  ⊒ˢ-both
    (renameᵗ-preserves-WfTy hA TyRenameWf-swap01)
    (renameᵗ-preserves-WfTy hA′ TyRenameWf-swap01)
    (swap01ᵗMode μ ,
      narrow-renameᵗ TyRenameWf-swap01
        (modeRename-swap01ᵗMode μ) q⊒)
    (⊒ˢ-rename-swap01ᵗ σ⊒)

≈ⁿ-rename-swap01ᵗ :
  ∀ {Δ σ s t A B} →
  suc (suc Δ) ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  suc (suc Δ) ∣ renameStoreNrw swap01ᵗ σ
    ⊢ renameᶜ swap01ᵗ s ≈ renameᶜ swap01ᵗ t
      ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
≈ⁿ-rename-swap01ᵗ {s = s} {t = t}
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  endpointsⁿ
    (trans (src-renameᶜ swap01ᵗ s) (cong (renameᵗ swap01ᵗ) srcs))
    (trans (tgt-renameᶜ swap01ᵗ s) (cong (renameᵗ swap01ᵗ) tgts))
    (trans (src-renameᶜ swap01ᵗ t) (cong (renameᵗ swap01ᵗ) srct))
    (trans (tgt-renameᶜ swap01ᵗ t) (cong (renameᵗ swap01ᵗ) tgtt))
    (⊒ˢ-rename-swap01ᵗ σ⊒)
    (WfTyˢ-rename TyRenameWf-swap01 (proj₁ wfΣ) ,
     WfTyˢ-rename TyRenameWf-swap01 (proj₂ wfΣ))
    (WfTyˢ-rename TyRenameWf-swap01 (proj₁ wfΣ′) ,
     WfTyˢ-rename TyRenameWf-swap01 (proj₂ wfΣ′))
    (let μ = proj₁ s⊒ in
      swap01ᵗMode μ ,
      narrow-renameᵗ TyRenameWf-swap01
        (modeRename-swap01ᵗMode μ) (proj₂ s⊒))
    (let μ = proj₁ t⊒ in
      swap01ᵗMode μ ,
      narrow-renameᵗ TyRenameWf-swap01
        (modeRename-swap01ᵗMode μ) (proj₂ t⊒))

StoreRenameOk :
  ∀ {Δ σ Σ Σ′} →
  Renameᵗ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Set
StoreRenameOk ρ ⊒ˢ-nil = ⊤
StoreRenameOk ρ (⊒ˢ-right hA σ⊒) = StoreRenameOk ρ σ⊒
StoreRenameOk ρ (⊒ˢ-left σ⊒) = StoreRenameOk ρ σ⊒
StoreRenameOk ρ (⊒ˢ-both hA hA′ (μ , s⊒) σ⊒) =
  ∃[ ν ] ModeRename ρ μ ν × StoreRenameOk ρ σ⊒

⊒ˢ-rename-guarded :
  ∀ {Δ Δ′ σ Σ Σ′ ρ} →
  TyRenameWf Δ Δ′ ρ →
  (σ⊒ : Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′) →
  StoreRenameOk ρ σ⊒ →
  Δ′ ⊢ renameStoreNrw ρ σ ꞉
    renameStoreᵗ ρ Σ ⊒ˢ renameStoreᵗ ρ Σ′
⊒ˢ-rename-guarded hρ ⊒ˢ-nil ok = ⊒ˢ-nil
⊒ˢ-rename-guarded hρ (⊒ˢ-right hA σ⊒) ok =
  ⊒ˢ-right (renameᵗ-preserves-WfTy hA hρ)
    (⊒ˢ-rename-guarded hρ σ⊒ ok)
⊒ˢ-rename-guarded hρ (⊒ˢ-left σ⊒) ok =
  ⊒ˢ-left (⊒ˢ-rename-guarded hρ σ⊒ ok)
⊒ˢ-rename-guarded hρ (⊒ˢ-both hA hA′ (μ , s⊒) σ⊒)
    (target , hμ , ok) =
  ⊒ˢ-both
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hA′ hρ)
    (target , narrow-renameᵗ hρ hμ s⊒)
    (⊒ˢ-rename-guarded hρ σ⊒ ok)

NarrowingRenameOk :
  ∀ {Δ Σ c A B} →
  Renameᵗ →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Set
NarrowingRenameOk ρ (μ , c⊒) =
  ∃[ ν ] ModeRename ρ μ ν

narrow-rename-guarded :
  ∀ {Δ Δ′ Σ c A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  (c⊒ : Δ ∣ Σ ⊢ c ∶ A ⊒ B) →
  NarrowingRenameOk ρ c⊒ →
  Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
narrow-rename-guarded hρ (μ , c⊒) (target , hμ) =
  target , narrow-renameᵗ hρ hμ c⊒

≈ⁿRenameOk :
  ∀ {Δ σ s t A B} →
  Renameᵗ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Set
≈ⁿRenameOk ρ
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  StoreRenameOk ρ σ⊒ ×
  NarrowingRenameOk ρ s⊒ ×
  NarrowingRenameOk ρ t⊒

≈ⁿ-rename-guarded :
  ∀ {Δ Δ′ σ s t A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  (s≈t : Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B) →
  ≈ⁿRenameOk ρ s≈t →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ s ≈ renameᶜ ρ t
      ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
≈ⁿ-rename-guarded {ρ = ρ} hρ
    (endpointsⁿ {s = s} {t = t}
      srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒)
    (okΣ , oks , okt) =
  endpointsⁿ
    (trans (src-renameᶜ ρ s) (cong (renameᵗ ρ) srcs))
    (trans (tgt-renameᶜ ρ s) (cong (renameᵗ ρ) tgts))
    (trans (src-renameᶜ ρ t) (cong (renameᵗ ρ) srct))
    (trans (tgt-renameᶜ ρ t) (cong (renameᵗ ρ) tgtt))
    (⊒ˢ-rename-guarded hρ σ⊒ okΣ)
    (WfTyˢ-rename hρ (proj₁ wfΣ) ,
     WfTyˢ-rename hρ (proj₂ wfΣ))
    (WfTyˢ-rename hρ (proj₁ wfΣ′) ,
     WfTyˢ-rename hρ (proj₂ wfΣ′))
    (narrow-rename-guarded hρ s⊒ oks)
    (narrow-rename-guarded hρ t⊒ okt)

⊒ˢ-source-target-swap :
  ∀ {Δ σ Σ Σ′ X Y A} →
  Δ ⊢ (⊒ X ꞉=☆) ∷ (Y ꞉= A ⊒) ∷ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ (Y ꞉= A ⊒) ∷ (⊒ X ꞉=☆) ∷ σ ꞉ Σ ⊒ˢ Σ′
⊒ˢ-source-target-swap (⊒ˢ-left (⊒ˢ-right hA σ⊒)) =
  ⊒ˢ-right hA (⊒ˢ-left σ⊒)

≈ⁿ-source-target-swap :
  ∀ {Δ σ X Y A s t B C} →
  Δ ∣ (⊒ X ꞉=☆) ∷ (Y ꞉= A ⊒) ∷ σ
    ⊢ s ≈ t ∶ B ⊒ C →
  Δ ∣ (Y ꞉= A ⊒) ∷ (⊒ X ꞉=☆) ∷ σ
    ⊢ s ≈ t ∶ B ⊒ C
≈ⁿ-source-target-swap
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (⊒ˢ-source-target-swap σ⊒)
    wfΣ
    wfΣ′
    s⊒
    t⊒

compose-leftⁿ-source-target-swap :
  ∀ {Δ σ X Y E q s r A B} →
  Δ ∣ (⊒ X ꞉=☆) ∷ (Y ꞉= E ⊒) ∷ σ
    ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ (Y ꞉= E ⊒) ∷ (⊒ X ꞉=☆) ∷ σ
    ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
compose-leftⁿ-source-target-swap
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒ (≈ⁿ-source-target-swap q⨟s≈r)

compose-rightⁿ-source-target-swap :
  ∀ {Δ σ X Y E r t p A B} →
  Δ ∣ (⊒ X ꞉=☆) ∷ (Y ꞉= E ⊒) ∷ σ
    ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ (Y ꞉= E ⊒) ∷ (⊒ X ꞉=☆) ∷ σ
    ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
compose-rightⁿ-source-target-swap
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒ (≈ⁿ-source-target-swap r≈t⨟p)

⊒ˢ-source-target-merge-id★ :
  ∀ {Δ σ Σ Σ′ X} →
  Δ ⊢ (⊒ X ꞉=☆) ∷ (X ꞉= ★ ⊒) ∷ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ (X ꞉ id ★) ∷ σ ꞉ Σ ⊒ˢ Σ′
⊒ˢ-source-target-merge-id★ (⊒ˢ-left (⊒ˢ-right hA σ⊒)) =
  ⊒ˢ-both wf★ wf★ (id-onlyᵈ , (cast-id wf★ refl , id★)) σ⊒

≈ⁿ-source-target-merge-id★ :
  ∀ {Δ σ X s t A B} →
  Δ ∣ (⊒ X ꞉=☆) ∷ (X ꞉= ★ ⊒) ∷ σ
    ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ (X ꞉ id ★) ∷ σ
    ⊢ s ≈ t ∶ A ⊒ B
≈ⁿ-source-target-merge-id★
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (⊒ˢ-source-target-merge-id★ σ⊒)
    wfΣ
    wfΣ′
    s⊒
    t⊒

compose-leftⁿ-source-target-merge-id★ :
  ∀ {Δ σ X q s r A B} →
  Δ ∣ (⊒ X ꞉=☆) ∷ (X ꞉= ★ ⊒) ∷ σ
    ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ (X ꞉ id ★) ∷ σ
    ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
compose-leftⁿ-source-target-merge-id★
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒ (≈ⁿ-source-target-merge-id★ q⨟s≈r)

compose-rightⁿ-source-target-merge-id★ :
  ∀ {Δ σ X r t p A B} →
  Δ ∣ (⊒ X ꞉=☆) ∷ (X ꞉= ★ ⊒) ∷ σ
    ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ (X ꞉ id ★) ∷ σ
    ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
compose-rightⁿ-source-target-merge-id★
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒ (≈ⁿ-source-target-merge-id★ r≈t⨟p)

data SourceTargetMergeRel : TyCtx → StoreNrw → StoreNrw → Set where
  merge-here :
    ∀ {Δ X σ} →
    SourceTargetMergeRel Δ
      ((⊒ X ꞉=☆) ∷ (X ꞉= ★ ⊒) ∷ σ)
      ((X ꞉ id ★) ∷ σ)

  merge-right :
    ∀ {Δ X A σ σ′} →
    SourceTargetMergeRel Δ σ σ′ →
    SourceTargetMergeRel Δ
      ((X ꞉= A ⊒) ∷ σ)
      ((X ꞉= A ⊒) ∷ σ′)

  merge-left :
    ∀ {Δ X σ σ′} →
    SourceTargetMergeRel Δ σ σ′ →
    SourceTargetMergeRel Δ
      ((⊒ X ꞉=☆) ∷ σ)
      ((⊒ X ꞉=☆) ∷ σ′)

  merge-both :
    ∀ {Δ X q σ σ′} →
    SourceTargetMergeRel Δ σ σ′ →
    SourceTargetMergeRel Δ
      ((X ꞉ q) ∷ σ)
      ((X ꞉ q) ∷ σ′)

SourceTargetMergeRel-⇑ˢ :
  ∀ {Δ σ σ′} →
  SourceTargetMergeRel Δ σ σ′ →
  SourceTargetMergeRel (suc Δ) (⇑ˢ σ) (⇑ˢ σ′)
SourceTargetMergeRel-⇑ˢ merge-here = merge-here
SourceTargetMergeRel-⇑ˢ (merge-right rel) =
  merge-right (SourceTargetMergeRel-⇑ˢ rel)
SourceTargetMergeRel-⇑ˢ (merge-left rel) =
  merge-left (SourceTargetMergeRel-⇑ˢ rel)
SourceTargetMergeRel-⇑ˢ (merge-both rel) =
  merge-both (SourceTargetMergeRel-⇑ˢ rel)

SourceTargetMergeRel-src≡ :
  ∀ {Δ σ σ′} →
  SourceTargetMergeRel Δ σ σ′ →
  srcStoreⁿ σ ≡ srcStoreⁿ σ′
SourceTargetMergeRel-src≡ merge-here = refl
SourceTargetMergeRel-src≡ (merge-right rel) =
  SourceTargetMergeRel-src≡ rel
SourceTargetMergeRel-src≡ (merge-left {X = X} rel) =
  cong ((X , ★) ∷_) (SourceTargetMergeRel-src≡ rel)
SourceTargetMergeRel-src≡ (merge-both {X = X} {q = q} rel) =
  cong ((X , src q) ∷_) (SourceTargetMergeRel-src≡ rel)

SourceTargetMergeRel-coercionᶜ :
  ∀ {Δ σ σ′ c A B} →
  SourceTargetMergeRel Δ σ σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ ∣ srcStoreⁿ σ′ ⊢ c ∶ᶜ A ⊒ B
SourceTargetMergeRel-coercionᶜ rel cᶜ =
  subst
    (λ Σ → _ ∣ Σ ⊢ _ ∶ᶜ _ ⊒ _)
    (SourceTargetMergeRel-src≡ rel)
    cᶜ

SourceTargetMergeRel-⊒ˢ :
  ∀ {Δ σ σ′ Σ Σ′} →
  SourceTargetMergeRel Δ σ σ′ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ σ′ ꞉ Σ ⊒ˢ Σ′
SourceTargetMergeRel-⊒ˢ merge-here σ⊒ =
  ⊒ˢ-source-target-merge-id★ σ⊒
SourceTargetMergeRel-⊒ˢ (merge-right rel) (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right hA (SourceTargetMergeRel-⊒ˢ rel σ⊒)
SourceTargetMergeRel-⊒ˢ (merge-left rel) (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (SourceTargetMergeRel-⊒ˢ rel σ⊒)
SourceTargetMergeRel-⊒ˢ (merge-both rel)
    (⊒ˢ-both hA hA′ s⊒ σ⊒) =
  ⊒ˢ-both hA hA′ s⊒ (SourceTargetMergeRel-⊒ˢ rel σ⊒)

SourceTargetMergeRel-≈ⁿ :
  ∀ {Δ σ σ′ s t A B} →
  SourceTargetMergeRel Δ σ σ′ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ s ≈ t ∶ A ⊒ B
SourceTargetMergeRel-≈ⁿ rel
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (SourceTargetMergeRel-⊒ˢ rel σ⊒)
    wfΣ
    wfΣ′
    s⊒
    t⊒

SourceTargetMergeRel-compose-left :
  ∀ {Δ σ σ′ q s r A B} →
  SourceTargetMergeRel Δ σ σ′ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
SourceTargetMergeRel-compose-left rel
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒ (SourceTargetMergeRel-≈ⁿ rel q⨟s≈r)

SourceTargetMergeRel-compose-right :
  ∀ {Δ σ σ′ r t p A B} →
  SourceTargetMergeRel Δ σ σ′ →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
SourceTargetMergeRel-compose-right rel
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒ (SourceTargetMergeRel-≈ⁿ rel r≈t⨟p)

split-source-target-merge-safe-rebuild :
  ∀ {Δ α A αᵢ σ σ′ γ N N′ p q C D} →
  (rel : SourceTargetMergeRel Δ σ σ′) →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
    ⊢ q ∶ᶜ ★ ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
    ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉ q) ∷ σ′ ∣ γ
    ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ →
  Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ′ ∣ γ
    ⊢ N [ αᵢ ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ
split-source-target-merge-safe-rebuild
    {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ} {σ = σ} {σ′ = σ′}
    rel qᶜ pαᶜ body =
  split
    (SourceTargetMergeRel-coercionᶜ splitRel qᶜ)
    (SourceTargetMergeRel-coercionᶜ splitRel pαᶜ)
    body
  where
    splitRel :
      SourceTargetMergeRel Δ
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ′)
    splitRel =
      merge-right (merge-left rel)

data SplitSourceTargetMergeView :
  ∀ {Δ α A αᵢ σ τ} →
  SourceTargetMergeRel Δ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) τ →
  Set where

  split-merge-safe :
    ∀ {Δ α A αᵢ σ σ′}
    (rel : SourceTargetMergeRel Δ σ σ′) →
    SplitSourceTargetMergeView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ} {σ = σ}
      (merge-right (merge-left rel))

  split-merge-unsafe :
    ∀ {Δ α A αᵢ σ} →
    SplitSourceTargetMergeView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ}
      {σ = (αᵢ ꞉= ★ ⊒) ∷ σ}
      (merge-right merge-here)

split-source-target-merge-view :
  ∀ {Δ α A αᵢ σ τ}
  (rel : SourceTargetMergeRel Δ
    ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) τ) →
  SplitSourceTargetMergeView rel
split-source-target-merge-view (merge-right merge-here) =
  split-merge-unsafe
split-source-target-merge-view (merge-right (merge-left rel)) =
  split-merge-safe rel

SourceTargetMergeSafeFor :
  ∀ {Δ σ σ′ γ M T c} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c →
  SourceTargetMergeRel Δ σ σ′ →
  Set
SourceTargetMergeSafeFor (extend qᶜ pαᶜ M⊒T) (merge-both rel) =
  SourceTargetMergeSafeFor M⊒T (merge-right rel)
SourceTargetMergeSafeFor (split qᶜ pαᶜ M⊒T) (merge-right merge-here) =
  ⊥
SourceTargetMergeSafeFor (split {q = q} qᶜ pαᶜ M⊒T)
    (merge-right (merge-left rel)) =
  SourceTargetMergeSafeFor M⊒T (merge-both {q = q} rel)
SourceTargetMergeSafeFor (⊒blame pᶜ) rel = ⊤
SourceTargetMergeSafeFor (x⊒x pᶜ x∋p) rel = ⊤
SourceTargetMergeSafeFor {γ = γ} (ƛ⊒ƛ {p = p} p↦qᶜ N⊒N′) rel =
  SourceTargetMergeSafeFor {γ = (- p) ∷ γ} N⊒N′ rel
SourceTargetMergeSafeFor (·⊒· qᶜ L⊒L′ M⊒M′) rel =
  SourceTargetMergeSafeFor L⊒L′ rel ×
  SourceTargetMergeSafeFor M⊒M′ rel
SourceTargetMergeSafeFor {γ = γ} (Λ⊒Λ allᶜ vV V⊒V′) rel =
  SourceTargetMergeSafeFor {γ = ⇑ᵍ γ} V⊒V′
    (SourceTargetMergeRel-⇑ˢ rel)
SourceTargetMergeSafeFor {γ = γ} (⊒Λ pᶜ N⊒V′) rel =
  SourceTargetMergeSafeFor {γ = ⇑ᵍ γ} N⊒V′
    (merge-right (SourceTargetMergeRel-⇑ˢ rel))
SourceTargetMergeSafeFor {γ = γ} (⊒⟨ν⟩ pᶜ i N⊒V′s) rel =
  SourceTargetMergeSafeFor {γ = ⇑ᵍ γ} N⊒V′s
    (merge-right (SourceTargetMergeRel-⇑ˢ rel))
SourceTargetMergeSafeFor (α⊒α γ′≡ qᶜ pαᶜ L⊒L′) rel = ⊥
SourceTargetMergeSafeFor (⊒α γ′≡ pαᶜ L⊒L′) rel = ⊥
SourceTargetMergeSafeFor {γ = γ} (ν⊒ν {q = q} pᶜ qᶜ N⊒N′) rel =
  SourceTargetMergeSafeFor {γ = ⇑ᵍ γ} N⊒N′
    (merge-both {q = ⇑ᶜ q} (SourceTargetMergeRel-⇑ˢ rel))
SourceTargetMergeSafeFor {γ = γ} (⊒ν pᶜ N⊒N′) rel =
  SourceTargetMergeSafeFor {γ = ⇑ᵍ γ} N⊒N′
    (merge-right (SourceTargetMergeRel-⇑ˢ rel))
SourceTargetMergeSafeFor {γ = γ} (ν⊒ pᶜ N⊒N′) rel =
  SourceTargetMergeSafeFor {γ = ⇑ᵍ γ} N⊒N′
    (merge-left (SourceTargetMergeRel-⇑ˢ rel))
SourceTargetMergeSafeFor (κ⊒κ κ) rel = ⊤
SourceTargetMergeSafeFor (⊕⊒⊕ M⊒M′ N⊒N′) rel =
  SourceTargetMergeSafeFor M⊒M′ rel ×
  SourceTargetMergeSafeFor N⊒N′ rel
SourceTargetMergeSafeFor (⊒cast+ qᶜ q⨟s≈r M⊒M′) rel =
  SourceTargetMergeSafeFor M⊒M′ rel
SourceTargetMergeSafeFor (⊒cast- qᶜ q⨟s≈r M⊒M′) rel =
  SourceTargetMergeSafeFor M⊒M′ rel
SourceTargetMergeSafeFor (cast+⊒ pᶜ r≈t⨟p M⊒M′) rel =
  SourceTargetMergeSafeFor M⊒M′ rel
SourceTargetMergeSafeFor (cast-⊒ pᶜ r≈t⨟p M⊒M′) rel =
  SourceTargetMergeSafeFor M⊒M′ rel

SourceTargetMergeSafe :
  ∀ {Δ σ σ′ γ M T c} →
  SourceTargetMergeRel Δ σ σ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c →
  Set
SourceTargetMergeSafe rel M⊒T =
  SourceTargetMergeSafeFor M⊒T rel

SourceTargetMergeRel-term-safe :
  ∀ {Δ σ σ′ γ M T c}
  (rel : SourceTargetMergeRel Δ σ σ′)
  (M⊒T : Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c) →
  SourceTargetMergeSafe rel M⊒T →
  Δ ∣ σ′ ∣ γ ⊢ M ⊒ T ∶ c
SourceTargetMergeRel-term-safe rel (α⊒α γ′≡ qᶜ pαᶜ L⊒L′) ()
SourceTargetMergeRel-term-safe rel (⊒α γ′≡ pαᶜ L⊒L′) ()
SourceTargetMergeRel-term-safe (merge-both rel)
    (extend {q = q} qᶜ pαᶜ M⊒T) safe =
  extend
    (SourceTargetMergeRel-coercionᶜ rel qᶜ)
    (SourceTargetMergeRel-coercionᶜ (merge-both {q = q} rel) pαᶜ)
    (SourceTargetMergeRel-term-safe (merge-right rel) M⊒T safe)
SourceTargetMergeRel-term-safe (merge-right merge-here)
    (split qᶜ pαᶜ M⊒T) ()
SourceTargetMergeRel-term-safe (merge-right (merge-left rel))
    (split {q = q} qᶜ pαᶜ M⊒T) safe =
  split-source-target-merge-safe-rebuild rel qᶜ pαᶜ
    (SourceTargetMergeRel-term-safe
      (merge-both {q = q} rel)
      M⊒T
      safe)
SourceTargetMergeRel-term-safe rel (⊒blame pᶜ) safe =
  ⊒blame (SourceTargetMergeRel-coercionᶜ rel pᶜ)
SourceTargetMergeRel-term-safe rel (x⊒x pᶜ x∋p) safe =
  x⊒x (SourceTargetMergeRel-coercionᶜ rel pᶜ) x∋p
SourceTargetMergeRel-term-safe {γ = γ} rel
    (ƛ⊒ƛ {p = p} p↦qᶜ N⊒N′) safe =
  ƛ⊒ƛ
    (SourceTargetMergeRel-coercionᶜ rel p↦qᶜ)
    (SourceTargetMergeRel-term-safe {γ = (- p) ∷ γ}
      rel N⊒N′ safe)
SourceTargetMergeRel-term-safe rel
    (·⊒· qᶜ L⊒L′ M⊒M′) (safeL , safeM) =
  ·⊒·
    (SourceTargetMergeRel-coercionᶜ rel qᶜ)
    (SourceTargetMergeRel-term-safe rel L⊒L′ safeL)
    (SourceTargetMergeRel-term-safe rel M⊒M′ safeM)
SourceTargetMergeRel-term-safe {γ = γ} rel
    (Λ⊒Λ allᶜ vV V⊒V′) safe =
  Λ⊒Λ
    (SourceTargetMergeRel-coercionᶜ rel allᶜ)
    vV
    (SourceTargetMergeRel-term-safe {γ = ⇑ᵍ γ}
      (SourceTargetMergeRel-⇑ˢ rel)
      V⊒V′
      safe)
SourceTargetMergeRel-term-safe {γ = γ} rel (⊒Λ pᶜ N⊒V′) safe =
  ⊒Λ
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    (SourceTargetMergeRel-term-safe {γ = ⇑ᵍ γ}
      (merge-right (SourceTargetMergeRel-⇑ˢ rel))
      N⊒V′
      safe)
SourceTargetMergeRel-term-safe {γ = γ} rel
    (⊒⟨ν⟩ pᶜ i N⊒V′s) safe =
  ⊒⟨ν⟩
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    i
    (SourceTargetMergeRel-term-safe {γ = ⇑ᵍ γ}
      (merge-right (SourceTargetMergeRel-⇑ˢ rel))
      N⊒V′s
      safe)
SourceTargetMergeRel-term-safe {γ = γ} rel
    (ν⊒ν {q = q} pᶜ qᶜ N⊒N′) safe =
  ν⊒ν
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    (SourceTargetMergeRel-coercionᶜ rel qᶜ)
    (SourceTargetMergeRel-term-safe {γ = ⇑ᵍ γ}
      (merge-both {q = ⇑ᶜ q} (SourceTargetMergeRel-⇑ˢ rel))
      N⊒N′
      safe)
SourceTargetMergeRel-term-safe {γ = γ} rel (⊒ν pᶜ N⊒N′) safe =
  ⊒ν
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    (SourceTargetMergeRel-term-safe {γ = ⇑ᵍ γ}
      (merge-right (SourceTargetMergeRel-⇑ˢ rel))
      N⊒N′
      safe)
SourceTargetMergeRel-term-safe {γ = γ} rel (ν⊒ pᶜ N⊒N′) safe =
  ν⊒
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    (SourceTargetMergeRel-term-safe {γ = ⇑ᵍ γ}
      (merge-left (SourceTargetMergeRel-⇑ˢ rel))
      N⊒N′
      safe)
SourceTargetMergeRel-term-safe rel (κ⊒κ κ) safe =
  κ⊒κ κ
SourceTargetMergeRel-term-safe rel
    (⊕⊒⊕ M⊒M′ N⊒N′) (safeM , safeN) =
  ⊕⊒⊕
    (SourceTargetMergeRel-term-safe rel M⊒M′ safeM)
    (SourceTargetMergeRel-term-safe rel N⊒N′ safeN)
SourceTargetMergeRel-term-safe rel
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) safe =
  ⊒cast+
    (SourceTargetMergeRel-coercionᶜ rel qᶜ)
    (SourceTargetMergeRel-compose-left rel q⨟s≈r)
    (SourceTargetMergeRel-term-safe rel M⊒M′ safe)
SourceTargetMergeRel-term-safe rel
    (⊒cast- qᶜ q⨟s≈r M⊒M′) safe =
  ⊒cast-
    (SourceTargetMergeRel-coercionᶜ rel qᶜ)
    (SourceTargetMergeRel-compose-left rel q⨟s≈r)
    (SourceTargetMergeRel-term-safe rel M⊒M′ safe)
SourceTargetMergeRel-term-safe rel
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) safe =
  cast+⊒
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    (SourceTargetMergeRel-compose-right rel r≈t⨟p)
    (SourceTargetMergeRel-term-safe rel M⊒M′ safe)
SourceTargetMergeRel-term-safe rel
    (cast-⊒ pᶜ r≈t⨟p M⊒M′) safe =
  cast-⊒
    (SourceTargetMergeRel-coercionᶜ rel pᶜ)
    (SourceTargetMergeRel-compose-right rel r≈t⨟p)
    (SourceTargetMergeRel-term-safe rel M⊒M′ safe)

data SourceTargetSwapRel : TyCtx → StoreNrw → StoreNrw → Set where
  swap-here :
    ∀ {Δ X Y A σ} →
    SourceTargetSwapRel Δ
      ((⊒ X ꞉=☆) ∷ (Y ꞉= A ⊒) ∷ σ)
      ((Y ꞉= A ⊒) ∷ (⊒ X ꞉=☆) ∷ σ)

  swap-right :
    ∀ {Δ X A σ σ′} →
    SourceTargetSwapRel Δ σ σ′ →
    SourceTargetSwapRel Δ
      ((X ꞉= A ⊒) ∷ σ)
      ((X ꞉= A ⊒) ∷ σ′)

  swap-left :
    ∀ {Δ X σ σ′} →
    SourceTargetSwapRel Δ σ σ′ →
    SourceTargetSwapRel Δ
      ((⊒ X ꞉=☆) ∷ σ)
      ((⊒ X ꞉=☆) ∷ σ′)

  swap-both :
    ∀ {Δ X q σ σ′} →
    SourceTargetSwapRel Δ σ σ′ →
    SourceTargetSwapRel Δ
      ((X ꞉ q) ∷ σ)
      ((X ꞉ q) ∷ σ′)

SourceTargetSwapRel-⇑ˢ :
  ∀ {Δ σ σ′} →
  SourceTargetSwapRel Δ σ σ′ →
  SourceTargetSwapRel (suc Δ) (⇑ˢ σ) (⇑ˢ σ′)
SourceTargetSwapRel-⇑ˢ swap-here = swap-here
SourceTargetSwapRel-⇑ˢ (swap-right rel) =
  swap-right (SourceTargetSwapRel-⇑ˢ rel)
SourceTargetSwapRel-⇑ˢ (swap-left rel) =
  swap-left (SourceTargetSwapRel-⇑ˢ rel)
SourceTargetSwapRel-⇑ˢ (swap-both rel) =
  swap-both (SourceTargetSwapRel-⇑ˢ rel)

SourceTargetSwapRel-src≡ :
  ∀ {Δ σ σ′} →
  SourceTargetSwapRel Δ σ σ′ →
  srcStoreⁿ σ ≡ srcStoreⁿ σ′
SourceTargetSwapRel-src≡ swap-here = refl
SourceTargetSwapRel-src≡ (swap-right rel) =
  SourceTargetSwapRel-src≡ rel
SourceTargetSwapRel-src≡ (swap-left {X = X} rel) =
  cong ((X , ★) ∷_) (SourceTargetSwapRel-src≡ rel)
SourceTargetSwapRel-src≡ (swap-both {X = X} {q = q} rel) =
  cong ((X , src q) ∷_) (SourceTargetSwapRel-src≡ rel)

SourceTargetSwapRel-coercionᶜ :
  ∀ {Δ σ σ′ c A B} →
  SourceTargetSwapRel Δ σ σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ ∣ srcStoreⁿ σ′ ⊢ c ∶ᶜ A ⊒ B
SourceTargetSwapRel-coercionᶜ rel cᶜ =
  subst
    (λ Σ → _ ∣ Σ ⊢ _ ∶ᶜ _ ⊒ _)
    (SourceTargetSwapRel-src≡ rel)
    cᶜ

SourceTargetSwapRel-⊒ˢ :
  ∀ {Δ σ σ′ Σ Σ′} →
  SourceTargetSwapRel Δ σ σ′ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ σ′ ꞉ Σ ⊒ˢ Σ′
SourceTargetSwapRel-⊒ˢ swap-here
    (⊒ˢ-left (⊒ˢ-right hA σ⊒)) =
  ⊒ˢ-right hA (⊒ˢ-left σ⊒)
SourceTargetSwapRel-⊒ˢ (swap-right rel) (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right hA (SourceTargetSwapRel-⊒ˢ rel σ⊒)
SourceTargetSwapRel-⊒ˢ (swap-left rel) (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (SourceTargetSwapRel-⊒ˢ rel σ⊒)
SourceTargetSwapRel-⊒ˢ (swap-both rel)
    (⊒ˢ-both hA hA′ s⊒ σ⊒) =
  ⊒ˢ-both hA hA′ s⊒ (SourceTargetSwapRel-⊒ˢ rel σ⊒)

SourceTargetSwapRel-≈ⁿ :
  ∀ {Δ σ σ′ s t A B} →
  SourceTargetSwapRel Δ σ σ′ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ s ≈ t ∶ A ⊒ B
SourceTargetSwapRel-≈ⁿ rel
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (SourceTargetSwapRel-⊒ˢ rel σ⊒)
    wfΣ
    wfΣ′
    s⊒
    t⊒

SourceTargetSwapRel-compose-left :
  ∀ {Δ σ σ′ q s r A B} →
  SourceTargetSwapRel Δ σ σ′ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
SourceTargetSwapRel-compose-left rel
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒
    (SourceTargetSwapRel-≈ⁿ rel q⨟s≈r)

SourceTargetSwapRel-compose-right :
  ∀ {Δ σ σ′ r t p A B} →
  SourceTargetSwapRel Δ σ σ′ →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
SourceTargetSwapRel-compose-right rel
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒
    (SourceTargetSwapRel-≈ⁿ rel r≈t⨟p)

-- Attempt 74.  A structural term transport for arbitrary
-- `SourceTargetSwapRel` almost works, but Agda exposes the unsound case:
-- `swap-right swap-here` through `split`.  That case moves the distinguished
-- source-only marker of a split past a following target-only entry, so the
-- result no longer has the `target-only, source-only` store shape required to
-- rebuild `split`.  The safe relation for the `⊒Λ` branch must therefore be
-- split-aware, not merely a closure of adjacent source/target swaps.
data SplitSourceTargetSwapView :
  ∀ {Δ α A αᵢ σ τ} →
  SourceTargetSwapRel Δ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) τ →
  Set where

  split-swap-safe :
    ∀ {Δ α A αᵢ σ σ′}
    (rel : SourceTargetSwapRel Δ σ σ′) →
    SplitSourceTargetSwapView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ}
      (swap-right (swap-left rel))

  split-swap-unsafe :
    ∀ {Δ α A αᵢ Y B σ} →
    SplitSourceTargetSwapView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ}
      (swap-right (swap-here {X = αᵢ} {Y = Y} {A = B} {σ = σ}))

split-source-target-swap-view :
  ∀ {Δ α A αᵢ σ τ}
  (rel : SourceTargetSwapRel Δ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) τ) →
  SplitSourceTargetSwapView rel
split-source-target-swap-view (swap-right swap-here) =
  split-swap-unsafe
split-source-target-swap-view (swap-right (swap-left rel)) =
  split-swap-safe rel

-- Attempt 75.  The split-shaped view above is the first usable split-aware
-- refinement: safe steps can continue structural transport below the marker,
-- while the unsafe case must be discharged by a split catchup/opening argument
-- rather than by rebuilding `split` after a plain store exchange.

data SourceTargetSwapRels : TyCtx → StoreNrw → StoreNrw → Set where
  swaps-refl :
    ∀ {Δ σ} →
    SourceTargetSwapRels Δ σ σ

  swaps-step :
    ∀ {Δ σ σ′ σ″} →
    SourceTargetSwapRel Δ σ σ′ →
    SourceTargetSwapRels Δ σ′ σ″ →
    SourceTargetSwapRels Δ σ σ″

SourceTargetSwapRels-⇑ˢ :
  ∀ {Δ σ σ′} →
  SourceTargetSwapRels Δ σ σ′ →
  SourceTargetSwapRels (suc Δ) (⇑ˢ σ) (⇑ˢ σ′)
SourceTargetSwapRels-⇑ˢ swaps-refl = swaps-refl
SourceTargetSwapRels-⇑ˢ (swaps-step rel rels) =
  swaps-step
    (SourceTargetSwapRel-⇑ˢ rel)
    (SourceTargetSwapRels-⇑ˢ rels)

SourceTargetSwapRels-src≡ :
  ∀ {Δ σ σ′} →
  SourceTargetSwapRels Δ σ σ′ →
  srcStoreⁿ σ ≡ srcStoreⁿ σ′
SourceTargetSwapRels-src≡ swaps-refl = refl
SourceTargetSwapRels-src≡ (swaps-step rel rels) =
  trans (SourceTargetSwapRel-src≡ rel)
    (SourceTargetSwapRels-src≡ rels)

SourceTargetSwapRels-coercionᶜ :
  ∀ {Δ σ σ′ c A B} →
  SourceTargetSwapRels Δ σ σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ ∣ srcStoreⁿ σ′ ⊢ c ∶ᶜ A ⊒ B
SourceTargetSwapRels-coercionᶜ rels cᶜ =
  subst
    (λ Σ → _ ∣ Σ ⊢ _ ∶ᶜ _ ⊒ _)
    (SourceTargetSwapRels-src≡ rels)
    cᶜ

SourceTargetSwapRels-⊒ˢ :
  ∀ {Δ σ σ′ Σ Σ′} →
  SourceTargetSwapRels Δ σ σ′ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ σ′ ꞉ Σ ⊒ˢ Σ′
SourceTargetSwapRels-⊒ˢ swaps-refl σ⊒ = σ⊒
SourceTargetSwapRels-⊒ˢ (swaps-step rel rels) σ⊒ =
  SourceTargetSwapRels-⊒ˢ rels
    (SourceTargetSwapRel-⊒ˢ rel σ⊒)

SourceTargetSwapRels-≈ⁿ :
  ∀ {Δ σ σ′ s t A B} →
  SourceTargetSwapRels Δ σ σ′ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ s ≈ t ∶ A ⊒ B
SourceTargetSwapRels-≈ⁿ swaps-refl s≈t = s≈t
SourceTargetSwapRels-≈ⁿ (swaps-step rel rels) s≈t =
  SourceTargetSwapRels-≈ⁿ rels
    (SourceTargetSwapRel-≈ⁿ rel s≈t)

SourceTargetSwapRels-compose-left :
  ∀ {Δ σ σ′ q s r A B} →
  SourceTargetSwapRels Δ σ σ′ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
SourceTargetSwapRels-compose-left swaps-refl q⨟s≈r = q⨟s≈r
SourceTargetSwapRels-compose-left (swaps-step rel rels) q⨟s≈r =
  SourceTargetSwapRels-compose-left rels
    (SourceTargetSwapRel-compose-left rel q⨟s≈r)

SourceTargetSwapRels-compose-right :
  ∀ {Δ σ σ′ r t p A B} →
  SourceTargetSwapRels Δ σ σ′ →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
SourceTargetSwapRels-compose-right swaps-refl r≈t⨟p = r≈t⨟p
SourceTargetSwapRels-compose-right (swaps-step rel rels) r≈t⨟p =
  SourceTargetSwapRels-compose-right rels
    (SourceTargetSwapRel-compose-right rel r≈t⨟p)

SourceTargetSwapRels-right :
  ∀ {Δ X A σ σ′} →
  SourceTargetSwapRels Δ σ σ′ →
  SourceTargetSwapRels Δ
    ((X ꞉= A ⊒) ∷ σ)
    ((X ꞉= A ⊒) ∷ σ′)
SourceTargetSwapRels-right swaps-refl = swaps-refl
SourceTargetSwapRels-right (swaps-step rel rels) =
  swaps-step (swap-right rel) (SourceTargetSwapRels-right rels)

SourceTargetSwapRels-left :
  ∀ {Δ X σ σ′} →
  SourceTargetSwapRels Δ σ σ′ →
  SourceTargetSwapRels Δ
    ((⊒ X ꞉=☆) ∷ σ)
    ((⊒ X ꞉=☆) ∷ σ′)
SourceTargetSwapRels-left swaps-refl = swaps-refl
SourceTargetSwapRels-left (swaps-step rel rels) =
  swaps-step (swap-left rel) (SourceTargetSwapRels-left rels)

SourceTargetSwapRels-both :
  ∀ {Δ X q σ σ′} →
  SourceTargetSwapRels Δ σ σ′ →
  SourceTargetSwapRels Δ
    ((X ꞉ q) ∷ σ)
    ((X ꞉ q) ∷ σ′)
SourceTargetSwapRels-both swaps-refl = swaps-refl
SourceTargetSwapRels-both (swaps-step rel rels) =
  swaps-step (swap-both rel) (SourceTargetSwapRels-both rels)

split-source-target-safe-rebuild :
  ∀ {Δ α A αᵢ σ σ′ γ N N′ p q C D} →
  (rels : SourceTargetSwapRels Δ σ σ′) →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
    ⊢ q ∶ᶜ ★ ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
    ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉ q) ∷ σ′ ∣ γ
    ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ →
  Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ′ ∣ γ
    ⊢ N [ αᵢ ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ
split-source-target-safe-rebuild
    {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ} {σ = σ} {σ′ = σ′}
    rels qᶜ pαᶜ body =
  split
    (SourceTargetSwapRels-coercionᶜ
      splitRels
      qᶜ)
    (SourceTargetSwapRels-coercionᶜ
      splitRels
      pαᶜ)
    body
  where
    splitRels :
      SourceTargetSwapRels Δ
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ′)
    splitRels =
      SourceTargetSwapRels-right {X = α} {A = A}
        (SourceTargetSwapRels-left {X = αᵢ} rels)

-- Attempt 78.  The safe side of split-aware replay can now be rebuilt without
-- reopening the full term derivation: once the recursive premise has been
-- transported below the split marker, `split-source-target-safe-rebuild`
-- moves the split side conditions through the lifted swap closure and
-- reconstructs the outer `split`.  The unsafe first-step case from
-- `SplitSourceTargetSwapsView` remains the part that must be handled by the
-- split/opening catchup argument.

source-target-bubble-empty :
  ∀ {Δ σ} →
  SourceTargetSwapRels Δ
    (renameStoreNrw swap01ᵗ
      ((⊒ zero ꞉=☆) ∷ ⇑ˢ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)))
    ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
source-target-bubble-empty {σ = σ} =
  subst
    (λ τ → SourceTargetSwapRels _
      ((⊒ suc zero ꞉=☆) ∷ (zero ꞉= ★ ⊒) ∷
        renameStoreNrw swap01ᵗ (⇑ˢ (⇑ˢ σ)))
      ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ τ))
    (renameStoreNrw-swap01-⇑ˢ⇑ˢ σ)
    (swaps-step swap-here swaps-refl)

source-target-bubble-empty-coercionᶜ :
  ∀ {Δ σ c A B} →
  suc (suc Δ) ∣
    srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ c ∶ᶜ A ⊒ B →
  suc (suc Δ) ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ renameᶜ swap01ᵗ c
      ∶ᶜ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
source-target-bubble-empty-coercionᶜ {σ = σ} cᶜ =
  SourceTargetSwapRels-coercionᶜ
    (source-target-bubble-empty {σ = σ})
    (renameStoreNrw-coercionᶜ
      {σ = (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)}
      TyRenameWf-swap01
      cᶜ)

source-target-bubble-empty-≈ⁿ :
  ∀ {Δ σ s t A B} →
  suc (suc Δ) ∣
    (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)
    ⊢ s ≈ t ∶ A ⊒ B →
  suc (suc Δ) ∣
    (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)
    ⊢ renameᶜ swap01ᵗ s ≈ renameᶜ swap01ᵗ t
      ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
source-target-bubble-empty-≈ⁿ {σ = σ} s≈t =
  SourceTargetSwapRels-≈ⁿ
    (source-target-bubble-empty {σ = σ})
    (≈ⁿ-rename-swap01ᵗ s≈t)

source-target-raise0-srcStore :
  ∀ σ →
  srcStoreⁿ
    (renameStoreNrw raise0ᵗ
      ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)))
  ≡
  srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
source-target-raise0-srcStore σ =
  cong ((suc zero , ★) ∷_)
    (cong srcStoreⁿ (renameStoreNrw-raise0-⇑ˢ⇑ˢ σ))

data SplitSourceTargetSwapsView :
  ∀ {Δ α A αᵢ σ τ} →
  SourceTargetSwapRels Δ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) τ →
  Set where

  split-swaps-refl :
    ∀ {Δ α A αᵢ σ} →
    SplitSourceTargetSwapsView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ} {σ = σ}
      swaps-refl

  split-swaps-safe-step :
    ∀ {Δ α A αᵢ σ σ′ τ}
    (rel : SourceTargetSwapRel Δ σ σ′) →
    (rels :
      SourceTargetSwapRels Δ
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ′)
        τ) →
    SplitSourceTargetSwapsView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ} {σ = σ}
      (swaps-step (swap-right (swap-left rel)) rels)

  split-swaps-unsafe-step :
    ∀ {Δ α A αᵢ Y B σ τ}
    (rels :
      SourceTargetSwapRels Δ
        ((α ꞉= A ⊒) ∷ (Y ꞉= B ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        τ) →
    SplitSourceTargetSwapsView
      {Δ = Δ} {α = α} {A = A} {αᵢ = αᵢ}
      (swaps-step
        (swap-right (swap-here {X = αᵢ} {Y = Y} {A = B} {σ = σ}))
        rels)

split-source-target-swaps-view :
  ∀ {Δ α A αᵢ σ τ}
  (rels :
    SourceTargetSwapRels Δ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) τ) →
  SplitSourceTargetSwapsView rels
split-source-target-swaps-view swaps-refl =
  split-swaps-refl
split-source-target-swaps-view (swaps-step rel rels)
    with split-source-target-swap-view rel
split-source-target-swaps-view
    (swaps-step .(swap-right (swap-left rel)) rels)
    | split-swap-safe rel =
  split-swaps-safe-step rel rels
split-source-target-swaps-view
    (swaps-step .(swap-right swap-here) rels)
    | split-swap-unsafe =
  split-swaps-unsafe-step rels

split-source-target-swaps-safe-view :
  ∀ {Δ α A αᵢ σ σ′}
  (rels : SourceTargetSwapRels Δ σ σ′) →
  SplitSourceTargetSwapsView
    (SourceTargetSwapRels-right {X = α} {A = A}
      (SourceTargetSwapRels-left {X = αᵢ} rels))
split-source-target-swaps-safe-view swaps-refl =
  split-swaps-refl
split-source-target-swaps-safe-view (swaps-step rel rels) =
  split-swaps-safe-step rel
    (SourceTargetSwapRels-right (SourceTargetSwapRels-left rels))

-- Attempt 76.  Lifting the split view to closure form makes the next replay
-- theorem structurally possible: it can consume zero swaps, continue below the
-- split marker for a safe first step, or hand the unsafe first step to the
-- split/opening catchup machinery before replaying the remaining swaps.

ext-suc-injective :
  RenameInjective (extᵗ suc)
ext-suc-injective {zero} {zero} refl = refl
ext-suc-injective {zero} {suc Y} ()
ext-suc-injective {suc X} {zero} ()
ext-suc-injective {suc X} {suc Y} eq = suc-injective eq

ext-suc-not-one :
  ∀ X →
  suc zero ≡ extᵗ suc X →
  ⊥
ext-suc-not-one zero ()
ext-suc-not-one (suc X) ()

TyRenameWf-ext-suc-bound :
  ∀ {α} →
  TyRenameWf α (extᵗ suc α) (extᵗ suc)
TyRenameWf-ext-suc-bound {zero} ()
TyRenameWf-ext-suc-bound {suc α} =
  TyRenameWf-ext TyRenameWf-suc

TyRenameWf-ext-suc-wide :
  ∀ {Δ} →
  TyRenameWf Δ (suc (suc Δ)) (extᵗ suc)
TyRenameWf-ext-suc-wide {zero} ()
TyRenameWf-ext-suc-wide {suc Δ} {zero} z<s = z<s
TyRenameWf-ext-suc-wide {suc Δ} {suc X} (s<s X<Δ) =
  s<s (s<s (m<n⇒m<1+n X<Δ))

renameStoreᵗ-cong :
  ∀ {ρ τ} →
  (∀ X → ρ X ≡ τ X) →
  ∀ Σ →
  renameStoreᵗ ρ Σ ≡ renameStoreᵗ τ Σ
renameStoreᵗ-cong rel [] = refl
renameStoreᵗ-cong {ρ = ρ} {τ = τ} rel ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ (rel α) (rename-cong rel A))
    (renameStoreᵗ-cong rel Σ)

∈-renameStoreᵗ-inv :
  ∀ ρ {Σ β B} →
  (β , B) ∈ renameStoreᵗ ρ Σ →
  ∃[ α ] ∃[ A ]
    (β ≡ ρ α × B ≡ renameᵗ ρ A × (α , A) ∈ Σ)
∈-renameStoreᵗ-inv ρ {Σ = []} ()
∈-renameStoreᵗ-inv ρ {Σ = (α , A) ∷ Σ} (here refl) =
  α , A , refl , refl , here refl
∈-renameStoreᵗ-inv ρ {Σ = (α , A) ∷ Σ} (there β∈Σ)
    with ∈-renameStoreᵗ-inv ρ β∈Σ
∈-renameStoreᵗ-inv ρ {Σ = (α , A) ∷ Σ} (there β∈Σ)
    | γ , C , γ≡ , C≡ , γ∈Σ =
  γ , C , γ≡ , C≡ , there γ∈Σ

StoreUnique-renameᵗ :
  ∀ {ρ Σ} →
  RenameInjective ρ →
  StoreUnique Σ →
  StoreUnique (renameStoreᵗ ρ Σ)
StoreUnique-renameᵗ {ρ = ρ} inj uniqueΣ α∈Σ β∈Σ
    with ∈-renameStoreᵗ-inv ρ α∈Σ
       | ∈-renameStoreᵗ-inv ρ β∈Σ
StoreUnique-renameᵗ {ρ = ρ} inj uniqueΣ α∈Σ β∈Σ
    | α , A , refl , refl , α∈Σ′
    | γ , B , α≡γ , B≡ , γ∈Σ′ =
  trans
    (cong (renameᵗ ρ)
      (uniqueΣ α∈Σ′
        (subst (λ X → (X , B) ∈ _) (sym (inj α≡γ)) γ∈Σ′)))
    (sym B≡)

StoreDetWf-rename-ext-suc :
  ∀ {Δ Σ} →
  StoreDetWf Δ Σ →
  StoreDetWf (suc (suc Δ)) (renameStoreᵗ (extᵗ suc) Σ)
StoreDetWf-rename-ext-suc wfΣ =
  record
    { at = StoreWfAt-rename TyRenameWf-ext-suc-wide (StoreDetWf.at wfΣ)
    ; wfOlder = wfOlder′
    ; unique = StoreUnique-renameᵗ ext-suc-injective (StoreDetWf.unique wfΣ)
    }
  where
    wfOlder′ :
      ∀ {α A} →
      (α , A) ∈ renameStoreᵗ (extᵗ suc) _ →
      WfTy α A
    wfOlder′ h
        with ∈-renameStoreᵗ-inv (extᵗ suc) h
    wfOlder′ h | α , A , refl , refl , α∈Σ =
      renameᵗ-preserves-WfTy
        (StoreDetWf.wfOlder wfΣ α∈Σ)
        TyRenameWf-ext-suc-bound

renameStoreᵗ-swap01-inst :
  ∀ Σ →
  renameStoreᵗ swap01ᵗ ((zero , ★) ∷ ⟰ᵗ Σ) ≡
    (suc zero , ★) ∷ renameStoreᵗ (extᵗ suc) Σ
renameStoreᵗ-swap01-inst Σ =
  cong ((suc zero , ★) ∷_)
    (trans
      (renameStoreᵗ-compose suc swap01ᵗ Σ)
      (renameStoreᵗ-cong swap01ᵗ-after-suc Σ))

renameStoreᵗ-ext-suc-no-one :
  ∀ {Σ A} →
  (suc zero , A) ∈ renameStoreᵗ (extᵗ suc) Σ →
  ⊥
renameStoreᵗ-ext-suc-no-one h
    with ∈-renameStoreᵗ-inv (extᵗ suc) h
renameStoreᵗ-ext-suc-no-one h | α , A , eq , refl , α∈Σ =
  ext-suc-not-one α eq

StoreDetWf-cons-one-star :
  ∀ {Δ Σ} →
  StoreDetWf (suc (suc Δ)) Σ →
  (∀ {A} → (suc zero , A) ∈ Σ → ⊥) →
  StoreDetWf (suc (suc Δ)) ((suc zero , ★) ∷ Σ)
StoreDetWf-cons-one-star wfΣ no-one =
  record
    { at = StoreWfAt-cons (s<s z<s) wf★ (StoreDetWf.at wfΣ)
    ; wfOlder = wfOlder′
    ; unique = unique′
    }
  where
    wfOlder′ :
      ∀ {α A} →
      (α , A) ∈ ((suc zero , ★) ∷ _) →
      WfTy α A
    wfOlder′ (here refl) = wf★
    wfOlder′ (there h) = StoreDetWf.wfOlder wfΣ h

    unique′ :
      StoreUnique ((suc zero , ★) ∷ _)
    unique′ (here refl) (here refl) = refl
    unique′ (here refl) (there h) = ⊥-elim (no-one h)
    unique′ (there h) (here refl) = ⊥-elim (no-one h)
    unique′ (there h₁) (there h₂) = StoreDetWf.unique wfΣ h₁ h₂

StoreDetWf-swap01-inst :
  ∀ {Δ Σ} →
  StoreDetWf Δ Σ →
  StoreDetWf (suc (suc Δ))
    (renameStoreᵗ swap01ᵗ ((zero , ★) ∷ ⟰ᵗ Σ))
StoreDetWf-swap01-inst {Σ = Σ} wfΣ =
  subst
    (StoreDetWf _)
    (sym (renameStoreᵗ-swap01-inst Σ))
    (StoreDetWf-cons-one-star
      (StoreDetWf-rename-ext-suc wfΣ)
      renameStoreᵗ-ext-suc-no-one)

⨟ⁿ-renameᵗ-determined :
  ∀ {ρ μ ν Δ Δ′ Σ A B C s t}
    (hρ : TyRenameWf Δ Δ′ ρ) →
  (hμ : ModeRename ρ μ ν) →
  (wfΣ : StoreDetWf Δ Σ) →
  (wfΣ′ : StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B) →
  (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ B ⊒ C) →
  proj₁ (_⨟ⁿ_ {wfΣ = wfΣ′}
    (narrow-renameᵗ {ν = ν} hρ hμ s⊒)
    (narrow-renameᵗ {ν = ν} hρ hμ t⊒))
  ≡ renameᶜ ρ (proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} s⊒ t⊒))
⨟ⁿ-renameᵗ-determined {ν = νᵐ} hρ hμ wfΣ wfΣ′ s⊒ t⊒ =
  narrowing-determinedᵐ wfΣ′
    (proj₂ (_⨟ⁿ_ {wfΣ = wfΣ′}
      (narrow-renameᵗ {ν = νᵐ} hρ hμ s⊒)
      (narrow-renameᵗ {ν = νᵐ} hρ hμ t⊒)))
    (narrow-renameᵗ {ν = νᵐ} hρ hμ
      (proj₂ (_⨟ⁿ_ {wfΣ = wfΣ} s⊒ t⊒)))

⨟ʷ-renameᵗ-determined :
  ∀ {ρ μ ν Δ Δ′ Σ A B C s t}
    (hρ : TyRenameWf Δ Δ′ ρ) →
  (hμ : ModeRename ρ μ ν) →
  (wfΣ : StoreDetWf Δ Σ) →
  (wfΣ′ : StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  (s⊑ : μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B) →
  (t⊑ : μ ∣ Δ ∣ Σ ⊢ t ∶ B ⊑ C) →
  proj₁ (_⨟ʷ_ {wfΣ = wfΣ′}
    (widen-renameᵗ {ν = ν} hρ hμ s⊑)
    (widen-renameᵗ {ν = ν} hρ hμ t⊑))
  ≡ renameᶜ ρ (proj₁ (_⨟ʷ_ {wfΣ = wfΣ} s⊑ t⊑))
⨟ʷ-renameᵗ-determined {ν = νᵐ} hρ hμ wfΣ wfΣ′ s⊑ t⊑ =
  widening-determinedᵐ wfΣ′
    (proj₂ (_⨟ʷ_ {wfΣ = wfΣ′}
      (widen-renameᵗ {ν = νᵐ} hρ hμ s⊑)
      (widen-renameᵗ {ν = νᵐ} hρ hμ t⊑)))
    (widen-renameᵗ {ν = νᵐ} hρ hμ
      (proj₂ (_⨟ʷ_ {wfΣ = wfΣ} s⊑ t⊑)))

ComposeLeftRenameOk :
  ∀ {Δ σ q s r A B} →
  Renameᵗ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Set
ComposeLeftRenameOk ρ (compose-leftⁿ {μ = μ} wfΣ q⊒ s⊒ q⨟s≈r) =
  ∃[ target ] ModeRename ρ μ target × ≈ⁿRenameOk ρ q⨟s≈r

ComposeRightRenameOk :
  ∀ {Δ σ r t p A B} →
  Renameᵗ →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Set
ComposeRightRenameOk ρ (compose-rightⁿ {μ = μ} wfΣ t⊒ p⊒ r≈t⨟p) =
  ∃[ target ] ModeRename ρ μ target × ≈ⁿRenameOk ρ r≈t⨟p

compose-leftⁿ-rename-guarded-components :
  ∀ {Δ Δ′ σ Σ μ q s r A B C ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  (wfΣ : StoreDetWf Δ Σ) →
  (wfΣ′ : StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C) →
  (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B) →
  (q⨟s≈r : Δ ∣ σ ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B) →
  (∃[ target ] ModeRename ρ μ target × ≈ⁿRenameOk ρ q⨟s≈r) →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s
      ≈ renameᶜ ρ r ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-leftⁿ-rename-guarded-components
    {ρ = ρ} hρ wfΣ wfΣ′ q⊒ s⊒ q⨟s≈r
    (target , hμ , ok≈) =
  compose-leftⁿ wfΣ′ q⊒′ s⊒′ eq′
  where
    q⊒′ =
      narrow-renameᵗ {ν = target} hρ hμ q⊒

    s⊒′ =
      narrow-renameᵗ {ν = target} hρ hμ s⊒

    u≡ =
      ⨟ⁿ-renameᵗ-determined
        {ν = target}
        hρ hμ wfΣ wfΣ′ q⊒ s⊒

    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ u ≈ renameᶜ ρ _ ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-rename-guarded hρ q⨟s≈r ok≈)

compose-rightⁿ-rename-guarded-components :
  ∀ {Δ Δ′ σ Σ μ r t p A B C ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  (wfΣ : StoreDetWf Δ Σ) →
  (wfΣ′ : StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ C) →
  (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ C ⊒ B) →
  (r≈t⨟p : Δ ∣ σ ⊢
    r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B) →
  (∃[ target ] ModeRename ρ μ target × ≈ⁿRenameOk ρ r≈t⨟p) →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ r
      ≈ renameᶜ ρ t ⨾ⁿ renameᶜ ρ p
        ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-rightⁿ-rename-guarded-components
    {ρ = ρ} hρ wfΣ wfΣ′ t⊒ p⊒ r≈t⨟p
    (target , hμ , ok≈) =
  compose-rightⁿ wfΣ′ t⊒′ p⊒′ eq′
  where
    t⊒′ =
      narrow-renameᵗ {ν = target} hρ hμ t⊒

    p⊒′ =
      narrow-renameᵗ {ν = target} hρ hμ p⊒

    u≡ =
      ⨟ⁿ-renameᵗ-determined
        {ν = target}
        hρ hμ wfΣ wfΣ′ t⊒ p⊒

    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ renameᶜ ρ _ ≈ u ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-rename-guarded hρ r≈t⨟p ok≈)

ComposeLeftRenameLocalOk :
  ∀ {Δ σ q s r A B} →
  TyCtx →
  Renameᵗ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Set₁
ComposeLeftRenameLocalOk Δ′ ρ
    (compose-leftⁿ {Σ = Σ} {μ = μ} wfΣ q⊒ s⊒ q⨟s≈r) =
  StoreDetWf Δ′ (renameStoreᵗ ρ Σ) ×
  ∃[ target ] ModeRename ρ μ target × ≈ⁿRenameOk ρ q⨟s≈r

ComposeRightRenameLocalOk :
  ∀ {Δ σ r t p A B} →
  TyCtx →
  Renameᵗ →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Set₁
ComposeRightRenameLocalOk Δ′ ρ
    (compose-rightⁿ {Σ = Σ} {μ = μ} wfΣ t⊒ p⊒ r≈t⨟p) =
  StoreDetWf Δ′ (renameStoreᵗ ρ Σ) ×
  ∃[ target ] ModeRename ρ μ target × ≈ⁿRenameOk ρ r≈t⨟p

compose-leftⁿ-rename-local :
  ∀ {Δ Δ′ σ q s r A B ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  (q⨟s≈r : Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B) →
  ComposeLeftRenameLocalOk Δ′ ρ q⨟s≈r →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s
      ≈ renameᶜ ρ r ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-leftⁿ-rename-local hρ
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
    (wfΣ′ , ok) =
  compose-leftⁿ-rename-guarded-components
    hρ wfΣ wfΣ′ q⊒ s⊒ q⨟s≈r ok

compose-rightⁿ-rename-local :
  ∀ {Δ Δ′ σ r t p A B ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  (r≈t⨟p : Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B) →
  ComposeRightRenameLocalOk Δ′ ρ r≈t⨟p →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ r
      ≈ renameᶜ ρ t ⨾ⁿ renameᶜ ρ p
        ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-rightⁿ-rename-local hρ
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p)
    (wfΣ′ , ok) =
  compose-rightⁿ-rename-guarded-components
    hρ wfΣ wfΣ′ t⊒ p⊒ r≈t⨟p ok

record ⊤₁ : Set₁ where
  constructor tt₁

data ⊥₁ : Set₁ where

⊥₁-elim :
  ∀ {A : Set₁} →
  ⊥₁ →
  A
⊥₁-elim ()

TermRenameLocalOk :
  ∀ {Δ σ γ M T c} →
  TyCtx →
  Renameᵗ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c →
  Set₁
TermRenameLocalOk Δ′ ρ (extend qᶜ pαᶜ M⊒T) =
  TermRenameLocalOk Δ′ ρ M⊒T
TermRenameLocalOk Δ′ ρ (split qᶜ pαᶜ M⊒T) =
  TermRenameLocalOk Δ′ ρ M⊒T
TermRenameLocalOk Δ′ ρ (⊒blame pᶜ) = ⊤₁
TermRenameLocalOk Δ′ ρ (x⊒x pᶜ x∋p) = ⊤₁
TermRenameLocalOk Δ′ ρ (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  TermRenameLocalOk Δ′ ρ N⊒N′
TermRenameLocalOk Δ′ ρ (·⊒· qᶜ L⊒L′ M⊒M′) =
  TermRenameLocalOk Δ′ ρ L⊒L′ ×
  TermRenameLocalOk Δ′ ρ M⊒M′
TermRenameLocalOk Δ′ ρ (Λ⊒Λ allᶜ vV V⊒V′) =
  TermRenameLocalOk (suc Δ′) (extᵗ ρ) V⊒V′
TermRenameLocalOk Δ′ ρ (⊒Λ pᶜ N⊒V′) =
  TermRenameLocalOk (suc Δ′) (extᵗ ρ) N⊒V′
TermRenameLocalOk Δ′ ρ (⊒⟨ν⟩ pᶜ i N⊒V′s) =
  TermRenameLocalOk (suc Δ′) (extᵗ ρ) N⊒V′s
TermRenameLocalOk Δ′ ρ (α⊒α γ′≡ qᶜ pαᶜ L⊒L′) = ⊥₁
TermRenameLocalOk Δ′ ρ (⊒α γ′≡ pαᶜ L⊒L′) = ⊥₁
TermRenameLocalOk Δ′ ρ (ν⊒ν pᶜ qᶜ N⊒N′) =
  TermRenameLocalOk (suc Δ′) (extᵗ ρ) N⊒N′
TermRenameLocalOk Δ′ ρ (⊒ν pᶜ N⊒N′) =
  TermRenameLocalOk (suc Δ′) (extᵗ ρ) N⊒N′
TermRenameLocalOk Δ′ ρ (ν⊒ pᶜ N⊒N′) =
  TermRenameLocalOk (suc Δ′) (extᵗ ρ) N⊒N′
TermRenameLocalOk Δ′ ρ (κ⊒κ κ) = ⊤₁
TermRenameLocalOk Δ′ ρ (⊕⊒⊕ M⊒M′ N⊒N′) =
  TermRenameLocalOk Δ′ ρ M⊒M′ ×
  TermRenameLocalOk Δ′ ρ N⊒N′
TermRenameLocalOk Δ′ ρ (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  ComposeLeftRenameLocalOk Δ′ ρ q⨟s≈r ×
  TermRenameLocalOk Δ′ ρ M⊒M′
TermRenameLocalOk Δ′ ρ (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  ComposeLeftRenameLocalOk Δ′ ρ q⨟s≈r ×
  TermRenameLocalOk Δ′ ρ M⊒M′
TermRenameLocalOk Δ′ ρ (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  ComposeRightRenameLocalOk Δ′ ρ r≈t⨟p ×
  TermRenameLocalOk Δ′ ρ M⊒M′
TermRenameLocalOk Δ′ ρ (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  ComposeRightRenameLocalOk Δ′ ρ r≈t⨟p ×
  TermRenameLocalOk Δ′ ρ M⊒M′

term-rename-local-⊒Λ-build :
  ∀ {Δ Δ′ σ γ A B N V′ p ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ′ ∣
    renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣
    renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
      ⊒ renameᵗᵐ (extᵗ ρ) V′ ∶ renameᶜ (extᵗ ρ) p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ N ⊒ renameᵗᵐ ρ (Λ V′) ∶ renameᶜ ρ (gen A p)
term-rename-local-⊒Λ-build {σ = σ} {γ = γ} {N = N} {ρ = ρ}
    hρ pᶜ body =
  ⊒Λ
    (renameStoreNrw-coercionᶜ hρ pᶜ)
    (subst
      (λ S → _ ∣ S ∣ ⇑ᵍ (renameCtxNrw _ γ)
        ⊢ ⇑ᵗᵐ (renameᵗᵐ ρ N) ⊒ _ ∶ _)
      store≡
      (subst
        (λ Γ → _ ∣ renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)
          ∣ Γ ⊢ ⇑ᵗᵐ (renameᵗᵐ ρ N) ⊒ _ ∶ _)
        ctx≡
        (subst
          (λ M → _ ∣ renameStoreNrw (extᵗ ρ)
            ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣
            renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
            ⊢ M ⊒ _ ∶ _)
          src≡
          body)))
  where
    store≡ :
      renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ≡
      (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ)
    store≡ = cong ((zero ꞉= ★ ⊒) ∷_) (renameStoreNrw-⇑ˢ ρ σ)

    ctx≡ :
      renameCtxNrw (extᵗ ρ) (⇑ᵍ γ) ≡ ⇑ᵍ (renameCtxNrw ρ γ)
    ctx≡ = renameCtxNrw-⇑ᵍ ρ γ

    src≡ :
      renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N) ≡ ⇑ᵗᵐ (renameᵗᵐ ρ N)
    src≡ = renameᵗᵐ-ext-suc-comm ρ N

term-rename-local-Λ⊒Λ-build :
  ∀ {Δ Δ′ σ γ A B V V′ p ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  Δ ∣ srcStoreⁿ σ ⊢ `∀ p ∶ᶜ `∀ A ⊒ `∀ B →
  Value V →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ) (⇑ˢ σ) ∣
    renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) V
      ⊒ renameᵗᵐ (extᵗ ρ) V′ ∶ renameᶜ (extᵗ ρ) p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ (Λ V) ⊒ renameᵗᵐ ρ (Λ V′)
      ∶ renameᶜ ρ (`∀ p)
term-rename-local-Λ⊒Λ-build {σ = σ} {γ = γ} {V = V} {ρ = ρ}
    hρ allᶜ vV body =
  Λ⊒Λ
    (renameStoreNrw-coercionᶜ hρ allᶜ)
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
    (subst
      (λ S → _ ∣ S ∣ ⇑ᵍ (renameCtxNrw ρ γ)
        ⊢ renameᵗᵐ (extᵗ ρ) V ⊒ _ ∶ _)
      store≡
      (subst
        (λ Γ → _ ∣ renameStoreNrw (extᵗ ρ) (⇑ˢ σ) ∣ Γ
          ⊢ renameᵗᵐ (extᵗ ρ) V ⊒ _ ∶ _)
        ctx≡
        body))
  where
    store≡ :
      renameStoreNrw (extᵗ ρ) (⇑ˢ σ) ≡
      ⇑ˢ (renameStoreNrw ρ σ)
    store≡ = renameStoreNrw-⇑ˢ ρ σ

    ctx≡ :
      renameCtxNrw (extᵗ ρ) (⇑ᵍ γ) ≡ ⇑ᵍ (renameCtxNrw ρ γ)
    ctx≡ = renameCtxNrw-⇑ᵍ ρ γ

term-rename-local-⊒⟨ν⟩-build :
  ∀ {Δ Δ′ σ γ A B N V′ p s ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Inert s →
  suc Δ′ ∣
    renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣
    renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
      ⊒ renameᵗᵐ (extᵗ ρ) (V′ ⟨ s ⟩)
      ∶ renameᶜ (extᵗ ρ) p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ N ⊒ renameᵗᵐ ρ (V′ ⟨ gen A s ⟩)
      ∶ renameᶜ ρ (gen A p)
term-rename-local-⊒⟨ν⟩-build {σ = σ} {γ = γ} {N = N} {ρ = ρ}
    hρ pᶜ i body =
  ⊒⟨ν⟩
    (renameStoreNrw-coercionᶜ hρ pᶜ)
    (renameᶜ-preserves-Inert (extᵗ ρ) i)
    (subst
      (λ S → _ ∣ S ∣ ⇑ᵍ (renameCtxNrw _ γ)
        ⊢ ⇑ᵗᵐ (renameᵗᵐ ρ N) ⊒ _ ∶ _)
      store≡
      (subst
        (λ Γ → _ ∣ renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)
          ∣ Γ ⊢ ⇑ᵗᵐ (renameᵗᵐ ρ N) ⊒ _ ∶ _)
        ctx≡
        (subst
          (λ M → _ ∣ renameStoreNrw (extᵗ ρ)
            ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣
            renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
            ⊢ M ⊒ _ ∶ _)
          src≡
          body)))
  where
    store≡ :
      renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ≡
      (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ)
    store≡ = cong ((zero ꞉= ★ ⊒) ∷_) (renameStoreNrw-⇑ˢ ρ σ)

    ctx≡ :
      renameCtxNrw (extᵗ ρ) (⇑ᵍ γ) ≡ ⇑ᵍ (renameCtxNrw ρ γ)
    ctx≡ = renameCtxNrw-⇑ᵍ ρ γ

    src≡ :
      renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N) ≡ ⇑ᵗᵐ (renameᵗᵐ ρ N)
    src≡ = renameᵗᵐ-ext-suc-comm ρ N

compose-leftⁿ-rename-guarded :
  ∀ {Δ Δ′ σ q s r A B ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  (∀ {Σ} →
    StoreDetWf Δ Σ →
    StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  (q⨟s≈r : Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B) →
  ComposeLeftRenameOk ρ q⨟s≈r →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s
      ≈ renameᶜ ρ r ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-leftⁿ-rename-guarded hρ detMap
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) ok =
  compose-leftⁿ-rename-guarded-components
    hρ wfΣ (detMap wfΣ) q⊒ s⊒ q⨟s≈r ok

compose-rightⁿ-rename-guarded :
  ∀ {Δ Δ′ σ r t p A B ρ} →
  (hρ : TyRenameWf Δ Δ′ ρ) →
  (∀ {Σ} →
    StoreDetWf Δ Σ →
    StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  (r≈t⨟p : Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B) →
  ComposeRightRenameOk ρ r≈t⨟p →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ r
      ≈ renameᶜ ρ t ⨾ⁿ renameᶜ ρ p
        ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-rightⁿ-rename-guarded hρ detMap
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) ok =
  compose-rightⁿ-rename-guarded-components
    hρ wfΣ (detMap wfΣ) t⊒ p⊒ r≈t⨟p ok

StoreDetWf-swap01-generic⊥ :
  StoreDetWf (suc (suc zero))
    (renameStoreᵗ swap01ᵗ ((suc zero , ＇ zero) ∷ [])) →
  ⊥
StoreDetWf-swap01-generic⊥ wfΣ
    with StoreDetWf.wfOlder wfΣ (here refl)
... | wfVar ()

StoreDetWf-merge01-different⊥ :
  StoreDetWf (suc (suc zero))
    (renameStoreᵗ merge01ᵗ
      ((zero , ★) ∷ (suc zero , ＇ zero) ∷ [])) →
  ⊥
StoreDetWf-merge01-different⊥ wfΣ
    with StoreDetWf.unique wfΣ (here refl) (there (here refl))
... | ()

TyRenameWf-raise0 :
  ∀ {Δ} →
  TyRenameWf (suc (suc Δ)) (suc (suc Δ)) raise0ᵗ
TyRenameWf-raise0 {X = zero} z<s = s<s z<s
TyRenameWf-raise0 {X = suc zero} (s<s z<s) = s<s z<s
TyRenameWf-raise0 {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s (s<s X<Δ)

modeRename-raise0-tag-or-id :
  ModeRename raise0ᵗ tag-or-idᵈ tag-or-idᵈ
modeRename-raise0-tag-or-id =
  modeRename-tag-or-id raise0ᵗ

modeRename-merge01-tag-or-id :
  ModeRename merge01ᵗ tag-or-idᵈ tag-or-idᵈ
modeRename-merge01-tag-or-id =
  modeRename-tag-or-id merge01ᵗ

modeRename-merge01-from-pieces :
  ∀ {μ ν : ModeEnv} →
  mode≤ (μ zero) (ν zero) ≡ true →
  mode≤ (μ (suc zero)) (ν zero) ≡ true →
  (∀ X → mode≤ (μ (suc (suc X))) (ν (suc (suc X))) ≡ true) →
  ModeRename merge01ᵗ μ ν
modeRename-merge01-from-pieces zero≤ν₀ one≤ν₀ tail zero = zero≤ν₀
modeRename-merge01-from-pieces zero≤ν₀ one≤ν₀ tail (suc zero) =
  one≤ν₀
modeRename-merge01-from-pieces zero≤ν₀ one≤ν₀ tail (suc (suc X)) =
  tail X

modeRename-merge01-head-equal :
  ∀ {μ : ModeEnv} →
  μ zero ≡ μ (suc zero) →
  ModeRename merge01ᵗ μ μ
modeRename-merge01-head-equal {μ = μ} eq =
  modeRename-merge01-from-pieces {ν = μ}
    (modeIncl-refl {μ = μ} zero)
    (subst (λ m → mode≤ (μ (suc zero)) m ≡ true)
      (sym eq)
      (modeIncl-refl {μ = μ} (suc zero)))
    (λ X → modeIncl-refl {μ = μ} (suc (suc X)))

tag-seal01ᵈ : ModeEnv
tag-seal01ᵈ zero = tag-or-id
tag-seal01ᵈ (suc zero) = seal-or-id
tag-seal01ᵈ (suc (suc X)) = id-only

tag-seal-mode≤⊥ :
  ∀ m →
  mode≤ tag-or-id m ≡ true →
  mode≤ seal-or-id m ≡ true →
  ⊥
tag-seal-mode≤⊥ id-only () _
tag-seal-mode≤⊥ tag-or-id _ ()
tag-seal-mode≤⊥ seal-or-id () _

merge01ᵗ-tag-seal-mode-rename⊥ :
  ∀ {ν : ModeEnv} →
  ModeRename merge01ᵗ tag-seal01ᵈ ν →
  ⊥
merge01ᵗ-tag-seal-mode-rename⊥ rel =
  tag-seal-mode≤⊥ _ (rel zero) (rel (suc zero))

source-first-merge01-srcStore :
  ∀ σ →
  srcStoreⁿ
    (renameStoreNrw merge01ᵗ
      ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)))
  ≡
  srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
source-first-merge01-srcStore σ =
  cong ((zero , ★) ∷_)
    (cong srcStoreⁿ (renameStoreNrw-merge01-⇑ˢ⇑ˢ σ))

source-first-merge01-coercionᶜ :
  ∀ {Δ σ c A B} →
  suc (suc Δ) ∣
    srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ c ∶ᶜ A ⊒ B →
  suc (suc Δ) ∣
    srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ renameᶜ merge01ᵗ c
      ∶ᶜ renameᵗ merge01ᵗ A ⊒ renameᵗ merge01ᵗ B
source-first-merge01-coercionᶜ
    {Δ = Δ} {σ = σ} {c = c} {A = A} {B = B} cᶜ =
  subst
    (λ Σ → suc (suc Δ) ∣ Σ ⊢ renameᶜ merge01ᵗ c
      ∶ᶜ renameᵗ merge01ᵗ A ⊒ renameᵗ merge01ᵗ B)
    (source-first-merge01-srcStore σ)
    (renameStoreNrw-coercionᶜ
      {σ = (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)}
      TyRenameWf-merge01
      cᶜ)

source-target-raise0-coercionᶜ :
  ∀ {Δ σ c A B} →
  suc (suc Δ) ∣
    srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ c ∶ᶜ A ⊒ B →
  suc (suc Δ) ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ renameᶜ raise0ᵗ c
      ∶ᶜ renameᵗ raise0ᵗ A ⊒ renameᵗ raise0ᵗ B
source-target-raise0-coercionᶜ
    {Δ = Δ} {σ = σ} {c = c} {A = A} {B = B} cᶜ =
  subst
    (λ Σ → suc (suc Δ) ∣ Σ ⊢ renameᶜ raise0ᵗ c
      ∶ᶜ renameᵗ raise0ᵗ A ⊒ renameᵗ raise0ᵗ B)
    (source-target-raise0-srcStore σ)
    (renameStoreNrw-coercionᶜ
      {σ = (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)}
      TyRenameWf-raise0
      cᶜ)

TyRenameWf-pred-lower :
  ∀ {Δ} →
  TyRenameWf (suc (suc Δ)) (suc Δ) predᵗ
TyRenameWf-pred-lower {X = zero} z<s = z<s
TyRenameWf-pred-lower {X = suc zero} (s<s z<s) = z<s
TyRenameWf-pred-lower {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s X<Δ

renameStoreNrw-pred-⇑ˢ⇑ˢ :
  ∀ σ →
  renameStoreNrw predᵗ (⇑ˢ (⇑ˢ σ)) ≡ ⇑ˢ σ
renameStoreNrw-pred-⇑ˢ⇑ˢ [] = refl
renameStoreNrw-pred-⇑ˢ⇑ˢ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉_ refl (renameᶜ-pred-suc (⇑ᶜ p)))
    (renameStoreNrw-pred-⇑ˢ⇑ˢ σ)
renameStoreNrw-pred-⇑ˢ⇑ˢ ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong₂ _꞉=_⊒ refl (renameᵗ-pred-suc (⇑ᵗ A)))
    (renameStoreNrw-pred-⇑ˢ⇑ˢ σ)
renameStoreNrw-pred-⇑ˢ⇑ˢ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_ refl (renameStoreNrw-pred-⇑ˢ⇑ˢ σ)

renameStoreNrw-pred-source-first :
  ∀ σ →
  renameStoreNrw predᵗ
    ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
  ≡ (⊒ zero ꞉=☆) ∷ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ
renameStoreNrw-pred-source-first σ =
  cong₂ _∷_ refl
    (cong₂ _∷_ refl (renameStoreNrw-pred-⇑ˢ⇑ˢ σ))

renameCtxNrw-pred-⇑ᵍ⇑ᵍ :
  ∀ γ →
  renameCtxNrw predᵗ (⇑ᵍ (⇑ᵍ γ)) ≡ ⇑ᵍ γ
renameCtxNrw-pred-⇑ᵍ⇑ᵍ [] = refl
renameCtxNrw-pred-⇑ᵍ⇑ᵍ (p ∷ γ) =
  cong₂ _∷_
    (renameᶜ-pred-suc (⇑ᶜ p))
    (renameCtxNrw-pred-⇑ᵍ⇑ᵍ γ)

renameᵗᵐ-pred-⇑ᵗᵐ⇑ᵗᵐ :
  ∀ M →
  renameᵗᵐ predᵗ (⇑ᵗᵐ (⇑ᵗᵐ M)) ≡ ⇑ᵗᵐ M
renameᵗᵐ-pred-⇑ᵗᵐ⇑ᵗᵐ M =
  renameᵗᵐ-pred-suc (⇑ᵗᵐ M)

source-first-pred-both-srcStore :
  ∀ σ →
  srcStoreⁿ
    (renameStoreNrw predᵗ
      ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)))
  ≡
  srcStoreⁿ ((zero ꞉ id ★) ∷ ⇑ˢ σ)
source-first-pred-both-srcStore σ =
  cong ((zero , ★) ∷_)
    (cong srcStoreⁿ (renameStoreNrw-pred-⇑ˢ⇑ˢ σ))

source-first-pred-both-coercionᶜ :
  ∀ {Δ σ c A B} →
  suc (suc Δ) ∣
    srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ c ∶ᶜ A ⊒ B →
  suc Δ ∣ srcStoreⁿ ((zero ꞉ id ★) ∷ ⇑ˢ σ)
    ⊢ renameᶜ predᵗ c
      ∶ᶜ renameᵗ predᵗ A ⊒ renameᵗ predᵗ B
source-first-pred-both-coercionᶜ {Δ = Δ} {σ = σ} {c = c}
    {A = A} {B = B} cᶜ =
  subst
    (λ Σ → suc Δ ∣ Σ ⊢ renameᶜ predᵗ c
      ∶ᶜ renameᵗ predᵗ A ⊒ renameᵗ predᵗ B)
    (source-first-pred-both-srcStore σ)
    (renameStoreNrw-coercionᶜ
      {σ = (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)}
      TyRenameWf-pred-lower
      cᶜ)

renameᵗ-raise0-pred :
  ∀ A →
  renameᵗ raise0ᵗ A ≡ ⇑ᵗ (renameᵗ predᵗ A)
renameᵗ-raise0-pred A =
  sym (renameᵗ-compose predᵗ suc A)

renameᶜ-raise0-pred :
  ∀ c →
  renameᶜ raise0ᵗ c ≡ ⇑ᶜ (renameᶜ predᵗ c)
renameᶜ-raise0-pred c =
  sym (renameᶜ-compose predᵗ suc c)

renameᵗᵐ-raise0-pred :
  ∀ M →
  renameᵗᵐ raise0ᵗ M ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ M)
renameᵗᵐ-raise0-pred M =
  sym (renameᵗᵐ-compose predᵗ suc M)

renameStoreNrw-raise0-pred :
  ∀ σ →
  renameStoreNrw raise0ᵗ σ ≡ ⇑ˢ (renameStoreNrw predᵗ σ)
renameStoreNrw-raise0-pred [] = refl
renameStoreNrw-raise0-pred ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong (λ c → raise0ᵗ X ꞉ c) (renameᶜ-raise0-pred p))
    (renameStoreNrw-raise0-pred σ)
renameStoreNrw-raise0-pred ((X ꞉= A ⊒) ∷ σ) =
  cong₂ _∷_
    (cong (λ B → raise0ᵗ X ꞉= B ⊒) (renameᵗ-raise0-pred A))
    (renameStoreNrw-raise0-pred σ)
renameStoreNrw-raise0-pred ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_ refl (renameStoreNrw-raise0-pred σ)

renameCtxNrw-raise0-pred :
  ∀ γ →
  renameCtxNrw raise0ᵗ γ ≡ ⇑ᵍ (renameCtxNrw predᵗ γ)
renameCtxNrw-raise0-pred [] = refl
renameCtxNrw-raise0-pred (p ∷ γ) =
  cong₂ _∷_ (renameᶜ-raise0-pred p) (renameCtxNrw-raise0-pred γ)
runtime-⇑ᵗᵐ :
  ∀ {M} →
  RuntimeOK M →
  RuntimeOK (⇑ᵗᵐ M)
runtime-⇑ᵗᵐ (ok-no noM) =
  ok-no (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-• vV noV) =
  ok-• (renameᵗᵐ-preserves-Value suc vV)
       (renameᵗᵐ-preserves-No• suc noV)
runtime-⇑ᵗᵐ (ok-·₁ okL noM) =
  ok-·₁ (runtime-⇑ᵗᵐ okL) (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-·₂ vV noV okM) =
  ok-·₂ (renameᵗᵐ-preserves-Value suc vV)
        (renameᵗᵐ-preserves-No• suc noV)
        (runtime-⇑ᵗᵐ okM)
runtime-⇑ᵗᵐ (ok-ν okL) = ok-ν (runtime-⇑ᵗᵐ okL)
runtime-⇑ᵗᵐ (ok-⊕₁ okL noM) =
  ok-⊕₁ (runtime-⇑ᵗᵐ okL) (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-⊕₂ vL noL okM) =
  ok-⊕₂ (renameᵗᵐ-preserves-Value suc vL)
        (renameᵗᵐ-preserves-No• suc noL)
        (runtime-⇑ᵗᵐ okM)
runtime-⇑ᵗᵐ (ok-⟨⟩ okM) = ok-⟨⟩ (runtime-⇑ᵗᵐ okM)

shifted-runtime-type-app-source-no-value-target :
  ∀ {Δ σ γ N V p} →
  RuntimeTypeApp N →
  Value V →
  Δ ∣ σ ∣ γ ⊢ ⇑ᵗᵐ N ⊒ V ∶ p →
  ⊥
shifted-runtime-type-app-source-no-value-target app vV N⊒V =
  runtime-type-app-source-no-value-target
    (renameᵗᵐ-preserves-RuntimeTypeApp suc app)
    vV
    N⊒V

postulate
  -- `split` changes which fresh type variable the source term is opened at.
  -- This should follow from `RuntimeOK` depending on the term/bullet shape
  -- rather than the particular type-variable names in casts and annotations.
  runtime-open-change :
    ∀ {N α β} →
    RuntimeOK (N [ α ]ᵀ) →
    RuntimeOK (N [ β ]ᵀ)

------------------------------------------------------------------------
-- Catchup
------------------------------------------------------------------------

-- Postulate audit:
-- * `left-widening-lemma` and `left-narrowing-lemma` correspond to named
--   cambridge25 lemmas.  The Agda statements add the emitted-store bookkeeping
--   (`χs`, `π`, and `combineStoreNrw`) needed by this mechanization.
-- * The other postulates in this file are not pre-existing named cambridge25
--   lemmas.  They are newly documented proof obligations/cases in
--   `cambridge25.lagda.md`, marked with `[New]`, and remain to be proved.

postulate
  -- cambridge25 "Left Widening Lemma": the source before the left cast is
  -- already a value.  The catchup induction that produces that value remains
  -- in `catchup-lemma`.  The Δ′ equality is Agda bookkeeping for the emitted
  -- store-change sequence.
  left-widening-lemma :
    ∀ {Δ σ V V′ p r t A B C D} →
    Value V →
    No• V →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
      No• W ×
      (V ⟨ - t ⟩ —↠[ χs ] W) ×
      (Δ′ ≡ applyTyCtxs χs Δ) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r

  -- cambridge25 "Left Narrowing Lemma", likewise value-level, with the same
  -- emitted-context bookkeeping.
  left-narrowing-lemma :
    ∀ {Δ σ V V′ p r t A B C D} →
    Value V →
    No• V →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ r →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
      No• W ×
      (V ⟨ t ⟩ —↠[ χs ] W) ×
      (Δ′ ≡ applyTyCtxs χs Δ) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p

  -- [New] Shifted-source catchup inversion for the `⊒Λ` case.
  --
  -- Counterexample note.  `proof.TraceProbe` instantiates this standalone
  -- statement and derives `⊥`, so the statement below is too broad as
  -- written.
  -- The actual `catchup-lemma` branch still has the original inner `⊒Λ`
  -- premise; a sound replacement should keep that premise or prove the branch
  -- directly from it.
  --
  -- Attempted proof notes.  A direct recursive call in the `⊒Λ` case catches
  -- up the shifted source `⇑ᵗᵐ N` under `(zero ꞉= ★ ⊒) ∷ ⇑ˢ σ`,
  -- but the final catchup conclusion needs an unshifted reduction from `N`
  -- under `σ`.  The useful next invariant is a reduction/store-prefix
  -- inversion lemma: peel the fresh source-only star entry from the emitted
  -- store changes, invert type-renamed source reductions, and rewrite target
  -- terms/coercions with the under-binder `applyTerms`/`applyCoercions`
  -- lemmas before rebuilding `⊒Λ`.
  shifted-source-catchup-Λ-inversion :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V′ p} →
    Value W →
    (⇑ᵗᵐ N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (N —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      suc Δ″ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ) ∣ []
        ⊢ ⇑ᵗᵐ W′ ⊒ applyTermsUnderTyBinders χs′ V′
          ∶ applyCoercionUnderTyBinders χs′ p

  -- [New] Same shifted-source catchup inversion for the `⊒⟨ν⟩` wrapper,
  -- where the target value remains outside the generated cast in the final
  -- result.
  -- The proof should share the same inversion lemma as `⊒Λ`; only the final
  -- rebuild differs, using `⊒⟨ν⟩` and inertness preservation for the
  -- under-binder coercion action.
  shifted-source-catchup-⟨ν⟩-inversion :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V′ p s} →
    Value W →
    (⇑ᵗᵐ N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (V′ ⟨ s ⟩) ∶ applyCoercions χs p →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (N —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      suc Δ″ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ) ∣ []
        ⊢ ⇑ᵗᵐ W′
          ⊒ applyTerms χs′ V′ ⟨ applyCoercionUnderTyBinders χs′ s ⟩
          ∶ applyCoercionUnderTyBinders χs′ p

-- A mode-polymorphic version of this transport was tried first, but the final
-- catchup proof only needs coercions in `tag-or-idᵈ`; keeping the generic mode
-- action obscured the actual side condition.
gen-tag-or-id≤tag-or-id :
  ModeIncl (genᵈ tag-or-idᵈ) tag-or-idᵈ
gen-tag-or-id≤tag-or-id zero = refl
gen-tag-or-id≤tag-or-id (suc X) = refl

applyCoercion-narrow :
  ∀ χ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B →
  applyTyCtx χ Δ ∣ applyStore χ Σ
    ⊢ applyCoercion χ c ∶ᶜ applyTy χ A ⊒ applyTy χ B
applyCoercion-narrow keep c⊒ = c⊒
applyCoercion-narrow (bind Aν) c⊒ =
  narrow-mode-relax gen-tag-or-id≤tag-or-id
    (narrow-weaken ≤-refl StoreIncl-drop (narrow-⇑ᵗ-gen c⊒))

applyCoercions-narrow :
  ∀ χs {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B →
  applyTyCtxs χs Δ ∣ applyStores χs Σ
    ⊢ applyCoercions χs c ∶ᶜ applyTys χs A ⊒ applyTys χs B
applyCoercions-narrow [] c⊒ = c⊒
applyCoercions-narrow (χ ∷ χs) c⊒ =
  applyCoercions-narrow χs (applyCoercion-narrow χ c⊒)

catchup-coercion-typing-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
    ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ applyTys χs B
catchup-coercion-typing-transport {Δ = Δ} {σ = σ} {π = π}
    {χs = χs} {p = p} {A = A} {B = B} pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  subst
    (λ Δ₀ → Δ₀ ∣ srcStoreⁿ (combineStoreNrw π σ)
      ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ applyTys χs B)
    (sym Δ′≡)
    (subst
      (λ Σ → applyTyCtxs χs Δ ∣ Σ
        ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ applyTys χs B)
      (sym
        (combineStoreNrw-applyStores-store
          {χs = χs} π⊒ Π≡ Π′≡ σ))
      (applyCoercions-narrow χs pᶜ))

catchup-gen-coercion-typing-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
    ⊢ gen (applyTys χs A) (applyCoercionUnderTyBinders χs p)
      ∶ᶜ applyTys χs A ⊒ `∀ (applyTysUnderTyBinders χs B)
catchup-gen-coercion-typing-transport {Δ′ = Δ′} {σ = σ} {π = π}
    {χs = χs} {p = p} {A = A} {B = B} pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  subst
    (λ B₀ → Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
      ⊢ gen (applyTys χs A) (applyCoercionUnderTyBinders χs p)
        ∶ᶜ applyTys χs A ⊒ B₀)
    (applyTys-∀ χs B)
    (subst
      (λ p₀ → Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
        ⊢ p₀ ∶ᶜ applyTys χs A ⊒ applyTys χs (`∀ B))
      (applyCoercions-gen χs A p)
      (catchup-coercion-typing-transport
        {σ = σ} {π = π} {χs = χs} {p = gen A p}
        {A = A} {B = `∀ B}
        pᶜ Δ′≡ Π≡ Π′≡ π⊒))

gen-body-coercionᶜ :
  ∀ {Δ Σ A B p} →
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  genᵈ tag-or-idᵈ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ p ∶ ⇑ᵗ A ⊒ B
gen-body-coercionᶜ (cast-gen hA occ body⊢ , gen bodyⁿ) =
  body⊢ , bodyⁿ

gen-target-occursᶜ :
  ∀ {Δ Σ A B p} →
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  occurs zero B ≡ true
gen-target-occursᶜ (cast-gen hA occ body⊢ , gen bodyⁿ) = occ

gen-shifted-body-source-one-fresh :
  ∀ {Δ Σ A B p} →
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  occurs (suc zero) (src (⇑ᶜ p)) ≡ false
gen-shifted-body-source-one-fresh {A = A} {p = p} pᶜ =
  trans
    (cong (occurs (suc zero)) (src-renameᶜ suc p))
    (trans
      (cong (λ T → occurs (suc zero) (⇑ᵗ T)) src-p)
      (occurs-one-⇑⇑-false A))
  where
    src-p :
      src p ≡ ⇑ᵗ A
    src-p =
      proj₁ (coercion-src-tgtᵐ (proj₁ (gen-body-coercionᶜ pᶜ)))

compose-right-gen-shift-left-source-fresh :
  ∀ {Δ₀ Δ Σ σ A B p r t q C D} →
  Δ₀ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ q ∶ C ⊒ D →
  r ≡ ⇑ᶜ p →
  occurs (suc zero) (src t) ≡ false
compose-right-gen-shift-left-source-fresh pᶜ
    (compose-rightⁿ wfΣ t⊒ q⊒
      (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒))
    r≡⇑p =
  trans
    (cong (occurs (suc zero))
      (proj₁ (coercion-src-tgtᵐ (proj₁ t⊒))))
    (trans
      (cong (occurs (suc zero)) (sym src-r))
      (trans
        (cong (occurs (suc zero)) (cong src r≡⇑p))
        (gen-shifted-body-source-one-fresh pᶜ)))

gen-source-all-overlap⊥ :
  ∀ {Δ Σ A B p s} →
  StoreDetWf Δ Σ →
  Δ ∣ Σ ⊢ gen (`∀ A) p ∶ᶜ `∀ A ⊒ `∀ B →
  extᵈ tag-or-idᵈ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B →
  ⊥
gen-source-all-overlap⊥ wfΣ pᶜ s⊒ =
  narrowing-all-gen-overlap⊥
    wfΣ (gen-target-occursᶜ pᶜ) s⊒ (gen-body-coercionᶜ pᶜ)

gen-body-coercionᶜ-tag :
  ∀ {Δ Σ A B p} →
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ p ∶ᶜ ⇑ᵗ A ⊒ B
gen-body-coercionᶜ-tag pᶜ =
  narrow-mode-relax gen-tag-or-id≤tag-or-id
    (gen-body-coercionᶜ pᶜ)

gen-body-target-first-coercionᶜ :
  ∀ {Δ σ A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc (suc Δ) ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ renameᶜ (extᵗ suc) p
      ∶ᶜ renameᵗ swap01ᵗ (⇑ᵗ (⇑ᵗ A)) ⊒ renameᵗ swap01ᵗ (⇑ᵗ B)
gen-body-target-first-coercionᶜ
    {Δ = Δ} {σ = σ} {A = A} {B = B} {p = p} pᶜ =
  subst
    (λ c → suc (suc Δ) ∣
      srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
      ⊢ c ∶ᶜ
        renameᵗ swap01ᵗ (⇑ᵗ (⇑ᵗ A)) ⊒ renameᵗ swap01ᵗ (⇑ᵗ B))
    (renameᶜ-swap01-⇑ p)
    (source-target-bubble-empty-coercionᶜ {σ = σ} sourceFirst)
  where
    base :
      suc Δ ∣ srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)
        ⊢ p ∶ᶜ ⇑ᵗ A ⊒ B
    base =
      subst
        (λ Σ → suc Δ ∣ Σ ⊢ p ∶ᶜ ⇑ᵗ A ⊒ B)
        (sym (srcStoreⁿ-⇑ˢ σ))
        (gen-body-coercionᶜ-tag pᶜ)

    shifted :
      suc (suc Δ) ∣ srcStoreⁿ (⇑ˢ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))
        ⊢ ⇑ᶜ p ∶ᶜ ⇑ᵗ (⇑ᵗ A) ⊒ ⇑ᵗ B
    shifted =
      narrow-⇑ᵗ-ᶜ-srcStoreⁿ
        {σ = (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ}
        base

    sourceFirst :
      suc (suc Δ) ∣
        srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
        ⊢ ⇑ᶜ p ∶ᶜ ⇑ᵗ (⇑ᵗ A) ⊒ ⇑ᵗ B
    sourceFirst =
      narrow-weaken ≤-refl StoreIncl-drop shifted

catchup-gen-body-coercionᶜ :
  ∀ {Δ Δ′ σ π Π Π′ χs A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  genᵈ tag-or-idᵈ ∣ suc Δ′ ∣
    ⟰ᵗ (srcStoreⁿ (combineStoreNrw π σ))
    ⊢ applyCoercionUnderTyBinders χs p
      ∶ ⇑ᵗ (applyTys χs A) ⊒ applyTysUnderTyBinders χs B
catchup-gen-body-coercionᶜ {σ = σ} {π = π} {χs = χs}
    pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  gen-body-coercionᶜ
    (catchup-gen-coercion-typing-transport
      {σ = σ} {χs = χs} pᶜ Δ′≡ Π≡ Π′≡ π⊒)

catchup-gen-target-occursᶜ :
  ∀ {Δ Δ′ σ π Π Π′ χs A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  occurs zero (applyTysUnderTyBinders χs B) ≡ true
catchup-gen-target-occursᶜ {σ = σ} {π = π} {χs = χs}
    pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  gen-target-occursᶜ
    (catchup-gen-coercion-typing-transport
      {σ = σ} {χs = χs} pᶜ Δ′≡ Π≡ Π′≡ π⊒)

catchup-gen-body-coercionᶜ-tag :
  ∀ {Δ Δ′ σ π Π Π′ χs A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  suc Δ′ ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π σ))
    ⊢ applyCoercionUnderTyBinders χs p
      ∶ᶜ ⇑ᵗ (applyTys χs A) ⊒ applyTysUnderTyBinders χs B
catchup-gen-body-coercionᶜ-tag {σ = σ} {π = π} {χs = χs}
    pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  subst
    (λ Σ → _ ∣ Σ ⊢ _ ∶ᶜ _ ⊒ _)
    (sym (srcStoreⁿ-⇑ˢ (combineStoreNrw π σ)))
    (gen-body-coercionᶜ-tag
      (catchup-gen-coercion-typing-transport
        {σ = σ} {χs = χs} pᶜ Δ′≡ Π≡ Π′≡ π⊒))

catchup-gen-body-ordinary-coercionᶜ :
  ∀ {Δ Δ′ σ π Π Π′ χs A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ srcStoreⁿ
    (combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))
    ⊢ applyCoercions χs p ∶ᶜ
      applyTys χs (⇑ᵗ A) ⊒ applyTys χs B
catchup-gen-body-ordinary-coercionᶜ {σ = σ} {π = π} {χs = χs}
    pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  catchup-coercion-typing-transport
    {σ = (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ} {π = π} {χs = χs}
    (subst
      (λ Σ → _ ∣ Σ ⊢ _ ∶ᶜ _ ⊒ _)
      (sym (srcStoreⁿ-⇑ˢ σ))
      (gen-body-coercionᶜ-tag pᶜ))
    Δ′≡
    Π≡
    Π′≡
    π⊒

source-first-body-ν⊒ :
  ∀ {Δ Δ′ σ π Π Π′ χs A B p W V′} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  suc Δ′ ∣
    (⊒ zero ꞉=☆) ∷
      ⇑ˢ (combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V′) ∶ ⇑ᶜ (applyCoercions χs p) →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ ν ★ W (⇑ᶜ (applyCoercions χs p)) ⊒ applyTerms χs V′
      ∶ applyCoercions χs p
source-first-body-ν⊒ {χs = χs} pᶜ Δ′≡ Π≡ Π′≡ π⊒ body =
  ν⊒
    (catchup-gen-body-ordinary-coercionᶜ
      {χs = χs} pᶜ Δ′≡ Π≡ Π′≡ π⊒)
    body

last-bind-source-first-ν⊒ :
  ∀ {Δ Δ′ σ χs Aχ keeps π π₀ A B p W V′} →
  (keeps-ok : AllKeep keeps) →
  π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀ →
  Δ′ ≡ applyTyCtxs (χs ++ bind Aχ ∷ keeps) (suc Δ) →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ⊢ π₀ ꞉ applyStores χs [] ⊒ˢ [] →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms (χs ++ bind Aχ ∷ keeps) V′
      ∶ applyCoercions (χs ++ bind Aχ ∷ keeps) p →
  applyTyCtxs χs (suc Δ) ∣
    combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ ν ★ W (⇑ᶜ (applyCoercions χs p)) ⊒ applyTerms χs V′
      ∶ applyCoercions χs p
last-bind-source-first-ν⊒
    {Δ = Δ} {Δ′ = Δ′} {σ = σ} {χs = χs}
    {Aχ = Aχ} {keeps = keeps} {π₀ = π₀}
    {p = p} {W = W} {V′ = V′}
    keeps-ok π≡ Δ′≡ pᶜ π₀⊒ W⊒V′ =
  source-first-body-ν⊒
    {χs = χs}
    pᶜ
    refl
    refl
    refl
    (⊒ˢ-empty-anyᵗ (applyTyCtxs χs (suc Δ)) π₀⊒)
    body
  where
    Δ′≡tail :
      Δ′ ≡ suc (applyTyCtxs χs (suc Δ))
    Δ′≡tail =
      trans Δ′≡
        (applyTyCtxs-last-bind χs Aχ keeps keeps-ok (suc Δ))

    body :
      suc (applyTyCtxs χs (suc Δ)) ∣
        (⊒ zero ꞉=☆) ∷
          ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)) ∣ []
        ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V′) ∶ ⇑ᶜ (applyCoercions χs p)
    body =
      subst
        (λ Δ₀ → Δ₀ ∣
          (⊒ zero ꞉=☆) ∷
            ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)) ∣ []
          ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V′)
            ∶ ⇑ᶜ (applyCoercions χs p))
        Δ′≡tail
        (last-bind-source-first-body
          {σ = σ} {χs = χs} {A = Aχ} {keeps = keeps}
          {V = V′} {p = p} {π₀ = π₀}
          keeps-ok π≡ W⊒V′)

≈ⁿ-⇑ˢ :
  ∀ {Δ σ s t A B} →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ s ≈ ⇑ᶜ t ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
≈ⁿ-⇑ˢ (endpointsⁿ {s = s} {t = t}
    srcs tgts srct tgtt σ⊒ (hA , hB) (hA′ , hB′) s⊒ t⊒) =
  endpointsⁿ
    (trans (src-renameᶜ suc s) (cong ⇑ᵗ srcs))
    (trans (tgt-renameᶜ suc s) (cong ⇑ᵗ tgts))
    (trans (src-renameᶜ suc t) (cong ⇑ᵗ srct))
    (trans (tgt-renameᶜ suc t) (cong ⇑ᵗ tgtt))
    (⊒ˢ-⇑ˢ σ⊒)
    (WfTyˢ-⇑ᵗ hA , WfTyˢ-⇑ᵗ hB)
    (WfTyˢ-⇑ᵗ hA′ , WfTyˢ-⇑ᵗ hB′)
    (narrow-⇑ᵗ-any s⊒)
    (narrow-⇑ᵗ-any t⊒)

≈ⁿ-add-left-star-var :
  ∀ X {Δ σ s t A B} →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ (⊒ X ꞉=☆) ∷ σ ⊢ s ≈ t ∶ A ⊒ B
≈ⁿ-add-left-star-var X (endpointsⁿ {t = t}
    srcs tgts srct tgtt σ⊒ (hA , hB) (hA′ , hB′) s⊒ t⊒) =
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (⊒ˢ-left σ⊒)
    (hA , hB)
    ( WfTyˢ-store-weaken StoreIncl-drop hA′
    , WfTyˢ-store-weaken StoreIncl-drop hB′
    )
    s⊒
    (narrow-drop-star-var X t⊒)

compose-leftⁿ-⇑ˢ :
  ∀ {Δ σ q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ q ⨾ⁿ ⇑ᶜ s ≈ ⇑ᶜ r ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
compose-leftⁿ-⇑ˢ (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  let
    q⊒′ = narrow-⇑ᵗ-gen q⊒
    s⊒′ = narrow-⇑ᵗ-gen s⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒
    new = _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} q⊒′ s⊒′
    u≡ =
      narrowing-determinedᵐ (StoreDetWf-⟰ᵗ wfΣ)
        (proj₂ new)
        (narrow-⇑ᵗ-gen (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ u ≈ ⇑ᶜ _ ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-⇑ˢ q⨟s≈r)
  in
  compose-leftⁿ (StoreDetWf-⟰ᵗ wfΣ) q⊒′ s⊒′ eq′

compose-leftⁿ-add-left-star-var :
  ∀ X {Δ σ q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ (⊒ X ꞉=☆) ∷ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
compose-leftⁿ-add-left-star-var X (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒ (≈ⁿ-add-left-star-var X q⨟s≈r)

compose-rightⁿ-⇑ˢ :
  ∀ {Δ σ r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ r ≈ ⇑ᶜ t ⨾ⁿ ⇑ᶜ p ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
compose-rightⁿ-⇑ˢ (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  let
    t⊒′ = narrow-⇑ᵗ-gen t⊒
    p⊒′ = narrow-⇑ᵗ-gen p⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒
    new = _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} t⊒′ p⊒′
    u≡ =
      narrowing-determinedᵐ (StoreDetWf-⟰ᵗ wfΣ)
        (proj₂ new)
        (narrow-⇑ᵗ-gen (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ ⇑ᶜ _ ≈ u ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-⇑ˢ r≈t⨟p)
  in
  compose-rightⁿ (StoreDetWf-⟰ᵗ wfΣ) t⊒′ p⊒′ eq′

compose-rightⁿ-add-left-star-var :
  ∀ X {Δ σ r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ (⊒ X ꞉=☆) ∷ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
compose-rightⁿ-add-left-star-var X (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒ (≈ⁿ-add-left-star-var X r≈t⨟p)

compose-leftⁿ-rename-swap01ᵗ-components :
  ∀ {Δ σ Σ μ q s r A B C} →
  (wfΣ : StoreDetWf (suc (suc Δ)) Σ) →
  (wfΣ′ : StoreDetWf (suc (suc Δ)) (renameStoreᵗ swap01ᵗ Σ)) →
  (q⊒ : μ ∣ suc (suc Δ) ∣ Σ ⊢ q ∶ A ⊒ C) →
  (s⊒ : μ ∣ suc (suc Δ) ∣ Σ ⊢ s ∶ C ⊒ B) →
  suc (suc Δ) ∣ σ ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B →
  suc (suc Δ) ∣ renameStoreNrw swap01ᵗ σ
    ⊢ renameᶜ swap01ᵗ q ⨾ⁿ renameᶜ swap01ᵗ s
      ≈ renameᶜ swap01ᵗ r ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
compose-leftⁿ-rename-swap01ᵗ-components
    {μ = μ} wfΣ wfΣ′ q⊒ s⊒ q⨟s≈r =
  compose-leftⁿ wfΣ′ q⊒′ s⊒′ eq′
  where
    rel = modeRename-swap01ᵗMode μ

    q⊒′ =
      narrow-renameᵗ {ν = swap01ᵗMode μ} TyRenameWf-swap01 rel q⊒

    s⊒′ =
      narrow-renameᵗ {ν = swap01ᵗMode μ} TyRenameWf-swap01 rel s⊒

    u≡ =
      ⨟ⁿ-renameᵗ-determined
        {ν = swap01ᵗMode μ}
        TyRenameWf-swap01 rel wfΣ wfΣ′ q⊒ s⊒

    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ u ≈ renameᶜ swap01ᵗ _ ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-rename-swap01ᵗ q⨟s≈r)

compose-rightⁿ-rename-swap01ᵗ-components :
  ∀ {Δ σ Σ μ r t p A B C} →
  (wfΣ : StoreDetWf (suc (suc Δ)) Σ) →
  (wfΣ′ : StoreDetWf (suc (suc Δ)) (renameStoreᵗ swap01ᵗ Σ)) →
  (t⊒ : μ ∣ suc (suc Δ) ∣ Σ ⊢ t ∶ A ⊒ C) →
  (p⊒ : μ ∣ suc (suc Δ) ∣ Σ ⊢ p ∶ C ⊒ B) →
  suc (suc Δ) ∣ σ ⊢
    r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B →
  suc (suc Δ) ∣ renameStoreNrw swap01ᵗ σ
    ⊢ renameᶜ swap01ᵗ r
      ≈ renameᶜ swap01ᵗ t ⨾ⁿ renameᶜ swap01ᵗ p
        ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
compose-rightⁿ-rename-swap01ᵗ-components
    {μ = μ} wfΣ wfΣ′ t⊒ p⊒ r≈t⨟p =
  compose-rightⁿ wfΣ′ t⊒′ p⊒′ eq′
  where
    rel = modeRename-swap01ᵗMode μ

    t⊒′ =
      narrow-renameᵗ {ν = swap01ᵗMode μ} TyRenameWf-swap01 rel t⊒

    p⊒′ =
      narrow-renameᵗ {ν = swap01ᵗMode μ} TyRenameWf-swap01 rel p⊒

    u≡ =
      ⨟ⁿ-renameᵗ-determined
        {ν = swap01ᵗMode μ}
        TyRenameWf-swap01 rel wfΣ wfΣ′ t⊒ p⊒

    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ renameᶜ swap01ᵗ _ ≈ u ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-rename-swap01ᵗ r≈t⨟p)

compose-leftⁿ-rename-swap01ᵗ :
  ∀ {Δ σ q s r A B} →
  (∀ {Σ} →
    StoreDetWf (suc (suc Δ)) Σ →
    StoreDetWf (suc (suc Δ)) (renameStoreᵗ swap01ᵗ Σ)) →
  suc (suc Δ) ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  suc (suc Δ) ∣ renameStoreNrw swap01ᵗ σ
    ⊢ renameᶜ swap01ᵗ q ⨾ⁿ renameᶜ swap01ᵗ s
      ≈ renameᶜ swap01ᵗ r ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
compose-leftⁿ-rename-swap01ᵗ detMap
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ-rename-swap01ᵗ-components
    wfΣ (detMap wfΣ) q⊒ s⊒ q⨟s≈r

compose-rightⁿ-rename-swap01ᵗ :
  ∀ {Δ σ r t p A B} →
  (∀ {Σ} →
    StoreDetWf (suc (suc Δ)) Σ →
    StoreDetWf (suc (suc Δ)) (renameStoreᵗ swap01ᵗ Σ)) →
  suc (suc Δ) ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  suc (suc Δ) ∣ renameStoreNrw swap01ᵗ σ
    ⊢ renameᶜ swap01ᵗ r
      ≈ renameᶜ swap01ᵗ t ⨾ⁿ renameᶜ swap01ᵗ p
        ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B
compose-rightⁿ-rename-swap01ᵗ detMap
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ-rename-swap01ᵗ-components
    wfΣ (detMap wfΣ) t⊒ p⊒ r≈t⨟p

catchup-compose-left-transport-shifted :
  ∀ n {Δ Δ′ σ π Π Π′ χs q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
      ≈ applyCoercions χs r ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-left-transport-shifted n {Δ = Δ} {Δ′ = Δ′} {σ = σ}
    {χs = χs} {q = q} {s = s} {r = r} {A = A} {B = B}
    q⨟s≈r Δ′≡ Π≡ Π′≡ ⊒ˢ-nil =
  let
    empty≡ = shiftStore-empty-inv n (sym Π≡)
    Δ′≡Δ = trans Δ′≡ (applyTyCtxs-empty-id χs empty≡ Δ)
    q≡ = applyCoercions-empty-id χs empty≡ q
    s≡ = applyCoercions-empty-id χs empty≡ s
    r≡ = applyCoercions-empty-id χs empty≡ r
    A≡ = applyTys-empty-id χs empty≡ A
    B≡ = applyTys-empty-id χs empty≡ B
  in
  subst
    (λ Δ₀ → Δ₀ ∣ σ
      ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
        ≈ applyCoercions χs r ∶ applyTys χs A ⊒ applyTys χs B)
    (sym Δ′≡Δ)
    (subst
      (λ B₀ → Δ ∣ σ
        ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
          ≈ applyCoercions χs r ∶ applyTys χs A ⊒ B₀)
      (sym B≡)
      (subst
        (λ A₀ → Δ ∣ σ
          ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
            ≈ applyCoercions χs r ∶ A₀ ⊒ B)
        (sym A≡)
        (subst
          (λ r₀ → Δ ∣ σ
            ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
              ≈ r₀ ∶ A ⊒ B)
          (sym r≡)
          (subst
            (λ s₀ → Δ ∣ σ
              ⊢ applyCoercions χs q ⨾ⁿ s₀ ≈ r ∶ A ⊒ B)
            (sym s≡)
            (subst
              (λ q₀ → Δ ∣ σ ⊢ q₀ ⨾ⁿ s ≈ r ∶ A ⊒ B)
              (sym q≡)
              q⨟s≈r)))))
catchup-compose-left-transport-shifted n
    q⨟s≈r Δ′≡ Π≡ () (⊒ˢ-right hA π⊒)
catchup-compose-left-transport-shifted n {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    with storeChangesLastBind χs
catchup-compose-left-transport-shifted n {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
catchup-compose-left-transport-shifted n {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps | ()
catchup-compose-left-transport-shifted n {Δ = Δ} {σ = σ}
    {χs = .(χs ++ bind Aχ ∷ keeps)}
    {q = q} {s = s} {r = r} {A = A} {B = B}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left {X = X} π⊒)
    | last-bind χs Aχ keeps keeps-ok =
  let
    Δtail≡ =
      trans Δ′≡
        (trans (applyTyCtxs-last-bind χs Aχ keeps keeps-ok Δ)
          (sym (applyTyCtxs-suc χs Δ)))
    Π-last≡ =
      trans Π≡
        (cong (shiftStore n)
          (applyStores-last-bind χs Aχ keeps keeps-ok []))
    Π-last-normal≡ =
      trans Π-last≡
        (shiftStore-cons n zero (⇑ᵗ Aχ) (⟰ᵗ (applyStores χs [])))
    Πtail≡ =
      trans (storeTail-∷≡ Π-last-normal≡)
        (shiftStore-⟰ᵗ n (applyStores χs []))
    tail =
      catchup-compose-left-transport-shifted (suc n) {χs = χs}
        (compose-leftⁿ-⇑ˢ q⨟s≈r)
        Δtail≡
        Πtail≡
        Π′≡
        π⊒
    lifted = compose-leftⁿ-add-left-star-var X tail
    q≡ =
      trans (applyCoercions-⇑ᶜ χs q)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok q))
    s≡ =
      trans (applyCoercions-⇑ᶜ χs s)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok s))
    r≡ =
      trans (applyCoercions-⇑ᶜ χs r)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok r))
    A≡ =
      trans (applyTys-⇑ᵗ χs A)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok A))
    B≡ =
      trans (applyTys-⇑ᵗ χs B)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok B))
  in
  subst
    (λ B₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
      ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) s
      ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) r
      ∶ applyTys (χs ++ bind Aχ ∷ keeps) A ⊒ B₀)
    B≡
    (subst
      (λ A₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
        ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) s
        ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) r
        ∶ A₀ ⊒ applyTys χs (⇑ᵗ B))
      A≡
      (subst
        (λ r₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
          ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) s
          ≈ r₀ ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
        r≡
        (subst
          (λ s₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
            ⨾ⁿ s₀ ≈ applyCoercions χs (⇑ᶜ r)
            ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
          s≡
          (subst
            (λ q₀ → _ ∣ _ ⊢ q₀
              ⨾ⁿ applyCoercions χs (⇑ᶜ s)
              ≈ applyCoercions χs (⇑ᶜ r)
              ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
            q≡
            lifted))))
catchup-compose-left-transport-shifted n
    q⨟s≈r Δ′≡ Π≡ () (⊒ˢ-both hA hA′ s⊒ π⊒)

catchup-compose-left-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
      ≈ applyCoercions χs r ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-left-transport {χs = χs} q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒ =
  catchup-compose-left-transport-shifted zero
    {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒

catchup-compose-right-transport-shifted :
  ∀ n {Δ Δ′ σ π Π Π′ χs r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs r
      ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
      ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-right-transport-shifted n {Δ = Δ} {Δ′ = Δ′} {σ = σ}
    {χs = χs} {r = r} {t = t} {p = p} {A = A} {B = B}
    r≈t⨟p Δ′≡ Π≡ Π′≡ ⊒ˢ-nil =
  let
    empty≡ = shiftStore-empty-inv n (sym Π≡)
    Δ′≡Δ = trans Δ′≡ (applyTyCtxs-empty-id χs empty≡ Δ)
    r≡ = applyCoercions-empty-id χs empty≡ r
    t≡ = applyCoercions-empty-id χs empty≡ t
    p≡ = applyCoercions-empty-id χs empty≡ p
    A≡ = applyTys-empty-id χs empty≡ A
    B≡ = applyTys-empty-id χs empty≡ B
  in
  subst
    (λ Δ₀ → Δ₀ ∣ σ
      ⊢ applyCoercions χs r
        ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
        ∶ applyTys χs A ⊒ applyTys χs B)
    (sym Δ′≡Δ)
    (subst
      (λ B₀ → Δ ∣ σ
        ⊢ applyCoercions χs r
          ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
          ∶ applyTys χs A ⊒ B₀)
      (sym B≡)
      (subst
        (λ A₀ → Δ ∣ σ
          ⊢ applyCoercions χs r
            ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
            ∶ A₀ ⊒ B)
        (sym A≡)
        (subst
          (λ p₀ → Δ ∣ σ
            ⊢ applyCoercions χs r
              ≈ applyCoercions χs t ⨾ⁿ p₀ ∶ A ⊒ B)
          (sym p≡)
          (subst
            (λ t₀ → Δ ∣ σ
              ⊢ applyCoercions χs r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
            (sym t≡)
            (subst
              (λ r₀ → Δ ∣ σ ⊢ r₀ ≈ t ⨾ⁿ p ∶ A ⊒ B)
              (sym r≡)
              r≈t⨟p)))))
catchup-compose-right-transport-shifted n
    r≈t⨟p Δ′≡ Π≡ () (⊒ˢ-right hA π⊒)
catchup-compose-right-transport-shifted n {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    with storeChangesLastBind χs
catchup-compose-right-transport-shifted n {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
catchup-compose-right-transport-shifted n {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps | ()
catchup-compose-right-transport-shifted n {Δ = Δ} {σ = σ}
    {χs = .(χs ++ bind Aχ ∷ keeps)}
    {r = r} {t = t} {p = p} {A = A} {B = B}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left {X = X} π⊒)
    | last-bind χs Aχ keeps keeps-ok =
  let
    Δtail≡ =
      trans Δ′≡
        (trans (applyTyCtxs-last-bind χs Aχ keeps keeps-ok Δ)
          (sym (applyTyCtxs-suc χs Δ)))
    Π-last≡ =
      trans Π≡
        (cong (shiftStore n)
          (applyStores-last-bind χs Aχ keeps keeps-ok []))
    Π-last-normal≡ =
      trans Π-last≡
        (shiftStore-cons n zero (⇑ᵗ Aχ) (⟰ᵗ (applyStores χs [])))
    Πtail≡ =
      trans (storeTail-∷≡ Π-last-normal≡)
        (shiftStore-⟰ᵗ n (applyStores χs []))
    tail =
      catchup-compose-right-transport-shifted (suc n) {χs = χs}
        (compose-rightⁿ-⇑ˢ r≈t⨟p)
        Δtail≡
        Πtail≡
        Π′≡
        π⊒
    lifted = compose-rightⁿ-add-left-star-var X tail
    r≡ =
      trans (applyCoercions-⇑ᶜ χs r)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok r))
    t≡ =
      trans (applyCoercions-⇑ᶜ χs t)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok t))
    p≡ =
      trans (applyCoercions-⇑ᶜ χs p)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok p))
    A≡ =
      trans (applyTys-⇑ᵗ χs A)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok A))
    B≡ =
      trans (applyTys-⇑ᵗ χs B)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok B))
  in
  subst
    (λ B₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
      ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) t
        ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) p
      ∶ applyTys (χs ++ bind Aχ ∷ keeps) A ⊒ B₀)
    B≡
    (subst
      (λ A₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
        ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) t
          ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) p
        ∶ A₀ ⊒ applyTys χs (⇑ᵗ B))
      A≡
      (subst
        (λ p₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
          ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) t
            ⨾ⁿ p₀ ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
        p≡
        (subst
          (λ t₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
            ≈ t₀ ⨾ⁿ applyCoercions χs (⇑ᶜ p)
            ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
          t≡
          (subst
            (λ r₀ → _ ∣ _ ⊢ r₀
              ≈ applyCoercions χs (⇑ᶜ t)
                ⨾ⁿ applyCoercions χs (⇑ᶜ p)
              ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
            r≡
            lifted))))
catchup-compose-right-transport-shifted n
    r≈t⨟p Δ′≡ Π≡ () (⊒ˢ-both hA hA′ s⊒ π⊒)

catchup-compose-right-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs r
      ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
      ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-right-transport {χs = χs} r≈t⨟p Δ′≡ Π≡ Π′≡ π⊒ =
  catchup-compose-right-transport-shifted zero
    {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ π⊒

data ExtendReplaceRel : TyCtx → StoreNrw → StoreNrw → Set where
  replace-here :
    ∀ {Δ α q A B σ} →
    Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
    ExtendReplaceRel Δ ((α ꞉= A ⊒) ∷ σ) ((α ꞉ q) ∷ σ)

  replace-right :
    ∀ {Δ X A σ σ′} →
    ExtendReplaceRel Δ σ σ′ →
    ExtendReplaceRel Δ ((X ꞉= A ⊒) ∷ σ) ((X ꞉= A ⊒) ∷ σ′)

  replace-left :
    ∀ {Δ X σ σ′} →
    ExtendReplaceRel Δ σ σ′ →
    ExtendReplaceRel Δ ((⊒ X ꞉=☆) ∷ σ) ((⊒ X ꞉=☆) ∷ σ′)

  replace-both :
    ∀ {Δ X q σ σ′} →
    ExtendReplaceRel Δ σ σ′ →
    ExtendReplaceRel Δ ((X ꞉ q) ∷ σ) ((X ꞉ q) ∷ σ′)

extendReplaceRel-⇑ˢ :
  ∀ {Δ σ σ′} →
  ExtendReplaceRel Δ σ σ′ →
  ExtendReplaceRel (suc Δ) (⇑ˢ σ) (⇑ˢ σ′)
extendReplaceRel-⇑ˢ (replace-here {σ = σ} qᶜ) =
  replace-here (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
extendReplaceRel-⇑ˢ (replace-right rel) =
  replace-right (extendReplaceRel-⇑ˢ rel)
extendReplaceRel-⇑ˢ (replace-left rel) =
  replace-left (extendReplaceRel-⇑ˢ rel)
extendReplaceRel-⇑ˢ (replace-both rel) =
  replace-both (extendReplaceRel-⇑ˢ rel)

extendReplaceRel-src-incl :
  ∀ {Δ σ σ′} →
  ExtendReplaceRel Δ σ σ′ →
  StoreIncl (srcStoreⁿ σ) (srcStoreⁿ σ′)
extendReplaceRel-src-incl (replace-here qᶜ) = StoreIncl-drop
extendReplaceRel-src-incl (replace-right rel) =
  extendReplaceRel-src-incl rel
extendReplaceRel-src-incl (replace-left rel) =
  StoreIncl-cons (extendReplaceRel-src-incl rel)
extendReplaceRel-src-incl (replace-both rel) =
  StoreIncl-cons (extendReplaceRel-src-incl rel)

storeIncl-substˡ :
  ∀ {Σ Σ₀ Σ′} →
  Σ ≡ Σ₀ →
  StoreIncl Σ₀ Σ′ →
  StoreIncl Σ Σ′
storeIncl-substˡ refl incl = incl

narrow-weaken-store :
  ∀ {Δ Σ Σ′ c A B} →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Δ ∣ Σ′ ⊢ c ∶ A ⊒ B
narrow-weaken-store incl (μ , c⊒) = μ , narrow-weaken ≤-refl incl c⊒

open-shiftᵐ :
  ∀ α M →
  (⇑ᵗᵐ M) [ α ]ᵀ ≡ M
open-shiftᵐ α M = renameᵗᵐ-left-inverse (λ X → refl) M

open-shiftᶜ :
  ∀ α c →
  (⇑ᶜ c) [ α ]ᶜ ≡ c
open-shiftᶜ α c = renameᶜ-left-inverse (λ X → refl) c

id★-coercionᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id ★ ∶ᶜ ★ ⊒ ★
id★-coercionᶜ = cast-id wf★ refl , id★

merge01-split-rebuild :
  ∀ {Δ σ W V′ p C D} →
  suc (suc Δ) ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ renameᶜ (extᵗ suc) p ∶ᶜ C ⊒ D →
  suc (suc Δ) ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ renameᵗᵐ merge01ᵗ W
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p →
  suc (suc Δ) ∣
    (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ renameᵗᵐ raise0ᵗ W
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p
merge01-split-rebuild
    {Δ = Δ} {σ = σ} {W = W} {V′ = V′} {p = p} {C = C} {D = D}
    pᶜ body =
  subst
    (λ c → _ ∣ splitStore ∣ []
      ⊢ renameᵗᵐ raise0ᵗ W
        ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ c)
    (open-shiftᶜ zero (renameᶜ (extᵗ suc) p))
    (subst
      (λ T → _ ∣ splitStore ∣ []
        ⊢ renameᵗᵐ raise0ᵗ W ⊒ T
          ∶ (⇑ᶜ (renameᶜ (extᵗ suc) p)) [ zero ]ᶜ)
      (open-shiftᵐ zero (renameᵗᵐ (extᵗ suc) V′))
      (subst
        (λ S → _ ∣ splitStore ∣ []
          ⊢ S ⊒ (⇑ᵗᵐ (renameᵗᵐ (extᵗ suc) V′)) [ zero ]ᵀ
            ∶ (⇑ᶜ (renameᶜ (extᵗ suc) p)) [ zero ]ᶜ)
        (renameᵗᵐ-close01-open1 W)
        raw))
  where
    splitStore =
      (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)

    premise :
      suc (suc Δ) ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
        ⊢ (renameᵗᵐ close01ᵗ W) [ zero ]ᵀ
          ⊒ (⇑ᵗᵐ (renameᵗᵐ (extᵗ suc) V′)) [ zero ]ᵀ
          ∶ (⇑ᶜ (renameᶜ (extᵗ suc) p)) [ zero ]ᶜ
    premise =
      subst
        (λ c → _ ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
          ⊢ (renameᵗᵐ close01ᵗ W) [ zero ]ᵀ
            ⊒ (⇑ᵗᵐ (renameᵗᵐ (extᵗ suc) V′)) [ zero ]ᵀ ∶ c)
        (sym (open-shiftᶜ zero (renameᶜ (extᵗ suc) p)))
        (subst
          (λ T → _ ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
            ⊢ (renameᵗᵐ close01ᵗ W) [ zero ]ᵀ ⊒ T
              ∶ renameᶜ (extᵗ suc) p)
          (sym (open-shiftᵐ zero (renameᵗᵐ (extᵗ suc) V′)))
          (subst
            (λ S → _ ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
              ⊢ S ⊒ renameᵗᵐ (extᵗ suc) V′
                ∶ renameᶜ (extᵗ suc) p)
            (sym (renameᵗᵐ-close01-open0 W))
            body))

    pᶜ-open :
      suc (suc Δ) ∣ srcStoreⁿ splitStore
        ⊢ (⇑ᶜ (renameᶜ (extᵗ suc) p)) [ zero ]ᶜ ∶ᶜ C ⊒ D
    pᶜ-open =
      subst
        (λ c → _ ∣ srcStoreⁿ splitStore ⊢ c ∶ᶜ C ⊒ D)
        (sym (open-shiftᶜ zero (renameᶜ (extᵗ suc) p)))
        pᶜ

    raw :
      suc (suc Δ) ∣ splitStore ∣ []
        ⊢ (renameᵗᵐ close01ᵗ W) [ suc zero ]ᵀ
          ⊒ (⇑ᵗᵐ (renameᵗᵐ (extᵗ suc) V′)) [ zero ]ᵀ
          ∶ (⇑ᶜ (renameᶜ (extᵗ suc) p)) [ zero ]ᶜ
    raw =
      split id★-coercionᶜ pᶜ-open premise

merge01-split-rebuild-pred :
  ∀ {Δ σ W V′ p C D} →
  suc (suc Δ) ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))
    ⊢ renameᶜ (extᵗ suc) p ∶ᶜ C ⊒ D →
  suc (suc Δ) ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ renameᵗᵐ merge01ᵗ W
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p →
  suc (suc Δ) ∣
    (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p
merge01-split-rebuild-pred {W = W} pᶜ body =
  subst
    (λ S → _ ∣ _ ∣ []
      ⊢ S ⊒ _ ∶ _)
    (renameᵗᵐ-raise0-pred W)
    (merge01-split-rebuild pᶜ body)

merge01-split-rebuild-gen :
  ∀ {Δ σ W V′ A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc (suc Δ) ∣ (zero ꞉ id ★) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ renameᵗᵐ merge01ᵗ W
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p →
  suc (suc Δ) ∣
    (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p
merge01-split-rebuild-gen
    {σ = σ} {A = A} {B = B} {p = p} pᶜ body =
  merge01-split-rebuild-pred
    {σ = σ} {p = p}
    (gen-body-target-first-coercionᶜ {σ = σ} {A = A} {B = B} pᶜ)
    body

gen-body-open-split-coercion :
  ∀ {Δ σ A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ)
    ⊢ (⇑ᶜ p) [ zero ]ᶜ ∶ᶜ ⇑ᵗ A ⊒ B
gen-body-open-split-coercion {σ = σ} {p = p}
    (cast-gen hA occ body⊢ , gen bodyⁿ) =
  subst
    (λ c → _ ∣ _ ⊢ c ∶ᶜ _ ⊒ _)
    (sym (open-shiftᶜ zero p))
    (subst
      (λ Σ → _ ∣ (suc zero , ★) ∷ Σ ⊢ p ∶ᶜ _ ⊒ _)
      (sym (srcStoreⁿ-⇑ˢ σ))
      (narrow-weaken ≤-refl StoreIncl-drop
        (narrow-mode-relax gen-tag-or-id≤tag-or-id (body⊢ , bodyⁿ))))

catchup-gen-body-open-split-coercion :
  ∀ {Δ Δ′ σ π Π Π′ χs A B p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  suc Δ′ ∣
    srcStoreⁿ
      ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷
        ⇑ˢ (combineStoreNrw π σ))
    ⊢ (⇑ᶜ (applyCoercionUnderTyBinders χs p)) [ zero ]ᶜ
      ∶ᶜ ⇑ᵗ (applyTys χs A) ⊒ applyTysUnderTyBinders χs B
catchup-gen-body-open-split-coercion {σ = σ} {π = π} {χs = χs}
    pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  gen-body-open-split-coercion {σ = combineStoreNrw π σ}
    (catchup-gen-coercion-typing-transport
      {σ = σ} {χs = χs} pᶜ Δ′≡ Π≡ Π′≡ π⊒)

extend-replace-here-term :
  ∀ {Δ α q A B σ γ M T c C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ c ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c →
  Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c
extend-replace-here-term {α = α} {q = q} {A = A} {σ = σ}
    {γ = γ} {M = M} {T = T} {c = c} qᶜ cᶜ M⊒T =
  let
    T≡ = open-shiftᵐ α T
    c≡ = open-shiftᶜ α c
    cᶜ′ =
      subst
        (λ c₀ → _ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ c₀ ∶ᶜ _ ⊒ _)
        (sym c≡)
        cᶜ
    premise =
      subst
        (λ c₀ → _ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
          ⊢ M ⊒ (⇑ᵗᵐ T) [ α ]ᵀ ∶ c₀)
        (sym c≡)
        (subst
          (λ T₀ → _ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ M ⊒ T₀ ∶ c)
          (sym T≡)
          M⊒T)
    rebuilt = extend qᶜ cᶜ′ premise
  in
  subst
    (λ T₀ → _ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ T₀ ∶ c)
    T≡
    (subst
      (λ c₀ → _ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ M ⊒ (⇑ᵗᵐ T) [ α ]ᵀ ∶ c₀)
      c≡
      rebuilt)

extendReplaceRel-⊒ˢ :
  ∀ {Δ σ σ′ Σ Σ′} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ σ′ ꞉ srcStoreⁿ σ′ ⊒ˢ Σ′
extendReplaceRel-⊒ˢ (replace-here {q = q} {A = A} qᶜ)
    (⊒ˢ-right hA σ⊒) =
  let
    srcq≡ = proj₁ (coercion-src-tgtᵐ (proj₁ qᶜ))
    qᶜ′ =
      subst
        (λ S → tag-or-idᵈ ∣ _ ∣ _ ⊢ q ∶ S ⊒ A)
        (sym srcq≡)
        qᶜ
    hsrcq = subst (λ S → WfTy _ S) (sym srcq≡) (narrow-src-wf qᶜ)
  in
  ⊒ˢ-both hsrcq hA (tag-or-idᵈ , qᶜ′)
    (subst (λ Σ₀ → _ ⊢ _ ꞉ Σ₀ ⊒ˢ _) (srcStoreⁿ-⊒ˢ σ⊒) σ⊒)
extendReplaceRel-⊒ˢ (replace-right rel) (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right hA (extendReplaceRel-⊒ˢ rel σ⊒)
extendReplaceRel-⊒ˢ (replace-left rel) (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (extendReplaceRel-⊒ˢ rel σ⊒)
extendReplaceRel-⊒ˢ (replace-both {q = q} rel)
    (⊒ˢ-both hA hA′ s⊒ σ⊒) =
  let
    incl =
      storeIncl-substˡ (srcStoreⁿ-⊒ˢ σ⊒)
        (extendReplaceRel-src-incl rel)
    srcq≡ = proj₁ (coercion-src-tgtᵐ (proj₁ (proj₂ s⊒)))
    s⊒′ =
      subst
        (λ S → _ ∣ _ ⊢ q ∶ S ⊒ _)
        (sym srcq≡)
        (narrow-weaken-store incl s⊒)
    hsrcq = subst (λ S → WfTy _ S) (sym srcq≡) hA
  in
  ⊒ˢ-both hsrcq hA′ s⊒′ (extendReplaceRel-⊒ˢ rel σ⊒)

extendReplaceRel-≈ⁿ :
  ∀ {Δ σ σ′ s t A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ s ≈ t ∶ A ⊒ B
extendReplaceRel-≈ⁿ rel
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  let
    incl =
      storeIncl-substˡ (srcStoreⁿ-⊒ˢ σ⊒)
        (extendReplaceRel-src-incl rel)
  in
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (extendReplaceRel-⊒ˢ rel σ⊒)
    wfΣ
    ( WfTyˢ-store-weaken incl (proj₁ wfΣ′)
    , WfTyˢ-store-weaken incl (proj₂ wfΣ′)
    )
    s⊒
    (narrow-weaken-store incl t⊒)

extendReplaceRel-coercionᶜ :
  ∀ {Δ σ σ′ c A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ ∣ srcStoreⁿ σ′ ⊢ c ∶ᶜ A ⊒ B
extendReplaceRel-coercionᶜ rel cᶜ =
  narrow-weaken ≤-refl (extendReplaceRel-src-incl rel) cᶜ

extendReplaceRel-compose-left :
  ∀ {Δ σ σ′ q s r A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
extendReplaceRel-compose-left rel
    (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒ (extendReplaceRel-≈ⁿ rel q⨟s≈r)

extendReplaceRel-compose-right :
  ∀ {Δ σ σ′ r t p A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
extendReplaceRel-compose-right rel
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒ (extendReplaceRel-≈ⁿ rel r≈t⨟p)

id-constᶜ :
  ∀ {Δ Σ} κ →
  Δ ∣ Σ ⊢ id (constTy κ) ∶ᶜ constTy κ ⊒ constTy κ
id-constᶜ (κℕ n) = cast-id wfBase refl , cross (id-‵ `ℕ)

id-ℕᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
id-ℕᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

value-•-impossible :
  ∀ {M} →
  Value (M •) →
  ⊥
value-•-impossible ()

extend-replace-here-current :
  ∀ {Δ α q A B σ γ M T c C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ σ) ⊢ c ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c →
  Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c
extend-replace-here-current qᶜ cᶜ =
  extend-replace-here-term qᶜ
    (narrow-weaken ≤-refl StoreIncl-drop cᶜ)

⊒Λ-body-add-split-marker :
  ∀ {Δ σ A B N V′ p} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ []
    ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p →
  suc Δ ∣ (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ ∣ []
    ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p
⊒Λ-body-add-split-marker
    {Δ = Δ} {σ = σ} {A = A} {B = B} {N = N} {V′ = V′} {p = p}
    pᶜ body =
  subst
    (λ c → suc Δ ∣ splitStore ∣ [] ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ c)
    (open-shiftᶜ zero p)
    (subst
      (λ T → suc Δ ∣ splitStore ∣ [] ⊢ ⇑ᵗᵐ N ⊒ T
        ∶ (⇑ᶜ p) [ zero ]ᶜ)
      (open-shiftᵐ zero V′)
      (subst
        (λ S → suc Δ ∣ splitStore ∣ [] ⊢ S
          ⊒ (⇑ᵗᵐ V′) [ zero ]ᵀ ∶ (⇑ᶜ p) [ zero ]ᶜ)
        (open-shiftᵐ (suc zero) (⇑ᵗᵐ N))
        raw))
  where
    splitStore = (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ

    pInnerᶜ :
      suc Δ ∣ srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)
        ⊢ p ∶ᶜ ⇑ᵗ A ⊒ B
    pInnerᶜ =
      subst
        (λ Σ → suc Δ ∣ Σ ⊢ p ∶ᶜ ⇑ᵗ A ⊒ B)
        (sym (srcStoreⁿ-⇑ˢ σ))
        (gen-body-coercionᶜ-tag pᶜ)

    bothBody :
      suc Δ ∣ (zero ꞉ id ★) ∷ ⇑ˢ σ ∣ []
        ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p
    bothBody =
      extend-replace-here-current id★-coercionᶜ pInnerᶜ body

    premise :
      suc Δ ∣ (zero ꞉ id ★) ∷ ⇑ˢ σ ∣ []
        ⊢ (⇑ᵗᵐ (⇑ᵗᵐ N)) [ zero ]ᵀ
          ⊒ (⇑ᵗᵐ V′) [ zero ]ᵀ
          ∶ (⇑ᶜ p) [ zero ]ᶜ
    premise =
      subst
        (λ c → suc Δ ∣ (zero ꞉ id ★) ∷ ⇑ˢ σ ∣ []
          ⊢ (⇑ᵗᵐ (⇑ᵗᵐ N)) [ zero ]ᵀ
          ⊒ (⇑ᵗᵐ V′) [ zero ]ᵀ ∶ c)
        (sym (open-shiftᶜ zero p))
        (subst
          (λ T → suc Δ ∣ (zero ꞉ id ★) ∷ ⇑ˢ σ ∣ []
            ⊢ (⇑ᵗᵐ (⇑ᵗᵐ N)) [ zero ]ᵀ ⊒ T ∶ p)
          (sym (open-shiftᵐ zero V′))
          (subst
            (λ S → suc Δ ∣ (zero ꞉ id ★) ∷ ⇑ˢ σ ∣ []
              ⊢ S ⊒ V′ ∶ p)
            (sym (open-shiftᵐ zero (⇑ᵗᵐ N)))
            bothBody))

    raw :
      suc Δ ∣ splitStore ∣ []
        ⊢ (⇑ᵗᵐ (⇑ᵗᵐ N)) [ suc zero ]ᵀ
          ⊒ (⇑ᵗᵐ V′) [ zero ]ᵀ
          ∶ (⇑ᶜ p) [ zero ]ᶜ
    raw =
      split id★-coercionᶜ
        (gen-body-open-split-coercion {σ = σ} pᶜ)
        premise

extendReplaceRel-term :
  ∀ {Δ σ σ′ γ M T c} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c →
  Δ ∣ σ′ ∣ γ ⊢ M ⊒ T ∶ c
extendReplaceRel-term (replace-here qᶜ) (split q₀ᶜ pαᶜ M⊒T) =
  extend-replace-here-current qᶜ pαᶜ (split q₀ᶜ pαᶜ M⊒T)
extendReplaceRel-term (replace-here qᶜ) (⊒blame pᶜ) =
  extend-replace-here-current qᶜ pᶜ (⊒blame pᶜ)
extendReplaceRel-term (replace-here qᶜ) (x⊒x pᶜ x∋p) =
  extend-replace-here-current qᶜ pᶜ (x⊒x pᶜ x∋p)
extendReplaceRel-term (replace-here qᶜ) (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  extend-replace-here-current qᶜ p↦qᶜ (ƛ⊒ƛ p↦qᶜ N⊒N′)
extendReplaceRel-term (replace-here qᶜ) (·⊒· q₀ᶜ L⊒L′ M⊒M′) =
  extend-replace-here-current qᶜ q₀ᶜ (·⊒· q₀ᶜ L⊒L′ M⊒M′)
extendReplaceRel-term (replace-here qᶜ) (Λ⊒Λ allᶜ vV V⊒V′) =
  extend-replace-here-current qᶜ allᶜ (Λ⊒Λ allᶜ vV V⊒V′)
extendReplaceRel-term (replace-here qᶜ) (⊒Λ pᶜ N⊒V′) =
  extend-replace-here-current qᶜ pᶜ (⊒Λ pᶜ N⊒V′)
extendReplaceRel-term (replace-here qᶜ) (⊒⟨ν⟩ pᶜ i N⊒V′s) =
  extend-replace-here-current qᶜ pᶜ (⊒⟨ν⟩ pᶜ i N⊒V′s)
extendReplaceRel-term (replace-here qᶜ) (⊒α γ′≡ pαᶜ L⊒L′) =
  extend-replace-here-current qᶜ pαᶜ (⊒α γ′≡ pαᶜ L⊒L′)
extendReplaceRel-term (replace-here qᶜ) (ν⊒ν pᶜ q₀ᶜ N⊒N′) =
  extend-replace-here-current qᶜ pᶜ (ν⊒ν pᶜ q₀ᶜ N⊒N′)
extendReplaceRel-term (replace-here qᶜ) (⊒ν pᶜ N⊒N′) =
  extend-replace-here-current qᶜ pᶜ (⊒ν pᶜ N⊒N′)
extendReplaceRel-term (replace-here qᶜ) (ν⊒ pᶜ N⊒N′) =
  extend-replace-here-current qᶜ pᶜ (ν⊒ pᶜ N⊒N′)
extendReplaceRel-term (replace-here qᶜ) (κ⊒κ κ) =
  extend-replace-here-current qᶜ (id-constᶜ κ) (κ⊒κ κ)
extendReplaceRel-term (replace-here qᶜ) (⊕⊒⊕ M⊒M′ N⊒N′) =
  extend-replace-here-current qᶜ id-ℕᶜ (⊕⊒⊕ M⊒M′ N⊒N′)
extendReplaceRel-term (replace-here qᶜ) (⊒cast+ q₀ᶜ q⨟s≈r M⊒M′) =
  extend-replace-here-current qᶜ q₀ᶜ
    (⊒cast+ q₀ᶜ q⨟s≈r M⊒M′)
extendReplaceRel-term (replace-here qᶜ)
    (⊒cast- q₀ᶜ q⨟s≈r M⊒M′) =
  ⊒cast-
    (narrow-weaken ≤-refl StoreIncl-drop q₀ᶜ)
    (extendReplaceRel-compose-left (replace-here qᶜ) q⨟s≈r)
    (extendReplaceRel-term (replace-here qᶜ) M⊒M′)
extendReplaceRel-term (replace-here qᶜ)
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  cast+⊒
    (narrow-weaken ≤-refl StoreIncl-drop pᶜ)
    (extendReplaceRel-compose-right (replace-here qᶜ) r≈t⨟p)
    (extendReplaceRel-term (replace-here qᶜ) M⊒M′)
extendReplaceRel-term (replace-here qᶜ) (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  extend-replace-here-current qᶜ pᶜ
    (cast-⊒ pᶜ r≈t⨟p M⊒M′)
extendReplaceRel-term (replace-right rel) M⊒T = {!!}
extendReplaceRel-term (replace-left rel) (⊒blame pᶜ) =
  ⊒blame (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
extendReplaceRel-term (replace-left rel) (x⊒x pᶜ x∋p) =
  x⊒x (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ) x∋p
extendReplaceRel-term (replace-left rel) (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  ƛ⊒ƛ (extendReplaceRel-coercionᶜ (replace-left rel) p↦qᶜ)
    (extendReplaceRel-term (replace-left rel) N⊒N′)
extendReplaceRel-term (replace-left rel) (·⊒· qᶜ L⊒L′ M⊒M′) =
  ·⊒·
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    (extendReplaceRel-term (replace-left rel) L⊒L′)
    (extendReplaceRel-term (replace-left rel) M⊒M′)
extendReplaceRel-term (replace-left rel) (Λ⊒Λ allᶜ vV V⊒V′) =
  Λ⊒Λ (extendReplaceRel-coercionᶜ (replace-left rel) allᶜ) vV
    (extendReplaceRel-term (replace-left (extendReplaceRel-⇑ˢ rel))
      V⊒V′)
extendReplaceRel-term (replace-left rel) (⊒Λ pᶜ N⊒V′) =
  ⊒Λ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-term
      (replace-right (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒V′)
extendReplaceRel-term (replace-left rel) (⊒⟨ν⟩ pᶜ i N⊒V′s) =
  ⊒⟨ν⟩ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ) i
    (extendReplaceRel-term
      (replace-right (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒V′s)
extendReplaceRel-term (replace-left rel) (ν⊒ν {q = q} pᶜ qᶜ N⊒N′) =
  ν⊒ν
    (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    (extendReplaceRel-term
      (replace-both {q = ⇑ᶜ q}
        (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-left rel) (⊒ν pᶜ N⊒N′) =
  ⊒ν (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-term
      (replace-right (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-left rel) (ν⊒ pᶜ N⊒N′) =
  ν⊒ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-term
      (replace-left (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-left rel) (κ⊒κ κ) = κ⊒κ κ
extendReplaceRel-term (replace-left rel) (⊕⊒⊕ M⊒M′ N⊒N′) =
  ⊕⊒⊕
    (extendReplaceRel-term (replace-left rel) M⊒M′)
    (extendReplaceRel-term (replace-left rel) N⊒N′)
extendReplaceRel-term (replace-left rel) (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  ⊒cast+
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    (extendReplaceRel-compose-left (replace-left rel) q⨟s≈r)
    (extendReplaceRel-term (replace-left rel) M⊒M′)
extendReplaceRel-term (replace-left rel) (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  ⊒cast-
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    (extendReplaceRel-compose-left (replace-left rel) q⨟s≈r)
    (extendReplaceRel-term (replace-left rel) M⊒M′)
extendReplaceRel-term (replace-left rel) (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  cast+⊒
    (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-compose-right (replace-left rel) r≈t⨟p)
    (extendReplaceRel-term (replace-left rel) M⊒M′)
extendReplaceRel-term (replace-left rel) (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  cast-⊒
    (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-compose-right (replace-left rel) r≈t⨟p)
    (extendReplaceRel-term (replace-left rel) M⊒M′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (extend qᶜ pαᶜ M⊒T) =
  extend
    (extendReplaceRel-coercionᶜ rel qᶜ)
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pαᶜ)
    (extendReplaceRel-term (replace-right rel) M⊒T)
extendReplaceRel-term (replace-both {q = qh} rel) (⊒blame pᶜ) =
  ⊒blame (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
extendReplaceRel-term (replace-both {q = qh} rel) (x⊒x pᶜ x∋p) =
  x⊒x
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    x∋p
extendReplaceRel-term (replace-both {q = qh} rel)
    (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  ƛ⊒ƛ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) p↦qᶜ)
    (extendReplaceRel-term (replace-both {q = qh} rel) N⊒N′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (·⊒· qᶜ L⊒L′ M⊒M′) =
  ·⊒·
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    (extendReplaceRel-term (replace-both {q = qh} rel) L⊒L′)
    (extendReplaceRel-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (Λ⊒Λ allᶜ vV V⊒V′) =
  Λ⊒Λ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) allᶜ) vV
    (extendReplaceRel-term
      (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel))
      V⊒V′)
extendReplaceRel-term (replace-both {q = qh} rel) (⊒Λ pᶜ N⊒V′) =
  ⊒Λ (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-term
      (replace-right
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒V′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (⊒⟨ν⟩ pᶜ i N⊒V′s) =
  ⊒⟨ν⟩
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ) i
    (extendReplaceRel-term
      (replace-right
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒V′s)
extendReplaceRel-term (replace-both {q = qh} rel)
    (ν⊒ν {q = q} pᶜ qᶜ N⊒N′) =
  ν⊒ν
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    (extendReplaceRel-term
      (replace-both {q = ⇑ᶜ q}
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-both {q = qh} rel) (⊒ν pᶜ N⊒N′) =
  ⊒ν (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-term
      (replace-right
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-both {q = qh} rel) (ν⊒ pᶜ N⊒N′) =
  ν⊒ (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-term
      (replace-left
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-both {q = qh} rel) (κ⊒κ κ) = κ⊒κ κ
extendReplaceRel-term (replace-both {q = qh} rel) (⊕⊒⊕ M⊒M′ N⊒N′) =
  ⊕⊒⊕
    (extendReplaceRel-term (replace-both {q = qh} rel) M⊒M′)
    (extendReplaceRel-term (replace-both {q = qh} rel) N⊒N′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  ⊒cast+
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    (extendReplaceRel-compose-left (replace-both {q = qh} rel) q⨟s≈r)
    (extendReplaceRel-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  ⊒cast-
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    (extendReplaceRel-compose-left (replace-both {q = qh} rel) q⨟s≈r)
    (extendReplaceRel-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  cast+⊒
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-compose-right (replace-both {q = qh} rel) r≈t⨟p)
    (extendReplaceRel-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-term (replace-both {q = qh} rel)
    (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  cast-⊒
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-compose-right (replace-both {q = qh} rel) r≈t⨟p)
    (extendReplaceRel-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-term (replace-both {q = qh} rel) M⊒T = {!!}

catchup-extend-rel-shifted :
  ∀ n {Δ Δ′ σ π Π Π′ χs α q A B} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  ExtendReplaceRel Δ′
    (combineStoreNrw π ((α ꞉= A ⊒) ∷ σ))
    (combineStoreNrw π ((α ꞉ q) ∷ σ))
catchup-extend-rel-shifted n {Δ = Δ} {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ ⊒ˢ-nil =
  let
    empty≡ = shiftStore-empty-inv n (sym Π≡)
    Δ′≡Δ = trans Δ′≡ (applyTyCtxs-empty-id χs empty≡ Δ)
    qᶜ′ =
      subst
        (λ Δ₀ → Δ₀ ∣ _ ⊢ _ ∶ᶜ _ ⊒ _)
        (sym Δ′≡Δ)
        qᶜ
  in
  replace-here qᶜ′
catchup-extend-rel-shifted n qᶜ Δ′≡ Π≡ () (⊒ˢ-right hA π⊒)
catchup-extend-rel-shifted n {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    with storeChangesLastBind χs
catchup-extend-rel-shifted n {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
catchup-extend-rel-shifted n {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps | ()
catchup-extend-rel-shifted n {Δ = Δ} {σ = σ}
    {χs = .(χs ++ bind Aχ ∷ keeps)}
    {α = α} {q = q} {A = A}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | last-bind χs Aχ keeps keeps-ok =
  let
    Δtail≡ =
      trans Δ′≡
        (trans (applyTyCtxs-last-bind χs Aχ keeps keeps-ok Δ)
          (sym (applyTyCtxs-suc χs Δ)))
    Π-last≡ =
      trans Π≡
        (cong (shiftStore n)
          (applyStores-last-bind χs Aχ keeps keeps-ok []))
    Π-last-normal≡ =
      trans Π-last≡
        (shiftStore-cons n zero (⇑ᵗ Aχ) (⟰ᵗ (applyStores χs [])))
    Πtail≡ =
      trans (storeTail-∷≡ Π-last-normal≡)
        (shiftStore-⟰ᵗ n (applyStores χs []))
    tail =
      catchup-extend-rel-shifted (suc n) {χs = χs}
        {α = suc α} {q = ⇑ᶜ q} {A = ⇑ᵗ A}
        (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
        Δtail≡
        Πtail≡
        Π′≡
        π⊒
  in
  replace-left tail
catchup-extend-rel-shifted n qᶜ Δ′≡ Π≡ () (⊒ˢ-both hA hA′ s⊒ π⊒)

-- [New] Extend Prefix Transport.
--
-- The emitted prefix determines a single hidden store replacement:
-- `α ꞉= A ⊒` becomes `α ꞉ q`, shifted under every emitted source-only
-- binder.  The structural transport above then moves the term-imprecision
-- derivation across that replacement.  At the exact replacement head it wraps
-- non-endpoint constructors with `extend`; the cast endpoint constructors are
-- rebuilt structurally because their conclusion index is not necessarily
-- `∶ᶜ`.
catchup-extend-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs W N′ α p q A B C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π ((α ꞉= A ⊒) ∷ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
      ∶ applyCoercions χs (p [ α ]ᶜ) →
  Δ′ ∣ combineStoreNrw π ((α ꞉ q) ∷ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
      ∶ applyCoercions χs (p [ α ]ᶜ)
catchup-extend-transport {χs = χs} qᶜ pαᶜ Δ′≡ Π≡ Π′≡ π⊒ W⊒V =
  extendReplaceRel-term
    (catchup-extend-rel-shifted zero {χs = χs}
      qᶜ Δ′≡ Π≡ Π′≡ π⊒)
    W⊒V

postulate
  -- [New] Split Catchup Case.
  --
  -- This is a new catchup case rather than a pre-existing named cambridge25
  -- lemma.  The recursive call catches up the premise opened at `α` under
  -- `(α ꞉ q) ∷ σ`, but the conclusion must reduce the source opened at the
  -- new source-only variable `αᵢ` under
  -- `(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ`.
  --
  -- Attempted proof notes.  Reusing the `extend` transport shape is not enough:
  -- the proof must also change the source opening from `N [ α ]ᵀ` to
  -- `N [ αᵢ ]ᵀ` and move the emitted prefix through two fresh entries.  The
  -- apparent next lemma is a split-specific reduction transport/opening
  -- lemma for source type variables, paired with the same emitted-prefix
  -- bookkeeping used by `catchup-extend-transport`.
  catchup-split-catchup :
    ∀ {Δ σ χs W Δ′ Π Π′ π N N′ α αᵢ p q A C D} →
    Value W →
    No• W →
    (N [ α ]ᵀ —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs Δ →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
      ⊢ q ∶ᶜ ★ ⊒ A →
    Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
      ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
    Δ′ ∣ combineStoreNrw π ((α ꞉ q) ∷ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
        ∶ applyCoercions χs (p [ α ]ᶜ) →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (N [ αᵢ ]ᵀ —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) ∣ []
        ⊢ W′ ⊒ applyTerms χs′ (N′ [ α ]ᵀ)
          ∶ applyCoercions χs′ (p [ α ]ᶜ)

⊒Λ-body-split-marker-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p} →
  Value W →
  No• W →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (⇑ᵗᵐ N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ (suc Δ)) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′
      ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ) ∣ []
      ⊢ W′ ⊒ applyTerms χs′ V′ ∶ applyCoercions χs′ p
⊒Λ-body-split-marker-catchup
    {Δ = Δ} {σ = σ} {χs = χs} {W = W} {π = π}
    {A = A} {B = B} {N = N} {V′ = V′} {p = p}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    with catchup-split-catchup
      {Δ = suc Δ} {σ = ⇑ˢ σ} {χs = χs}
      {W = W} {α = zero} {αᵢ = suc zero}
      {p = ⇑ᶜ p} {q = id ★} {A = ★}
      vW
      noW
      (subst
        (λ S → S —↠[ χs ] W)
        (sym (open-shiftᵐ zero (⇑ᵗᵐ N)))
        ⇑N↠W)
      Δ′≡
      Π≡
      Π′≡
      π⊒
      id★-coercionᶜ
      (gen-body-open-split-coercion {σ = σ} pᶜ)
      (catchup-extend-transport
        {σ = ⇑ˢ σ} {π = π} {χs = χs}
        {α = zero} {q = id ★} {A = ★}
        id★-coercionᶜ
        (subst
          (λ c → suc Δ ∣ srcStoreⁿ ((zero ꞉ id ★) ∷ ⇑ˢ σ)
            ⊢ c ∶ᶜ ⇑ᵗ A ⊒ B)
          (sym (open-shiftᶜ zero p))
          (subst
            (λ Σ → suc Δ ∣ (zero , ★) ∷ Σ ⊢ p ∶ᶜ ⇑ᵗ A ⊒ B)
            (sym (srcStoreⁿ-⇑ˢ σ))
            (narrow-weaken ≤-refl StoreIncl-drop
              (gen-body-coercionᶜ-tag pᶜ))))
        Δ′≡
        Π≡
        Π′≡
        π⊒
        (subst
          (λ c → _ ∣ combineStoreNrw π
            ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
            ⊢ W ⊒ applyTerms χs ((⇑ᵗᵐ V′) [ zero ]ᵀ)
              ∶ applyCoercions χs c)
          (sym (open-shiftᶜ zero p))
          (subst
            (λ T → _ ∣ combineStoreNrw π
              ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
              ⊢ W ⊒ applyTerms χs T ∶ applyCoercions χs p)
            (sym (open-shiftᵐ zero V′))
            W⊒V′)))
⊒Λ-body-split-marker-catchup
    {Δ = Δ} {σ = σ} {χs = χs} {W = W} {N = N} {V′ = V′} {p = p}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , source↠′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body′ =
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  noW′ ,
  subst
    (λ S → S —↠[ χs′ ] W′)
    (open-shiftᵐ (suc zero) (⇑ᵗᵐ N))
    source↠′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′
      ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ) ∣ []
      ⊢ W′ ⊒ applyTerms χs′ V′ ∶ applyCoercions χs′ c)
    (open-shiftᶜ zero p)
    (subst
      (λ T → Δ″ ∣ combineStoreNrw π′
        ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ) ∣ []
        ⊢ W′ ⊒ applyTerms χs′ T ∶
          applyCoercions χs′ ((⇑ᶜ p) [ zero ]ᶜ))
      (open-shiftᵐ zero V′)
      body′)

catchup-⊒Λ-no-bind-finish :
  ∀ {Δ σ χs N W′ A B V′ p} →
  AllKeep χs →
  Value W′ →
  No• W′ →
  (N —↠[ χs ] W′) →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ []
    ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ p →
  ∃[ χs′ ] ∃[ W″ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W″ ×
    No• W″ ×
    (N —↠[ χs′ ] W″) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W″ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-no-bind-finish {Δ = Δ} {σ = σ} {χs = χs}
    {W′ = W′} {A = A} {V′ = V′} {p = p}
    keeps vW′ noW′ N↠W′ pᶜ body =
  let
    Δ≡ = sym (allKeep-applyTyCtxs-id keeps Δ)
    Π≡ = sym (allKeep-applyStores-id keeps [])
    target≡ =
      trans (applyTerms-Λ χs V′)
        (cong Λ_ (allKeep-applyTermsUnderTyBinders-id keeps V′))
    coercion≡ =
      trans (applyCoercions-gen χs A p)
        (cong₂ gen (allKeep-applyTys-id keeps A)
          (allKeep-applyCoercionUnderTyBinders-id keeps p))
    rebuilt = ⊒Λ pᶜ body
  in
  χs , W′ , Δ , [] , [] , [] ,
  vW′ ,
  noW′ ,
  N↠W′ ,
  Δ≡ ,
  Π≡ ,
  refl ,
  ⊒ˢ-nil ,
  subst
    (λ c → Δ ∣ combineStoreNrw [] σ ∣ []
      ⊢ W′ ⊒ applyTerms χs (Λ V′) ∶ c)
    (sym coercion≡)
    (subst
      (λ T → Δ ∣ combineStoreNrw [] σ ∣ [] ⊢ W′ ⊒ T ∶ gen A p)
      (sym target≡)
      rebuilt)

catchup-⊒Λ-no-bind-shift-image :
  ∀ {Δ σ χs N W W′ Δ′ π A B V′ p} →
  AllKeep χs →
  Value W′ →
  No• W′ →
  (N —↠[ χs ] W′) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  π ≡ [] →
  W ≡ ⇑ᵗᵐ W′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W″ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W″ ×
    No• W″ ×
    (N —↠[ χs′ ] W″) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W″ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-no-bind-shift-image
    {Δ = Δ} {σ = σ} {χs = χs} {W = W} {W′ = W′}
    {Δ′ = Δ′} {π = π} {V′ = V′} {p = p}
    keeps vW′ noW′ N↠W′ Δ′≡ π≡[] W≡⇑W′ pᶜ W⊒V′ =
  catchup-⊒Λ-no-bind-finish keeps vW′ noW′ N↠W′ pᶜ body
  where
    σ★ = (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ
    Δ′≡sucΔ = trans Δ′≡ (allKeep-applyTyCtxs-id keeps (suc Δ))
    σ≡ = cong (λ π₀ → combineStoreNrw π₀ σ★) π≡[]
    target≡ = allKeep-applyTerms-id keeps V′
    coercion≡ = allKeep-applyCoercions-id keeps p

    body :
      suc Δ ∣ σ★ ∣ [] ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ p
    body =
      subst
        (λ Δ₀ → Δ₀ ∣ σ★ ∣ [] ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ p)
        Δ′≡sucΔ
        (subst
          (λ σ₀ → Δ′ ∣ σ₀ ∣ [] ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ p)
          σ≡
          (subst
            (λ c → Δ′ ∣ combineStoreNrw π σ★ ∣ []
              ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ c)
            coercion≡
            (subst
              (λ T → Δ′ ∣ combineStoreNrw π σ★ ∣ []
                ⊢ ⇑ᵗᵐ W′ ⊒ T ∶ applyCoercions χs p)
              target≡
              (subst
                (λ S → Δ′ ∣ combineStoreNrw π σ★ ∣ []
                  ⊢ S ⊒ applyTerms χs V′ ∶ applyCoercions χs p)
                W≡⇑W′
                W⊒V′))))

catchup-⊒Λ-single-bind-finish :
  ∀ {Δ σ χs keeps N W′ A B V′ p} →
  AllKeep χs →
  AllKeep keeps →
  Value W′ →
  No• W′ →
  (N —↠[ χs ++ bind ★ ∷ keeps ] W′) →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc (suc Δ) ∣
    (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ ⇑ᵗᵐ W′ ⊒ renameᵗᵐ (extᵗ suc) V′
      ∶ renameᶜ (extᵗ suc) p →
  ∃[ χs′ ] ∃[ W″ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W″ ×
    No• W″ ×
    (N —↠[ χs′ ] W″) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W″ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-single-bind-finish
    {Δ = Δ} {σ = σ} {χs = χs} {keeps = keeps}
    {W′ = W′} {A = A} {B = B} {V′ = V′} {p = p}
    keepsχ keepsTail vW′ noW′ N↠W′ pᶜ body =
  χs′ , W′ , suc Δ , (zero , ★) ∷ [] , [] , π′ ,
  vW′ ,
  noW′ ,
  N↠W′ ,
  Δ≡ ,
  Π≡ ,
  refl ,
  π′⊒ ,
  subst
    (λ c → suc Δ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′) ∶ c)
    (sym coercion≡)
    (subst
      (λ T → suc Δ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ T ∶ gen (⇑ᵗ A) (renameᶜ (extᵗ suc) p))
      (sym target≡)
      (⊒Λ pᶜ′ body))
  where
    χs′ = χs ++ bind ★ ∷ keeps
    π′ = (⊒ zero ꞉=☆) ∷ []

    Δ≡ :
      suc Δ ≡ applyTyCtxs χs′ Δ
    Δ≡ =
      sym
        (trans
          (applyTyCtxs-last-bind χs ★ keeps keepsTail Δ)
          (cong suc (allKeep-applyTyCtxs-id keepsχ Δ)))

    Π≡ :
      (zero , ★) ∷ [] ≡ applyStores χs′ []
    Π≡ =
      sym
        (trans
          (applyStores-last-bind χs ★ keeps keepsTail [])
          (cong (applyStore (bind ★))
            (allKeep-applyStores-id keepsχ [])))

    π′⊒ :
      suc Δ ⊢ π′ ꞉ (zero , ★) ∷ [] ⊒ˢ []
    π′⊒ = ⊒ˢ-left ⊒ˢ-nil

    A≡ :
      applyTys χs′ A ≡ ⇑ᵗ A
    A≡ =
      trans
        (applyTys-last-bind χs ★ keeps keepsTail A)
        (cong ⇑ᵗ (allKeep-applyTys-id keepsχ A))

    pUnder≡ :
      applyCoercionUnderTyBinders χs′ p ≡ renameᶜ (extᵗ suc) p
    pUnder≡ =
      trans
        (applyCoercionUnderTyBinders-last-bind
          {χs = χs} {A = ★} {keeps = keeps} keepsTail)
        (cong (renameᶜ (extᵗ suc))
          (allKeep-applyCoercionUnderTyBinders-id keepsχ p))

    pᶜ′ :
      suc Δ ∣ srcStoreⁿ (combineStoreNrw π′ σ)
        ⊢ gen (⇑ᵗ A) (renameᶜ (extᵗ suc) p)
          ∶ᶜ ⇑ᵗ A ⊒ `∀ (applyTysUnderTyBinders χs′ B)
    pᶜ′ =
      subst
        (λ q → suc Δ ∣ srcStoreⁿ (combineStoreNrw π′ σ)
          ⊢ gen (⇑ᵗ A) q ∶ᶜ ⇑ᵗ A ⊒
            `∀ (applyTysUnderTyBinders χs′ B))
        pUnder≡
        (subst
          (λ C → suc Δ ∣ srcStoreⁿ (combineStoreNrw π′ σ)
            ⊢ gen C (applyCoercionUnderTyBinders χs′ p)
              ∶ᶜ C ⊒ `∀ (applyTysUnderTyBinders χs′ B))
          A≡
          (catchup-gen-coercion-typing-transport
            {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A}
            pᶜ Δ≡ Π≡ refl π′⊒))

    target≡ :
      applyTerms χs′ (Λ V′) ≡ Λ (renameᵗᵐ (extᵗ suc) V′)
    target≡ =
      trans
        (applyTerms-Λ χs′ V′)
        (cong Λ_
          (trans
            (applyTermsUnderTyBinders-last-bind
              {χs = χs} {A = ★} {keeps = keeps} keepsTail)
            (cong (renameᵗᵐ (extᵗ suc))
              (allKeep-applyTermsUnderTyBinders-id keepsχ V′))))

    coercion≡ :
      applyCoercions χs′ (gen A p) ≡
        gen (⇑ᵗ A) (renameᶜ (extᵗ suc) p)
    coercion≡ =
      trans
        (applyCoercions-gen χs′ A p)
        (cong₂ gen A≡ pUnder≡)

catchup-⊒Λ-no-earlier-bind-source-first :
  ∀ {Δ σ χs keeps Aχ W Δ′ Π Π′ π N V′ p} →
  AllKeep χs →
  AllKeep keeps →
  Value W →
  CatchupSafe (⇑ᵗᵐ N) →
  (⇑ᵗᵐ N —↠[ χs ++ bind Aχ ∷ keeps ] W) →
  Δ′ ≡ applyTyCtxs (χs ++ bind Aχ ∷ keeps) (suc Δ) →
  Π ≡ applyStores (χs ++ bind Aχ ∷ keeps) [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms (χs ++ bind Aχ ∷ keeps) V′
      ∶ applyCoercions (χs ++ bind Aχ ∷ keeps) p →
  (N —↠[ χs ++ bind ★ ∷ keeps ] renameᵗᵐ predᵗ W) ×
  (suc (suc Δ) ∣
    (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p)
catchup-⊒Λ-no-earlier-bind-source-first
    {Δ = Δ} {σ = σ} {χs = χs} {keeps = keeps}
    {Aχ = Aχ} {W = W} {Δ′ = Δ′} {Π = Π} {Π′ = Π′}
    {π = π} {N = N₀} {V′ = V′} {p = p}
    keepsχ keepsTail vW safe⇑N ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′
    with ↠-split-last-bind ⇑N↠W
       | last-bind-empty-target-lowered-tail
           {π = π} {Π = Π} {χs = χs} {A = Aχ} {keeps = keeps}
           keepsTail Π≡
           (subst (λ Π₀ → _ ⊢ _ ꞉ _ ⊒ˢ Π₀) Π′≡ π⊒)
catchup-⊒Λ-no-earlier-bind-source-first
    {Δ = Δ} {σ = σ} {χs = χs} {keeps = keeps}
    {Aχ = Aχ} {W = W} {Δ′ = Δ′} {Π = Π} {Π′ = Π′}
    {π = π} {N = N₀} {V′ = V′} {p = p}
    keepsχ keepsTail vW safe⇑N ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′
    | P , Q , ⇑N↠P , P→Q , Q↠W
    | π₀ , π≡ , π₀⊒ =
  N↠W′ , body
  where
    Aχ≡★ : Aχ ≡ ★
    Aχ≡★ =
      last-bind-empty-target-star
        {π = π} {Π = Π} {χs = χs} {A = Aχ} {keeps = keeps}
        keepsTail Π≡
        (subst (λ Π₀ → _ ⊢ _ ꞉ _ ⊒ˢ Π₀) Π′≡ π⊒)

    N↠W′ : N₀ —↠[ χs ++ bind ★ ∷ keeps ] renameᵗᵐ predᵗ W
    N↠W′ =
      last-bind-pred-reduction
        {N = N₀}
        keepsχ keepsTail Aχ≡★ safe⇑N ⇑N↠P P→Q Q↠W vW

    Δ′≡tail :
      Δ′ ≡ suc (applyTyCtxs χs (suc Δ))
    Δ′≡tail =
      trans Δ′≡
        (applyTyCtxs-last-bind χs Aχ keeps keepsTail (suc Δ))

    Δ′≡sucsuc :
      Δ′ ≡ suc (suc Δ)
    Δ′≡sucsuc =
      trans Δ′≡tail
        (cong suc (allKeep-applyTyCtxs-id keepsχ (suc Δ)))

    target≡ :
      ⇑ᵗᵐ (applyTerms χs V′) ≡ ⇑ᵗᵐ V′
    target≡ = cong ⇑ᵗᵐ (allKeep-applyTerms-id keepsχ V′)

    coercion≡ :
      ⇑ᶜ (applyCoercions χs p) ≡ ⇑ᶜ p
    coercion≡ = cong ⇑ᶜ (allKeep-applyCoercions-id keepsχ p)

    body₀ :
      Δ′ ∣
        (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
        ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V′)
          ∶ ⇑ᶜ (applyCoercions χs p)
    body₀ =
      last-bind-source-first-body-empty-tail
        {σ = σ} {χs = χs} {A = Aχ} {keeps = keeps}
        {V = V′} {p = p} {π₀ = π₀}
        {Π = applyStores χs []} {Π′ = []}
        keepsχ keepsTail π≡ refl refl π₀⊒ W⊒V′

    body :
      suc (suc Δ) ∣
        (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
        ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p
    body =
      subst
        (λ Δ₀ → Δ₀ ∣
          (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
          ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p)
        Δ′≡sucsuc
        (subst
          (λ c → Δ′ ∣
            (⊒ zero ꞉=☆) ∷
              (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
            ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ c)
          coercion≡
          (subst
            (λ T → Δ′ ∣
              (⊒ zero ꞉=☆) ∷
                (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
              ⊢ W ⊒ T ∶ ⇑ᶜ (applyCoercions χs p))
            target≡
            body₀))

catchup-⊒Λ-no-earlier-bind-catchup :
  ∀ {Δ σ χs keeps Aχ W Δ′ Π Π′ π A B N V′ p} →
  AllKeep χs →
  AllKeep keeps →
  Value W →
  No• W →
  CatchupSafe (⇑ᵗᵐ N) →
  (⇑ᵗᵐ N —↠[ χs ++ bind Aχ ∷ keeps ] W) →
  Δ′ ≡ applyTyCtxs (χs ++ bind Aχ ∷ keeps) (suc Δ) →
  Π ≡ applyStores (χs ++ bind Aχ ∷ keeps) [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms (χs ++ bind Aχ ∷ keeps) V′
      ∶ applyCoercions (χs ++ bind Aχ ∷ keeps) p →
  suc (suc Δ) ∣
    (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
    ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
      ⊒ renameᵗᵐ (extᵗ suc) V′ ∶ renameᶜ (extᵗ suc) p →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-no-earlier-bind-catchup
    keepsχ keepsTail vW noW safe⇑N ⇑N↠W
    Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′ replay =
  catchup-⊒Λ-single-bind-finish
    keepsχ
    keepsTail
    (renameᵗᵐ-preserves-Value predᵗ vW)
    (renameᵗᵐ-preserves-No• predᵗ noW)
    N↠W′
    pᶜ
    replay
  where
    N↠W′ =
      proj₁
        (catchup-⊒Λ-no-earlier-bind-source-first
          keepsχ keepsTail vW safe⇑N ⇑N↠W
          Δ′≡ Π≡ Π′≡ π⊒ W⊒V′)

catchup-⊒Λ-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p} →
  Value W →
  No• W →
  CatchupSafe (⇑ᵗᵐ N) →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-catchup
    vW noW safe⇑N ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    with storeChangesLastBind _
catchup-⊒Λ-catchup
    vW noW safe⇑N ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | no-bind keeps =
  catchup-⊒Λ-no-bind-shift-image
    keeps
    (renameᵗᵐ-preserves-Value predᵗ vW)
    (renameᵗᵐ-preserves-No• predᵗ noW)
    (pure-pred-↠-shifted-value keeps ⇑N↠W vW)
    Δ′≡
    (allKeep-empty-target-nil keeps Π≡ Π′≡ π⊒)
    (safe-allKeep-value-image safe⇑N (_ , refl) keeps ⇑N↠W vW)
    pᶜ
    W⊒V′
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW noW safe⇑N ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | last-bind χs Aχ keeps keeps-ok
    with shifted-source-catchup-Λ-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW noW safe⇑N ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | last-bind χs Aχ keeps keeps-ok
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
  let
    pᶜ′ =
      catchup-gen-coercion-typing-transport
        {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A} {B = B}
        pᶜ Δ″≡ Π″≡ Π″′≡ π′⊒
    rebuilt = ⊒Λ pᶜ′ body
    target≡ = applyTerms-Λ χs′ V′
    coercion≡ = applyCoercions-gen χs′ A p
  in
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  noW′ ,
  N↠W′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′) ∶ c)
    (sym coercion≡)
    (subst
      (λ T → Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ T ∶ gen (applyTys χs′ A)
          (applyCoercionUnderTyBinders χs′ p))
      (sym target≡)
      rebuilt)

catchup-⊒⟨ν⟩-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p s} →
  Value W →
  No• W →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Inert s →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (V′ ⟨ s ⟩) ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    with shifted-source-catchup-⟨ν⟩-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′s
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
  let
    pᶜ′ =
      catchup-gen-coercion-typing-transport
        {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A} {B = B}
        pᶜ Δ″≡ Π″≡ Π″′≡ π′⊒
    i′ = applyCoercionUnderTyBinders-preserves-Inert χs′ i
    rebuilt = ⊒⟨ν⟩ pᶜ′ i′ body
    target≡ =
      trans (applyTerms-cast χs′ V′ (gen A s))
        (cong (λ c → applyTerms χs′ V′ ⟨ c ⟩)
          (applyCoercions-gen χs′ A s))
    coercion≡ = applyCoercions-gen χs′ A p
  in
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  noW′ ,
  N↠W′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩) ∶ c)
    (sym coercion≡)
    (subst
      (λ T → Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ T ∶ gen (applyTys χs′ A)
          (applyCoercionUnderTyBinders χs′ p))
      (sym target≡)
      rebuilt)

postulate
  -- [New] Right ν Catchup Case.
  --
  -- This is a new catchup case, not a pre-existing named cambridge25 lemma.
  -- The recursive call catches up the shifted premise under
  -- `(⊒ zero ꞉=☆) ∷ ⇑ˢ σ`; the desired conclusion is for the
  -- unshifted wrapper `ν ★ N (⇑ᶜ p)` under `σ`.
  --
  -- Attempted proof notes.  Lifting the recursive source reduction through the
  -- `ν` wrapper is straightforward, but the remaining step needs more than a
  -- plain transport: one has to use the canonical runtime shape of the
  -- caught-up polymorphic value to take the `ν` store-opening step, then
  -- remove the source-only star entry from the emitted prefix and unshift the
  -- target relation.  This should probably be factored through the same
  -- shifted-source inversion lemma needed by `⊒Λ`, plus a small reduction
  -- lemma for `ν` opening and the corresponding store-prefix transport.
  catchup-ν⊒-catchup :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V p A B} →
    Value V →
    Value W →
    No• W →
    (N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
    Δ′ ∣ combineStoreNrw π ((⊒ zero ꞉=☆) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (⇑ᵗᵐ V) ∶ applyCoercions χs (⇑ᶜ p) →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (ν ★ N (⇑ᶜ p) —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ applyTerms χs′ V ∶ applyCoercions χs′ p

catchup-lemma :
  ∀ {Δ σ M V p} →
  RuntimeOK M →
  Value V →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (M —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V ∶ applyCoercions χs p
catchup-lemma okM vV M⊒V = {!!}

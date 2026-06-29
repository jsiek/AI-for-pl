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
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Store using (StoreIncl; StoreIncl-cons; StoreIncl-drop)
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
    ( StoreDetWf-⟰ᵗ
    ; WfTyˢ-⇑ᵗ
    ; WfTyˢ-store-weaken
    ; narrowing-determinedᵐ
    ; narrow-⇑ᵗ-ᶜ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤
    ; narrow-⇑ᵗ-any
    ; narrow-drop-star-var
    ; narrow-drop-star
    ; srcStoreⁿ-⊒ˢ
    ; srcStoreⁿ-⇑ˢ
    ; ⇑ˢ-++
    ; ⊒ˢ-⇑ˢ
    ; ⊒ˢ-empty-⇑ˢ
    ; ⊒ˢ-empty-anyᵗ
    )
open import proof.CoercionProperties
  using
    ( coercion-src-tgtᵐ
    ; ModeRename
    ; renameᶜ-compose
    ; renameᶜ-ext-suc-comm
    ; renameᶜ-left-inverse
    ; src-renameᶜ
    ; tgt-renameᶜ
    )
open import proof.NuTermProperties
  using
    ( renameᵗᵐ-compose
    ; renameᵗᵐ-left-inverse
    ; renameᵗᵐ-preserves-Value
    ; renameᵗᵐ-reflects-Value
    )
open import proof.TypeProperties
  using (TyRenameWf; predᵗ; renameᵗ-compose; renameᵗ-ext-suc-comm)
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
    ; shifted-source-remainder
    ; type-app-source-no-value-target
    ; value?-none-no-value
    ; value-target-source-no-active
    ; value-target-source-safe
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

raise0ᵗ : Renameᵗ
raise0ᵗ X = suc (predᵗ X)

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
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
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
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ r →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
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

extend-replace-here-current :
  ∀ {Δ α q A B σ γ M T c C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ σ) ⊢ c ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c →
  Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c
extend-replace-here-current qᶜ cᶜ =
  extend-replace-here-term qᶜ
    (narrow-weaken ≤-refl StoreIncl-drop cᶜ)

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
extendReplaceRel-term (replace-here qᶜ) (⊒α pαᶜ L⊒L′) =
  extend-replace-here-current qᶜ pαᶜ (⊒α pαᶜ L⊒L′)
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
extendReplaceRel-term R@(replace-right (replace-left rel))
    (split {q = q} qᶜ pαᶜ M⊒T) =
  split
    (extendReplaceRel-coercionᶜ R qᶜ)
    (extendReplaceRel-coercionᶜ R pαᶜ)
    (extendReplaceRel-term (replace-both {q = q} rel) M⊒T)
extendReplaceRel-term R@(replace-right rel) (⊒blame pᶜ) =
  ⊒blame (extendReplaceRel-coercionᶜ R pᶜ)
extendReplaceRel-term R@(replace-right rel) (x⊒x pᶜ x∋p) =
  x⊒x (extendReplaceRel-coercionᶜ R pᶜ) x∋p
extendReplaceRel-term R@(replace-right rel) (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  ƛ⊒ƛ (extendReplaceRel-coercionᶜ R p↦qᶜ)
    (extendReplaceRel-term (replace-right rel) N⊒N′)
extendReplaceRel-term R@(replace-right rel) (·⊒· qᶜ L⊒L′ M⊒M′) =
  ·⊒·
    (extendReplaceRel-coercionᶜ R qᶜ)
    (extendReplaceRel-term (replace-right rel) L⊒L′)
    (extendReplaceRel-term (replace-right rel) M⊒M′)
extendReplaceRel-term R@(replace-right rel) (Λ⊒Λ allᶜ vV V⊒V′) =
  Λ⊒Λ (extendReplaceRel-coercionᶜ R allᶜ) vV
    (extendReplaceRel-term (replace-right (extendReplaceRel-⇑ˢ rel))
      V⊒V′)
extendReplaceRel-term R@(replace-right rel) (⊒Λ pᶜ N⊒V′) =
  ⊒Λ (extendReplaceRel-coercionᶜ R pᶜ)
    (extendReplaceRel-term
      (replace-right (replace-right (extendReplaceRel-⇑ˢ rel)))
      N⊒V′)
extendReplaceRel-term R@(replace-right rel) (⊒⟨ν⟩ pᶜ i N⊒V′s) =
  ⊒⟨ν⟩ (extendReplaceRel-coercionᶜ R pᶜ) i
    (extendReplaceRel-term
      (replace-right (replace-right (extendReplaceRel-⇑ˢ rel)))
      N⊒V′s)
extendReplaceRel-term R@(replace-right rel) (⊒α pαᶜ L⊒L′) =
  ⊒α
    (extendReplaceRel-coercionᶜ R pαᶜ)
    (extendReplaceRel-term rel L⊒L′)
extendReplaceRel-term R@(replace-right rel)
    (ν⊒ν {q = q} pᶜ qᶜ N⊒N′) =
  ν⊒ν
    (extendReplaceRel-coercionᶜ R pᶜ)
    (extendReplaceRel-coercionᶜ R qᶜ)
    (extendReplaceRel-term
      (replace-both {q = ⇑ᶜ q}
        (replace-right (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term R@(replace-right rel) (⊒ν pᶜ N⊒N′) =
  ⊒ν (extendReplaceRel-coercionᶜ R pᶜ)
    (extendReplaceRel-term
      (replace-right (replace-right (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term R@(replace-right rel) (ν⊒ pᶜ N⊒N′) =
  ν⊒ (extendReplaceRel-coercionᶜ R pᶜ)
    (extendReplaceRel-term
      (replace-left (replace-right (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-term (replace-right rel) (κ⊒κ κ) = κ⊒κ κ
extendReplaceRel-term (replace-right rel) (⊕⊒⊕ M⊒M′ N⊒N′) =
  ⊕⊒⊕
    (extendReplaceRel-term (replace-right rel) M⊒M′)
    (extendReplaceRel-term (replace-right rel) N⊒N′)
extendReplaceRel-term R@(replace-right rel) (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  ⊒cast+
    (extendReplaceRel-coercionᶜ R qᶜ)
    (extendReplaceRel-compose-left R q⨟s≈r)
    (extendReplaceRel-term (replace-right rel) M⊒M′)
extendReplaceRel-term R@(replace-right rel) (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  ⊒cast-
    (extendReplaceRel-coercionᶜ R qᶜ)
    (extendReplaceRel-compose-left R q⨟s≈r)
    (extendReplaceRel-term (replace-right rel) M⊒M′)
extendReplaceRel-term R@(replace-right rel) (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  cast+⊒
    (extendReplaceRel-coercionᶜ R pᶜ)
    (extendReplaceRel-compose-right R r≈t⨟p)
    (extendReplaceRel-term (replace-right rel) M⊒M′)
extendReplaceRel-term R@(replace-right rel) (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  cast-⊒
    (extendReplaceRel-coercionᶜ R pᶜ)
    (extendReplaceRel-compose-right R r≈t⨟p)
    (extendReplaceRel-term (replace-right rel) M⊒M′)
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
    (α⊒α qᶜ pαᶜ L⊒L′) =
  α⊒α
    (extendReplaceRel-coercionᶜ rel qᶜ)
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pαᶜ)
    (extendReplaceRel-term rel L⊒L′)
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
      (N [ αᵢ ]ᵀ —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) ∣ []
        ⊢ W′ ⊒ applyTerms χs′ (N′ [ α ]ᵀ)
          ∶ applyCoercions χs′ (p [ α ]ᶜ)

catchup-⊒Λ-no-bind-finish :
  ∀ {Δ σ χs N W′ A B V′ p} →
  AllKeep χs →
  Value W′ →
  (N —↠[ χs ] W′) →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ []
    ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ p →
  ∃[ χs′ ] ∃[ W″ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W″ ×
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
    keeps vW′ N↠W′ pᶜ body =
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
  (N —↠[ χs ] W′) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  π ≡ [] →
  W ≡ ⇑ᵗᵐ W′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W″ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W″ ×
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
    keeps vW′ N↠W′ Δ′≡ π≡[] W≡⇑W′ pᶜ W⊒V′ =
  catchup-⊒Λ-no-bind-finish keeps vW′ N↠W′ pᶜ body
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

catchup-⊒Λ-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p} →
  Value W →
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
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    with shifted-source-catchup-Λ-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
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
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    with shifted-source-catchup-⟨ν⟩-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′s
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
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
      (ν ★ N (⇑ᶜ p) —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ applyTerms χs′ V ∶ applyCoercions χs′ p

catchup-lemma :
  ∀ {Δ σ M V p} →
  Value V →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    (M —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V ∶ applyCoercions χs p
catchup-lemma vV (extend qᶜ pαᶜ M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma vV (extend qᶜ pαᶜ M⊒V)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V =
  -- Need transport for catchup evidence through the de Bruijn store-prefix
  -- change made by `extend`: rebuild `extend` after moving the emitted
  -- narrowing `π` under the existing fresh α entry.  The side conditions
  -- `qᶜ` and `pαᶜ` must also be transported from the original Δ/σ to the
  -- emitted Δ′/`combineStoreNrw π σ` context.  This is source-only
  -- store-prefix transport, not ordinary `applyStore` transport on both
  -- source and target stores.
  χs , W , Δ′ , Π , Π′ , π ,
  vW ,
  M↠W ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  catchup-extend-transport
    {π = π} {χs = χs}
    qᶜ pαᶜ Δ′≡ Π≡ Π′≡ π⊒ W⊒V
catchup-lemma vV (split qᶜ pαᶜ M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma vV (split qᶜ pαᶜ M⊒V)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V =
  catchup-split-catchup
    vW
    M↠W
    Δ′≡
    Π≡
    Π′≡
    π⊒
    qᶜ
    pαᶜ
    W⊒V
catchup-lemma () (⊒blame pᶜ)
catchup-lemma () (x⊒x pᶜ x∋p)
catchup-lemma (ƛ N′) (ƛ⊒ƛ {N = N} p↦qᶜ N⊒N′) =
  [] , ƛ N , _ , [] , [] , [] ,
  ƛ N ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ƛ⊒ƛ p↦qᶜ N⊒N′
catchup-lemma () (·⊒· qᶜ L⊒L′ M⊒M′)
catchup-lemma (Λ vV′) (Λ⊒Λ allᶜ vV V⊒V′) =
  [] , Λ _ , _ , [] , [] , [] ,
  Λ vV ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  Λ⊒Λ allᶜ vV V⊒V′
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′)
    with value? N in valueN≡
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′) | just vN =
  [] , N , _ , [] , [] , [] ,
  vN ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒Λ pᶜ N⊒V′
catchup-lemma (Λ vV′) (⊒Λ {N = Λ M} pᶜ N⊒V′)
    | nothing
    with value? M in valueM≡
catchup-lemma (Λ vV′) (⊒Λ {N = Λ M} pᶜ N⊒V′)
    | nothing | just vM =
  [] , Λ M , _ , [] , [] , [] ,
  Λ vM ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒Λ pᶜ N⊒V′
catchup-lemma (Λ vV′) (⊒Λ {N = Λ M} pᶜ N⊒V′)
    | nothing | nothing =
  ⊥-elim
    (value?-none-no-value valueM≡
      (renameᵗᵐ-reflects-Value (extᵗ suc)
        (lambda-source-value-target-source-value vV′ N⊒V′)))
catchup-lemma (Λ vV′) (⊒Λ {N = L •} pᶜ N⊒V′)
    | nothing =
  ⊥-elim (type-app-source-no-value-target vV′ N⊒V′)
catchup-lemma (Λ vV′) (⊒Λ {N = ` x} pᶜ N⊒V′)
    | nothing =
  ⊥-elim (neutral-source-no-value-target neutral-` vV′ N⊒V′)
catchup-lemma (Λ vV′) (⊒Λ {N = L · M} pᶜ N⊒V′)
    | nothing =
  ⊥-elim (neutral-source-no-value-target neutral-· vV′ N⊒V′)
catchup-lemma (Λ vV′) (⊒Λ {N = L ⊕[ op ] M} pᶜ N⊒V′)
    | nothing =
  ⊥-elim (neutral-source-no-value-target neutral-⊕ vV′ N⊒V′)
catchup-lemma (Λ vV′) (⊒Λ {N = blame} pᶜ N⊒V′)
    | nothing =
  ⊥-elim (neutral-source-no-value-target neutral-blame vV′ N⊒V′)
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′)
    | nothing
    with shifted-source-remainder N valueN≡ vV′ N⊒V′
       | catchup-lemma vV′ N⊒V′
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    with storeChangesLastBind χs
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | no-bind keeps =
  ⊥-elim (allKeep-ν-no-value keeps ⇑N↠W vW)
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    with last-bind-empty-target-star
      {χs = χs₀} {A = Aχ} {keeps = keeps}
      keeps-ok Π≡
      (subst (λ Π₀ → Δ′ ⊢ π ꞉ Π ⊒ˢ Π₀) Π′≡ π⊒)
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    with last-bind-empty-target-lowered-tail
      {χs = χs₀} {A = Aχ} {keeps = keeps}
      keeps-ok Π≡
      (subst (λ Π₀ → Δ′ ⊢ π ꞉ Π ⊒ˢ Π₀) Π′≡ π⊒)
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    with ↠-split-last-bind {χs = χs₀} {A = Aχ} {keeps = keeps} ⇑N↠W
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    | P , Q , ⇑N↠P , P→Q , Q↠W
    with nu-source-value-target-base-empty hist
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-nu hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    | P , Q , ⇑N↠P , P→Q , Q↠W
    | nu-base-empty vBase pBaseᶜ bodyBase =
  catchup-⊒Λ-catchup vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    with storeChangesLastBind χs
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | no-bind keeps
    with pure-pred-↠-shifted-value keeps ⇑N↠W vW
       | cast-source-value-target-base-empty hist
       | allKeep-empty-target-nil keeps Π≡ Π′≡ π⊒
       | allKeep-under-binder-value-id keeps vV′
       | allKeep-gen-under-binder-coercion-id keeps pᶜ
       | value-target-source-no-active vV′ N⊒V′
    | value-target-source-safe vV′ N⊒V′
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | no-bind keeps
    | N↠predW
    | cast-base-empty+ vBase pBaseᶜ base≈ bodyBase
    | π≡[]
    | targetUnder≡
    | coercionUnder≡
    | noActive⇑N
    | safe⇑N =
  catchup-⊒Λ-no-bind-shift-image keeps
    (renameᵗᵐ-preserves-Value predᵗ vW)
    N↠predW
    Δ′≡
    π≡[]
    (safe-allKeep-value-image safe⇑N (N , refl) keeps ⇑N↠W vW)
    pᶜ
    W⊒V′
catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | no-bind keeps
    | N↠predW
    | cast-base-empty- vBase pBaseᶜ base≈ bodyBase
    | π≡[]
    | targetUnder≡
    | coercionUnder≡
    | noActive⇑N
    | safe⇑N =
  catchup-⊒Λ-no-bind-shift-image keeps
    (renameᵗᵐ-preserves-Value predᵗ vW)
    N↠predW
    Δ′≡
    π≡[]
    (safe-allKeep-value-image safe⇑N (N , refl) keeps ⇑N↠W vW)
    pᶜ
    W⊒V′
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    with last-bind-empty-target-star
      {χs = χs₀} {A = Aχ} {keeps = keeps}
      keeps-ok Π≡
      (subst (λ Π₀ → Δ′ ⊢ π ꞉ Π ⊒ˢ Π₀) Π′≡ π⊒)
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    with last-bind-empty-target-lowered-tail
      {χs = χs₀} {A = Aχ} {keeps = keeps}
      keeps-ok Π≡
      (subst (λ Π₀ → Δ′ ⊢ π ꞉ Π ⊒ˢ Π₀) Π′≡ π⊒)
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    with ↠-split-last-bind {χs = χs₀} {A = Aχ} {keeps = keeps} ⇑N↠W
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    | P , Q , ⇑N↠P , P→Q , Q↠W
    with cast-source-value-target-base-empty hist
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    | P , Q , ⇑N↠P , P→Q , Q↠W
    | cast-base-empty+ vBase pBaseᶜ base≈ bodyBase =
  catchup-⊒Λ-catchup vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | nothing
    | remainder-cast hist
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | last-bind χs₀ Aχ keeps keeps-ok
    | Aχ≡★
    | π₀ , π≡ , π₀⊒
    | P , Q , ⇑N↠P , P→Q , Q↠W
    | cast-base-empty- vBase pBaseᶜ base≈ bodyBase =
  catchup-⊒Λ-catchup vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
catchup-lemma (vV′ ⟨ i ⟩) (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
    with catchup-lemma (vV′ ⟨ sᵢ ⟩) N⊒V′
catchup-lemma (vV′ ⟨ i ⟩) (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′s =
  catchup-⊒⟨ν⟩-catchup vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ sᵢ W⊒V′s
catchup-lemma () (α⊒α qᶜ pαᶜ L⊒L′)
catchup-lemma () (⊒α pαᶜ L⊒L′)
catchup-lemma () (ν⊒ν pᶜ qᶜ N⊒N′)
catchup-lemma () (⊒ν pᶜ N⊒N′)
catchup-lemma vV (ν⊒ {p = p} pᶜ N⊒V)
    with catchup-lemma (renameᵗᵐ-preserves-Value suc vV) N⊒V
catchup-lemma vV (ν⊒ {p = p} pᶜ N⊒V)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒⇑V =
  catchup-ν⊒-catchup vV vW N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒⇑V
catchup-lemma {Δ = Δ} ($ κ) (κ⊒κ κ) =
  [] , $ κ , Δ , [] , [] , [] ,
  $ κ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  κ⊒κ κ
catchup-lemma () (⊕⊒⊕ M⊒M′ N⊒N′)
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast+ {M′ = M′} {q = q} {s = s} qᶜ q⨟s≈r M⊒M′)
    with catchup-lemma vV′ M⊒M′
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast+ {M′ = M′} {q = q} {s = s} qᶜ q⨟s≈r M⊒M′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  -- Rebuild `⊒cast+` after transporting the side conditions through the
  -- emitted store changes, then rewrite the weakened target cast into the
  -- syntactic shape of `applyTerms χs`.
  χs , W , Δ′ , Π , Π′ , π ,
  vW ,
  M↠W ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  subst
    (λ T → Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ T ∶ applyCoercions χs q)
    (sym (applyTerms-cast-dual χs M′ s))
    (⊒cast+
      (catchup-coercion-typing-transport
        {σ = σ} {π = π} {χs = χs} {p = q}
        qᶜ Δ′≡ Π≡ Π′≡ π⊒)
      (catchup-compose-left-transport
        {σ = σ} {π = π} {χs = χs} {q = q} {s = s}
        q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒)
      W⊒M′)
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast- {M′ = M′} {q = q} {r = r} {s = s}
      qᶜ q⨟s≈r M⊒M′)
    with catchup-lemma vV′ M⊒M′
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast- {M′ = M′} {q = q} {r = r} {s = s}
      qᶜ q⨟s≈r M⊒M′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  -- Same as `⊒cast+`: the recursive narrowing is available, but the cast
  -- typing/equivalence side conditions must be transported to the emitted
  -- Δ′/store-prefix context before `⊒cast-` can be rebuilt.
  χs , W , Δ′ , Π , Π′ , π ,
  vW ,
  M↠W ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  subst
    (λ T → Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ T ∶ applyCoercions χs r)
    (sym (applyTerms-cast χs M′ s))
    (⊒cast-
      (catchup-coercion-typing-transport
        {σ = σ} {π = π} {χs = χs}
        qᶜ Δ′≡ Π≡ Π′≡ π⊒)
      (catchup-compose-left-transport
        {σ = σ} {π = π} {χs = χs} {q = q} {s = s} {r = r}
        q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒)
      W⊒M′)
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    with cast-dual-↠ {c = t} M↠W₁
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | M-t↠W₁-t
    with left-widening-lemma
           {Δ = Δ₁} {σ = combineStoreNrw π₁ σ}
           {p = applyCoercions χs₁ p}
           {r = applyCoercions χs₁ r}
           {t = applyCoercions χs₁ t}
           vW₁
           (catchup-coercion-typing-transport
             {σ = σ} {π = π₁} {χs = χs₁} {p = p}
             pᶜ Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           (catchup-compose-right-transport
             {σ = σ} {π = π₁} {χs = χs₁}
             {r = r} {t = t} {p = p}
             r≈t⨟p Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           W₁⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | M-t↠W₁-t
    | χs₂ , W₂ , Δ₂ , Π₂ , Π₂′ , π₂ ,
      vW₂ , W₁-t↠W₂ , Δ₂≡ , Π₂≡ , Π₂′≡ , π₂⊒ , W₂⊒V =
  -- Catch up `M` to the value `W₁`, lift that reduction through the surrounding
  -- dual cast, invoke the value-level Left Widening Lemma on the transformed
  -- cast, and combine the two emitted source-only store prefixes.
  χs₁ ++ χs₂ , W₂ , Δ₂ ,
  srcStoreⁿ (combineStoreNrw π₂ π₁) , [] ,
  combineStoreNrw π₂ π₁ ,
  vW₂ ,
  ↠-trans M-t↠W₁-t W₁-t↠W₂ ,
  trans Δ₂≡
    (trans (cong (applyTyCtxs χs₂) Δ₁≡)
      (sym (applyTyCtxs-++ χs₁ χs₂ Δ))) ,
  combineStoreNrw-applyStores
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ ,
  refl ,
  combineStoreNrw-empty-⊒ˢ
    (subst (λ Π′ → _ ⊢ π₂ ꞉ _ ⊒ˢ Π′) Π₂′≡ π₂⊒)
    (⊒ˢ-empty-anyᵗ Δ₂
      (subst (λ Π′ → _ ⊢ π₁ ꞉ _ ⊒ˢ Π′) Π₁′≡ π₁⊒)) ,
  subst
    (λ c → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
      ⊢ W₂ ⊒ applyTerms (χs₁ ++ χs₂) V ∶ c)
    (sym (applyCoercions-++ χs₁ χs₂ r))
    (subst
      (λ T → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
        ⊢ W₂ ⊒ T ∶ applyCoercions χs₂ (applyCoercions χs₁ r))
      (sym (applyTerms-++ χs₁ χs₂ V))
      (subst
        (λ τ → Δ₂ ∣ τ ∣ [] ⊢ W₂
          ⊒ applyTerms χs₂ (applyTerms χs₁ V) ∶
            applyCoercions χs₂ (applyCoercions χs₁ r))
        (sym (combineStoreNrw-assoc π₂ π₁ σ))
        W₂⊒V))
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    with cast-↠ {c = t} M↠W₁
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | Mt↠W₁t
    with left-narrowing-lemma
           {Δ = Δ₁} {σ = combineStoreNrw π₁ σ}
           {p = applyCoercions χs₁ p}
           {t = applyCoercions χs₁ t}
           vW₁
           (catchup-coercion-typing-transport
             {σ = σ} {π = π₁} {χs = χs₁} {p = p}
             pᶜ Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           (catchup-compose-right-transport
             {σ = σ} {π = π₁} {χs = χs₁}
             {t = t} {p = p}
             r≈t⨟p Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           W₁⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | Mt↠W₁t
    | χs₂ , W₂ , Δ₂ , Π₂ , Π₂′ , π₂ ,
      vW₂ , W₁t↠W₂ , Δ₂≡ , Π₂≡ , Π₂′≡ , π₂⊒ , W₂⊒V =
  -- Same structure for Left Narrowing: the non-value source is handled by the
  -- recursive catchup call, and the paper lemma is applied only to the caught-up
  -- value, again using the transformed cast and composed source-only prefix.
  χs₁ ++ χs₂ , W₂ , Δ₂ ,
  srcStoreⁿ (combineStoreNrw π₂ π₁) , [] ,
  combineStoreNrw π₂ π₁ ,
  vW₂ ,
  ↠-trans Mt↠W₁t W₁t↠W₂ ,
  trans Δ₂≡
    (trans (cong (applyTyCtxs χs₂) Δ₁≡)
      (sym (applyTyCtxs-++ χs₁ χs₂ Δ))) ,
  combineStoreNrw-applyStores
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ ,
  refl ,
  combineStoreNrw-empty-⊒ˢ
    (subst (λ Π′ → _ ⊢ π₂ ꞉ _ ⊒ˢ Π′) Π₂′≡ π₂⊒)
    (⊒ˢ-empty-anyᵗ Δ₂
      (subst (λ Π′ → _ ⊢ π₁ ꞉ _ ⊒ˢ Π′) Π₁′≡ π₁⊒)) ,
  subst
    (λ c → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
      ⊢ W₂ ⊒ applyTerms (χs₁ ++ χs₂) V ∶ c)
    (sym (applyCoercions-++ χs₁ χs₂ p))
    (subst
      (λ T → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
        ⊢ W₂ ⊒ T ∶ applyCoercions χs₂ (applyCoercions χs₁ p))
      (sym (applyTerms-++ χs₁ χs₂ V))
      (subst
        (λ τ → Δ₂ ∣ τ ∣ [] ⊢ W₂
          ⊒ applyTerms χs₂ (applyTerms χs₁ V) ∶
            applyCoercions χs₂ (applyCoercions χs₁ p))
        (sym (combineStoreNrw-assoc π₂ π₁ σ))
        W₂⊒V))

{-# OPTIONS --allow-unsolved-metas #-}

module proof.MediatedLeftInsertion where

-- File Charter:
--   * Left-insertion weakening of the mediated term-narrowing relation:
--     the machinery behind `left-changes-term-narrowingᵐ` (the ⊒ᵐ
--     replacement of the old postulated `left-change-term-narrowing`).
--   * A left store-change chain `χs` is one renaming of the left type
--     variables (`applyRenᵗ`); applying it `k` binders down is the
--     insertion renaming `insRen χs k`.  `LeftIns χs k ρ ρ′` says ρ′ is
--     ρ with the chain applied k lockstep binders down, and the
--     generalized transport `term-narrowing-insertᵐ` renames the left
--     term and the source endpoint by `insRen χs k` while the index
--     raw, the right term, and everything right-sided stay fixed.
--   * PARTIAL: five constructor cases are hole-bodied because they are
--     UNPROVABLE for the relation as currently stated — they share
--     left-varying syntax with left-invariant positions.  Each hole
--     records its refutation; see also the checklist "Migration step 5"
--     entry.  The other twelve cases and all the machinery are proved.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; subst₂; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Store using (StoreIncl; StoreWfAt)
open import Coercions
open import Primitives using (constTy; constTy-renameᵗ)
open import NarrowWiden using (renameⁿ; _∣_∣_⊢_∶_⊒_)
open import NuTerms
open import NuReduction using
  ( StoreChange; keep; bind; StoreChanges
  ; applyTy; applyTys; applyTyCtx; applyTyCtxs
  ; applyStore; applyStores; applyTerm; applyTerms
  )
open import StoreCorrespondence
open import Mediation
open import TermNarrowingSeparated using
  ( CtxCorrEntry; ctx-entry; CtxCorr; leftCtx; rightCtx; ⇑ᵍᶜ
  ; TermTypingEndpointsᶜ
  )
open import MediatedNarrowing
open import proof.TypeProperties using
  ( TyRenameWf; TyRenameWf-ext; renameᵗ-preserves-WfTy
  ; renameᵗ-id; renameᵗ-compose; renameᵗ-ext-suc-comm
  ; renameStoreᵗ-ext-suc-comm
  )
open import proof.StoreProperties using (∈-renameStoreᵗ; renameStoreᵗ-incl)
open import proof.CoercionProperties using
  ( ModeRename; coercion-weakenᵐ; coercion-renameᵗᵐ
  ; renameᶜ-cong; renameᶜ-compose
  )
open import proof.NuTermProperties using
  ( lookup-map-renameᵗ; map-renameᵗ-⤊
  ; renameᵗᵐ-preserves-Value
  ; renameᵗᵐ-cong; renameᵗᵐ-compose; renameᵗᵐ-ext-suc-comm
  )
open import proof.NarrowWidenProperties using (∈-⟰ᵗ-zero)
import proof.NarrowWidenProperties as NWP
open import proof.CatchupSeparated using
  (applyLeftChange; applyLeftChanges; leftStore-applyLeftChanges)
open import proof.MediationProperties using
  ( narrowing-dual¹-raw
  ; fun-narrow-domain-dualᵐ-determined
  ; rightStore-applyLeftChanges
  )
open import proof.DualRawProperties using (dualRawⁿ-renameᶜ)

------------------------------------------------------------------------
-- The renaming a left store-change chain induces
------------------------------------------------------------------------

-- Each `bind` shifts every pre-existing left type variable by one;
-- `keep` does nothing.  A whole chain is therefore one renaming.
applyRenᵗ : StoreChanges → Renameᵗ
applyRenᵗ [] α = α
applyRenᵗ (keep ∷ χs) α = applyRenᵗ χs α
applyRenᵗ (bind X ∷ χs) α = applyRenᵗ χs (suc α)

-- The same chain seen from k lockstep binders below the change: the k
-- newest variables are untouched, everything older shifts.
insRen : StoreChanges → ℕ → Renameᵗ
insRen χs zero = applyRenᵗ χs
insRen χs (suc k) = extᵗ (insRen χs k)

applyTys-renameᵗ :
  ∀ χs A → applyTys χs A ≡ renameᵗ (applyRenᵗ χs) A
applyTys-renameᵗ [] A = sym (renameᵗ-id A)
applyTys-renameᵗ (keep ∷ χs) A = applyTys-renameᵗ χs A
applyTys-renameᵗ (bind X ∷ χs) A =
  trans (applyTys-renameᵗ χs (⇑ᵗ A))
        (renameᵗ-compose suc (applyRenᵗ χs) A)

------------------------------------------------------------------------
-- Identity renamings for terms and coercions
------------------------------------------------------------------------

extᵗ-id : ∀ (X : TyVar) → extᵗ (λ Y → Y) X ≡ X
extᵗ-id zero = refl
extᵗ-id (suc X) = refl

renameᶜ-id : ∀ c → renameᶜ (λ X → X) c ≡ c
renameᶜ-id (id A) = cong id (renameᵗ-id A)
renameᶜ-id (c ︔ d) = cong₂ _︔_ (renameᶜ-id c) (renameᶜ-id d)
renameᶜ-id (c ↦ d) = cong₂ _↦_ (renameᶜ-id c) (renameᶜ-id d)
renameᶜ-id (`∀ c) =
  cong `∀ (trans (renameᶜ-cong extᵗ-id c) (renameᶜ-id c))
renameᶜ-id (G !) = cong _! (renameᵗ-id G)
renameᶜ-id (G ？) = cong _？ (renameᵗ-id G)
renameᶜ-id (seal A α) = cong (λ A′ → seal A′ α) (renameᵗ-id A)
renameᶜ-id (unseal α A) = cong (unseal α) (renameᵗ-id A)
renameᶜ-id (gen A c) =
  cong₂ gen (renameᵗ-id A)
    (trans (renameᶜ-cong extᵗ-id c) (renameᶜ-id c))
renameᶜ-id (inst B c) =
  cong₂ inst (renameᵗ-id B)
    (trans (renameᶜ-cong extᵗ-id c) (renameᶜ-id c))

renameᵗᵐ-id : ∀ M → renameᵗᵐ (λ X → X) M ≡ M
renameᵗᵐ-id (` x) = refl
renameᵗᵐ-id (ƛ M) = cong ƛ_ (renameᵗᵐ-id M)
renameᵗᵐ-id (L · M) = cong₂ _·_ (renameᵗᵐ-id L) (renameᵗᵐ-id M)
renameᵗᵐ-id (Λ M) =
  cong Λ_ (trans (renameᵗᵐ-cong extᵗ-id M) (renameᵗᵐ-id M))
renameᵗᵐ-id (M •) = cong _• (renameᵗᵐ-id M)
renameᵗᵐ-id (ν A L c) =
  trans
    (cong (λ A′ → ν A′ (renameᵗᵐ (λ X → X) L)
                    (renameᶜ (extᵗ (λ X → X)) c))
      (renameᵗ-id A))
    (trans
      (cong (λ L′ → ν A L′ (renameᶜ (extᵗ (λ X → X)) c))
        (renameᵗᵐ-id L))
      (cong (ν A L)
        (trans (renameᶜ-cong extᵗ-id c) (renameᶜ-id c))))
renameᵗᵐ-id ($ κ) = refl
renameᵗᵐ-id (L ⊕[ op ] M) =
  cong₂ _⊕[ op ]_ (renameᵗᵐ-id L) (renameᵗᵐ-id M)
renameᵗᵐ-id (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵗᵐ-id M) (renameᶜ-id c)
renameᵗᵐ-id blame = refl

applyTerms-renameᵗᵐ :
  ∀ χs M → applyTerms χs M ≡ renameᵗᵐ (applyRenᵗ χs) M
applyTerms-renameᵗᵐ [] M = sym (renameᵗᵐ-id M)
applyTerms-renameᵗᵐ (keep ∷ χs) M = applyTerms-renameᵗᵐ χs M
applyTerms-renameᵗᵐ (bind X ∷ χs) M =
  trans (applyTerms-renameᵗᵐ χs (⇑ᵗᵐ M))
        (renameᵗᵐ-compose suc (applyRenᵗ χs) M)

------------------------------------------------------------------------
-- Context arithmetic for the insertion renaming
------------------------------------------------------------------------

applyTyCtxs-suc :
  ∀ χs Δ → applyTyCtxs χs (suc Δ) ≡ suc (applyTyCtxs χs Δ)
applyTyCtxs-suc [] Δ = refl
applyTyCtxs-suc (keep ∷ χs) Δ = applyTyCtxs-suc χs Δ
applyTyCtxs-suc (bind X ∷ χs) Δ = applyTyCtxs-suc χs (suc Δ)

≤-applyTyCtxs : ∀ χs Δ → Δ ≤ applyTyCtxs χs Δ
≤-applyTyCtxs [] Δ = ≤-refl
≤-applyTyCtxs (keep ∷ χs) Δ = ≤-applyTyCtxs χs Δ
≤-applyTyCtxs (bind X ∷ χs) Δ =
  ≤-trans (n≤1+n Δ) (≤-applyTyCtxs χs (suc Δ))

TyRenameWf-applyRen :
  ∀ χs {Δ} → TyRenameWf Δ (applyTyCtxs χs Δ) (applyRenᵗ χs)
TyRenameWf-applyRen [] lt = lt
TyRenameWf-applyRen (keep ∷ χs) lt = TyRenameWf-applyRen χs lt
TyRenameWf-applyRen (bind X ∷ χs) lt =
  TyRenameWf-applyRen χs (s<s lt)

TyRenameWf-insRen :
  ∀ χs k {Δ} → TyRenameWf Δ (applyTyCtxs χs Δ) (insRen χs k)
TyRenameWf-insRen χs zero = TyRenameWf-applyRen χs
TyRenameWf-insRen χs (suc k) {Δ} {zero} lt =
  <-≤-trans lt (≤-applyTyCtxs χs Δ)
TyRenameWf-insRen χs (suc k) {suc Δ} {suc X} (s<s lt) =
  subst (λ n → suc (insRen χs k X) < n)
    (sym (applyTyCtxs-suc χs Δ))
    (s<s (TyRenameWf-insRen χs k lt))

------------------------------------------------------------------------
-- Mode environments across the insertion renaming
------------------------------------------------------------------------

-- The mode-environment image of a chain: each `bind` reads the old
-- modes one binder down (`instᵈ` agrees with the source on all shifted
-- variables, and its mode for the new seal is irrelevant here).
insModeEnv₀ : StoreChanges → ModeEnv → ModeEnv
insModeEnv₀ [] μ = μ
insModeEnv₀ (keep ∷ χs) μ = insModeEnv₀ χs μ
insModeEnv₀ (bind X ∷ χs) μ = insModeEnv₀ χs (instᵈ μ)

insModeEnv : StoreChanges → ℕ → ModeEnv → ModeEnv
insModeEnv χs zero μ = insModeEnv₀ χs μ
insModeEnv χs (suc k) μ zero = μ zero
insModeEnv χs (suc k) μ (suc Y) = insModeEnv χs k (λ Z → μ (suc Z)) Y

modeRename-applyRen :
  ∀ χs {μ} → ModeRename (applyRenᵗ χs) μ (insModeEnv₀ χs μ)
modeRename-applyRen [] {μ} X = modeIncl-refl {μ = μ} X
modeRename-applyRen (keep ∷ χs) {μ} X =
  modeRename-applyRen χs {μ} X
modeRename-applyRen (bind Y ∷ χs) {μ} X =
  modeRename-applyRen χs {instᵈ μ} (suc X)

modeRename-insRen :
  ∀ χs k {μ} → ModeRename (insRen χs k) μ (insModeEnv χs k μ)
modeRename-insRen χs zero {μ} = modeRename-applyRen χs {μ}
modeRename-insRen χs (suc k) {μ} zero = modeIncl-refl {μ = μ} zero
modeRename-insRen χs (suc k) {μ} (suc X) =
  modeRename-insRen χs k {λ Z → μ (suc Z)} X

------------------------------------------------------------------------
-- Store membership across the insertion renaming
------------------------------------------------------------------------

renameStoreᵗ-id : ∀ Σ → renameStoreᵗ (λ X → X) Σ ≡ Σ
renameStoreᵗ-id [] = refl
renameStoreᵗ-id ((α , A) ∷ Σ) =
  cong₂ _∷_ (cong (α ,_) (renameᵗ-id A)) (renameStoreᵗ-id Σ)

renameStoreᵗ-compose :
  ∀ ρ τ Σ →
  renameStoreᵗ τ (renameStoreᵗ ρ Σ) ≡
    renameStoreᵗ (λ X → τ (ρ X)) Σ
renameStoreᵗ-compose ρ τ [] = refl
renameStoreᵗ-compose ρ τ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong (τ (ρ α) ,_) (renameᵗ-compose ρ τ A))
    (renameStoreᵗ-compose ρ τ Σ)

applyStores-incl :
  ∀ χs Σ →
  StoreIncl (renameStoreᵗ (applyRenᵗ χs) Σ) (applyStores χs Σ)
applyStores-incl [] Σ x∈ =
  subst (λ S → _ ∈ S) (renameStoreᵗ-id Σ) x∈
applyStores-incl (keep ∷ χs) Σ x∈ = applyStores-incl χs Σ x∈
applyStores-incl (bind X ∷ χs) Σ x∈ =
  applyStores-incl χs ((zero , ⇑ᵗ X) ∷ ⟰ᵗ Σ)
    (there
      (subst (λ S → _ ∈ S)
        (sym (renameStoreᵗ-compose suc (applyRenᵗ χs) Σ))
        x∈))

------------------------------------------------------------------------
-- Store-level insertion
------------------------------------------------------------------------

-- The store image of a chain applied k binders down: `si-bind` for a
-- binder that allocates nothing on this side, `si-entry` for one that
-- allocates the head entry.
data StoreIns (χs : StoreChanges) : ℕ → Store → Store → Set where
  si-zero : ∀ {Σ} →
    StoreIns χs zero Σ (applyStores χs Σ)
  si-bind : ∀ {k Σ Σ′} →
    StoreIns χs k Σ Σ′ →
    StoreIns χs (suc k) (⟰ᵗ Σ) (⟰ᵗ Σ′)
  si-entry : ∀ {k Σ Σ′} A →
    StoreIns χs k Σ Σ′ →
    StoreIns χs (suc k)
      ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
      ((zero , ⇑ᵗ (renameᵗ (insRen χs k) A)) ∷ ⟰ᵗ Σ′)

storeIns-incl :
  ∀ {χs k Σ Σ′} →
  StoreIns χs k Σ Σ′ →
  StoreIncl (renameStoreᵗ (insRen χs k) Σ) Σ′
storeIns-incl {χs} (si-zero {Σ = Σ}) = applyStores-incl χs Σ
storeIns-incl {χs} (si-bind {k = k} {Σ = Σ} si) x∈ =
  renameStoreᵗ-incl suc (storeIns-incl si)
    (subst (λ S → _ ∈ S)
      (renameStoreᵗ-ext-suc-comm (insRen χs k) Σ)
      x∈)
storeIns-incl {χs} (si-entry {k = k} {Σ = Σ} A si) (here eq) =
  here
    (trans eq
      (cong (zero ,_) (renameᵗ-ext-suc-comm (insRen χs k) A)))
storeIns-incl {χs} (si-entry {k = k} {Σ = Σ} A si) (there x∈) =
  there
    (renameStoreᵗ-incl suc (storeIns-incl si)
      (subst (λ S → _ ∈ S)
        (renameStoreᵗ-ext-suc-comm (insRen χs k) Σ)
        x∈))

------------------------------------------------------------------------
-- Correspondence-level insertion
------------------------------------------------------------------------

-- ρ′ is ρ with the chain χs applied k lockstep binders down.  The
-- binder constructors mirror the correspondence extensions of the
-- term-relation's binder rules: `li-bind` (Λ⊒Λᵗ), `li-matched`
-- (α⊒αᵗ/ν⊒νᵗ), `li-right` (⊒Λᵗ/⊒⟨ν⟩ᵗ/⊒αᵗ/⊒νᵗ).  Matched entries
-- carry a left type, which renames one binder further out; right-only
-- entries are untouched.
data LeftIns (χs : StoreChanges) : ℕ → SealCorr → SealCorr → Set where
  li-zero : ∀ {ρ} →
    LeftIns χs zero ρ (applyLeftChanges χs ρ)
  li-bind : ∀ {k ρ ρ′} →
    LeftIns χs k ρ ρ′ →
    LeftIns χs (suc k) (⇑ᶜorr ρ) (⇑ᶜorr ρ′)
  li-matched : ∀ {k ρ ρ′} A B →
    LeftIns χs k ρ ρ′ →
    LeftIns χs (suc k)
      (matched zero (⇑ᵗ A) zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ)
      (matched zero (⇑ᵗ (renameᵗ (insRen χs k) A)) zero (⇑ᵗ B)
        ∷ ⇑ᶜorr ρ′)
  li-right : ∀ {k ρ ρ′} B →
    LeftIns χs k ρ ρ′ →
    LeftIns χs (suc k)
      (right-only zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ)
      (right-only zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ′)

-- The right store is untouched by a left insertion.
rightStore-⇑ᶜorr-cong :
  ∀ {ρ ρ′} →
  rightStore ρ′ ≡ rightStore ρ →
  rightStore (⇑ᶜorr ρ′) ≡ rightStore (⇑ᶜorr ρ)
rightStore-⇑ᶜorr-cong {ρ} {ρ′} eq =
  trans (rightStore-⇑ᶜorr ρ′)
    (trans (cong ⟰ᵗ eq) (sym (rightStore-⇑ᶜorr ρ)))

rightStore-insert :
  ∀ {χs k ρ ρ′} →
  LeftIns χs k ρ ρ′ →
  rightStore ρ′ ≡ rightStore ρ
rightStore-insert {χs} (li-zero {ρ = ρ}) =
  rightStore-applyLeftChanges χs ρ
rightStore-insert (li-bind li) =
  rightStore-⇑ᶜorr-cong (rightStore-insert li)
rightStore-insert (li-matched A B li) =
  cong ((zero , ⇑ᵗ B) ∷_)
    (rightStore-⇑ᶜorr-cong (rightStore-insert li))
rightStore-insert (li-right B li) =
  cong ((zero , ⇑ᵗ B) ∷_)
    (rightStore-⇑ᶜorr-cong (rightStore-insert li))

-- The left store of an insertion is a store-level insertion.
storeIns-left :
  ∀ {χs k ρ ρ′} →
  LeftIns χs k ρ ρ′ →
  StoreIns χs k (leftStore ρ) (leftStore ρ′)
storeIns-left {χs} (li-zero {ρ = ρ}) =
  subst (λ Σ → StoreIns χs zero (leftStore ρ) Σ)
    (sym (leftStore-applyLeftChanges χs ρ))
    si-zero
storeIns-left {χs} (li-bind {k = k} {ρ = ρ} {ρ′ = ρ′} li) =
  subst₂ (StoreIns χs (suc k))
    (sym (leftStore-⇑ᶜorr ρ))
    (sym (leftStore-⇑ᶜorr ρ′))
    (si-bind (storeIns-left li))
storeIns-left {χs} (li-matched {k = k} {ρ = ρ} {ρ′ = ρ′} A B li) =
  subst₂ (StoreIns χs (suc k))
    (cong ((zero , ⇑ᵗ A) ∷_) (sym (leftStore-⇑ᶜorr ρ)))
    (cong ((zero , ⇑ᵗ (renameᵗ (insRen χs k) A)) ∷_)
      (sym (leftStore-⇑ᶜorr ρ′)))
    (si-entry A (storeIns-left li))
storeIns-left {χs} (li-right {k = k} {ρ = ρ} {ρ′ = ρ′} B li) =
  subst₂ (StoreIns χs (suc k))
    (sym (leftStore-⇑ᶜorr ρ))
    (sym (leftStore-⇑ᶜorr ρ′))
    (si-bind (storeIns-left li))

------------------------------------------------------------------------
-- MatchedVar across the insertion
------------------------------------------------------------------------

mv-shiftᵇ-inv :
  ∀ ρ {α β} →
  MatchedVar (⇑ᶜorr ρ) α β →
  Σ[ α₀ ∈ TyVar ] Σ[ β₀ ∈ TyVar ]
    ((α ≡ suc α₀) × (β ≡ suc β₀) × MatchedVar ρ α₀ β₀)
mv-shiftᵇ-inv (matched α₀ A β₀ B ∷ ρ) mv-here =
  α₀ , β₀ , refl , refl , mv-here
mv-shiftᵇ-inv (matched α₀ A β₀ B ∷ ρ) (mv-there v)
    with mv-shiftᵇ-inv ρ v
mv-shiftᵇ-inv (matched α₀ A β₀ B ∷ ρ) (mv-there v)
    | α₁ , β₁ , eqα , eqβ , v₀ =
  α₁ , β₁ , eqα , eqβ , mv-there v₀
mv-shiftᵇ-inv (left-only α₀ A ∷ ρ) (mv-there v)
    with mv-shiftᵇ-inv ρ v
mv-shiftᵇ-inv (left-only α₀ A ∷ ρ) (mv-there v)
    | α₁ , β₁ , eqα , eqβ , v₀ =
  α₁ , β₁ , eqα , eqβ , mv-there v₀
mv-shiftᵇ-inv (right-only β₀ B ∷ ρ) (mv-there v)
    with mv-shiftᵇ-inv ρ v
mv-shiftᵇ-inv (right-only β₀ B ∷ ρ) (mv-there v)
    | α₁ , β₁ , eqα , eqβ , v₀ =
  α₁ , β₁ , eqα , eqβ , mv-there v₀

mv-insert₀ :
  ∀ χs {ρ α β} →
  MatchedVar ρ α β →
  MatchedVar (applyLeftChanges χs ρ) (applyRenᵗ χs α) β
mv-insert₀ [] v = v
mv-insert₀ (keep ∷ χs) v = mv-insert₀ χs v
mv-insert₀ (bind X ∷ χs) v = mv-insert₀ χs (mv-left-alloc v)

mv-insert :
  ∀ {χs k ρ ρ′} →
  LeftIns χs k ρ ρ′ →
  ∀ {α β} →
  MatchedVar ρ α β →
  MatchedVar ρ′ (insRen χs k α) β
mv-insert {χs} li-zero v = mv-insert₀ χs v
mv-insert (li-bind {ρ = ρ} li) v
    with mv-shiftᵇ-inv ρ v
mv-insert (li-bind {ρ = ρ} li) v
    | α₀ , β₀ , refl , refl , v₀ =
  mv-shiftᵇ (mv-insert li v₀)
mv-insert (li-matched A B li) mv-here = mv-here
mv-insert (li-matched {ρ = ρ} A B li) (mv-there v)
    with mv-shiftᵇ-inv ρ v
mv-insert (li-matched {ρ = ρ} A B li) (mv-there v)
    | α₀ , β₀ , refl , refl , v₀ =
  mv-there (mv-shiftᵇ (mv-insert li v₀))
mv-insert (li-right {ρ = ρ} B li) (mv-there v)
    with mv-shiftᵇ-inv ρ v
mv-insert (li-right {ρ = ρ} B li) (mv-there v)
    | α₀ , β₀ , refl , refl , v₀ =
  mv-there (mv-shiftᵇ (mv-insert li v₀))

------------------------------------------------------------------------
-- Insertion transport of the mediated coercion judgment
------------------------------------------------------------------------

-- The mediated core: the index raw, its home typing, and the target
-- endpoint are untouched; only the source endpoint and its mediation
-- move.  This is `left-changes-transportᵐ` generalized to arbitrary
-- insertion depth.
narrowing-insertᵐ :
  ∀ {χs k μ ΔL ΔR ρ ρ′ r A B} →
  LeftIns χs k ρ ρ′ →
  StoreCorr (applyTyCtxs χs ΔL) ΔR ρ′ →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B →
  μ ∣ applyTyCtxs χs ΔL ∣ ΔR ∣ ρ′
    ⊢ r ∶ renameᵗ (insRen χs k) A ⊒ᵐ B
narrowing-insertᵐ {χs} {k} {μ = μ} {r = r} {B = B} li corr′
    (corr , wfA , wfB , Aʳ , med , r⊒) =
  corr′ ,
  renameᵗ-preserves-WfTy wfA (TyRenameWf-insRen χs k) ,
  wfB ,
  Aʳ ,
  medTy-mapˡ (insRen χs k) (mv-insert li) med ,
  subst (λ Σ → μ ∣ _ ∣ Σ ⊢ r ∶ Aʳ ⊒ B)
    (sym (rightStore-insert li))
    r⊒

-- One-store left evidence: raw, endpoints, store, and witness all
-- rename together (contrast `narrowing-insertᵐ`).
narrowing-insertˡ :
  ∀ {χs k μ Δ ρ ρ′ s A B} →
  LeftIns χs k ρ ρ′ →
  μ ∣ Δ ∣ leftStore ρ ⊢ s ∶ A ⊒ B →
  insModeEnv χs k μ ∣ applyTyCtxs χs Δ ∣ leftStore ρ′
    ⊢ renameᶜ (insRen χs k) s
    ∶ renameᵗ (insRen χs k) A ⊒ renameᵗ (insRen χs k) B
narrowing-insertˡ {χs} {k} li (s⊢ , sⁿ) =
  coercion-weakenᵐ ≤-refl (storeIns-incl (storeIns-left li))
    (coercion-renameᵗᵐ
      (TyRenameWf-insRen χs k)
      (modeRename-insRen χs k)
      s⊢) ,
  renameⁿ (insRen χs k) sⁿ

-- Composition records cross the insertion field-wise.
comp-tgt-insertᵐ :
  ∀ {χs k ΔL ΔR ρ ρ′ p t r A B} →
  LeftIns χs k ρ ρ′ →
  StoreCorr (applyTyCtxs χs ΔL) ΔR ρ′ →
  ΔL ∣ ΔR ∣ ρ ⊢ p ⨟ʳ t ≈ r ∶ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ ρ′
    ⊢ p ⨟ʳ t ≈ r ∶ renameᵗ (insRen χs k) A ⊒ᵐ B
comp-tgt-insertᵐ {ΔR = ΔR} {t = t} li corr′
    (composed-index-tgt {midTy = midTy} {νᶜᵒᵐᵖ = ν₀} p⊒ t⊒ʳ r⊒) =
  composed-index-tgt
    (narrowing-insertᵐ li corr′ p⊒)
    (subst (λ Σ → ν₀ ∣ ΔR ∣ Σ ⊢ t ∶ midTy ⊒ _)
      (sym (rightStore-insert li))
      t⊒ʳ)
    (narrowing-insertᵐ li corr′ r⊒)

comp-src-insertᵐ :
  ∀ {χs k ΔL ΔR ρ ρ′ s q r A B} →
  LeftIns χs k ρ ρ′ →
  StoreCorr (applyTyCtxs χs ΔL) ΔR ρ′ →
  ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ˡ q ≈ r ∶ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ ρ′
    ⊢ renameᶜ (insRen χs k) s ⨟ˡ q ≈ r
    ∶ renameᵗ (insRen χs k) A ⊒ᵐ B
comp-src-insertᵐ li corr′ (composed-index-src s⊒ˡ q⊒ r⊒) =
  composed-index-src
    (narrowing-insertˡ li s⊒ˡ)
    (narrowing-insertᵐ li corr′ q⊒)
    (narrowing-insertᵐ li corr′ r⊒)

------------------------------------------------------------------------
-- Term-context correspondence across the insertion
------------------------------------------------------------------------

-- Only the left type of an entry moves; the right type and the
-- (home-typed) entry coercion are left-invariant.
insCtxEntry : StoreChanges → ℕ → CtxCorrEntry → CtxCorrEntry
insCtxEntry χs k (ctx-entry A B p) =
  ctx-entry (renameᵗ (insRen χs k) A) B p

insCtx : StoreChanges → ℕ → CtxCorr → CtxCorr
insCtx χs k = map (insCtxEntry χs k)

∋-insCtx :
  ∀ {χs k γ x A B p} →
  γ ∋ x ⦂ ctx-entry A B p →
  insCtx χs k γ ∋ x ⦂ ctx-entry (renameᵗ (insRen χs k) A) B p
∋-insCtx Z = Z
∋-insCtx (S h) = S (∋-insCtx h)

insCtx-⇑ᵍᶜ :
  ∀ χs k γ →
  insCtx χs (suc k) (⇑ᵍᶜ γ) ≡ ⇑ᵍᶜ (insCtx χs k γ)
insCtx-⇑ᵍᶜ χs k [] = refl
insCtx-⇑ᵍᶜ χs k (ctx-entry A B p ∷ γ) =
  cong₂ _∷_
    (cong (λ A′ → ctx-entry A′ (⇑ᵗ B) (⇑ᶜ p))
      (renameᵗ-ext-suc-comm (insRen χs k) A))
    (insCtx-⇑ᵍᶜ χs k γ)

leftCtx-insCtx :
  ∀ χs k γ →
  leftCtx (insCtx χs k γ) ≡ map (renameᵗ (insRen χs k)) (leftCtx γ)
leftCtx-insCtx χs k [] = refl
leftCtx-insCtx χs k (ctx-entry A B p ∷ γ) =
  cong (renameᵗ (insRen χs k) A ∷_) (leftCtx-insCtx χs k γ)

rightCtx-insCtx :
  ∀ χs k γ →
  rightCtx (insCtx χs k γ) ≡ rightCtx γ
rightCtx-insCtx χs k [] = refl
rightCtx-insCtx χs k (ctx-entry A B p ∷ γ) =
  cong (B ∷_) (rightCtx-insCtx χs k γ)

------------------------------------------------------------------------
-- Term typing across the insertion
------------------------------------------------------------------------

typing-insertᵀ :
  ∀ {χs k Δ Σ Σ′ Γ M A} →
  StoreIns χs k Σ Σ′ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  applyTyCtxs χs Δ ∣ Σ′ ∣ map (renameᵗ (insRen χs k)) Γ
    ⊢ renameᵗᵐ (insRen χs k) M ⦂ renameᵗ (insRen χs k) A
typing-insertᵀ si (⊢` h) = ⊢` (lookup-map-renameᵗ h)
typing-insertᵀ {χs} {k} si (⊢ƛ hA hM) =
  ⊢ƛ (renameᵗ-preserves-WfTy hA (TyRenameWf-insRen χs k))
     (typing-insertᵀ si hM)
typing-insertᵀ si (⊢· hL hM) =
  ⊢· (typing-insertᵀ si hL) (typing-insertᵀ si hM)
typing-insertᵀ {χs} {k} {Δ} {Σ′ = Σ′} {Γ = Γ} si
    (⊢Λ {M = M} {A = A} vM hM) =
  ⊢Λ (renameᵗᵐ-preserves-Value (extᵗ (insRen χs k)) vM)
    (subst₂
      (λ Δ″ Γ″ →
        Δ″ ∣ ⟰ᵗ Σ′ ∣ Γ″
          ⊢ renameᵗᵐ (extᵗ (insRen χs k)) M
          ⦂ renameᵗ (extᵗ (insRen χs k)) A)
      (applyTyCtxs-suc χs Δ)
      (map-renameᵗ-⤊ (insRen χs k) Γ)
      (typing-insertᵀ (si-bind si) hM))
-- BLOCKED (recorded 2026-07-06): the ⊢• rule anchors the store HEAD to
-- the •-opened seal and shares Γ verbatim between the premise (at Δ₀)
-- and the conclusion (at suc Δ₀).  A depth-0 insertion puts the new
-- entry ABOVE that head, so the transported term `(⇑ᵗᵐ⇑ᵗᵐ V)•` has no
-- ⊢• derivation at all; at depth ≥ 1 the recursion on V (one binder
-- out, depth k-1) produces the context `map (renameᵗ (insRen χs
-- (k-1))) Γ` while the rule's Γ-sharing demands `map (renameᵗ (insRen
-- χs k)) Γ` — these differ unless Γ's entries are ⇑ᵗ-shifted deeply
-- enough.  A provable version needs either a Γ-provenance invariant
-- for ⊢• or a reshaped rule; see the checklist "Migration step 5".
typing-insertᵀ si (⊢• eqΔ eqΣ hC vV noV hV) =
  {! typing-insertᵀ-⊢•-blocked !}
typing-insertᵀ {χs} {k} {Δ} {Σ = Σ} {Σ′ = Σ′} si
    (⊢ν {L = L} {A = A} {B = B} {C = C} {c = c} {μ = μ} hA hL c⊢) =
  ⊢ν {μ = insModeEnv χs (suc k) μ}
    (renameᵗ-preserves-WfTy hA (TyRenameWf-insRen χs k))
    (typing-insertᵀ si hL)
    (subst
      (λ T →
        insModeEnv χs (suc k) μ ∣ suc (applyTyCtxs χs Δ)
          ∣ (zero , ⇑ᵗ (renameᵗ (insRen χs k) A)) ∷ ⟰ᵗ Σ′
          ⊢ renameᶜ (extᵗ (insRen χs k)) c
          ∶ renameᵗ (extᵗ (insRen χs k)) C =⇒ T)
      (renameᵗ-ext-suc-comm (insRen χs k) B)
      (coercion-weakenᵐ ≤-refl
        (storeIns-incl (si-entry A si))
        (subst
          (λ Δ″ →
            insModeEnv χs (suc k) μ ∣ Δ″
              ∣ renameStoreᵗ (extᵗ (insRen χs k))
                  ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
              ⊢ renameᶜ (extᵗ (insRen χs k)) c
              ∶ renameᵗ (extᵗ (insRen χs k)) C
              =⇒ renameᵗ (extᵗ (insRen χs k)) (⇑ᵗ B))
          (applyTyCtxs-suc χs Δ)
          (coercion-renameᵗᵐ
            (TyRenameWf-insRen χs (suc k))
            (modeRename-insRen χs (suc k))
            c⊢))))
typing-insertᵀ {χs} {k} si (⊢$ κ) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ $ κ ⦂ T)
    (constTy-renameᵗ (insRen χs k) κ)
    (⊢$ κ)
typing-insertᵀ si (⊢⊕ hL op hM) =
  ⊢⊕ (typing-insertᵀ si hL) op (typing-insertᵀ si hM)
typing-insertᵀ {χs} {k} si (⊢⟨⟩ {μ = μ} c⊢ hM) =
  ⊢⟨⟩ {μ = insModeEnv χs k μ}
    (coercion-weakenᵐ ≤-refl (storeIns-incl si)
      (coercion-renameᵗᵐ
        (TyRenameWf-insRen χs k)
        (modeRename-insRen χs k)
        c⊢))
    (typing-insertᵀ si hM)
typing-insertᵀ {χs} {k} si (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA (TyRenameWf-insRen χs k))

------------------------------------------------------------------------
-- StoreCorr extension helpers
------------------------------------------------------------------------

-- The lockstep-binder extension of the transported correspondence.
corr-bind-insert :
  ∀ {χs ΔL ΔR ρ′} →
  StoreCorr (applyTyCtxs χs ΔL) ΔR ρ′ →
  StoreCorr (applyTyCtxs χs (suc ΔL)) (suc ΔR) (⇑ᶜorr ρ′)
corr-bind-insert {χs} {ΔL} {ΔR} {ρ′} corr′ =
  subst (λ Δ → StoreCorr Δ (suc ΔR) (⇑ᶜorr ρ′))
    (sym (applyTyCtxs-suc χs ΔL))
    (corr-⇑ᶜorr corr′)

-- The right-only extension (⊒νᵗ-shaped), with the head entry's
-- well-formedness facts supplied by the caller (extracted from the
-- original derivation's packages).
corr-right-insert :
  ∀ {χs ΔL ΔR ρ′ A} →
  WfTy (suc ΔR) (⇑ᵗ A) →
  WfTy zero (⇑ᵗ A) →
  StoreCorr (applyTyCtxs χs ΔL) ΔR ρ′ →
  StoreCorr (applyTyCtxs χs (suc ΔL)) (suc ΔR)
    (right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ′)
corr-right-insert {χs} {ΔL} {ΔR} {ρ′} {A} wfA-R wfA-0 corr′ =
  subst
    (λ Δ →
      StoreCorr Δ (suc ΔR) (right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ′))
    (sym (applyTyCtxs-suc χs ΔL))
    (corr-right z<s wfA-R wfA-0 uniq (corr-⇑ᶜorr corr′))
  where
  uniq : ∀ {D} → (zero , D) ∈ rightStore (⇑ᶜorr ρ′) → ⇑ᵗ A ≡ D
  uniq {D} mem =
    ⊥-elim
      (∈-⟰ᵗ-zero
        (subst (λ Σ → (zero , D) ∈ Σ) (rightStore-⇑ᶜorr ρ′) mem))

------------------------------------------------------------------------
-- The generalized term-relation transport
------------------------------------------------------------------------

-- Insertion weakening of the mediated term relation: the left term and
-- the source endpoint rename by `insRen χs k`; the index raw, the
-- right term, and the target endpoint are untouched.
--
-- PARTIAL — five constructor cases are hole-bodied because the
-- statement is UNPROVABLE for them as the relation stands (each hole
-- records its refutation).  The failures share one root cause: those
-- constructors tie left-varying syntax to left-invariant positions.
term-narrowing-insertᵐ :
  ∀ {χs k ΔL ΔR ρ ρ′ γ M M′ p A B} →
  LeftIns χs k ρ ρ′ →
  StoreCorr (applyTyCtxs χs ΔL) ΔR ρ′ →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ ρ′ ∣ insCtx χs k γ
    ⊢ renameᵗᵐ (insRen χs k) M ⊒ M′ ∶ p
    ⦂ renameᵗ (insRen χs k) A ⊒ᵐ B

term-narrowing-insertᵐ {χs} {k} {γ = γ} li corr′ (⊒blameᵗ M⊢ p⊒) =
  ⊒blameᵗ
    (subst (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
      (sym (leftCtx-insCtx χs k γ))
      (typing-insertᵀ (storeIns-left li) M⊢))
    (narrowing-insertᵐ li corr′ p⊒)

term-narrowing-insertᵐ li corr′ (x⊒xᵗ pᶜ x∋p) =
  x⊒xᵗ (narrowing-insertᵐ li corr′ pᶜ) (∋-insCtx x∋p)

term-narrowing-insertᵐ {χs} {k} {ρ′ = ρ′} {γ = γ} li corr′
    (ƛ⊒ƛᵗ {N = N} {N′ = N′} {p = p} {q = q}
      {A = A} {A′ = A′} {B = B} {B′ = B′} p↦qᶜ N⊒N′) =
  ƛ⊒ƛᵗ p↦qᶜ₊
    (subst
      (λ c →
        _ ∣ _ ∣ ρ′ ∣ ctx-entry (renameᵗ (insRen χs k) A) A′ c
            ∷ insCtx χs k γ
          ⊢ renameᵗᵐ (insRen χs k) N ⊒ N′ ∶ q
          ⦂ renameᵗ (insRen χs k) B ⊒ᵐ B′)
      (fun-narrow-domain-dualᵐ-determined p↦qᶜ p↦qᶜ₊)
      (term-narrowing-insertᵐ li corr′ N⊒N′))
  where
  p↦qᶜ₊ = narrowing-insertᵐ li corr′ p↦qᶜ

term-narrowing-insertᵐ {χs} {k} {ρ′ = ρ′} {γ = γ} li corr′
    (·⊒·ᵗ {M = M} {M′ = M′} {A = A} {A′ = A′} p↦qᶜ L⊒L′ M⊒M′) =
  ·⊒·ᵗ p↦qᶜ₊
    (term-narrowing-insertᵐ li corr′ L⊒L′)
    (subst
      (λ c →
        _ ∣ _ ∣ ρ′ ∣ insCtx χs k γ
          ⊢ renameᵗᵐ (insRen χs k) M ⊒ M′ ∶ c
          ⦂ renameᵗ (insRen χs k) A ⊒ᵐ A′)
      (fun-narrow-domain-dualᵐ-determined p↦qᶜ p↦qᶜ₊)
      (term-narrowing-insertᵐ li corr′ M⊒M′))
  where
  p↦qᶜ₊ = narrowing-insertᵐ li corr′ p↦qᶜ

term-narrowing-insertᵐ {χs} {k} {ΔL} {ΔR} {ρ′ = ρ′} {γ = γ}
    li corr′
    (Λ⊒Λᵗ {V = V} {V′ = V′} {p = p} {A = A} {B = B}
      allᶜ vV vV′ V⊒V′) =
  Λ⊒Λᵗ
    (narrowing-insertᵐ li corr′ allᶜ)
    (renameᵗᵐ-preserves-Value (extᵗ (insRen χs k)) vV)
    vV′
    (subst₂
      (λ Δ″ γ″ →
        Δ″ ∣ suc ΔR ∣ ⇑ᶜorr ρ′ ∣ γ″
          ⊢ renameᵗᵐ (extᵗ (insRen χs k)) V ⊒ V′ ∶ p
          ⦂ renameᵗ (extᵗ (insRen χs k)) A ⊒ᵐ B)
      (applyTyCtxs-suc χs ΔL)
      (insCtx-⇑ᵍᶜ χs k γ)
      (term-narrowing-insertᵐ (li-bind li)
        (corr-bind-insert corr′)
        V⊒V′))

-- BLOCKED (recorded 2026-07-06): the conclusion index `gen A p`
-- embeds the LEFT endpoint A.  The ∶ᶜ premise's home typing
-- (cast-gen) forces the raw's embedded type to be the mediated image
-- Aʳ, and forces Aʳ ≡ A — self-mediation.  Under a left insertion the
-- endpoint becomes `renameᵗ (insRen χs k) A` while the index must stay
-- `gen A p`; rebuilding via ⊒Λᵗ yields index `gen A₊ p` instead, and
-- no other constructor can conclude at a Λ right term with a
-- gen-shaped index.  Counterexample shape: N = ` x, A = ＇ 0 at
-- ρ = matched 0 ★ 0 ★ ∷ [] and χs = bind X ∷ [] — the transported
-- instance is underivable.  Fix requires decoupling the raw's embedded
-- type from the source endpoint (state the premise at `gen Aʳ p`).
term-narrowing-insertᵐ li corr′ (⊒Λᵗ typing genᶜ N⊒V′) =
  {! ⊒Λᵗ-insert-blocked !}

-- BLOCKED (recorded 2026-07-06): as ⊒Λᵗ, and additionally the RIGHT
-- term `V′ ⟨ gen A s ⟩` embeds the left endpoint A, so even a
-- reshaped index leaves the (left-invariant) right term stale.
term-narrowing-insertᵐ li corr′ (⊒⟨ν⟩ᵗ typing genᶜ i N⊒V′s) =
  {! ⊒⟨ν⟩ᵗ-insert-blocked !}

-- BLOCKED (recorded 2026-07-06): the α⊒αᵗ conclusion anchors the
-- matched entry at position ZERO of the correspondence and its left
-- term is `(⇑ᵗᵐ L) •`, whose ⊢• typing anchors the left store HEAD.
-- A depth-0 insertion (li-zero) puts the new left-only entry above
-- both anchors, and no constructor can rebuild the pair
-- ((⇑ᵗᵐ⇑ᵗᵐL) • , (⇑ᵗᵐL′) •) at a left-only-headed correspondence.
-- At depth ≥ 1 the case would go through the li-matched extension,
-- but the ⊢•-typing transport is itself blocked (see typing-insertᵀ).
term-narrowing-insertᵐ li corr′ (α⊒αᵗ γ′≡ typing qᶜ pᶜ L⊒L′) =
  {! α⊒αᵗ-insert-blocked !}

-- BLOCKED (recorded 2026-07-06): as α⊒αᵗ — the conclusion anchors a
-- right-only entry at position zero (broken by a depth-0 insertion,
-- which yields a left-only head) and the right term `(⇑ᵗᵐ L′) •`
-- cannot be rebuilt by any other constructor; the left typing field
-- also crosses ⊢•.
term-narrowing-insertᵐ li corr′ (⊒αᵗ γ′≡ typing pᶜ L⊒L′) =
  {! ⊒αᵗ-insert-blocked !}

-- BLOCKED (recorded 2026-07-06): ν⊒νᵗ shares ONE raw between the left
-- term, the right term, and the index: both terms embed `⇑ᶜ p` where
-- p is the (home-typed, left-invariant) index.  The left term renames
-- to `ν A₊ N₊ (⇑ᶜ (renameᶜ (insRen χs k) p))` while the right term
-- keeps `⇑ᶜ p`, and ν⊒νᵗ forces the two embedded raws to coincide
-- with ⇑ᶜ of the index — impossible whenever p mentions a shifted
-- variable (e.g. p = id (＇ β)).  ⊒νᵗ cannot rescue the pair: it
-- would need the shifted whole left ν-term related to the body N′,
-- and there is no left-only-ν introduction rule.  Fix requires the
-- left term to embed its own left-typed raw (as the cast rules do via
-- `narrowing-dual¹`), related to the index by mediation rather than
-- syntactic identity.
term-narrowing-insertᵐ li corr′ (ν⊒νᵗ typing pᶜ qᶜ N⊒N′) =
  {! ν⊒νᵗ-insert-blocked !}

term-narrowing-insertᵐ {χs} {k} {ΔL} {ΔR} {ρ = ρ} {ρ′ = ρ′} {γ = γ}
    li corr′
    (⊒νᵗ {A = A} {B = B} {B′ = B′} {N = N} {N′ = N′} {p = p}
      typing pᶜ N⊒N′) =
  ⊒νᵗ
    ( subst (λ Γ → _ ∣ _ ∣ Γ ⊢ renameᵗᵐ (insRen χs k) N ⦂ _)
        (sym (leftCtx-insCtx χs k γ))
        (typing-insertᵀ (storeIns-left li) (proj₁ typing))
    , subst₂
        (λ Σ Γ → ΔR ∣ Σ ∣ Γ ⊢ ν A N′ (⇑ᶜ p) ⦂ B′)
        (sym (rightStore-insert li))
        (sym (rightCtx-insCtx χs k γ))
        (proj₂ typing) )
    (narrowing-insertᵐ li corr′ pᶜ)
    sub₊
  where
  pkg₀ = typed-term-narrowing-coercionᵐ N⊒N′

  corr₀ :
    StoreCorr (suc ΔL) (suc ΔR) (right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ)
  corr₀ = proj₁ (proj₂ pkg₀)

  corrExt :
    StoreCorr (applyTyCtxs χs (suc ΔL)) (suc ΔR)
      (right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ′)
  corrExt =
    corr-right-insert
      (StoreWfAt.wfTy (rightStore-wf corr₀) (here refl))
      (NWP.StoreDetWf.wfOlder (rightStore-det corr₀) (here refl))
      corr′

  sub₊ :
    suc (applyTyCtxs χs ΔL) ∣ suc ΔR
      ∣ right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ′
      ∣ ⇑ᵍᶜ (insCtx χs k γ)
      ⊢ ⇑ᵗᵐ (renameᵗᵐ (insRen χs k) N) ⊒ N′ ∶ ⇑ᶜ p
      ⦂ ⇑ᵗ (renameᵗ (insRen χs k) B) ⊒ᵐ ⇑ᵗ B′
  sub₊ =
    subst₂
      (λ Δ″ γ″ →
        Δ″ ∣ suc ΔR ∣ right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ′ ∣ γ″
          ⊢ ⇑ᵗᵐ (renameᵗᵐ (insRen χs k) N) ⊒ N′ ∶ ⇑ᶜ p
          ⦂ ⇑ᵗ (renameᵗ (insRen χs k) B) ⊒ᵐ ⇑ᵗ B′)
      (applyTyCtxs-suc χs ΔL)
      (insCtx-⇑ᵍᶜ χs k γ)
      (subst₂
        (λ N″ T →
          applyTyCtxs χs (suc ΔL) ∣ suc ΔR
            ∣ right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ′
            ∣ insCtx χs (suc k) (⇑ᵍᶜ γ)
            ⊢ N″ ⊒ N′ ∶ ⇑ᶜ p ⦂ T ⊒ᵐ ⇑ᵗ B′)
        (renameᵗᵐ-ext-suc-comm (insRen χs k) N)
        (renameᵗ-ext-suc-comm (insRen χs k) B)
        (term-narrowing-insertᵐ (li-right A li) corrExt N⊒N′))

term-narrowing-insertᵐ {χs} {k} li corr′ (κ⊒κᵗ κ pᶜ) =
  subst
    (λ T → _ ∣ _ ∣ _ ∣ _ ⊢ $ κ ⊒ $ κ ∶ id (constTy κ)
      ⦂ T ⊒ᵐ constTy κ)
    (constTy-renameᵗ (insRen χs k) κ)
    (κ⊒κᵗ κ
      (subst
        (λ T → _ ∣ _ ∣ _ ⊢ id (constTy κ) ∶ᶜ T ⊒ᵐ constTy κ)
        (sym (constTy-renameᵗ (insRen χs k) κ))
        (narrowing-insertᵐ li corr′ pᶜ)))

term-narrowing-insertᵐ li corr′ (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′) =
  ⊕⊒⊕ᵗ (narrowing-insertᵐ li corr′ pᶜ)
    (term-narrowing-insertᵐ li corr′ M⊒M′)
    (term-narrowing-insertᵐ li corr′ N⊒N′)

term-narrowing-insertᵐ {χs} {k} {ΔR = ΔR} {ρ′ = ρ′} {γ = γ}
    li corr′
    (⊒cast+ᵗ {M = M} {M′ = M′} {p = p} {t = t}
      {A = A} {B = B} {C = C} {η = η} pᶜ r⊒ t⊒ʳ comp M⊒M′) =
  subst
    (λ c →
      _ ∣ _ ∣ ρ′ ∣ insCtx χs k γ
        ⊢ renameᵗᵐ (insRen χs k) M ⊒ M′ ⟨ c ⟩ ∶ p
        ⦂ renameᵗ (insRen χs k) A ⊒ᵐ C)
    (trans (narrowing-dual¹-raw t⊒ʳ₊)
      (sym (narrowing-dual¹-raw t⊒ʳ)))
    (⊒cast+ᵗ
      (narrowing-insertᵐ li corr′ pᶜ)
      (narrowing-insertᵐ li corr′ r⊒)
      t⊒ʳ₊
      (comp-tgt-insertᵐ li corr′ comp)
      (term-narrowing-insertᵐ li corr′ M⊒M′))
  where
  t⊒ʳ₊ : _ ∣ ΔR ∣ rightStore ρ′ ⊢ t ∶ C ⊒ B
  t⊒ʳ₊ =
    subst (λ Σ → η ∣ ΔR ∣ Σ ⊢ t ∶ C ⊒ B)
      (sym (rightStore-insert li))
      t⊒ʳ

term-narrowing-insertᵐ {ΔR = ΔR} {ρ′ = ρ′} li corr′
    (⊒cast-ᵗ {t = t} {B = B} {C = C} {η = η}
      pᶜ r⊒ t⊒ʳ comp M⊒M′) =
  ⊒cast-ᵗ
    (narrowing-insertᵐ li corr′ pᶜ)
    (narrowing-insertᵐ li corr′ r⊒)
    (subst (λ Σ → η ∣ ΔR ∣ Σ ⊢ t ∶ C ⊒ B)
      (sym (rightStore-insert li))
      t⊒ʳ)
    (comp-tgt-insertᵐ li corr′ comp)
    (term-narrowing-insertᵐ li corr′ M⊒M′)

term-narrowing-insertᵐ {χs} {k} {ρ′ = ρ′} {γ = γ} li corr′
    (cast+⊒ᵗ {M = M} {M′ = M′} {r = r} {s = s}
      {A = A} {B = B} {C = C} qᶜ r⊒ s⊒ˡ comp M⊒M′) =
  subst
    (λ c →
      _ ∣ _ ∣ ρ′ ∣ insCtx χs k γ
        ⊢ renameᵗᵐ (insRen χs k) M ⟨ c ⟩ ⊒ M′ ∶ r
        ⦂ renameᵗ (insRen χs k) A ⊒ᵐ B)
    dual-eq
    (cast+⊒ᵗ
      (narrowing-insertᵐ li corr′ qᶜ)
      (narrowing-insertᵐ li corr′ r⊒)
      s⊒ˡ₊
      (comp-src-insertᵐ li corr′ comp)
      (term-narrowing-insertᵐ li corr′ M⊒M′))
  where
  s⊒ˡ₊ = narrowing-insertˡ li s⊒ˡ

  dual-eq :
    narrowing-dual¹ s⊒ˡ₊ ≡
      renameᶜ (insRen χs k) (narrowing-dual¹ s⊒ˡ)
  dual-eq =
    trans (narrowing-dual¹-raw s⊒ˡ₊)
      (trans
        (dualRawⁿ-renameᶜ (insRen χs k) normalᵃ normalᵃ
          (λ α → refl) s)
        (cong (renameᶜ (insRen χs k))
          (sym (narrowing-dual¹-raw s⊒ˡ))))

term-narrowing-insertᵐ li corr′
    (cast-⊒ᵗ qᶜ r⊒ s⊒ˡ comp M⊒M′) =
  cast-⊒ᵗ
    (narrowing-insertᵐ li corr′ qᶜ)
    (narrowing-insertᵐ li corr′ r⊒)
    (narrowing-insertˡ li s⊒ˡ)
    (comp-src-insertᵐ li corr′ comp)
    (term-narrowing-insertᵐ li corr′ M⊒M′)

------------------------------------------------------------------------
-- The whole-chain transport
------------------------------------------------------------------------

-- The mediated term-relation transport across left store changes: the
-- ⊒ᵐ replacement for the old postulated `left-change-term-narrowing`.
-- The index raw `p` is untouched — the point of the mediated design.
-- Inherits the five documented holes of `term-narrowing-insertᵐ`.
left-changes-term-narrowingᵐ :
  ∀ χs {ΔL ΔR ρ M M′ p A B} →
  StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
    ⊢ applyTerms χs M ⊒ M′ ∶ p ⦂ applyTys χs A ⊒ᵐ B
left-changes-term-narrowingᵐ χs {M = M} {M′ = M′} {p = p} {A = A}
    corr M⊒M′ =
  subst₂
    (λ N T → _ ∣ _ ∣ _ ∣ [] ⊢ N ⊒ M′ ∶ p ⦂ T ⊒ᵐ _)
    (sym (applyTerms-renameᵗᵐ χs M))
    (sym (applyTys-renameᵗ χs A))
    (term-narrowing-insertᵐ li-zero corr M⊒M′)

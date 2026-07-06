{-# OPTIONS --allow-unsolved-metas #-}

module proof.MediationProperties where

-- File Charter:
--   * Store-typing properties of the mediated judgment: its
--     store-change transports, the one-store and composition-record
--     arrow projections, and the left-change transport family.
--   * Holes: the one-store left-change transports (base-language
--     lemmas, independent of mediation), the mediated term-relation
--     left-change transport, and the one-store weakening used by the
--     home-side allocation transport.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc; _<_; s≤s; z≤n)
open import Data.List using ([]; _∷_)
open import Data.Product using
  (_×_; _,_; proj₁; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans)

open import Types
open import Coercions
open import Store using (StoreWfAt)
open import NarrowWiden using
  ( cross
  ; dualʷ
  ; _∣_∣_⊢_∶_⊒_
  )
  renaming (_↦_ to _↦ⁿʷ_)
open import NuReduction using
  (StoreChange; keep; bind; StoreChanges;
   applyTy; applyTys; applyTyCtx; applyTyCtxs; applyCoercion;
   applyStores; applyTerms)
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.TypeProperties using (predᵗ)
open import proof.CoercionProperties using
  ( dualActionOk-normal
  ; dualStoreAt-normal
  )
open import proof.NarrowWidenProperties using
  ( dualʷ-flips-typingᵐ
  )
open import proof.ReductionProperties using (applyCoercions)
open import proof.CatchupSeparated using
  ( applyLeftChange
  ; applyLeftChanges
  ; applyRightChange
  ; rightStore-applyLeftChange
  ; leftStore-applyLeftChanges
  )
open import proof.LeftChangeNarrowingSeparated using
  ( dualʷ-raw-determined
  )

------------------------------------------------------------------------
-- Store-change transports of the mediated judgment
------------------------------------------------------------------------

wfTy-⇑ : ∀ {Δ A} → WfTy Δ A → WfTy (suc Δ) (⇑ᵗ A)
wfTy-⇑ = go suc (λ x<Δ → s≤s x<Δ)
  where
  go :
    ∀ {Δ Δ′} (r : Renameᵗ) →
    (∀ {X} → X < Δ → r X < Δ′) →
    ∀ {A} → WfTy Δ A → WfTy Δ′ (renameᵗ r A)
  go r k (wfVar lt) = wfVar (k lt)
  go r k wfBase = wfBase
  go r k wf★ = wf★
  go r k (wf⇒ a b) = wf⇒ (go r k a) (go r k b)
  go r k (wf∀ a) =
    wf∀ (go (extᵗ r) k′ a)
    where
    k′ : ∀ {X} → X < _ → extᵗ r X < _
    k′ {zero} lt = s≤s z≤n
    k′ {suc X} (s≤s lt) = s≤s (k lt)

-- Non-home (left) store allocation: the home raw, its typing, and its
-- endpoints are untouched; only the mediation and the source endpoint
-- move.  The shared-raw analogue of this statement is what the
-- left-change postulate family could not have.
left-alloc-transportᵐ :
  ∀ {μ ΔL ΔR ρ r A B X} →
  StoreCorr (suc ΔL) ΔR (left-only zero (⇑ᵗ X) ∷ ⇑ˡᶜorr ρ) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B →
  μ ∣ suc ΔL ∣ ΔR ∣ (left-only zero (⇑ᵗ X) ∷ ⇑ˡᶜorr ρ)
    ⊢ r ∶ ⇑ᵗ A ⊒ᵐ B
left-alloc-transportᵐ {ρ = ρ} {r = r} {B = B}
    corr′ (corr , wfA , wfB , Aʳ , med , r⊒) =
  corr′ ,
  wfTy-⇑ wfA ,
  wfB ,
  Aʳ ,
  medTy-mapˡ suc mv-left-alloc med ,
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ r ∶ Aʳ ⊒ B)
    (sym (rightStore-⇑ˡᶜorr ρ))
    r⊒

-- Home (right) store allocation: the home raw and its endpoints shift
-- together with the home store, exactly as ξ-⟨⟩ rewrites the coercion
-- it steps under.  The mediation side is proved; the one-store
-- weakening of the home typing is a base-language lemma.
right-alloc-transportᵐ :
  ∀ {μ ΔL ΔR ρ r A B X} →
  StoreCorr ΔL (suc ΔR) (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B →
  instᵈ μ ∣ ΔL ∣ suc ΔR ∣ (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ)
    ⊢ ⇑ᶜ r ∶ A ⊒ᵐ ⇑ᵗ B
right-alloc-transportᵐ {μ = μ} {ρ = ρ} {r = r} {A = A} {B = B} {X = X}
    corr′ (corr , wfA , wfB , Aʳ , med , r⊒) =
  corr′ ,
  wfA ,
  wfTy-⇑ wfB ,
  ⇑ᵗ Aʳ ,
  medTy-mapʳ suc mv-right-alloc med ,
  {! right-store-shift-weakening !}
  -- needed:
  --   instᵈ μ ∣ suc ΔR ∣ (0 , ⇑ᵗ X) ∷ ⟰ᵗ (rightStore ρ)
  --     ⊢ ⇑ᶜ r ∶ ⇑ᵗ Aʳ ⊒ ⇑ᵗ B
  -- from r⊒ : μ ∣ ΔR ∣ rightStore ρ ⊢ r ∶ Aʳ ⊒ B, modulo
  -- rightStore (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ) ≡
  --   (0 , ⇑ᵗ X) ∷ ⟰ᵗ (rightStore ρ)  (rightStore-⇑ʳᶜorr).
  -- Ordinary one-store weakening in the base language, independent of
  -- the mediation design.

------------------------------------------------------------------------
-- The mediated left-change family
------------------------------------------------------------------------

-- These are the ⊒ᵐ replacements for the postulated `left-change-*`
-- transports of the old two-store judgment.  The decisive difference:
-- the index raw is typed against the right store only, so a source
-- store change never touches it — the transport is component-wise and
-- needs no intermediate store correspondences, only the final one for
-- the output package.

wfTy-applyTys :
  ∀ χs {Δ A} → WfTy Δ A → WfTy (applyTyCtxs χs Δ) (applyTys χs A)
wfTy-applyTys [] wf = wf
wfTy-applyTys (keep ∷ χs) wf = wfTy-applyTys χs wf
wfTy-applyTys (bind X ∷ χs) wf = wfTy-applyTys χs (wfTy-⇑ wf)

medTy-applyLeftChanges :
  ∀ χs {ρ A Aʳ} →
  MedTy (MatchedVar ρ) A Aʳ →
  MedTy (MatchedVar (applyLeftChanges χs ρ)) (applyTys χs A) Aʳ
medTy-applyLeftChanges [] med = med
medTy-applyLeftChanges (keep ∷ χs) med =
  medTy-applyLeftChanges χs med
medTy-applyLeftChanges (bind X ∷ χs) med =
  medTy-applyLeftChanges χs (medTy-mapˡ suc mv-left-alloc med)

rightStore-applyLeftChanges :
  ∀ χs ρ →
  rightStore (applyLeftChanges χs ρ) ≡ rightStore ρ
rightStore-applyLeftChanges [] ρ = refl
rightStore-applyLeftChanges (χ ∷ χs) ρ =
  trans
    (rightStore-applyLeftChanges χs (applyLeftChange χ ρ))
    (rightStore-applyLeftChange χ ρ)

-- The whole-chain transport: raw untouched, target endpoint
-- untouched, source endpoint and mediation move with the source
-- store.  Compare `left-change-coercion-narrowing` (postulated, old
-- judgment), whose conclusion had to rewrite the raw to
-- `applyCoercions χs c`.
left-changes-transportᵐ :
  ∀ χs {μ ΔL ΔR ρ r A B} →
  StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B →
  μ ∣ applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
    ⊢ r ∶ applyTys χs A ⊒ᵐ B
left-changes-transportᵐ χs {ρ = ρ} {r = r} {B = B}
    corr′ (corr , wfA , wfB , Aʳ , med , r⊒) =
  corr′ ,
  wfTy-applyTys χs wfA ,
  wfB ,
  Aʳ ,
  medTy-applyLeftChanges χs med ,
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ r ∶ Aʳ ⊒ B)
    (sym (rightStore-applyLeftChanges χs ρ))
    r⊒

-- The single-target-change transport (the shape the DGG theorem's χ′
-- introduces): `keep` is the identity, `bind` is the home-side
-- allocation.
right-change-transportᵐ :
  ∀ χ′ {μ ΔL ΔR ρ r A B} →
  StoreCorr ΔL (applyTyCtx χ′ ΔR) (applyRightChange χ′ ρ) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B →
  ∃[ μ′ ]
    μ′ ∣ ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ
      ⊢ applyCoercion χ′ r ∶ A ⊒ᵐ applyTy χ′ B
right-change-transportᵐ keep {μ = μ}
    corr′ (corr , wfA , wfB , Aʳ , med , r⊒) =
  μ , (corr′ , wfA , wfB , Aʳ , med , r⊒)
right-change-transportᵐ (bind X) {μ = μ} corr′ ev =
  instᵈ μ , right-alloc-transportᵐ corr′ ev

------------------------------------------------------------------------
-- One-store left transports (source-cast evidence)
------------------------------------------------------------------------

-- The deterministic mode-environment image of a store change: `bind`
-- shifts the store, so the modes of the old variables are read one
-- binder down (this is the mode `applyCoercion-typing` produces).
-- Exposed as a function so the three factors of a transported
-- composition record stay at ONE shared mode environment.
applyModeEnv : StoreChange → ModeEnv → ModeEnv
applyModeEnv keep μ = μ
applyModeEnv (bind A) μ = λ Y → μ (predᵗ Y)

applyModeEnvs : StoreChanges → ModeEnv → ModeEnv
applyModeEnvs [] μ = μ
applyModeEnvs (χ ∷ χs) μ = applyModeEnvs χs (applyModeEnv χ μ)

-- One-store transport of a left-store narrowing judgment across
-- emitted left store changes: raw, endpoints, and store shift
-- together (contrast `left-changes-transportᵐ`, where the home raw
-- is untouched).  Base-language plumbing — `applyCoercion-typing`
-- shapes plus the `renameⁿ` witness renaming; hole-bodied pending
-- the store-wf chaining question recorded in the checklist.
left-changes-narrowingˡ :
  ∀ χs {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  applyModeEnvs χs μ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
    ⊢ applyCoercions χs c ∶ applyTys χs A ⊒ applyTys χs B
left-changes-narrowingˡ χs c⊒ = {! left-changes-narrowingˡ !}

-- The dual raw of a narrowing is determined by the raw alone and
-- commutes with the store-change shifts.  Stated over two
-- independent witnesses (at `χs = []` this is a narrowing sibling of
-- `dualʷ-raw-determined`).
narrowing-dual¹-applyCoercions :
  ∀ χs {μ μ′ Δ Δ′ Σ Σ′ c A B A′ B′} →
  (e : μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B) →
  (e′ : μ′ ∣ Δ′ ∣ Σ′ ⊢ applyCoercions χs c ∶ A′ ⊒ B′) →
  narrowing-dual¹ e′ ≡ applyCoercions χs (narrowing-dual¹ e)
narrowing-dual¹-applyCoercions χs e e′ =
  {! narrowing-dual¹-applyCoercions !}

------------------------------------------------------------------------
-- One-store arrow projections
------------------------------------------------------------------------

-- The domain dual of one-store arrow cast evidence: the raw that
-- β-↦ exposes as the argument-position cast when the source function
-- is a casted value.
fun-narrow-domain-dual¹ :
  ∀ {μ Δ Σ c d A B A′ B′} →
  μ ∣ Δ ∣ Σ ⊢ c ↦ d ∶ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Coercion
fun-narrow-domain-dual¹ (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) =
  proj₁ (dualʷ normalᵃ cʷ)

fun-narrow-domain-dual-typing¹ :
  ∀ {μ Δ Σ c d A B A′ B′} →
  StoreWfAt Δ Σ →
  (e : μ ∣ Δ ∣ Σ ⊢ c ↦ d ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
  μ ∣ Δ ∣ Σ ⊢ fun-narrow-domain-dual¹ e ∶ A ⊒ A′
fun-narrow-domain-dual-typing¹ {μ = μ} wfΣ
    (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) =
  dualʷ-flips-typingᵐ
    {μ = μ}
    {η = normalᵃ}
    {ν = μ}
    dualActionOk-normal
    dualStoreAt-normal
    wfΣ
    (c⊢ , cʷ)

fun-narrow-codomain¹ :
  ∀ {μ Δ Σ c d A B A′ B′} →
  μ ∣ Δ ∣ Σ ⊢ c ↦ d ∶ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  μ ∣ Δ ∣ Σ ⊢ d ∶ B ⊒ B′
fun-narrow-codomain¹ (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) =
  d⊢ , dⁿ

-- The domain dual of a mediated arrow index is witness-, mode-, and
-- store-independent: it is computed from the home witness of the
-- raw, and dual raws are determined across witnesses.  (The two
-- evidences may live at different stores — the transported inner
-- index of the recursion is compared against the original.)
fun-narrow-domain-dualᵐ-determined :
  ∀ {μ₁ μ₂ ΔL₁ ΔR₁ ρ₁ ΔL₂ ΔR₂ ρ₂ p q
     A A′ B B′ A₁ A₁′ B₁ B₁′} →
  (e₁ : μ₁ ∣ ΔL₁ ∣ ΔR₁ ∣ ρ₁ ⊢ p ↦ q ∶ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′)) →
  (e₂ : μ₂ ∣ ΔL₂ ∣ ΔR₂ ∣ ρ₂ ⊢ p ↦ q ∶ (A₁ ⇒ B₁) ⊒ᵐ (A₁′ ⇒ B₁′)) →
  fun-narrow-domain-dualᵐ e₁ ≡ fun-narrow-domain-dualᵐ e₂
fun-narrow-domain-dualᵐ-determined
    (_ , _ , _ , _ , _ , (_ , cross (p₁ʷ ↦ⁿʷ _)))
    (_ , _ , _ , _ , _ , (_ , cross (p₂ʷ ↦ⁿʷ _))) =
  dualʷ-raw-determined normalᵃ p₁ʷ p₂ʷ

------------------------------------------------------------------------
-- Source-side composition record projections (⨟ˡ)
------------------------------------------------------------------------

-- Domain-dual projection of an arrow-level source composition: the
-- left factor pins the middle type as an arrow, its domain widening
-- dualizes in the left store, and the mediated factors project
-- through `fun-narrow-domain-dual-typingᵐ` — determinacy of dual
-- raws rephrases the results at the use site's own evidences.
comp-src-fun-domain-dualᵐ :
  ∀ {μ₁ μ₂ η ΔL ΔR ρ cₛ dₛ p₁ q₁ p₂ q₂
     A₀ B₀ AL BL AR BR A₁ B₁ A₁′ B₁′ A₂ B₂ A₂′ B₂′} →
  StoreCorr ΔL ΔR ρ →
  ΔL ∣ ΔR ∣ ρ ⊢ (cₛ ↦ dₛ) ⨟ˡ (p₁ ↦ q₁) ≈ (p₂ ↦ q₂)
    ∶ (A₀ ⇒ B₀) ⊒ᵐ (AR ⇒ BR) →
  (s⊒ˡ : η ∣ ΔL ∣ leftStore ρ ⊢ cₛ ↦ dₛ
           ∶ (A₀ ⇒ B₀) ⊒ (AL ⇒ BL)) →
  (e₁ : μ₁ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p₁ ↦ q₁
          ∶ (A₁ ⇒ B₁) ⊒ᵐ (A₁′ ⇒ B₁′)) →
  (e₂ : μ₂ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p₂ ↦ q₂
          ∶ (A₂ ⇒ B₂) ⊒ᵐ (A₂′ ⇒ B₂′)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dual¹ s⊒ˡ
        ⨟ˡ fun-narrow-domain-dualᵐ e₁
        ≈ fun-narrow-domain-dualᵐ e₂ ∶ A₀ ⊒ᵐ AR
comp-src-fun-domain-dualᵐ {ρ = ρ} corr
    (composed-index-src {ηˢ = ηᶠ} {νᶜᵒᵐᵖ = ν}
      (cast-fun cₛ⊢ᶠ dₛ⊢ᶠ , cross (cₛʷᶠ ↦ⁿʷ dₛⁿᶠ))
      q⊒ᶠ r⊒ᶠ)
    (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ))
    e₁ e₂ =
  composed-index-src
    (subst
      (λ c₀ → ηᶠ ∣ _ ∣ leftStore ρ ⊢ c₀ ∶ _ ⊒ _)
      (dualʷ-raw-determined normalᵃ cₛʷᶠ cʷ)
      (dualʷ-flips-typingᵐ
        {μ = ηᶠ} {η = normalᵃ} {ν = ηᶠ}
        dualActionOk-normal
        dualStoreAt-normal
        (leftStore-wf corr)
        (cₛ⊢ᶠ , cₛʷᶠ)))
    (subst
      (λ c₀ → ν ∣ _ ∣ _ ∣ ρ ⊢ c₀ ∶ _ ⊒ᵐ _)
      (fun-narrow-domain-dualᵐ-determined q⊒ᶠ e₁)
      (fun-narrow-domain-dual-typingᵐ q⊒ᶠ))
    (subst
      (λ c₀ → ν ∣ _ ∣ _ ∣ ρ ⊢ c₀ ∶ _ ⊒ᵐ _)
      (fun-narrow-domain-dualᵐ-determined r⊒ᶠ e₂)
      (fun-narrow-domain-dual-typingᵐ r⊒ᶠ))

-- Codomain projection of an arrow-level source composition: pure
-- field inversion — the left factor's codomain and the mediated
-- factors' codomain projections.
comp-src-fun-codomainᵐ :
  ∀ {ΔL ΔR ρ cₛ dₛ p₁ q₁ p₂ q₂ A₀ B₀ AR BR} →
  ΔL ∣ ΔR ∣ ρ ⊢ (cₛ ↦ dₛ) ⨟ˡ (p₁ ↦ q₁) ≈ (p₂ ↦ q₂)
    ∶ (A₀ ⇒ B₀) ⊒ᵐ (AR ⇒ BR) →
  ΔL ∣ ΔR ∣ ρ ⊢ dₛ ⨟ˡ q₁ ≈ q₂ ∶ B₀ ⊒ᵐ BR
comp-src-fun-codomainᵐ
    (composed-index-src
      (cast-fun cₛ⊢ᶠ dₛ⊢ᶠ , cross (cₛʷᶠ ↦ⁿʷ dₛⁿᶠ))
      q⊒ᶠ r⊒ᶠ) =
  composed-index-src
    (dₛ⊢ᶠ , dₛⁿᶠ)
    (fun-narrow-codomainᵐ q⊒ᶠ)
    (fun-narrow-codomainᵐ r⊒ᶠ)

------------------------------------------------------------------------
-- Left-change transports of the ⨟ˡ record and the term relation
------------------------------------------------------------------------

-- A source-cast composition record crosses left store changes
-- field-wise: the left factor and its typing shift with the left
-- store, while the mediated factors move by `left-changes-transportᵐ`
-- — raws and home typings untouched.
left-changes-comp-srcᵐ :
  ∀ χs {ΔL ΔR ρ s q r A B} →
  StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ˡ q ≈ r ∶ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
    ⊢ applyCoercions χs s ⨟ˡ q ≈ r ∶ applyTys χs A ⊒ᵐ B
left-changes-comp-srcᵐ χs {ΔL = ΔL} {ρ = ρ} corr′
    (composed-index-src {ηˢ = η} s⊒ˡ q⊒ r⊒) =
  composed-index-src
    (reindex (left-changes-narrowingˡ χs s⊒ˡ))
    (left-changes-transportᵐ χs corr′ q⊒)
    (left-changes-transportᵐ χs corr′ r⊒)
  where
  reindex :
    ∀ {c A B} →
    applyModeEnvs χs η ∣ applyTyCtxs χs ΔL ∣ applyStores χs (leftStore ρ)
      ⊢ c ∶ A ⊒ B →
    applyModeEnvs χs η ∣ applyTyCtxs χs ΔL
      ∣ leftStore (applyLeftChanges χs ρ) ⊢ c ∶ A ⊒ B
  reindex =
    subst
      (λ Σ → applyModeEnvs χs η ∣ applyTyCtxs χs ΔL ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (sym (leftStore-applyLeftChanges χs ρ))

-- The mediated term-relation transport across left store changes:
-- the ⊒ᵐ replacement for the old postulated
-- `left-change-term-narrowing`.  Note the index raw `p` is untouched
-- — the point of the mediated design.  Structural induction over the
-- relation (binder cases shift the correspondence); hole-bodied, to
-- be discharged with the rest of the mediated left-change family.
left-changes-term-narrowingᵐ :
  ∀ χs {ΔL ΔR ρ M M′ p A B} →
  StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
    ⊢ applyTerms χs M ⊒ M′ ∶ p ⦂ applyTys χs A ⊒ᵐ B
left-changes-term-narrowingᵐ χs corr M⊒M′ =
  {! left-changes-term-narrowingᵐ !}

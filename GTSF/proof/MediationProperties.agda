{-# OPTIONS --allow-unsolved-metas #-}

module proof.MediationProperties where

-- File Charter:
--   * Store-typing properties of the mediation relations: the crux
--     lemma (mediation preserves cast typing across the two stores)
--     and the store-change transports of the mediated judgment.
--   * Holes: the structural Narrowing-witness transport (shape-only)
--     and the one-store weakening used by the home-side allocation
--     transport (base-language lemma, independent of mediation).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc; _<_; s≤s; z≤n)
open import Data.List using ([]; _∷_)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Types
open import Coercions
open import Store using (StoreWfAt)
open import NarrowWiden using
  ( Narrowing
  ; Widening
  ; cross
  ; dualʷ
  ; dualⁿ
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
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
-- The crux lemma
------------------------------------------------------------------------

-- Mediation preserves cast typing across the stores: with
-- corresponding modes, mediating store payloads, and a mediated raw,
-- a typing in the left store yields a typing of the mediated raw in
-- the right store at mediated endpoints.  This replaces the
-- shared-raw demand of the retired two-store judgment.
med-cast-typing :
  ∀ {V μL μR ΔR ΣL ΣR c c′ A B} {ΔL : TyCtx} →
  Functional V →
  ModeCorr V μL μR →
  StoreMed V ΣL ΣR →
  VarScopedʳ V ΔR →
  MedCo V c c′ →
  μL ∣ ΔL ∣ ΣL ⊢ c ∶ A =⇒ B →
  Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
    MedTy V A A′ × MedTy V B B′ ×
    (μR ∣ ΔR ∣ ΣR ⊢ c′ ∶ A′ =⇒ B′)
med-cast-typing f mc sm sc (medc-id med) (cast-id wfA ok) =
  _ , _ , med , med ,
  cast-id (med-wf sc med) (med-idTyAllowed mc med ok)
med-cast-typing f mc sm sc (medc-seal v med) (cast-seal wfA α∈ mok)
  with sm v α∈
... | P , β∈ , medP
  with medTy-functional f med medP
... | refl =
  _ , _ , med , med-var v ,
  cast-seal (med-wf sc med) β∈
    (trans (sym (cong sealModeAllowed (mc v))) mok)
med-cast-typing f mc sm sc (medc-unseal v med) (cast-unseal wfA α∈ mok)
  with sm v α∈
... | P , β∈ , medP
  with medTy-functional f med medP
... | refl =
  _ , _ , med-var v , med ,
  cast-unseal (med-wf sc med) β∈
    (trans (sym (cong sealModeAllowed (mc v))) mok)
med-cast-typing f mc sm sc (medc-seq ms mt) (cast-seq s⊢ t⊢)
  with med-cast-typing f mc sm sc ms s⊢
... | A′ , B₁ , medA , medB₁ , s⊢′
  with med-cast-typing f mc sm sc mt t⊢
... | B₂ , C′ , medB₂ , medC , t⊢′
  with medTy-functional f medB₂ medB₁
... | refl =
  A′ , C′ , medA , medC , cast-seq s⊢′ t⊢′
med-cast-typing f mc sm sc (medc-tag med) (cast-tag wfG gG tok) =
  _ , _ , med , med-★ ,
  cast-tag (med-wf sc med) (med-ground med gG)
    (med-tagTyAllowed mc med tok)
med-cast-typing f mc sm sc (medc-untag med) (cast-untag wfH gH tok) =
  _ , _ , med-★ , med ,
  cast-untag (med-wf sc med) (med-ground med gH)
    (med-tagTyAllowed mc med tok)
med-cast-typing f mc sm sc (medc-fun ms mt) (cast-fun s⊢ t⊢)
  with med-cast-typing f mc sm sc ms s⊢
     | med-cast-typing f mc sm sc mt t⊢
... | A′₁ , A₁ , medA′ , medA , s⊢′
    | B₁ , B′₁ , medB , medB′ , t⊢′ =
  _ , _ , med-⇒ medA medB , med-⇒ medA′ medB′ ,
  cast-fun s⊢′ t⊢′
med-cast-typing f mc sm sc (medc-all ms) (cast-all s⊢)
  with med-cast-typing (extVar-functional f) (modeCorr-ext mc)
         (storeMed-⟰ sm) (varScopedʳ-ext sc) ms s⊢
... | A₁ , B₁ , medA , medB , s⊢′ =
  _ , _ , med-∀ medA , med-∀ medB , cast-all s⊢′
med-cast-typing f mc sm sc (medc-gen medA ms) (cast-gen wfA occ s⊢)
  with med-cast-typing (extVar-functional f) (modeCorr-gen mc)
         (storeMed-⟰ sm) (varScopedʳ-ext sc) ms s⊢
... | A₁ , B₁ , medA₁ , medB , s⊢′
  with medTy-functional (extVar-functional f) medA₁ (medTy-⇑ medA)
... | refl =
  _ , _ , medA , med-∀ medB ,
  cast-gen (med-wf sc medA) (med-occurs medB occ) s⊢′
med-cast-typing f mc sm sc (medc-inst medB ms) (cast-inst wfB occ s⊢)
  with med-cast-typing (extVar-functional f) (modeCorr-inst mc)
         (storeMed-inst sm) (varScopedʳ-ext sc) ms s⊢
... | A₁ , B₁ , medA , medB₁ , s⊢′
  with medTy-functional (extVar-functional f) medB₁ (medTy-⇑ medB)
... | refl =
  _ , _ , med-∀ medA , medB ,
  cast-inst (med-wf sc medB) (med-occurs medA occ) s⊢′

-- The structural Narrowing witness only inspects the shape of the
-- raw, which mediation preserves.  Large mutual data, no conceptual
-- content; transport left as a named hole.
med-narrowing-witness :
  ∀ {V c c′} → MedCo V c c′ → Narrowing c → Narrowing c′
med-narrowing-witness med w = {! med-narrowing-witness !}

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
-- Mediation and coercion duals
------------------------------------------------------------------------

-- MedCo is closed under the grammar-directed duals: dualizing a pair
-- of mediated raws (each through its own side's witness) yields
-- mediated raws again.  Shape-only structural transport over the
-- witness grammars, like `med-narrowing-witness`; left as a named
-- hole.  (A direct proof generalizes the two dual-action
-- environments over a correspondence invariant — `normalᵃ` turns
-- into `extᵃ`/`genᵃ`/`instᵃ` on both sides in lockstep with the
-- `ExtVar` binder extension of the variable correspondence.)
medCo-dualʷ :
  ∀ {V c c′} →
  MedCo V c c′ →
  (w : Widening c) →
  (w′ : Widening c′) →
  MedCo V (proj₁ (dualʷ normalᵃ w)) (proj₁ (dualʷ normalᵃ w′))
medCo-dualʷ med w w′ = {! medCo-dualʷ !}

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

------------------------------------------------------------------------
-- Source-side composition record projections (⨟ˡ)
------------------------------------------------------------------------

-- Domain-dual projection of an arrow-level source composition.  The
-- record's left images are inverted field-wise (MedCo/MedTy are
-- structural, so the left images of arrow raws are arrows), their
-- domain widenings are dualized in the left store, and the mediation
-- of the dual raws comes from `medCo-dualʷ`.  This answers the
-- recorded open question positively: the ⨟ˡ record's fields DO
-- produce the inner-domain composition that the argument-cast node
-- of `sim-betaᵐ` needs, with no field change.
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
    (composed-index-src {νᶜᵒᵐᵖ = ν}
      (med-⇒ mAR mBR)
      (medc-fun mp₁ mq₁)
      (medc-fun mp₂ mq₂)
      (cast-fun cₛ⊢ᶠ dₛ⊢ᶠ , cross (cₛʷᶠ ↦ⁿʷ dₛⁿᶠ))
      (cast-fun p₁ᴸ⊢ q₁ᴸ⊢ , cross (p₁ᴸʷ ↦ⁿʷ q₁ᴸⁿ))
      (cast-fun p₂ᴸ⊢ q₂ᴸ⊢ , cross (p₂ᴸʷ ↦ⁿʷ q₂ᴸⁿ)))
    (cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ))
    (_ , _ , _ , _ , med-⇒ _ _ ,
      (cast-fun p₁⊢ q₁⊢ , cross (p₁ʷ ↦ⁿʷ q₁ⁿ)))
    (_ , _ , _ , _ , med-⇒ _ _ ,
      (cast-fun p₂⊢ q₂⊢ , cross (p₂ʷ ↦ⁿʷ q₂ⁿ))) =
  composed-index-src
    mAR
    (medCo-dualʷ mp₁ p₁ᴸʷ p₁ʷ)
    (medCo-dualʷ mp₂ p₂ᴸʷ p₂ʷ)
    (subst
      (λ c₀ → ν ∣ _ ∣ leftStore ρ ⊢ c₀ ∶ _ ⊒ _)
      (dualʷ-raw-determined normalᵃ cₛʷᶠ cʷ)
      (dualʷ-flips-typingᵐ
        {μ = ν} {η = normalᵃ} {ν = ν}
        dualActionOk-normal
        dualStoreAt-normal
        (leftStore-wf corr)
        (cₛ⊢ᶠ , cₛʷᶠ)))
    (dualʷ-flips-typingᵐ
      {μ = ν} {η = normalᵃ} {ν = ν}
      dualActionOk-normal
      dualStoreAt-normal
      (leftStore-wf corr)
      (p₁ᴸ⊢ , p₁ᴸʷ))
    (dualʷ-flips-typingᵐ
      {μ = ν} {η = normalᵃ} {ν = ν}
      dualActionOk-normal
      dualStoreAt-normal
      (leftStore-wf corr)
      (p₂ᴸ⊢ , p₂ᴸʷ))

-- Codomain projection of an arrow-level source composition: pure
-- field inversion — every output field is a sub-field of the input
-- record.
comp-src-fun-codomainᵐ :
  ∀ {ΔL ΔR ρ cₛ dₛ p₁ q₁ p₂ q₂ A₀ B₀ AR BR} →
  ΔL ∣ ΔR ∣ ρ ⊢ (cₛ ↦ dₛ) ⨟ˡ (p₁ ↦ q₁) ≈ (p₂ ↦ q₂)
    ∶ (A₀ ⇒ B₀) ⊒ᵐ (AR ⇒ BR) →
  ΔL ∣ ΔR ∣ ρ ⊢ dₛ ⨟ˡ q₁ ≈ q₂ ∶ B₀ ⊒ᵐ BR
comp-src-fun-codomainᵐ
    (composed-index-src
      (med-⇒ mAR mBR)
      (medc-fun mp₁ mq₁)
      (medc-fun mp₂ mq₂)
      (cast-fun cₛ⊢ᶠ dₛ⊢ᶠ , cross (cₛʷᶠ ↦ⁿʷ dₛⁿᶠ))
      (cast-fun p₁ᴸ⊢ q₁ᴸ⊢ , cross (p₁ᴸʷ ↦ⁿʷ q₁ᴸⁿ))
      (cast-fun p₂ᴸ⊢ q₂ᴸ⊢ , cross (p₂ᴸʷ ↦ⁿʷ q₂ᴸⁿ))) =
  composed-index-src
    mBR
    mq₁
    mq₂
    (dₛ⊢ᶠ , dₛⁿᶠ)
    (q₁ᴸ⊢ , q₁ᴸⁿ)
    (q₂ᴸ⊢ , q₂ᴸⁿ)

------------------------------------------------------------------------
-- Left-change transports of the ⨟ˡ record and the term relation
------------------------------------------------------------------------

medCo-applyLeftChanges :
  ∀ χs {ρ c cʳ} →
  MedCo (MatchedVar ρ) c cʳ →
  MedCo (MatchedVar (applyLeftChanges χs ρ)) (applyCoercions χs c) cʳ
medCo-applyLeftChanges [] med = med
medCo-applyLeftChanges (keep ∷ χs) med =
  medCo-applyLeftChanges χs med
medCo-applyLeftChanges (bind X ∷ χs) med =
  medCo-applyLeftChanges χs (medCo-mapˡ suc mv-left-alloc med)

-- A source-cast composition record crosses left store changes
-- field-wise: the left images and their typings shift with the left
-- store, while the mediated (home) raws are untouched.
left-changes-comp-srcᵐ :
  ∀ χs {ΔL ΔR ρ s q r A B} →
  ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ˡ q ≈ r ∶ A ⊒ᵐ B →
  applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
    ⊢ applyCoercions χs s ⨟ˡ q ≈ r ∶ applyTys χs A ⊒ᵐ B
left-changes-comp-srcᵐ χs {ΔL = ΔL} {ρ = ρ}
    (composed-index-src {νᶜᵒᵐᵖ = ν} med-B med-q med-r s⊒ˡ q⊒ˡ r⊒ˡ) =
  composed-index-src
    (medTy-applyLeftChanges χs med-B)
    (medCo-applyLeftChanges χs med-q)
    (medCo-applyLeftChanges χs med-r)
    (reindex (left-changes-narrowingˡ χs s⊒ˡ))
    (reindex (left-changes-narrowingˡ χs q⊒ˡ))
    (reindex (left-changes-narrowingˡ χs r⊒ˡ))
  where
  reindex :
    ∀ {c A B} →
    applyModeEnvs χs ν ∣ applyTyCtxs χs ΔL ∣ applyStores χs (leftStore ρ)
      ⊢ c ∶ A ⊒ B →
    applyModeEnvs χs ν ∣ applyTyCtxs χs ΔL
      ∣ leftStore (applyLeftChanges χs ρ) ⊢ c ∶ A ⊒ B
  reindex =
    subst
      (λ Σ → applyModeEnvs χs ν ∣ applyTyCtxs χs ΔL ∣ Σ ⊢ _ ∶ _ ⊒ _)
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

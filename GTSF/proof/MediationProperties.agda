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
open import NarrowWiden using (Narrowing; _∣_∣_⊢_∶_⊒_)
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing

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

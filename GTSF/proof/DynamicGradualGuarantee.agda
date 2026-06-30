{-# OPTIONS --allow-unsolved-metas #-}

module proof.DynamicGradualGuarantee where

-- File Charter:
--   * Top-down mechanization skeleton for the dynamic gradual guarantee from
--     cambridge25.
--   * Keeps the theorem statement and proof case analysis separate from local
--     inversion work such as Left Seal Narrowing Inversion.
--   * The proof follows the cambridge25 section "Gradual Guarantee": recurse on
--     term narrowing and on the right-hand reduction, invoking named lemmas for
--     catch-up, inversion, wrapping, and cast movement.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition using (_∣_⊢_⨾ⁿ_≈_∶_⊒_)
open import TermNarrowing
open import proof.Catchup
  using (catchup-lemma; runtime-open-change; runtime-⇑ᵗᵐ)
open import proof.CatchupStore using (combineStoreNrw)
open import proof.LeftSealNarrowingInversion using
  (LeftSealNarrowingInversion; leftSealNarrowingInversion)
open import proof.ReductionProperties using (type-rename-step-⇑ᵗᵐ)
open import proof.RightSealInversion2 using
  (right-seal-inversion₂; right-seal-inversion₂-cast-unseal⊥)
open import proof.TermSubstitutionNarrowing using
  (term-substitution-narrowing)
open import proof.NuPreservation using
  (runtime-·₁; runtime-•; runtime-⟨⟩; runtime-ν; runtime-⊕₁)

runtime-·₂-any :
  ∀ {L M} →
  RuntimeOK (L · M) →
  RuntimeOK M
runtime-·₂-any (ok-no (no•-· noL noM)) = ok-no noM
runtime-·₂-any (ok-·₁ okL noM) = ok-no noM
runtime-·₂-any (ok-·₂ vL noL okM) = okM

runtime-⊕₂-any :
  ∀ {L op M} →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK M
runtime-⊕₂-any (ok-no (no•-⊕ noL noM)) = ok-no noM
runtime-⊕₂-any (ok-⊕₁ okL noM) = ok-no noM
runtime-⊕₂-any (ok-⊕₂ vL noL okM) = okM

------------------------------------------------------------------------
-- Lemmas used by the cambridge25 top-down proof
------------------------------------------------------------------------

postulate
  right-tag-inversion₁ :
    ∀ {Δ σ γ M V q G} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G ! ⟩ ∶ q →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ G ？

  right-tag-inversion₂ :
    ∀ {Δ σ γ M V r G} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G ？ ⟩ ∶ r →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ id ★

  -- Refuted by `proof.RightSealInversionCounterexample`.
  -- right-seal-inversion₁ :
  --   ∀ {Δ σ γ M V r A α} →
  --   Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  --   ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q

  wrap-narrowing-lemma :
    ∀ {Δ σ V′ V W′ W p q s t} →
    Δ ∣ σ ∣ [] ⊢ V′ ⊒ V ⟨ - (s ↦ t) ⟩ ∶ p ↦ q →
    Δ ∣ σ ∣ [] ⊢ W′ ⊒ W ∶ - p →
    ∃[ χs ] ∃[ N′ ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ q′ ]
      (V′ · W′ —↠[ χs ] N′) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N′
        ⊒ V · (W ⟨ - s ⟩) ⟨ - t ⟩ ∶ q′

  wrap-widening-lemma :
    ∀ {Δ σ V′ V W′ W p q s t} →
    Δ ∣ σ ∣ [] ⊢ V′ ⊒ V ⟨ s ↦ t ⟩ ∶ p ↦ q →
    Δ ∣ σ ∣ [] ⊢ W′ ⊒ W ∶ - p →
    ∃[ χs ] ∃[ N′ ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ q′ ]
      (V′ · W′ —↠[ χs ] N′) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N′
        ⊒ V · (W ⟨ s ⟩) ⟨ t ⟩ ∶ q′

------------------------------------------------------------------------
-- Function application simulation
------------------------------------------------------------------------

function-application-simulation-ƛ⊒ƛ :
  ∀ {Δ σ N N′ V V′ a q} →
  Value V →
  Δ ∣ σ ∣ a ∷ [] ⊢ N ⊒ N′ ∶ q →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ a →
  ∃[ χs ] ∃[ P ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ q′ ]
    ((ƛ N) · V —↠[ χs ] P) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ P ⊒ N′ [ V′ ] ∶ q′
function-application-simulation-ƛ⊒ƛ {N = N} {V = V} vV N⊒N′ V⊒V′ =
  keep ∷ [] , N [ V ] , _ , [] , [] , [] , _ ,
  ↠-step (pure-step (β vV)) ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  term-substitution-narrowing _ N⊒N′

function-application-simulation :
  ∀ {Δ σ L L′ M N′ V′ r p q} →
  RuntimeOK M →
  Value V′ →
  Δ ∣ σ ∣ [] ⊢ L ⊒ L′ ∶ r →
  L′ ≡ ƛ N′ →
  r ≡ p ↦ q →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V′ ∶ - p →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ q′ ]
    (L · M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ [ V′ ] ∶ q′
function-application-simulation okM vV′ L⊒L′ eq eqr M⊒V′ = {!!}

------------------------------------------------------------------------
-- Dynamic gradual guarantee
------------------------------------------------------------------------

dynamicGradualGuarantee :
  ∀ {Δ σ M M′ N′ p χ′} →
  RuntimeOK M →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore χ′ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ ∶ p′

dynamicGradualGuarantee okM
    (α⊒α {L′ = blame} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blame pαᶜ
dynamicGradualGuarantee okM
    (α⊒α {L′ = Λ V′} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′)) =
  {!!}
dynamicGradualGuarantee okM
    (α⊒α {L′ = V′ ⟨ `∀ c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′)) =
  {!!}
dynamicGradualGuarantee okM
    (α⊒α {L′ = V′ ⟨ gen A c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′)) =
  {!!}
dynamicGradualGuarantee okM
    (α⊒α γ′≡ qᶜ pαᶜ L⊒L′) red = {!!}
dynamicGradualGuarantee okM
    (⊒α {L′ = blame} γ′≡ pαᶜ L⊒L′) (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blame pαᶜ
dynamicGradualGuarantee okM
    (⊒α {L′ = Λ V′} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′)) =
  {!!}
dynamicGradualGuarantee okM
    (⊒α {L′ = V′ ⟨ `∀ c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′)) =
  {!!}
dynamicGradualGuarantee okM
    (⊒α {L′ = V′ ⟨ gen A c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′)) =
  {!!}
dynamicGradualGuarantee okM (⊒α γ′≡ pαᶜ L⊒L′) red = {!!}
dynamicGradualGuarantee okM M⊒M′ M′→N′ = {!!}

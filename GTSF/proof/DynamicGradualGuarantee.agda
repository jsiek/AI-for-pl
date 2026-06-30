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
open import NuStore using (StoreWf)
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
  (term-substitution-narrowingᵗ)
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

typed-term-narrowing-source-typing :
  ∀ {Δ σ M M′ p A B} →
  StoreWf Δ (srcStoreⁿ σ) →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ∣ [] ⊢ M ⦂ A
typed-term-narrowing-source-typing wfΣ M⊒M′ = {!!}

typed-term-narrowing-target-typing :
  ∀ {Δ σ Σ′ M M′ p A B} →
  StoreWf Δ (srcStoreⁿ σ) →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ Σ′ ∣ [] ⊢ M′ ⦂ B
typed-term-narrowing-target-typing wfΣ σ⊒ M⊒M′ = {!!}

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
  ∀ {Δ σ N N′ V V′ a q A B C D} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ a ∶ᶜ A ⊒ B →
  Δ ∣ σ ∣ a ∷ [] ⊢ N ⊒ N′ ∶ q ⦂ C ⊒ D →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ a ⦂ A ⊒ B →
  ∃[ χs ] ∃[ P ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ q′ ]
    ((ƛ N) · V —↠[ χs ] P) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ P ⊒ N′ [ V′ ] ∶ q′
function-application-simulation-ƛ⊒ƛ {N = N} {V = V} vV aᶜ N⊒N′ V⊒V′ =
  keep ∷ [] , N [ V ] , _ , [] , [] , [] , _ ,
  ↠-step (pure-step (β vV)) ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  typed-term-narrowing-erasure (term-substitution-narrowingᵗ _ N⊒N′)

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
  ∀ {Δ σ Σ′ M M′ N′ A B p χ′} →
  StoreWf Δ (srcStoreⁿ σ) →
  RuntimeOK M →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ srcStoreⁿ σ ∣ [] ⊢ M ⦂ A →
  Δ ∣ Σ′ ∣ [] ⊢ M′ ⦂ B →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore χ′ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ ∶ p′

dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {L′ = blame} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blame pαᶜ
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {L′ = Λ V′} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′)) =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {L′ = V′ ⟨ `∀ c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′)) =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {L′ = V′ ⟨ gen A c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′)) =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ γ′≡ qᶜ pαᶜ L⊒L′) red = {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {L′ = blame} γ′≡ pαᶜ L⊒L′) (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blame pαᶜ
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {L′ = Λ V′} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′)) =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {L′ = V′ ⟨ `∀ c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′)) =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {L′ = V′ ⟨ gen A c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′)) =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ γ′≡ pαᶜ L⊒L′) red =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒
    (⊢· L⊢ M⊢) (⊢· L′⊢ M′⊢) qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
    (ξ-·₁ L′→N′ shiftM) =
  let
    rec =
      dynamicGradualGuarantee
        wfΣ
        (runtime-·₁ okM)
        σ⊒
        (typed-term-narrowing-source-typing wfΣ L⊒L′)
        (typed-term-narrowing-target-typing wfΣ σ⊒ L⊒L′)
        p↦qᶜ
        L⊒L′
        L′→N′
  in
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ M⊒M′ M′→N′ = {!!}

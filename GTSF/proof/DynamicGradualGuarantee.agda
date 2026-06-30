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
open import Relation.Binary.PropositionalEquality using (subst; sym)
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
open import proof.Catchup using (catchup-lemma)
open import proof.CatchupStore using (combineStoreNrw)
open import proof.NarrowWidenProperties using (tgtStoreⁿ-⊒ˢ)
open import proof.ReductionProperties using (type-rename-step-⇑ᵗᵐ)
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

typed-term-narrowing-target-typing-⊒ˢ :
  ∀ {Δ σ Σ′ M M′ p A B} →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ Σ′ ∣ [] ⊢ M′ ⦂ B
typed-term-narrowing-target-typing-⊒ˢ {Δ = Δ} {σ = σ} {Σ′ = Σ′}
    {M′ = M′} {B = B} σ⊒ M⊒M′ =
  subst
    (λ Σ₀ → Δ ∣ Σ₀ ∣ [] ⊢ M′ ⦂ B)
    (sym (tgtStoreⁿ-⊒ˢ σ⊒))
    (typed-term-narrowing-target-typing M⊒M′)

------------------------------------------------------------------------
-- Function application simulation
------------------------------------------------------------------------

function-application-simulation-ƛ⊒ƛᵗ :
  ∀ {Δ σ N N′ V V′ a q A B C D} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ a ∶ᶜ A ⊒ B →
  Δ ∣ σ ∣ a ∷ [] ⊢ N ⊒ N′ ∶ q ⦂ C ⊒ D →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ a ⦂ A ⊒ B →
  ∃[ χs ] ∃[ P ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ C′ ] ∃[ D′ ] ∃[ q′ ]
    ((ƛ N) · V —↠[ χs ] P) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ P ⊒ N′ [ V′ ] ∶ q′ ⦂ C′ ⊒ D′
function-application-simulation-ƛ⊒ƛᵗ {N = N} {V = V}
    vV aᶜ N⊒N′ V⊒V′ =
  keep ∷ [] , N [ V ] , _ , [] , [] , [] , _ , _ , _ ,
  ↠-step (pure-step (β vV)) ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  term-substitution-narrowingᵗ _ N⊒N′

function-application-simulation :
  ∀ {Δ σ L M N′ V′ p q A A′ B B′} →
  RuntimeOK M →
  Value V′ →
  Δ ∣ σ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V′ ∶ - p ⦂ A ⊒ A′ →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ C′ ] ∃[ D′ ] ∃[ q′ ]
    (L · M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ [ V′ ] ∶ q′ ⦂ C′ ⊒ D′
function-application-simulation okM vV′ L⊒L′ M⊒V′
    with catchup-lemma okM vV′ M⊒V′
function-application-simulation okM vV′ L⊒L′ M⊒V′
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′ =
  {!!}

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
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ A′ ] ∃[ B′ ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore χ′ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ ∶ p′ ⦂ A′ ⊒ B′

dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {L′ = blame} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ , _ , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blameᵗ pαᶜ
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    with catchup-lemma (runtime-• okM) {!!} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒Λ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    with catchup-lemma (runtime-• okM) {!!} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒∀ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    with catchup-lemma (runtime-• okM) {!!} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒gen =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (α⊒αᵗ γ′≡ qᶜ pαᶜ L⊒L′) red = {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {L′ = blame} γ′≡ pαᶜ L⊒L′) (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ , _ , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blameᵗ pαᶜ
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    with catchup-lemma {!!} {!!} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒Λ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    with catchup-lemma {!!} {!!} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒∀ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    with catchup-lemma {!!} {!!} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒gen =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ
    (⊒αᵗ γ′≡ pαᶜ L⊒L′) red =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒
    (⊢· L⊢ M⊢) (⊢· L′⊢ M′⊢) qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
    (pure-step (β vV)) =
  function-application-simulation (runtime-·₂-any okM) vV L⊒L′ M⊒M′
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
        (typed-term-narrowing-source-typing L⊒L′)
        (typed-term-narrowing-target-typing-⊒ˢ σ⊒ L⊒L′)
        p↦qᶜ
        L⊒L′
        L′→N′
  in
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒
    (⊢⊕ M⊢ op N⊢) (⊢⊕ M′⊢ .op N′⊢) qᶜ
    (⊕⊒⊕ᵗ M⊒M′ N⊒N′)
    (pure-step δ-⊕)
    with catchup-lemma (runtime-⊕₁ okM) ($ _) M⊒M′
       | catchup-lemma (runtime-⊕₂-any okM) ($ _) N⊒N′
dynamicGradualGuarantee wfΣ okM σ⊒
    (⊢⊕ M⊢ op N⊢) (⊢⊕ M′⊢ .op N′⊢) qᶜ
    (⊕⊒⊕ᵗ M⊒M′ N⊒N′)
    (pure-step δ-⊕)
    | χsM , WM , ΔM , ΠM , ΠM′ , πM ,
      vWM , noWM , M↠WM , ΔM≡ , ΠM≡ , ΠM′≡ , πM⊒ , WM⊒M′
    | χsN , WN , ΔN , ΠN , ΠN′ , πN ,
      vWN , noWN , N↠WN , ΔN≡ , ΠN≡ , ΠN′≡ , πN⊒ , WN⊒N′ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒
    M⊢ M′⊢ qᶜ
    (⊒cast+ᵗ {s = id A} q₀ᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma okM vV M⊒M′
dynamicGradualGuarantee wfΣ okM σ⊒
    M⊢ M′⊢ qᶜ
    (⊒cast+ᵗ {s = id A} q₀ᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒
    M⊢ (⊢⟨⟩ c⊢ M′⊢) qᶜ
    (⊒cast-ᵗ {s = id A} q₀ᶜ rᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma okM vV M⊒M′
dynamicGradualGuarantee wfΣ okM σ⊒
    M⊢ (⊢⟨⟩ c⊢ M′⊢) qᶜ
    (⊒cast-ᵗ {s = id A} q₀ᶜ rᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  {!!}
dynamicGradualGuarantee wfΣ okM σ⊒ M⊢ M′⊢ pᶜ M⊒M′ M′→N′ = {!!}

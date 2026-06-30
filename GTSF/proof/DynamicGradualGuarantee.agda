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
  (runtime-·₁; runtime-⟨⟩; runtime-ν; runtime-⊕₁)

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
function-application-simulation okM vV′
    (extend qᶜ pαᶜ L⊒L′) eq eqr M⊒V′ =
  {!!}
function-application-simulation okM vV′
    (split qᶜ pαᶜ L⊒L′) eq eqr M⊒V′ =
  {!!}
function-application-simulation okM vV′ (⊒blame pᶜ) () eqr M⊒V′
function-application-simulation okM vV′ (x⊒x pᶜ x∋p) () eqr M⊒V′
-- The direct λ/λ case reduces to the beta helper once the source argument is
-- known to be a value.  The full proof should obtain that value by catchup.
function-application-simulation okM vV′
    (ƛ⊒ƛ {N = N} {N′ = N′} p↦qᶜ N⊒N′)
    refl refl M⊒V′
    with catchup-lemma okM vV′ M⊒V′
function-application-simulation okM vV′
    (ƛ⊒ƛ {N = N} {N′ = N′} p↦qᶜ N⊒N′)
    refl refl M⊒V′
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    with function-application-simulation-ƛ⊒ƛ
           {N = N} {N′ = N′} {V = W} {V′ = _} vW {!!} W⊒V′
function-application-simulation okM vV′
    (ƛ⊒ƛ {N = N} {N′ = N′} p↦qᶜ N⊒N′)
    refl refl M⊒V′
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | χsβ , P , Δβ , Πβ , Πβ′ , πβ , qβ ,
      β↠ , Πβ≡ , Πβ′≡ , πβ⊒ , P⊒N′ =
  {!!}
function-application-simulation okM vV′
    (·⊒· qᶜ L⊒L′ M⊒M′) () eqr M⊒V′
function-application-simulation okM vV′
    (Λ⊒Λ allᶜ vV V⊒V′) () eqr M⊒V′
function-application-simulation okM vV′ (⊒Λ pᶜ N⊒V′) () eqr M⊒V′
function-application-simulation okM vV′ (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
    () eqr M⊒V′
function-application-simulation okM vV′
    (α⊒α qᶜ pαᶜ L⊒L′) () eqr M⊒V′
function-application-simulation okM vV′ (⊒α pαᶜ L⊒L′)
    () eqr M⊒V′
function-application-simulation okM vV′ (ν⊒ν pᶜ qᶜ N⊒N′)
    () eqr M⊒V′
function-application-simulation okM vV′ (⊒ν pᶜ L⊒L′) () eqr M⊒V′
function-application-simulation okM vV′ (ν⊒ pᶜ L⊒L′) refl eqr M⊒V′ =
  {!!}
function-application-simulation okM vV′ (κ⊒κ κ) () eqr M⊒V′
function-application-simulation okM vV′ (⊕⊒⊕ M⊒M′ N⊒N′)
    () eqr M⊒V′
function-application-simulation okM vV′
    (⊒cast+ qᶜ q⨟s≈r L⊒L′) () eqr M⊒V′
function-application-simulation okM vV′
    (⊒cast- qᶜ q⨟s≈r L⊒L′) () eqr M⊒V′
function-application-simulation okM vV′
    (cast+⊒ pᶜ r≈t⨟p L⊒L′) refl eqr M⊒V′ =
  {!!}
function-application-simulation okM vV′
    (cast-⊒ pᶜ r≈t⨟p L⊒L′) refl eqr M⊒V′ =
  {!!}

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

-- Store/context-shaping rules.  The recursive call is on the contained term
-- narrowing derivation; the missing part is transport through the de Bruijn
-- type-variable opening/substitution used by the store rule.
dynamicGradualGuarantee okM (extend qᶜ pαᶜ M⊒N′) red
    with dynamicGradualGuarantee okM M⊒N′ red
dynamicGradualGuarantee okM (extend qᶜ pαᶜ M⊒N′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (split qᶜ pαᶜ N⊒N′) red
    with dynamicGradualGuarantee (runtime-open-change okM) N⊒N′ red
dynamicGradualGuarantee okM (split qᶜ pαᶜ N⊒N′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′′ =
  {!!}

-- Atomic right-hand terms cannot step.
dynamicGradualGuarantee okM (⊒blame pᶜ) (pure-step ())
dynamicGradualGuarantee okM (x⊒x pᶜ x∋p) (pure-step ())
dynamicGradualGuarantee okM (κ⊒κ κ) (pure-step ())

-- Lambda application.  Contextual right reduction recurses on the matching
-- subderivation; the β redex uses function-application simulation, and the
-- casted-function redex is handled by the wrapping lemma.
dynamicGradualGuarantee okM (ƛ⊒ƛ p↦qᶜ N⊒N′) (pure-step ())
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step (β vV))
  = function-application-simulation
      (runtime-·₂-any okM) vV L⊒L′ refl refl M⊒M′
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′)
    (pure-step (β-↦ vV vW)) =
  wrap-widening-lemma L⊒L′ M⊒M′
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step blame-·₁) =
  {!!}
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step (blame-·₂ vV)) =
  {!!}
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₁ L′→N′ shiftM)
    with dynamicGradualGuarantee (runtime-·₁ okM) L⊒L′ L′→N′
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₁ L′→N′ shiftM)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₂ vV shiftV M′→N′)
    with dynamicGradualGuarantee (runtime-·₂-any okM) M⊒M′ M′→N′
dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₂ vV shiftV M′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}

-- Universal introduction and elimination.  The pure type-application redexes
-- use the α/ν cases from the paper; contextual ν steps recurse under the
-- stored body.
dynamicGradualGuarantee okM (Λ⊒Λ allᶜ vV V⊒V′) (pure-step ())
dynamicGradualGuarantee okM (⊒Λ pᶜ N⊒V′) (pure-step ())
dynamicGradualGuarantee okM (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) (pure-step red) =
  {!!}
dynamicGradualGuarantee okM (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) (ξ-⟨⟩ V′→N′) =
  {!!}
dynamicGradualGuarantee okM (α⊒α qᶜ pαᶜ L⊒L′) (ν-step vV noV)
    with catchup-lemma (runtime-ν okM) vV L⊒L′
dynamicGradualGuarantee okM (α⊒α qᶜ pαᶜ L⊒L′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , noN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒L′ =
  {!!}
dynamicGradualGuarantee okM (α⊒α qᶜ pαᶜ L⊒L′) (ξ-ν L′→N′)
    with dynamicGradualGuarantee (runtime-ν okM) L⊒L′ L′→N′
dynamicGradualGuarantee okM (α⊒α qᶜ pαᶜ L⊒L′) (ξ-ν L′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (α⊒α qᶜ pαᶜ L⊒L′) blame-ν =
  {!!}
dynamicGradualGuarantee okM (⊒α pαᶜ L⊒L′) (ν-step vV noV)
    with catchup-lemma okM vV L⊒L′
dynamicGradualGuarantee okM (⊒α pαᶜ L⊒L′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , noN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒L′ =
  {!!}
dynamicGradualGuarantee okM (⊒α pαᶜ L⊒L′) (ξ-ν L′→N′)
    with dynamicGradualGuarantee okM L⊒L′ L′→N′
dynamicGradualGuarantee okM (⊒α pαᶜ L⊒L′) (ξ-ν L′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (⊒α pαᶜ L⊒L′) blame-ν =
  {!!}

-- ν cases.  The `ν⊒ν` and `ν⊒` bind steps are the direct store-extension
-- cases at the end of the cambridge25 proof.  Contextual body steps recurse.
dynamicGradualGuarantee okM (ν⊒ν pᶜ qᶜ N⊒N′) (ν-step vV noV)
    with catchup-lemma (runtime-ν okM) vV N⊒N′
dynamicGradualGuarantee okM (ν⊒ν pᶜ qᶜ N⊒N′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , noN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒N′ =
  {!!}
dynamicGradualGuarantee okM (ν⊒ν pᶜ qᶜ N⊒N′) (ξ-ν N′→P′)
    with dynamicGradualGuarantee (runtime-ν okM) N⊒N′ N′→P′
dynamicGradualGuarantee okM (ν⊒ν pᶜ qᶜ N⊒N′) (ξ-ν N′→P′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}
dynamicGradualGuarantee okM (ν⊒ν pᶜ qᶜ N⊒N′) blame-ν =
  {!!}
dynamicGradualGuarantee okM (⊒ν pᶜ N⊒N′) (ν-step vV noV)
    with catchup-lemma (runtime-⇑ᵗᵐ okM) vV N⊒N′
dynamicGradualGuarantee okM (⊒ν pᶜ N⊒N′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , noN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒N′ =
  {!!}
dynamicGradualGuarantee okM (⊒ν pᶜ N⊒N′) (ξ-ν N′→P′)
    with dynamicGradualGuarantee (runtime-⇑ᵗᵐ okM) N⊒N′ N′→P′
dynamicGradualGuarantee okM (⊒ν pᶜ N⊒N′) (ξ-ν N′→P′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}
dynamicGradualGuarantee okM (⊒ν pᶜ N⊒N′) blame-ν =
  {!!}
dynamicGradualGuarantee okM (ν⊒ pᶜ N⊒N′) red
    with type-rename-step-⇑ᵗᵐ red
dynamicGradualGuarantee okM (ν⊒ pᶜ N⊒N′) red
    | χ′ , P′ , red′
    with dynamicGradualGuarantee (runtime-ν okM) N⊒N′ red′
dynamicGradualGuarantee okM (ν⊒ pᶜ N⊒N′) red
    | χ′ , P′ , red′
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}

-- Primitive arithmetic.  The pure δ case first catches both source operands up
-- to the right-hand constants; contextual substeps recurse on the corresponding
-- premise.
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step δ-⊕)
    with catchup-lemma (runtime-⊕₁ okM) ($ _) M⊒M′
       | catchup-lemma (runtime-⊕₂-any okM) ($ _) N⊒N′
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step δ-⊕)
    | χsM , M , ΔM , ΠM , ΠM′ , πM ,
      vM , noM , M↠ , ΔM≡ , ΠM≡ , ΠM′≡ , πM⊒ , W⊒M′
    | χsN , N , ΔN , ΠN , ΠN′ , πN ,
      vN , noN , N↠ , ΔN≡ , ΠN≡ , ΠN′≡ , πN⊒ , W⊒N′ =
  {!!}
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step blame-⊕₁) =
  {!!}
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step (blame-⊕₂ vV)) =
  {!!}
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₁ M′→P′ shiftN)
    with dynamicGradualGuarantee (runtime-⊕₁ okM) M⊒M′ M′→P′
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₁ M′→P′ shiftN)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₂ vV shiftM N′→P′)
    with dynamicGradualGuarantee (runtime-⊕₂-any okM) N⊒N′ N′→P′
dynamicGradualGuarantee okM (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₂ vV shiftM N′→P′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}

-- Right-cast reductions.  The ξ case recurses; the redex cases invoke the
-- right-tag, right-seal, sequence, ν-widening, and catch-up lemmas.
dynamicGradualGuarantee okM (⊒cast+ qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    with dynamicGradualGuarantee okM M⊒M′ M′→N′
dynamicGradualGuarantee okM (⊒cast+ qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (⊒cast+ {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma okM vV M⊒M′
dynamicGradualGuarantee okM (⊒cast+ {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , noN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒M′ =
  {!!}
dynamicGradualGuarantee okM (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV))
    with right-tag-inversion₂ (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
dynamicGradualGuarantee okM (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV))
    | M⊒V!
    with right-tag-inversion₁ M⊒V!
dynamicGradualGuarantee okM (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV))
    | M⊒V!
    | M⊒V =
  {!!}
dynamicGradualGuarantee okM (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G))
    with right-tag-inversion₂ (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
dynamicGradualGuarantee okM (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G))
    | M⊒V!
    with right-tag-inversion₁ M⊒V!
dynamicGradualGuarantee okM (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G))
    | M⊒V!
    | M⊒V =
  {!!}
dynamicGradualGuarantee okM (⊒cast+ {s = seal B α} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    with right-seal-inversion₂ vV qᶜ q⨟s≈r M⊒M′
dynamicGradualGuarantee okM (⊒cast+ {s = seal B α} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    | r , q⨟seal≈r , M⊒Vseal
  = {!!}
dynamicGradualGuarantee okM (⊒cast+ qᶜ q⨟s≈r M⊒M′) (pure-step red) =
  {!!}
dynamicGradualGuarantee okM (⊒cast- qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    with dynamicGradualGuarantee okM M⊒M′ M′→N′
dynamicGradualGuarantee okM (⊒cast- qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (⊒cast- {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma okM vV M⊒M′
dynamicGradualGuarantee okM (⊒cast- {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , noN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒M′ =
  {!!}
dynamicGradualGuarantee okM (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV))
    with right-tag-inversion₂ (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
dynamicGradualGuarantee okM (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV))
    | M⊒V!
    with right-tag-inversion₁ M⊒V!
dynamicGradualGuarantee okM (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV))
    | M⊒V!
    | M⊒V =
  {!!}
dynamicGradualGuarantee okM (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G))
    with right-tag-inversion₂ (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
dynamicGradualGuarantee okM (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G))
    | M⊒V!
    with right-tag-inversion₁ M⊒V!
dynamicGradualGuarantee okM (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G))
    | M⊒V!
    | M⊒V =
  {!!}
dynamicGradualGuarantee okM (⊒cast- {s = unseal α B} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    with right-seal-inversion₂-cast-unseal⊥ qᶜ q⨟s≈r
dynamicGradualGuarantee okM (⊒cast- {s = unseal α B} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    | ()
dynamicGradualGuarantee okM (⊒cast- qᶜ q⨟s≈r M⊒M′) (pure-step red) =
  {!!}

-- Left-cast administrative cases recurse on the premise, then move the cast
-- across the resulting multi-step evidence.
dynamicGradualGuarantee okM (cast+⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    with dynamicGradualGuarantee (runtime-⟨⟩ okM) M⊒M′ red
dynamicGradualGuarantee okM (cast+⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee okM (cast-⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    with dynamicGradualGuarantee (runtime-⟨⟩ okM) M⊒M′ red
dynamicGradualGuarantee okM (cast-⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}

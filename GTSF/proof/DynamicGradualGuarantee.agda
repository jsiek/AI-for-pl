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
open import TermNarrowing
open import proof.Catchup using (catchup-lemma)
open import proof.CatchupStore using (combineStoreNrw)
open import proof.LeftSealNarrowingInversion using
  (LeftSealNarrowingInversion; leftSealNarrowingInversion)
open import proof.ReductionProperties using (type-rename-step-⇑ᵗᵐ)
open import proof.TermSubstitutionNarrowing using
  (term-substitution-narrowing)

------------------------------------------------------------------------
-- Lemmas used by the cambridge25 top-down proof
------------------------------------------------------------------------

postulate
  right-tag-inversion₂ :
    ∀ {Δ σ γ M V r G} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G ？ ⟩ ∶ r →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ id ★

  -- Refuted by `proof.RightSealInversionCounterexample`.
  -- right-seal-inversion₁ :
  --   ∀ {Δ σ γ M V r A α} →
  --   Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  --   ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q

  right-seal-inversion₂ :
    ∀ {Δ σ γ M V q A α} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ unseal α A ⟩ ∶ q →
    ∃[ r ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r

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
function-application-simulation vV′ (extend qᶜ pαᶜ L⊒L′) eq eqr M⊒V′ =
  {!!}
function-application-simulation vV′ (split qᶜ pαᶜ L⊒L′) eq eqr M⊒V′ =
  {!!}
function-application-simulation vV′ (⊒blame pᶜ) () eqr M⊒V′
function-application-simulation vV′ (x⊒x pᶜ x∋p) () eqr M⊒V′
-- The direct λ/λ case reduces to the beta helper once the source argument is
-- known to be a value.  The full proof should obtain that value by catchup.
function-application-simulation vV′ (ƛ⊒ƛ {N = N} {N′ = N′} p↦qᶜ N⊒N′)
    refl refl M⊒V′
    with catchup-lemma vV′ M⊒V′
function-application-simulation vV′ (ƛ⊒ƛ {N = N} {N′ = N′} p↦qᶜ N⊒N′)
    refl refl M⊒V′
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    with function-application-simulation-ƛ⊒ƛ
           {N = N} {N′ = N′} {V = W} {V′ = _} vW {!!} W⊒V′
function-application-simulation vV′ (ƛ⊒ƛ {N = N} {N′ = N′} p↦qᶜ N⊒N′)
    refl refl M⊒V′
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′
    | χsβ , P , Δβ , Πβ , Πβ′ , πβ , qβ ,
      β↠ , Πβ≡ , Πβ′≡ , πβ⊒ , P⊒N′ =
  {!!}
function-application-simulation vV′ (·⊒· qᶜ L⊒L′ M⊒M′) () eqr M⊒V′
function-application-simulation vV′ (Λ⊒Λ allᶜ vV V⊒V′) () eqr M⊒V′
function-application-simulation vV′ (⊒Λ pᶜ N⊒V′) () eqr M⊒V′
function-application-simulation vV′ (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) () eqr M⊒V′
function-application-simulation vV′ (α⊒α qᶜ pαᶜ L⊒L′) () eqr M⊒V′
function-application-simulation vV′ (⊒α pαᶜ L⊒L′) () eqr M⊒V′
function-application-simulation vV′ (ν⊒ν pᶜ qᶜ N⊒N′) () eqr M⊒V′
function-application-simulation vV′ (⊒ν pᶜ L⊒L′) () eqr M⊒V′
function-application-simulation vV′ (ν⊒ pᶜ L⊒L′) refl eqr M⊒V′ =
  {!!}
function-application-simulation vV′ (κ⊒κ κ) () eqr M⊒V′
function-application-simulation vV′ (⊕⊒⊕ M⊒M′ N⊒N′) () eqr M⊒V′
function-application-simulation vV′ (⊒cast+ qᶜ q⨟s≈r L⊒L′) () eqr M⊒V′
function-application-simulation vV′ (⊒cast- qᶜ q⨟s≈r L⊒L′) () eqr M⊒V′
function-application-simulation vV′ (cast+⊒ pᶜ r≈t⨟p L⊒L′) refl eqr M⊒V′ =
  {!!}
function-application-simulation vV′ (cast-⊒ pᶜ r≈t⨟p L⊒L′) refl eqr M⊒V′ =
  {!!}

------------------------------------------------------------------------
-- Dynamic gradual guarantee
------------------------------------------------------------------------

dynamicGradualGuarantee :
  ∀ {Δ σ M M′ N′ p χ′} →
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
dynamicGradualGuarantee (extend qᶜ pαᶜ M⊒N′) red
    with dynamicGradualGuarantee M⊒N′ red
dynamicGradualGuarantee (extend qᶜ pαᶜ M⊒N′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (split qᶜ pαᶜ N⊒N′) red
    with dynamicGradualGuarantee N⊒N′ red
dynamicGradualGuarantee (split qᶜ pαᶜ N⊒N′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′′ =
  {!!}

-- Atomic right-hand terms cannot step.
dynamicGradualGuarantee (⊒blame pᶜ) (pure-step ())
dynamicGradualGuarantee (x⊒x pᶜ x∋p) (pure-step ())
dynamicGradualGuarantee (κ⊒κ κ) (pure-step ())

-- Lambda application.  Contextual right reduction recurses on the matching
-- subderivation; the β redex uses function-application simulation, and the
-- casted-function redex is handled by the wrapping lemma.
dynamicGradualGuarantee (ƛ⊒ƛ p↦qᶜ N⊒N′) (pure-step ())
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step (β vV))
  = function-application-simulation vV L⊒L′ refl refl M⊒M′
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′)
    (pure-step (β-↦ vV vW)) =
  wrap-widening-lemma L⊒L′ M⊒M′
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step blame-·₁) =
  {!!}
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step (blame-·₂ vV)) =
  {!!}
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₁ L′→N′ shiftM)
    with dynamicGradualGuarantee L⊒L′ L′→N′
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₁ L′→N′ shiftM)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₂ vV shiftV M′→N′)
    with dynamicGradualGuarantee M⊒M′ M′→N′
dynamicGradualGuarantee (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₂ vV shiftV M′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}

-- Universal introduction and elimination.  The pure type-application redexes
-- use the α/ν cases from the paper; contextual ν steps recurse under the
-- stored body.
dynamicGradualGuarantee (Λ⊒Λ allᶜ vV V⊒V′) (pure-step ())
dynamicGradualGuarantee (⊒Λ pᶜ N⊒V′) (pure-step ())
dynamicGradualGuarantee (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) (pure-step red) =
  {!!}
dynamicGradualGuarantee (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) (ξ-⟨⟩ V′→N′) =
  {!!}
dynamicGradualGuarantee (α⊒α qᶜ pαᶜ L⊒L′) (ν-step vV noV)
    with catchup-lemma vV L⊒L′
dynamicGradualGuarantee (α⊒α qᶜ pαᶜ L⊒L′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒L′ =
  {!!}
dynamicGradualGuarantee (α⊒α qᶜ pαᶜ L⊒L′) (ξ-ν L′→N′)
    with dynamicGradualGuarantee L⊒L′ L′→N′
dynamicGradualGuarantee (α⊒α qᶜ pαᶜ L⊒L′) (ξ-ν L′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (α⊒α qᶜ pαᶜ L⊒L′) blame-ν =
  {!!}
dynamicGradualGuarantee (⊒α pαᶜ L⊒L′) (ν-step vV noV)
    with catchup-lemma vV L⊒L′
dynamicGradualGuarantee (⊒α pαᶜ L⊒L′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒L′ =
  {!!}
dynamicGradualGuarantee (⊒α pαᶜ L⊒L′) (ξ-ν L′→N′)
    with dynamicGradualGuarantee L⊒L′ L′→N′
dynamicGradualGuarantee (⊒α pαᶜ L⊒L′) (ξ-ν L′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (⊒α pαᶜ L⊒L′) blame-ν =
  {!!}

-- ν cases.  The `ν⊒ν` and `ν⊒` bind steps are the direct store-extension
-- cases at the end of the cambridge25 proof.  Contextual body steps recurse.
dynamicGradualGuarantee (ν⊒ν pᶜ qᶜ N⊒N′) (ν-step vV noV)
    with catchup-lemma vV N⊒N′
dynamicGradualGuarantee (ν⊒ν pᶜ qᶜ N⊒N′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒N′ =
  {!!}
dynamicGradualGuarantee (ν⊒ν pᶜ qᶜ N⊒N′) (ξ-ν N′→P′)
    with dynamicGradualGuarantee N⊒N′ N′→P′
dynamicGradualGuarantee (ν⊒ν pᶜ qᶜ N⊒N′) (ξ-ν N′→P′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}
dynamicGradualGuarantee (ν⊒ν pᶜ qᶜ N⊒N′) blame-ν =
  {!!}
dynamicGradualGuarantee (⊒ν pᶜ N⊒N′) (ν-step vV noV)
    with catchup-lemma vV N⊒N′
dynamicGradualGuarantee (⊒ν pᶜ N⊒N′) (ν-step vV noV)
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒N′ =
  {!!}
dynamicGradualGuarantee (⊒ν pᶜ N⊒N′) (ξ-ν N′→P′)
    with dynamicGradualGuarantee N⊒N′ N′→P′
dynamicGradualGuarantee (⊒ν pᶜ N⊒N′) (ξ-ν N′→P′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}
dynamicGradualGuarantee (⊒ν pᶜ N⊒N′) blame-ν =
  {!!}
dynamicGradualGuarantee (ν⊒ pᶜ N⊒N′) red
    with type-rename-step-⇑ᵗᵐ red
dynamicGradualGuarantee (ν⊒ pᶜ N⊒N′) red
    | χ′ , P′ , red′
    with dynamicGradualGuarantee N⊒N′ red′
dynamicGradualGuarantee (ν⊒ pᶜ N⊒N′) red
    | χ′ , P′ , red′
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}

-- Primitive arithmetic.  The pure δ case first catches both source operands up
-- to the right-hand constants; contextual substeps recurse on the corresponding
-- premise.
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step δ-⊕)
    with catchup-lemma ($ _) M⊒M′ | catchup-lemma ($ _) N⊒N′
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step δ-⊕)
    | χsM , M , ΔM , ΠM , ΠM′ , πM ,
      vM , M↠ , ΔM≡ , ΠM≡ , ΠM′≡ , πM⊒ , W⊒M′
    | χsN , N , ΔN , ΠN , ΠN′ , πN ,
      vN , N↠ , ΔN≡ , ΠN≡ , ΠN′≡ , πN⊒ , W⊒N′ =
  {!!}
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step blame-⊕₁) =
  {!!}
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (pure-step (blame-⊕₂ vV)) =
  {!!}
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₁ M′→P′ shiftN)
    with dynamicGradualGuarantee M⊒M′ M′→P′
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₁ M′→P′ shiftN)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₂ vV shiftM N′→P′)
    with dynamicGradualGuarantee N⊒N′ N′→P′
dynamicGradualGuarantee (⊕⊒⊕ M⊒M′ N⊒N′) (ξ-⊕₂ vV shiftM N′→P′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒P′ =
  {!!}

-- Right-cast reductions.  The ξ case recurses; the redex cases invoke the
-- right-tag, right-seal, sequence, ν-widening, and catch-up lemmas.
dynamicGradualGuarantee (⊒cast+ qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    with dynamicGradualGuarantee M⊒M′ M′→N′
dynamicGradualGuarantee (⊒cast+ qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (⊒cast+ {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma vV M⊒M′
dynamicGradualGuarantee (⊒cast+ {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒M′ =
  {!!}
dynamicGradualGuarantee (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV)) =
  {!!}
dynamicGradualGuarantee (⊒cast+ {s = (‵ ι) !} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G)) =
  {!!}
dynamicGradualGuarantee (⊒cast+ {s = seal B α} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    with right-seal-inversion₂ (⊒cast+ {s = seal B α} qᶜ q⨟s≈r M⊒M′)
dynamicGradualGuarantee (⊒cast+ {s = seal B α} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    | r , M⊒Vseal
  = {!!}
dynamicGradualGuarantee (⊒cast+ qᶜ q⨟s≈r M⊒M′) (pure-step red) =
  {!!}
dynamicGradualGuarantee (⊒cast- qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    with dynamicGradualGuarantee M⊒M′ M′→N′
dynamicGradualGuarantee (⊒cast- qᶜ q⨟s≈r M⊒M′) (ξ-⟨⟩ M′→N′)
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (⊒cast- {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma vV M⊒M′
dynamicGradualGuarantee (⊒cast- {s = id A} qᶜ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , N , Δ′ , Π , Π′ , π ,
      vN , N↠ , Δ′≡ , Π≡ , Π′≡ , π⊒ , N⊒M′ =
  {!!}
dynamicGradualGuarantee (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-ok vV)) =
  {!!}
dynamicGradualGuarantee (⊒cast- {s = G ？} qᶜ q⨟s≈r M⊒M′)
    (pure-step (tag-untag-bad vV H≢G)) =
  {!!}
dynamicGradualGuarantee (⊒cast- {s = unseal α B} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    with right-seal-inversion₂ (⊒cast- {s = unseal α B} qᶜ q⨟s≈r M⊒M′)
dynamicGradualGuarantee (⊒cast- {s = unseal α B} qᶜ q⨟s≈r M⊒M′)
    (pure-step (seal-unseal vV))
    | r , M⊒Vseal
  = {!!}
dynamicGradualGuarantee (⊒cast- qᶜ q⨟s≈r M⊒M′) (pure-step red) =
  {!!}

-- Left-cast administrative cases recurse on the premise, then move the cast
-- across the resulting multi-step evidence.
dynamicGradualGuarantee (cast+⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    with dynamicGradualGuarantee M⊒M′ red
dynamicGradualGuarantee (cast+⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}
dynamicGradualGuarantee (cast-⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    with dynamicGradualGuarantee M⊒M′ red
dynamicGradualGuarantee (cast-⊒ {t = t} pᶜ r≈t⨟p M⊒M′) red
    | χs , N , Δ′ , Π , Π′ , π , p′ , N↠ , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  {!!}

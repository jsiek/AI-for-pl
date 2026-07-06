{-# OPTIONS --allow-unsolved-metas #-}

module proof.LeftNuWideningSeparated where

-- File Charter:
--   * Separated-store statement and proof skeleton for the Cambridge25
--     Left ν Widening Lemma.
--   * Pins down the DGG call shape for the matched α/type-application
--     `β-gen•` case.
--   * Keeps every emitted source store change, right-step store change, and
--     endpoint equality explicit in the theorem result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NuReduction using
  ( keep
  ; applyTy
  ; applyTyCtx
  ; applyTys
  ; applyTyCtxs
  ; _—→[_]_
  ; _—↠[_]_
  )
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyRightChange
  )
open import proof.ReductionProperties using
  ( applyCoercions
  )

------------------------------------------------------------------------
-- Separated Left ν Widening Lemma
------------------------------------------------------------------------

left-widening-lemma-separated :
  ∀ {ΔL ΔR ρ V V′ p r t A B C D} →
  Value V →
  No• V →
  ΔL ∣ ΔR ∣ ρ ⊢ t ⨟ p ≈ r ∶ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ V ⊒ V′ ∶ p ⦂ C ⊒ D →
  ∃[ χs ] ∃[ W ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (V ⟨ - t ⟩ —↠[ χs ] W) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep B) ×
    (r′ ≡ applyCoercions χs r) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ W ⊒ V′ ∶ r′ ⦂ C′ ⊒ D′
left-widening-lemma-separated vV noV compᵏ V⊒V′ =
  {! left-widening-lemma-separated-proof !}

left-narrowing-lemma-separated :
  ∀ {ΔL ΔR ρ V V′ p r t A B C D} →
  Value V →
  No• V →
  ΔL ∣ ΔR ∣ ρ ⊢ t ⨟ p ≈ r ∶ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ V ⊒ V′ ∶ r ⦂ A ⊒ B →
  ∃[ χs ] ∃[ W ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ p′ ]
    (V ⟨ t ⟩ —↠[ χs ] W) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs C) ×
    (D′ ≡ applyTy keep D) ×
    (p′ ≡ applyCoercions χs p) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ W ⊒ V′ ∶ p′ ⦂ C′ ⊒ D′
left-narrowing-lemma-separated vV noV compᵏ V⊒V′ =
  {! left-narrowing-lemma-separated-proof !}

-- Cambridge25-shaped value-level lemma.  The premise relation is the
-- polymorphic value relation `V ⊒ V′ : ∀ p`; the source term adds the
-- dual of the left widening cast `t`; and the composition witness pins the
-- resulting index `r`.  The ν-specific instantiation is supplied by the
-- caller through the shape of `t`, `r`, and the composition witness.
--
-- This is intentionally more general than the DGG call-site theorem below:
-- it does not mention the target `β-gen•` step or the matched-α type
-- application.  Those belong to the caller that exposes where this lemma is
-- needed.
left-ν-widening-lemma :
  ∀ {ΔL ΔR ρ V V′ p r t A B C D} →
  Value V →
  No• V →
  ΔL ∣ ΔR ∣ ρ ⊢ t ⨟ `∀ p ≈ r ∶ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ V ⊒ V′ ∶ `∀ p ⦂ C ⊒ D →
  ∃[ χs ] ∃[ W ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (V ⟨ - t ⟩ —↠[ χs ] W) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep B) ×
    (r′ ≡ applyCoercions χs r) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ [] ⊢ W ⊒ V′ ∶ r′ ⦂ C′ ⊒ D′
left-ν-widening-lemma vV noV compᵏ
    (Λ⊒Λᵗ allᶜ vBody vBody′ body⊒) =
  let
    -- Cambridge25 `Λ⊒Λ`: the recursive work is delegated to the ordinary
    -- left-widening lemma on the body-level relation and smaller cast.
    ih =
      left-widening-lemma-separated
        {! leftν-Λ-value !}
        {! leftν-Λ-no• !}
        {! leftν-Λ-composition !}
        body⊒
  in
  {! leftν-Λ⊒Λ-case !}
left-ν-widening-lemma vV noV compᵏ
    (⊒cast+ᵗ qᶜ rᶜ t⊒ compᵏ′ V⊒V′cast) =
  let
    -- Cambridge25 target cast wrapper (`⊒+`): recurse on the inner
    -- relation, then rebuild the target cast wrapper around the result.
    ih =
      left-widening-lemma-separated
        {! leftν-⊒cast+-value !}
        {! leftν-⊒cast+-no• !}
        {! leftν-⊒cast+-composition !}
        V⊒V′cast
  in
  {! leftν-⊒cast+-case !}
left-ν-widening-lemma vV noV compᵏ
    (⊒cast-ᵗ qᶜ rᶜ t⊒ compᵏ′ V⊒V′cast) =
  let
    -- Cambridge25 target cast wrapper (`⊒+`), non-dual target cast form.
    ih =
      left-widening-lemma-separated
        {! leftν-⊒cast--value !}
        {! leftν-⊒cast--no• !}
        {! leftν-⊒cast--composition !}
        V⊒V′cast
  in
  {! leftν-⊒cast--case !}
left-ν-widening-lemma vV noV compᵏ
    (cast+⊒ᵗ qᶜ rᶜ s⊒ compᵏ′ Vcast⊒V′) =
  let
    -- Cambridge25 source cast wrapper (`+⊒` / `⊒Λ/-⊒`): the recursive
    -- branch uses the ordinary left-narrowing shape when the source cast
    -- must be peeled before the ν-widening cast is rebuilt.
    ih =
      left-narrowing-lemma-separated
        {! leftν-cast+⊒-value !}
        {! leftν-cast+⊒-no• !}
        {! leftν-cast+⊒-composition !}
        Vcast⊒V′
  in
  {! leftν-cast+⊒-case !}
left-ν-widening-lemma vV noV compᵏ
    (cast-⊒ᵗ qᶜ rᶜ s⊒ compᵏ′ Vcast⊒V′) =
  let
    -- Cambridge25 source cast wrapper (`+⊒` / `⊒Λ/-⊒`), non-dual source
    -- cast form.
    ih =
      left-narrowing-lemma-separated
        {! leftν-cast-⊒-value !}
        {! leftν-cast-⊒-no• !}
        {! leftν-cast-⊒-composition !}
        Vcast⊒V′
  in
  {! leftν-cast-⊒-case !}
left-ν-widening-lemma vV noV compᵏ V⊒V′ =
  {! left-ν-widening-remaining-case !}

-- DGG call-site obligation for the separated `α⊒αᵗ` / `β-gen•` case.
-- The source begins at the matched fresh α type application
-- `(⇑ᵗᵐ L) •`; the target one-step redex is an explicit premise, so the
-- DGG caller pins it to `pure-step (β-gen• vV′)`.
--
-- The result mirrors `dynamicGradualGuarantee`: `χs` are the source-side
-- store changes produced by the lemma, while the target-side change is the
-- explicit `keep` from the pure target step.
matched-α-beta-gen-left-ν-widening-call :
  ∀ {ΔL ΔR ρ γ L L′ N′ p q Aα Bα C D E F} →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  ((⇑ᵗᵐ L′) •) —→[ keep ] N′ →
  [] ≡ ⇑ᵍᶜ γ →
  TermTypingEndpointsᶜ (suc ΔL) (suc ΔR)
    (matched zero (⇑ᵗ Aα) zero (⇑ᵗ Bα) ∷ ⇑ᶜorr ρ) []
    ((⇑ᵗᵐ L) •) ((⇑ᵗᵐ L′) •) C D →
  ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ Aα ⊒ Bα →
  suc ΔL ∣ suc ΔR
    ∣ matched zero (⇑ᵗ Aα) zero (⇑ᵗ Bα) ∷ ⇑ᶜorr ρ
    ⊢ p ∶ᶜ C ⊒ D →
  ΔL ∣ ΔR ∣ ρ ∣ γ
    ⊢ L ⊒ L′ ∶ `∀ p ⦂ E ⊒ F →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r ]
    (((⇑ᵗᵐ L) •) —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs (suc ΔL)) ×
    (ΔR′ ≡ applyTyCtx keep (suc ΔR)) ×
    (ρ′ ≡ applyRightChange keep
      (applyLeftChanges χs
        (matched zero (⇑ᵗ Aα) zero (⇑ᵗ Bα) ∷ ⇑ᶜorr ρ))) ×
    (C′ ≡ applyTys χs C) ×
    (D′ ≡ applyTy keep D) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ ∶ r ⦂ C′ ⊒ D′
matched-α-beta-gen-left-ν-widening-call
    okM target-step γ′≡ endpoints qᶜ pᶜ L⊒L′ =
  let
    -- This is the intended bridge to the general Cambridge25 lemma.  The
    -- remaining holes are precisely the inversions that expose the value `V`,
    -- the ν-widening cast `gen Aν t`, and the composition witness from the
    -- matched-α DGG premise.
    general-leftν =
      left-ν-widening-lemma
        {! matched-α-leftν-value !}
        {! matched-α-leftν-no• !}
        {! matched-α-leftν-composition !}
        {! matched-α-leftν-value-relation !}
  in
  {! matched-α-beta-gen-left-ν-widening-obligation !}

-- Structural proof skeleton for the intended mutual induction.  The exact
-- result transports are still the holes in the lemmas above; this
-- helper records which separated constructors recurse into which premises
-- before those transports are filled.
{-# TERMINATING #-}
left-ν-widening-induction-skeleton :
  ∀ {ΔL ΔR ρ γ L L′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ L′ ∶ p ⦂ A ⊒ B →
  Set₁
left-ν-widening-induction-skeleton (⊒blameᵗ _ _) = Set
left-ν-widening-induction-skeleton (x⊒xᵗ _ _) = Set
left-ν-widening-induction-skeleton (ƛ⊒ƛᵗ _ N⊒N′) =
  left-ν-widening-induction-skeleton N⊒N′
left-ν-widening-induction-skeleton (·⊒·ᵗ _ L⊒L′ M⊒M′) =
  left-ν-widening-induction-skeleton L⊒L′ ×
  left-ν-widening-induction-skeleton M⊒M′
left-ν-widening-induction-skeleton (Λ⊒Λᵗ _ _ _ V⊒V′) =
  left-ν-widening-induction-skeleton V⊒V′
left-ν-widening-induction-skeleton (⊒Λᵗ _ _ N⊒V′) =
  left-ν-widening-induction-skeleton N⊒V′
left-ν-widening-induction-skeleton (⊒⟨ν⟩ᵗ _ _ _ N⊒V′s) =
  left-ν-widening-induction-skeleton N⊒V′s
left-ν-widening-induction-skeleton (α⊒αᵗ _ _ _ _ L⊒L′) =
  left-ν-widening-induction-skeleton L⊒L′
left-ν-widening-induction-skeleton (⊒αᵗ _ _ _ L⊒L′) =
  left-ν-widening-induction-skeleton L⊒L′
left-ν-widening-induction-skeleton (ν⊒νᵗ _ _ _ N⊒N′) =
  left-ν-widening-induction-skeleton N⊒N′
left-ν-widening-induction-skeleton (⊒νᵗ _ _ N⊒N′) =
  left-ν-widening-induction-skeleton N⊒N′
left-ν-widening-induction-skeleton (κ⊒κᵗ _ _) = Set
left-ν-widening-induction-skeleton (⊕⊒⊕ᵗ _ M⊒M′ N⊒N′) =
  left-ν-widening-induction-skeleton M⊒M′ ×
  left-ν-widening-induction-skeleton N⊒N′
left-ν-widening-induction-skeleton (⊒cast+ᵗ _ _ _ _ M⊒M′) =
  left-ν-widening-induction-skeleton M⊒M′
left-ν-widening-induction-skeleton (⊒cast-ᵗ _ _ _ _ M⊒M′) =
  left-ν-widening-induction-skeleton M⊒M′
left-ν-widening-induction-skeleton (cast+⊒ᵗ _ _ _ _ M⊒M′) =
  left-ν-widening-induction-skeleton M⊒M′
left-ν-widening-induction-skeleton (cast-⊒ᵗ _ _ _ _ M⊒M′) =
  left-ν-widening-induction-skeleton M⊒M′

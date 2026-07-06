{-# OPTIONS --allow-unsolved-metas #-}

module proof.InnerStepCastSeparated where

-- File Charter:
--   * ξ-⟨⟩ simulation for target-side casts in the separated DGG: when
--     the target term steps under a cast (possibly allocating, χ′), the
--     ⊒cast±ᵗ relation is rebuilt over the store-changed contexts that
--     the induction hypothesis produces.
--   * The store-change transports of the sibling cast evidence are
--     hole-bodied lemmas here — not postulates.  See the checklist
--     ("Right store changes and shared coercion raws") for the
--     counterexample analysis behind their statements.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyRightChange
  )
open import proof.ReductionProperties using (applyCoercions)

------------------------------------------------------------------------
-- Store-change transports for cast evidence
------------------------------------------------------------------------

-- A relation-indexing coercion moves with both stores: its source
-- endpoint and raw follow the source changes χs, its target endpoint
-- follows the single target change χ′ of the simulated step.  The
-- χ′-side raw shift matches ξ-⟨⟩, which shifts the coercions it steps
-- under.
change-relation-coercion-narrowing :
  ∀ χs χ′ {μ ΔL ΔR ρ c A B} →
  StoreCorr (applyTyCtxs χs ΔL) (applyTyCtx χ′ ΔR)
    (applyRightChange χ′ (applyLeftChanges χs ρ)) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  μ ∣ applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
    ∣ applyRightChange χ′ (applyLeftChanges χs ρ)
    ⊢ applyCoercion χ′ (applyCoercions χs c)
      ∶ applyTys χs A ⊒ applyTy χ′ B
change-relation-coercion-narrowing χs χ′ corr c⊒ =
  {! change-relation-coercion-transport !}

-- A target-side mediating coercion: both endpoints are types of the
-- target-side cast, so both move by χ′, and the raw is untouched by the
-- source changes χs — the target term does not move when the source
-- steps — and shifted by χ′ exactly as ξ-⟨⟩ shifts the cast it steps
-- under.  The Σ-component transports the dual raw the same way, which
-- is what lets the ⊒cast+ᵗ caller rewrite its target term.
change-target-coercion-narrowing :
  ∀ χs χ′ {μ ΔL ΔR ρ c A B} →
  StoreCorr (applyTyCtxs χs ΔL) (applyTyCtx χ′ ΔR)
    (applyRightChange χ′ (applyLeftChanges χs ρ)) →
  (c⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B) →
  Σ[ e ∈ (μ ∣ applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
            ∣ applyRightChange χ′ (applyLeftChanges χs ρ)
            ⊢ applyCoercion χ′ c
              ∶ applyTy χ′ A ⊒ applyTy χ′ B) ]
    narrowing-dual e ≡ applyCoercion χ′ (narrowing-dual c⊒)
change-target-coercion-narrowing χs χ′ corr c⊒ =
  {! change-target-coercion-transport !}

-- Composition transport.  The composite of the transported factors is
-- canonical at the transported endpoints (`narrowing-determinedᵐ`), so
-- the factors compose to any coercion well-typed at that index — in
-- particular to the coercion the induction hypothesis produced.
change-composed-index :
  ∀ χs χ′ {ΔL ΔR ρ p t r r₁ A B μ₁} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ⨟ t ≈ r ∶ A ⊒ B →
  μ₁ ∣ applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
    ∣ applyRightChange χ′ (applyLeftChanges χs ρ)
    ⊢ r₁ ∶ applyTys χs A ⊒ applyTy χ′ B →
  applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
    ∣ applyRightChange χ′ (applyLeftChanges χs ρ)
    ⊢ applyCoercion χ′ (applyCoercions χs p) ⨟ applyCoercion χ′ t
      ≈ r₁ ∶ applyTys χs A ⊒ applyTy χ′ B
change-composed-index χs χ′ comp r₁⊒ =
  {! change-composed-index-transport !}

------------------------------------------------------------------------
-- ξ-⟨⟩ case lemmas
------------------------------------------------------------------------

-- Target cast on the right of a ⊒cast+ᵗ node, inner target step.  The
-- result relation is indexed by the transported outer coercion; its
-- inner coercion is whatever the induction hypothesis produced, glued
-- in by the composition transport.
target-cast-plus-inner-step-result :
  ∀ {χs χ′ ΔL ΔR ρ ΔL′ ΔR′ ρ′ N S′ p′ r t A B C rᶦʰ η} →
  ΔL ∣ ΔR ∣ ρ ⊢ p′ ∶ᶜ A ⊒ C →
  (t⊒ : η ∣ ΔL ∣ ΔR ∣ ρ ⊢ t ∶ C ⊒ B) →
  ΔL ∣ ΔR ∣ ρ ⊢ p′ ⨟ t ≈ r ∶ A ⊒ B →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  ΔR′ ≡ applyTyCtx χ′ ΔR →
  ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ) →
  ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
    ⊢ N ⊒ S′ ∶ rᶦʰ ⦂ applyTys χs A ⊒ applyTy χ′ B →
  ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
    ⊢ N ⊒ S′ ⟨ applyCoercion χ′ (narrowing-dual t⊒) ⟩
      ∶ applyCoercion χ′ (applyCoercions χs p′)
      ⦂ applyTys χs A ⊒ applyTy χ′ C
target-cast-plus-inner-step-result {χs} {χ′} {ΔL} {ΔR} {ρ}
    {N = N} {S′ = S′} {p′ = p′} {t = t}
    {A = A} {B = B} {C = C}
    p′ᶜ t⊒ comp refl refl refl ih =
  let
    μih , rᶦʰ⊒ = typed-term-narrowing-coercion ih

    corr = narrowing-store-corrᶜ rᶦʰ⊒

    p₁ᶜ = change-relation-coercion-narrowing χs χ′ corr p′ᶜ

    t₁⊒dual = change-target-coercion-narrowing χs χ′ corr t⊒

    comp₁ = change-composed-index χs χ′ comp rᶦʰ⊒
  in
  subst
    (λ d →
      applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
        ∣ applyRightChange χ′ (applyLeftChanges χs ρ) ∣ []
        ⊢ N ⊒ S′ ⟨ d ⟩
          ∶ applyCoercion χ′ (applyCoercions χs p′)
          ⦂ applyTys χs A ⊒ applyTy χ′ C)
    (proj₂ t₁⊒dual)
    (⊒cast+ᵗ p₁ᶜ rᶦʰ⊒ (proj₁ t₁⊒dual) comp₁ ih)

-- Target cast on the right of a ⊒cast-ᵗ node, inner target step.  The
-- inner relation of the rebuilt node must be indexed by the transported
-- p′; the induction hypothesis's coercion index is identified with it
-- by canonicity (the named hole below).
target-cast-minus-inner-step-result :
  ∀ {χs χ′ ΔL ΔR ρ ΔL′ ΔR′ ρ′ N S′ p′ r t A B C pᶦʰ μ η} →
  ΔL ∣ ΔR ∣ ρ ⊢ p′ ∶ᶜ A ⊒ C →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ B →
  η ∣ ΔL ∣ ΔR ∣ ρ ⊢ t ∶ C ⊒ B →
  ΔL ∣ ΔR ∣ ρ ⊢ p′ ⨟ t ≈ r ∶ A ⊒ B →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  ΔR′ ≡ applyTyCtx χ′ ΔR →
  ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ) →
  ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
    ⊢ N ⊒ S′ ∶ pᶦʰ ⦂ applyTys χs A ⊒ applyTy χ′ C →
  ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
    ⊢ N ⊒ S′ ⟨ applyCoercion χ′ t ⟩
      ∶ applyCoercion χ′ (applyCoercions χs r)
      ⦂ applyTys χs A ⊒ applyTy χ′ B
target-cast-minus-inner-step-result {χs} {χ′} {ΔL} {ΔR} {ρ}
    {N = N} {S′ = S′} {p′ = p′} {r = r} {t = t}
    {A = A} {B = B} {C = C} {pᶦʰ = pᶦʰ}
    p′ᶜ r⊒ t⊒ comp refl refl refl ih =
  let
    μih , pᶦʰ⊒ = typed-term-narrowing-coercion ih

    corr = narrowing-store-corrᶜ pᶦʰ⊒

    p₁ᶜ = change-relation-coercion-narrowing χs χ′ corr p′ᶜ

    r₁⊒ = change-relation-coercion-narrowing χs χ′ corr r⊒

    t₁⊒dual = change-target-coercion-narrowing χs χ′ corr t⊒

    comp₁ = change-composed-index χs χ′ comp r₁⊒

    pᶦʰ≡p₁ : pᶦʰ ≡ applyCoercion χ′ (applyCoercions χs p′)
    pᶦʰ≡p₁ = {! inner-step-coercion-index-determined !}

    ih′ :
      applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
        ∣ applyRightChange χ′ (applyLeftChanges χs ρ) ∣ []
        ⊢ N ⊒ S′ ∶ applyCoercion χ′ (applyCoercions χs p′)
          ⦂ applyTys χs A ⊒ applyTy χ′ C
    ih′ =
      subst
        (λ c →
          applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
            ∣ applyRightChange χ′ (applyLeftChanges χs ρ) ∣ []
            ⊢ N ⊒ S′ ∶ c ⦂ applyTys χs A ⊒ applyTy χ′ C)
        pᶦʰ≡p₁
        ih
  in
  ⊒cast-ᵗ p₁ᶜ r₁⊒ (proj₁ t₁⊒dual) comp₁ ih′

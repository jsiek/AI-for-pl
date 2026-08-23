module proof.LR-narrow.ArgumentFrame where

-- File Charter:
--   * The evaluation frame `V · □` for a function value `V`, as an
--     instance of proof.LR-narrow.FramePhases.
--   * Closed application of related function values to related argument
--     computations, by composition under the argument frames.

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (<⇒≤; n≤1+n; ≤-trans)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete)
open import proof.LR-narrow.BetaExpansion using (value-step-none)
open import proof.LR-narrow.Application using
  (apply-change-value; app-argument-step-question; app-stuck-step-none;
   app-blame-step-question; value-unique)
open import proof.LR-narrow.FunctionApplication using
  (related-function-application)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases
open import proof.LR-narrow.FrameComposition

------------------------------------------------------------------------
-- The argument frame of a function value
------------------------------------------------------------------------

record ArgumentFrm (Δ : TyCtx) : Set where
  constructor argument-frm
  field
    function : Term Δ
    function-value : Value function

open ArgumentFrm public

argumentFrame : Frame
argumentFrame = record
  { Frm = ArgumentFrm
  ; plug = λ f M → function f · M
  ; transport = λ χ f →
      argument-frm (χ ▷ᵀ function f)
        (apply-change-value χ (function-value f))
  ; plug-step = λ f step → ξ-·₂ (function-value f) step refl
  ; plug-step? = λ { f {Σ} {χ} {M} {N} {step} step-eq →
      step-question {Σ = Σ} {M = M} {χ = χ} {N = N} {step = step}
        (function-value f) step-eq }
  ; plug-stuck = λ { f {Σ} {M} step-eq value-eq M≢blame →
      app-stuck-step-none {Σ = Σ} {M = M} (function-value f)
        step-eq value-eq M≢blame }
  ; plug-nonvalue = λ f value-eq → refl
  ; plug-not-blame = λ f M ()
  ; plug-blame = λ f → blame-·₂ (function-value f)
  ; plug-blame-step? = λ { f {Σ} → blame-question {Σ = Σ} f }
  }
  where
  step-question : ∀ {Δ Δ′} {Σ : TyStore Δ} {V M : Term Δ}
      {χ : StoreChange Δ Δ′} {N : Term Δ′} {step : M —→[ χ ] N}
    → (vV : Value V)
    → E.step? Σ M ≡ just (E.step-result χ N step)
    → E.step? Σ (V · M) ≡
        just (E.step-result χ ((χ ▷ᵀ V) · N) (ξ-·₂ vV step refl))
  step-question {Σ = Σ} vV step-eq
      with app-argument-step-question {Σ = Σ} vV step-eq
  step-question vV step-eq | vV′ , eq
      rewrite value-unique vV′ vV = eq

  blame-question : ∀ {Δ} {Σ : TyStore Δ} (f : ArgumentFrm Δ)
    → E.step? Σ (function f · blame) ≡
        just (E.step-result keep blame
          (pure-step (blame-·₂ (function-value f))))
  blame-question {Σ = Σ} f
      with app-blame-step-question {Σ = Σ} (function-value f)
  blame-question f | vV′ , eq
      rewrite value-unique vV′ (function-value f) = eq

------------------------------------------------------------------------
-- Closed application to a related argument computation
------------------------------------------------------------------------

open Composition argumentFrame argumentFrame

-- Related function values applied to related argument computations: the
-- arguments evaluate under the argument frames, and the calls are the
-- applications of the lifted functions to the returned values.

transports-function : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
    (V : Term Δ) (vV : Value V)
  → function (Frame.transports argumentFrame χs (argument-frm V vV))
      ≡ χs ▶ᵀ V
transports-function [] V vV = refl
transports-function (χ ∷ χs) V vV =
  transports-function χs (χ ▷ᵀ V) (apply-change-value χ vV)

related-application-computation : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p q) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ · Mᴵ) (Vᴾ · Mᴾ)
related-application-computation {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {W = W} {p = p} {q = q} {k = k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} function-related
    argument-related =
  frame-computations-related
    {R = FutureValueRelation p} {S = FutureValueRelation q}
    (argument-frm Vᴾ vVᴾ) (argument-frm Vᴵ vVᴵ) k Mᴵ Mᴾ
    plug-values argument-related
  where
  endpoints = ClosureProof.value-imprecision-endpoints function-related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  plug-values : PlugValues W (FutureValueRelation p)
      (FutureValueRelation q) k (argument-frm Vᴾ vVᴾ)
      (argument-frm Vᴵ vVᴵ)
  plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = zero} j≤k related =
    ClosureProof.computations-related-zero
  plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = suc j} j≤k {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      related =
    computations-related-future-compose W≼W′ q
      (ClosureProof.computations-related-reindex
        (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
        refl refl
        (cong (_· Uᴵ) (trans (sym (termsᴵ Vᴵ))
          (sym (transports-function χsᴵ Vᴵ vVᴵ))))
        (cong (_· Uᴾ) (trans (sym (termsᴾ Vᴾ))
          (sym (transports-function χsᴾ Vᴾ vVᴾ))))
        (related-function-application
          (ClosureProof.value-imprecision-reindex
            (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p)
              (liftCenterImprecision W≼W′ q))
            (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q))
            (sym (liftCenterTy-arrow W≼W′ Aᴾ Bᴾ))
            (sym (liftCenterTy-arrow W≼W′ Aᴵ Bᴵ))
            (ClosureProof.value-imprecision-future
              {W = W} {p = I.⇒⊑⇒ p q} {k = suc j} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
              W≼W′
              (ClosureProof.value-imprecision-downward-to j≤k
                function-related)))
          related))

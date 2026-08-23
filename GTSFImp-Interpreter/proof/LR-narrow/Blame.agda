module proof.LR-narrow.Blame where

-- File Charter:
--   * Proves compatibility of precise blame against any imprecise term.
--   * Uses immediate blame to discharge both directed observations.
--   * Keeps evaluator impossibility arguments out of the public module.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat using (_∸_; _≤_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
import Imprecision as I
import proof.DGG.CtxImp as CTI
open import Reduction using ([]; ↠-refl)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.TermRelation
open import proof.LR-narrow.ClosingSubstitution using (lift-precise-blame)

blame-now : ∀ {Δ} {Σ : TyStore Δ}
  → BlamesFrom Σ zero (blame {Δ = Δ})
blame-now = _ , [] , ↠-refl , refl

blame-not-returned : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {result : E.EvalResult (blame {Δ = Δ})}
  → interpretFrom Σ gas blame ≡ returned result
  → ⊥
blame-not-returned {gas = zero} ()
blame-not-returned {gas = suc gas} ()

precise-blame-related : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ}
  → ComputationsRelated W R k Mᴵ blame
precise-blame-related {W = W} {R = R} {k = k} {Mᴵ = Mᴵ} = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forwardBlame
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n Mᴵ
        ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult blame ]
          interpretFrom (preciseStore (core W)) m blame
            ≡ returned resultᴾ
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m blame)
  forward n≤k returnᴵ = inj₂
    (zero , blame-now {Σ = preciseStore (core W)})

  backward : ∀ {n} {resultᴾ : E.EvalResult blame}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n blame
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W R (k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤k returnᴾ = ⊥-elim
    (blame-not-returned {Σ = preciseStore (core W)} {gas = n} returnᴾ)

  forwardBlame : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m blame
  forwardBlame n≤k blameᴵ =
    zero , blame-now {Σ = preciseStore (core W)}

blame-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} {Mᴵ : Term Δᴵ}
    (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
  → CompiledTermRelation {W = W} p k Γ blame Mᴵ
blame-compatible {W = W} p W′ W≼W′ γ
    rewrite lift-precise-blame W≼W′ =
  precise-blame-related

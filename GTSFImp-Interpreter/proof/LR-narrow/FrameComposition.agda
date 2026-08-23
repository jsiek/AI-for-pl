module proof.LR-narrow.FrameComposition where

-- File Charter:
--   * Composes related operand computations with related continuations
--     under an abstract evaluation frame on each side: if the operands
--     are related and the frames applied to related returned values
--     yield related computations at every future, then the wrapped
--     computations are related.
--   * Generic over the frames of proof.LR-narrow.FramePhases; the
--     consistency-cast, reveal, and conceal congruences are instances.

open import Data.Nat using (ℕ; _+_; _∸_; _≤_; zero; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.Application using
  (apply-stores-++; apply-terms-++; first-of-two≤;
   drop-left-≤; subtract-phases; return-store-reindex;
   blame-store-reindex; paired-returns-reindex; value-return-exact)
open import proof.LR-narrow.TypeApplication using (returned-injective)
open import proof.LR-narrow.CastComposition using (sum-bound-from-split)
open import proof.LR-narrow.FramePhases

module Composition (Fᴾ Fᴵ : Frame) where
  private
    module P = Frame Fᴾ
    module I = Frame Fᴵ

  ----------------------------------------------------------------------
  -- Assembling paired phase results
  ----------------------------------------------------------------------

  assemble-pair : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx} {W₀ : World Δᴾ Δᴵ Δᶜ}
      {S : IndexedValueRelation W₀}
      {fᴾ : P.Frm Δᴾ} {fᴵ : I.Frm Δᴵ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      {operandResultᴾ : E.EvalResult Mᴾ}
      {operandResultᴵ : E.EvalResult Mᴵ}
      {callResultᴾ : E.EvalResult
        (P.plug (P.transports (E.changes operandResultᴾ) fᴾ)
          (E.term operandResultᴾ))}
      {callResultᴵ : E.EvalResult
        (I.plug (I.transports (E.changes operandResultᴵ) fᴵ)
          (E.term operandResultᴵ))}
      {Δᶜ₁ : TyCtx}
      {W₁ : World (E.Δ′ operandResultᴾ) (E.Δ′ operandResultᴵ) Δᶜ₁}
      {Δᶜ₂ : TyCtx}
      {W₂ : World (E.Δ′ callResultᴾ) (E.Δ′ callResultᴵ) Δᶜ₂}
      {j k : ℕ}
    → (W₀≼W₁ : Future W₀ W₁)
    → impreciseStore (core W₁) ≡
        E.changes operandResultᴵ ▶ˢ impreciseStore (core W₀)
    → preciseStore (core W₁) ≡
        E.changes operandResultᴾ ▶ˢ preciseStore (core W₀)
    → (∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₁ M)
    → (∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₁ M)
    → (W₁≼W₂ : Future W₁ W₂)
    → impreciseStore (core W₂) ≡
        E.changes callResultᴵ ▶ˢ impreciseStore (core W₁)
    → preciseStore (core W₂) ≡
        E.changes callResultᴾ ▶ˢ preciseStore (core W₁)
    → (∀ M → E.changes callResultᴵ ▶ᵀ M ≡
        liftImpreciseTerm W₁≼W₂ M)
    → (∀ M → E.changes callResultᴾ ▶ᵀ M ≡
        liftPreciseTerm W₁≼W₂ M)
    → j ≡ k
    → S W₂ (future-trans W₀≼W₁ W₁≼W₂)
        j (E.term callResultᴵ) (E.term callResultᴾ)
    → PairedReturns W₀ S k
        (I.sequence-result fᴵ operandResultᴵ callResultᴵ)
        (P.sequence-result fᴾ operandResultᴾ callResultᴾ)
  assemble-pair {W₀ = W₀} {fᴾ = fᴾ} {fᴵ = fᴵ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ}
      {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
      {W₁ = W₁} {W₂ = W₂}
      W₀≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      W₁≼W₂ callStoreᴵ callStoreᴾ callTermsᴵ callTermsᴾ refl
      call-related =
    paired-returns W₂ W₀≼W₂ imprecise-store-eq precise-store-eq
      imprecise-terms-eq precise-terms-eq call-related
    where
    W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

    imprecise-store-eq = trans callStoreᴵ
      (trans (cong (λ Σ → E.changes callResultᴵ ▶ˢ Σ) operandStoreᴵ)
        (apply-stores-++ (E.changes operandResultᴵ)
          (E.changes callResultᴵ) (impreciseStore (core W₀))))

    precise-store-eq = trans callStoreᴾ
      (trans (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) operandStoreᴾ)
        (apply-stores-++ (E.changes operandResultᴾ)
          (E.changes callResultᴾ) (preciseStore (core W₀))))

    imprecise-result = I.sequence-result fᴵ operandResultᴵ callResultᴵ
    precise-result = P.sequence-result fᴾ operandResultᴾ callResultᴾ

    imprecise-terms-eq : ∀ M → E.changes imprecise-result ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₂ M
    imprecise-terms-eq M = trans
      (sym (apply-terms-++ (E.changes operandResultᴵ)
        (E.changes callResultᴵ) M))
      (trans
        (cong (λ N → E.changes callResultᴵ ▶ᵀ N)
          (operandTermsᴵ M))
        (trans (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
          (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

    precise-terms-eq : ∀ M → E.changes precise-result ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₂ M
    precise-terms-eq M = trans
      (sym (apply-terms-++ (E.changes operandResultᴾ)
        (E.changes callResultᴾ) M))
      (trans
        (cong (λ N → E.changes callResultᴾ ▶ᵀ N)
          (operandTermsᴾ M))
        (trans (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
          (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  ----------------------------------------------------------------------
  -- The continuation hypothesis
  ----------------------------------------------------------------------

  -- Plugging related returned values into the transported frames gives
  -- related computations, at every future reached by an operand phase.
  PlugValues : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx} (W : World Δᴾ Δᴵ Δᶜ)
    → IndexedValueRelation W → IndexedValueRelation W
    → P.Frm Δᴾ → I.Frm Δᴵ → Set₁
  PlugValues {Δᴾ = Δᴾ} {Δᴵ = Δᴵ} W R S fᴾ fᴵ =
    ∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      {χsᴾ : StoreChanges Δᴾ Δᴾ′} {χsᴵ : StoreChanges Δᴵ Δᴵ′}
    → impreciseStore (core W′) ≡ χsᴵ ▶ˢ impreciseStore (core W)
    → preciseStore (core W′) ≡ χsᴾ ▶ˢ preciseStore (core W)
    → (∀ M → χsᴵ ▶ᵀ M ≡ liftImpreciseTerm W≼W′ M)
    → (∀ M → χsᴾ ▶ᵀ M ≡ liftPreciseTerm W≼W′ M)
    → {j : ℕ} {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → ComputationsRelated W′
        (λ W″ W′≼W″ → S W″ (future-trans W≼W′ W′≼W″)) j
        (I.plug (I.transports χsᴵ fᴵ) Vᴵ)
        (P.plug (P.transports χsᴾ fᴾ) Vᴾ)

  ----------------------------------------------------------------------
  -- Composition
  ----------------------------------------------------------------------

  frame-computations-related : ∀
      {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
      {R S : IndexedValueRelation W}
      (fᴾ : P.Frm Δᴾ) (fᴵ : I.Frm Δᴵ)
      (k : ℕ) (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ)
    → PlugValues W R S fᴾ fᴵ
    → ComputationsRelated W R k Mᴵ Mᴾ
    → ComputationsRelated W S k (I.plug fᴵ Mᴵ) (P.plug fᴾ Mᴾ)
  frame-computations-related {W = W} {S = S} fᴾ fᴵ k Mᴵ Mᴾ
      plug-values operand-related = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = forward-blame-frame
    }
    where
    forward : ∀ {n} {resultᴵ : E.EvalResult (I.plug fᴵ Mᴵ)}
      → n ≤ k
      → interpretFrom (impreciseStore (core W)) n (I.plug fᴵ Mᴵ)
          ≡ returned resultᴵ
      → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult (P.plug fᴾ Mᴾ) ]
            interpretFrom (preciseStore (core W)) m (P.plug fᴾ Mᴾ)
              ≡ returned resultᴾ
            × PairedReturns W S (k ∸ n) resultᴵ resultᴾ)
         ⊎ (Σ[ m ∈ ℕ ]
            BlamesFrom (preciseStore (core W)) m (P.plug fᴾ Mᴾ))
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        with I.return-phases-of {Σ = impreciseStore (core W)} {gas = n}
          fᴵ {M = Mᴵ} {result = resultᴵ} result-eq
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResult operandReturn
            callGas callResult callReturn result-split gas-split
        with forward-return operand-related {n = operandGas}
          {resultᴵ = operandResult} operandGas≤ operandReturn
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k

      operandGas≤ = first-of-two≤
        {a = operandGas} {b = callGas} {k = k} phases≤
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResult operandReturn
            callGas callResult callReturn result-split gas-split
        | inj₂ (preciseOperandGas , preciseOperandBlame)
        with P.operand-blame-expand
          {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
          fᴾ {M = Mᴾ} preciseOperandBlame
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResult operandReturn
            callGas callResult callReturn result-split gas-split
        | inj₂ (preciseOperandGas , preciseOperandBlame)
        | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        with forward-return call-related {n = callGas}
          {resultᴵ = callResultᴵ} callGas≤ callReturn-at-W₁
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k

      callGas≤ = drop-left-≤
        {a = operandGas} {b = callGas} {k = k} phases≤

      callReturn-at-W₁ = return-store-reindex
        {gas = callGas} {result = callResultᴵ}
        operandStoreᴵ callReturn

      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ}
        {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ operandGas}
        {Vᴵ = E.term operandResultᴵ} {Vᴾ = E.term operandResultᴾ}
        operandValueRelated
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₂ (preciseCallGas , preciseCallBlame)
        with P.call-blame-expand
          {Σ = preciseStore (core W)}
          {operandGas = preciseOperandGas} {callGas = preciseCallGas}
          fᴾ {M = Mᴾ} {operandResult = operandResultᴾ}
          preciseOperandReturn
          (blame-store-reindex {gas = preciseCallGas}
            (sym operandStoreᴾ) preciseCallBlame)
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₂ (preciseCallGas , preciseCallBlame)
        | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
            paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
              callTermsᴵ callTermsᴾ callValueRelated)
        with P.return-expand {Σ = preciseStore (core W)}
          {operandGas = preciseOperandGas} {callGas = preciseCallGas}
          fᴾ {M = Mᴾ} {operandResult = operandResultᴾ}
          {callResult = callResultᴾ} preciseOperandReturn
          (return-store-reindex {gas = preciseCallGas}
            {result = callResultᴾ}
            (sym operandStoreᴾ) preciseCallReturn)
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
            paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
              callTermsᴵ callTermsᴾ callValueRelated)
        | wholeGas , wholeReturn =
      inj₁ (wholeGas , P.sequence-result fᴾ operandResultᴾ callResultᴾ ,
        wholeReturn , paired-returns-reindex result-split refl assembled)
      where
      index-eq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      assembled = assemble-pair
        {S = S} {fᴾ = fᴾ} {fᴵ = fᴵ}
        {operandResultᴾ = operandResultᴾ}
        {operandResultᴵ = operandResultᴵ}
        {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
        {j = k ∸ operandGas ∸ callGas} {k = k ∸ n}
        W≼W₁ operandStoreᴵ operandStoreᴾ
        operandTermsᴵ operandTermsᴾ W₁≼W₂ callStoreᴵ callStoreᴾ
        callTermsᴵ callTermsᴾ index-eq callValueRelated

    backward : ∀ {n} {resultᴾ : E.EvalResult (P.plug fᴾ Mᴾ)}
      → n ≤ k
      → interpretFrom (preciseStore (core W)) n (P.plug fᴾ Mᴾ)
          ≡ returned resultᴾ
      → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult (I.plug fᴵ Mᴵ) ]
          interpretFrom (impreciseStore (core W)) m (I.plug fᴵ Mᴵ)
            ≡ returned resultᴵ
          × PairedReturns W S (k ∸ n) resultᴵ resultᴾ
    backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
        with P.return-phases-of {Σ = preciseStore (core W)} {gas = n}
          fᴾ {M = Mᴾ} {result = resultᴾ} result-eq
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        with backward-return operand-related {n = operandGas}
          {resultᴾ = operandResultᴾ} operandGas≤ operandReturn
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k

      operandGas≤ = first-of-two≤
        {a = operandGas} {b = callGas} {k = k} phases≤
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        with backward-return call-related {n = callGas}
          {resultᴾ = callResultᴾ} callGas≤ callReturn-at-W₁
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k

      callGas≤ = drop-left-≤
        {a = operandGas} {b = callGas} {k = k} phases≤
      callReturn-at-W₁ = return-store-reindex
        {gas = callGas} {result = callResultᴾ}
        operandStoreᴾ callReturn

      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ}
        {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ operandGas}
        {Vᴵ = E.term operandResultᴵ} {Vᴾ = E.term operandResultᴾ}
        operandValueRelated
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        | impreciseCallGas , callResultᴵ , impreciseCallReturn ,
            paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
              callTermsᴵ callTermsᴾ callValueRelated
        with I.return-expand {Σ = impreciseStore (core W)}
          {operandGas = impreciseOperandGas}
          {callGas = impreciseCallGas}
          fᴵ {M = Mᴵ} {operandResult = operandResultᴵ}
          {callResult = callResultᴵ} impreciseOperandReturn
          (return-store-reindex {gas = impreciseCallGas}
            {result = callResultᴵ}
            (sym operandStoreᴵ) impreciseCallReturn)
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        | impreciseCallGas , callResultᴵ , impreciseCallReturn ,
            paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
              callTermsᴵ callTermsᴾ callValueRelated
        | wholeGas , wholeReturn =
      wholeGas , I.sequence-result fᴵ operandResultᴵ callResultᴵ ,
      wholeReturn , paired-returns-reindex refl result-split assembled
      where
      index-eq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      assembled = assemble-pair
        {S = S} {fᴾ = fᴾ} {fᴵ = fᴵ}
        {operandResultᴾ = operandResultᴾ}
        {operandResultᴵ = operandResultᴵ}
        {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
        {j = k ∸ operandGas ∸ callGas} {k = k ∸ n}
        W≼W₁ operandStoreᴵ operandStoreᴾ
        operandTermsᴵ operandTermsᴾ W₁≼W₂ callStoreᴵ callStoreᴾ
        callTermsᴵ callTermsᴾ index-eq callValueRelated

    forward-blame-frame : ∀ {n}
      → n ≤ k
      → BlamesFrom (impreciseStore (core W)) n (I.plug fᴵ Mᴵ)
      → Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m (P.plug fᴾ Mᴾ)
    forward-blame-frame {n = n} n≤k blaming
        with I.blame-phases-of {Σ = impreciseStore (core W)} {gas = n}
          fᴵ {M = Mᴵ} blaming
    forward-blame-frame {n = n} n≤k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        with forward-blame operand-related {n = operandGas}
          (≤-trans operandGas≤n n≤k) operandBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        | preciseOperandGas , preciseOperandBlame
        with P.operand-blame-expand
          {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
          fᴾ {M = Mᴾ} preciseOperandBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        | preciseOperandGas , preciseOperandBlame
        | wholeGas , wholeBlame = wholeGas , wholeBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        with forward-return operand-related {n = operandGas}
          {resultᴵ = operandResultᴵ} operandGas≤ operandReturn
      where
      operandGas≤ = first-of-two≤ (≤-trans phases≤n n≤k)
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₂ (preciseOperandGas , preciseOperandBlame)
        with P.operand-blame-expand
          {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
          fᴾ {M = Mᴾ} preciseOperandBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₂ (preciseOperandGas , preciseOperandBlame)
        | wholeGas , wholeBlame = wholeGas , wholeBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        with forward-blame call-related {n = callGas}
          callGas≤ callBlame-at-W₁
      where
      phases≤k = ≤-trans phases≤n n≤k
      callGas≤ = drop-left-≤ phases≤k
      callBlame-at-W₁ = blame-store-reindex {gas = callGas}
        operandStoreᴵ callBlame

      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ}
        {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ operandGas}
        {Vᴵ = E.term operandResultᴵ} {Vᴾ = E.term operandResultᴾ}
        operandValueRelated
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | preciseCallGas , preciseCallBlame
        with P.call-blame-expand
          {Σ = preciseStore (core W)}
          {operandGas = preciseOperandGas} {callGas = preciseCallGas}
          fᴾ {M = Mᴾ} {operandResult = operandResultᴾ}
          preciseOperandReturn
          (blame-store-reindex {gas = preciseCallGas}
            (sym operandStoreᴾ) preciseCallBlame)
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | preciseCallGas , preciseCallBlame
        | wholeGas , wholeBlame = wholeGas , wholeBlame

------------------------------------------------------------------------
-- One-sided composition: a frame on the precise side only
------------------------------------------------------------------------

module PreciseComposition (Fᴾ : Frame) where
  private
    module P = Frame Fᴾ

  assemble-precise-pair : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx} {W₀ : World Δᴾ Δᴵ Δᶜ}
      {S : IndexedValueRelation W₀}
      {fᴾ : P.Frm Δᴾ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      {operandResultᴾ : E.EvalResult Mᴾ}
      {operandResultᴵ : E.EvalResult Mᴵ}
      {callResultᴾ : E.EvalResult
        (P.plug (P.transports (E.changes operandResultᴾ) fᴾ)
          (E.term operandResultᴾ))}
      {Δᶜ₁ : TyCtx}
      {W₁ : World (E.Δ′ operandResultᴾ) (E.Δ′ operandResultᴵ) Δᶜ₁}
      {j k : ℕ}
    → (W₀≼W₁ : Future W₀ W₁)
    → impreciseStore (core W₁) ≡
        E.changes operandResultᴵ ▶ˢ impreciseStore (core W₀)
    → preciseStore (core W₁) ≡
        E.changes operandResultᴾ ▶ˢ preciseStore (core W₀)
    → (∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₁ M)
    → (∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₁ M)
    → PairedReturns W₁
        (λ W₂ W₁≼W₂ → S W₂ (future-trans W₀≼W₁ W₁≼W₂)) j
        (E.result _ [] (E.term operandResultᴵ) ↠-refl
          (E.value operandResultᴵ)) callResultᴾ
    → j ≡ k
    → PairedReturns W₀ S k operandResultᴵ
        (P.sequence-result fᴾ operandResultᴾ callResultᴾ)
  assemble-precise-pair {W₀ = W₀} {fᴾ = fᴾ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ} {callResultᴾ = callResultᴾ}
      W₀≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
        callTermsᴵ callTermsᴾ callRelated) refl =
    paired-returns W₂ W₀≼W₂ imprecise-store-eq precise-store-eq
      imprecise-terms-eq precise-terms-eq callRelated
    where
    W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

    imprecise-store-eq = trans callStoreᴵ operandStoreᴵ

    precise-store-eq = trans callStoreᴾ
      (trans
        (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) operandStoreᴾ)
        (apply-stores-++ (E.changes operandResultᴾ)
          (E.changes callResultᴾ) (preciseStore (core W₀))))

    precise-result = P.sequence-result fᴾ operandResultᴾ callResultᴾ

    imprecise-terms-eq : ∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₂ M
    imprecise-terms-eq M = trans (operandTermsᴵ M)
      (trans
        (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
        (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))

    precise-terms-eq : ∀ M → E.changes precise-result ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₂ M
    precise-terms-eq M = trans
      (sym (apply-terms-++ (E.changes operandResultᴾ)
        (E.changes callResultᴾ) M))
      (trans
        (cong (λ N → E.changes callResultᴾ ▶ᵀ N) (operandTermsᴾ M))
        (trans
          (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
          (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  PrecisePlugValues : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx} (W : World Δᴾ Δᴵ Δᶜ)
    → IndexedValueRelation W → IndexedValueRelation W
    → P.Frm Δᴾ → Set₁
  PrecisePlugValues {Δᴾ = Δᴾ} {Δᴵ = Δᴵ} W R S fᴾ =
    ∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      {χsᴾ : StoreChanges Δᴾ Δᴾ′} {χsᴵ : StoreChanges Δᴵ Δᴵ′}
    → impreciseStore (core W′) ≡ χsᴵ ▶ˢ impreciseStore (core W)
    → preciseStore (core W′) ≡ χsᴾ ▶ˢ preciseStore (core W)
    → (∀ M → χsᴵ ▶ᵀ M ≡ liftImpreciseTerm W≼W′ M)
    → (∀ M → χsᴾ ▶ᵀ M ≡ liftPreciseTerm W≼W′ M)
    → {j : ℕ} {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → ComputationsRelated W′
        (λ W″ W′≼W″ → S W″ (future-trans W≼W′ W′≼W″)) j
        Vᴵ (P.plug (P.transports χsᴾ fᴾ) Vᴾ)

  precise-frame-computations-related : ∀
      {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
      {R S : IndexedValueRelation W}
      (fᴾ : P.Frm Δᴾ)
      (k : ℕ) (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ)
    → PrecisePlugValues W R S fᴾ
    → ComputationsRelated W R k Mᴵ Mᴾ
    → ComputationsRelated W S k Mᴵ (P.plug fᴾ Mᴾ)
  precise-frame-computations-related {W = W} {S = S} fᴾ k Mᴵ Mᴾ
      plug-values operand-related = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = forward-blame-frame
    }
    where
    forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
      → n ≤ k
      → interpretFrom (impreciseStore (core W)) n Mᴵ
          ≡ returned resultᴵ
      → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult (P.plug fᴾ Mᴾ) ]
            interpretFrom (preciseStore (core W)) m (P.plug fᴾ Mᴾ)
              ≡ returned resultᴾ
            × PairedReturns W S (k ∸ n) resultᴵ resultᴾ)
         ⊎ (Σ[ m ∈ ℕ ]
            BlamesFrom (preciseStore (core W)) m (P.plug fᴾ Mᴾ))
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        with forward-return operand-related n≤k result-eq
    forward {n = n} n≤k result-eq
        | inj₂ (preciseOperandGas , preciseOperandBlame)
        with P.operand-blame-expand
          {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
          fᴾ {M = Mᴾ} preciseOperandBlame
    forward {n = n} n≤k result-eq
        | inj₂ (preciseOperandGas , preciseOperandBlame)
        | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        with forward-return call-related z≤n callReturnᴵ
      where
      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ} {χsᴵ = E.changes resultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ n} {Vᴵ = E.term resultᴵ}
        {Vᴾ = E.term operandResultᴾ} operandValueRelated

      callReturnᴵ = value-return-exact
        {Σ = impreciseStore (core W₁)} zero (E.value resultᴵ)
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₂ (preciseCallGas , preciseCallBlame)
        with P.call-blame-expand
          {Σ = preciseStore (core W)}
          {operandGas = preciseOperandGas} {callGas = preciseCallGas}
          fᴾ {M = Mᴾ} {operandResult = operandResultᴾ}
          preciseOperandReturn
          (blame-store-reindex {gas = preciseCallGas}
            (sym operandStoreᴾ) preciseCallBlame)
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₂ (preciseCallGas , preciseCallBlame)
        | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
            callPair)
        with P.return-expand {Σ = preciseStore (core W)}
          {operandGas = preciseOperandGas} {callGas = preciseCallGas}
          fᴾ {M = Mᴾ} {operandResult = operandResultᴾ}
          {callResult = callResultᴾ} preciseOperandReturn
          (return-store-reindex {gas = preciseCallGas}
            {result = callResultᴾ}
            (sym operandStoreᴾ) preciseCallReturn)
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
            callPair)
        | wholeGas , wholeReturn =
      inj₁ (wholeGas , P.sequence-result fᴾ operandResultᴾ callResultᴾ ,
        wholeReturn , assembled)
      where
      assembled : PairedReturns W S (k ∸ n)
        resultᴵ (P.sequence-result fᴾ operandResultᴾ callResultᴾ)
      assembled = assemble-precise-pair
        {S = S} {fᴾ = fᴾ}
        {operandResultᴾ = operandResultᴾ}
        {operandResultᴵ = resultᴵ} {callResultᴾ = callResultᴾ}
        W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        callPair refl

    backward : ∀ {n} {resultᴾ : E.EvalResult (P.plug fᴾ Mᴾ)}
      → n ≤ k
      → interpretFrom (preciseStore (core W)) n (P.plug fᴾ Mᴾ)
          ≡ returned resultᴾ
      → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
          interpretFrom (impreciseStore (core W)) m Mᴵ
            ≡ returned resultᴵ
          × PairedReturns W S (k ∸ n) resultᴵ resultᴾ
    backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
        with P.return-phases-of {Σ = preciseStore (core W)} {gas = n}
          fᴾ {M = Mᴾ} {result = resultᴾ} result-eq
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        with backward-return operand-related {n = operandGas}
          {resultᴾ = operandResultᴾ} operandGas≤ operandReturn
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k

      operandGas≤ = first-of-two≤
        {a = operandGas} {b = callGas} {k = k} phases≤
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        with backward-return call-related {n = callGas}
          {resultᴾ = callResultᴾ} callGas≤ callReturn-at-W₁
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k

      callGas≤ = drop-left-≤
        {a = operandGas} {b = callGas} {k = k} phases≤
      callReturn-at-W₁ = return-store-reindex
        {gas = callGas} {result = callResultᴾ}
        operandStoreᴾ callReturn

      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ}
        {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ operandGas} {Vᴵ = E.term operandResultᴵ}
        {Vᴾ = E.term operandResultᴾ} operandValueRelated
    backward {n = n} n≤k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        | impreciseCallGas , callResultᴵ , impreciseCallReturn ,
            callPair =
      impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
        paired-returns-reindex refl result-split assembled
      where
      exactCallResult = E.result _ [] (E.term operandResultᴵ) ↠-refl
        (E.value operandResultᴵ)

      callResultEq : callResultᴵ ≡ exactCallResult
      callResultEq = returned-injective
        (trans (sym impreciseCallReturn)
          (value-return-exact {Σ = impreciseStore (core W₁)}
            impreciseCallGas (E.value operandResultᴵ)))

      exactCallPair = paired-returns-reindex
        (sym callResultEq) refl callPair

      indexEq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      assembled : PairedReturns W S (k ∸ n)
        operandResultᴵ
        (P.sequence-result fᴾ operandResultᴾ callResultᴾ)
      assembled = assemble-precise-pair
        {S = S} {fᴾ = fᴾ}
        {operandResultᴾ = operandResultᴾ}
        {operandResultᴵ = operandResultᴵ} {callResultᴾ = callResultᴾ}
        W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        exactCallPair indexEq

    forward-blame-frame : ∀ {n}
      → n ≤ k
      → BlamesFrom (impreciseStore (core W)) n Mᴵ
      → Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m (P.plug fᴾ Mᴾ)
    forward-blame-frame {n = n} n≤k blaming
        with forward-blame operand-related n≤k blaming
    forward-blame-frame {n = n} n≤k blaming
        | preciseOperandGas , preciseOperandBlame
        with P.operand-blame-expand
          {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
          fᴾ {M = Mᴾ} preciseOperandBlame
    forward-blame-frame {n = n} n≤k blaming
        | preciseOperandGas , preciseOperandBlame
        | wholeGas , wholeBlame = wholeGas , wholeBlame

------------------------------------------------------------------------
-- One-sided composition: a frame on the imprecise side only
------------------------------------------------------------------------

module ImpreciseComposition (Fᴵ : Frame) where
  private
    module I = Frame Fᴵ

  assemble-imprecise-pair : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx} {W₀ : World Δᴾ Δᴵ Δᶜ}
      {S : IndexedValueRelation W₀}
      {fᴵ : I.Frm Δᴵ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      {operandResultᴾ : E.EvalResult Mᴾ}
      {operandResultᴵ : E.EvalResult Mᴵ}
      {callResultᴵ : E.EvalResult
        (I.plug (I.transports (E.changes operandResultᴵ) fᴵ)
          (E.term operandResultᴵ))}
      {Δᶜ₁ : TyCtx}
      {W₁ : World (E.Δ′ operandResultᴾ) (E.Δ′ operandResultᴵ) Δᶜ₁}
      {j k : ℕ}
    → (W₀≼W₁ : Future W₀ W₁)
    → impreciseStore (core W₁) ≡
        E.changes operandResultᴵ ▶ˢ impreciseStore (core W₀)
    → preciseStore (core W₁) ≡
        E.changes operandResultᴾ ▶ˢ preciseStore (core W₀)
    → (∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₁ M)
    → (∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₁ M)
    → PairedReturns W₁
        (λ W₂ W₁≼W₂ → S W₂ (future-trans W₀≼W₁ W₁≼W₂)) j
        callResultᴵ
        (E.result _ [] (E.term operandResultᴾ) ↠-refl
          (E.value operandResultᴾ))
    → j ≡ k
    → PairedReturns W₀ S k
        (I.sequence-result fᴵ operandResultᴵ callResultᴵ)
        operandResultᴾ
  assemble-imprecise-pair {W₀ = W₀} {fᴵ = fᴵ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ} {callResultᴵ = callResultᴵ}
      W₀≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
        callTermsᴵ callTermsᴾ callRelated) refl =
    paired-returns W₂ W₀≼W₂ imprecise-store-eq precise-store-eq
      imprecise-terms-eq precise-terms-eq callRelated
    where
    W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

    imprecise-store-eq = trans callStoreᴵ
      (trans
        (cong (λ Σ → E.changes callResultᴵ ▶ˢ Σ) operandStoreᴵ)
        (apply-stores-++ (E.changes operandResultᴵ)
          (E.changes callResultᴵ) (impreciseStore (core W₀))))

    precise-store-eq = trans callStoreᴾ operandStoreᴾ

    imprecise-result = I.sequence-result fᴵ operandResultᴵ callResultᴵ

    imprecise-terms-eq : ∀ M → E.changes imprecise-result ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₂ M
    imprecise-terms-eq M = trans
      (sym (apply-terms-++ (E.changes operandResultᴵ)
        (E.changes callResultᴵ) M))
      (trans
        (cong (λ N → E.changes callResultᴵ ▶ᵀ N) (operandTermsᴵ M))
        (trans
          (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
          (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

    precise-terms-eq : ∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₂ M
    precise-terms-eq M = trans (operandTermsᴾ M)
      (trans
        (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
        (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))

  ImprecisePlugValues : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx} (W : World Δᴾ Δᴵ Δᶜ)
    → IndexedValueRelation W → IndexedValueRelation W
    → I.Frm Δᴵ → Set₁
  ImprecisePlugValues {Δᴾ = Δᴾ} {Δᴵ = Δᴵ} W R S fᴵ =
    ∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      {χsᴾ : StoreChanges Δᴾ Δᴾ′} {χsᴵ : StoreChanges Δᴵ Δᴵ′}
    → impreciseStore (core W′) ≡ χsᴵ ▶ˢ impreciseStore (core W)
    → preciseStore (core W′) ≡ χsᴾ ▶ˢ preciseStore (core W)
    → (∀ M → χsᴵ ▶ᵀ M ≡ liftImpreciseTerm W≼W′ M)
    → (∀ M → χsᴾ ▶ᵀ M ≡ liftPreciseTerm W≼W′ M)
    → {j : ℕ} {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → ComputationsRelated W′
        (λ W″ W′≼W″ → S W″ (future-trans W≼W′ W′≼W″)) j
        (I.plug (I.transports χsᴵ fᴵ) Vᴵ) Vᴾ

  imprecise-frame-computations-related : ∀
      {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
      {R S : IndexedValueRelation W}
      (fᴵ : I.Frm Δᴵ)
      (k : ℕ) (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ)
    → ImprecisePlugValues W R S fᴵ
    → ComputationsRelated W R k Mᴵ Mᴾ
    → ComputationsRelated W S k (I.plug fᴵ Mᴵ) Mᴾ
  imprecise-frame-computations-related {W = W} {S = S} fᴵ k Mᴵ Mᴾ
      plug-values operand-related = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = forward-blame-frame
    }
    where
    forward : ∀ {n} {resultᴵ : E.EvalResult (I.plug fᴵ Mᴵ)}
      → n ≤ k
      → interpretFrom (impreciseStore (core W)) n (I.plug fᴵ Mᴵ)
          ≡ returned resultᴵ
      → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
            interpretFrom (preciseStore (core W)) m Mᴾ
              ≡ returned resultᴾ
            × PairedReturns W S (k ∸ n) resultᴵ resultᴾ)
         ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
        with I.return-phases-of {Σ = impreciseStore (core W)} {gas = n}
          fᴵ {M = Mᴵ} {result = resultᴵ} result-eq
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        with forward-return operand-related {n = operandGas}
          {resultᴵ = operandResultᴵ} operandGas≤ operandReturn
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k
      operandGas≤ = first-of-two≤
        {a = operandGas} {b = callGas} {k = k} phases≤
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₂ (preciseOperandGas , preciseOperandBlame) =
      inj₂ (preciseOperandGas , preciseOperandBlame)
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        with forward-return call-related {n = callGas}
          {resultᴵ = callResultᴵ} callGas≤ callReturn-at-W₁
      where
      phases≤ : operandGas + callGas ≤ k
      phases≤ = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n≤k
      callGas≤ = drop-left-≤
        {a = operandGas} {b = callGas} {k = k} phases≤

      callReturn-at-W₁ = return-store-reindex {gas = callGas}
        {result = callResultᴵ} operandStoreᴵ callReturn

      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ}
        {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ operandGas} {Vᴵ = E.term operandResultᴵ}
        {Vᴾ = E.term operandResultᴾ} operandValueRelated
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₂ (preciseCallGas , Δ′ , changes , trace , preciseCallBlame)
        with trans
          (sym (value-return-exact {Σ = preciseStore (core W₁)}
            preciseCallGas (E.value operandResultᴾ))) preciseCallBlame
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₂ (preciseCallGas , Δ′ , changes , trace , preciseCallBlame)
        | ()
    forward {n = n} n≤k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
            callPair) =
      inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
        paired-returns-reindex result-split refl assembled)
      where
      exactCallResult = E.result _ [] (E.term operandResultᴾ) ↠-refl
        (E.value operandResultᴾ)

      callResultEq : callResultᴾ ≡ exactCallResult
      callResultEq = returned-injective
        (trans (sym preciseCallReturn)
          (value-return-exact {Σ = preciseStore (core W₁)}
            preciseCallGas (E.value operandResultᴾ)))

      exactCallPair = paired-returns-reindex refl (sym callResultEq)
        callPair
      indexEq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      assembled : PairedReturns W S (k ∸ n)
        (I.sequence-result fᴵ operandResultᴵ callResultᴵ)
        operandResultᴾ
      assembled = assemble-imprecise-pair
        {S = S} {fᴵ = fᴵ} {operandResultᴾ = operandResultᴾ}
        {operandResultᴵ = operandResultᴵ} {callResultᴵ = callResultᴵ}
        W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        exactCallPair indexEq

    backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
      → n ≤ k
      → interpretFrom (preciseStore (core W)) n Mᴾ
          ≡ returned resultᴾ
      → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult (I.plug fᴵ Mᴵ) ]
          interpretFrom (impreciseStore (core W)) m (I.plug fᴵ Mᴵ)
            ≡ returned resultᴵ
          × PairedReturns W S (k ∸ n) resultᴵ resultᴾ
    backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
        with backward-return operand-related n≤k result-eq
    backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        with backward-return call-related {n = zero} z≤n callReturnᴾ
      where
      call-related = plug-values W≼W₁
        {χsᴾ = E.changes resultᴾ} {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ n} {Vᴵ = E.term operandResultᴵ}
        {Vᴾ = E.term resultᴾ} operandValueRelated

      callReturnᴾ = value-return-exact
        {Σ = preciseStore (core W₁)} zero (E.value resultᴾ)
    backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        | impreciseCallGas , callResultᴵ , impreciseCallReturn , callPair
        with I.return-expand {Σ = impreciseStore (core W)}
          {operandGas = impreciseOperandGas}
          {callGas = impreciseCallGas}
          fᴵ {M = Mᴵ} {operandResult = operandResultᴵ}
          {callResult = callResultᴵ} impreciseOperandReturn
          (return-store-reindex {gas = impreciseCallGas}
            {result = callResultᴵ} (sym operandStoreᴵ)
            impreciseCallReturn)
    backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
        | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated
        | impreciseCallGas , callResultᴵ , impreciseCallReturn , callPair
        | wholeGas , wholeReturn =
      wholeGas , I.sequence-result fᴵ operandResultᴵ callResultᴵ ,
        wholeReturn , assembled
      where
      assembled : PairedReturns W S (k ∸ n)
        (I.sequence-result fᴵ operandResultᴵ callResultᴵ) resultᴾ
      assembled = assemble-imprecise-pair
        {S = S} {fᴵ = fᴵ} {operandResultᴾ = resultᴾ}
        {operandResultᴵ = operandResultᴵ} {callResultᴵ = callResultᴵ}
        W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        callPair refl

    forward-blame-frame : ∀ {n}
      → n ≤ k
      → BlamesFrom (impreciseStore (core W)) n (I.plug fᴵ Mᴵ)
      → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
    forward-blame-frame {n = n} n≤k blaming
        with I.blame-phases-of {Σ = impreciseStore (core W)} {gas = n}
          fᴵ {M = Mᴵ} blaming
    forward-blame-frame {n = n} n≤k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n =
      forward-blame operand-related (≤-trans operandGas≤n n≤k)
        operandBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        with forward-return operand-related {n = operandGas}
          {resultᴵ = operandResultᴵ} operandGas≤ operandReturn
      where
      operandGas≤ = first-of-two≤
        {a = operandGas} {b = callGas} {k = k}
        (≤-trans phases≤n n≤k)
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₂ (preciseOperandGas , preciseOperandBlame) =
      preciseOperandGas , preciseOperandBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        with forward-blame call-related {n = callGas}
          callGas≤ callBlame-at-W₁
      where
      phases≤k = ≤-trans phases≤n n≤k
      callGas≤ = drop-left-≤
        {a = operandGas} {b = callGas} {k = k} phases≤k
      callBlame-at-W₁ = blame-store-reindex {gas = callGas}
        operandStoreᴵ callBlame

      call-related = plug-values W≼W₁
        {χsᴾ = E.changes operandResultᴾ}
        {χsᴵ = E.changes operandResultᴵ}
        operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
        {j = k ∸ operandGas} {Vᴵ = E.term operandResultᴵ}
        {Vᴾ = E.term operandResultᴾ} operandValueRelated
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | preciseCallGas , Δ′ , changes , trace , preciseCallBlame
        with trans
          (sym (value-return-exact {Σ = preciseStore (core W₁)}
            preciseCallGas (E.value operandResultᴾ))) preciseCallBlame
    forward-blame-frame {n = n} n≤k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (preciseOperandGas , operandResultᴾ ,
            preciseOperandReturn ,
            paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
              operandTermsᴵ operandTermsᴾ operandValueRelated)
        | preciseCallGas , Δ′ , changes , trace , preciseCallBlame
        | ()

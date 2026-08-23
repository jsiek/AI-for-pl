module proof.LR-narrow.Primitive where

-- File Charter:
--   * Proves compatibility of strict binary primitive operations.
--   * Decomposes evaluation into left, right, and delta phases.
--   * Reuses generic evaluator and future-world composition infrastructure.


open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Bool using (false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-assoc; m∸n≤m)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.TermSubstitution using (subst-cong)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import Reduction
import Eval as E
open import Interpreter
import Imprecision as I
import GradualTermImprecision as GTI
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.FunctionApplication
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete; value-eval; value-return;
   related-values-return)
open import proof.LR-narrow.BetaExpansion using
  (value-step-none; interpreter-outcome; interpret-from-eval)
open import proof.LR-narrow.Constant using (constant-values-related)
open import proof.LR-narrow.StepExpansion using (related-pure-step-expand)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
import proof.LR-narrow.Closure as ClosureProof
import proof.LR-narrow.ClosingSubstitution as ClosingProof
open import Primitives
open import proof.LR-narrow.Application hiding
  (app-blame-not-returned; app-blame-step-question; app-final-left-none;
   app-final-none; app-stuck-step-none; app-value-final-none;
   blame-from-eval; eval-app-stuck-none; eval-from-blame; prepend-blamed)

lift-imprecise-prim : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (op : Prim) (L M : Term Δᴵ₀)
  → liftImpreciseTerm W₀≼W₁ (L ⊕[ op ] M) ≡
      liftImpreciseTerm W₀≼W₁ L ⊕[ op ] liftImpreciseTerm W₀≼W₁ M
lift-imprecise-prim future-refl op L M = refl
lift-imprecise-prim (future-paired W₀≼W₁ related fresh) op L M
    rewrite lift-imprecise-prim W₀≼W₁ op L M = refl
lift-imprecise-prim (future-precise W₀≼W₁ fresh) op L M =
  lift-imprecise-prim W₀≼W₁ op L M
lift-imprecise-prim (future-imprecise W₀≼W₁) op L M
    rewrite lift-imprecise-prim W₀≼W₁ op L M = refl

lift-precise-prim : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (op : Prim) (L M : Term Δᴾ₀)
  → liftPreciseTerm W₀≼W₁ (L ⊕[ op ] M) ≡
      liftPreciseTerm W₀≼W₁ L ⊕[ op ] liftPreciseTerm W₀≼W₁ M
lift-precise-prim future-refl op L M = refl
lift-precise-prim (future-paired W₀≼W₁ related fresh) op L M
    rewrite lift-precise-prim W₀≼W₁ op L M = refl
lift-precise-prim (future-precise W₀≼W₁ fresh) op L M
    rewrite lift-precise-prim W₀≼W₁ op L M = refl
lift-precise-prim (future-imprecise W₀≼W₁) op L M =
  lift-precise-prim W₀≼W₁ op L M

positive-prim-values : ∀
    {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (op : Prim)
    {k : ℕ} {Vᴵ Uᴵ : Term Δᴵ} {Vᴾ Uᴾ : Term Δᴾ}
  → suc zero ≤ k
  → ValueImprecision W (GTI.primResultTy-⊑ (impEnv (core W)) op)
      k Vᴵ Vᴾ
  → ValueImprecision W (GTI.primResultTy-⊑ (impEnv (core W)) op)
      k Uᴵ Uᴾ
  → ComputationsRelated W
      (FutureValueRelation
        (GTI.primResultTy-⊑ (impEnv (core W)) op)) k
      (Vᴵ ⊕[ op ] Uᴵ) (Vᴾ ⊕[ op ] Uᴾ)
positive-prim-values addℕ {k = zero} () left right
positive-prim-values {W = W} addℕ
    {k = suc k} positive
    (left-endpoints , same-natural m)
    (right-endpoints , same-natural n) =
  related-pure-step-expand (λ ()) (λ ()) refl refl
    (δ-⊕ δ-add) (δ-⊕ δ-add) refl refl
    (related-values-return ($ (κℕ (m + n))) ($ (κℕ (m + n)))
      (λ j j≤k → constant-values-related {W = W} j (κℕ (m + n))))
positive-prim-values and𝔹 {k = zero} () left right
positive-prim-values {W = W} and𝔹
    {k = suc k} positive
    (left-endpoints , same-boolean b)
    (right-endpoints , same-boolean c) =
  related-pure-step-expand (λ ()) (λ ()) refl refl
    (δ-⊕ δ-and) (δ-⊕ δ-and) refl refl
    (related-values-return ($ (κ𝔹 (b ∧ c))) ($ (κ𝔹 (b ∧ c)))
      (λ j j≤k → constant-values-related {W = W} j (κ𝔹 (b ∧ c))))

sequential-center-constant : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ Δᴾ₃ Δᴵ₃ Δᶜ₃}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₃ : World Δᴾ₃ Δᴵ₃ Δᶜ₃}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (W₂≼W₃ : Future W₂ W₃) (κ : Const)
  → liftCenterTy W₂≼W₃
      (liftCenterTy W₁≼W₂ (liftCenterTy W₀≼W₁ (constTy κ))) ≡
      constTy κ
sequential-center-constant W₀≼W₁ W₁≼W₂ W₂≼W₃ κ = trans
  (cong (liftCenterTy W₂≼W₃)
    (trans (cong (liftCenterTy W₁≼W₂)
      (liftCenterTy-constant W₀≼W₁ κ))
      (liftCenterTy-constant W₁≼W₂ κ)))
  (liftCenterTy-constant W₂≼W₃ κ)

sequential-prim-value-reindex : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ Δᴾ₃ Δᴵ₃ Δᶜ₃}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₃ : World Δᴾ₃ Δᴵ₃ Δᶜ₃}
    (op : Prim)
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (W₂≼W₃ : Future W₂ W₃)
    {p : primArgTy {Δᴾ₀} op ⊑ᵂ⟨ core W₀ ⟩
      primArgTy {Δᴵ₀} op}
    {k : ℕ} {Vᴵ : Term Δᴵ₃} {Vᴾ : Term Δᴾ₃}
  → ValueImprecision W₃
      (liftCenterImprecision W₂≼W₃
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ p))) k Vᴵ Vᴾ
  → ValueImprecision W₃
      (GTI.primResultTy-⊑ (impEnv (core W₃)) op) k Vᴵ Vᴾ
sequential-prim-value-reindex {W₃ = W₃}
    addℕ W₀≼W₁ W₁≼W₂ W₂≼W₃
    {p = I.ι⊑ι} related =
  ClosureProof.value-imprecision-reindex
    (GTI.primResultTy-⊑ (impEnv (core W₃)) addℕ)
    (liftCenterImprecision W₂≼W₃
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ I.ι⊑ι)))
    (sym eq) (sym eq) related
  where
  eq = sequential-center-constant W₀≼W₁ W₁≼W₂ W₂≼W₃
    (κℕ zero)
sequential-prim-value-reindex {W₃ = W₃}
    and𝔹 W₀≼W₁ W₁≼W₂ W₂≼W₃
    {p = I.ι⊑ι} related =
  ClosureProof.value-imprecision-reindex
    (GTI.primResultTy-⊑ (impEnv (core W₃)) and𝔹)
    (liftCenterImprecision W₂≼W₃
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ I.ι⊑ι)))
    (sym eq) (sym eq) related
  where
  eq = sequential-center-constant W₀≼W₁ W₁≼W₂ W₂≼W₃
    (κ𝔹 false)

sequential-prim-computations-reindex : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ Δᴾ₃ Δᴵ₃ Δᶜ₃}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₃ : World Δᴾ₃ Δᴵ₃ Δᶜ₃}
    (op : Prim)
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (W₂≼W₃ : Future W₂ W₃)
    {q : primResultTy {Δᴾ₀} op ⊑ᵂ⟨ core W₀ ⟩
      primResultTy {Δᴵ₀} op}
    {k : ℕ} {Mᴵ : Term Δᴵ₃} {Mᴾ : Term Δᴾ₃}
  → ComputationsRelated W₃
      (FutureValueRelation
        (GTI.primResultTy-⊑ (impEnv (core W₃)) op)) k Mᴵ Mᴾ
  → ComputationsRelated W₃
      (FutureValueRelation
        (liftCenterImprecision W₂≼W₃
          (liftCenterImprecision W₁≼W₂
            (liftCenterImprecision W₀≼W₁ q)))) k Mᴵ Mᴾ
sequential-prim-computations-reindex {W₃ = W₃} addℕ
    W₀≼W₁ W₁≼W₂ W₂≼W₃ {q = I.ι⊑ι} related =
  ClosureProof.computations-related-reindex
    (GTI.primResultTy-⊑ (impEnv (core W₃)) addℕ)
    (liftCenterImprecision W₂≼W₃
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ I.ι⊑ι)))
    (sym eq) (sym eq) refl refl related
  where
  eq = sequential-center-constant W₀≼W₁ W₁≼W₂ W₂≼W₃
    (κℕ zero)
sequential-prim-computations-reindex {W₃ = W₃} and𝔹
    W₀≼W₁ W₁≼W₂ W₂≼W₃ {q = I.ι⊑ι} related =
  ClosureProof.computations-related-reindex
    (GTI.primResultTy-⊑ (impEnv (core W₃)) and𝔹)
    (liftCenterImprecision W₂≼W₃
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ I.ι⊑ι)))
    (sym eq) (sym eq) refl refl related
  where
  eq = sequential-center-constant W₀≼W₁ W₁≼W₂ W₂≼W₃
    (κ𝔹 false)

module ForPrimitive (op : Prim) where

    prim-left-trace : ∀ {Δ₀ Δ₁}
        {L : Term Δ₀} {V : Term Δ₁} {M : Term Δ₀}
        {χs : StoreChanges Δ₀ Δ₁}
      → L —↠[ χs ] V
      → L ⊕[ op ] M —↠[ χs ] V ⊕[ op ] (χs ▶ᵀ M)
    prim-left-trace ↠-refl = ↠-refl
    prim-left-trace {M = M}
        (↠-step {χ = χ} L→N N↠V) =
      ↠-step (ξ-⊕₁ L→N refl)
        (prim-left-trace {M = χ ▷ᵀ M} N↠V)

    prim-right-trace : ∀ {Δ₀ Δ₁}
        {V M : Term Δ₀} {U : Term Δ₁}
        {χs : StoreChanges Δ₀ Δ₁}
      → (vV : Value V)
      → M —↠[ χs ] U
      → V ⊕[ op ] M —↠[ χs ] (χs ▶ᵀ V) ⊕[ op ] U
    prim-right-trace vV ↠-refl = ↠-refl
    prim-right-trace {V = V}
        vV (↠-step {χ = χ} M→N N↠U) =
      ↠-step (ξ-⊕₂ vV M→N refl)
        (prim-right-trace (apply-change-value χ vV) N↠U)

    sequence-right-result : ∀ {Δ₀} {V M : Term Δ₀}
      → Value V
      → (rightResult : E.EvalResult M)
      → E.EvalResult
          ((E.changes rightResult ▶ᵀ V) ⊕[ op ] E.term rightResult)
      → E.EvalResult (V ⊕[ op ] M)
    sequence-right-result vV
        (E.result Δ₁ χs U M↠U vU)
        (E.result Δ₂ ψs Z delta↠Z vZ) =
      E.result Δ₂ (χs ++ˢ ψs) Z
        (append-trace (prim-right-trace vV M↠U) delta↠Z) vZ

    sequence-right-result-value-cong : ∀ {Δ} {V M : Term Δ}
        {vV vV′ : Value V} {rightResult : E.EvalResult M}
        {deltaResult : E.EvalResult
          ((E.changes rightResult ▶ᵀ V) ⊕[ op ] E.term rightResult)}
      → vV ≡ vV′
      → sequence-right-result vV rightResult deltaResult ≡
          sequence-right-result vV′ rightResult deltaResult
    sequence-right-result-value-cong refl = refl

    sequence-prim-result : ∀ {Δ₀} {L M : Term Δ₀}
      → (leftResult : E.EvalResult L)
      → (rightResult :
          E.EvalResult (E.changes leftResult ▶ᵀ M))
      → E.EvalResult
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult)
      → E.EvalResult (L ⊕[ op ] M)
    sequence-prim-result
        (E.result Δ₁ χs V L↠V vV)
        (E.result Δ₂ ψs U M↠U vU)
        (E.result Δ₃ θs Z delta↠Z vZ) =
      E.result Δ₃ (χs ++ˢ (ψs ++ˢ θs)) Z
        (append-trace (prim-left-trace L↠V)
          (append-trace (prim-right-trace vV M↠U) delta↠Z))
        vZ

    eval-prim-prepend-return : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {L M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
        {gas : ℕ} {step : L ⊕[ op ] M —→[ χ ] N}
        {next-result : E.EvalResult N}
      → E.step? Σ (L ⊕[ op ] M) ≡ just (E.step-result χ N step)
      → E.evalFrom (χ ▷ˢ Σ) gas N ≡ just (E.returned next-result)
      → E.evalFrom Σ (suc gas) (L ⊕[ op ] M) ≡
          just (E.returned (prepend-result step next-result))
    eval-prim-prepend-return step-eq next-eq
        rewrite step-eq | next-eq = refl

    app-right-step-question : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {V M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
        {step : M —→[ χ ] N}
      → (vV : Value V)
      → E.step? Σ M ≡ just (E.step-result χ N step)
      → Σ[ vV′ ∈ Value V ]
          E.step? Σ (V ⊕[ op ] M) ≡
            just (E.step-result χ ((χ ▷ᵀ V) ⊕[ op ] N)
              (ξ-⊕₂ vV′ step refl))
    app-right-step-question {Σ = Σ} {V = V} {M = M}
        {χ = χ} {N = N} vV right-step-eq
        with value-question-complete vV | value-step-none {Σ = Σ} vV
    app-right-step-question vV right-step-eq
        | vV′ , value-eq | left-step-eq
        rewrite left-step-eq | right-step-eq | value-eq =
      vV′ , refl

    right-return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
        {rightGas deltaGas : ℕ} {V M : Term Δ}
        {rightResult : E.EvalResult M}
        {deltaResult : E.EvalResult
          ((E.changes rightResult ▶ᵀ V) ⊕[ op ] E.term rightResult)}
      → (vV : Value V)
      → E.evalFrom Σ rightGas M ≡ just (E.returned rightResult)
      → E.evalFrom (E.changes rightResult ▶ˢ Σ) deltaGas
          ((E.changes rightResult ▶ᵀ V) ⊕[ op ] E.term rightResult)
          ≡ just (E.returned deltaResult)
      → Σ[ wholeGas ∈ ℕ ]
          E.evalFrom Σ wholeGas (V ⊕[ op ] M) ≡
            just (E.returned
              (sequence-right-result vV rightResult deltaResult))
    right-return-expand-eval {Σ = Σ} {rightGas = zero}
        {deltaGas = deltaGas} {V = V} {M = M} vV right-eq delta-eq
        with blame-view M
    right-return-expand-eval vV right-eq delta-eq
        | is-blame refl with right-eq
    right-return-expand-eval vV right-eq delta-eq
        | is-blame refl | ()
    right-return-expand-eval {Σ = Σ} {rightGas = zero}
        {deltaGas = deltaGas} {V = V} {M = M}
        {rightResult = rightResult} vV right-eq delta-eq
        | not-blame M≢blame
        with E.value? M in right-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
               {M = M} M≢blame)) right-eq
    right-return-expand-eval {deltaGas = deltaGas} vV right-eq delta-eq
        | not-blame M≢blame | just vM | refl = deltaGas , delta-eq
    right-return-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | ()
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        {rightResult = rightResult} vV right-eq delta-eq
        with blame-view M
    right-return-expand-eval vV right-eq delta-eq
        | is-blame refl with right-eq
    right-return-expand-eval vV right-eq delta-eq
        | is-blame refl | ()
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        {rightResult = rightResult} vV right-eq delta-eq
        | not-blame M≢blame
        with E.value? M in right-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ}
               {gas = suc rightGas} {M = M} M≢blame)) right-eq
    right-return-expand-eval {deltaGas = deltaGas} vV right-eq delta-eq
        | not-blame M≢blame | just vM | refl = deltaGas , delta-eq
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        {rightResult = rightResult} vV right-eq delta-eq
        | not-blame M≢blame | nothing | normalized-eq
        with E.step? Σ M in right-step-eq
    right-return-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | () | nothing
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        {rightResult = rightResult} vV right-eq delta-eq
        | not-blame M≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) rightGas N in next-eq
    right-return-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | ()
        | just (E.step-result χ N step) | nothing
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        {rightResult = rightResult} vV right-eq delta-eq
        | not-blame M≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        | just (E.returned next-result)
        with normalized-eq
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        vV right-eq delta-eq
        | not-blame M≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        with right-return-expand-eval {Σ = χ ▷ˢ Σ}
          {rightGas = rightGas} {deltaGas = deltaGas}
          {V = χ ▷ᵀ V} {M = N} {rightResult = next-result}
          (apply-change-value χ vV) next-eq delta-eq
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        vV right-eq delta-eq
        | not-blame M≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        | wholeGas , whole-eq
        with app-right-step-question {Σ = Σ} vV right-step-eq
    right-return-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M}
        vV right-eq delta-eq
        | not-blame M≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        | wholeGas , whole-eq | vV′ , prim-step-eq
        rewrite value-unique vV′ vV =
      suc wholeGas ,
      eval-prim-prepend-return {Σ = Σ} prim-step-eq whole-eq
    right-return-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | ()
        | just (E.step-result χ N step)
        | just (E.blamed changes trace)

    app-left-step-question : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {L M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
        {step : L —→[ χ ] N}
      → E.step? Σ L ≡ just (E.step-result χ N step)
      → E.step? Σ (L ⊕[ op ] M) ≡
          just (E.step-result χ (N ⊕[ op ] (χ ▷ᵀ M))
            (ξ-⊕₁ step refl))
    app-left-step-question left-step-eq
        rewrite left-step-eq = refl

    prim-return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
        {leftGas rightGas deltaGas : ℕ} {L M : Term Δ}
        {leftResult : E.EvalResult L}
        {rightResult : E.EvalResult
          (E.changes leftResult ▶ᵀ M)}
        {deltaResult : E.EvalResult
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult)}
      → E.evalFrom Σ leftGas L ≡ just (E.returned leftResult)
      → E.evalFrom (E.changes leftResult ▶ˢ Σ) rightGas
          (E.changes leftResult ▶ᵀ M) ≡
            just (E.returned rightResult)
      → E.evalFrom
          (E.changes rightResult ▶ˢ
            (E.changes leftResult ▶ˢ Σ)) deltaGas
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult) ≡ just (E.returned deltaResult)
      → Σ[ wholeGas ∈ ℕ ]
          E.evalFrom Σ wholeGas (L ⊕[ op ] M) ≡
            just (E.returned
              (sequence-prim-result leftResult rightResult
                deltaResult))
    prim-return-expand-eval {Σ = Σ} {leftGas = zero}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq right-eq delta-eq
        with blame-view L
    prim-return-expand-eval left-eq right-eq delta-eq
        | is-blame refl with left-eq
    prim-return-expand-eval left-eq right-eq delta-eq
        | is-blame refl | ()
    prim-return-expand-eval {Σ = Σ} {leftGas = zero}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq right-eq delta-eq
        | not-blame L≢blame
        with E.value? L in left-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
               {M = L} L≢blame)) left-eq
    prim-return-expand-eval {Σ = Σ} {rightGas = rightGas}
        {deltaGas = deltaGas} left-eq right-eq delta-eq
        | not-blame L≢blame | just vL | refl =
      right-return-expand-eval {Σ = Σ} {rightGas = rightGas}
        {deltaGas = deltaGas} vL right-eq delta-eq
    prim-return-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | ()
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq right-eq delta-eq
        with blame-view L
    prim-return-expand-eval left-eq right-eq delta-eq
        | is-blame refl with left-eq
    prim-return-expand-eval left-eq right-eq delta-eq
        | is-blame refl | ()
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq right-eq delta-eq
        | not-blame L≢blame
        with E.value? L in left-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ}
               {gas = suc leftGas} {M = L} L≢blame)) left-eq
    prim-return-expand-eval {Σ = Σ} {rightGas = rightGas}
        {deltaGas = deltaGas} left-eq right-eq delta-eq
        | not-blame L≢blame | just vL | refl =
      right-return-expand-eval {Σ = Σ} {rightGas = rightGas}
        {deltaGas = deltaGas} vL right-eq delta-eq
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | normalized-eq
        with E.step? Σ L in left-step-eq
    prim-return-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | () | nothing
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) leftGas N in next-eq
    prim-return-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | ()
        | just (E.step-result χ N step) | nothing
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        | just (E.returned next-result)
        with normalized-eq
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        with prim-return-expand-eval {Σ = χ ▷ˢ Σ}
          {leftGas = leftGas} {rightGas = rightGas}
          {deltaGas = deltaGas} {L = N} {M = χ ▷ᵀ M}
          next-eq right-eq delta-eq
    prim-return-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        | wholeGas , whole-eq =
      suc wholeGas , eval-prim-prepend-return {Σ = Σ}
        (app-left-step-question {Σ = Σ} left-step-eq) whole-eq
    prim-return-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | ()
        | just (E.step-result χ N step)
        | just (E.blamed changes trace)

    record RightReturnPhases {Δ : TyCtx}
        (Σ : TyStore Δ) (gas : ℕ) (V M : Term Δ)
        (wholeResult : E.EvalResult (V ⊕[ op ] M)) : Set where
      constructor right-return-phases-record
      field
        rightLeftValue′ : Value V

        rightGas′ : ℕ
        rightResult′ : E.EvalResult M
        rightReturn′ :
          interpretFrom Σ rightGas′ M ≡ returned rightResult′

        deltaGas′ : ℕ
        deltaResult′ : E.EvalResult
          ((E.changes rightResult′ ▶ᵀ V) ⊕[ op ] E.term rightResult′)
        deltaReturn′ :
          interpretFrom (E.changes rightResult′ ▶ˢ Σ) deltaGas′
            ((E.changes rightResult′ ▶ᵀ V)
              ⊕[ op ] E.term rightResult′) ≡ returned deltaResult′

        right-result-splits : wholeResult ≡
          sequence-right-result rightLeftValue′ rightResult′
            deltaResult′

        right-gas-splits : rightGas′ + deltaGas′ ≡ gas

    open RightReturnPhases public

    app-value-final-none : ∀ {Δ : TyCtx} {V M : Term Δ}
        (vV : Value V)
      → M ≢ blame
      → E.value? M ≡ nothing
      → E.prim-value-final? op vV M ≡ nothing
    app-value-final-none {M = ` x} vV M≢blame eq = refl
    app-value-final-none {M = ƛ N} vV M≢blame ()
    app-value-final-none {M = L · M} vV M≢blame eq rewrite eq = refl
    app-value-final-none {M = Λ N} vV M≢blame eq rewrite eq = refl
    app-value-final-none {M = L ⦂∀ B [ A ]} vV M≢blame eq
        rewrite eq = refl
    app-value-final-none {M = $ κ} vV M≢blame ()
    app-value-final-none {M = L ⊕[ op ] M} vV M≢blame eq rewrite eq = refl
    app-value-final-none {M = M ⟨ c ⟩} vV M≢blame eq rewrite eq = refl
    app-value-final-none {M = M ↑ c} vV M≢blame eq rewrite eq = refl
    app-value-final-none {M = M ↓ c} vV M≢blame eq rewrite eq = refl
    app-value-final-none {M = blame} vV M≢blame eq = ⊥-elim (M≢blame refl)

    app-final-none : ∀ {Δ : TyCtx} {V M : Term Δ}
        (vV : Value V)
      → M ≢ blame
      → E.value? M ≡ nothing
      → E.prim-final? op V M ≡ nothing
    app-final-none (ƛ N) M≢blame right-value-eq =
      app-value-final-none (ƛ N) M≢blame right-value-eq
    app-final-none (Λ vV) M≢blame right-value-eq
        with value-question-complete vV
    app-final-none (Λ vV) M≢blame right-value-eq | vV′ , value-eq
        rewrite value-eq =
      app-value-final-none (Λ vV′) M≢blame right-value-eq
    app-final-none ($ κ) M≢blame right-value-eq =
      app-value-final-none ($ κ) M≢blame right-value-eq
    app-final-none (vV 《 inert 》) M≢blame right-value-eq
        with value-question-complete (vV 《 inert 》)
    app-final-none (vV 《 inert 》) M≢blame right-value-eq
        | wrapped , value-eq rewrite value-eq =
      app-value-final-none wrapped M≢blame right-value-eq
    app-final-none (vV ↑ reveal) M≢blame right-value-eq
        with value-question-complete (vV ↑ reveal)
    app-final-none (vV ↑ reveal) M≢blame right-value-eq
        | wrapped , value-eq rewrite value-eq =
      app-value-final-none wrapped M≢blame right-value-eq
    app-final-none (vV ↓ conceal) M≢blame right-value-eq
        with value-question-complete (vV ↓ conceal)
    app-final-none (vV ↓ conceal) M≢blame right-value-eq
        | wrapped , value-eq rewrite value-eq =
      app-value-final-none wrapped M≢blame right-value-eq

    app-stuck-step-none : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {V M : Term Δ}
      → (vV : Value V)
      → E.step? Σ M ≡ nothing
      → E.value? M ≡ nothing
      → M ≢ blame
      → E.step? Σ (V ⊕[ op ] M) ≡ nothing
    app-stuck-step-none {Σ = Σ} {V = V} {M = M}
        vV right-step-eq right-value-eq M≢blame
        with E.step? Σ V | value-step-none {Σ = Σ} vV
    app-stuck-step-none {Σ = Σ} {V = V} {M = M}
        vV right-step-eq right-value-eq M≢blame
        | nothing | refl with E.step? Σ M | right-step-eq
    app-stuck-step-none {Σ = Σ} {V = V} {M = M}
        vV right-step-eq right-value-eq M≢blame
        | nothing | refl | nothing | refl =
      app-final-none vV M≢blame right-value-eq

    eval-app-stuck-none : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ}
      → E.step? Σ (V ⊕[ op ] M) ≡ nothing
      → E.evalFrom Σ (suc gas) (V ⊕[ op ] M) ≡ nothing
    eval-app-stuck-none {Σ = Σ} {gas = gas} {V = V} {M = M}
        step-eq with E.step? Σ (V ⊕[ op ] M) | step-eq
    eval-app-stuck-none step-eq | nothing | refl = refl

    app-blame-step-question : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {V : Term Δ}
      → (vV : Value V)
      → Σ[ vV′ ∈ Value V ]
          E.step? Σ (V ⊕[ op ] blame) ≡
            just (E.step-result keep blame (pure-step (blame-⊕₂ vV′)))
    app-blame-step-question (ƛ N) = (ƛ N) , refl
    app-blame-step-question (Λ vV) with value-question-complete vV
    app-blame-step-question (Λ vV) | vV′ , value-eq
        rewrite value-eq = (Λ vV′) , refl
    app-blame-step-question ($ κ) = ($ κ) , refl
    app-blame-step-question {Σ = Σ} (vV 《 inert 》)
        with value-question-complete (vV 《 inert 》)
           | value-step-none {Σ = Σ} (vV 《 inert 》)
    app-blame-step-question {Σ = Σ} (vV 《 inert 》)
        | wrapped , value-eq | step-eq
        rewrite step-eq | value-eq = wrapped , refl
    app-blame-step-question {Σ = Σ} (vV ↑ reveal)
        with value-question-complete (vV ↑ reveal)
           | value-step-none {Σ = Σ} (vV ↑ reveal)
    app-blame-step-question {Σ = Σ} (vV ↑ reveal)
        | wrapped , value-eq | step-eq
        rewrite step-eq | value-eq = wrapped , refl
    app-blame-step-question {Σ = Σ} (vV ↓ conceal)
        with value-question-complete (vV ↓ conceal)
           | value-step-none {Σ = Σ} (vV ↓ conceal)
    app-blame-step-question {Σ = Σ} (vV ↓ conceal)
        | wrapped , value-eq | step-eq
        rewrite step-eq | value-eq = wrapped , refl

    app-blame-not-returned : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {V : Term Δ} {result : E.EvalResult (V ⊕[ op ] blame)}
      → Value V
      → E.evalFrom Σ (suc gas) (V ⊕[ op ] blame)
          ≡ just (E.returned result)
      → ⊥
    app-blame-not-returned {Σ = Σ} {gas = zero} {V = V}
        vV result-eq with app-blame-step-question {Σ = Σ} vV
    app-blame-not-returned vV result-eq | vV′ , step-eq
        rewrite step-eq with result-eq
    app-blame-not-returned vV result-eq | vV′ , step-eq | ()
    app-blame-not-returned {Σ = Σ} {gas = suc gas} {V = V}
        vV result-eq with app-blame-step-question {Σ = Σ} vV
    app-blame-not-returned vV result-eq | vV′ , step-eq
        rewrite step-eq with result-eq
    app-blame-not-returned vV result-eq | vV′ , step-eq | ()

    right-stuck-impossible : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V ⊕[ op ] M)}
      → Value V
      → E.step? Σ M ≡ nothing
      → E.value? M ≡ nothing
      → E.evalFrom Σ (suc gas) (V ⊕[ op ] M) ≡ just (E.returned result)
      → ⊥
    right-stuck-impossible {Σ = Σ} {gas = gas} {V = V} {M = M}
        vV right-step-eq right-value-eq result-eq
        with blame-view M
    right-stuck-impossible {Σ = Σ} {gas = gas} {V = V}
        vV right-step-eq right-value-eq result-eq
        | is-blame refl = app-blame-not-returned {Σ = Σ} vV result-eq
    right-stuck-impossible {Σ = Σ} {gas = gas} {V = V} {M = M}
        vV right-step-eq right-value-eq result-eq
        | not-blame M≢blame =
      impossible
      where
      step-none = app-stuck-step-none {Σ = Σ} vV right-step-eq
        right-value-eq M≢blame
      none-eq = eval-app-stuck-none {Σ = Σ} {gas = gas} step-none

      impossible : ⊥
      impossible with trans (sym none-eq) result-eq
      impossible | ()

    app-final-left-none : ∀ {Δ : TyCtx} {L M : Term Δ}
      → L ≢ blame
      → E.value? L ≡ nothing
      → E.prim-final? op L M ≡ nothing
    app-final-left-none {L = ` x} L≢blame value-eq = refl
    app-final-left-none {L = ƛ N} L≢blame ()
    app-final-left-none {L = L · N} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = Λ N} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = L ⦂∀ B [ A ]} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = $ κ} L≢blame ()
    app-final-left-none {L = L ⊕[ op ] N} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = L ⟨ c ⟩} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = L ↑ c} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = L ↓ c} L≢blame value-eq
        rewrite value-eq = refl
    app-final-left-none {L = blame} L≢blame value-eq =
      ⊥-elim (L≢blame refl)

    app-left-stuck-step-none : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {L M : Term Δ}
      → E.step? Σ L ≡ nothing
      → E.value? L ≡ nothing
      → L ≢ blame
      → E.step? Σ (L ⊕[ op ] M) ≡ nothing
    app-left-stuck-step-none {Σ = Σ} {L = L} {M = M}
        left-step-eq left-value-eq L≢blame
        rewrite left-step-eq
        with E.step? Σ M in right-step-eq
    app-left-stuck-step-none {L = L} {M = M}
        left-step-eq left-value-eq L≢blame
        | just (E.step-result χ N step)
        with E.value? L | left-value-eq
    app-left-stuck-step-none {L = L} {M = M}
        left-step-eq left-value-eq L≢blame
        | just (E.step-result χ N step)
        | nothing | refl rewrite right-step-eq =
      app-final-left-none L≢blame left-value-eq
    app-left-stuck-step-none {L = L} {M = M}
        left-step-eq left-value-eq L≢blame
        | nothing
        rewrite right-step-eq =
      app-final-left-none L≢blame left-value-eq

    blame-left-step-question : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {M : Term Δ}
      → E.step? Σ (blame ⊕[ op ] M) ≡
          just (E.step-result keep blame (pure-step blame-⊕₁))
    blame-left-step-question {Σ = Σ} {M = M}
        with E.step? Σ M
    blame-left-step-question | just (E.step-result χ N step) = refl
    blame-left-step-question | nothing = refl

    eval-blame-left-prim : ∀
        {Δ : TyCtx} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
      → E.evalFrom Σ (suc gas) (blame ⊕[ op ] M) ≡
          just (E.blamed (keep ∷ [])
            (↠-step (pure-step blame-⊕₁) ↠-refl))
    eval-blame-left-prim {Σ = Σ} {gas = zero} {M = M}
        rewrite blame-left-step-question {Σ = Σ} {M = M} = refl
    eval-blame-left-prim {Σ = Σ} {gas = suc gas} {M = M}
        rewrite blame-left-step-question {Σ = Σ} {M = M} = refl

    blame-left-prim-not-returned : ∀
        {Δ : TyCtx} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
        {result : E.EvalResult (blame ⊕[ op ] M)}
      → E.evalFrom Σ gas (blame ⊕[ op ] M) ≡ just (E.returned result)
      → ⊥
    blame-left-prim-not-returned {gas = zero} ()
    blame-left-prim-not-returned {Σ = Σ} {gas = suc gas}
        {M = M} result-eq
        with trans (sym (eval-blame-left-prim
          {Σ = Σ} {gas = gas} {M = M})) result-eq
    blame-left-prim-not-returned result-eq | ()

    left-stuck-impossible : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {L M : Term Δ} {result : E.EvalResult (L ⊕[ op ] M)}
      → E.step? Σ L ≡ nothing
      → E.value? L ≡ nothing
      → E.evalFrom Σ (suc gas) (L ⊕[ op ] M) ≡ just (E.returned result)
      → ⊥
    left-stuck-impossible {Σ = Σ} {gas = gas} {L = L} {M = M}
        left-step-eq left-value-eq result-eq
        with blame-view L
    left-stuck-impossible {Σ = Σ} {gas = gas} {M = M}
        left-step-eq left-value-eq result-eq
        | is-blame refl =
      blame-left-prim-not-returned
        {Σ = Σ} {gas = suc gas} {M = M} result-eq
    left-stuck-impossible {Σ = Σ} {gas = gas} {L = L} {M = M}
        left-step-eq left-value-eq result-eq
        | not-blame L≢blame =
      impossible
      where
      step-none = app-left-stuck-step-none {Σ = Σ}
        left-step-eq left-value-eq L≢blame
      none-eq = eval-app-stuck-none {Σ = Σ} {gas = gas} step-none

      impossible : ⊥
      impossible with trans (sym none-eq) result-eq
      impossible | ()

    right-return-phases-eval : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V ⊕[ op ] M)}
      → Value V
      → E.evalFrom Σ gas (V ⊕[ op ] M) ≡ just (E.returned result)
      → RightReturnPhases Σ gas V M result
    right-return-phases-eval {gas = zero} vV ()
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        with E.step? Σ M in right-step-eq
           | value-question-complete vV
           | value-step-none {Σ = Σ} vV
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        with E.evalFrom (χ ▷ˢ Σ) gas ((χ ▷ᵀ V) ⊕[ op ] N) in next-eq
    right-return-phases-eval vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | nothing
        rewrite value-step-eq | right-step-eq | value-eq | next-eq
        with result-eq
    right-return-phases-eval vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | nothing | ()
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.returned next-result)
        rewrite value-step-eq | right-step-eq | value-eq | next-eq
        with result-eq
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.returned next-result) | refl
        with right-return-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
          {V = χ ▷ᵀ V} {M = N} {result = next-result}
          (apply-change-value χ vV′) next-eq
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.returned next-result) | refl
        | right-return-phases-record leftValue rightGas
            rightResult rightReturn deltaGas deltaResult deltaReturn
            result-split gas-eq =
      right-return-phases-record vV′ (suc rightGas)
        (prepend-result step rightResult)
        (prepend-return {Σ = Σ} {M = M} {gas = rightGas}
          right-step-eq rightReturn)
        deltaGas deltaResult deltaReturn
        (cong (prepend-result (ξ-⊕₂ vV′ step refl))
          (trans result-split
            (sequence-right-result-value-cong
              {rightResult = rightResult} {deltaResult = deltaResult}
              (value-unique leftValue (apply-change-value χ vV′)))))
        (cong suc gas-eq)
    right-return-phases-eval vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.blamed changes trace)
        rewrite value-step-eq | right-step-eq | value-eq | next-eq
        with result-eq
    right-return-phases-eval vV result-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.blamed changes trace) | ()
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | nothing | vV′ , value-eq | value-step-eq
        with E.value? M in right-value-eq
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | nothing | vV′ , value-eq | value-step-eq
        | just vM with value-eval {Σ = Σ} zero vM
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | nothing | vV′ , value-eq | value-step-eq
        | just vM | vM′ , right-eval =
      right-return-phases-record vV′ zero
        (E.result _ [] M ↠-refl vM′)
        (return-from-eval {Σ = Σ} {gas = zero} {M = M} right-eval)
        (suc gas) _
        (return-from-eval {Σ = Σ} {gas = suc gas} {M = V ⊕[ op ] M}
          result-eq)
        refl
        refl
    right-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
        {M = M} vV result-eq
        | nothing | vV′ , value-eq | value-step-eq
        | nothing = ⊥-elim
          (right-stuck-impossible {Σ = Σ} {gas = gas} {V = V}
            {M = M} vV right-step-eq right-value-eq result-eq)

    right-return-phases : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V ⊕[ op ] M)}
      → Value V
      → interpretFrom Σ gas (V ⊕[ op ] M) ≡ returned result
      → RightReturnPhases Σ gas V M result
    right-return-phases {Σ = Σ} {gas = gas} {V = V} {M = M}
        vV result-eq =
      right-return-phases-eval {Σ = Σ} {gas = gas} {V = V} {M = M}
        vV (eval-from-return {Σ = Σ} {gas = gas} {M = V ⊕[ op ] M}
          result-eq)

    record PrimitiveReturnPhases {Δ : TyCtx}
        (Σ : TyStore Δ) (gas : ℕ) (L M : Term Δ)
        (wholeResult : E.EvalResult (L ⊕[ op ] M)) : Set where
      constructor return-phases
      field
        leftGas : ℕ
        leftResult : E.EvalResult L
        leftReturn :
          interpretFrom Σ leftGas L ≡ returned leftResult

        rightGas : ℕ
        rightResult :
          E.EvalResult (E.changes leftResult ▶ᵀ M)
        rightReturn :
          interpretFrom (E.changes leftResult ▶ˢ Σ) rightGas
            (E.changes leftResult ▶ᵀ M) ≡ returned rightResult

        deltaGas : ℕ
        deltaResult : E.EvalResult
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult)
        deltaReturn :
          interpretFrom
            (E.changes rightResult ▶ˢ
              (E.changes leftResult ▶ˢ Σ)) deltaGas
            ((E.changes rightResult ▶ᵀ E.term leftResult)
              ⊕[ op ] E.term rightResult) ≡ returned deltaResult

        result-splits : wholeResult ≡
          sequence-prim-result leftResult rightResult deltaResult

        gas-splits : leftGas + rightGas + deltaGas ≡ gas

    open PrimitiveReturnPhases public

    prim-value-return-phases : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V ⊕[ op ] M)}
      → Value V
      → E.evalFrom Σ gas (V ⊕[ op ] M) ≡ just (E.returned result)
      → RightReturnPhases Σ gas V M result
    prim-value-return-phases = right-return-phases-eval

    prim-return-phases-eval : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {L M : Term Δ} {result : E.EvalResult (L ⊕[ op ] M)}
      → E.evalFrom Σ gas (L ⊕[ op ] M) ≡ just (E.returned result)
      → PrimitiveReturnPhases Σ gas L M result
    prim-return-phases-eval {gas = zero} ()
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} {result = result} result-eq
        with E.value? L in left-value-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} {result = result} result-eq
        | just vL
        with prim-value-return-phases {Σ = Σ} {gas = suc gas}
          {V = L} {M = M} {result = result} vL result-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | just vL
        | right-return-phases-record leftValue rightGas
            rightResult rightReturn deltaGas deltaResult deltaReturn
            result-split gas-eq =
      return-phases zero (E.result _ [] L ↠-refl leftValue)
        (value-return-exact {Σ = Σ} zero leftValue)
        rightGas rightResult rightReturn
        deltaGas deltaResult deltaReturn result-split gas-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing with E.step? Σ L in left-step-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) gas (N ⊕[ op ] (χ ▷ᵀ M)) in next-eq
    prim-return-phases-eval result-eq
        | nothing | just (E.step-result χ N step) | nothing
        rewrite left-step-eq | next-eq
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | just (E.step-result χ N step) | nothing | ()
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | just (E.step-result χ N step)
        | just (E.returned next-result)
        rewrite left-step-eq | next-eq
        with result-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        with prim-return-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
          {L = N} {M = χ ▷ᵀ M} {result = next-result} next-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | just (E.step-result χ N step)
        | just (E.returned next-result) | refl
        | return-phases leftGas leftResult leftReturn
            rightGas rightResult rightReturn
            deltaGas deltaResult deltaReturn result-split gas-eq =
      return-phases (suc leftGas)
        (prepend-result step leftResult)
        (prepend-return {Σ = Σ} {M = L} {gas = leftGas}
          left-step-eq leftReturn)
        rightGas rightResult rightReturn
        deltaGas deltaResult deltaReturn
        (cong (prepend-result (ξ-⊕₁ step refl)) result-split)
        (cong suc gas-eq)
    prim-return-phases-eval result-eq
        | nothing | just (E.step-result χ N step)
        | just (E.blamed changes trace)
        rewrite left-step-eq | next-eq
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | just (E.step-result χ N step)
        | just (E.blamed changes trace) | ()
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | nothing
        with blame-view L | E.step? Σ M in right-step-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | nothing | is-blame refl
        | just (E.step-result χ N step)
        with gas
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl
        | just (E.step-result χ N step) | zero
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl
        | just (E.step-result χ N step) | zero | ()
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl
        | just (E.step-result χ N step) | suc gas′
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl
        | just (E.step-result χ N step) | suc gas′ | ()
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | nothing | is-blame refl | nothing
        with gas
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl | nothing | zero
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl | nothing | zero | ()
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl | nothing | suc gas′
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | is-blame refl | nothing | suc gas′ | ()
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | nothing | not-blame L≢blame
        | just (E.step-result χ N step)
        with E.value? L | left-value-eq
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | nothing | not-blame L≢blame
        | just (E.step-result χ N step) | nothing | refl
        with E.prim-final? op L M in final-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | not-blame L≢blame
        | just (E.step-result χ N step) | nothing | refl | nothing
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | not-blame L≢blame
        | just (E.step-result χ N step) | nothing | refl | nothing | ()
    prim-return-phases-eval {L = L} result-eq
        | nothing | nothing | not-blame L≢blame
        | just (E.step-result χ N step) | nothing | refl
        | just (E.step-result ψ P final-step) =
      ⊥-elim impossible
      where
      impossible : ⊥
      impossible with trans (sym final-eq)
        (app-final-left-none L≢blame left-value-eq)
      impossible | ()
    prim-return-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} result-eq
        | nothing | nothing | not-blame L≢blame | nothing
        with E.prim-final? op L M in final-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | not-blame L≢blame | nothing | nothing
        with result-eq
    prim-return-phases-eval result-eq
        | nothing | nothing | not-blame L≢blame | nothing | nothing | ()
    prim-return-phases-eval {L = L} result-eq
        | nothing | nothing | not-blame L≢blame | nothing
        | just (E.step-result ψ P final-step) =
      ⊥-elim impossible
      where
      impossible : ⊥
      impossible with trans (sym final-eq)
        (app-final-left-none L≢blame left-value-eq)
      impossible | ()

    prim-return-phases : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
        {gas : ℕ} {L M : Term Δ} {result : E.EvalResult (L ⊕[ op ] M)}
      → interpretFrom Σ gas (L ⊕[ op ] M) ≡ returned result
      → PrimitiveReturnPhases Σ gas L M result
    prim-return-phases {Σ = Σ} {gas = gas} {L = L} {M = M}
        result-eq =
      prim-return-phases-eval {Σ = Σ} {gas = gas} {L = L} {M = M}
        (eval-from-return {Σ = Σ} {gas = gas} {M = L ⊕[ op ] M} result-eq)

    prim-return-expand : ∀ {Δ} {Σ : TyStore Δ}
        {leftGas rightGas deltaGas : ℕ} {L M : Term Δ}
        {leftResult : E.EvalResult L}
        {rightResult : E.EvalResult
          (E.changes leftResult ▶ᵀ M)}
        {deltaResult : E.EvalResult
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult)}
      → interpretFrom Σ leftGas L ≡ returned leftResult
      → interpretFrom (E.changes leftResult ▶ˢ Σ) rightGas
          (E.changes leftResult ▶ᵀ M) ≡ returned rightResult
      → interpretFrom
          (E.changes rightResult ▶ˢ
            (E.changes leftResult ▶ˢ Σ)) deltaGas
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult) ≡ returned deltaResult
      → Σ[ wholeGas ∈ ℕ ]
          interpretFrom Σ wholeGas (L ⊕[ op ] M) ≡
            returned (sequence-prim-result leftResult
              rightResult deltaResult)
    prim-return-expand {Σ = Σ} {leftGas = leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        {rightResult = rightResult}
        left-eq right-eq delta-eq
        with prim-return-expand-eval {Σ = Σ}
          {leftGas = leftGas} {rightGas = rightGas}
          {deltaGas = deltaGas} {L = L} {M = M}
          (eval-from-return {Σ = Σ} {gas = leftGas} left-eq)
          (eval-from-return
            {Σ = E.changes leftResult ▶ˢ Σ} {gas = rightGas}
            right-eq)
          (eval-from-return
            {Σ = E.changes rightResult ▶ˢ
              (E.changes leftResult ▶ˢ Σ)} {gas = deltaGas} delta-eq)
    prim-return-expand {Σ = Σ} left-eq right-eq delta-eq
        | wholeGas , whole-eq =
      wholeGas , return-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

    eval-from-blame : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
        {M : Term Δ} {changes : StoreChanges Δ Δ′}
        {trace : M —↠[ changes ] blame}
      → interpretFrom Σ gas M ≡ blamed changes trace
      → E.evalFrom Σ gas M ≡ just (E.blamed changes trace)
    eval-from-blame {Σ = Σ} {gas = gas} {M = M} blame-eq
        with E.evalFrom Σ gas M
    eval-from-blame blame-eq | nothing with blame-eq
    eval-from-blame blame-eq | nothing | ()
    eval-from-blame blame-eq | just (E.returned result′) with blame-eq
    eval-from-blame blame-eq | just (E.returned result′) | ()
    eval-from-blame blame-eq | just (E.blamed changes trace)
        with blame-eq
    eval-from-blame blame-eq | just (E.blamed changes trace) | refl = refl

    blame-from-eval : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
        {M : Term Δ} {changes : StoreChanges Δ Δ′}
        {trace : M —↠[ changes ] blame}
      → E.evalFrom Σ gas M ≡ just (E.blamed changes trace)
      → BlamesFrom Σ gas M
    blame-from-eval {Σ = Σ} {gas = gas} {M = M}
        {changes = changes} {trace = trace} eval-eq =
      _ , changes , trace ,
      trans (interpret-from-eval {Σ = Σ} {gas = gas} {M = M})
        (cong (interpreter-outcome {M = M}) eval-eq)

    prepend-blamed : ∀ {Δ Δ′} {Σ : TyStore Δ} {M : Term Δ}
        {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
        {step : M —→[ χ ] N}
      → E.step? Σ M ≡ just (E.step-result χ N step)
      → BlamesFrom (χ ▷ˢ Σ) gas N
      → BlamesFrom Σ (suc gas) M
    prepend-blamed {Σ = Σ} {M = M} {χ = χ} {gas = gas}
        {step = step} step-eq (Δ″ , changes , trace , blame-eq) =
      blame-from-eval {Σ = Σ} {gas = suc gas}
        (eval-prepend-blamed {Σ = Σ} step-eq
          (eval-from-blame {Σ = χ ▷ˢ Σ} {gas = gas} blame-eq))

    eval-prim-prepend-blame : ∀ {Δ Δ′ Δ″}
        {Σ : TyStore Δ} {L M : Term Δ}
        {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
        {step : L ⊕[ op ] M —→[ χ ] N}
        {changes : StoreChanges Δ′ Δ″}
        {trace : N —↠[ changes ] blame}
      → E.step? Σ (L ⊕[ op ] M) ≡ just (E.step-result χ N step)
      → E.evalFrom (χ ▷ˢ Σ) gas N ≡ just (E.blamed changes trace)
      → E.evalFrom Σ (suc gas) (L ⊕[ op ] M) ≡
          just (E.blamed (χ ∷ changes) (↠-step step trace))
    eval-prim-prepend-blame step-eq next-eq
        rewrite step-eq | next-eq = refl

    left-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {leftGas : ℕ} {L M : Term Δ}
        {changes : StoreChanges Δ Δ′} {trace : L —↠[ changes ] blame}
      → E.evalFrom Σ leftGas L ≡ just (E.blamed changes trace)
      → Σ[ wholeGas ∈ ℕ ]
        Σ[ Δ″ ∈ TyCtx ]
        Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
        Σ[ wholeTrace ∈ L ⊕[ op ] M —↠[ wholeChanges ] blame ]
          E.evalFrom Σ wholeGas (L ⊕[ op ] M) ≡
            just (E.blamed wholeChanges wholeTrace)
    left-blame-expand-eval {Σ = Σ} {leftGas = zero}
        {L = L} {M = M} left-eq with blame-view L
    left-blame-expand-eval {Σ = Σ} left-eq | is-blame refl =
      1 , _ , keep ∷ [] , ↠-step (pure-step blame-⊕₁) ↠-refl ,
      eval-blame-left-prim {Σ = Σ}
    left-blame-expand-eval {Σ = Σ} {leftGas = zero}
        {L = L} left-eq | not-blame L≢blame
        rewrite eval-from-nonblame {Σ = Σ} {gas = zero} L≢blame
        with E.value? L
    left-blame-expand-eval left-eq | not-blame L≢blame
        | just vL with left-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | just vL | ()
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing with left-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | ()
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        with blame-view L
    left-blame-expand-eval {Σ = Σ} left-eq | is-blame refl =
      1 , _ , keep ∷ [] , ↠-step (pure-step blame-⊕₁) ↠-refl ,
      eval-blame-left-prim {Σ = Σ}
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        | not-blame L≢blame
        rewrite eval-from-nonblame {Σ = Σ} {gas = suc leftGas}
          L≢blame
        with E.value? L in left-value-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | just vL with left-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | just vL | ()
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        | not-blame L≢blame | nothing
        with E.step? Σ L in left-step-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | nothing with left-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | nothing | ()
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        | not-blame L≢blame | nothing
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) leftGas N in next-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | just (E.step-result χ N step) | nothing
        with left-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | just (E.step-result χ N step) | nothing | ()
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | just (E.step-result χ N step)
        | just (E.returned next-result) with left-eq
    left-blame-expand-eval left-eq | not-blame L≢blame
        | nothing | just (E.step-result χ N step)
        | just (E.returned next-result) | ()
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        | not-blame L≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace)
        with left-eq
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        | not-blame L≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        with left-blame-expand-eval {Σ = χ ▷ˢ Σ}
          {leftGas = leftGas} {L = N} {M = χ ▷ᵀ M} next-eq
    left-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {L = L} {M = M} left-eq
        | not-blame L≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      suc wholeGas , Δ″ , χ ∷ wholeChanges ,
      ↠-step (ξ-⊕₁ step refl) wholeTrace ,
      eval-prim-prepend-blame {Σ = Σ}
        (app-left-step-question {Σ = Σ} left-step-eq) whole-eq

    left-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
        {leftGas : ℕ} {L M : Term Δ}
      → BlamesFrom Σ leftGas L
      → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L ⊕[ op ] M)
    left-blame-expand {Σ = Σ} {leftGas = leftGas}
        {L = L} {M = M} (Δ′ , changes , trace , left-eq)
        with left-blame-expand-eval {Σ = Σ}
          {leftGas = leftGas} {L = L} {M = M}
          (eval-from-blame {Σ = Σ} {gas = leftGas} left-eq)
    left-blame-expand {Σ = Σ} leftBlame
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

    eval-value-blame-prim : ∀ {Δ} {Σ : TyStore Δ}
        {V : Term Δ}
      → (vV : Value V)
      → Σ[ vV′ ∈ Value V ]
          E.evalFrom Σ 1 (V ⊕[ op ] blame) ≡
            just (E.blamed (keep ∷ [])
              (↠-step (pure-step (blame-⊕₂ vV′)) ↠-refl))
    eval-value-blame-prim {Σ = Σ} vV
        with app-blame-step-question {Σ = Σ} vV
    eval-value-blame-prim vV | vV′ , step-eq
        rewrite step-eq = vV′ , refl

    right-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {rightGas : ℕ} {V M : Term Δ}
        {changes : StoreChanges Δ Δ′} {trace : M —↠[ changes ] blame}
      → (vV : Value V)
      → E.evalFrom Σ rightGas M ≡ just (E.blamed changes trace)
      → Σ[ wholeGas ∈ ℕ ]
        Σ[ Δ″ ∈ TyCtx ]
        Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
        Σ[ wholeTrace ∈ V ⊕[ op ] M —↠[ wholeChanges ] blame ]
          E.evalFrom Σ wholeGas (V ⊕[ op ] M) ≡
            just (E.blamed wholeChanges wholeTrace)
    right-blame-expand-eval {Σ = Σ} {rightGas = zero}
        {V = V} {M = M} vV right-eq with blame-view M
    right-blame-expand-eval {Σ = Σ} vV right-eq
        | is-blame refl with eval-value-blame-prim {Σ = Σ} vV
    right-blame-expand-eval vV right-eq
        | is-blame refl | vV′ , whole-eq =
      1 , _ , keep ∷ [] ,
      ↠-step (pure-step (blame-⊕₂ vV′)) ↠-refl , whole-eq
    right-blame-expand-eval {Σ = Σ} {rightGas = zero}
        {V = V} {M = M} vV right-eq | not-blame M≢blame
        rewrite eval-from-nonblame {Σ = Σ} {gas = zero} M≢blame
        with E.value? M
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | just vM with right-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | just vM | ()
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing with right-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | ()
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq with blame-view M
    right-blame-expand-eval {Σ = Σ} vV right-eq
        | is-blame refl with eval-value-blame-prim {Σ = Σ} vV
    right-blame-expand-eval vV right-eq
        | is-blame refl | vV′ , whole-eq =
      1 , _ , keep ∷ [] ,
      ↠-step (pure-step (blame-⊕₂ vV′)) ↠-refl , whole-eq
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame
        rewrite eval-from-nonblame {Σ = Σ} {gas = suc rightGas}
          M≢blame
        with E.value? M in right-value-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | just vM with right-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | just vM | ()
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame | nothing
        with E.step? Σ M in right-step-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | nothing with right-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | nothing | ()
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame | nothing
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) rightGas N in next-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | just (E.step-result χ N step) | nothing
        with right-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | just (E.step-result χ N step) | nothing | ()
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | just (E.step-result χ N step)
        | just (E.returned nextResult) with right-eq
    right-blame-expand-eval vV right-eq | not-blame M≢blame
        | nothing | just (E.step-result χ N step)
        | just (E.returned nextResult) | ()
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) with right-eq
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        with right-blame-expand-eval {Σ = χ ▷ˢ Σ}
          {rightGas = rightGas} {V = χ ▷ᵀ V} {M = N}
          (apply-change-value χ vV) next-eq
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
        with app-right-step-question {Σ = Σ} vV right-step-eq
    right-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {V = V} {M = M}
        vV right-eq | not-blame M≢blame | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
        | vV′ , prim-step-eq =
      suc wholeGas , Δ″ , χ ∷ wholeChanges ,
      ↠-step (ξ-⊕₂ vV′ step refl) wholeTrace ,
      eval-prim-prepend-blame {Σ = Σ} prim-step-eq whole-eq

    right-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
        {rightGas : ℕ} {V M : Term Δ}
      → Value V
      → BlamesFrom Σ rightGas M
      → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (V ⊕[ op ] M)
    right-blame-expand {Σ = Σ} {rightGas = rightGas}
        {V = V} {M = M} vV
        (Δ′ , changes , trace , right-eq)
        with right-blame-expand-eval {Σ = Σ}
          {rightGas = rightGas} {V = V} {M = M} vV
          (eval-from-blame {Σ = Σ} {gas = rightGas} right-eq)
    right-blame-expand {Σ = Σ} vV rightBlame
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

    prim-right-blame-expand-eval : ∀ {Δ Δ′}
        {Σ : TyStore Δ} {leftGas rightGas : ℕ}
        {L M : Term Δ} {leftResult : E.EvalResult L}
        {changes : StoreChanges (E.Δ′ leftResult) Δ′}
        {trace : E.changes leftResult ▶ᵀ M —↠[ changes ] blame}
      → E.evalFrom Σ leftGas L ≡ just (E.returned leftResult)
      → E.evalFrom (E.changes leftResult ▶ˢ Σ) rightGas
          (E.changes leftResult ▶ᵀ M) ≡
            just (E.blamed changes trace)
      → Σ[ wholeGas ∈ ℕ ]
        Σ[ Δ″ ∈ TyCtx ]
        Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
        Σ[ wholeTrace ∈ L ⊕[ op ] M —↠[ wholeChanges ] blame ]
          E.evalFrom Σ wholeGas (L ⊕[ op ] M) ≡
            just (E.blamed wholeChanges wholeTrace)
    prim-right-blame-expand-eval {Σ = Σ} {leftGas = zero}
        {rightGas = rightGas} {L = L} {M = M}
        left-eq right-eq with blame-view L
    prim-right-blame-expand-eval left-eq right-eq
        | is-blame refl with left-eq
    prim-right-blame-expand-eval left-eq right-eq
        | is-blame refl | ()
    prim-right-blame-expand-eval {Σ = Σ} {leftGas = zero}
        {rightGas = rightGas} {L = L} {M = M}
        left-eq right-eq | not-blame L≢blame
        with E.value? L in left-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
               {M = L} L≢blame)) left-eq
    prim-right-blame-expand-eval {Σ = Σ}
        {rightGas = rightGas} left-eq right-eq
        | not-blame L≢blame | just vL | refl =
      right-blame-expand-eval {Σ = Σ} {rightGas = rightGas}
        vL right-eq
    prim-right-blame-expand-eval left-eq right-eq
        | not-blame L≢blame | nothing | ()
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq with blame-view L
    prim-right-blame-expand-eval left-eq right-eq
        | is-blame refl with left-eq
    prim-right-blame-expand-eval left-eq right-eq
        | is-blame refl | ()
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq
        | not-blame L≢blame
        with E.value? L in left-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ}
               {gas = suc leftGas} {M = L} L≢blame)) left-eq
    prim-right-blame-expand-eval {Σ = Σ}
        {rightGas = rightGas} left-eq right-eq
        | not-blame L≢blame | just vL | refl =
      right-blame-expand-eval {Σ = Σ} {rightGas = rightGas}
        vL right-eq
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq
        | not-blame L≢blame | nothing | normalized-eq
        with E.step? Σ L in left-step-eq
    prim-right-blame-expand-eval left-eq right-eq
        | not-blame L≢blame | nothing | () | nothing
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq
        | not-blame L≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) leftGas N in next-eq
    prim-right-blame-expand-eval left-eq right-eq
        | not-blame L≢blame | nothing | ()
        | just (E.step-result χ N step) | nothing
    prim-right-blame-expand-eval left-eq right-eq
        | not-blame L≢blame | nothing | ()
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace)
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq
        | not-blame L≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        | just (E.returned nextResult) with normalized-eq
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq
        | not-blame L≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        with prim-right-blame-expand-eval {Σ = χ ▷ˢ Σ}
          {leftGas = leftGas} {rightGas = rightGas}
          {L = N} {M = χ ▷ᵀ M} next-eq right-eq
    prim-right-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas} {rightGas = rightGas}
        {L = L} {M = M} left-eq right-eq
        | not-blame L≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      suc wholeGas , Δ″ , χ ∷ wholeChanges ,
      ↠-step (ξ-⊕₁ step refl) wholeTrace ,
      eval-prim-prepend-blame {Σ = Σ}
        (app-left-step-question {Σ = Σ} left-step-eq) whole-eq

    prim-right-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
        {leftGas rightGas : ℕ} {L M : Term Δ}
        {leftResult : E.EvalResult L}
      → interpretFrom Σ leftGas L ≡ returned leftResult
      → BlamesFrom (E.changes leftResult ▶ˢ Σ) rightGas
          (E.changes leftResult ▶ᵀ M)
      → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L ⊕[ op ] M)
    prim-right-blame-expand {Σ = Σ}
        {leftGas = leftGas} {rightGas = rightGas}
        {L = L} {M = M} {leftResult = leftResult}
        left-eq (Δ′ , changes , trace , right-eq)
        with prim-right-blame-expand-eval {Σ = Σ}
          {leftGas = leftGas} {rightGas = rightGas}
          {L = L} {M = M} {leftResult = leftResult}
          (eval-from-return {Σ = Σ} {gas = leftGas} left-eq)
          (eval-from-blame {Σ = E.changes leftResult ▶ˢ Σ}
            {gas = rightGas} right-eq)
    prim-right-blame-expand {Σ = Σ} left-eq rightBlame
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

    right-delta-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {rightGas deltaGas : ℕ} {V M : Term Δ}
        {rightResult : E.EvalResult M}
        {changes : StoreChanges (E.Δ′ rightResult) Δ′}
        {trace : (E.changes rightResult ▶ᵀ V)
          ⊕[ op ] E.term rightResult —↠[ changes ] blame}
      → (vV : Value V)
      → E.evalFrom Σ rightGas M ≡ just (E.returned rightResult)
      → E.evalFrom (E.changes rightResult ▶ˢ Σ) deltaGas
          ((E.changes rightResult ▶ᵀ V) ⊕[ op ] E.term rightResult) ≡
            just (E.blamed changes trace)
      → Σ[ wholeGas ∈ ℕ ]
        Σ[ Δ″ ∈ TyCtx ]
        Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
        Σ[ wholeTrace ∈ V ⊕[ op ] M —↠[ wholeChanges ] blame ]
          E.evalFrom Σ wholeGas (V ⊕[ op ] M) ≡
            just (E.blamed wholeChanges wholeTrace)
    right-delta-blame-expand-eval {Σ = Σ} {rightGas = zero}
        {deltaGas = deltaGas} {V = V} {M = M}
        vV right-eq delta-eq with blame-view M
    right-delta-blame-expand-eval vV right-eq delta-eq
        | is-blame refl with right-eq
    right-delta-blame-expand-eval vV right-eq delta-eq
        | is-blame refl | ()
    right-delta-blame-expand-eval {Σ = Σ} {rightGas = zero}
        {deltaGas = deltaGas} {V = V} {M = M}
        vV right-eq delta-eq | not-blame M≢blame
        with E.value? M in right-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
               {M = M} M≢blame)) right-eq
    right-delta-blame-expand-eval {deltaGas = deltaGas}
        vV right-eq delta-eq
        | not-blame M≢blame | just vM | refl =
      deltaGas , _ , _ , _ , delta-eq
    right-delta-blame-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | ()
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq with blame-view M
    right-delta-blame-expand-eval vV right-eq delta-eq
        | is-blame refl with right-eq
    right-delta-blame-expand-eval vV right-eq delta-eq
        | is-blame refl | ()
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame
        with E.value? M in right-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ}
               {gas = suc rightGas} {M = M} M≢blame)) right-eq
    right-delta-blame-expand-eval {deltaGas = deltaGas}
        vV right-eq delta-eq
        | not-blame M≢blame | just vM | refl =
      deltaGas , _ , _ , _ , delta-eq
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame | nothing | normalized-eq
        with E.step? Σ M in right-step-eq
    right-delta-blame-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | () | nothing
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) rightGas N in next-eq
    right-delta-blame-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | ()
        | just (E.step-result χ N step) | nothing
    right-delta-blame-expand-eval vV right-eq delta-eq
        | not-blame M≢blame | nothing | ()
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace)
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        | just (E.returned nextResult) with normalized-eq
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        with right-delta-blame-expand-eval {Σ = χ ▷ˢ Σ}
          {rightGas = rightGas} {deltaGas = deltaGas}
          {V = χ ▷ᵀ V} {M = N} (apply-change-value χ vV)
          next-eq delta-eq
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
        with app-right-step-question {Σ = Σ} vV right-step-eq
    right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = suc rightGas} {deltaGas = deltaGas}
        {V = V} {M = M} vV right-eq delta-eq
        | not-blame M≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
        | vV′ , prim-step-eq =
      suc wholeGas , Δ″ , χ ∷ wholeChanges ,
      ↠-step (ξ-⊕₂ vV′ step refl) wholeTrace ,
      eval-prim-prepend-blame {Σ = Σ} prim-step-eq whole-eq

    prim-delta-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {leftGas rightGas deltaGas : ℕ} {L M : Term Δ}
        {leftResult : E.EvalResult L}
        {rightResult : E.EvalResult
          (E.changes leftResult ▶ᵀ M)}
        {changes : StoreChanges (E.Δ′ rightResult) Δ′}
        {trace : (E.changes rightResult ▶ᵀ E.term leftResult)
          ⊕[ op ] E.term rightResult —↠[ changes ] blame}
      → E.evalFrom Σ leftGas L ≡ just (E.returned leftResult)
      → E.evalFrom (E.changes leftResult ▶ˢ Σ) rightGas
          (E.changes leftResult ▶ᵀ M) ≡
            just (E.returned rightResult)
      → E.evalFrom
          (E.changes rightResult ▶ˢ
            (E.changes leftResult ▶ˢ Σ)) deltaGas
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult) ≡ just (E.blamed changes trace)
      → Σ[ wholeGas ∈ ℕ ]
        Σ[ Δ″ ∈ TyCtx ]
        Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
        Σ[ wholeTrace ∈ L ⊕[ op ] M —↠[ wholeChanges ] blame ]
          E.evalFrom Σ wholeGas (L ⊕[ op ] M) ≡
            just (E.blamed wholeChanges wholeTrace)
    prim-delta-blame-expand-eval {Σ = Σ} {leftGas = zero}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        with blame-view L
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | is-blame refl with left-eq
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | is-blame refl | ()
    prim-delta-blame-expand-eval {Σ = Σ} {leftGas = zero}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame
        with E.value? L in left-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
               {M = L} L≢blame)) left-eq
    prim-delta-blame-expand-eval {Σ = Σ}
        {rightGas = rightGas} {deltaGas = deltaGas}
        left-eq right-eq delta-eq
        | not-blame L≢blame | just vL | refl =
      right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = rightGas} {deltaGas = deltaGas}
        vL right-eq delta-eq
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | ()
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        with blame-view L
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | is-blame refl with left-eq
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | is-blame refl | ()
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame
        with E.value? L in left-value-eq
           | trans (sym (eval-from-nonblame {Σ = Σ}
               {gas = suc leftGas} {M = L} L≢blame)) left-eq
    prim-delta-blame-expand-eval {Σ = Σ}
        {rightGas = rightGas} {deltaGas = deltaGas}
        left-eq right-eq delta-eq
        | not-blame L≢blame | just vL | refl =
      right-delta-blame-expand-eval {Σ = Σ}
        {rightGas = rightGas} {deltaGas = deltaGas}
        vL right-eq delta-eq
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | normalized-eq
        with E.step? Σ L in left-step-eq
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | () | nothing
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) leftGas N in next-eq
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | ()
        | just (E.step-result χ N step) | nothing
    prim-delta-blame-expand-eval left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | ()
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace)
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | normalized-eq
        | just (E.step-result χ N step)
        | just (E.returned nextResult) with normalized-eq
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        with prim-delta-blame-expand-eval {Σ = χ ▷ˢ Σ}
          {leftGas = leftGas} {rightGas = rightGas}
          {deltaGas = deltaGas} {L = N} {M = χ ▷ᵀ M}
          next-eq right-eq delta-eq
    prim-delta-blame-expand-eval {Σ = Σ}
        {leftGas = suc leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} left-eq right-eq delta-eq
        | not-blame L≢blame | nothing | refl
        | just (E.step-result χ N step)
        | just (E.returned nextResult) | refl
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      suc wholeGas , Δ″ , χ ∷ wholeChanges ,
      ↠-step (ξ-⊕₁ step refl) wholeTrace ,
      eval-prim-prepend-blame {Σ = Σ}
        (app-left-step-question {Σ = Σ} left-step-eq) whole-eq

    prim-delta-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
        {leftGas rightGas deltaGas : ℕ} {L M : Term Δ}
        {leftResult : E.EvalResult L}
        {rightResult : E.EvalResult
          (E.changes leftResult ▶ᵀ M)}
      → interpretFrom Σ leftGas L ≡ returned leftResult
      → interpretFrom (E.changes leftResult ▶ˢ Σ) rightGas
          (E.changes leftResult ▶ᵀ M) ≡ returned rightResult
      → BlamesFrom
          (E.changes rightResult ▶ˢ
            (E.changes leftResult ▶ˢ Σ)) deltaGas
          ((E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult)
      → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L ⊕[ op ] M)
    prim-delta-blame-expand {Σ = Σ} {leftGas = leftGas}
        {rightGas = rightGas} {deltaGas = deltaGas}
        {L = L} {M = M} {leftResult = leftResult}
        {rightResult = rightResult} left-eq right-eq
        (Δ′ , changes , trace , delta-eq)
        with prim-delta-blame-expand-eval {Σ = Σ}
          {leftGas = leftGas} {rightGas = rightGas}
          {deltaGas = deltaGas} {L = L} {M = M}
          {leftResult = leftResult} {rightResult = rightResult}
          (eval-from-return {Σ = Σ} {gas = leftGas} left-eq)
          (eval-from-return {Σ = E.changes leftResult ▶ˢ Σ}
            {gas = rightGas} right-eq)
          (eval-from-blame {Σ = E.changes rightResult ▶ˢ
            (E.changes leftResult ▶ˢ Σ)} {gas = deltaGas} delta-eq)
    prim-delta-blame-expand {Σ = Σ}
        left-eq right-eq deltaBlame
        | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
      wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

    data RightBlamePhases {Δ : TyCtx}
        (Σ : TyStore Δ) (gas : ℕ) (V M : Term Δ) : Set where
      right-phase-blames :
          (leftValue : Value V)
        → (rightGas : ℕ)
        → BlamesFrom Σ rightGas M
        → rightGas ≤ gas
        → RightBlamePhases Σ gas V M

      delta-phase-blames :
          (leftValue : Value V)
        → (rightGas : ℕ)
        → (rightResult : E.EvalResult M)
        → interpretFrom Σ rightGas M ≡ returned rightResult
        → (deltaGas : ℕ)
        → BlamesFrom (E.changes rightResult ▶ˢ Σ) deltaGas
            ((E.changes rightResult ▶ᵀ V) ⊕[ op ] E.term rightResult)
        → rightGas + deltaGas ≤ gas
        → RightBlamePhases Σ gas V M

    right-blame-phases-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ} {changes : StoreChanges Δ Δ′}
        {trace : V ⊕[ op ] M —↠[ changes ] blame}
      → Value V
      → E.evalFrom Σ gas (V ⊕[ op ] M) ≡ just (E.blamed changes trace)
      → RightBlamePhases Σ gas V M
    right-blame-phases-eval {gas = zero} vV ()
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        with E.step? Σ M in right-step-eq
           | value-question-complete vV
           | value-step-none {Σ = Σ} vV
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        with E.evalFrom (χ ▷ˢ Σ) gas ((χ ▷ᵀ V) ⊕[ op ] N) in next-eq
    right-blame-phases-eval vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | nothing rewrite value-step-eq | right-step-eq | value-eq
          | next-eq with whole-eq
    right-blame-phases-eval vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | nothing | ()
    right-blame-phases-eval vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.returned nextResult)
        rewrite value-step-eq | right-step-eq | value-eq | next-eq
        with whole-eq
    right-blame-phases-eval vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.returned nextResult) | ()
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.blamed nextChanges nextTrace)
        rewrite value-step-eq | right-step-eq | value-eq | next-eq
        with whole-eq
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.blamed nextChanges nextTrace) | refl
        with right-blame-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
          {V = χ ▷ᵀ V} {M = N} (apply-change-value χ vV′) next-eq
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.blamed nextChanges nextTrace) | refl
        | right-phase-blames leftValue rightGas rightBlame
            rightGas≤ =
      right-phase-blames vV′ (suc rightGas)
        (prepend-blamed {Σ = Σ} right-step-eq rightBlame)
        (s≤s rightGas≤)
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
        | just (E.blamed nextChanges nextTrace) | refl
        | delta-phase-blames leftValue rightGas rightResult
            rightReturn deltaGas deltaBlame phases≤ =
      delta-phase-blames vV′ (suc rightGas)
        (prepend-result step rightResult)
        (prepend-return {Σ = Σ} right-step-eq rightReturn)
        deltaGas deltaBlame (s≤s phases≤)
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | nothing | vV′ , value-eq | value-step-eq
        with E.value? M in right-value-eq
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | nothing | vV′ , value-eq | value-step-eq | just vM =
      delta-phase-blames vV′ zero (E.result _ [] M ↠-refl vM)
        (value-return-exact {Σ = Σ} zero vM) (suc gas)
        (blame-from-eval {Σ = Σ} {gas = suc gas} whole-eq) ≤-refl
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | nothing | vV′ , value-eq | value-step-eq | nothing
        with blame-view M
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | nothing | vV′ , value-eq | value-step-eq | nothing
        | is-blame refl =
      right-phase-blames vV′ zero
        (_ , [] , ↠-refl , refl) z≤n
    right-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {V = V} {M = M} vV whole-eq
        | nothing | vV′ , value-eq | value-step-eq | nothing
        | not-blame M≢blame = ⊥-elim impossible
      where
      app-step-none = app-stuck-step-none {Σ = Σ} vV
        right-step-eq right-value-eq M≢blame
      app-eval-none = eval-app-stuck-none {Σ = Σ} {gas = gas} app-step-none

      impossible : ⊥
      impossible with trans (sym app-eval-none) whole-eq
      impossible | ()

    right-blame-phases : ∀ {Δ} {Σ : TyStore Δ}
        {gas : ℕ} {V M : Term Δ}
      → Value V
      → BlamesFrom Σ gas (V ⊕[ op ] M)
      → RightBlamePhases Σ gas V M
    right-blame-phases {Σ = Σ} {gas = gas} {V = V} {M = M}
        vV (Δ′ , changes , trace , whole-eq) =
      right-blame-phases-eval {Σ = Σ} {gas = gas} {V = V} {M = M}
        vV (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)

    data PrimitiveBlamePhases {Δ : TyCtx}
        (Σ : TyStore Δ) (gas : ℕ) (L M : Term Δ) : Set where
      left-phase-blames :
          (leftGas : ℕ)
        → BlamesFrom Σ leftGas L
        → leftGas ≤ gas
        → PrimitiveBlamePhases Σ gas L M

      prim-right-phase-blames :
          (leftGas : ℕ)
        → (leftResult : E.EvalResult L)
        → interpretFrom Σ leftGas L ≡ returned leftResult
        → (rightGas : ℕ)
        → BlamesFrom (E.changes leftResult ▶ˢ Σ) rightGas
            (E.changes leftResult ▶ᵀ M)
        → leftGas + rightGas ≤ gas
        → PrimitiveBlamePhases Σ gas L M

      prim-delta-phase-blames :
          (leftGas : ℕ)
        → (leftResult : E.EvalResult L)
        → interpretFrom Σ leftGas L ≡ returned leftResult
        → (rightGas : ℕ)
        → (rightResult :
            E.EvalResult (E.changes leftResult ▶ᵀ M))
        → interpretFrom (E.changes leftResult ▶ˢ Σ) rightGas
            (E.changes leftResult ▶ᵀ M) ≡ returned rightResult
        → (deltaGas : ℕ)
        → BlamesFrom
            (E.changes rightResult ▶ˢ
              (E.changes leftResult ▶ˢ Σ)) deltaGas
            ((E.changes rightResult ▶ᵀ E.term leftResult)
              ⊕[ op ] E.term rightResult)
        → leftGas + rightGas + deltaGas ≤ gas
        → PrimitiveBlamePhases Σ gas L M

    prim-blame-phases-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
        {gas : ℕ} {L M : Term Δ} {changes : StoreChanges Δ Δ′}
        {trace : L ⊕[ op ] M —↠[ changes ] blame}
      → E.evalFrom Σ gas (L ⊕[ op ] M) ≡ just (E.blamed changes trace)
      → PrimitiveBlamePhases Σ gas L M
    prim-blame-phases-eval {gas = zero} ()
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq
        with E.value? L in left-value-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | just vL
        with right-blame-phases-eval {Σ = Σ} {gas = suc gas}
          {V = L} {M = M} vL whole-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | just vL
        | right-phase-blames leftValue rightGas rightBlame
            rightGas≤ =
      prim-right-phase-blames zero
        (E.result _ [] L ↠-refl leftValue)
        (value-return-exact {Σ = Σ} zero leftValue)
        rightGas rightBlame rightGas≤
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | just vL
        | delta-phase-blames leftValue rightGas rightResult
            rightReturn deltaGas deltaBlame phases≤ =
      prim-delta-phase-blames zero
        (E.result _ [] L ↠-refl leftValue)
        (value-return-exact {Σ = Σ} zero leftValue)
        rightGas rightResult rightReturn deltaGas deltaBlame phases≤
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        with E.step? Σ L in left-step-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        | just (E.step-result χ N step)
        with E.evalFrom (χ ▷ˢ Σ) gas (N ⊕[ op ] (χ ▷ᵀ M)) in next-eq
    prim-blame-phases-eval whole-eq | nothing
        | just (E.step-result χ N step) | nothing
        rewrite left-step-eq | next-eq
        with whole-eq
    prim-blame-phases-eval whole-eq | nothing
        | just (E.step-result χ N step) | nothing | ()
    prim-blame-phases-eval whole-eq | nothing
        | just (E.step-result χ N step) | just (E.returned nextResult)
        rewrite left-step-eq | next-eq
        with whole-eq
    prim-blame-phases-eval whole-eq | nothing
        | just (E.step-result χ N step) | just (E.returned nextResult) | ()
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace)
        rewrite left-step-eq | next-eq
        with whole-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        with prim-blame-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
          {L = N} {M = χ ▷ᵀ M} next-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        | left-phase-blames leftGas leftBlame leftGas≤ =
      left-phase-blames (suc leftGas)
        (prepend-blamed {Σ = Σ} left-step-eq leftBlame)
        (s≤s leftGas≤)
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        | prim-right-phase-blames leftGas leftResult
            leftReturn rightGas rightBlame phases≤ =
      prim-right-phase-blames (suc leftGas)
        (prepend-result step leftResult)
        (prepend-return {Σ = Σ} left-step-eq leftReturn)
        rightGas rightBlame (s≤s phases≤)
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing
        | just (E.step-result χ N step)
        | just (E.blamed nextChanges nextTrace) | refl
        | prim-delta-phase-blames leftGas leftResult
            leftReturn rightGas rightResult rightReturn
            deltaGas deltaBlame phases≤ =
      prim-delta-phase-blames (suc leftGas)
        (prepend-result step leftResult)
        (prepend-return {Σ = Σ} left-step-eq leftReturn)
        rightGas rightResult rightReturn deltaGas deltaBlame
        (s≤s phases≤)
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing | nothing
        with blame-view L | E.step? Σ M in right-step-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing | nothing
        | is-blame refl | just (E.step-result χ N step) =
      left-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing | nothing
        | is-blame refl | nothing =
      left-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing | nothing
        | not-blame L≢blame | just (E.step-result χ N step)
        with E.value? L | left-value-eq
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing | nothing
        | not-blame L≢blame | just (E.step-result χ N step)
        | nothing | refl with E.prim-final? op L M in final-eq
    prim-blame-phases-eval whole-eq | nothing | nothing
        | not-blame L≢blame | just (E.step-result χ N step)
        | nothing | refl | nothing with whole-eq
    prim-blame-phases-eval whole-eq | nothing | nothing
        | not-blame L≢blame | just (E.step-result χ N step)
        | nothing | refl | nothing | ()
    prim-blame-phases-eval {L = L} whole-eq | nothing | nothing
        | not-blame L≢blame | just (E.step-result χ N step)
        | nothing | refl | just (E.step-result ψ P final-step) =
      ⊥-elim impossible
      where
      impossible : ⊥
      impossible with trans (sym final-eq)
        (app-final-left-none L≢blame left-value-eq)
      impossible | ()
    prim-blame-phases-eval {Σ = Σ} {gas = suc gas}
        {L = L} {M = M} whole-eq | nothing | nothing
        | not-blame L≢blame | nothing
        with E.prim-final? op L M in final-eq
    prim-blame-phases-eval whole-eq | nothing | nothing
        | not-blame L≢blame | nothing | nothing with whole-eq
    prim-blame-phases-eval whole-eq | nothing | nothing
        | not-blame L≢blame | nothing | nothing | ()
    prim-blame-phases-eval {L = L} whole-eq | nothing | nothing
        | not-blame L≢blame | nothing
        | just (E.step-result ψ P final-step) =
      ⊥-elim impossible
      where
      impossible : ⊥
      impossible with trans (sym final-eq)
        (app-final-left-none L≢blame left-value-eq)
      impossible | ()

    prim-blame-phases : ∀ {Δ} {Σ : TyStore Δ}
        {gas : ℕ} {L M : Term Δ}
      → BlamesFrom Σ gas (L ⊕[ op ] M)
      → PrimitiveBlamePhases Σ gas L M
    prim-blame-phases {Σ = Σ} {gas = gas} {L = L} {M = M}
        (Δ′ , changes , trace , whole-eq) =
      prim-blame-phases-eval {Σ = Σ} {gas = gas}
        {L = L} {M = M}
        (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)

    prim-return-positive≤ : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
        {L M : Term Δ} {result : E.EvalResult (L ⊕[ op ] M)}
      → interpretFrom Σ gas (L ⊕[ op ] M) ≡ returned result
      → suc zero ≤ gas
    prim-return-positive≤ {gas = zero} ()
    prim-return-positive≤ {gas = suc gas} result-eq = s≤s z≤n

    prim-blame-positive≤ : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
        {L M : Term Δ}
      → BlamesFrom Σ gas (L ⊕[ op ] M)
      → suc zero ≤ gas
    prim-blame-positive≤ {gas = zero}
        (Δ′ , changes , trace , ())
    prim-blame-positive≤ {gas = suc gas} blaming = s≤s z≤n

    assemble-prim-pair : ∀
        {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁ Δᶜ₂ Δᶜ₃}
        {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
        {Aᴾ Aᴵ : Ty Δᶜ₀}
        {q : impEnv (core W₀) I.⊢ Aᴾ ⊑ Aᴵ}
        {Lᴾ Mᴾ : Term Δᴾ₀} {Lᴵ Mᴵ : Term Δᴵ₀}
        {leftResultᴾ : E.EvalResult Lᴾ}
        {leftResultᴵ : E.EvalResult Lᴵ}
        {rightResultᴾ : E.EvalResult
          (E.changes leftResultᴾ ▶ᵀ Mᴾ)}
        {rightResultᴵ : E.EvalResult
          (E.changes leftResultᴵ ▶ᵀ Mᴵ)}
        {deltaResultᴾ : E.EvalResult
          ((E.changes rightResultᴾ ▶ᵀ E.term leftResultᴾ)
            ⊕[ op ] E.term rightResultᴾ)}
        {deltaResultᴵ : E.EvalResult
          ((E.changes rightResultᴵ ▶ᵀ E.term leftResultᴵ)
            ⊕[ op ] E.term rightResultᴵ)}
        {W₁ : World (E.Δ′ leftResultᴾ)
          (E.Δ′ leftResultᴵ) Δᶜ₁}
        {W₂ : World (E.Δ′ rightResultᴾ)
          (E.Δ′ rightResultᴵ) Δᶜ₂}
        {W₃ : World (E.Δ′ deltaResultᴾ)
          (E.Δ′ deltaResultᴵ) Δᶜ₃}
        {j k : ℕ}
      → (W₀≼W₁ : Future W₀ W₁)
      → impreciseStore (core W₁) ≡
          E.changes leftResultᴵ ▶ˢ impreciseStore (core W₀)
      → preciseStore (core W₁) ≡
          E.changes leftResultᴾ ▶ˢ preciseStore (core W₀)
      → (∀ M → E.changes leftResultᴵ ▶ᵀ M ≡
          liftImpreciseTerm W₀≼W₁ M)
      → (∀ M → E.changes leftResultᴾ ▶ᵀ M ≡
          liftPreciseTerm W₀≼W₁ M)
      → (W₁≼W₂ : Future W₁ W₂)
      → impreciseStore (core W₂) ≡
          E.changes rightResultᴵ ▶ˢ impreciseStore (core W₁)
      → preciseStore (core W₂) ≡
          E.changes rightResultᴾ ▶ˢ preciseStore (core W₁)
      → (∀ M → E.changes rightResultᴵ ▶ᵀ M ≡
          liftImpreciseTerm W₁≼W₂ M)
      → (∀ M → E.changes rightResultᴾ ▶ᵀ M ≡
          liftPreciseTerm W₁≼W₂ M)
      → (W₂≼W₃ : Future W₂ W₃)
      → impreciseStore (core W₃) ≡
          E.changes deltaResultᴵ ▶ˢ impreciseStore (core W₂)
      → preciseStore (core W₃) ≡
          E.changes deltaResultᴾ ▶ˢ preciseStore (core W₂)
      → (∀ M → E.changes deltaResultᴵ ▶ᵀ M ≡
          liftImpreciseTerm W₂≼W₃ M)
      → (∀ M → E.changes deltaResultᴾ ▶ᵀ M ≡
          liftPreciseTerm W₂≼W₃ M)
      → j ≡ k
      → ValueImprecision W₃
          (liftCenterImprecision W₂≼W₃
            (liftCenterImprecision W₁≼W₂
              (liftCenterImprecision W₀≼W₁ q)))
          j (E.term deltaResultᴵ) (E.term deltaResultᴾ)
      → PairedReturns W₀ (FutureValueRelation q) k
          (sequence-prim-result leftResultᴵ
            rightResultᴵ deltaResultᴵ)
          (sequence-prim-result leftResultᴾ
            rightResultᴾ deltaResultᴾ)
    assemble-prim-pair {W₀ = W₀} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {q = q}
        {leftResultᴾ = leftResultᴾ}
        {leftResultᴵ = leftResultᴵ}
        {rightResultᴾ = rightResultᴾ}
        {rightResultᴵ = rightResultᴵ}
        {deltaResultᴾ = deltaResultᴾ} {deltaResultᴵ = deltaResultᴵ}
        {W₁ = W₁} {W₂ = W₂} {W₃ = W₃}
        W₀≼W₁ leftStoreᴵ leftStoreᴾ
        leftTermsᴵ leftTermsᴾ
        W₁≼W₂ rightStoreᴵ rightStoreᴾ
        rightTermsᴵ rightTermsᴾ
        W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
        deltaTermsᴵ deltaTermsᴾ indexEq
        deltaValueRelated =
      paired-returns W₃ W₀≼W₃ impreciseStoreEq preciseStoreEq
        impreciseTermsEq preciseTermsEq finalValueRelated
      where
      W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂
      W₀≼W₃ = future-trans W₀≼W₂ W₂≼W₃

      impreciseStoreEq = trans deltaStoreᴵ
        (trans
          (cong (λ Σ → E.changes deltaResultᴵ ▶ˢ Σ) rightStoreᴵ)
          (trans
            (cong (λ Σ → E.changes deltaResultᴵ ▶ˢ
              (E.changes rightResultᴵ ▶ˢ Σ)) leftStoreᴵ)
            (trans
              (apply-stores-++ (E.changes rightResultᴵ)
                (E.changes deltaResultᴵ)
                (E.changes leftResultᴵ ▶ˢ impreciseStore (core W₀)))
              (apply-stores-++ (E.changes leftResultᴵ)
                (E.changes rightResultᴵ ++ˢ E.changes deltaResultᴵ)
                (impreciseStore (core W₀))))))

      preciseStoreEq = trans deltaStoreᴾ
        (trans
          (cong (λ Σ → E.changes deltaResultᴾ ▶ˢ Σ) rightStoreᴾ)
          (trans
            (cong (λ Σ → E.changes deltaResultᴾ ▶ˢ
              (E.changes rightResultᴾ ▶ˢ Σ)) leftStoreᴾ)
            (trans
              (apply-stores-++ (E.changes rightResultᴾ)
                (E.changes deltaResultᴾ)
                (E.changes leftResultᴾ ▶ˢ preciseStore (core W₀)))
              (apply-stores-++ (E.changes leftResultᴾ)
                (E.changes rightResultᴾ ++ˢ E.changes deltaResultᴾ)
                (preciseStore (core W₀))))))

      imprecisePrimitiveResult = sequence-prim-result
        leftResultᴵ rightResultᴵ deltaResultᴵ

      precisePrimitiveResult = sequence-prim-result
        leftResultᴾ rightResultᴾ deltaResultᴾ

      impreciseTermsEq : ∀ M →
          E.changes imprecisePrimitiveResult ▶ᵀ M ≡
            liftImpreciseTerm W₀≼W₃ M
      impreciseTermsEq M = trans
        (sym (apply-terms-++ (E.changes leftResultᴵ)
          (E.changes rightResultᴵ ++ˢ E.changes deltaResultᴵ) M))
        (trans
          (cong (λ N → (E.changes rightResultᴵ ++ˢ
            E.changes deltaResultᴵ) ▶ᵀ N) (leftTermsᴵ M))
          (trans
            (sym (apply-terms-++ (E.changes rightResultᴵ)
              (E.changes deltaResultᴵ) (liftImpreciseTerm W₀≼W₁ M)))
            (trans
              (cong (λ N → E.changes deltaResultᴵ ▶ᵀ N)
                (rightTermsᴵ (liftImpreciseTerm W₀≼W₁ M)))
              (trans
                (deltaTermsᴵ (liftImpreciseTerm W₁≼W₂
                  (liftImpreciseTerm W₀≼W₁ M)))
                (trans
                  (cong (liftImpreciseTerm W₂≼W₃)
                    (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))
                  (sym (liftImpreciseTerm-trans W₀≼W₂ W₂≼W₃ M)))))))

      preciseTermsEq : ∀ M →
          E.changes precisePrimitiveResult ▶ᵀ M ≡
            liftPreciseTerm W₀≼W₃ M
      preciseTermsEq M = trans
        (sym (apply-terms-++ (E.changes leftResultᴾ)
          (E.changes rightResultᴾ ++ˢ E.changes deltaResultᴾ) M))
        (trans
          (cong (λ N → (E.changes rightResultᴾ ++ˢ
            E.changes deltaResultᴾ) ▶ᵀ N) (leftTermsᴾ M))
          (trans
            (sym (apply-terms-++ (E.changes rightResultᴾ)
              (E.changes deltaResultᴾ) (liftPreciseTerm W₀≼W₁ M)))
            (trans
              (cong (λ N → E.changes deltaResultᴾ ▶ᵀ N)
                (rightTermsᴾ (liftPreciseTerm W₀≼W₁ M)))
              (trans
                (deltaTermsᴾ (liftPreciseTerm W₁≼W₂
                  (liftPreciseTerm W₀≼W₁ M)))
                (trans
                  (cong (liftPreciseTerm W₂≼W₃)
                    (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))
                  (sym (liftPreciseTerm-trans W₀≼W₂ W₂≼W₃ M)))))))

      compositeQ = liftCenterImprecision W₀≼W₃ q
      sequentialQ = liftCenterImprecision W₂≼W₃
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ q))

      preciseQEq = trans
        (liftCenterTy-trans W₀≼W₂ W₂≼W₃
          Aᴾ)
        (cong (liftCenterTy W₂≼W₃)
          (liftCenterTy-trans W₀≼W₁ W₁≼W₂
            Aᴾ))

      impreciseQEq = trans
        (liftCenterTy-trans W₀≼W₂ W₂≼W₃
          Aᴵ)
        (cong (liftCenterTy W₂≼W₃)
          (liftCenterTy-trans W₀≼W₁ W₁≼W₂
            Aᴵ))

      finalValueRelated = ClosureProof.value-imprecision-reindex
        compositeQ sequentialQ preciseQEq impreciseQEq
        (value-index-reindex indexEq deltaValueRelated)

    ------------------------------------------------------------------------
    -- Reopening a component relation after a returned phase
    ------------------------------------------------------------------------

    prim-semantic-bounded : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {Γ : CTI.CtxImp (forgetWorld W)}
        {p : primArgTy {Δᴾ} op ⊑ᵂ⟨ core W ⟩ primArgTy {Δᴵ} op}
        {q : primResultTy {Δᴾ} op ⊑ᵂ⟨ core W ⟩
          primResultTy {Δᴵ} op}
        {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
      → (k : ℕ)
      → (∀ j → j ≤ k →
          CompiledTermRelation {W = W} p j Γ Lᴾ Lᴵ)
      → (∀ j → j ≤ k →
          CompiledTermRelation {W = W} p j Γ Mᴾ Mᴵ)
      → CompiledTermRelation {W = W} q k Γ
          (Lᴾ ⊕[ op ] Mᴾ) (Lᴵ ⊕[ op ] Mᴵ)
    prim-semantic-bounded {W = W} {Γ = Γ} {p = p} {q = q}
        {Lᴾ = Lᴾ} {Mᴾ = Mᴾ} {Lᴵ = Lᴵ} {Mᴵ = Mᴵ}
        k L-related M-related W′ W≼W′ γ =
      ClosureProof.computations-related-reindex
        (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
        refl refl (sym imprecise-prim-eq)
        (sym precise-prim-eq)
        (record
          { forward-return = forward
          ; backward-return = backward
          ; forward-blame = forwardBlame
          })
      where
      Lᴵ′ = close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Lᴵ)
      Mᴵ′ = close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Mᴵ)
      Lᴾ′ = close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ Lᴾ)
      Mᴾ′ = close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ Mᴾ)

      imprecise-prim-eq : close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (Lᴵ ⊕[ op ] Mᴵ))
          ≡ Lᴵ′ ⊕[ op ] Mᴵ′
      imprecise-prim-eq = cong
        (close (impreciseClosingSubstitution γ))
        (lift-imprecise-prim W≼W′ op Lᴵ Mᴵ)

      precise-prim-eq : close (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (Lᴾ ⊕[ op ] Mᴾ))
          ≡ Lᴾ′ ⊕[ op ] Mᴾ′
      precise-prim-eq = cong
        (close (preciseClosingSubstitution γ))
        (lift-precise-prim W≼W′ op Lᴾ Mᴾ)

      left-related = L-related k ≤-refl W′ W≼W′ γ

      forward : ∀ {n} {resultᴵ : E.EvalResult (Lᴵ′ ⊕[ op ] Mᴵ′)}
        → n ≤ k
        → interpretFrom (impreciseStore (core W′)) n
            (Lᴵ′ ⊕[ op ] Mᴵ′)
            ≡ returned resultᴵ
        →
          (Σ[ m ∈ ℕ ]
           Σ[ resultᴾ ∈ E.EvalResult (Lᴾ′ ⊕[ op ] Mᴾ′) ]
             interpretFrom (preciseStore (core W′)) m
               (Lᴾ′ ⊕[ op ] Mᴾ′)
               ≡ returned resultᴾ
             × PairedReturns W′
                (FutureValueRelation (liftCenterImprecision W≼W′ q))
                (k ∸ n) resultᴵ resultᴾ)
          ⊎
          (Σ[ m ∈ ℕ ]
            BlamesFrom (preciseStore (core W′)) m (Lᴾ′ ⊕[ op ] Mᴾ′))
      forward {n} n≤k result-eq
          with prim-return-phases
            {Σ = impreciseStore (core W′)} result-eq
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          with forward-return left-related
            (first-phase≤ {a = leftGas} {rightGas} {deltaGas}
              (subst≤ gas-split n≤k)) leftReturn
        where
        subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
        subst≤ refl a≤k = a≤k
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₂ (preciseGas , preciseBlame)
          with left-blame-expand {Σ = preciseStore (core W′)}
            {leftGas = preciseGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseBlame
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₂ (preciseGas , preciseBlame)
          | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          with forward-return right-related rightGas≤ rightPhaseReturn
        where
        phases≤ = subst≤ gas-split n≤k
          where
          subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
          subst≤ refl a≤k = a≤k

        rightGas≤ = second-phase≤
          {a = leftGas} {rightGas} {deltaGas} phases≤

        raw-right-related = compiled-component-future-at
          (M-related (k ∸ leftGas) (m∸n≤m k leftGas))
          W≼W′ γ W′≼W₁ (m∸n≤m k leftGas)

        right-related = ClosureProof.computations-related-reindex
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          refl refl (sym (leftTermsᴵ Mᴵ′))
          (sym (leftTermsᴾ Mᴾ′)) raw-right-related

        rightPhaseReturn =
          return-store-reindex {gas = rightGas}
            {M = E.changes leftResult ▶ᵀ Mᴵ′}
            leftStoreᴵ rightReturn
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₂ (preciseRightGas , preciseRightBlame)
          with prim-right-blame-expand
            {Σ = preciseStore (core W′)}
            {leftGas = preciseLeftGas}
            {rightGas = preciseRightGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseLeftReturn
            (blame-store-reindex {gas = preciseRightGas}
              {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
              (sym leftStoreᴾ) preciseRightBlame)
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₂ (preciseRightGas , preciseRightBlame)
          | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          with forward-return delta-related deltaGas≤ deltaPhaseReturn
        where
        phases≤ = subst≤ gas-split n≤k
          where
          subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
          subst≤ refl a≤k = a≤k

        deltaGas≤ = third-phase≤
          {a = leftGas} {rightGas} {deltaGas} phases≤

        pAtW₁ = liftCenterImprecision W′≼W₁
          (liftCenterImprecision W≼W′ p)

        qAtW₁ = liftCenterImprecision W′≼W₁
          (liftCenterImprecision W≼W′ q)

        explicitLeftAtW₁ = leftValueRelated

        pAtW₂ = liftCenterImprecision W₁≼W₂ pAtW₁
        qAtW₂ = liftCenterImprecision W₁≼W₂ qAtW₁
        explicitLeftAtW₂ = value-imprecision-future W₁≼W₂
          (value-imprecision-downward-to
            (m∸n≤m (k ∸ leftGas) rightGas)
            explicitLeftAtW₁)

        leftValueAtDelta = value-terms-reindex
          (rightTermsᴵ (E.term leftResult))
          (rightTermsᴾ (E.term preciseLeftResult))
          explicitLeftAtW₂

        residual-positive = ≤-trans
          (prim-return-positive≤
            {Σ = E.changes rightResult ▶ˢ
              (E.changes leftResult ▶ˢ impreciseStore (core W′))}
            deltaReturn)
          deltaGas≤

        canonicalLeft = sequential-prim-value-reindex op
          W≼W′ W′≼W₁ W₁≼W₂ leftValueAtDelta

        canonicalRight = sequential-prim-value-reindex op
          W≼W′ W′≼W₁ W₁≼W₂ rightValueRelated

        canonicalDelta = positive-prim-values op
          residual-positive canonicalLeft canonicalRight

        delta-related =
          sequential-prim-computations-reindex op
            W≼W′ W′≼W₁ W₁≼W₂ {q = q} canonicalDelta

        deltaStoreᴵ = trans rightStoreᴵ
          (cong (λ Σ → E.changes rightResult ▶ˢ Σ) leftStoreᴵ)

        deltaPhaseReturn = return-store-reindex {gas = deltaGas}
          {M = (E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult}
          deltaStoreᴵ deltaReturn
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          | inj₂ (preciseDeltaGas , preciseDeltaBlame)
          with prim-delta-blame-expand
            {Σ = preciseStore (core W′)}
            {leftGas = preciseLeftGas}
            {rightGas = preciseRightGas}
            {deltaGas = preciseDeltaGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseLeftReturn preciseRightPhaseReturn
            preciseDeltaPhaseBlame
        where
        preciseRightPhaseReturn = return-store-reindex
          {gas = preciseRightGas}
          {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
          (sym leftStoreᴾ) preciseRightReturn

        deltaStoreᴾ = trans rightStoreᴾ
          (cong (λ Σ → E.changes preciseRightResult ▶ˢ Σ)
            leftStoreᴾ)

        preciseDeltaPhaseBlame = blame-store-reindex
          {gas = preciseDeltaGas}
          {M = (E.changes preciseRightResult ▶ᵀ
            E.term preciseLeftResult) ⊕[ op ] E.term preciseRightResult}
          (sym deltaStoreᴾ) preciseDeltaBlame
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          | inj₂ (preciseDeltaGas , preciseDeltaBlame)
          | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          | inj₁ (preciseDeltaGas , preciseDeltaResult , preciseDeltaReturn ,
              paired-returns W₃ W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
                deltaTermsᴵ deltaTermsᴾ deltaValueRelated)
          with prim-return-expand
            {Σ = preciseStore (core W′)}
            {leftGas = preciseLeftGas}
            {rightGas = preciseRightGas}
            {deltaGas = preciseDeltaGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseLeftReturn preciseRightPhaseReturn
            preciseDeltaPhaseReturn
        where
        preciseRightPhaseReturn = return-store-reindex
          {gas = preciseRightGas}
          {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
          (sym leftStoreᴾ) preciseRightReturn

        deltaStoreFromInitialᴾ = trans rightStoreᴾ
          (cong (λ Σ → E.changes preciseRightResult ▶ˢ Σ)
            leftStoreᴾ)

        preciseDeltaPhaseReturn = return-store-reindex
          {gas = preciseDeltaGas}
          {M = (E.changes preciseRightResult ▶ᵀ
            E.term preciseLeftResult) ⊕[ op ] E.term preciseRightResult}
          (sym deltaStoreFromInitialᴾ) preciseDeltaReturn
      forward {n} n≤k result-eq
          | return-phases leftGas leftResult leftReturn
              rightGas rightResult rightReturn
              deltaGas deltaResult deltaReturn result-split gas-split
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          | inj₁ (preciseDeltaGas , preciseDeltaResult , preciseDeltaReturn ,
              paired-returns W₃ W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
                deltaTermsᴵ deltaTermsᴾ deltaValueRelated)
          | wholeGas , preciseWholeReturn =
            inj₁ (wholeGas , precisePrimitiveResult , preciseWholeReturn ,
              paired-returns-reindex result-split refl assembledPair)
        where
        precisePrimitiveResult = sequence-prim-result
          preciseLeftResult preciseRightResult preciseDeltaResult

        indexEq = trans (subtract-three k leftGas rightGas deltaGas)
          (cong (k ∸_) gas-split)

        assembledPair = assemble-prim-pair
          {W₀ = W′} {q = liftCenterImprecision W≼W′ q}
          {Lᴾ = Lᴾ′} {Mᴾ = Mᴾ′} {Lᴵ = Lᴵ′} {Mᴵ = Mᴵ′}
          {leftResultᴾ = preciseLeftResult}
          {leftResultᴵ = leftResult}
          {rightResultᴾ = preciseRightResult}
          {rightResultᴵ = rightResult}
          {deltaResultᴾ = preciseDeltaResult} {deltaResultᴵ = deltaResult}
          W′≼W₁ leftStoreᴵ leftStoreᴾ
          leftTermsᴵ leftTermsᴾ
          W₁≼W₂ rightStoreᴵ rightStoreᴾ
          rightTermsᴵ rightTermsᴾ
          W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
          deltaTermsᴵ deltaTermsᴾ indexEq
          deltaValueRelated

      backward : ∀ {n} {resultᴾ : E.EvalResult (Lᴾ′ ⊕[ op ] Mᴾ′)}
        → n ≤ k
        → interpretFrom (preciseStore (core W′)) n
            (Lᴾ′ ⊕[ op ] Mᴾ′)
            ≡ returned resultᴾ
        → Σ[ m ∈ ℕ ]
          Σ[ resultᴵ ∈ E.EvalResult (Lᴵ′ ⊕[ op ] Mᴵ′) ]
            interpretFrom (impreciseStore (core W′)) m
              (Lᴵ′ ⊕[ op ] Mᴵ′)
              ≡ returned resultᴵ
            × PairedReturns W′
                (FutureValueRelation (liftCenterImprecision W≼W′ q))
                (k ∸ n) resultᴵ resultᴾ
      backward {n} n≤k result-eq
          with prim-return-phases
            {Σ = preciseStore (core W′)} result-eq
      backward {n} n≤k result-eq
          | return-phases preciseLeftGas preciseLeftResult
              preciseLeftReturn preciseRightGas preciseRightResult
              preciseRightReturn preciseDeltaGas preciseDeltaResult
              preciseDeltaReturn result-split gas-split
          with backward-return left-related leftGas≤
            preciseLeftReturn
        where
        phases≤ = subst≤ gas-split n≤k
          where
          subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
          subst≤ refl a≤k = a≤k

        leftGas≤ = first-phase≤
          {a = preciseLeftGas} {preciseRightGas} {preciseDeltaGas}
          phases≤
      backward {n} n≤k result-eq
          | return-phases preciseLeftGas preciseLeftResult
              preciseLeftReturn preciseRightGas preciseRightResult
              preciseRightReturn preciseDeltaGas preciseDeltaResult
              preciseDeltaReturn result-split gas-split
          | leftGas , leftResult , leftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated
          with backward-return right-related rightGas≤
            rightPhaseReturn
        where
        phases≤ = subst≤ gas-split n≤k
          where
          subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
          subst≤ refl a≤k = a≤k

        rightGas≤ = second-phase≤
          {a = preciseLeftGas} {preciseRightGas} {preciseDeltaGas}
          phases≤

        raw-right-related = compiled-component-future-at
          (M-related (k ∸ preciseLeftGas)
            (m∸n≤m k preciseLeftGas))
          W≼W′ γ W′≼W₁ (m∸n≤m k preciseLeftGas)

        right-related = ClosureProof.computations-related-reindex
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          refl refl (sym (leftTermsᴵ Mᴵ′))
          (sym (leftTermsᴾ Mᴾ′)) raw-right-related

        rightPhaseReturn = return-store-reindex
          {gas = preciseRightGas}
          {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
          leftStoreᴾ preciseRightReturn
      backward {n} n≤k result-eq
          | return-phases preciseLeftGas preciseLeftResult
              preciseLeftReturn preciseRightGas preciseRightResult
              preciseRightReturn preciseDeltaGas preciseDeltaResult
              preciseDeltaReturn result-split gas-split
          | leftGas , leftResult , leftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated
          | rightGas , rightResult , rightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated
          with backward-return delta-related deltaGas≤ deltaPhaseReturn
        where
        phases≤ = subst≤ gas-split n≤k
          where
          subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
          subst≤ refl a≤k = a≤k

        deltaGas≤ = third-phase≤
          {a = preciseLeftGas} {preciseRightGas} {preciseDeltaGas}
          phases≤

        pAtW₁ = liftCenterImprecision W′≼W₁
          (liftCenterImprecision W≼W′ p)

        qAtW₁ = liftCenterImprecision W′≼W₁
          (liftCenterImprecision W≼W′ q)

        explicitLeftAtW₁ = leftValueRelated

        pAtW₂ = liftCenterImprecision W₁≼W₂ pAtW₁
        qAtW₂ = liftCenterImprecision W₁≼W₂ qAtW₁
        explicitLeftAtW₂ = value-imprecision-future W₁≼W₂
          (value-imprecision-downward-to
            (m∸n≤m (k ∸ preciseLeftGas) preciseRightGas)
            explicitLeftAtW₁)

        leftValueAtDelta = value-terms-reindex
          (rightTermsᴵ (E.term leftResult))
          (rightTermsᴾ (E.term preciseLeftResult))
          explicitLeftAtW₂

        residual-positive = ≤-trans
          (prim-return-positive≤
            {Σ = E.changes preciseRightResult ▶ˢ
              (E.changes preciseLeftResult ▶ˢ preciseStore (core W′))}
            preciseDeltaReturn)
          deltaGas≤

        canonicalLeft = sequential-prim-value-reindex op
          W≼W′ W′≼W₁ W₁≼W₂ leftValueAtDelta

        canonicalRight = sequential-prim-value-reindex op
          W≼W′ W′≼W₁ W₁≼W₂ rightValueRelated

        canonicalDelta = positive-prim-values op
          residual-positive canonicalLeft canonicalRight

        delta-related =
          sequential-prim-computations-reindex op
            W≼W′ W′≼W₁ W₁≼W₂ {q = q} canonicalDelta

        deltaStoreᴾ = trans rightStoreᴾ
          (cong (λ Σ → E.changes preciseRightResult ▶ˢ Σ)
            leftStoreᴾ)

        deltaPhaseReturn = return-store-reindex
          {gas = preciseDeltaGas}
          {M = (E.changes preciseRightResult ▶ᵀ
            E.term preciseLeftResult) ⊕[ op ] E.term preciseRightResult}
          deltaStoreᴾ preciseDeltaReturn
      backward {n} n≤k result-eq
          | return-phases preciseLeftGas preciseLeftResult
              preciseLeftReturn preciseRightGas preciseRightResult
              preciseRightReturn preciseDeltaGas preciseDeltaResult
              preciseDeltaReturn result-split gas-split
          | leftGas , leftResult , leftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated
          | rightGas , rightResult , rightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated
          | deltaGas , deltaResult , deltaReturn ,
              paired-returns W₃ W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
                deltaTermsᴵ deltaTermsᴾ deltaValueRelated
          with prim-return-expand
            {Σ = impreciseStore (core W′)} {leftGas = leftGas}
            {rightGas = rightGas} {deltaGas = deltaGas}
            {L = Lᴵ′} {M = Mᴵ′}
            leftReturn rightPhaseReturn deltaPhaseReturn
        where
        rightPhaseReturn = return-store-reindex
          {gas = rightGas} {M = E.changes leftResult ▶ᵀ Mᴵ′}
          (sym leftStoreᴵ) rightReturn

        deltaStoreFromInitialᴵ = trans rightStoreᴵ
          (cong (λ Σ → E.changes rightResult ▶ˢ Σ) leftStoreᴵ)

        deltaPhaseReturn = return-store-reindex
          {gas = deltaGas}
          {M = (E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult}
          (sym deltaStoreFromInitialᴵ) deltaReturn
      backward {n} n≤k result-eq
          | return-phases preciseLeftGas preciseLeftResult
              preciseLeftReturn preciseRightGas preciseRightResult
              preciseRightReturn preciseDeltaGas preciseDeltaResult
              preciseDeltaReturn result-split gas-split
          | leftGas , leftResult , leftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated
          | rightGas , rightResult , rightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated
          | deltaGas , deltaResult , deltaReturn ,
              paired-returns W₃ W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
                deltaTermsᴵ deltaTermsᴾ deltaValueRelated
          | wholeGas , wholeReturn =
            wholeGas , imprecisePrimitiveResult , wholeReturn ,
              paired-returns-reindex refl result-split assembledPair
        where
        imprecisePrimitiveResult = sequence-prim-result
          leftResult rightResult deltaResult

        indexEq = trans
          (subtract-three k preciseLeftGas preciseRightGas
            preciseDeltaGas)
          (cong (k ∸_) gas-split)

        assembledPair = assemble-prim-pair
          {W₀ = W′}
          {q = liftCenterImprecision W≼W′ q}
          {Lᴾ = Lᴾ′} {Mᴾ = Mᴾ′} {Lᴵ = Lᴵ′} {Mᴵ = Mᴵ′}
          {leftResultᴾ = preciseLeftResult}
          {leftResultᴵ = leftResult}
          {rightResultᴾ = preciseRightResult}
          {rightResultᴵ = rightResult}
          {deltaResultᴾ = preciseDeltaResult} {deltaResultᴵ = deltaResult}
          W′≼W₁ leftStoreᴵ leftStoreᴾ
          leftTermsᴵ leftTermsᴾ
          W₁≼W₂ rightStoreᴵ rightStoreᴾ
          rightTermsᴵ rightTermsᴾ
          W₂≼W₃ deltaStoreᴵ deltaStoreᴾ
          deltaTermsᴵ deltaTermsᴾ indexEq
          deltaValueRelated

      forwardBlame : ∀ {n}
        → n ≤ k
        → BlamesFrom (impreciseStore (core W′)) n
            (Lᴵ′ ⊕[ op ] Mᴵ′)
        → Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W′)) m (Lᴾ′ ⊕[ op ] Mᴾ′)
      forwardBlame {n} n≤k blaming
          with prim-blame-phases {Σ = impreciseStore (core W′)}
            {gas = n} {L = Lᴵ′} {M = Mᴵ′} blaming
      forwardBlame {n} n≤k blaming
          | left-phase-blames leftGas leftBlame leftGas≤
          with forward-blame left-related
            (≤-trans leftGas≤ n≤k) leftBlame
      forwardBlame {n} n≤k blaming
          | left-phase-blames leftGas leftBlame leftGas≤
          | preciseLeftGas , preciseLeftBlame
          with left-blame-expand
            {Σ = preciseStore (core W′)} {leftGas = preciseLeftGas}
            {L = Lᴾ′} {M = Mᴾ′} preciseLeftBlame
      forwardBlame {n} n≤k blaming
          | left-phase-blames leftGas leftBlame leftGas≤
          | preciseLeftGas , preciseLeftBlame
          | wholeGas , wholeBlame = wholeGas , wholeBlame
      forwardBlame {n} n≤k blaming
          | prim-right-phase-blames leftGas leftResult
              leftReturn rightGas rightBlame phases≤n
          with forward-return left-related leftGas≤ leftReturn
        where
        phases≤k = ≤-trans phases≤n n≤k

        leftGas≤ : leftGas ≤ k
        leftGas≤ = first-of-two≤ phases≤k
      forwardBlame {n} n≤k blaming
          | prim-right-phase-blames leftGas leftResult
              leftReturn rightGas rightBlame phases≤n
          | inj₂ (preciseLeftGas , preciseLeftBlame)
          with left-blame-expand
            {Σ = preciseStore (core W′)} {leftGas = preciseLeftGas}
            {L = Lᴾ′} {M = Mᴾ′} preciseLeftBlame
      forwardBlame {n} n≤k blaming
          | prim-right-phase-blames leftGas leftResult
              leftReturn rightGas rightBlame phases≤n
          | inj₂ (preciseLeftGas , preciseLeftBlame)
          | wholeGas , wholeBlame = wholeGas , wholeBlame
      forwardBlame {n} n≤k blaming
          | prim-right-phase-blames leftGas leftResult
              leftReturn rightGas rightBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          with forward-blame right-related rightGas≤
            rightPhaseBlame
        where
        phases≤k = ≤-trans phases≤n n≤k

        rightGas≤ : rightGas ≤ k ∸ leftGas
        rightGas≤ = drop-left-≤ phases≤k

        raw-right-related = compiled-component-future-at
          (M-related (k ∸ leftGas) (m∸n≤m k leftGas))
          W≼W′ γ W′≼W₁ (m∸n≤m k leftGas)

        right-related = ClosureProof.computations-related-reindex
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          refl refl (sym (leftTermsᴵ Mᴵ′))
          (sym (leftTermsᴾ Mᴾ′)) raw-right-related

        rightPhaseBlame = blame-store-reindex
          {gas = rightGas} {M = E.changes leftResult ▶ᵀ Mᴵ′}
          leftStoreᴵ rightBlame
      forwardBlame {n} n≤k blaming
          | prim-right-phase-blames leftGas leftResult
              leftReturn rightGas rightBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | preciseRightGas , preciseRightBlame
          with prim-right-blame-expand
            {Σ = preciseStore (core W′)}
            {leftGas = preciseLeftGas}
            {rightGas = preciseRightGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseLeftReturn
            (blame-store-reindex {gas = preciseRightGas}
              {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
              (sym leftStoreᴾ) preciseRightBlame)
      forwardBlame {n} n≤k blaming
          | prim-right-phase-blames leftGas leftResult
              leftReturn rightGas rightBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | preciseRightGas , preciseRightBlame
          | wholeGas , wholeBlame = wholeGas , wholeBlame
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          with forward-return left-related leftGas≤ leftReturn
        where
        phases≤k = ≤-trans phases≤n n≤k

        leftGas≤ = first-phase≤
          {a = leftGas} {rightGas} {deltaGas} phases≤k
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₂ (preciseLeftGas , preciseLeftBlame)
          with left-blame-expand
            {Σ = preciseStore (core W′)} {leftGas = preciseLeftGas}
            {L = Lᴾ′} {M = Mᴾ′} preciseLeftBlame
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₂ (preciseLeftGas , preciseLeftBlame)
          | wholeGas , wholeBlame = wholeGas , wholeBlame
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          with forward-return right-related rightGas≤
            rightPhaseReturn
        where
        phases≤k = ≤-trans phases≤n n≤k

        rightGas≤ = second-phase≤
          {a = leftGas} {rightGas} {deltaGas} phases≤k

        raw-right-related = compiled-component-future-at
          (M-related (k ∸ leftGas) (m∸n≤m k leftGas))
          W≼W′ γ W′≼W₁ (m∸n≤m k leftGas)

        right-related = ClosureProof.computations-related-reindex
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          (liftCenterImprecision W′≼W₁
            (liftCenterImprecision W≼W′ p))
          refl refl (sym (leftTermsᴵ Mᴵ′))
          (sym (leftTermsᴾ Mᴾ′)) raw-right-related

        rightPhaseReturn = return-store-reindex {gas = rightGas}
          {M = E.changes leftResult ▶ᵀ Mᴵ′}
          leftStoreᴵ rightReturn
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₂ (preciseRightGas , preciseRightBlame)
          with prim-right-blame-expand
            {Σ = preciseStore (core W′)}
            {leftGas = preciseLeftGas}
            {rightGas = preciseRightGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseLeftReturn
            (blame-store-reindex {gas = preciseRightGas}
              {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
              (sym leftStoreᴾ) preciseRightBlame)
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₂ (preciseRightGas , preciseRightBlame)
          | wholeGas , wholeBlame = wholeGas , wholeBlame
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          with forward-blame delta-related deltaGas≤ deltaPhaseBlame
        where
        phases≤k = ≤-trans phases≤n n≤k

        deltaGas≤ = third-phase≤
          {a = leftGas} {rightGas} {deltaGas} phases≤k

        pAtW₁ = liftCenterImprecision W′≼W₁
          (liftCenterImprecision W≼W′ p)

        qAtW₁ = liftCenterImprecision W′≼W₁
          (liftCenterImprecision W≼W′ q)

        explicitLeftAtW₁ = leftValueRelated

        pAtW₂ = liftCenterImprecision W₁≼W₂ pAtW₁
        qAtW₂ = liftCenterImprecision W₁≼W₂ qAtW₁
        explicitLeftAtW₂ = value-imprecision-future W₁≼W₂
          (value-imprecision-downward-to
            (m∸n≤m (k ∸ leftGas) rightGas)
            explicitLeftAtW₁)

        leftValueAtDelta = value-terms-reindex
          (rightTermsᴵ (E.term leftResult))
          (rightTermsᴾ (E.term preciseLeftResult))
          explicitLeftAtW₂

        residual-positive = ≤-trans
          (prim-blame-positive≤
            {Σ = E.changes rightResult ▶ˢ
              (E.changes leftResult ▶ˢ impreciseStore (core W′))}
            deltaBlame)
          deltaGas≤

        canonicalLeft = sequential-prim-value-reindex op
          W≼W′ W′≼W₁ W₁≼W₂ leftValueAtDelta

        canonicalRight = sequential-prim-value-reindex op
          W≼W′ W′≼W₁ W₁≼W₂ rightValueRelated

        canonicalDelta = positive-prim-values op
          residual-positive canonicalLeft canonicalRight

        delta-related =
          sequential-prim-computations-reindex op
            W≼W′ W′≼W₁ W₁≼W₂ {q = q} canonicalDelta

        deltaStoreᴵ = trans rightStoreᴵ
          (cong (λ Σ → E.changes rightResult ▶ˢ Σ) leftStoreᴵ)

        deltaPhaseBlame = blame-store-reindex
          {gas = deltaGas}
          {M = (E.changes rightResult ▶ᵀ E.term leftResult)
            ⊕[ op ] E.term rightResult}
          deltaStoreᴵ deltaBlame
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          | preciseDeltaGas , preciseDeltaBlame
          with prim-delta-blame-expand
            {Σ = preciseStore (core W′)}
            {leftGas = preciseLeftGas}
            {rightGas = preciseRightGas}
            {deltaGas = preciseDeltaGas} {L = Lᴾ′} {M = Mᴾ′}
            preciseLeftReturn preciseRightPhaseReturn
            preciseDeltaPhaseBlame
        where
        preciseRightPhaseReturn = return-store-reindex
          {gas = preciseRightGas}
          {M = E.changes preciseLeftResult ▶ᵀ Mᴾ′}
          (sym leftStoreᴾ) preciseRightReturn

        deltaStoreᴾ = trans rightStoreᴾ
          (cong (λ Σ → E.changes preciseRightResult ▶ˢ Σ)
            leftStoreᴾ)

        preciseDeltaPhaseBlame = blame-store-reindex
          {gas = preciseDeltaGas}
          {M = (E.changes preciseRightResult ▶ᵀ
            E.term preciseLeftResult) ⊕[ op ] E.term preciseRightResult}
          (sym deltaStoreᴾ) preciseDeltaBlame
      forwardBlame {n} n≤k blaming
          | prim-delta-phase-blames leftGas leftResult
              leftReturn rightGas rightResult rightReturn
              deltaGas deltaBlame phases≤n
          | inj₁ (preciseLeftGas , preciseLeftResult ,
              preciseLeftReturn ,
              paired-returns W₁ W′≼W₁ leftStoreᴵ leftStoreᴾ
                leftTermsᴵ leftTermsᴾ leftValueRelated)
          | inj₁ (preciseRightGas , preciseRightResult ,
              preciseRightReturn ,
              paired-returns W₂ W₁≼W₂ rightStoreᴵ rightStoreᴾ
                rightTermsᴵ rightTermsᴾ rightValueRelated)
          | preciseDeltaGas , preciseDeltaBlame
          | wholeGas , wholeBlame = wholeGas , wholeBlame

    prim-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {Γ : CTI.CtxImp (forgetWorld W)}
        {p : primArgTy {Δᴾ} op ⊑ᵂ⟨ core W ⟩ primArgTy {Δᴵ} op}
        {q : primResultTy {Δᴾ} op ⊑ᵂ⟨ core W ⟩
          primResultTy {Δᴵ} op}
        {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
      → forgetWorld W ∣ Γ ⊢² Lᴾ ⊑ Lᴵ ∶ p
      → forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p
      → (∀ k → CompiledTermRelation {W = W} p k Γ Lᴾ Lᴵ)
      → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
      → ∀ k → CompiledTermRelation {W = W} q k Γ
          (Lᴾ ⊕[ op ] Mᴾ) (Lᴵ ⊕[ op ] Mᴵ)
    prim-compatible L⊑ M⊑ L-related M-related k =
      prim-semantic-bounded k
        (λ j j≤k → L-related j)
        (λ j j≤k → M-related j)

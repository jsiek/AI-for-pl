module proof.MLBRouteOperationalExperiment where

-- File Charter:
--   * Compares execution of the same closed cast from the bad-GLB endpoint
--     types when coercion synthesis is forced through either incomparable
--     maximal lower bound.
--   * Builds the two narrowing/widening coercion pairs directly from their
--     lower-bound witnesses, then evaluates both observed programs.
--   * Depends on the executable NuTerms evaluator and the checked bad-GLB
--     witnesses from `proof.MLBGlbCounterexample`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; z<s; s<s)
open import Data.Product using (proj₁; proj₂)

open import Types
open import Coercions
import Eval as Eval
import Imprecision as Imp
open import Imprecision using (idᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuReduction
open import NuTerms
open import Primitives using (κℕ)
open import proof.CompileCoercions using
  (coerce-downⁿ; coerce-upʷ; realizes-idᵢᴺᵂ-id-only)
open import proof.MLBGlbExample using
  ( glb-bad-A
  ; glb-bad-B
  ; glb-lower-XY
  ; glb-lower-XY⊑A
  ; glb-lower-XY⊑B
  ; glb-lower-YX
  ; glb-lower-YX⊑A
  ; glb-lower-YX⊑B
  )
open import TypeCheck using
  (IsJust; fromJust; is-just; type-check-expect)
import ImprecisionWf as IWF

------------------------------------------------------------------------
-- The two forced narrowing/widening routes
------------------------------------------------------------------------

route-label : Label
route-label = 72

glb-lower-XY⊑A-old :
  idᵢ zero Imp.⊢ glb-lower-XY ⊑ glb-bad-A
glb-lower-XY⊑A-old =
  Imp.∀ⁱ
    (Imp.ν refl
      ((Imp.idˣ (there (here refl)))
        Imp.↦ (Imp.tagˣ (here refl))))

glb-lower-XY⊑B-old :
  idᵢ zero Imp.⊢ glb-lower-XY ⊑ glb-bad-B
glb-lower-XY⊑B-old =
  Imp.ν refl
    (Imp.∀ⁱ
      ((Imp.tagˣ (there (here refl)))
        Imp.↦ (Imp.idˣ (here refl))))

glb-lower-YX⊑A-old :
  idᵢ zero Imp.⊢ glb-lower-YX ⊑ glb-bad-A
glb-lower-YX⊑A-old =
  Imp.ν refl
    (Imp.∀ⁱ
      ((Imp.idˣ (here refl))
        Imp.↦ (Imp.tagˣ (there (here refl)))))

glb-lower-YX⊑B-old :
  idᵢ zero Imp.⊢ glb-lower-YX ⊑ glb-bad-B
glb-lower-YX⊑B-old =
  Imp.∀ⁱ
    (Imp.ν refl
      ((Imp.tagˣ (here refl))
        Imp.↦ (Imp.idˣ (there (here refl)))))

down-D : Coercion
down-D =
  proj₁
    (coerce-downⁿ route-label
      (IWF.⊑-src-wf glb-lower-XY⊑A)
      (IWF.⊑-tgt-wf glb-lower-XY⊑A)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-XY⊑A-old)

down-D-⊒ :
  id-onlyᵈ ∣ zero ∣ [] ⊢ down-D ∶ glb-bad-A ⊒ glb-lower-XY
down-D-⊒ =
  proj₂
    (coerce-downⁿ route-label
      (IWF.⊑-src-wf glb-lower-XY⊑A)
      (IWF.⊑-tgt-wf glb-lower-XY⊑A)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-XY⊑A-old)

up-D : Coercion
up-D =
  proj₁
    (coerce-upʷ route-label
      (IWF.⊑-src-wf glb-lower-XY⊑B)
      (IWF.⊑-tgt-wf glb-lower-XY⊑B)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-XY⊑B-old)

up-D-⊑ :
  id-onlyᵈ ∣ zero ∣ [] ⊢ up-D ∶ glb-lower-XY ⊑ glb-bad-B
up-D-⊑ =
  proj₂
    (coerce-upʷ route-label
      (IWF.⊑-src-wf glb-lower-XY⊑B)
      (IWF.⊑-tgt-wf glb-lower-XY⊑B)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-XY⊑B-old)

down-E : Coercion
down-E =
  proj₁
    (coerce-downⁿ route-label
      (IWF.⊑-src-wf glb-lower-YX⊑A)
      (IWF.⊑-tgt-wf glb-lower-YX⊑A)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-YX⊑A-old)

down-E-⊒ :
  id-onlyᵈ ∣ zero ∣ [] ⊢ down-E ∶ glb-bad-A ⊒ glb-lower-YX
down-E-⊒ =
  proj₂
    (coerce-downⁿ route-label
      (IWF.⊑-src-wf glb-lower-YX⊑A)
      (IWF.⊑-tgt-wf glb-lower-YX⊑A)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-YX⊑A-old)

up-E : Coercion
up-E =
  proj₁
    (coerce-upʷ route-label
      (IWF.⊑-src-wf glb-lower-YX⊑B)
      (IWF.⊑-tgt-wf glb-lower-YX⊑B)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-YX⊑B-old)

up-E-⊑ :
  id-onlyᵈ ∣ zero ∣ [] ⊢ up-E ∶ glb-lower-YX ⊑ glb-bad-B
up-E-⊑ =
  proj₂
    (coerce-upʷ route-label
      (IWF.⊑-src-wf glb-lower-YX⊑B)
      (IWF.⊑-tgt-wf glb-lower-YX⊑B)
      (realizes-idᵢᴺᵂ-id-only zero)
      glb-lower-YX⊑B-old)

-- A second ambiguous pair whose common lower bounds return `★`.
route-value-A : Ty
route-value-A = `∀ (＇ zero ⇒ ★ ⇒ ★)

route-value-B : Ty
route-value-B = `∀ (★ ⇒ ＇ zero ⇒ ★)

-- `∀X. ∀Y. X → Y → ★`
route-value-D : Ty
route-value-D = `∀ (`∀ (＇ (suc zero) ⇒ ＇ zero ⇒ ★))

-- `∀Y. ∀X. X → Y → ★`
route-value-E : Ty
route-value-E = `∀ (`∀ (＇ zero ⇒ ＇ (suc zero) ⇒ ★))

route-value-D⊑A :
  idᵢ zero ∣ zero ⊢ route-value-D ⊑ route-value-A ⊣ zero
route-value-D⊑A =
  IWF.∀ⁱ
    (IWF.ν refl
      ((IWF.idˣ (there (here refl)) (s<s z<s) z<s)
        IWF.↦ ((IWF.tagˣ (here refl) z<s) IWF.↦ IWF.id★)))

route-value-D⊑B :
  idᵢ zero ∣ zero ⊢ route-value-D ⊑ route-value-B ⊣ zero
route-value-D⊑B =
  IWF.ν refl
    (IWF.∀ⁱ
      ((IWF.tagˣ (there (here refl)) (s<s z<s))
        IWF.↦ ((IWF.idˣ (here refl) z<s z<s) IWF.↦ IWF.id★)))

route-value-E⊑A :
  idᵢ zero ∣ zero ⊢ route-value-E ⊑ route-value-A ⊣ zero
route-value-E⊑A =
  IWF.ν refl
    (IWF.∀ⁱ
      ((IWF.idˣ (here refl) z<s z<s)
        IWF.↦
          ((IWF.tagˣ (there (here refl)) (s<s z<s)) IWF.↦ IWF.id★)))

route-value-E⊑B :
  idᵢ zero ∣ zero ⊢ route-value-E ⊑ route-value-B ⊣ zero
route-value-E⊑B =
  IWF.∀ⁱ
    (IWF.ν refl
      ((IWF.tagˣ (here refl) z<s)
        IWF.↦
          ((IWF.idˣ (there (here refl)) (s<s z<s) z<s) IWF.↦ IWF.id★)))

route-value-D⊑A-old :
  idᵢ zero Imp.⊢ route-value-D ⊑ route-value-A
route-value-D⊑A-old =
  Imp.∀ⁱ
    (Imp.ν refl
      ((Imp.idˣ (there (here refl)))
        Imp.↦ ((Imp.tagˣ (here refl)) Imp.↦ Imp.id★)))

route-value-D⊑B-old :
  idᵢ zero Imp.⊢ route-value-D ⊑ route-value-B
route-value-D⊑B-old =
  Imp.ν refl
    (Imp.∀ⁱ
      ((Imp.tagˣ (there (here refl)))
        Imp.↦ ((Imp.idˣ (here refl)) Imp.↦ Imp.id★)))

route-value-E⊑A-old :
  idᵢ zero Imp.⊢ route-value-E ⊑ route-value-A
route-value-E⊑A-old =
  Imp.ν refl
    (Imp.∀ⁱ
      ((Imp.idˣ (here refl))
        Imp.↦ ((Imp.tagˣ (there (here refl))) Imp.↦ Imp.id★)))

route-value-E⊑B-old :
  idᵢ zero Imp.⊢ route-value-E ⊑ route-value-B
route-value-E⊑B-old =
  Imp.∀ⁱ
    (Imp.ν refl
      ((Imp.tagˣ (here refl))
        Imp.↦ ((Imp.idˣ (there (here refl))) Imp.↦ Imp.id★)))

down-value-D : Coercion
down-value-D =
  proj₁
    (coerce-downⁿ route-label
      (IWF.⊑-src-wf route-value-D⊑A)
      (IWF.⊑-tgt-wf route-value-D⊑A)
      (realizes-idᵢᴺᵂ-id-only zero)
      route-value-D⊑A-old)

up-value-D : Coercion
up-value-D =
  proj₁
    (coerce-upʷ route-label
      (IWF.⊑-src-wf route-value-D⊑B)
      (IWF.⊑-tgt-wf route-value-D⊑B)
      (realizes-idᵢᴺᵂ-id-only zero)
      route-value-D⊑B-old)

down-value-E : Coercion
down-value-E =
  proj₁
    (coerce-downⁿ route-label
      (IWF.⊑-src-wf route-value-E⊑A)
      (IWF.⊑-tgt-wf route-value-E⊑A)
      (realizes-idᵢᴺᵂ-id-only zero)
      route-value-E⊑A-old)

up-value-E : Coercion
up-value-E =
  proj₁
    (coerce-upʷ route-label
      (IWF.⊑-src-wf route-value-E⊑B)
      (IWF.⊑-tgt-wf route-value-E⊑B)
      (realizes-idᵢᴺᵂ-id-only zero)
      route-value-E⊑B-old)

------------------------------------------------------------------------
-- Identical observations around the two route-specific casts
------------------------------------------------------------------------

Nat : Ty
Nat = ‵ `ℕ

nat : ℕ → Term
nat n = $ (κℕ n)

taggedNat : ℕ → Term
taggedNat n = nat n ⟨ Nat ! ⟩

source-A : Term
source-A = Λ (ƛ ((` zero) ⟨ (＇ zero) ! ⟩))

cast-via-D : Term
cast-via-D = source-A ⟨ down-D ⟩ ⟨ up-D ⟩

cast-via-E : Term
cast-via-E = source-A ⟨ down-E ⟩ ⟨ up-E ⟩

instantiate-B-at-Nat : Term → Term
instantiate-B-at-Nat M = ν Nat M (id ★ ↦ unseal zero Nat)

program-via-D : Term
program-via-D = instantiate-B-at-Nat cast-via-D · taggedNat 7

program-via-E : Term
program-via-E = instantiate-B-at-Nat cast-via-E · taggedNat 7

value-program-via-D : Term
value-program-via-D = instantiate-B-at-Nat cast-via-D

value-program-via-E : Term
value-program-via-E = instantiate-B-at-Nat cast-via-E

source-value-A : Term
source-value-A = Λ (ƛ (ƛ (taggedNat 7)))

cast-value-via-D : Term
cast-value-via-D = source-value-A ⟨ down-value-D ⟩ ⟨ up-value-D ⟩

cast-value-via-E : Term
cast-value-via-E = source-value-A ⟨ down-value-E ⟩ ⟨ up-value-E ⟩

instantiate-value-B-at-Nat : Term → Term
instantiate-value-B-at-Nat M =
  ν Nat M (id ★ ↦ (seal Nat zero ↦ id ★))

number-program-via-D : Term
number-program-via-D =
  ((instantiate-value-B-at-Nat cast-value-via-D · taggedNat 3) · nat 5)
    ⟨ Nat ？ ⟩

number-program-via-E : Term
number-program-via-E =
  ((instantiate-value-B-at-Nat cast-value-via-E · taggedNat 3) · nat 5)
    ⟨ Nat ？ ⟩

expect-⊢ :
  (M : Term) →
  (A : Ty) →
  IsJust (type-check-expect zero [] [] M A) →
  zero ∣ [] ∣ [] ⊢ M ⦂ A
expect-⊢ M A ok = fromJust (type-check-expect zero [] [] M A) ok

source-A-⊢ : zero ∣ [] ∣ [] ⊢ source-A ⦂ glb-bad-A
source-A-⊢ = expect-⊢ source-A glb-bad-A is-just

cast-via-D-⊢ : zero ∣ [] ∣ [] ⊢ cast-via-D ⦂ glb-bad-B
cast-via-D-⊢ = expect-⊢ cast-via-D glb-bad-B is-just

cast-via-E-⊢ : zero ∣ [] ∣ [] ⊢ cast-via-E ⦂ glb-bad-B
cast-via-E-⊢ = expect-⊢ cast-via-E glb-bad-B is-just

program-via-D-⊢ : zero ∣ [] ∣ [] ⊢ program-via-D ⦂ Nat
program-via-D-⊢ = expect-⊢ program-via-D Nat is-just

program-via-E-⊢ : zero ∣ [] ∣ [] ⊢ program-via-E ⦂ Nat
program-via-E-⊢ = expect-⊢ program-via-E Nat is-just

value-program-via-D-⊢ :
  zero ∣ [] ∣ [] ⊢ value-program-via-D ⦂ ★ ⇒ Nat
value-program-via-D-⊢ = expect-⊢ value-program-via-D (★ ⇒ Nat) is-just

value-program-via-E-⊢ :
  zero ∣ [] ∣ [] ⊢ value-program-via-E ⦂ ★ ⇒ Nat
value-program-via-E-⊢ = expect-⊢ value-program-via-E (★ ⇒ Nat) is-just

source-value-A-⊢ : zero ∣ [] ∣ [] ⊢ source-value-A ⦂ route-value-A
source-value-A-⊢ = expect-⊢ source-value-A route-value-A is-just

cast-value-via-D-⊢ :
  zero ∣ [] ∣ [] ⊢ cast-value-via-D ⦂ route-value-B
cast-value-via-D-⊢ = expect-⊢ cast-value-via-D route-value-B is-just

cast-value-via-E-⊢ :
  zero ∣ [] ∣ [] ⊢ cast-value-via-E ⦂ route-value-B
cast-value-via-E-⊢ = expect-⊢ cast-value-via-E route-value-B is-just

number-program-via-D-⊢ :
  zero ∣ [] ∣ [] ⊢ number-program-via-D ⦂ Nat
number-program-via-D-⊢ = expect-⊢ number-program-via-D Nat is-just

number-program-via-E-⊢ :
  zero ∣ [] ∣ [] ⊢ number-program-via-E ⦂ Nat
number-program-via-E-⊢ = expect-⊢ number-program-via-E Nat is-just

program-via-D-no• : No• program-via-D
program-via-D-no• =
  no•-·
    (no•-ν
      (no•-⟨⟩
        (no•-⟨⟩
          (no•-Λ (no•-ƛ (no•-⟨⟩ no•-`))))))
    (no•-⟨⟩ no•-$)

program-via-E-no• : No• program-via-E
program-via-E-no• =
  no•-·
    (no•-ν
      (no•-⟨⟩
        (no•-⟨⟩
          (no•-Λ (no•-ƛ (no•-⟨⟩ no•-`))))))
    (no•-⟨⟩ no•-$)

value-program-via-D-no• : No• value-program-via-D
value-program-via-D-no• =
  no•-ν
    (no•-⟨⟩
      (no•-⟨⟩
        (no•-Λ (no•-ƛ (no•-⟨⟩ no•-`)))))

value-program-via-E-no• : No• value-program-via-E
value-program-via-E-no• =
  no•-ν
    (no•-⟨⟩
      (no•-⟨⟩
        (no•-Λ (no•-ƛ (no•-⟨⟩ no•-`)))))

number-program-via-D-no• : No• number-program-via-D
number-program-via-D-no• =
  no•-⟨⟩
    (no•-·
      (no•-·
        (no•-ν
          (no•-⟨⟩
            (no•-⟨⟩
              (no•-Λ (no•-ƛ (no•-ƛ (no•-⟨⟩ no•-$)))))))
        (no•-⟨⟩ no•-$))
      no•-$)

number-program-via-E-no• : No• number-program-via-E
number-program-via-E-no• =
  no•-⟨⟩
    (no•-·
      (no•-·
        (no•-ν
          (no•-⟨⟩
            (no•-⟨⟩
              (no•-Λ (no•-ƛ (no•-ƛ (no•-⟨⟩ no•-$)))))))
        (no•-⟨⟩ no•-$))
      no•-$)

run-gas : ℕ
run-gas = 40

run-D =
  Eval.eval run-gas program-via-D

run-E =
  Eval.eval run-gas program-via-E

run-value-D =
  Eval.eval run-gas value-program-via-D

run-value-E =
  Eval.eval run-gas value-program-via-E

run-number-D =
  Eval.eval run-gas number-program-via-D

run-number-E =
  Eval.eval run-gas number-program-via-E

result-term :
  ∀ {M} →
  Maybe (Eval.EvalOutcome M) →
  Maybe Term
result-term nothing = nothing
result-term (just r) = just (Eval.finalTerm r)

program-via-D-result : result-term run-D ≡ just blame
program-via-D-result = refl

program-via-E-result : result-term run-E ≡ just blame
program-via-E-result = refl

number-program-via-D-result : result-term run-number-D ≡ just (nat 7)
number-program-via-D-result = refl

number-program-via-E-result : result-term run-number-E ≡ just (nat 7)
number-program-via-E-result = refl

data OutcomeKind : Set where
  value-outcome blame-outcome : OutcomeKind

outcome-kind :
  ∀ {M} →
  Eval.EvalOutcome M →
  OutcomeKind
outcome-kind (Eval.returned r) = value-outcome
outcome-kind (Eval.blamed changes trace) = blame-outcome

maybe-outcome-kind :
  ∀ {M} →
  Maybe (Eval.EvalOutcome M) →
  Maybe OutcomeKind
maybe-outcome-kind nothing = nothing
maybe-outcome-kind (just r) = just (outcome-kind r)

value-program-via-D-result :
  maybe-outcome-kind run-value-D ≡ just value-outcome
value-program-via-D-result = refl

value-program-via-E-result :
  maybe-outcome-kind run-value-E ≡ just value-outcome
value-program-via-E-result = refl

------------------------------------------------------------------------
-- Readable views of the evaluator's reduction traces
------------------------------------------------------------------------

data PureStepName : Set where
  δ-⊕-step β-ƛ-step β-Λ•-step : PureStepName
  β-∀•-step β-gen•-step : PureStepName
  β-id-step β-seq-step β-↦-step β-inst-step : PureStepName
  tag-untag-ok-step tag-untag-bad-step seal-unseal-step : PureStepName
  blame-·₁-step blame-·₂-step blame-•-step : PureStepName
  blame-cast-step : PureStepName
  blame-⊕₁-step blame-⊕₂-step : PureStepName

pure-step-name : ∀ {M N} → M —→ N → PureStepName
pure-step-name δ-⊕ = δ-⊕-step
pure-step-name (β vV) = β-ƛ-step
pure-step-name (β-Λ• vV) = β-Λ•-step
pure-step-name (β-∀• vV) = β-∀•-step
pure-step-name (β-gen• vV) = β-gen•-step
pure-step-name (β-id vV) = β-id-step
pure-step-name (β-seq vV) = β-seq-step
pure-step-name (β-↦ vV vW) = β-↦-step
pure-step-name (β-inst vV) = β-inst-step
pure-step-name (tag-untag-ok vV) = tag-untag-ok-step
pure-step-name (tag-untag-bad vV neq) = tag-untag-bad-step
pure-step-name (seal-unseal vV) = seal-unseal-step
pure-step-name blame-·₁ = blame-·₁-step
pure-step-name (blame-·₂ vV) = blame-·₂-step
pure-step-name blame-• = blame-•-step
pure-step-name blame-⟨⟩ = blame-cast-step
pure-step-name blame-⊕₁ = blame-⊕₁-step
pure-step-name (blame-⊕₂ vV) = blame-⊕₂-step

data StepName : Set where
  root : PureStepName → StepName
  allocate-ν : StepName
  under-app-left under-app-right under-cast under-ν : StepName → StepName
  blame-ν-step : StepName
  under-⊕-left under-⊕-right : StepName → StepName

step-name : ∀ {M χ N} → M —→[ χ ] N → StepName
step-name (pure-step M→N) = root (pure-step-name M→N)
step-name (ν-step vV noV) = allocate-ν
step-name (ξ-·₁ L→L′ shiftM) = under-app-left (step-name L→L′)
step-name (ξ-·₂ vV shiftV M→M′) = under-app-right (step-name M→M′)
step-name (ξ-⟨⟩ M→M′) = under-cast (step-name M→M′)
step-name (ξ-ν L→L′) = under-ν (step-name L→L′)
step-name blame-ν = blame-ν-step
step-name (ξ-⊕₁ L→L′ shiftM) = under-⊕-left (step-name L→L′)
step-name (ξ-⊕₂ vL shiftL M→M′) = under-⊕-right (step-name M→M′)

trace-step-names : ∀ {M χs N} → M —↠[ χs ] N → List StepName
trace-step-names ↠-refl = []
trace-step-names (↠-step M→N N↠P) =
  step-name M→N ∷ trace-step-names N↠P

outcome-step-names :
  ∀ {M} →
  Maybe (Eval.EvalOutcome M) →
  Maybe (List StepName)
outcome-step-names nothing = nothing
outcome-step-names (just r) = just (trace-step-names (Eval.outcomeTrace r))

trace-D :
  outcome-step-names run-D ≡
  just
    ( under-app-left (under-ν (root β-inst-step))
    ∷ under-app-left (under-ν allocate-ν)
    ∷ under-app-left (under-ν (under-cast (root β-∀•-step)))
    ∷ under-app-left
        (under-ν (under-cast (under-cast (root β-Λ•-step))))
    ∷ under-app-left allocate-ν
    ∷ under-app-left (under-cast (root β-∀•-step))
    ∷ under-app-left (under-cast (under-cast (root β-gen•-step)))
    ∷ root β-↦-step
    ∷ under-cast (under-app-right (root β-id-step))
    ∷ under-cast (root β-↦-step)
    ∷ under-cast (under-cast (root β-↦-step))
    ∷ under-cast
        (under-cast (under-cast (under-app-right (root β-id-step))))
    ∷ under-cast (under-cast (under-cast (root β-ƛ-step)))
    ∷ under-cast (under-cast (root tag-untag-bad-step))
    ∷ under-cast (root blame-cast-step)
    ∷ root blame-cast-step
    ∷ [] )
trace-D = refl

trace-E :
  outcome-step-names run-E ≡
  just
    ( under-app-left allocate-ν
    ∷ under-app-left (under-cast (root β-∀•-step))
    ∷ under-app-left (under-cast (under-cast (root β-gen•-step)))
    ∷ under-app-left (under-cast (root β-inst-step))
    ∷ under-app-left (under-cast allocate-ν)
    ∷ under-app-left
        (under-cast (under-cast (root β-∀•-step)))
    ∷ under-app-left
        (under-cast (under-cast (under-cast (root β-Λ•-step))))
    ∷ root β-↦-step
    ∷ under-cast (under-app-right (root β-id-step))
    ∷ under-cast (root β-↦-step)
    ∷ under-cast (under-cast (root β-↦-step))
    ∷ under-cast
        (under-cast (under-cast (under-app-right (root β-id-step))))
    ∷ under-cast (under-cast (under-cast (root β-ƛ-step)))
    ∷ under-cast (under-cast (root tag-untag-bad-step))
    ∷ under-cast (root blame-cast-step)
    ∷ root blame-cast-step
    ∷ [] )
trace-E = refl

trace-value-D :
  outcome-step-names run-value-D ≡
  just
    ( under-ν (root β-inst-step)
    ∷ under-ν allocate-ν
    ∷ under-ν (under-cast (root β-∀•-step))
    ∷ under-ν (under-cast (under-cast (root β-Λ•-step)))
    ∷ allocate-ν
    ∷ under-cast (root β-∀•-step)
    ∷ under-cast (under-cast (root β-gen•-step))
    ∷ [] )
trace-value-D = refl

trace-value-E :
  outcome-step-names run-value-E ≡
  just
    ( allocate-ν
    ∷ under-cast (root β-∀•-step)
    ∷ under-cast (under-cast (root β-gen•-step))
    ∷ under-cast (root β-inst-step)
    ∷ under-cast allocate-ν
    ∷ under-cast (under-cast (root β-∀•-step))
    ∷ under-cast (under-cast (under-cast (root β-Λ•-step)))
    ∷ [] )
trace-value-E = refl

trace-number-D :
  outcome-step-names run-number-D ≡
  just
    ( under-cast
        (under-app-left (under-app-left (under-ν (root β-inst-step))))
    ∷ under-cast
        (under-app-left (under-app-left (under-ν allocate-ν)))
    ∷ under-cast
        (under-app-left
          (under-app-left (under-ν (under-cast (root β-∀•-step)))))
    ∷ under-cast
        (under-app-left
          (under-app-left
            (under-ν (under-cast (under-cast (root β-Λ•-step))))))
    ∷ under-cast (under-app-left (under-app-left allocate-ν))
    ∷ under-cast
        (under-app-left
          (under-app-left (under-cast (root β-∀•-step))))
    ∷ under-cast
        (under-app-left
          (under-app-left (under-cast (under-cast (root β-gen•-step)))))
    ∷ under-cast (under-app-left (root β-↦-step))
    ∷ under-cast
        (under-app-left
          (under-cast (under-app-right (root β-id-step))))
    ∷ under-cast (under-app-left (under-cast (root β-↦-step)))
    ∷ under-cast
        (under-app-left (under-cast (under-cast (root β-↦-step))))
    ∷ under-cast
        (under-app-left
          (under-cast
            (under-cast (under-cast (under-app-right (root β-id-step))))))
    ∷ under-cast
        (under-app-left
          (under-cast (under-cast (under-cast (root β-ƛ-step)))))
    ∷ under-cast (root β-↦-step)
    ∷ under-cast (under-cast (root β-↦-step))
    ∷ under-cast
        (under-cast (under-cast (under-app-right (root β-id-step))))
    ∷ under-cast (under-cast (under-cast (root β-↦-step)))
    ∷ under-cast
        (under-cast (under-cast (under-cast (root β-ƛ-step))))
    ∷ under-cast (under-cast (under-cast (root β-id-step)))
    ∷ under-cast (under-cast (root β-id-step))
    ∷ under-cast (root β-id-step)
    ∷ root tag-untag-ok-step
    ∷ [] )
trace-number-D = refl

trace-number-E :
  outcome-step-names run-number-E ≡
  just
    ( under-cast (under-app-left (under-app-left allocate-ν))
    ∷ under-cast
        (under-app-left
          (under-app-left (under-cast (root β-∀•-step))))
    ∷ under-cast
        (under-app-left
          (under-app-left (under-cast (under-cast (root β-gen•-step)))))
    ∷ under-cast
        (under-app-left
          (under-app-left (under-cast (root β-inst-step))))
    ∷ under-cast
        (under-app-left (under-app-left (under-cast allocate-ν)))
    ∷ under-cast
        (under-app-left
          (under-app-left
            (under-cast (under-cast (root β-∀•-step)))))
    ∷ under-cast
        (under-app-left
          (under-app-left
            (under-cast (under-cast (under-cast (root β-Λ•-step))))))
    ∷ under-cast (under-app-left (root β-↦-step))
    ∷ under-cast
        (under-app-left
          (under-cast (under-app-right (root β-id-step))))
    ∷ under-cast (under-app-left (under-cast (root β-↦-step)))
    ∷ under-cast
        (under-app-left (under-cast (under-cast (root β-↦-step))))
    ∷ under-cast
        (under-app-left
          (under-cast
            (under-cast (under-cast (under-app-right (root β-id-step))))))
    ∷ under-cast
        (under-app-left
          (under-cast (under-cast (under-cast (root β-ƛ-step)))))
    ∷ under-cast (root β-↦-step)
    ∷ under-cast (under-cast (root β-↦-step))
    ∷ under-cast
        (under-cast (under-cast (under-app-right (root β-id-step))))
    ∷ under-cast (under-cast (under-cast (root β-↦-step)))
    ∷ under-cast
        (under-cast (under-cast (under-cast (root β-ƛ-step))))
    ∷ under-cast (under-cast (under-cast (root β-id-step)))
    ∷ under-cast (under-cast (root β-id-step))
    ∷ under-cast (root β-id-step)
    ∷ root tag-untag-ok-step
    ∷ [] )
trace-number-E = refl

module proof.InterpreterSyntacticValueComputationProof where

-- File Charter:
--   * Proves return uniqueness and blame impossibility for syntactic values.
--   * Follows only the direct interpreter and `closeValue` equations.
--   * Contains no small-step reduction, catch-up result, or DGG theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.WithK using
  (≡-irrelevant)
open import Relation.Nullary using (yes; no)

import Coercions as C
open import Interpreter
import NuTerms as N
open import proof.InterpreterCloseValueTyping using
  (syntacticValue-complete)
open import Types using (Ground; ★⇒★; ＇_; ‵_)


ground-irrelevant :
  ∀ {G} →
  (g h : Ground G) →
  g ≡ h
ground-irrelevant (＇ X) (＇ .X) =
  refl
ground-irrelevant (‵ ι) (‵ .ι) =
  refl
ground-irrelevant ★⇒★ ★⇒★ =
  refl


seal-name-injective :
  ∀ {α β} →
  seal-name α ≡ seal-name β →
  α ≡ β
seal-name-injective refl =
  refl


runtime-ground-irrelevant :
  ∀ {θ G} →
  (g h : RuntimeGround θ G) →
  g ≡ h
runtime-ground-irrelevant
    (seal-variable-ground {α = α} name-eq)
    (seal-variable-ground {α = β} name-eq′)
    with seal-name-injective
      (just-injective (trans (sym name-eq) name-eq′))
runtime-ground-irrelevant
    (seal-variable-ground name-eq)
    (seal-variable-ground name-eq′) | refl
    rewrite ≡-irrelevant name-eq name-eq′ =
  refl
runtime-ground-irrelevant (base-ground ι) (base-ground .ι) =
  refl
runtime-ground-irrelevant function-ground function-ground =
  refl


inert-irrelevant :
  ∀ {c} →
  (i j : C.Inert c) →
  i ≡ j
inert-irrelevant (G C.!) (.G C.!) =
  refl
inert-irrelevant (C.seal A X) (C.seal .A .X) =
  refl
inert-irrelevant (c C.↦ d) (.c C.↦ .d) =
  refl
inert-irrelevant (C.`∀ c) (C.`∀ .c) =
  refl
inert-irrelevant (C.gen A c) (C.gen .A .c) =
  refl


syntactic-value-irrelevant :
  ∀ {M} →
  (v w : N.Value M) →
  v ≡ w
syntactic-value-irrelevant (N.ƛ M) (N.ƛ .M) =
  refl
syntactic-value-irrelevant (N.Λ v) (N.Λ w)
    rewrite syntactic-value-irrelevant v w =
  refl
syntactic-value-irrelevant (N.$ κ) (N.$ .κ) =
  refl
syntactic-value-irrelevant (v N.⟨ i ⟩) (w N.⟨ j ⟩)
    rewrite syntactic-value-irrelevant v w
          | inert-irrelevant i j =
  refl


immediate-return :
  World →
  Value →
  StepIndex →
  Outcome
immediate-return W V zero =
  timed W
immediate-return W V (suc n) =
  returned W V


returned-outcome :
  World →
  Value →
  Outcome
returned-outcome W V =
  returned W V


timed-outcome :
  World →
  Outcome
timed-outcome W =
  timed W


blamed-outcome :
  World →
  Outcome
blamed-outcome W =
  blamed W


failed-outcome :
  World →
  ErrorKind →
  Outcome
failed-outcome W e =
  failed W e


type-abstraction-computation :
  ∀ {W γ θ M V}
    (vM : N.Value M) →
  syntacticValue? M ≡ yes vM →
  closeValue (N.Λ vM) γ θ ≡ just V →
  ∀ n →
  interpret W γ θ (N.Λ M) n ≡ immediate-return W V n
type-abstraction-computation vM decision close zero =
  refl
type-abstraction-computation vM decision close (suc n)
    rewrite decision | close =
  refl


returned-shape :
  ∀ {W U V V′} →
  returned-outcome W V ≡ returned U V′ →
  (U ≡ W) × (V′ ≡ V)
returned-shape refl =
  refl , refl


timed-returned-impossible :
  ∀ {W U V} →
  timed-outcome W ≡ returned U V →
  ⊥
timed-returned-impossible ()


blamed-returned-impossible :
  ∀ {W U V} →
  blamed-outcome W ≡ returned U V →
  ⊥
blamed-returned-impossible ()


failed-returned-impossible :
  ∀ {W U e V} →
  failed-outcome W e ≡ returned U V →
  ⊥
failed-returned-impossible ()


timed-blamed-impossible :
  ∀ {W U} →
  timed-outcome W ≡ blamed U →
  ⊥
timed-blamed-impossible ()


failed-blamed-impossible :
  ∀ {W U e} →
  failed-outcome W e ≡ blamed U →
  ⊥
failed-blamed-impossible ()


returned-blamed-impossible :
  ∀ {W U V} →
  returned-outcome W V ≡ blamed U →
  ⊥
returned-blamed-impossible ()


continue-cast :
  TypeEnvironment →
  C.Coercion →
  StepIndex →
  Outcome →
  Outcome
continue-cast θ c n (timed W) =
  timed W
continue-cast θ c n (blamed W) =
  blamed W
continue-cast θ c n (failed W e) =
  failed W e
continue-cast θ c n (returned W V) =
  coerceValue W θ c V n


interpret-cast-computation :
  ∀ {W γ θ M c n outcome} →
  interpret W γ θ M n ≡ outcome →
  interpret W γ θ (M N.⟨ c ⟩) (suc n) ≡
    continue-cast θ c n outcome
interpret-cast-computation
    {W} {γ} {θ} {M} {c} {n} {timed W₁} body-eq
    rewrite body-eq =
  refl
interpret-cast-computation
    {W} {γ} {θ} {M} {c} {n} {blamed W₁} body-eq
    rewrite body-eq =
  refl
interpret-cast-computation
    {W} {γ} {θ} {M} {c} {n} {failed W₁ e} body-eq
    rewrite body-eq =
  refl
interpret-cast-computation
    {W} {γ} {θ} {M} {c} {n} {returned W₁ V} body-eq
    rewrite body-eq =
  refl


interpret-cast-blame-outcome :
  ∀ {W U γ θ M c n outcome} →
  interpret W γ θ M n ≡ outcome →
  interpret W γ θ (M N.⟨ c ⟩) (suc n) ≡ blamed U →
  continue-cast θ c n outcome ≡ blamed U
interpret-cast-blame-outcome
    {W} {U} {γ} {θ} {M} {c} {n} {outcome}
    body-eq outer-eq =
  trans
    (sym
      (interpret-cast-computation
        {W = W} {γ = γ} {θ = θ} {M = M} {c = c} {n = n}
        {outcome = outcome} body-eq))
    outer-eq


type-abstraction-failure-computation :
  ∀ {W γ θ M}
    (vM : N.Value M) →
  syntacticValue? M ≡ yes vM →
  closeValue (N.Λ vM) γ θ ≡ nothing →
  ∀ n →
  interpret W γ θ (N.Λ M) (suc n) ≡
    failed W expected-value-under-type-abstraction
type-abstraction-failure-computation vM decision close n
    rewrite decision | close =
  refl


coerce-inert-never-blames :
  ∀ {W U θ c V n} →
  C.Inert c →
  coerceValue W θ c V n ≡ blamed U →
  ⊥
coerce-inert-never-blames {n = zero} inert ()
coerce-inert-never-blames {θ = θ} {n = suc n} (G C.!) eq
    with ground? θ G
coerce-inert-never-blames {θ = θ} {n = suc n} (G C.!) ()
    | no ¬gG
coerce-inert-never-blames {θ = θ} {n = suc n} (G C.!) ()
    | yes runtime-ground
coerce-inert-never-blames {θ = θ} {n = suc n} (C.seal A X) eq
    with lookup θ X
coerce-inert-never-blames {θ = θ} {n = suc n} (C.seal A X) ()
    | just (seal-name α)
coerce-inert-never-blames {θ = θ} {n = suc n} (C.seal A X) ()
    | just (abstract-name Y)
coerce-inert-never-blames {θ = θ} {n = suc n} (C.seal A X) ()
    | nothing
coerce-inert-never-blames {n = suc n} (c C.↦ d) ()
coerce-inert-never-blames {n = suc n} (C.`∀ c) ()
coerce-inert-never-blames {n = suc n} (C.gen A c) ()


syntactic-value-return-unique :
  ∀ {W U γ θ M V V′ n}
    (vM : N.Value M) →
  closeValue vM γ θ ≡ just V →
  interpret W γ θ M n ≡ returned U V′ →
  (U ≡ W) × (V′ ≡ V)
syntactic-value-return-unique {n = zero} (N.ƛ M) refl ()
syntactic-value-return-unique {n = suc n} (N.ƛ M) refl refl =
  refl , refl
syntactic-value-return-unique
    {γ = γ} {θ} {n = zero} (N.Λ vM) close-eq ()
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n}
    (N.Λ vM) close-eq result-eq
    with syntacticValue-complete vM
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n}
    (N.Λ vM) close-eq result-eq
    | vM′ , decision
    with syntactic-value-irrelevant vM′ vM
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n}
    (N.Λ vM) close-eq result-eq
    | .vM , decision | refl =
  returned-shape
    (trans
      (sym
        (type-abstraction-computation
          vM decision close-eq (suc n)))
      result-eq)
syntactic-value-return-unique {n = zero} (N.$ κ) refl ()
syntactic-value-return-unique {n = suc n} (N.$ κ) refl refl =
  refl , refl
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = zero} (vM N.⟨ G C.! ⟩)
    close-eq ()
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    close-eq result-eq
    with ground? θ G | closeValue vM γ θ in body-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    () result-eq
    | no ¬gG | body-result
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    () result-eq
    | yes gG | nothing
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀
    with interpret W γ θ _ n in body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | timed W₁
  = ⊥-elim
      (timed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = G C.!} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | blamed W₁
  = ⊥-elim
      (blamed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = G C.!} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | failed W₁ e
  = ⊥-elim
      (failed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = G C.!} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | returned W₁ V₁
    with syntactic-value-return-unique
      {W = W} {γ = γ} {θ = θ} {n = n}
      vM body-eq body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | returned .W .V₀
    | refl , refl
    rewrite body-result-eq
    with n
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ G C.! ⟩)
    refl ()
    | yes runtime-ground | just V₀ | returned .W .V₀
    | refl , refl | zero
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | returned .W .V₀
    | refl , refl | suc k
    with ground? θ G
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | returned .W .V₀
    | refl , refl | suc k | no not-runtime-ground =
  ⊥-elim (not-runtime-ground runtime-ground)
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ G C.! ⟩)
    refl result-eq
    | yes runtime-ground | just V₀ | returned .W .V₀
    | refl , refl | suc k | yes runtime-ground′
    rewrite runtime-ground-irrelevant runtime-ground′ runtime-ground =
  returned-shape result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = zero} (vM N.⟨ C.seal A X ⟩)
    close-eq ()
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    close-eq result-eq
    with lookup θ X in name-eq | closeValue vM γ θ in body-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    () result-eq
    | just (abstract-name Y) | body-result
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    () result-eq
    | nothing | body-result
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    () result-eq
    | just (seal-name α) | nothing
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀
    with interpret W γ θ _ n in body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀ | timed W₁
  = ⊥-elim
      (timed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.seal A X} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀ | blamed W₁
  = ⊥-elim
      (blamed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.seal A X} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀ | failed W₁ e
  = ⊥-elim
      (failed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.seal A X} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀ | returned W₁ V₁
    with syntactic-value-return-unique
      {W = W} {γ = γ} {θ = θ} {n = n}
      vM body-eq body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀ | returned .W .V₀
    | refl , refl
    rewrite body-result-eq
    with n
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ C.seal A X ⟩)
    refl ()
    | just (seal-name α) | just V₀ | returned .W .V₀
    | refl , refl | zero
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ C.seal A X ⟩)
    refl result-eq
    | just (seal-name α) | just V₀ | returned .W .V₀
    | refl , refl | suc k
    rewrite name-eq =
  returned-shape result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = zero} (vM N.⟨ c C.↦ d ⟩)
    close-eq ()
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    close-eq result-eq
    with closeValue vM γ θ in body-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    () result-eq | nothing
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    refl result-eq | just V₀
    with interpret W γ θ _ n in body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    refl result-eq
    | just V₀ | timed W₁
  = ⊥-elim
      (timed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = c C.↦ d} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    refl result-eq
    | just V₀ | blamed W₁
  = ⊥-elim
      (blamed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = c C.↦ d} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    refl result-eq
    | just V₀ | failed W₁ e
  = ⊥-elim
      (failed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = c C.↦ d} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    refl result-eq
    | just V₀ | returned W₁ V₁
    with syntactic-value-return-unique
      {W = W} {γ = γ} {θ = θ} {n = n}
      vM body-eq body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ c C.↦ d ⟩)
    refl result-eq
    | just V₀ | returned .W .V₀ | refl , refl
    rewrite body-result-eq
    with n
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ c C.↦ d ⟩)
    refl ()
    | just V₀ | returned .W .V₀ | refl , refl | zero
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ c C.↦ d ⟩)
    refl refl
    | just V₀ | returned .W .V₀ | refl , refl | suc k =
  refl , refl
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = zero} (vM N.⟨ C.`∀ c ⟩)
    close-eq ()
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    close-eq result-eq
    with closeValue vM γ θ in body-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    () result-eq | nothing
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    refl result-eq | just V₀
    with interpret W γ θ _ n in body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    refl result-eq
    | just V₀ | timed W₁
  = ⊥-elim
      (timed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.`∀ c} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    refl result-eq
    | just V₀ | blamed W₁
  = ⊥-elim
      (blamed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.`∀ c} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    refl result-eq
    | just V₀ | failed W₁ e
  = ⊥-elim
      (failed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.`∀ c} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    refl result-eq
    | just V₀ | returned W₁ V₁
    with syntactic-value-return-unique
      {W = W} {γ = γ} {θ = θ} {n = n}
      vM body-eq body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.`∀ c ⟩)
    refl result-eq
    | just V₀ | returned .W .V₀ | refl , refl
    rewrite body-result-eq
    with n
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ C.`∀ c ⟩)
    refl ()
    | just V₀ | returned .W .V₀ | refl , refl | zero
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ C.`∀ c ⟩)
    refl refl
    | just V₀ | returned .W .V₀ | refl , refl | suc k =
  refl , refl
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = zero} (vM N.⟨ C.gen A c ⟩)
    close-eq ()
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    close-eq result-eq
    with closeValue vM γ θ in body-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    () result-eq | nothing
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    refl result-eq | just V₀
    with interpret W γ θ _ n in body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    refl result-eq
    | just V₀ | timed W₁
  = ⊥-elim
      (timed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.gen A c} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    refl result-eq
    | just V₀ | blamed W₁
  = ⊥-elim
      (blamed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.gen A c} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    refl result-eq
    | just V₀ | failed W₁ e
  = ⊥-elim
      (failed-returned-impossible
        (trans (sym (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {c = C.gen A c} {n = n}
          body-result-eq))
          result-eq))
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    refl result-eq
    | just V₀ | returned W₁ V₁
    with syntactic-value-return-unique
      {W = W} {γ = γ} {θ = θ} {n = n}
      vM body-eq body-result-eq
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} {n = suc n} (vM N.⟨ C.gen A c ⟩)
    refl result-eq
    | just V₀ | returned .W .V₀ | refl , refl
    rewrite body-result-eq
    with n
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ C.gen A c ⟩)
    refl ()
    | just V₀ | returned .W .V₀ | refl , refl | zero
syntactic-value-return-unique
    {W = W} {γ = γ} {θ} (vM N.⟨ C.gen A c ⟩)
    refl refl
    | just V₀ | returned .W .V₀ | refl , refl | suc k =
  refl , refl


mutual

  syntactic-value-never-blames :
    ∀ {W U γ θ M n} →
    N.Value M →
    interpret W γ θ M n ≡ blamed U →
    ⊥
  syntactic-value-never-blames {n = zero} vM ()
  syntactic-value-never-blames {n = suc n} (N.ƛ M) ()
  syntactic-value-never-blames
      {W = W} {U} {γ = γ} {θ} {n = suc n} (N.Λ vM) eq
      with syntacticValue? _ in decision-eq
  syntactic-value-never-blames
      {W = W} {U} {γ = γ} {θ} {n = suc n} (N.Λ vM) eq
      | no ¬v =
    ⊥-elim (¬v vM)
  syntactic-value-never-blames
      {W = W} {U} {γ = γ} {θ} {n = suc n} (N.Λ vM) eq
      | yes vM′
      with closeValue (N.Λ vM′) γ θ in close-eq
  syntactic-value-never-blames
      {W = W} {U} {γ = γ} {θ} {n = suc n} (N.Λ vM) eq
      | yes vM′ | just V =
    ⊥-elim
      (returned-blamed-impossible
        (trans
          (sym
            (type-abstraction-computation
              vM′ decision-eq close-eq (suc n)))
          eq))
  syntactic-value-never-blames
      {W = W} {U} {γ = γ} {θ} {n = suc n} (N.Λ vM) eq
      | yes vM′ | nothing =
    ⊥-elim
      (failed-blamed-impossible
        (trans
          (sym
            (type-abstraction-failure-computation
              vM′ decision-eq close-eq n))
          eq))
  syntactic-value-never-blames {n = suc n} (N.$ κ) ()
  syntactic-value-never-blames
      {W = W} {U} {γ = γ} {θ}
      {M = V N.⟨ c ⟩} {n = suc n} (vM N.⟨ inert ⟩) eq =
    cast-value-never-blames
      {W = W} {U = U} {γ = γ} {θ = θ}
      {V = V} {c = c} {n = n} vM inert eq
      (interpret W γ θ V n) refl

  cast-value-never-blames :
    ∀ {W U γ θ V c n} →
    (vV : N.Value V) →
    (inert : C.Inert c) →
    interpret W γ θ (V N.⟨ c ⟩) (suc n) ≡ blamed U →
    (outcome : Outcome) →
    interpret W γ θ V n ≡ outcome →
    ⊥
  cast-value-never-blames
      {W} {U} {γ} {θ} {V} {c} {n}
      vV inert outer-eq (timed W₁) body-eq =
    ⊥-elim
      (timed-blamed-impossible
        (interpret-cast-blame-outcome
          {W = W} {U = U} {γ = γ} {θ = θ}
          {M = V} {c = c} {n = n}
          body-eq outer-eq))
  cast-value-never-blames
      {W} {U} {γ} {θ} {V} {c} {n}
      vV inert outer-eq (blamed W₁) body-eq =
    syntactic-value-never-blames
      {W = W} {U = W₁} {γ = γ} {θ = θ} {M = V} {n = n}
      vV body-eq
  cast-value-never-blames
      {W} {U} {γ} {θ} {V} {c} {n}
      vV inert outer-eq (failed W₁ e) body-eq =
    ⊥-elim
      (failed-blamed-impossible
        (interpret-cast-blame-outcome
          {W = W} {U = U} {γ = γ} {θ = θ}
          {M = V} {c = c} {n = n}
          body-eq outer-eq))
  cast-value-never-blames
      {W} {U} {γ} {θ} {V} {c} {n}
      vV inert outer-eq (returned W₁ Q) body-eq =
    coerce-inert-never-blames
      {W = W₁} {U = U} {θ = θ} {c = c} {V = Q} {n = n}
      inert
      (interpret-cast-blame-outcome
        {W = W} {U = U} {γ = γ} {θ = θ}
        {M = V} {c = c} {n = n}
        body-eq outer-eq)

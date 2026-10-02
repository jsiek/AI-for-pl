module T6D8a3OccurrenceFeasibilityProbe where

-- File Charter:
--   * Calibrates occurrence-harvested substitution on the D8a2 entangled
--     tagged-sealed caller argument, without a substitution induction.
--   * Builds a body that really uses the beta variable below a source reveal
--     at the rebased premise world and checks that its harvested image
--     obligation is empty.
--   * Checks that substituting before replaying the wrapper leaves the image
--     pair below that same wrapper, where the needed premise is still empty.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; ★; ＇_; `ℕ; ‵_; _⇒_)
import Imprecision as I
open import Conversion using (Conv↑; seal; id↑; _↦↑_)
open import CastTerms using
  (Term; singleSub; subst; `_ ; ƛ_; _·_; _↑_)
import proof.DGG.CastTermImprecision2 as CTI2
import T6D8a2ClosedValueRebaseTransportProbe as P
import T6D8a2CallerSupplyProbe as Caller


root-context : CTI2.CtxImp P.W
root-context = CTI2.ctx-imp ★ ★ I.★⊑★ ∷ []

premise-context : CTI2.CtxImp P.Wᵖ
premise-context = CTI2.ctx-imp ★ ★ I.★⊑★ ∷ []

p-use : ★ CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ ★
p-use = I.★⊑★

p-pivot-star : (＇ P.X) CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ ★
p-pivot-star = I.X⊑★ refl

p-premise-function :
  ((＇ P.X) ⇒ ★) CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ (★ ⇒ ★)
p-premise-function = I.⇒⊑⇒ p-pivot-star p-use

p-root-body :
  ((‵ `ℕ) ⇒ ★) CTI2.⊑ᵂ⟨ P.W ⟩ (★ ⇒ ★)
p-root-body = I.⇒⊑⇒ I.ι⊑★ I.★⊑★

source-core : Term 1
source-core = ƛ (` 1)

target-core : Term 2
target-core = ƛ (` 1)

use-relation :
  P.Wᵖ CTI2.∣
    (CTI2.ctx-imp (＇ P.X) ★ p-pivot-star ∷ premise-context)
    ⊢² ` 1 ⊑ ` 1 ∶ p-use
use-relation = CTI2.x⊑x² (CTI2.Sʷ CTI2.Zʷ)

core-at-premise :
  P.Wᵖ CTI2.∣ premise-context ⊢²
    source-core ⊑ target-core ∶ p-premise-function
core-at-premise = CTI2.ƛ⊑ƛ² use-relation

source-wrapper : Conv↑ 1 ((＇ P.X) ⇒ ★) ((‵ `ℕ) ⇒ ★)
source-wrapper = seal P.X (‵ `ℕ) ↦↑ id↑ ★

source-wrapper-typed :
  CTI2.sourceStoreʷ P.W CTI2.⊢↑[ just P.X ] source-wrapper
source-wrapper-typed =
  CTI2.⊢↑-⇒ˣ CTI2.join-left
    (CTI2.⊢↓-sealˣ P.source-entry) CTI2.⊢↑-idˣ

source-body : Term 1
source-body = source-core ↑ source-wrapper

target-body : Term 2
target-body = target-core

body-at-root :
  P.W CTI2.∣ root-context ⊢²
    source-body ⊑ target-body ∶ p-root-body
body-at-root =
  CTI2.reveal⊑² P.mono-forward
    (CTI2.rebase-varᴸ P.forward-rebase)
    (CTI2.same-∷ CTI2.same-[])
    source-wrapper-typed core-at-premise p-root-body

source-function : Term 1
source-function = ƛ source-body

target-function : Term 2
target-function = ƛ target-body

function-at-root :
  P.W CTI2.∣ [] ⊢² source-function ⊑ target-function ∶
    I.⇒⊑⇒ I.★⊑★ p-root-body
function-at-root = CTI2.ƛ⊑ƛ² body-at-root

application-at-root :
  P.W CTI2.∣ [] ⊢²
    source-function · Caller.source-argument ⊑
    target-function · Caller.target-argument ∶ p-root-body
application-at-root =
  CTI2.·⊑·² function-at-root Caller.argument-at-W

harvested-obligation-empty :
  P.Wᵖ CTI2.∣ [] ⊢²
    singleSub Caller.source-argument 0 ⊑
    singleSub Caller.target-argument 0 ∶ p-use
  → ⊥
harvested-obligation-empty = Caller.argument-at-Wᵖ-empty

base-to-target-variable-empty : ∀ {W′ : CTI2.World 1 2 2}
  → (‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ (＇ P.Y-old)
  → ⊥
base-to-target-variable-empty ()

constant-to-target-tag-empty : ∀ {W′ : CTI2.World 1 2 2}
    {γ : CTI2.CtxImp W′} {p : (‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ ★}
  → W′ CTI2.∣ γ ⊢²
      P.source-value ⊑ Caller.target-argument ∶ p
  → ⊥
constant-to-target-tag-empty {W′ = W′}
    (CTI2.⊑cast² {p = p} c′ rel q) =
  base-to-target-variable-empty {W′ = W′} p

source-seal-to-target-tag-empty : ∀ {γ : CTI2.CtxImp P.Wᵖ}
    {p : (＇ P.X) CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ ★}
  → P.Wᵖ CTI2.∣ γ ⊢²
      P.source-sealed ⊑ Caller.target-argument ∶ p
  → ⊥
source-seal-to-target-tag-empty
    (CTI2.⊑cast² {p = p} c′ rel q) =
  P.pivot-old-at-Wᵖ-empty p
source-seal-to-target-tag-empty
    (CTI2.conceal⊑² ok mono rebase sc c⊢ rel q) =
  constant-to-target-tag-empty rel

argument-at-premise-under-any-context-empty :
  ∀ {γ : CTI2.CtxImp P.Wᵖ}
  → P.Wᵖ CTI2.∣ γ ⊢²
      Caller.source-argument ⊑ Caller.target-argument ∶ p-use
  → ⊥
argument-at-premise-under-any-context-empty
    (CTI2.cast⊑cast² {p = p} c c′ rel .I.★⊑★) =
  P.pivot-old-at-Wᵖ-empty p
argument-at-premise-under-any-context-empty
    (CTI2.⊑cast² {p = p} c′ rel .I.★⊑★) with p
argument-at-premise-under-any-context-empty
    (CTI2.⊑cast² {p = p} c′ rel .I.★⊑★) | ()
argument-at-premise-under-any-context-empty
    (CTI2.cast⊑² c rel .I.★⊑★) =
  source-seal-to-target-tag-empty rel

source-substitution-shape :
  subst (singleSub Caller.source-argument) source-body
    ≡ (ƛ Caller.source-argument) ↑ source-wrapper
source-substitution-shape = refl

target-substitution-shape :
  subst (singleSub Caller.target-argument) target-body
    ≡ ƛ Caller.target-argument
target-substitution-shape = refl

peeled-substituted-premise-empty :
  P.Wᵖ CTI2.∣ [] ⊢²
    ƛ Caller.source-argument ⊑ ƛ Caller.target-argument ∶
      p-premise-function
  → ⊥
peeled-substituted-premise-empty (CTI2.ƛ⊑ƛ² rel) =
  argument-at-premise-under-any-context-empty rel

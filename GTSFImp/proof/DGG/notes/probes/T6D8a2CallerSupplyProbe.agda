module T6D8a2CallerSupplyProbe where

-- File Charter:
--   * Validates the D8a2 boundary-indexed substitution premise at the direct
--     lambda/beta caller in SimPairedFunClosing.
--   * Embeds a rebase-entangled pair of closed tagged values into the actual
--     caller premises and tests lookup at a boundary-reachable node.
--   * Contains only checked positive witnesses and negative inversion proofs;
--     it is not imported by the live DGG development.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; ★; ＇_; `ℕ; ‵_; _⇒_)
open import Consistency using (Env∼; X∼★; _⊢_∼_; id; _!)
open import Imprecision using (★⊑★; ι⊑ι; ⇒⊑⇒)
open import CastTerms using
  (Term; Value; singleSub; `_ ; ƛ_; _·_; $; _⟨_⟩)
import CastTerms as CT
open import Primitives using (κℕ)
open import Reduction using (keep; pure-step; β; _—→[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.CatchupToMorePreciseDef using
  (boundary-source-reveal)
open import proof.DGG.Parked.ParkedWorldDef using
  (ParkedWorld; parked-initial; parked-both-bind; parked-right-bind)
open import T6D8a2RepairDraftProbe using
  ( BoundaryStackReachable
  ; TermSubstRelBoundary
  ; boundary-node
  ; reachable-boundary
  ; reachable-root
  )
import T6D8a2ClosedValueRebaseTransportProbe as P


source-env : Env∼ 1
source-env _ = X∼★

target-env : Env∼ 2
target-env _ = X∼★

source-X! : source-env ⊢ ＇ P.X ∼ ★
source-X! = id { μ = source-env } (＇ P.X) !

target-Y-old! : target-env ⊢ ＇ P.Y-old ∼ ★
target-Y-old! = id { μ = target-env } (＇ P.Y-old) !

source-argument : Term 1
source-argument = P.source-sealed ⟨ source-X! ⟩

target-argument : Term 2
target-argument = P.target-old-sealed ⟨ target-Y-old! ⟩

source-argument-value : Value source-argument
source-argument-value = P.source-sealed-value CT.《 CT.inj 》

target-argument-value : Value target-argument
target-argument-value = P.target-old-sealed-value CT.《 CT.inj 》

argument-at-W :
  P.W CTI2.∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★
argument-at-W =
  CTI2.cast⊑cast² source-X! target-Y-old! P.entangled-at-W ★⊑★

parked-W : ParkedWorld P.W
parked-W = parked-right-bind (parked-both-bind parked-initial)

source-body : Term 1
source-body = $ (κℕ 1)

target-body : Term 2
target-body = $ (κℕ 1)

source-function : Term 1
source-function = ƛ source-body

target-function : Term 2
target-function = ƛ target-body

source-function-value : Value source-function
source-function-value = CT.ƛ source-body

body-at-W :
  P.W CTI2.∣ CTI2.ctx-imp ★ ★ ★⊑★ ∷ [] ⊢²
    source-body ⊑ target-body ∶ ι⊑ι
body-at-W = CTI2.κ⊑κ² (κℕ 1) ι⊑ι

function-at-W :
  P.W CTI2.∣ [] ⊢² source-function ⊑ target-function ∶
    ⇒⊑⇒ ★⊑★ ι⊑ι
function-at-W = CTI2.ƛ⊑ƛ² body-at-W

application-at-W :
  P.W CTI2.∣ [] ⊢²
    source-function · source-argument ⊑
    target-function · target-argument ∶ ι⊑ι
application-at-W = CTI2.·⊑·² function-at-W argument-at-W

source-beta-step :
  source-function · source-argument —→[ keep ]
    source-body CT.[ source-argument ]
source-beta-step = pure-step (β source-argument-value)

root-source-ctx : CTI2.CtxImp P.W
root-source-ctx = CTI2.ctx-imp ★ ★ ★⊑★ ∷ []

premise-source-ctx : CTI2.CtxImp P.Wᵖ
premise-source-ctx = CTI2.ctx-imp ★ ★ ★⊑★ ∷ []

root-node : T6D8a2RepairDraftProbe.BoundaryNode
root-node = boundary-node P.W root-source-ctx []

premise-node : T6D8a2RepairDraftProbe.BoundaryNode
premise-node = boundary-node P.Wᵖ premise-source-ctx []

premise-reachable : BoundaryStackReachable root-node premise-node
premise-reachable =
  reachable-boundary reachable-root
    (boundary-source-reveal P.mono-forward
      (CTI2.tag-rebase-varᴸ P.forward-rebase))
    (CTI2.same-∷ CTI2.same-[])
    CTI2.same-[]

base-to-target-variable-empty : ∀ {W′ : CTI2.World 1 2 2}
  → (‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ (＇ P.Y-old)
  → ⊥
base-to-target-variable-empty ()

constant-to-target-tag-empty : ∀ {W′ : CTI2.World 1 2 2}
    {p : (‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ ★}
  → W′ CTI2.∣ [] ⊢² P.source-value ⊑ target-argument ∶ p
  → ⊥
constant-to-target-tag-empty {W′ = W′}
    (CTI2.⊑cast² {p = p} c′ rel q) =
  base-to-target-variable-empty {W′ = W′} p

source-seal-to-target-tag-empty :
  ∀ {p : (＇ P.X) CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ ★}
  → P.Wᵖ CTI2.∣ [] ⊢² P.source-sealed ⊑ target-argument ∶ p
  → ⊥
source-seal-to-target-tag-empty
    (CTI2.⊑cast² {p = p} c′ rel q) =
  P.pivot-old-at-Wᵖ-empty p
source-seal-to-target-tag-empty
    (CTI2.conceal⊑² ok mono rebase CTI2.same-[] c⊢ rel q) =
  constant-to-target-tag-empty rel

argument-at-Wᵖ-empty :
  P.Wᵖ CTI2.∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★
  → ⊥
argument-at-Wᵖ-empty
    (CTI2.cast⊑cast² {p = p} c c′ rel .★⊑★) =
  P.pivot-old-at-Wᵖ-empty p
argument-at-Wᵖ-empty
    (CTI2.⊑cast² {p = p} c′ rel .★⊑★) with p
argument-at-Wᵖ-empty
    (CTI2.⊑cast² {p = p} c′ rel .★⊑★) | ()
argument-at-Wᵖ-empty
    (CTI2.cast⊑² c rel .★⊑★) =
  source-seal-to-target-tag-empty rel

caller-boundary-environment-empty :
  TermSubstRelBoundary root-node
    (singleSub source-argument) (singleSub target-argument)
  → ⊥
caller-boundary-environment-empty env =
  argument-at-Wᵖ-empty
    (T6D8a2RepairDraftProbe.TermSubstRelBoundary.lookup env
      premise-reachable CTI2.Zʷ)

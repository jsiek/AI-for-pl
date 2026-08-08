module QHuntScratch where

-- Root-level scratch for the rep-★ ExtraCastRight² reachability hunt.
-- It imports the source reachability catalog read-only, runs selected
-- compiled right-side traces through a syntactic bad-projection scanner, and
-- links the exact abstract rep-★ mismatch refutation.

open import Data.Bool using (Bool; false; true; _∨_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; id; _↦_; ∀ᶜ_; _!; ？_; inst_; gen_;
   bot-elim; bot-intro)
open import CastTerms using
  (Term; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_;
   _↓_; blame)
open import Reduction using
  (_—↠[_]_; ↠-refl; ↠-step; keep; []; _∷_)
import Eval
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS
import proof.DGG.ExtraCastRight2 as ECR
import ProjectionMismatchStarRepScratch as PMS

------------------------------------------------------------------------
-- A trace scanner for the bad projected-name signature
------------------------------------------------------------------------

isVarTy : ∀ {Δ} → Ty Δ → Bool
isVarTy (＇ X) = true
isVarTy (‵ ι) = false
isVarTy ★ = false
isVarTy (A ⇒ B) = false
isVarTy (`∀ A) = false

badTopTagFor : ∀ {Δ} → Term Δ → Ty Δ → Bool
badTopTagFor (M ⟨ _! {G = G} c ⟩) H
    with isVarTy H | G ≟Ty H
badTopTagFor (M ⟨ _! {G = G} c ⟩) H | true | no G≢H = true
badTopTagFor (M ⟨ _! {G = G} c ⟩) H | true | yes G≡H = false
badTopTagFor (M ⟨ _! {G = G} c ⟩) H | false | eq? = false
badTopTagFor (M ⟨ c ⟩) H = false
badTopTagFor (` x) H = false
badTopTagFor (ƛ M) H = false
badTopTagFor (L · M) H = false
badTopTagFor (Λ M) H = false
badTopTagFor (M ⦂∀ B [ A ]) H = false
badTopTagFor ($ κ) H = false
badTopTagFor (L ⊕[ op ] M) H = false
badTopTagFor (M ↑ c) H = false
badTopTagFor (M ↓ c) H = false
badTopTagFor blame H = false

badProjectionCast : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → Term Δ
  → μ ⊢ A ∼ B
  → Bool
badProjectionCast {A = ★} M (id a) = false
badProjectionCast {A = ★} M (？_ {G = H} c) = badTopTagFor M H
badProjectionCast {A = ★} M ((gen c) A≢★) = false
badProjectionCast {A = ＇ X} M c = false
badProjectionCast {A = ‵ ι} M c = false
badProjectionCast {A = A ⇒ B} M c = false
badProjectionCast {A = `∀ A} M c = false

hasBadNameProjection : ∀ {Δ} → Term Δ → Bool
hasBadNameProjection (` x) = false
hasBadNameProjection (ƛ M) = hasBadNameProjection M
hasBadNameProjection (L · M) =
  hasBadNameProjection L ∨ hasBadNameProjection M
hasBadNameProjection (Λ M) = hasBadNameProjection M
hasBadNameProjection (M ⦂∀ B [ A ]) = hasBadNameProjection M
hasBadNameProjection ($ κ) = false
hasBadNameProjection (L ⊕[ op ] M) =
  hasBadNameProjection L ∨ hasBadNameProjection M
hasBadNameProjection (M ⟨ c ⟩) =
  badProjectionCast M c ∨ hasBadNameProjection M
hasBadNameProjection (M ↑ c) = hasBadNameProjection M
hasBadNameProjection (M ↓ c) = hasBadNameProjection M
hasBadNameProjection blame = false

traceHasBadNameProjection : ∀ {Δ Δ′ χs} {M : Term Δ} {N : Term Δ′}
  → M —↠[ χs ] N
  → Bool
traceHasBadNameProjection {M = M} ↠-refl =
  hasBadNameProjection M
traceHasBadNameProjection {M = M} (↠-step step rest) =
  hasBadNameProjection M ∨ traceHasBadNameProjection rest

rightTraceHasBadNameProjection : RS.Entry → Bool
rightTraceHasBadNameProjection e
    with Eval.eval (RS.Entry.gasᴿ e) (RS.Entry.more-imprecise e)
rightTraceHasBadNameProjection e | just out =
  traceHasBadNameProjection (Eval.outcomeTrace out)
rightTraceHasBadNameProjection e | nothing =
  hasBadNameProjection (RS.Entry.more-imprecise e)

------------------------------------------------------------------------
-- Selected source-catalog stress gates
------------------------------------------------------------------------

skew-star-inst-no-bad-projection :
  rightTraceHasBadNameProjection (RC.compiled RC.skew-star-inst) ≡ false
skew-star-inst-no-bad-projection = refl

tag-boundary-star-inst-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.tag-boundary-star-inst) ≡ false
tag-boundary-star-inst-no-bad-projection = refl

adversarial-source-star-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.adversarial-source-star) ≡ false
adversarial-source-star-no-bad-projection = refl

left-only-inst-path-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.left-only-inst-path) ≡ false
left-only-inst-path-no-bad-projection = refl

left-only-gen-path-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.left-only-gen-path) ≡ false
left-only-gen-path-no-bad-projection = refl

higher-order-shared-arg-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.higher-order-shared-arg) ≡ false
higher-order-shared-arg-no-bad-projection = refl

adversarial-source-chain-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.adversarial-source-chain) ≡ false
adversarial-source-chain-no-bad-projection = refl

blame-dyn-bool-no-bad-projection :
  rightTraceHasBadNameProjection
    (RC.compiled RC.blame-dyn-bool) ≡ false
blame-dyn-bool-no-bad-projection = refl

skew-star-inst-screen-clean :
  RS.crossing-suspect (RC.compiled RC.skew-star-inst) ≡ RS.clean
skew-star-inst-screen-clean = RC.skew-star-inst-screens-clean

tag-boundary-star-inst-screen-clean :
  RS.crossing-suspect (RC.compiled RC.tag-boundary-star-inst) ≡ RS.clean
tag-boundary-star-inst-screen-clean =
  RC.tag-boundary-star-inst-screens-clean

adversarial-source-star-screen-clean :
  RS.crossing-suspect (RC.compiled RC.adversarial-source-star) ≡ RS.clean
adversarial-source-star-screen-clean =
  RC.adversarial-source-star-screens-clean

left-only-inst-path-screen-clean :
  RS.crossing-suspect (RC.compiled RC.left-only-inst-path) ≡ RS.clean
left-only-inst-path-screen-clean = RC.left-only-inst-path-screens-clean

left-only-gen-path-screen-clean :
  RS.crossing-suspect (RC.compiled RC.left-only-gen-path) ≡ RS.clean
left-only-gen-path-screen-clean = RC.left-only-gen-path-screens-clean

higher-order-shared-arg-screen-clean :
  RS.crossing-suspect (RC.compiled RC.higher-order-shared-arg) ≡ RS.clean
higher-order-shared-arg-screen-clean =
  RC.higher-order-shared-arg-screens-clean

adversarial-source-chain-screen-clean :
  RS.crossing-suspect (RC.compiled RC.adversarial-source-chain) ≡ RS.clean
adversarial-source-chain-screen-clean =
  RC.adversarial-source-chain-screens-clean

------------------------------------------------------------------------
-- Exact abstract rep-★ mismatch is still a theorem-shape refutation
------------------------------------------------------------------------

abstract-rep★-mismatch-blames :
  PMS.mismatch-term —↠[ keep ∷ [] ] blame
abstract-rep★-mismatch-blames = PMS.mismatch-steps-to-blame

abstract-rep★-refutes-extra-cast-right :
  ECR.ExtraCastRight² → ⊥
abstract-rep★-refutes-extra-cast-right =
  PMS.extra-cast-right²-contradiction

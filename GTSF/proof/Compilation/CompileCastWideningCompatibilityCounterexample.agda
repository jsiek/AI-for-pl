module
  proof.Compilation.CompileCastWideningCompatibilityCounterexample
  where

-- File Charter:
--   * Gives a strict counterexample to reduction-closed widening
--     compatibility for canonical cast plans produced by compilation.
--   * Isolates the active source instantiation versus inert target tag
--     obstruction at the compiler/QTI boundary.
--   * Depends only on cast-plan compilation, quotient compatibility, and the
--     impossibility of relating `★` to a function type.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; z<s)
open import Data.Product using (_,_)

open import Types
import Coercions as C
open import Compile using
  ( CastPlan
  ; consistency-cast-plan
  ; lower⊑target
  ; up
  )
open import ForallPermutation using
  (quotientᵖ; ≈∀-refl; ≈∀-arrow-left)
import Imprecision as Imp
open import Imprecision using (tag_⇛_)
import ImprecisionWf as IWF
open import ImprecisionComposition using (⌊_⌋)
open import QuotientImprecisionCompatibility using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  ; compatible-through-non-function-representativesᴿ
  )
open import proof.Core.Properties.ImprecisionProperties using
  (⊑-star-arrow-⊥)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-forgetᵢ)


source-plan : CastPlan zero [] (`∀ (＇ zero ⇒ ＇ zero)) ★
source-plan =
  consistency-cast-plan zero
    ( `∀ (＇ zero ⇒ ＇ zero)
    , Imp.∀ⁱ
        ((Imp.idˣ (here refl)) Imp.↦ (Imp.idˣ (here refl)))
    , Imp.ν Imp.nonvar-fun refl
        (Imp.tag (Imp.tagˣ (here refl)) ⇛ (Imp.tagˣ (here refl)))
    )


target-plan : CastPlan zero [] (★ ⇒ ★) ★
target-plan =
  consistency-cast-plan zero
    ( ★ ⇒ ★
    , Imp.id★ Imp.↦ Imp.id★
    , Imp.tag Imp.id★ ⇛ Imp.id★
    )


source-up-shape :
  up source-plan ≡
    C.inst (★ ⇒ ★) (C.seal ★ zero C.↦ C.unseal zero ★)
      C.︔ ((★ ⇒ ★) C.!)
source-up-shape = refl


target-up-shape :
  up target-plan ≡ (★ ⇒ ★) C.!
target-up-shape = refl


private
  paired-widening-compatibility-impossible :
    ∀ {A A₁ A₂ p q source-shape target-shape} →
    ReductionClosedPairedWideningCompatible
      [] zero zero
      (C.inst (★ ⇒ ★) (C.seal ★ zero C.↦ C.unseal zero ★)
        C.︔ ((★ ⇒ ★) C.!))
      ((★ ⇒ ★) C.!)
      {A} {A₁ ⇒ A₂} {★} {★}
      p q source-shape target-shape →
    ⊥
  paired-widening-compatibility-impossible
      (compatible-target-activeᴿ () target-active)
  paired-widening-compatibility-impossible
      (compatible-target-inert-bridgeᴿ bridge-evidence)
      with bridge-evidence ((★ ⇒ ★) C.!)
  paired-widening-compatibility-impossible
      (compatible-target-inert-bridgeᴿ bridge-evidence)
      | bridge , source-triangle , target-triangle =
    ⊑-star-arrow-⊥ (⊑-forgetᵢ bridge)


canonical-compiled-widening-compatibility-impossible :
  ReductionClosedQuotientWideningCompatible
    [] zero zero
    (up source-plan) (up target-plan)
    (quotientᵖ ≈∀-refl
      (IWF.ν Imp.nonvar-fun refl
        ((IWF.tagˣ (here refl) z<s) IWF.↦
         (IWF.tagˣ (here refl) z<s)))
      ≈∀-refl)
    IWF.id★
    ⌊ lower⊑target source-plan ⌋
    ⌊ lower⊑target target-plan ⌋ →
  ⊥
canonical-compiled-widening-compatibility-impossible
    (compatible-through-non-function-representativesᴿ
      {tgt = target-equivalence}
      non-function source-shape target-shape compatible)
    with ≈∀-arrow-left target-equivalence
canonical-compiled-widening-compatibility-impossible
    (compatible-through-non-function-representativesᴿ
      {tgt = target-equivalence}
      non-function source-shape target-shape compatible)
    | A₁ , A₂ , refl =
  paired-widening-compatibility-impossible compatible

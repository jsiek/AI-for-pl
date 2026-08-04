module
  proof.Compilation.CompileCanonicalDownCompatibilityExperiment
  where

-- File Charter:
--   * Tests whether paired canonical compiler cast plans always provide the
--     narrowing-elimination compatibility required by live paired-down QTI.
--   * Gives a fixed-pair counterexample for every quotient index.
--   * Shows that contravariant function downcasts expose an impossible
--     active-source/inert-target widening pair in their domains.

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
  ; down
  ; lower
  ; lower⊑source
  ; up
  )
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; ≈∀-arrow-left)
import Imprecision as Imp
import ImprecisionWf as IWF
open import ImprecisionComposition using (⌊_⌋)
open import QuotientImprecisionCompatibility using
  ( QuotientNarrowingEliminationCompatible
  ; NonPairedFunctionCoercions
  ; ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  ; compatible-through-non-function-representativesᴿ
  ; function-elimination
  ; non-function-elimination
  ; source-non-function
  ; target-non-function
  )
open import proof.Compilation.CompileCastWideningCompatibilityCounterexample
  using
  ( source-consistency
  ; source-plan
  ; source-up-shape
  ; target-consistency
  ; target-plan
  ; target-up-shape
  )


private
  _⇒ℕ-consistent :
    ∀ {Δ A B} →
    Δ Imp.⊢ A ~ B →
    Δ Imp.⊢ (A ⇒ ‵ `ℕ) ~ (B ⇒ ‵ `ℕ)
  _⇒ℕ-consistent (D , D⊑A , D⊑B) =
    D ⇒ ‵ `ℕ
    , (D⊑A Imp.↦ Imp.idι)
    , (D⊑B Imp.↦ Imp.idι)

  consistency-sym :
    ∀ {Δ A B} →
    Δ Imp.⊢ A ~ B →
    Δ Imp.⊢ B ~ A
  consistency-sym (D , D⊑A , D⊑B) =
    D , D⊑B , D⊑A


outer-source-consistency :
  zero Imp.⊢
    (★ ⇒ ‵ `ℕ) ~ ((`∀ (＇ zero ⇒ ＇ zero)) ⇒ ‵ `ℕ)
outer-source-consistency =
  consistency-sym (source-consistency ⇒ℕ-consistent)


outer-target-consistency :
  zero Imp.⊢
    (★ ⇒ ‵ `ℕ) ~ ((★ ⇒ ★) ⇒ ‵ `ℕ)
outer-target-consistency =
  consistency-sym (target-consistency ⇒ℕ-consistent)


outer-source-plan :
  CastPlan zero []
    (★ ⇒ ‵ `ℕ) ((`∀ (＇ zero ⇒ ＇ zero)) ⇒ ‵ `ℕ)
outer-source-plan =
  consistency-cast-plan zero outer-source-consistency


outer-target-plan :
  CastPlan zero []
    (★ ⇒ ‵ `ℕ) ((★ ⇒ ★) ⇒ ‵ `ℕ)
outer-target-plan =
  consistency-cast-plan zero outer-target-consistency


input-imprecision :
  [] IWF.∣ zero ⊢
    (★ ⇒ ‵ `ℕ) ⊑ (★ ⇒ ‵ `ℕ)
    ⊣ zero
input-imprecision =
  IWF.id★ IWF.↦ IWF.idι


result-domain-imprecision :
  [] IWF.∣ zero ⊢
    `∀ (＇ zero ⇒ ＇ zero) ⊑ ★ ⇒ ★
    ⊣ zero
result-domain-imprecision =
  IWF.ν Imp.nonvar-fun refl
    ((IWF.tagˣ (here refl) z<s) IWF.↦
     (IWF.tagˣ (here refl) z<s))


result-imprecision :
  [] IWF.∣ zero ⊢
    ((`∀ (＇ zero ⇒ ＇ zero)) ⇒ ‵ `ℕ)
      ⊑ ((★ ⇒ ★) ⇒ ‵ `ℕ)
    ⊣ zero
result-imprecision =
  result-domain-imprecision IWF.↦ IWF.idι


outer-source-down-shape :
  down outer-source-plan ≡
    up source-plan C.↦ C.id (‵ `ℕ)
outer-source-down-shape = refl


outer-target-down-shape :
  down outer-target-plan ≡
    up target-plan C.↦ C.id (‵ `ℕ)
outer-target-down-shape = refl


private
  star-function-imprecision-impossible :
    ∀ {Φ Δᴸ Δᴿ A B} →
    Φ IWF.∣ Δᴸ ⊢ ★ ⊑ A ⇒ B ⊣ Δᴿ →
    ⊥
  star-function-imprecision-impossible ()

  paired-function-coercions-are-functions :
    ∀ {a b a′ b′} →
    NonPairedFunctionCoercions
      (a C.↦ b) (a′ C.↦ b′) →
    ⊥
  paired-function-coercions-are-functions
      (source-non-function ())
  paired-function-coercions-are-functions
      (target-non-function ())

  exposed-domain-widening-impossible :
    ∀ {A A₁ A₂ p q source-shape target-shape} →
    ReductionClosedPairedWideningCompatible
      [] zero zero
      (C.inst (★ ⇒ ★)
        (C.seal ★ zero C.↦ C.unseal zero ★)
        C.︔ ((★ ⇒ ★) C.!))
      ((★ ⇒ ★) C.!)
      {A} {A₁ ⇒ A₂} {★} {★}
      p q source-shape target-shape →
    ⊥
  exposed-domain-widening-impossible
      (compatible-target-activeᴿ () target-active)
  exposed-domain-widening-impossible
      (compatible-target-inert-bridgeᴿ bridge-evidence)
      with bridge-evidence ((★ ⇒ ★) C.!)
  exposed-domain-widening-impossible
      (compatible-target-inert-bridgeᴿ bridge-evidence)
      | bridge , source-triangle , target-triangle =
    star-function-imprecision-impossible bridge

  exposed-domain-quotient-widening-impossible :
    ∀ {D q source-shape target-shape} →
    ReductionClosedQuotientWideningCompatible
      [] zero zero
      (C.inst (★ ⇒ ★)
        (C.seal ★ zero C.↦ C.unseal zero ★)
        C.︔ ((★ ⇒ ★) C.!))
      ((★ ⇒ ★) C.!)
      {D} {★ ⇒ ★} {★} {★}
      q IWF.id★ source-shape target-shape →
    ⊥
  exposed-domain-quotient-widening-impossible
      (compatible-through-non-function-representativesᴿ
        {tgt = target-equivalence}
        non-function source-shape target-shape compatible)
      with ≈∀-arrow-left target-equivalence
  exposed-domain-quotient-widening-impossible
      (compatible-through-non-function-representativesᴿ
        {tgt = target-equivalence}
        non-function source-shape target-shape compatible)
      | A₁ , A₂ , refl =
    exposed-domain-widening-impossible compatible


canonical-plan-down-compatibility-impossible :
  ∀ {q :
      [] ∣ zero ⊢
        lower outer-source-plan ⊑ᵖ lower outer-target-plan
        ⊣ zero} →
  QuotientNarrowingEliminationCompatible
    [] zero zero
    (down outer-source-plan) (down outer-target-plan)
    input-imprecision q
    ⌊ lower⊑source outer-source-plan ⌋
    ⌊ lower⊑source outer-target-plan ⌋ →
  ⊥
canonical-plan-down-compatibility-impossible
    (non-function-elimination non-functions)
    rewrite outer-source-down-shape | outer-target-down-shape =
  paired-function-coercions-are-functions non-functions
canonical-plan-down-compatibility-impossible
    (function-elimination components domain-compatible
      codomain-compatible)
    rewrite source-up-shape | target-up-shape =
  exposed-domain-quotient-widening-impossible domain-compatible

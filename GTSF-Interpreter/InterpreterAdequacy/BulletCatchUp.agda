module InterpreterAdequacy.BulletCatchUp where

-- File Charter:
--   * Defines finite catch-up across the runtime bullet introduced by the
--     small-step `ν` rule.
--   * Proves that every catch-up is an all-`keep` small-step trace whose
--     endpoint is again in the direct-interpreter source fragment.
--   * Contains no completeness driver or interpreter execution theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (subst)

open import Coercions using (Coercion)
import Coercions as C
open import SmallStepInterface.InterpreterTermShape using
  ( InterpreterTerm
  ; application-term
  ; closure-term
  ; coercion-application-term
  ; constant-term
  ; instantiation-term
  ; primitive-term
  ; type-abstraction-term
  ; variable-term
  )
open import NuReduction using
  ( StoreChanges
  ; keep
  ; pure-step
  ; β-gen•
  ; β-Λ•
  ; β-∀•
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
import NuTerms as N
import proof.Core.Properties.ReductionProperties as Reduction
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import Types using (extᵗ; singleRenameᵗ)

interpreter-term-type-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ ρ M)
interpreter-term-type-rename ρ (variable-term x) =
  variable-term x
interpreter-term-type-rename ρ (closure-term M-ok) =
  closure-term (interpreter-term-type-rename ρ M-ok)
interpreter-term-type-rename ρ (application-term L-ok M-ok) =
  application-term
    (interpreter-term-type-rename ρ L-ok)
    (interpreter-term-type-rename ρ M-ok)
interpreter-term-type-rename ρ
    (type-abstraction-term vV V-ok) =
  type-abstraction-term
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
    (interpreter-term-type-rename (extᵗ ρ) V-ok)
interpreter-term-type-rename ρ (instantiation-term L-ok) =
  instantiation-term (interpreter-term-type-rename ρ L-ok)
interpreter-term-type-rename ρ (constant-term κ) =
  constant-term κ
interpreter-term-type-rename ρ (primitive-term op L-ok M-ok) =
  primitive-term op
    (interpreter-term-type-rename ρ L-ok)
    (interpreter-term-type-rename ρ M-ok)
interpreter-term-type-rename ρ (coercion-application-term M-ok) =
  coercion-application-term (interpreter-term-type-rename ρ M-ok)

interpreter-term-type-name-substitute :
  ∀ X {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ (singleRenameᵗ X) M)
interpreter-term-type-name-substitute X =
  interpreter-term-type-rename (singleRenameᵗ X)

-- A well-typed runtime bullet can expose a type abstraction, a forall proxy,
-- or a generalized value.  The forall case may expose another bullet.
data BulletCatchUp : N.Term → N.Term → Set where
  bullet-type-abstraction :
    ∀ {V} →
    (vV : N.Value V) →
    InterpreterTerm V →
    BulletCatchUp ((N.Λ V) N.•) (V N.[ zero ]ᵀ)

  bullet-forall-proxy :
    ∀ {V R c} →
    (vV : N.Value V) →
    BulletCatchUp (V N.•) R →
    BulletCatchUp
      ((V N.⟨ C.`∀ c ⟩) N.•)
      (R N.⟨ c C.[ zero ]ᶜ ⟩)

  bullet-generalized :
    ∀ {V A c} →
    (vV : N.Value V) →
    InterpreterTerm V →
    BulletCatchUp
      ((V N.⟨ C.gen A c ⟩) N.•)
      (V N.⟨ c C.[ zero ]ᶜ ⟩)

bulletChanges : ∀ {M R} → BulletCatchUp M R → StoreChanges
bulletChanges (bullet-type-abstraction vV V-ok) = keep ∷ []
bulletChanges (bullet-forall-proxy vV catch-up) =
  keep ∷ bulletChanges catch-up
bulletChanges (bullet-generalized vV V-ok) = keep ∷ []

data AllKeep : StoreChanges → Set where
  all-keep-empty : AllKeep []
  all-keep-cons :
    ∀ {χs} →
    AllKeep χs →
    AllKeep (keep ∷ χs)

bulletChanges-all-keep :
  ∀ {M R} →
  (catch-up : BulletCatchUp M R) →
  AllKeep (bulletChanges catch-up)
bulletChanges-all-keep (bullet-type-abstraction vV V-ok) =
  all-keep-cons all-keep-empty
bulletChanges-all-keep (bullet-forall-proxy vV catch-up) =
  all-keep-cons (bulletChanges-all-keep catch-up)
bulletChanges-all-keep (bullet-generalized vV V-ok) =
  all-keep-cons all-keep-empty

applyCoercions-all-keep :
  ∀ {χs} →
  AllKeep χs →
  (c : Coercion) →
  Reduction.applyCoercions χs c ≡ c
applyCoercions-all-keep all-keep-empty c = refl
applyCoercions-all-keep (all-keep-cons keeps) c =
  applyCoercions-all-keep keeps c

bullet-catch-up-trace :
  ∀ {M R} →
  (catch-up : BulletCatchUp M R) →
  M —↠[ bulletChanges catch-up ] R
bullet-catch-up-trace (bullet-type-abstraction vV V-ok) =
  ↠-step (pure-step (β-Λ• vV)) ↠-refl
bullet-catch-up-trace
    (bullet-forall-proxy {V = V} {R = R} {c = c} vV catch-up) =
  ↠-step (pure-step (β-∀• vV))
    (subst
      (λ d →
        (V N.•) N.⟨ c C.[ zero ]ᶜ ⟩
          —↠[ bulletChanges catch-up ] R N.⟨ d ⟩)
      (applyCoercions-all-keep
        (bulletChanges-all-keep catch-up) (c C.[ zero ]ᶜ))
      (Reduction.cast-↠ (bullet-catch-up-trace catch-up)))
bullet-catch-up-trace (bullet-generalized vV V-ok) =
  ↠-step (pure-step (β-gen• vV)) ↠-refl

bullet-catch-up-interpreter-term :
  ∀ {M R} →
  BulletCatchUp M R →
  InterpreterTerm R
bullet-catch-up-interpreter-term
    (bullet-type-abstraction vV V-ok) =
  interpreter-term-type-name-substitute zero V-ok
bullet-catch-up-interpreter-term
    (bullet-forall-proxy vV catch-up) =
  coercion-application-term
    (bullet-catch-up-interpreter-term catch-up)
bullet-catch-up-interpreter-term (bullet-generalized vV V-ok) =
  coercion-application-term V-ok

-- Catch-up remains valid under the conversion surrounding the runtime bullet
-- produced by the `ν` rule.
cast-bullet-catch-up-trace :
  ∀ {M R c} →
  (catch-up : BulletCatchUp M R) →
  (M N.⟨ c ⟩)
    —↠[ bulletChanges catch-up ]
    (R N.⟨ c ⟩)
cast-bullet-catch-up-trace {M} {R} {c} catch-up =
  subst
    (λ d →
      (M N.⟨ c ⟩)
        —↠[ bulletChanges catch-up ]
        (R N.⟨ d ⟩))
    (applyCoercions-all-keep
      (bulletChanges-all-keep catch-up) c)
    (Reduction.cast-↠ (bullet-catch-up-trace catch-up))

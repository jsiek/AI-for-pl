module InterpreterAdequacy.proof.TypeAbstractionBetaReification where

-- File Charter:
--   * Identifies the `β-Λ•` target of a reified semantic type abstraction.
--   * Makes the freshly allocated seal index explicit at de Bruijn index zero.
--   * Is syntax-only and independent of interpreter recursion and worlds.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import InterpreterAdequacy.TraceAgreement using
  (environmentSubstitution)
open import InterpreterAdequacy.proof.SyntaxReification using
  (reified-term; substˣᵐ-cong)
import NuTerms as N
import Coercions as C
open import Coercions using (Coercion; renameᶜ)
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-compose; renameᶜ-cong)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-compose; renameᵗᵐ-cong)
open import proof.Substitution.Term.TermSubstitutionSyntax using
  (substˣᵐ-open)
open import Types using (Renameᵗ; extᵗ; singleRenameᵗ)

extend-after-opening : Renameᵗ → Renameᵗ
extend-after-opening τ zero = zero
extend-after-opening τ (suc X) = τ X

extend-after-insertion :
  ∀ τ X →
  extend-after-opening (λ Y → suc (τ Y)) X ≡ extᵗ τ X
extend-after-insertion τ zero = refl
extend-after-insertion τ (suc X) = refl

open-extended-renaming :
  ∀ τ M →
  (N.renameᵗᵐ (extᵗ τ) M N.[ zero ]ᵀ) ≡
    N.renameᵗᵐ (extend-after-opening τ) M
open-extended-renaming τ M =
  trans
    (renameᵗᵐ-compose (extᵗ τ) (singleRenameᵗ zero) M)
    (renameᵗᵐ-cong (λ { zero → refl ; (suc X) → refl }) M)

open-extended-coercion :
  ∀ τ c →
  (renameᶜ (extᵗ τ) c C.[ zero ]ᶜ) ≡
    renameᶜ (extend-after-opening τ) c
open-extended-coercion τ c =
  trans
    (renameᶜ-compose (extᵗ τ) (singleRenameᵗ zero) c)
    (renameᶜ-cong (λ { zero → refl ; (suc X) → refl }) c)

type-beta-reification :
  ∀ (τ : Renameᵗ) (vs : List N.Term) M →
  (N.substˣᵐ
      (N.↑ᵗᵐ (environmentSubstitution vs))
      (N.renameᵗᵐ (extᵗ τ) M)
    N.[ zero ]ᵀ) ≡
  reified-term (extend-after-opening τ) vs M
type-beta-reification τ vs M =
  trans
    (sym
      (substˣᵐ-open (environmentSubstitution vs)
        (N.renameᵗᵐ (extᵗ τ) M) zero))
    (cong (N.substˣᵐ (environmentSubstitution vs))
      (open-extended-renaming τ M))

module proof.DGG.notes.probes.LambdaFreshWorldInvariantProbe where

-- File Charter:
--   * Checks the binder alignment of the invariant-preserving replacement
--     for the old post-Λ target-store rewrite.
--   * Records why the former generic body-prefix transport cannot target
--     this world: the source binder and the newest target binder are distinct.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (★; ＇_; ‵_; `ℕ; _⇒_)
open import TyStore using (store-empty; store-lift; store-bind)
open import Consistency using (empty; keep; skip)
import Imprecision as I
import proof.DGG.CtxImp as CTX


empty-imp-env : I.ImpEnv 0
empty-imp-env ()


fresh-world =
  CTX.liftWorldLeft
    (CTX.rightOnlyWorld
      (CTX.rightOnlyWorld CTX.emptyʷ ★ (inj₁ refl))
      (＇ Fin.zero)
      (inj₂ (Fin.suc Fin.zero , refl , (λ Xᴸ ()))))


fresh-binders-are-not-imprecise :
    (＇ Fin.zero) CTX.⊑ᵂ⟨
      fresh-world
    ⟩ (＇ Fin.zero)
  → ⊥
fresh-binders-are-not-imprecise ()


fresh-nonvariable-bodies-are-not-imprecise :
    ((‵ `ℕ) ⇒ ＇ Fin.zero) CTX.⊑ᵂ⟨ fresh-world ⟩
      ((‵ `ℕ) ⇒ ＇ Fin.zero)
  → ⊥
fresh-nonvariable-bodies-are-not-imprecise
    (I.⇒⊑⇒ domain ())


split-alias-mid-invariants-impossible :
    CTX.WorldInvariants
      (skip (skip (keep empty)))
      (skip (keep (keep empty)))
      (I.instᵐ (I.instᵐ (I.instᵐ empty-imp-env)))
      (store-lift store-empty)
      (store-bind (store-bind store-empty ★) (＇ Fin.zero))
  → ⊥
split-alias-mid-invariants-impossible inv
    with CTX.unmatchedTargetsDynamic inv Fin.zero no-source
  where
  no-source : ∀ Xᴸ
    → _
  no-source Fin.zero ()
split-alias-mid-invariants-impossible inv | inj₁ ()
split-alias-mid-invariants-impossible inv | inj₂ (Fin.zero , () , head)
split-alias-mid-invariants-impossible inv
    | inj₂ (Fin.suc Fin.zero , refl , head) =
  head Fin.zero refl

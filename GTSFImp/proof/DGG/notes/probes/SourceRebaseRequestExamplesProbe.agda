{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.SourceRebaseRequestExamplesProbe where

-- File Charter:
--   * Exercises the canonical source-rebase request with identity,
--     source-only, and paired operational examples.
--   * Keeps the former producer probe's concrete fixture coverage while the
--     reusable plan and request surfaces live under proof.DGG.

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (★; ‵_; `ℕ)
open import TyStore using (store-empty)
import Imprecision as I
open import CastTerms using (Ctx; ⟨_,_,_⟩; _,ˢ_)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.SourceRebasePlan
open import proof.DGG.SourceRebaseRequest


empty-context : Ctx
empty-context = ⟨ zero , store-empty , [] ⟩

identity-request : SourceRebaseRequest emptyᶜ nothing nothing
identity-request = source-request-id

unmatched-source-world :
    (empty-context ,ˢ (‵ `ℕ)) ⊑ᶜ empty-context
unmatched-source-world = bindLeftᶜ emptyᶜ (‵ `ℕ)

unmatched-source-request :
    SourceRebaseRequest unmatched-source-world (just Fin.zero) nothing
unmatched-source-request =
  source-request-only refl (λ ()) I.ι⊑★

separated-pivots-world :
    (empty-context ,ˢ (‵ `ℕ)) ⊑ᶜ (empty-context ,ˢ ★)
separated-pivots-world =
  bindRightᶜ unmatched-source-world ★ (inj₁ refl)

paired-move-plan :
    SourceRebasePlan separated-pivots-world Fin.zero Fin.zero
paired-move-plan =
  source-to-target refl refl (inj₁ refl) I.ι⊑★ (λ ())

paired-move-request :
    SourceRebaseRequest separated-pivots-world
      (just Fin.zero) (just Fin.zero)
paired-move-request =
  source-request-paired paired-move-plan I.ι⊑★


-- The live optional boundary supplies the three-way pivot classification.
-- Its unmatched and paired cases currently relate `resolveVar` results, not
-- the direct lookup entries required here.  A direct-entry premise must
-- therefore be produced at the boundary; it cannot be recovered without the
-- forbidden resolver or an invariant injection.  A moving paired boundary
-- additionally carries its constructor-form SourceRebasePlan.

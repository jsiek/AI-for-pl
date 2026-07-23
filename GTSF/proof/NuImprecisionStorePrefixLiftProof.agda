module proof.NuImprecisionStorePrefixLiftProof where

-- File Charter:
--   * Proves forward paired and source-only store lifting across arbitrary
--     relational-store prefixes, together with the target-only analogue.
--   * Recursively lifts each newly prefixed entry with the canonical type-
--     binder precision and well-formedness transports.
--   * Contains no term relation, postulate, hole, catch-all, or permissive
--     option.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)

open import NuTermImprecision using
  ( lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; lift-right-store-left
  ; lift-right-store-link
  ; lift-right-store-right
  ; lift-right-store-∷
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import QuotientedTermImprecision using
  (prefix-reflⁱ; prefix-∷ⁱ)
open import proof.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ; ⊑-target-lift-rightᵢ)
open import proof.NuImprecisionStorePrefixLiftDef using
  (LeftStorePrefixLiftᵀ; PairedStorePrefixLiftᵀ; RightStorePrefixLiftᵀ)
open import proof.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)
open import Types using (⇑ᵗ)


paired-store-prefix-lift-proofᵀ : PairedStorePrefixLiftᵀ
paired-store-prefix-lift-proofᵀ prefix-reflⁱ liftρ =
  _ , liftρ , prefix-reflⁱ
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) liftρ
    with paired-store-prefix-lift-proofᵀ prefix liftρ
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ⁺↑ ,
  lift-store-∷ lift⁺ , prefix-∷ⁱ prefix↑
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) liftρ
    with paired-store-prefix-lift-proofᵀ prefix liftρ
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-store-left lift⁺ , prefix-∷ⁱ prefix↑
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) liftρ
    with paired-store-prefix-lift-proofᵀ prefix liftρ
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-store-right lift⁺ , prefix-∷ⁱ prefix↑
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) liftρ
    with paired-store-prefix-lift-proofᵀ prefix liftρ
paired-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-link (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ⁺↑ ,
  lift-store-link lift⁺ , prefix-∷ⁱ prefix↑


left-store-prefix-lift-proofᵀ : LeftStorePrefixLiftᵀ
left-store-prefix-lift-proofᵀ prefix-reflⁱ liftρ =
  _ , liftρ , prefix-reflⁱ
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) liftρ
    with left-store-prefix-lift-proofᵀ prefix liftρ
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-matched (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ⁺↑ ,
  lift-left-store-∷ lift⁺ , prefix-∷ⁱ prefix↑
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) liftρ
    with left-store-prefix-lift-proofᵀ prefix liftρ
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-left-store-left lift⁺ , prefix-∷ⁱ prefix↑
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) liftρ
    with left-store-prefix-lift-proofᵀ prefix liftρ
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-right β B hB ∷ ρ⁺↑ ,
  lift-left-store-right lift⁺ , prefix-∷ⁱ prefix↑
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) liftρ
    with left-store-prefix-lift-proofᵀ prefix liftρ
left-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-link (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ⁺↑ ,
  lift-left-store-link lift⁺ , prefix-∷ⁱ prefix↑


right-store-prefix-lift-proofᵀ : RightStorePrefixLiftᵀ
right-store-prefix-lift-proofᵀ prefix-reflⁱ liftρ =
  _ , liftρ , prefix-reflⁱ
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) liftρ
    with right-store-prefix-lift-proofᵀ prefix liftρ
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-matched α A (suc β) (⇑ᵗ B)
    (⊑-target-lift-rightᵢ p) ∷ ρ⁺↑ ,
  lift-right-store-∷ lift⁺ , prefix-∷ⁱ prefix↑
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) liftρ
    with right-store-prefix-lift-proofᵀ prefix liftρ
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-left α A hA ∷ ρ⁺↑ ,
  lift-right-store-left lift⁺ , prefix-∷ⁱ prefix↑
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) liftρ
    with right-store-prefix-lift-proofᵀ prefix liftρ
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-right-store-right lift⁺ , prefix-∷ⁱ prefix↑
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) liftρ
    with right-store-prefix-lift-proofᵀ prefix liftρ
right-store-prefix-lift-proofᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-link α A (suc β) (⇑ᵗ B)
    (⊑-target-lift-rightᵢ p) ∷ ρ⁺↑ ,
  lift-right-store-link lift⁺ , prefix-∷ⁱ prefix↑

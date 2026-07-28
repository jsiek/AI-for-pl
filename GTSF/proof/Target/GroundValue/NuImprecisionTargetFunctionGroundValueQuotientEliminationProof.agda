module proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationProof where

-- File Charter:
--   * Proves quotient elimination for values at target type `★ ⇒ ★`.
--   * Handles the sole live `paired-downᵀ` boundary and both spine modes.
--   * Relies on the adjacent stable ground-permutation properties, not a
--     general quotient-to-ordinary principle.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
import NarrowWiden as NW
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
open import QuotientImprecisionCompatibility using
  (gradual↓; id-only↓)
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; paired-downᵀ
  ; ⊑cast⊒ᵀ
  )
open import TermTyping using (cast-tag-or-id)
import Types as T
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties using
  (imprecision-composition-shape-transport)
open import
  proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationDef
  using (TargetFunctionGroundValueQuotientEliminationᵀ)
open import
  proof.Target.GroundValue.NuImprecisionTargetGroundValueQuotientEliminationProperties
  using
  ( cast-shape-result-unique
  ; cast-value-inert
  ; function-ground-right-identity-composition
  ; inert-function-ground-narrowing-shape
  ; inert-function-ground-narrowing-source
  ; ⊑ᵖ-function-ground-right-composition
  ; ⊑ᵖ-ground-right
  )


target-function-ground-value-quotient-elimination-proofᵀ :
  TargetFunctionGroundValueQuotientEliminationᵀ
target-function-ground-value-quotient-elimination-proofᵀ
    {qD = qD} vV vV′
    (paired-downᵀ M⊑M′ mode d⊒ d-shape
      mode′ d′⊒ d′-shape square)
    with inert-function-ground-narrowing-source
      d′⊒ (cast-value-inert vV′)
target-function-ground-value-quotient-elimination-proofᵀ
    {qD = qD} vV vV′
    (paired-downᵀ M⊑M′ id-only↓ d⊒ d-shape
      id-only↓ d′⊒ d′-shape square)
    | refl =
  q ,
  ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
    (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d′⊒)
    (cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d⊒)
      M⊑M′ q d-shape source-composition)
    q d′-shape target-composition
  where
  q = ⊑ᵖ-ground-right T.★⇒★ qD

  final-shape =
    cast-shape-result-unique d′-shape
      (inert-function-ground-narrowing-shape
        d′⊒ (cast-value-inert vV′))

  source-composition =
    ⊑ᵖ-function-ground-right-composition qD square final-shape

  target-composition =
    imprecision-composition-shape-transport
      refl final-shape refl
      (function-ground-right-identity-composition q)
target-function-ground-value-quotient-elimination-proofᵀ
    {qD = qD} vV vV′
    (paired-downᵀ M⊑M′ id-only↓ d⊒ d-shape
      (gradual↓ mode′ seal★′) d′⊒ d′-shape square)
    | refl =
  q ,
  ⊑cast⊒ᵀ mode′ seal★′ d′⊒
    (cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d⊒)
      M⊑M′ q d-shape source-composition)
    q d′-shape target-composition
  where
  q = ⊑ᵖ-ground-right T.★⇒★ qD

  final-shape =
    cast-shape-result-unique d′-shape
      (inert-function-ground-narrowing-shape
        d′⊒ (cast-value-inert vV′))

  source-composition =
    ⊑ᵖ-function-ground-right-composition qD square final-shape

  target-composition =
    imprecision-composition-shape-transport
      refl final-shape refl
      (function-ground-right-identity-composition q)
target-function-ground-value-quotient-elimination-proofᵀ
    {qD = qD} vV vV′
    (paired-downᵀ M⊑M′ (gradual↓ mode seal★) d⊒ d-shape
      id-only↓ d′⊒ d′-shape square)
    | refl =
  q ,
  ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
    (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d′⊒)
    (cast⊒⊑ᵀ mode seal★ d⊒
      M⊑M′ q d-shape source-composition)
    q d′-shape target-composition
  where
  q = ⊑ᵖ-ground-right T.★⇒★ qD

  final-shape =
    cast-shape-result-unique d′-shape
      (inert-function-ground-narrowing-shape
        d′⊒ (cast-value-inert vV′))

  source-composition =
    ⊑ᵖ-function-ground-right-composition qD square final-shape

  target-composition =
    imprecision-composition-shape-transport
      refl final-shape refl
      (function-ground-right-identity-composition q)
target-function-ground-value-quotient-elimination-proofᵀ
    {qD = qD} vV vV′
    (paired-downᵀ M⊑M′ (gradual↓ mode seal★) d⊒ d-shape
      (gradual↓ mode′ seal★′) d′⊒ d′-shape square)
    | refl =
  q ,
  ⊑cast⊒ᵀ mode′ seal★′ d′⊒
    (cast⊒⊑ᵀ mode seal★ d⊒
      M⊑M′ q d-shape source-composition)
    q d′-shape target-composition
  where
  q = ⊑ᵖ-ground-right T.★⇒★ qD

  final-shape =
    cast-shape-result-unique d′-shape
      (inert-function-ground-narrowing-shape
        d′⊒ (cast-value-inert vV′))

  source-composition =
    ⊑ᵖ-function-ground-right-composition qD square final-shape

  target-composition =
    imprecision-composition-shape-transport
      refl final-shape refl
      (function-ground-right-identity-composition q)

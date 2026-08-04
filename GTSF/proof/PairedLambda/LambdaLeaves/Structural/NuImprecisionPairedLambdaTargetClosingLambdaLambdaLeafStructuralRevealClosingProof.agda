module
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingProof
  where

-- File Charter:
--   * Reduces the structural matched-`Lambda` paired-reveal leaf to its exact
--     live source-`reveal-all` and matched/matched double-unseal branches.
--   * Exhaustively eliminates impossible reveal and imprecision indices using
--     ambient world coherence, source-name exclusivity, and fresh-variable
--     lower-bound impossibility.
--   * Contains no implementation of either live branch, postulate, hole,
--     permissive option, broad simulation import, or recursive closer.

open import Conversion using
  ( reveal-all
  ; reveal-id-var
  ; reveal-unseal
  )
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.Any using (there)
open import ImprecisionWf using (idˣ; tagˣ; ∀ⁱ_; ν)
open import proof.Core.Properties.ImprecisionProperties using (un⇑ᵢ-★∈)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (no-occurs-var-lower-νctxᵢ)
open import
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralAllRevealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafStructuralAllRevealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (corresponds-idˣ)
open import Types using (`∀)


paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-proofᵀ :
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralAllRevealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-proofᵀ
    all-reveal matched-unseal liftΛ liftγ
    vV noV vV′ noV′ V⊑V′ {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    (reveal-all source-reveal) target-reveal =
  all-reveal liftΛ liftγ vV noV vV′ noV′ V⊑V′ {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    source-reveal target-reveal
paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-proofᵀ
    all-reveal matched-unseal {r = tagˣ (there star∈) α<} liftΛ liftγ
    vV noV vV′ noV′ V⊑V′ {X = `∀ F}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    (reveal-unseal hX αX∈Σ ok) target-reveal =
  ⊥-elim
    (exclusive (un⇑ᵢ-★∈ star∈) (corresponds-idˣ coherent corr))
paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-proofᵀ
    all-reveal matched-unseal {r = idˣ (there match∈) α< β<}
    liftΛ liftγ
    vV noV vV′ noV′ V⊑V′ {X = `∀ F} {q = ν safe occ body}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    (reveal-unseal hX αX∈Σ ok)
    (reveal-id-var hY ok′) =
  ⊥-elim (no-occurs-var-lower-νctxᵢ occ body)
paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-proofᵀ
    all-reveal matched-unseal {r = idˣ (there match∈) α< β<}
    liftΛ liftγ
    vV noV vV′ noV′ V⊑V′ {X = `∀ F} {p = p}
    {q = ν safe occ body}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    source-reveal@(reveal-unseal hX αX∈Σ ok)
    target-reveal@(reveal-unseal hX′ βX′∈Σ ok′) =
  matched-unseal liftΛ liftγ vV noV vV′ noV′ V⊑V′ {p = p}
    {q = ν safe occ body}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    source-reveal target-reveal
paired-lambda-target-closing-lambda-lambda-leaf-structural-reveal-closing-proofᵀ
    all-reveal matched-unseal {r = idˣ (there match∈) α< β<}
    liftΛ liftγ
    vV noV vV′ noV′ V⊑V′ {X = `∀ F} {X′ = `∀ G}
    {p = p} {q = ∀ⁱ body}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    source-reveal@(reveal-unseal hX αX∈Σ ok)
    target-reveal@(reveal-unseal hX′ βX′∈Σ ok′) =
  matched-unseal liftΛ liftγ vV noV vV′ noV′ V⊑V′ {p = p}
    {q = ∀ⁱ body}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    source-reveal target-reveal

module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareProof
  where

-- File Charter:
--   * Reduces both target/imprecision fresh-path half-squares to their exact
--     structural outer-universal contracts.
--   * Proves internally that an active target unseal is incompatible with a
--     used fresh source-only variable.
--   * Contains no structural half-square implementation, postulate, hole,
--     permissive option, handler import, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Conversion using
  ( conceal-all
  ; reveal-all
  ; reveal-unseal
  )
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_≟_; suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; idˣ
  ; ν
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (no; yes)
open import Types using (Ty; TyCtx; TyVar; ＇_; occurs)
open import proof.Core.Properties.ImprecisionProperties using
  ( no-⇑ᴸᵢ-zero-left
  ; un⇑ᴸᵢ-ˣ∈
  )
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using (at-body)
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
  )


occurs-var-true→≡ :
  ∀ {X Y} →
  occurs X (＇ Y) ≡ true →
  X ≡ Y
occurs-var-true→≡ {X} {Y} occ with X ≟ Y
occurs-var-true→≡ {X} {.X} occ | yes refl = refl
occurs-var-true→≡ {X} {Y} () | no X≢Y


fresh-source-only-no-var :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ Y) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  ⊥
fresh-source-only-no-var (here ())
fresh-source-only-no-var (there member) =
  no-⇑ᴸᵢ-zero-left member


lift-source-only-no-var :
  ∀ {Φ X} →
  (∀ {Y} → (X ˣ⊑ˣ Y) ∈ Φ → ⊥) →
  ∀ {Y} →
  (suc X ˣ⊑ˣ Y) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  ⊥
lift-source-only-no-var no-var (here ())
lift-source-only-no-var no-var (there member) =
  no-var (un⇑ᴸᵢ-ˣ∈ member)


source-only-occurrence-cannot-target-var :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {A : Ty} {X Y : TyVar} →
  (∀ {Z} → (X ˣ⊑ˣ Z) ∈ Φ → ⊥) →
  Φ ∣ Δᴸ ⊢ A ⊑ ＇ Y ⊣ Δᴿ →
  occurs X A ≡ true →
  ⊥
source-only-occurrence-cannot-target-var no-var
    (idˣ member X<Δ Y<Δ) occ =
  no-var
    (subst (λ Z → (Z ˣ⊑ˣ _) ∈ _)
      (sym (occurs-var-true→≡ occ)) member)
source-only-occurrence-cannot-target-var no-var (ν _ occ-A relation) occ =
  source-only-occurrence-cannot-target-var
    (lift-source-only-no-var no-var) relation occ


paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ :
  PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ →
  PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ
    structural {r = r} corresponds
    (reveal-unseal hX′ β∈Σ ok) occ-B source-path fresh-path =
  ⊥-elim
    (source-only-occurrence-cannot-target-var
      fresh-source-only-no-var r occ-B)
paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ
    structural {B = B} {r = r} {s = s} corresponds
    (reveal-all target-reveal) occ-B source-path
    (at-body fresh-path) =
  at-body
    (structural {B = B} {r = r} {s = s}
      corresponds target-reveal occ-B source-path fresh-path)


paired-universal-conversion-fresh-path-target-conceal-half-square-proofᵀ :
  PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ →
  PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-conceal-half-square-proofᵀ
    structural {B = B} {r = r} {s = s} corresponds
    (conceal-all target-conceal) occ-B source-path
    (at-body fresh-path) =
  at-body
    (structural {B = B} {r = r} {s = s}
      corresponds target-conceal occ-B source-path fresh-path)

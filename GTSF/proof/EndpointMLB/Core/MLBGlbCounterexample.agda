module proof.EndpointMLB.Core.MLBGlbCounterexample where

-- File Charter:
--   * Formalizes the small counterexample from `GTSF/notes.md` showing that
--     lower bounds of two consistent types need not have a greatest element.
--   * Refutes the broad monotonicity claim for the canonical endpoint
--     selector without depending on a historical evidence-directed selector.
--   * Uses `ImprecisionWf` for the positive lower-bound witnesses and the
--     old imprecision decision procedure, via `⊑-forgetᵢ`, for the negative
--     incomparability witnesses.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)

open import Types
import Imprecision as Imp
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.Core.Properties.ImprecisionProperties using (idᵢ-var-identity)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using (MLB; rawEndpointMlbsAt)
open import proof.EndpointMLB.Core.MLBGlbExample
open import proof.Core.Properties.NuImprecisionWfBridgeProperties using
  (⊑-forgetᵢ)

------------------------------------------------------------------------
-- The flipped lower bounds are incomparable.
------------------------------------------------------------------------

glb-lower-XY⋢YX-old : ¬ (idᵢ zero Imp.⊢ glb-lower-XY ⊑ glb-lower-YX)
glb-lower-XY⋢YX-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    with idᵢ-var-identity x∈
glb-lower-XY⋢YX-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    | ()
glb-lower-XY⋢YX-old (Imp.∀ⁱ (Imp.ν safe occ ()))
glb-lower-XY⋢YX-old (Imp.ν safe occ (Imp.∀ⁱ ()))
glb-lower-XY⋢YX-old (Imp.ν safe occ (Imp.ν safe′ occ′ ()))

glb-lower-YX⋢XY-old : ¬ (idᵢ zero Imp.⊢ glb-lower-YX ⊑ glb-lower-XY)
glb-lower-YX⋢XY-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    with idᵢ-var-identity x∈
glb-lower-YX⋢XY-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    | ()
glb-lower-YX⋢XY-old (Imp.∀ⁱ (Imp.ν safe occ ()))
glb-lower-YX⋢XY-old (Imp.ν safe occ (Imp.∀ⁱ ()))
glb-lower-YX⋢XY-old (Imp.ν safe occ (Imp.ν safe′ occ′ ()))

glb-lower-XY⋢YX :
  ¬ (idᵢ zero ∣ zero ⊢ glb-lower-XY ⊑ glb-lower-YX ⊣ zero)
glb-lower-XY⋢YX p = glb-lower-XY⋢YX-old (⊑-forgetᵢ p)

glb-lower-YX⋢XY :
  ¬ (idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ glb-lower-XY ⊣ zero)
glb-lower-YX⋢XY p = glb-lower-YX⋢XY-old (⊑-forgetᵢ p)

------------------------------------------------------------------------
-- The source factors through the compatible raw target route.
------------------------------------------------------------------------

glb-lower-YX-raw :
  glb-lower-YX ∈ rawEndpointMlbsAt zero glb-bad-A glb-bad-B
glb-lower-YX-raw = there (here refl)

glb-lower-YX⊑YX :
  idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ glb-lower-YX ⊣ zero
glb-lower-YX⊑YX =
  ∀ⁱ
    (∀ⁱ
      ( idˣ (here refl) z<s z<s
      ↦ idˣ (there (here refl)) (s<s z<s) (s<s z<s)
      ))

glb-lower-YX-raw-factor :
  ∃[ D ]
    (D ∈ rawEndpointMlbsAt zero glb-bad-A glb-bad-B ×
     idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ D ⊣ zero)
glb-lower-YX-raw-factor =
  glb-lower-YX , glb-lower-YX-raw , glb-lower-YX⊑YX

------------------------------------------------------------------------
-- No maximal endpoint selector can satisfy the proposed broad coherence.
------------------------------------------------------------------------

bad-simple-selector-coherence-counterexampleᵢ :
  ¬
    (∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      MLB Δᴸ A B ≡ just C →
      MLB Δᴿ A′ B′ ≡ just C′ →
      Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
bad-simple-selector-coherence-counterexampleᵢ coherence =
  glb-lower-YX⋢XY
    (coherence
      {Φ = idᵢ zero}
      {Δᴸ = zero}
      {Δᴿ = zero}
      {A = glb-lower-YX}
      {A′ = glb-bad-A}
      {B = glb-lower-YX}
      {B′ = glb-bad-B}
      {C = glb-lower-YX}
      {C′ = glb-lower-XY}
      {pA = glb-lower-YX⊑A}
      {pB = glb-lower-YX⊑B}
      refl
      refl)

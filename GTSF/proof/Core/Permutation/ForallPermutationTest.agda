module proof.Core.Permutation.ForallPermutationTest where

-- File Charter:
--   * Checks that the two incomparable bad-GLB lower bounds become equivalent
--     under the `∀`-permutation quotient.
--   * Demonstrates bidirectional quotiented imprecision without adding ordinary
--     imprecision between the exposed types.

open import Agda.Builtin.Equality using (refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; z<s; s<s)

open import Types
open import Imprecision using (idᵢ)
import ImprecisionWf as IWF
open import ForallPermutation
open import proof.EndpointMLB.Core.MLBGlbExample using (glb-lower-XY; glb-lower-YX)

glb-lower-XY≈YX : glb-lower-XY ≈∀ glb-lower-YX
glb-lower-XY≈YX = ≈∀-swap

glb-lower-YX≈XY : glb-lower-YX ≈∀ glb-lower-XY
glb-lower-YX≈XY = ≈∀-sym glb-lower-XY≈YX

glb-lower-XY⊑XY :
  idᵢ zero IWF.∣ zero ⊢ glb-lower-XY ⊑ glb-lower-XY ⊣ zero
glb-lower-XY⊑XY =
  IWF.∀ⁱ
    (IWF.∀ⁱ
      ( IWF.idˣ (there (here refl)) (s<s z<s) (s<s z<s)
      IWF.↦ IWF.idˣ (here refl) z<s z<s
      ))

glb-lower-YX⊑YX :
  idᵢ zero IWF.∣ zero ⊢ glb-lower-YX ⊑ glb-lower-YX ⊣ zero
glb-lower-YX⊑YX =
  IWF.∀ⁱ
    (IWF.∀ⁱ
      ( IWF.idˣ (here refl) z<s z<s
      IWF.↦ IWF.idˣ (there (here refl)) (s<s z<s) (s<s z<s)
      ))

glb-lower-XY⊑ᵖYX :
  idᵢ zero ∣ zero ⊢ glb-lower-XY ⊑ᵖ glb-lower-YX ⊣ zero
glb-lower-XY⊑ᵖYX =
  quotientᵖ ≈∀-refl glb-lower-XY⊑XY glb-lower-XY≈YX

glb-lower-YX⊑ᵖXY :
  idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ᵖ glb-lower-XY ⊣ zero
glb-lower-YX⊑ᵖXY =
  quotientᵖ ≈∀-refl glb-lower-YX⊑YX glb-lower-YX≈XY

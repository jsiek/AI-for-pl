module proof.EndpointMLB.Core.MLBGlbExample where

-- File Charter:
--   * Defines the small polymorphic endpoint pair with two incomparable
--     common lower bounds used by the GLB and operational experiments.
--   * Provides only the endpoint and lower-bound imprecision witnesses.
--   * Deliberately avoids selector and maximal-lower-bound metatheory so
--     executable experiments can import it cheaply.

open import Agda.Builtin.Equality using (refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s; s<s)

open import Types
open import Imprecision using (idᵢ)
open import ImprecisionWf

glb-bad-A : Ty
glb-bad-A = `∀ (＇ zero ⇒ ★)

glb-bad-B : Ty
glb-bad-B = `∀ (★ ⇒ ＇ zero)

glb-bad-A⊑A : idᵢ zero ∣ zero ⊢ glb-bad-A ⊑ glb-bad-A ⊣ zero
glb-bad-A⊑A =
  ∀ⁱ (idˣ (here refl) z<s z<s ↦ id★)

glb-bad-B⊑B : idᵢ zero ∣ zero ⊢ glb-bad-B ⊑ glb-bad-B ⊣ zero
glb-bad-B⊑B =
  ∀ⁱ (id★ ↦ idˣ (here refl) z<s z<s)

-- `∀X. ∀Y. X → Y`
glb-lower-XY : Ty
glb-lower-XY = `∀ (`∀ (＇ (suc zero) ⇒ ＇ zero))

-- `∀Y. ∀X. X → Y`
glb-lower-YX : Ty
glb-lower-YX = `∀ (`∀ (＇ zero ⇒ ＇ (suc zero)))

glb-lower-XY⊑A :
  idᵢ zero ∣ zero ⊢ glb-lower-XY ⊑ glb-bad-A ⊣ zero
glb-lower-XY⊑A =
  ∀ⁱ
    (ν nonvar-fun refl
      ( idˣ (there (here refl)) (s<s z<s) z<s
      ↦ tagˣ (here refl) z<s
      ))

glb-lower-XY⊑B :
  idᵢ zero ∣ zero ⊢ glb-lower-XY ⊑ glb-bad-B ⊣ zero
glb-lower-XY⊑B =
  ν nonvar-all refl
    (∀ⁱ
      ( tagˣ (there (here refl)) (s<s z<s)
      ↦ idˣ (here refl) z<s z<s
      ))

glb-lower-YX⊑A :
  idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ glb-bad-A ⊣ zero
glb-lower-YX⊑A =
  ν nonvar-all refl
    (∀ⁱ
      ( idˣ (here refl) z<s z<s
      ↦ tagˣ (there (here refl)) (s<s z<s)
      ))

glb-lower-YX⊑B :
  idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ glb-bad-B ⊣ zero
glb-lower-YX⊑B =
  ∀ⁱ
    (ν nonvar-fun refl
      ( tagˣ (here refl) z<s
      ↦ idˣ (there (here refl)) (s<s z<s) z<s
      ))

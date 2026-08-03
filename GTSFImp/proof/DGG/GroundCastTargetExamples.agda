module proof.DGG.GroundCastTargetExamples where

-- File Charter:
--   * Records small concrete uses of `ground-cast-target⊑`.
--   * Serves as a probe for the ground-target imprecision helper used by the
--     extra-cast-on-the-right proof.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Types
import Consistency as C
import Imprecision as I
import proof.ImprecisionConsistency as IC

------------------------------------------------------------------------
-- Atomic and function grounds
------------------------------------------------------------------------

base-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (‵ `ℕ) (‵ `ℕ)
base-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = ‵ `ℕ} {B = ‵ `ℕ} {G = ‵ `ℕ}
    C.g-ι nonstar-ι (C.id (‵ `ℕ)) I.ι⊑ι I.ι⊑★

fun-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (‵ `ℕ ⇒ ‵ `𝔹) (★ ⇒ ★)
fun-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = ‵ `ℕ ⇒ ‵ `𝔹} {B = ‵ `ℕ ⇒ ‵ `𝔹} {G = ★ ⇒ ★}
    C.g-⇒ nonstar-⇒
    (C._↦_ (C._! (C.id (‵ `ℕ))) (C._! (C.id (‵ `𝔹))))
    (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)
    (I.⇒⊑★ I.ι⊑★ I.ι⊑★)

var-ground-target :
  I._⊢_⊑_ (I.instᵐ (I.idᵐ {Δ = 0})) (＇ zero) (＇ zero)
var-ground-target =
  IC.ground-cast-target⊑ {Δ = 1}
    {μ = I.instᵐ (I.idᵐ {Δ = 0})}
    {ν = C.instᵐ (C.idᶜ {Δ = 0})}
    {A = ＇ zero} {B = ＇ zero} {G = ＇ zero}
    (C.g-X refl) nonstar-X (C.id (＇ zero)) I.X⊑X
    (I.X⊑★ refl)

------------------------------------------------------------------------
-- Universal ground
------------------------------------------------------------------------

all-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (`∀ ★) (`∀ ★)
all-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = `∀ ★} {B = `∀ ★} {G = `∀ ★}
    C.g-∀ nonstar-∀ (C.∀ᶜ (C.id ★)) (I.∀⊑∀ I.★⊑★)
    I.∀★⊑★

bot-elim-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (`∀ (＇ zero)) (`∀ ★)
bot-elim-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = `∀ (＇ zero)} {B = `∀ (＇ zero)} {G = `∀ ★}
    C.g-∀ nonstar-∀ C.bot-elim
    (I.∀⊑∀ I.X⊑X) I.bot⊑★

forall-closed-body-to-universal-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (`∀ (‵ `ℕ ⇒ ★)) (`∀ ★)
forall-closed-body-to-universal-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = `∀ (‵ `ℕ ⇒ ★)} {B = `∀ (‵ `ℕ ⇒ ★)} {G = `∀ ★}
    C.g-∀ nonstar-∀
    (C.∀ᶜ (C._! (C._↦_ (C._! (C.id (‵ `ℕ))) (C.id ★))))
    (I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.★⊑★))
    (I.∀⊑★ nonstar-⇒
      (I.⇒⊑★ I.ι⊑★ I.★⊑★))

forall-elim-to-fun-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (`∀ (＇ zero ⇒ ★)) (★ ⇒ ★)
forall-elim-to-fun-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = `∀ (＇ zero ⇒ ★)} {B = ★ ⇒ ★} {G = ★ ⇒ ★}
    C.g-⇒ nonstar-⇒
    (C._↦_ (C.id ★) (C.id ★))
    (I.∀⊑ nonvar-fun (∈-fun-left var-∈)
      (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★))
    (I.∀⊑ nonvar-fun (∈-fun-left var-∈)
      (I.⇒⊑★ (I.X⊑★ refl) I.★⊑★))

inst-consistency-to-fun-ground-target :
  I._⊢_⊑_ (I.idᵐ {Δ = 0}) (`∀ (＇ zero ⇒ ★)) (★ ⇒ ★)
inst-consistency-to-fun-ground-target =
  IC.ground-cast-target⊑ {Δ = 0} {μ = I.idᵐ} {ν = C.idᶜ}
    {A = `∀ (＇ zero ⇒ ★)} {B = `∀ (＇ zero ⇒ ★)}
    {G = ★ ⇒ ★}
    C.g-⇒ nonstar-∀
    (C.inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = ∈-fun-left var-∈ ⦄
      (C._↦_ (C._! (C.id (＇ zero))) (C.id ★)) (λ ()))
    (I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.★⊑★))
    (I.∀⊑ nonvar-fun (∈-fun-left var-∈)
      (I.⇒⊑★ (I.X⊑★ refl) I.★⊑★))

------------------------------------------------------------------------
-- Why the `A ⊑ ★` premise is not redundant for arbitrary environments
------------------------------------------------------------------------

no-star-counterexample-consistency :
  C._⊢_∼_ (C.instᵐ (C.idᶜ {Δ = 0}))
    (＇ zero ⇒ ＇ zero) (★ ⇒ ★)
no-star-counterexample-consistency =
  C._↦_ (C._! (C.id (＇ zero))) (C._! (C.id (＇ zero)))

no-star-counterexample-imprecision :
  I._⊢_⊑_ (I.idᵐ {Δ = 1})
    (＇ zero ⇒ ＇ zero) (＇ zero ⇒ ＇ zero)
no-star-counterexample-imprecision =
  I.⇒⊑⇒ I.X⊑X I.X⊑X

no-star-counterexample-conclusion-impossible :
  I._⊢_⊑_ (I.idᵐ {Δ = 1}) (＇ zero ⇒ ＇ zero) (★ ⇒ ★)
    → ⊥
no-star-counterexample-conclusion-impossible
    (I.⇒⊑⇒ (I.X⊑★ ()) _)

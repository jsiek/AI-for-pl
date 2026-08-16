module
  proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof where

-- File Charter:
--   * Proves that store allocation preserves pending-spine cast mass.
--   * Supplies allocation transport for structural instantiation.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import Reduction using (StoreChange; keep; bind)
open import proof.DGG.Catchup.FuelSupportProof using
  (castSize-applyConsistency)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef


spine-cast-mass-map : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (spine : InstantiationSpine A B)
  → spineCastMass (mapInstantiationSpine χ spine) ≡
      spineCastMass spine
spine-cast-mass-map keep []ⁱ = refl
spine-cast-mass-map (bind R) []ⁱ = refl
spine-cast-mass-map keep (type-transport-frame eq ▻ⁱ spine) =
  spine-cast-mass-map keep spine
spine-cast-mass-map (bind R) (type-transport-frame eq ▻ⁱ spine) =
  spine-cast-mass-map (bind R) spine
spine-cast-mass-map keep
    (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  spine-cast-mass-map keep spine
spine-cast-mass-map (bind R)
    (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  spine-cast-mass-map (bind R) spine
spine-cast-mass-map keep (cast-frame c ▻ⁱ spine)
    rewrite spine-cast-mass-map keep spine = refl
spine-cast-mass-map (bind R) (cast-frame c ▻ⁱ spine)
    rewrite castSize-applyConsistency (bind R) c
          | spine-cast-mass-map (bind R) spine = refl
spine-cast-mass-map keep (reveal-frame c ▻ⁱ spine) =
  spine-cast-mass-map keep spine
spine-cast-mass-map (bind R) (reveal-frame c ▻ⁱ spine) =
  spine-cast-mass-map (bind R) spine
spine-cast-mass-map keep (conceal-frame c ▻ⁱ spine) =
  spine-cast-mass-map keep spine
spine-cast-mass-map (bind R) (conceal-frame c ▻ⁱ spine) =
  spine-cast-mass-map (bind R) spine

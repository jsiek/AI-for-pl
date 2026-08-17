module proof.DGG.Catchup.StructuralValueInstantiationRankDef where

-- File Charter:
--   * Defines the internal administrative rank for structural named
--     instantiation.
--   * Counts pending name frames first, then exponential conversion-crossing
--     potential, then raw spine length.
--   * The rank is proof-recursion control and is not part of the public
--     instantiation package surface.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)

open import Types using (Ty)
import CastTerms as CT
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


valueConversionUnits : ∀ {Δ} {V : CT.Term Δ} → CT.Value V → ℕ
valueConversionUnits (CT.ƛ N) = zero
valueConversionUnits (CT.Λ vV) = valueConversionUnits vV
valueConversionUnits (CT.$ k) = zero
valueConversionUnits (vV CT.《 inert 》) = valueConversionUnits vV
valueConversionUnits (vV CT.↑ reveal-value) =
  suc (valueConversionUnits vV)
valueConversionUnits (vV CT.↓ conceal-value) =
  suc (valueConversionUnits vV)


nameFrames : ∀ {Δ A B} → InstantiationSpine {Δ} A B → ℕ
nameFrames []ⁱ = zero
nameFrames (type-transport-frame eq ▻ⁱ spine) = nameFrames spine
nameFrames (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  suc (nameFrames spine)
nameFrames (cast-frame c ▻ⁱ spine) = nameFrames spine
nameFrames (reveal-frame c ▻ⁱ spine) = nameFrames spine
nameFrames (conceal-frame c ▻ⁱ spine) = nameFrames spine


spineConversionPotential :
  ∀ {Δ A B} → InstantiationSpine {Δ} A B → ℕ
spineConversionPotential []ⁱ = zero
spineConversionPotential (type-transport-frame eq ▻ⁱ spine) =
  spineConversionPotential spine
spineConversionPotential
    (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  spineConversionPotential spine
spineConversionPotential (cast-frame c ▻ⁱ spine) =
  spineConversionPotential spine
spineConversionPotential (reveal-frame c ▻ⁱ spine) =
  3 ^ nameFrames spine + spineConversionPotential spine
spineConversionPotential (conceal-frame c ▻ⁱ spine) =
  3 ^ nameFrames spine + spineConversionPotential spine


expPotential : ∀ {Δ} {V : CT.Term Δ} {A B : Ty Δ}
  → CT.Value V
  → InstantiationSpine A B
  → ℕ
expPotential vV spine =
  valueConversionUnits vV * (3 ^ nameFrames spine) +
  spineConversionPotential spine


spineLength : ∀ {Δ A B} → InstantiationSpine {Δ} A B → ℕ
spineLength []ⁱ = zero
spineLength (frame ▻ⁱ spine) = suc (spineLength spine)


record InstantiationRank : Set where
  constructor inst-rank
  field
    rankNameFrames : ℕ
    rankExpPotential : ℕ
    rankSpineLength : ℕ


pendingRank : ∀ {Δ} {V : CT.Term Δ} {A B : Ty Δ}
  → CT.Value V
  → InstantiationSpine A B
  → InstantiationRank
pendingRank vV spine =
  inst-rank (nameFrames spine) (expPotential vV spine)
    (spineLength spine)

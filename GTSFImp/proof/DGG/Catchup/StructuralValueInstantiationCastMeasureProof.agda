module
  proof.DGG.Catchup.StructuralValueInstantiationCastMeasureProof where

-- File Charter:
--   * Proves the non-exact rank edge for opening a universal cast.
--   * Uses only non-increase of the opened body consistency size.
--   * Leaves the concrete opening theorem to the structural worker.

open import Data.Nat using (_≤_; _<_; _+_; _*_; suc; s≤s)
open import Data.Nat.Properties using (≤-refl; +-mono-≤)

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_; extᵐ; ∀ᶜ_)
import CastTerms as CT
open import proof.Consistency using (castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef

private
  double-mono : ∀ {m n} → m ≤ n → 2 * m ≤ 2 * n
  double-mono m≤n = +-mono-≤ m≤n (+-mono-≤ m≤n ≤-refl)

cast-frame-rank-size-mono : ∀ {Δ Δᵈ} {A B E : Ty Δ}
    {C D : Ty Δᵈ} {μ : Env∼ Δ} {ν : Env∼ Δᵈ} {V}
    {c : μ ⊢ A ∼ B} {d : ν ⊢ C ∼ D}
    (vV : CT.Value {Δ = Δ} V) (spine : InstantiationSpine B E)
  → castSize c ≤ castSize d
  → pendingAdministrationRank vV (cast-frame c ▻ⁱ spine) ≤
      2 * (valueAdministrationWeight vV +
        (castAdministrationWeight d + spineAdministrationWeight spine)) +
        suc (spineCastLength spine)
cast-frame-rank-size-mono {c = c} {d = d} vV spine size≤ =
  +-mono-≤ (double-mono inner≤) ≤-refl
  where
  cast≤ : castAdministrationWeight c ≤ castAdministrationWeight d
  cast≤ = s≤s (double-mono size≤)

  inner≤ : valueAdministrationWeight vV +
      (castAdministrationWeight c + spineAdministrationWeight spine) ≤
    valueAdministrationWeight vV +
      (castAdministrationWeight d + spineAdministrationWeight spine)
  inner≤ = +-mono-≤ ≤-refl (+-mono-≤ cast≤ ≤-refl)

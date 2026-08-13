module proof.DGG.Catchup.StructuralValueInstantiationAllMeasureProof where

-- File Charter:
--   * Proves strict rank descent for an opened universal cast wrapper.
--   * Consumes only a non-increasing cast-size proof for the opened body.

open import Data.Nat using (_≤_; _<_; _+_; _*_; suc; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-<-trans; n≤1+n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_; extᵐ; ∀ᶜ_)
import CastTerms as CT
open import proof.Consistency using (castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationMeasureDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMeasureProof
  using (cast-frame-rank-size-mono)

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)


private
  cast-administration-weight-all : ∀ {Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} (d : extᵐ μ ⊢ A ∼ B)
    → castAdministrationWeight (∀ᶜ d) ≡
        suc (suc (castAdministrationWeight d))
  cast-administration-weight-all d =
    solve 1
      (λ s → con 1 :+ (con 2 :* (con 1 :+ s)) :=ᵉ
        con 2 :+ (con 1 :+ (con 2 :* s)))
      refl (castSize d)

  all-rank-gap : ∀ {Δ} {A B : Ty (suc Δ)} {C D : Ty Δ}
      {μ : Env∼ Δ} {V} {d : extᵐ μ ⊢ A ∼ B}
      (vV : CT.Value {Δ = Δ} V) (spine : InstantiationSpine C D)
    → pendingAdministrationRank (vV CT.《 CT.all {c = d} 》) spine ≡
        suc (suc (suc
          (2 * (valueAdministrationWeight vV +
            (castAdministrationWeight d +
              spineAdministrationWeight spine)) +
            suc (spineCastLength spine))))
  all-rank-gap {d = d} vV spine =
    trans
      (cong
        (λ q → 2 * ((valueAdministrationWeight vV + q) +
          spineAdministrationWeight spine) + spineCastLength spine)
        (cast-administration-weight-all d))
      (solve 4
        (λ w q p l →
          (con 2 :* ((w :+ (con 1 :+ (con 1 :+ q))) :+ p)) :+ l :=ᵉ
          con 3 :+ ((con 2 :* (w :+ (q :+ p))) :+ (con 1 :+ l)))
        refl (valueAdministrationWeight vV) (castAdministrationWeight d)
        (spineAdministrationWeight spine) (spineCastLength spine))


all-instantiation-rank-decreases : ∀ {Δ} {A B : Ty (suc Δ)}
    {C D E : Ty Δ} {μ ν : Env∼ Δ} {V}
    {c : ν ⊢ C ∼ D} {d : extᵐ μ ⊢ A ∼ B}
    (vV : CT.Value {Δ = Δ} V) (spine : InstantiationSpine D E)
  → castSize c ≤ castSize d
  → pendingAdministrationRank vV (cast-frame c ▻ⁱ spine) <
      pendingAdministrationRank (vV CT.《 CT.all {c = d} 》) spine
all-instantiation-rank-decreases {c = c} {d = d} vV spine size≤ =
  ≤-<-trans (cast-frame-rank-size-mono vV spine size≤) upper<outer
  where
  upper = 2 * (valueAdministrationWeight vV +
    (castAdministrationWeight d + spineAdministrationWeight spine)) +
    suc (spineCastLength spine)

  upper<outer : upper <
      pendingAdministrationRank (vV CT.《 CT.all {c = d} 》) spine
  upper<outer =
    subst (λ n → upper < n) (sym (all-rank-gap vV spine))
      (s≤s (≤-trans (n≤1+n upper) (n≤1+n (suc upper))))

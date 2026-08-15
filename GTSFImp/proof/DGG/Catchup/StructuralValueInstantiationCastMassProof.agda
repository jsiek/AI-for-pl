module
  proof.DGG.Catchup.StructuralValueInstantiationCastMassProof where

-- File Charter:
--   * Proves primary cast-mass descent for all, gen, and inst transitions.
--   * Leaves cast-mass-preserving conversion steps to a secondary measure.

open import Data.Nat using (_≤_; _<_; _+_; suc)
open import Data.Nat.Properties using (≤-refl; ≤-<-trans; +-mono-≤; n<1+n)
open import Data.Nat.Solver using (module +-*-Solver)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym)

open import Types using (Ty; NonVar; _∈ᵗ_; ⇑ᵗ)
open import Consistency using (Env∼; _⊢_∼_; ∀ᶜ_; gen_; inst_)
import CastTerms as CT
open import proof.Consistency using (castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef

open +-*-Solver using (solve; _:+_; con)
  renaming (_:=_ to _:=ᵉ_)


all-cast-mass-decreases : ∀ {Δ} {A B E : Ty Δ}
    {C D : Ty (suc Δ)} {μ ν : Env∼ Δ}
    {V} {c : μ ⊢ A ∼ B} {d : Consistency.extᵐ ν ⊢ C ∼ D}
    (vV : CT.Value { Δ = Δ } V) (spine : InstantiationSpine B E)
  → castSize c ≤ castSize d
  → pendingCastMass vV (cast-frame c ▻ⁱ spine) <
      pendingCastMass (vV CT.《 CT.all {c = d} 》) spine
all-cast-mass-decreases {c = c} {d = d} vV spine c≤d =
  ≤-<-trans child≤upper
    (subst (λ n → upper < n) (sym outer-gap) (n<1+n upper))
  where
  upper = valueCastMass vV + (castSize d + spineCastMass spine)
  child≤upper : pendingCastMass vV (cast-frame c ▻ⁱ spine) ≤ upper
  child≤upper =
    +-mono-≤ (≤-refl {x = valueCastMass vV})
      (+-mono-≤ c≤d (≤-refl {x = spineCastMass spine}))

  outer-gap : pendingCastMass (vV CT.《 CT.all {c = d} 》) spine
      ≡ suc upper
  outer-gap = solve 3
    (λ v s p → (v :+ (con 1 :+ s)) :+ p :=ᵉ
      con 1 :+ (v :+ (s :+ p)))
    refl (valueCastMass vV) (castSize d) (spineCastMass spine)


gen-value-cast-mass-gap : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {μ : Env∼ Δ} {V} {c : Consistency.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {A≠★} (vV : CT.Value { Δ = Δ } V) (safe : CT.GenSafe c)
  → valueCastMass (vV CT.《 CT.genᵥ A≠★ safe 》) ≡
      suc (valueCastMass vV + castSize c)
gen-value-cast-mass-gap {c = c} vV safe = solve 2
  (λ v s → v :+ (con 1 :+ s) :=ᵉ con 1 :+ (v :+ s))
  refl (valueCastMass vV) (castSize c)

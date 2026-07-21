module proof.NuImprecisionTargetAdministrationMeasureProof where

-- File Charter:
--   * Proves the natural-number equalities for the target administration
--     measure.
--   * Exposes strictly oriented rank-decrease equations for pending sequence,
--     inert absorption, instantiation, and target `ν` administration.
--   * Depends only on coercion sizes, target measure definitions, and
--     standard-library natural-number arithmetic.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; length)
open import Data.Nat using (suc; _+_)
open import Data.Nat.Solver using (module +-*-Solver)

open import Coercions using
  (Coercion; Inert; _︔_; `∀; gen; inst; renameᶜ; sizeᶜ;
   sizeᶜ-renameᶜ)
open import NuTerms using (Value; _⟨_⟩)
open import proof.NuImprecisionTargetAdministrationMeasureDef using
  ( castAdministrationWeight; valueAdministrationWeight
  ; pendingCastAdministrationWeight; targetPendingAdministrationRank
  ; targetNuAdministrationRank
  )

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)


cast-administration-weight-seq :
  ∀ s t →
  castAdministrationWeight (s ︔ t) ≡
  suc (castAdministrationWeight s + castAdministrationWeight t)
cast-administration-weight-seq s t =
  solve 2
    (λ a b →
      con 1 :+ (con 2 :* (con 1 :+ (a :+ b)))
      :=ᵉ
      con 1 :+ ((con 1 :+ (con 2 :* a)) :+
        (con 1 :+ (con 2 :* b))))
    refl
    (sizeᶜ s)
    (sizeᶜ t)

cast-administration-weight-all :
  ∀ c →
  castAdministrationWeight (`∀ c) ≡
  suc (suc (castAdministrationWeight c))
cast-administration-weight-all c =
  solve 1
    (λ a →
      con 1 :+ (con 2 :* (con 1 :+ a))
      :=ᵉ
      con 3 :+ (con 2 :* a))
    refl
    (sizeᶜ c)

cast-administration-weight-gen :
  ∀ A c →
  castAdministrationWeight (gen A c) ≡
  suc (suc (castAdministrationWeight c))
cast-administration-weight-gen A c =
  solve 1
    (λ a →
      con 1 :+ (con 2 :* (con 1 :+ a))
      :=ᵉ
      con 3 :+ (con 2 :* a))
    refl
    (sizeᶜ c)

cast-administration-weight-inst :
  ∀ B c →
  castAdministrationWeight (inst B c) ≡
  suc (suc (castAdministrationWeight c))
cast-administration-weight-inst B c =
  solve 1
    (λ a →
      con 1 :+ (con 2 :* (con 1 :+ a))
      :=ᵉ
      con 3 :+ (con 2 :* a))
    refl
    (sizeᶜ c)

cast-administration-weight-rename :
  ∀ ρ c →
  castAdministrationWeight (renameᶜ ρ c) ≡
  castAdministrationWeight c
cast-administration-weight-rename ρ c
  rewrite sizeᶜ-renameᶜ ρ c = refl

target-sequence-rank-decreases :
  ∀ {V} (vV : Value V) s t cs →
  targetPendingAdministrationRank vV ((s ︔ t) ∷ cs) ≡
  suc (targetPendingAdministrationRank vV (s ∷ t ∷ cs))
target-sequence-rank-decreases vV s t cs =
  solve 5
    (λ w a b p l →
      (con 2 :* (w :+
        ((con 1 :+ (con 2 :* (con 1 :+ (a :+ b)))) :+ p)))
      :+ (con 1 :+ l)
      :=ᵉ
      con 1 :+
      ((con 2 :* (w :+
        ((con 1 :+ (con 2 :* a)) :+
        ((con 1 :+ (con 2 :* b)) :+ p))))
      :+ (con 2 :+ l)))
    refl
    (valueAdministrationWeight vV)
    (sizeᶜ s)
    (sizeᶜ t)
    (pendingCastAdministrationWeight cs)
    (length cs)

target-inert-rank-decreases :
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  targetPendingAdministrationRank vV (c ∷ cs) ≡
  suc (targetPendingAdministrationRank (vV ⟨ inert-c ⟩) cs)
target-inert-rank-decreases {c = c} vV inert-c cs =
  solve 4
    (λ w q p l →
      (con 2 :* (w :+ (q :+ p))) :+ (con 1 :+ l)
      :=ᵉ
      con 1 :+ ((con 2 :* ((w :+ q) :+ p)) :+ l))
    refl
    (valueAdministrationWeight vV)
    (castAdministrationWeight c)
    (pendingCastAdministrationWeight cs)
    (length cs)

target-inst-rank-decreases :
  ∀ {V} (vV : Value V) B c cs →
  targetPendingAdministrationRank vV (inst B c ∷ cs) ≡
  suc (suc (suc (targetNuAdministrationRank vV c cs)))
target-inst-rank-decreases vV B c cs =
  solve 4
    (λ w a p l →
      (con 2 :* (w :+
        ((con 1 :+ (con 2 :* (con 1 :+ a))) :+ p)))
      :+ (con 1 :+ l)
      :=ᵉ
      con 3 :+
      (((con 2 :* ((w :+ (con 1 :+ (con 2 :* a))) :+ p))
      :+ (con 1 :+ l)) :+ con 1))
    refl
    (valueAdministrationWeight vV)
    (sizeᶜ c)
    (pendingCastAdministrationWeight cs)
    (length cs)

target-nu-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  targetNuAdministrationRank vV c cs ≡
  suc (targetPendingAdministrationRank vV (c ∷ cs))
target-nu-rank-decreases vV c cs =
  solve 4
    (λ w q p l →
      ((con 2 :* ((w :+ q) :+ p)) :+ (con 1 :+ l)) :+ con 1
      :=ᵉ
      con 1 :+ ((con 2 :* (w :+ (q :+ p))) :+ (con 1 :+ l)))
    refl
    (valueAdministrationWeight vV)
    (castAdministrationWeight c)
    (pendingCastAdministrationWeight cs)
    (length cs)

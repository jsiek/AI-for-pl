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
open import Data.Nat using (suc; zero; _+_)
open import Data.Nat.Solver using (module +-*-Solver)

import Coercions as C
open import Coercions using
  (Coercion; Inert; _︔_; `∀; gen; inst; renameᶜ; sizeᶜ;
   sizeᶜ-renameᶜ)
open import NuTerms using (Value; ƛ_; Λ_; $; _⟨_⟩)
open import proof.NuImprecisionTargetAdministrationMeasureDef using
  ( castAdministrationWeight; valueAdministrationWeight
  ; pendingCastAdministrationWeight; targetPendingAdministrationRank
  ; targetNuAdministrationRank
  )
open import proof.NuTermProperties using (renameᵗᵐ-preserves-Value)
open import Types using (Renameᵗ; extᵗ; singleRenameᵗ)

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


value-administration-weight-rename :
  ∀ (ρ : Renameᵗ) {V} (vV : Value V) →
  valueAdministrationWeight (renameᵗᵐ-preserves-Value ρ vV) ≡
  valueAdministrationWeight vV
value-administration-weight-rename ρ (ƛ N) = refl
value-administration-weight-rename ρ (Λ vV)
  rewrite value-administration-weight-rename (extᵗ ρ) vV = refl
value-administration-weight-rename ρ ($ k) = refl
value-administration-weight-rename ρ
    {V = V ⟨ c ⟩} (vV ⟨ inert-c ⟩)
  rewrite value-administration-weight-rename ρ vV
        | cast-administration-weight-rename ρ c = refl


value-administration-weight-all :
  ∀ {V} (vV : Value V) c →
  valueAdministrationWeight (vV ⟨ C.`∀ c ⟩) ≡
  suc (suc (valueAdministrationWeight vV +
    castAdministrationWeight c))
value-administration-weight-all vV c
    rewrite cast-administration-weight-all c =
  solve 2
    (λ w q →
      w :+ (con 1 :+ (con 1 :+ q))
      :=ᵉ
      con 1 :+ (con 1 :+ (w :+ q)))
    refl
    (valueAdministrationWeight vV)
    (castAdministrationWeight c)


value-administration-weight-gen :
  ∀ {V A} (vV : Value V) c →
  valueAdministrationWeight (vV ⟨ C.gen A c ⟩) ≡
  suc (suc (valueAdministrationWeight vV +
    castAdministrationWeight c))
value-administration-weight-gen {A = A} vV c
    rewrite cast-administration-weight-gen A c =
  solve 2
    (λ w q →
      w :+ (con 1 :+ (con 1 :+ q))
      :=ᵉ
      con 1 :+ (con 1 :+ (w :+ q)))
    refl
    (valueAdministrationWeight vV)
    (castAdministrationWeight c)

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


target-Λ-bullet-rank-decreases :
  ∀ {V} (vV : Value V) cs →
  targetPendingAdministrationRank (Λ vV) cs ≡
  suc (suc (targetPendingAdministrationRank
    (renameᵗᵐ-preserves-Value (singleRenameᵗ zero) vV) cs))
target-Λ-bullet-rank-decreases vV cs
    rewrite value-administration-weight-rename
      (singleRenameᵗ zero) vV =
  solve 3
    (λ w p l →
      (con 2 :* ((con 1 :+ w) :+ p)) :+ l
      :=ᵉ
      con 1 :+ (con 1 :+ ((con 2 :* (w :+ p)) :+ l)))
    refl
    (valueAdministrationWeight vV)
    (pendingCastAdministrationWeight cs)
    (length cs)


target-all-bullet-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  targetPendingAdministrationRank (vV ⟨ C.`∀ c ⟩) cs ≡
  suc (suc (suc (targetPendingAdministrationRank vV
    (renameᶜ (singleRenameᵗ zero) c ∷ cs))))
target-all-bullet-rank-decreases vV c cs
    rewrite value-administration-weight-all vV c
          | sizeᶜ-renameᶜ (singleRenameᵗ zero) c =
  solve 4
    (λ w q p l →
      (con 2 :* ((con 1 :+ (con 1 :+ (w :+ q))) :+ p)) :+ l
      :=ᵉ
      con 1 :+ (con 1 :+ (con 1 :+
        ((con 2 :* (w :+ (q :+ p))) :+ (con 1 :+ l)))))
    refl
    (valueAdministrationWeight vV)
    (castAdministrationWeight c)
    (pendingCastAdministrationWeight cs)
    (length cs)


target-gen-bullet-rank-decreases :
  ∀ {V A} (vV : Value V) c cs →
  targetPendingAdministrationRank (vV ⟨ C.gen A c ⟩) cs ≡
  suc (suc (suc (targetPendingAdministrationRank vV
    (renameᶜ (singleRenameᵗ zero) c ∷ cs))))
target-gen-bullet-rank-decreases {A = A} vV c cs
    rewrite value-administration-weight-gen {A = A} vV c
          | sizeᶜ-renameᶜ (singleRenameᵗ zero) c =
  solve 4
    (λ w q p l →
      (con 2 :* ((con 1 :+ (con 1 :+ (w :+ q))) :+ p)) :+ l
      :=ᵉ
      con 1 :+ (con 1 :+ (con 1 :+
        ((con 2 :* (w :+ (q :+ p))) :+ (con 1 :+ l)))))
    refl
    (valueAdministrationWeight vV)
    (castAdministrationWeight c)
    (pendingCastAdministrationWeight cs)
    (length cs)

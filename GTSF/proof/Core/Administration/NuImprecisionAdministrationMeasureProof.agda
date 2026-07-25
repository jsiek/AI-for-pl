module proof.Core.Administration.NuImprecisionAdministrationMeasureProof where

-- File Charter:
--   * Proves the natural-number equalities for the side-neutral
--     administration measure.
--   * Exposes strictly oriented rank-decrease equations for pending sequence,
--     inert absorption, instantiation, and target `ν` administration.
--   * Combines the `Λ`-bullet and inert-head equations into the exact ranked
--     continuation step used after direct paired-lambda target allocation.
--   * Proves that shifting every pending coercion through a right allocation
--     preserves the target-administration rank.
--   * Proves that removing any pending-list head strictly decreases the rank.
--   * Proves strict rank growth when an inert cast is absorbed into a value.
--   * Depends only on coercion sizes, target measure definitions, and
--     standard-library natural-number arithmetic.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; length; map)
open import Data.Nat using (s≤s; suc; zero; _+_; _*_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Coercions as C
open import Coercions using
  (Coercion; Inert; _︔_; `∀; gen; inst; renameᶜ; sizeᶜ;
   sizeᶜ-renameᶜ; sizeᶜ-⇑ᶜ; ⇑ᶜ)
open import NuTerms using (Value; ƛ_; Λ_; $; _⟨_⟩)
open import proof.Core.Administration.NuImprecisionAdministrationMeasureDef using
  ( InertValueAdministrationIncreaseᵀ
  ; LambdaAllocationContinuationRankDecreaseᵀ
  ; LambdaShiftedAllocationContinuationRankDecreaseᵀ
  ; PendingAdministrationTailDecreaseᵀ
  ; PendingAdministrationShiftMapRankInvariantᵀ
  ; castAdministrationWeight; valueAdministrationWeight
  ; pendingCastAdministrationWeight; pendingAdministrationRank
  ; nuAdministrationRank
  )
open import proof.Core.Properties.NuTermProperties using (renameᵗᵐ-preserves-Value)
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


private
  pending-administration-cons-rank :
    ∀ {V} (vV : Value V) c cs →
    pendingAdministrationRank vV (c ∷ cs) ≡
      suc
        (pendingAdministrationRank vV cs +
          2 * castAdministrationWeight c)
  pending-administration-cons-rank vV c cs =
    solve 4
      (λ w q p l →
        (con 2 :* (w :+ (q :+ p))) :+ (con 1 :+ l)
        :=ᵉ
        con 1 :+
          (((con 2 :* (w :+ p)) :+ l) :+
            (con 2 :* q)))
      refl
      (valueAdministrationWeight vV)
      (castAdministrationWeight c)
      (pendingCastAdministrationWeight cs)
      (length cs)


pending-administration-tail-decrease-proofᵀ :
  PendingAdministrationTailDecreaseᵀ
pending-administration-tail-decrease-proofᵀ vV c cs
    rewrite pending-administration-cons-rank vV c cs =
  s≤s
    (m≤m+n
      (pendingAdministrationRank vV cs)
      (2 * castAdministrationWeight c))


private
  inert-value-administration-rank :
    ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
    pendingAdministrationRank (vV ⟨ inert-c ⟩) cs ≡
      suc
        (pendingAdministrationRank vV cs +
          suc (4 * sizeᶜ c))
  inert-value-administration-rank {c = c} vV inert-c cs =
    solve 4
      (λ w a p l →
        (con 2 :*
          ((w :+ (con 1 :+ (con 2 :* a))) :+ p)) :+ l
        :=ᵉ
        con 1 :+
          (((con 2 :* (w :+ p)) :+ l) :+
            (con 1 :+ (con 4 :* a))))
      refl
      (valueAdministrationWeight vV)
      (sizeᶜ c)
      (pendingCastAdministrationWeight cs)
      (length cs)


inert-value-administration-increase-proofᵀ :
  InertValueAdministrationIncreaseᵀ
inert-value-administration-increase-proofᵀ
    {c = c} vV inert-c cs
    rewrite
      inert-value-administration-rank vV inert-c cs =
  s≤s
    (m≤m+n
      (pendingAdministrationRank vV cs)
      (suc (4 * sizeᶜ c)))


sequence-rank-decreases :
  ∀ {V} (vV : Value V) s t cs →
  pendingAdministrationRank vV ((s ︔ t) ∷ cs) ≡
  suc (pendingAdministrationRank vV (s ∷ t ∷ cs))
sequence-rank-decreases vV s t cs =
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

inert-rank-decreases :
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  pendingAdministrationRank vV (c ∷ cs) ≡
  suc (pendingAdministrationRank (vV ⟨ inert-c ⟩) cs)
inert-rank-decreases {c = c} vV inert-c cs =
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

inst-rank-decreases :
  ∀ {V} (vV : Value V) B c cs →
  pendingAdministrationRank vV (inst B c ∷ cs) ≡
  suc (suc (suc (nuAdministrationRank vV c cs)))
inst-rank-decreases vV B c cs =
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

nu-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  nuAdministrationRank vV c cs ≡
  suc (pendingAdministrationRank vV (c ∷ cs))
nu-rank-decreases vV c cs =
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


Λ-bullet-rank-decreases :
  ∀ {V} (vV : Value V) cs →
  pendingAdministrationRank (Λ vV) cs ≡
  suc (suc (pendingAdministrationRank
    (renameᵗᵐ-preserves-Value (singleRenameᵗ zero) vV) cs))
Λ-bullet-rank-decreases vV cs
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


private
  pending-administration-rank-rename :
    ∀ (ρ : Renameᵗ) {V} (vV : Value V) cs →
    pendingAdministrationRank
      (renameᵗᵐ-preserves-Value ρ vV) cs ≡
      pendingAdministrationRank vV cs
  pending-administration-rank-rename ρ vV cs
      rewrite value-administration-weight-rename ρ vV =
    refl


lambda-allocation-continuation-rank-decrease-proofᵀ :
  LambdaAllocationContinuationRankDecreaseᵀ
lambda-allocation-continuation-rank-decrease-proofᵀ
    {c = c} vV inert-c cs =
  trans
    (Λ-bullet-rank-decreases vV (c ∷ cs))
    (cong suc
      (cong suc
        (trans
          (pending-administration-rank-rename
            (singleRenameᵗ zero) vV (c ∷ cs))
          (inert-rank-decreases vV inert-c cs))))


private
  pending-cast-administration-weight-shift-map :
    ∀ cs →
    pendingCastAdministrationWeight (map ⇑ᶜ cs) ≡
      pendingCastAdministrationWeight cs
  pending-cast-administration-weight-shift-map [] = refl
  pending-cast-administration-weight-shift-map (c ∷ cs)
      rewrite sizeᶜ-⇑ᶜ c
            | pending-cast-administration-weight-shift-map cs =
    refl

  length-shift-map :
    ∀ cs → length (map ⇑ᶜ cs) ≡ length cs
  length-shift-map [] = refl
  length-shift-map (c ∷ cs) rewrite length-shift-map cs = refl


pending-administration-shift-map-rank-invariant-proofᵀ :
  PendingAdministrationShiftMapRankInvariantᵀ
pending-administration-shift-map-rank-invariant-proofᵀ vV cs
    rewrite pending-cast-administration-weight-shift-map cs
          | length-shift-map cs =
  refl


pending-administration-shifted-tail-rank-invariant :
  ∀ {V} (vV : Value V) c cs →
  pendingAdministrationRank
    (renameᵗᵐ-preserves-Value suc vV) (c ∷ map ⇑ᶜ cs) ≡
    pendingAdministrationRank vV (c ∷ cs)
pending-administration-shifted-tail-rank-invariant vV c cs
    rewrite value-administration-weight-rename suc vV
          | pending-cast-administration-weight-shift-map cs
          | length-shift-map cs =
  refl


lambda-shifted-allocation-continuation-rank-decrease-proofᵀ :
  LambdaShiftedAllocationContinuationRankDecreaseᵀ
lambda-shifted-allocation-continuation-rank-decrease-proofᵀ
    vV inert-c cs =
  trans
    (lambda-allocation-continuation-rank-decrease-proofᵀ
      vV inert-c cs)
    (cong suc
      (cong suc
        (cong suc
          (sym
            (pending-administration-shift-map-rank-invariant-proofᵀ
              (vV ⟨ inert-c ⟩) cs)))))


all-bullet-rank-decreases :
  ∀ {V} (vV : Value V) c cs →
  pendingAdministrationRank (vV ⟨ C.`∀ c ⟩) cs ≡
  suc (suc (suc (pendingAdministrationRank vV
    (renameᶜ (singleRenameᵗ zero) c ∷ cs))))
all-bullet-rank-decreases vV c cs
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


gen-bullet-rank-decreases :
  ∀ {V A} (vV : Value V) c cs →
  pendingAdministrationRank (vV ⟨ C.gen A c ⟩) cs ≡
  suc (suc (suc (pendingAdministrationRank vV
    (renameᶜ (singleRenameᵗ zero) c ∷ cs))))
gen-bullet-rank-decreases {A = A} vV c cs
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

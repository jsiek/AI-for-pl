module SealStarOpenVarTagShapeProbe where

-- Probe for the T14/D15 source-only `seal X ★` open rule.  The world below
-- has no target occupant at source `X`, while target `Y` is a visible
-- top-level variable tag at a different center.  The checked result is that
-- the `★⊑★` premise needed by `conceal⊑²-seal-star-open` cannot be built for
-- this unrelated target tag.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; id; _!)
open import Conversion using (seal)
open import Imprecision
open import CastTerms using (Term; Value; $; _⟨_⟩; _↓_; _《_》; inj)
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   TagRebaseAtᴸ; CtxImp; sourceStoreʷ)

private
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ★

  target-store : TyStore 1
  target-store = store-bind store-empty (‵ `ℕ)

  source-X∋ : source-store ∋ X ⦂ ★
  source-X∋ = Z∋ refl

  target-Y∋ : target-store ∋ Y ⦂ ‵ `ℕ
  target-Y∋ = Z∋ refl

  source-η : 1 ↪ᵗ 2
  source-η = keep empty

  target-η : 1 ↪ᵗ 2
  target-η = skip (keep empty)

  imp-env : ImpEnv 2
  imp-env Fin.zero = X⊑★
  imp-env (Fin.suc Fin.zero) = X⊑★

  W : World 1 1 2
  W = world source-η target-η imp-env source-store target-store

  source-env-tag : Env∼ 1
  source-env-tag _ = X∼★

  target-env-tag : Env∼ 1
  target-env-tag _ = X∼★

  ℕ!ˢ : source-env-tag ⊢ (‵ `ℕ) ∼ ★
  ℕ!ˢ = id (‵ `ℕ) !

  Y! : target-env-tag ⊢ ＇ Y ∼ ★
  Y! = id (＇ Y) !

  source-dyn-nat : Term 1
  source-dyn-nat = $ (κℕ 0) ⟨ ℕ!ˢ ⟩

  target-Y-sealed : Term 1
  target-Y-sealed = $ (κℕ 0) ↓ seal Y (‵ `ℕ)

  target-Y-tagged : Term 1
  target-Y-tagged = target-Y-sealed ⟨ Y! ⟩

  source-open-term : Term 1
  source-open-term = source-dyn-nat ↓ seal X ★

  source-dyn-nat-value : Value source-dyn-nat
  source-dyn-nat-value = $ (κℕ 0) 《 inj 》

  target-Y-sealed-value : Value target-Y-sealed
  target-Y-sealed-value = $ (κℕ 0) ↓ CastTerms.seal

  target-Y-tagged-value : Value target-Y-tagged
  target-Y-tagged-value = target-Y-sealed-value 《 inj 》

  source-X-seal-typed : source-store Conv.⊢↓[ just X ] seal X ★
  source-X-seal-typed = Conv.⊢↓-sealˣ source-X∋

  no-target-at-X : CTI2.NoTargetOccupantAtSource W X
  no-target-at-X (Fin.zero , ())

  not-center-aligned-X-Y : CTI2.CenterAligned W X Y → ⊥
  not-center-aligned-X-Y ()

  no-target-rebase : TagRebaseAtᴸ W W (just X) nothing
  no-target-rebase =
    CTI2.tag-rebase-onlyᴸ refl (λ { Fin.zero () }) ★⊑★

  mono-refl : CTI2.ImpEnvMono W W
  mono-refl Z eq = eq

  qX★ : ＇ X ⊑ᵂ⟨ W ⟩ ★
  qX★ = X⊑★ refl

  ℕ-not-target-Y : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ ＇ Y → ⊥
  ℕ-not-target-Y ()

  ★-not-target-Y : ★ ⊑ᵂ⟨ W ⟩ ＇ Y → ⊥
  ★-not-target-Y ()

  source-nat-target-Y-tagged-empty :
    W ∣ [] ⊢² $ (κℕ 0) ⊑ target-Y-tagged ∶ ι⊑★ {ι = `ℕ}
    → ⊥
  source-nat-target-Y-tagged-empty
      (CTI2.⊑cast² {p = p} _ _ _) =
    ℕ-not-target-Y p

  shape-free-open-premise-empty :
    W ∣ [] ⊢² source-dyn-nat ⊑ target-Y-tagged ∶ ★⊑★
    → ⊥
  shape-free-open-premise-empty
      (CTI2.cast⊑cast² {p = p} _ _ _ _) =
    ℕ-not-target-Y p
  shape-free-open-premise-empty
      (CTI2.cast⊑² {p = p} _ D _)
      with p
  shape-free-open-premise-empty
      (CTI2.cast⊑² {p = p} _ D _)
      | ι⊑★ {ι = `ℕ} =
    source-nat-target-Y-tagged-empty D
  shape-free-open-premise-empty
      (CTI2.⊑cast² {p = p} _ D _)
      with p
  shape-free-open-premise-empty
      (CTI2.⊑cast² {p = p} _ D _)
      | ()

ShapeFreeVarTagProbeVerdict : Set
ShapeFreeVarTagProbeVerdict =
  W ∣ [] ⊢² source-dyn-nat ⊑ target-Y-tagged ∶ ★⊑★ → ⊥

shape-free-var-tag-probe-verdict : ShapeFreeVarTagProbeVerdict
shape-free-var-tag-probe-verdict = shape-free-open-premise-empty

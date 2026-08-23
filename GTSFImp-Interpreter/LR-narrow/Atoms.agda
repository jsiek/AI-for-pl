module LR-narrow.Atoms where

-- File Charter:
--   * Defines semantic slots indexed by their center-variable mode.
--   * Separates occupied paired slots from unoccupied dynamic slots;
--     a paired slot may remain usable after its center mark decays to X⊑★.
--   * Records endpoint non-occupancy on one-sided slots.  A target-only slot
--     is semantically inert because imprecision has no ★⊑X clause.
--   * Reindexes atoms through paired and either-sided fresh store bindings.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

open import Types
open import TyStore
open import CastTerms
open import Consistency using (toRenameᵗ; wk↪ᵗ)
import Imprecision as I
open import proof.TypeInTermSubst
  using (renameᵗᵐ-preserves-Value; typing-shiftᵗ-bind)
open import proof.ImprecisionConsistency using (fin-suc-injective)
open import LR-narrow.WorldCore

StepIndexedRelation : TyCtx → TyCtx → Set₁
StepIndexedRelation Δᴾ Δᴵ = ℕ → Term Δᴵ → Term Δᴾ → Set

DownwardClosed : ∀ {Δᴾ Δᴵ} → StepIndexedRelation Δᴾ Δᴵ → Set
DownwardClosed R = ∀ {k Vᴵ Vᴾ}
  → R (suc k) Vᴵ Vᴾ
  → R k Vᴵ Vᴾ

record SemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set₁ where
  constructor semantic-atom
  field
    preciseVariable : TyVar Δᴾ
    impreciseVariable : TyVar Δᴵ
    preciseAligned :
      toRenameᵗ (preciseEmbedding W) preciseVariable ≡ Z
    impreciseAligned :
      toRenameᵗ (impreciseEmbedding W) impreciseVariable ≡ Z
    relation : StepIndexedRelation Δᴾ Δᴵ
    relation-downward : DownwardClosed relation
    relation-valid : ∀ {k Vᴵ Vᴾ}
      → relation k Vᴵ Vᴾ
      → (Value Vᴵ ×
          ⟨ Δᴵ , impreciseStore W , [] ⟩
            ⊢ Vᴵ ⦂ ＇ impreciseVariable)
        × (Value Vᴾ ×
          ⟨ Δᴾ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ ＇ preciseVariable)

open SemanticAtom public

record DynamicSemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set₁ where
  constructor dynamic-semantic-atom
  field
    dynamicPreciseVariable : TyVar Δᴾ
    dynamicPreciseAligned :
      toRenameᵗ (preciseEmbedding W) dynamicPreciseVariable ≡ Z
    dynamicNoTargetOccupant :
      (Σ[ Y ∈ TyVar Δᴵ ]
        toRenameᵗ (impreciseEmbedding W) Y ≡ Z) → ⊥
    dynamicRelation : StepIndexedRelation Δᴾ Δᴵ
    dynamicRelation-downward : DownwardClosed dynamicRelation
    dynamicRelation-valid : ∀ {k Vᴵ Vᴾ}
      → dynamicRelation k Vᴵ Vᴾ
      → (Value Vᴵ ×
          ⟨ Δᴵ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ ★)
        × (Value Vᴾ ×
          ⟨ Δᴾ , preciseStore W , [] ⟩
            ⊢ Vᴾ ⦂ ＇ dynamicPreciseVariable)

open DynamicSemanticAtom public

record TargetSemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set where
  constructor target-semantic-atom
  field
    targetImpreciseVariable : TyVar Δᴵ
    targetImpreciseAligned :
      toRenameᵗ (impreciseEmbedding W) targetImpreciseVariable ≡ Z
    targetNoPreciseOccupant :
      (Σ[ X ∈ TyVar Δᴾ ]
        toRenameᵗ (preciseEmbedding W) X ≡ Z) → ⊥

open TargetSemanticAtom public

data SemanticEntry {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
    (Z : TyVar Δᶜ) : I.VarImp → Set₁ where
  paired-entry : ∀ {mode}
    → SemanticAtom W Z
    → SemanticEntry W Z mode
  dynamic-entry : DynamicSemanticAtom W Z → SemanticEntry W Z I.X⊑★
  target-entry : TargetSemanticAtom W Z → SemanticEntry W Z I.X⊑★

record AtomHolds {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z} (a : SemanticAtom W Z) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor atom-holds
  field
    relation-holds : relation a k Vᴵ Vᴾ

open AtomHolds public

PairedAtomHolds : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
  → SemanticEntry W Z mode
  → ℕ → Term Δᴵ → Term Δᴾ → Set
PairedAtomHolds (paired-entry a) k Vᴵ Vᴾ = AtomHolds a k Vᴵ Vᴾ
PairedAtomHolds (dynamic-entry a) k Vᴵ Vᴾ = ⊥
PairedAtomHolds (target-entry a) k Vᴵ Vᴾ = ⊥

DynamicAtomHolds : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
  → (entry : SemanticEntry W Z mode)
  → mode ≡ I.X⊑★
  → ℕ → Term Δᴵ → Term Δᴾ → Set
DynamicAtomHolds (paired-entry a) eq k Vᴵ Vᴾ = ⊥
DynamicAtomHolds (dynamic-entry a) refl k Vᴵ Vᴾ =
  dynamicRelation a k Vᴵ Vᴾ
DynamicAtomHolds (target-entry a) refl k Vᴵ Vᴾ = ⊥

paired-atom-downward : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode)
  → PairedAtomHolds entry (suc k) Vᴵ Vᴾ
  → PairedAtomHolds entry k Vᴵ Vᴾ
paired-atom-downward (paired-entry a) (atom-holds holds) =
  atom-holds (relation-downward a holds)
paired-atom-downward (dynamic-entry a) ()
paired-atom-downward (target-entry a) ()

dynamic-atom-downward : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds entry eq (suc k) Vᴵ Vᴾ
  → DynamicAtomHolds entry eq k Vᴵ Vᴾ
dynamic-atom-downward (paired-entry a) eq ()
dynamic-atom-downward (dynamic-entry a) refl related =
  dynamicRelation-downward a related
dynamic-atom-downward (target-entry a) refl ()

paired-atom-evidence : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode)
  → PairedAtomHolds entry k Vᴵ Vᴾ
  → Σ[ Xᴾ ∈ TyVar Δᴾ ] Σ[ Xᴵ ∈ TyVar Δᴵ ]
      (toRenameᵗ (preciseEmbedding W) Xᴾ ≡ Z)
      × (toRenameᵗ (impreciseEmbedding W) Xᴵ ≡ Z)
      × (Value Vᴵ ×
          ⟨ Δᴵ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ ＇ Xᴵ)
      × (Value Vᴾ ×
          ⟨ Δᴾ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ ＇ Xᴾ)
paired-atom-evidence (paired-entry a) (atom-holds holds) =
  preciseVariable a , impreciseVariable a , preciseAligned a ,
  impreciseAligned a , relation-valid a holds
paired-atom-evidence (dynamic-entry a) ()
paired-atom-evidence (target-entry a) ()

dynamic-atom-evidence : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds entry eq k Vᴵ Vᴾ
  → Σ[ Xᴾ ∈ TyVar Δᴾ ]
      (toRenameᵗ (preciseEmbedding W) Xᴾ ≡ Z)
      × (Value Vᴵ ×
          ⟨ Δᴵ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ ★)
      × (Value Vᴾ ×
          ⟨ Δᴾ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ ＇ Xᴾ)
dynamic-atom-evidence (paired-entry a) eq ()
dynamic-atom-evidence (dynamic-entry a) refl related =
  dynamicPreciseVariable a , dynamicPreciseAligned a ,
  dynamicRelation-valid a related
dynamic-atom-evidence (target-entry a) refl ()

dynamic-atom-no-target : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds entry eq k Vᴵ Vᴾ
  → (Σ[ Y ∈ TyVar Δᴵ ]
      toRenameᵗ (impreciseEmbedding W) Y ≡ Z) → ⊥
dynamic-atom-no-target (paired-entry a) eq ()
dynamic-atom-no-target (dynamic-entry a) refl related =
  dynamicNoTargetOccupant a
dynamic-atom-no-target (target-entry a) refl ()

data LiftedRelation {Δᴾ Δᴵ} (R : StepIndexedRelation Δᴾ Δᴵ) :
    StepIndexedRelation (suc Δᴾ) (suc Δᴵ) where
  lift-related : ∀ {k Vᴵ Vᴾ}
    → R k Vᴵ Vᴾ
    → LiftedRelation R k (⇑ᵗᵐ Vᴵ) (⇑ᵗᵐ Vᴾ)

data PreciseLiftedRelation {Δᴾ Δᴵ}
    (R : StepIndexedRelation Δᴾ Δᴵ) :
    StepIndexedRelation (suc Δᴾ) Δᴵ where
  precise-lift-related : ∀ {k Vᴵ Vᴾ}
    → R k Vᴵ Vᴾ
    → PreciseLiftedRelation R k Vᴵ (⇑ᵗᵐ Vᴾ)

data ImpreciseLiftedRelation {Δᴾ Δᴵ}
    (R : StepIndexedRelation Δᴾ Δᴵ) :
    StepIndexedRelation Δᴾ (suc Δᴵ) where
  imprecise-lift-related : ∀ {k Vᴵ Vᴾ}
    → R k Vᴵ Vᴾ
    → ImpreciseLiftedRelation R k (⇑ᵗᵐ Vᴵ) Vᴾ

lifted-downward : ∀ {Δᴾ Δᴵ} {R : StepIndexedRelation Δᴾ Δᴵ}
  → DownwardClosed R
  → DownwardClosed (LiftedRelation R)
lifted-downward down (lift-related related) =
  lift-related (down related)

precise-lifted-downward : ∀ {Δᴾ Δᴵ}
    {R : StepIndexedRelation Δᴾ Δᴵ}
  → DownwardClosed R
  → DownwardClosed (PreciseLiftedRelation R)
precise-lifted-downward down (precise-lift-related related) =
  precise-lift-related (down related)

imprecise-lifted-downward : ∀ {Δᴾ Δᴵ}
    {R : StepIndexedRelation Δᴾ Δᴵ}
  → DownwardClosed R
  → DownwardClosed (ImpreciseLiftedRelation R)
imprecise-lifted-downward down (imprecise-lift-related related) =
  imprecise-lift-related (down related)

weaken-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → SemanticAtom W Z
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-semantic-atom Aᴾ Aᴵ a =
  semantic-atom (Fin.suc (preciseVariable a))
    (Fin.suc (impreciseVariable a))
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (LiftedRelation (relation a))
    (lifted-downward (relation-downward a)) valid
  where
  valid : ∀ {k Vᴵ Vᴾ}
    → LiftedRelation (relation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , store-bind _ Aᴵ , [] ⟩ ⊢ Vᴵ ⦂ ＇ _)
      × (Value Vᴾ ×
        ⟨ _ , store-bind _ Aᴾ , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = relation-valid a related
    in (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴵ ,
        typing-shiftᵗ-bind Vᴵ⊢) ,
       (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴾ ,
        typing-shiftᵗ-bind Vᴾ⊢)

weaken-semantic-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → SemanticAtom W Z
  → SemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z)
weaken-semantic-atom-precise {W = W} Aᴾ a =
  semantic-atom (Fin.suc (preciseVariable a)) (impreciseVariable a)
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (PreciseLiftedRelation (relation a))
    (precise-lifted-downward (relation-downward a)) valid
  where
  valid : ∀ {k Vᴵ Vᴾ}
    → PreciseLiftedRelation (relation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ ＇ _)
      × (Value Vᴾ ×
        ⟨ _ , store-bind _ Aᴾ , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (precise-lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = relation-valid a related
    in (vVᴵ , Vᴵ⊢) ,
       (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴾ ,
        typing-shiftᵗ-bind Vᴾ⊢)

weaken-semantic-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → SemanticAtom W Z
  → SemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z)
weaken-semantic-atom-imprecise {W = W} Aᴵ a =
  semantic-atom (preciseVariable a) (Fin.suc (impreciseVariable a))
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (ImpreciseLiftedRelation (relation a))
    (imprecise-lifted-downward (relation-downward a)) valid
  where
  valid : ∀ {k Vᴵ Vᴾ}
    → ImpreciseLiftedRelation (relation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , store-bind _ Aᴵ , [] ⟩ ⊢ Vᴵ ⦂ ＇ _)
      × (Value Vᴾ ×
        ⟨ _ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (imprecise-lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = relation-valid a related
    in (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴵ ,
        typing-shiftᵗ-bind Vᴵ⊢) ,
       (vVᴾ , Vᴾ⊢)

weaken-dynamic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-dynamic-atom {W = W} {Z = Z} Aᴾ Aᴵ a =
  dynamic-semantic-atom (Fin.suc (dynamicPreciseVariable a))
    (cong Fin.suc (dynamicPreciseAligned a))
    no-target
    (LiftedRelation (dynamicRelation a))
    (lifted-downward (dynamicRelation-downward a)) valid
  where
  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (pairedBindCore W Aᴾ Aᴵ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Fin.zero , ())
  no-target (Fin.suc Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

  valid : ∀ {k Vᴵ Vᴾ}
    → LiftedRelation (dynamicRelation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , store-bind _ Aᴵ , [] ⟩ ⊢ Vᴵ ⦂ ★)
      × (Value Vᴾ ×
        ⟨ _ , store-bind _ Aᴾ , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = dynamicRelation-valid a related
    in (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴵ ,
        typing-shiftᵗ-bind Vᴵ⊢) ,
       (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴾ ,
        typing-shiftᵗ-bind Vᴾ⊢)

weaken-dynamic-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z)
weaken-dynamic-atom-precise {W = W} {Z = Z} Aᴾ a =
  dynamic-semantic-atom (Fin.suc (dynamicPreciseVariable a))
    (cong Fin.suc (dynamicPreciseAligned a))
    no-target
    (PreciseLiftedRelation (dynamicRelation a))
    (precise-lifted-downward (dynamicRelation-downward a)) valid
  where
  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (preciseBindCore W Aᴾ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

  valid : ∀ {k Vᴵ Vᴾ}
    → PreciseLiftedRelation (dynamicRelation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ ★)
      × (Value Vᴾ ×
        ⟨ _ , store-bind _ Aᴾ , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (precise-lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = dynamicRelation-valid a related
    in (vVᴵ , Vᴵ⊢) ,
       (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴾ ,
        typing-shiftᵗ-bind Vᴾ⊢)

weaken-dynamic-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z)
weaken-dynamic-atom-imprecise {W = W} {Z = Z} Aᴵ a =
  dynamic-semantic-atom (dynamicPreciseVariable a)
    (cong Fin.suc (dynamicPreciseAligned a)) no-target
    (ImpreciseLiftedRelation (dynamicRelation a))
    (imprecise-lifted-downward (dynamicRelation-downward a)) valid
  where
  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (impreciseBindCore W Aᴵ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Fin.zero , ())
  no-target (Fin.suc Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

  valid : ∀ {k Vᴵ Vᴾ}
    → ImpreciseLiftedRelation (dynamicRelation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , store-bind _ Aᴵ , [] ⟩ ⊢ Vᴵ ⦂ ★)
      × (Value Vᴾ ×
        ⟨ _ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (imprecise-lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = dynamicRelation-valid a related
    in (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴵ ,
        typing-shiftᵗ-bind Vᴵ⊢) ,
       (vVᴾ , Vᴾ⊢)

weaken-target-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-target-atom {W = W} {Z = Z} Aᴾ Aᴵ a =
  target-semantic-atom (Fin.suc (targetImpreciseVariable a))
    (cong Fin.suc (targetImpreciseAligned a)) no-precise
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (pairedBindCore W Aᴾ Aᴵ)) X ≡ Fin.suc Z) → ⊥
  no-precise (Fin.zero , ())
  no-precise (Fin.suc X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-target-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z)
weaken-target-atom-precise {W = W} {Z = Z} Aᴾ a =
  target-semantic-atom (targetImpreciseVariable a)
    (cong Fin.suc (targetImpreciseAligned a)) no-precise
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (preciseBindCore W Aᴾ)) X ≡ Fin.suc Z) → ⊥
  no-precise (Fin.zero , ())
  no-precise (Fin.suc X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-target-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z)
weaken-target-atom-imprecise {W = W} {Z = Z} Aᴵ a =
  target-semantic-atom (Fin.suc (targetImpreciseVariable a))
    (cong Fin.suc (targetImpreciseAligned a)) no-precise
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (impreciseBindCore W Aᴵ)) X ≡ Fin.suc Z) → ⊥
  no-precise (X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-entry : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → SemanticEntry W Z mode
  → SemanticEntry (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z) mode
weaken-entry Aᴾ Aᴵ (paired-entry a) =
  paired-entry (weaken-semantic-atom Aᴾ Aᴵ a)
weaken-entry Aᴾ Aᴵ (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom Aᴾ Aᴵ a)
weaken-entry Aᴾ Aᴵ (target-entry a) =
  target-entry (weaken-target-atom Aᴾ Aᴵ a)

weaken-entry-precise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → SemanticEntry W Z mode
  → SemanticEntry (preciseBindCore W Aᴾ) (Fin.suc Z) mode
weaken-entry-precise Aᴾ (paired-entry a) =
  paired-entry (weaken-semantic-atom-precise Aᴾ a)
weaken-entry-precise Aᴾ (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom-precise Aᴾ a)
weaken-entry-precise Aᴾ (target-entry a) =
  target-entry (weaken-target-atom-precise Aᴾ a)

weaken-entry-imprecise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → SemanticEntry W Z mode
  → SemanticEntry (impreciseBindCore W Aᴵ) (Fin.suc Z) mode
weaken-entry-imprecise Aᴵ (paired-entry a) =
  paired-entry (weaken-semantic-atom-imprecise Aᴵ a)
weaken-entry-imprecise Aᴵ (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom-imprecise Aᴵ a)
weaken-entry-imprecise Aᴵ (target-entry a) =
  target-entry (weaken-target-atom-imprecise Aᴵ a)

paired-holds-weaken : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
    (entry : SemanticEntry W Z mode)
  → PairedAtomHolds entry k Vᴵ Vᴾ
  → PairedAtomHolds (weaken-entry Aᴾ Aᴵ entry) k
      (⇑ᵗᵐ Vᴵ) (⇑ᵗᵐ Vᴾ)
paired-holds-weaken Aᴾ Aᴵ (paired-entry a) (atom-holds holds) =
  atom-holds (lift-related holds)
paired-holds-weaken Aᴾ Aᴵ (dynamic-entry a) ()
paired-holds-weaken Aᴾ Aᴵ (target-entry a) ()

paired-holds-weaken-precise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (Aᴾ : Ty Δᴾ) (entry : SemanticEntry W Z mode)
  → PairedAtomHolds entry k Vᴵ Vᴾ
  → PairedAtomHolds (weaken-entry-precise Aᴾ entry) k
      Vᴵ (⇑ᵗᵐ Vᴾ)
paired-holds-weaken-precise Aᴾ (paired-entry a) (atom-holds holds) =
  atom-holds (precise-lift-related holds)
paired-holds-weaken-precise Aᴾ (dynamic-entry a) ()
paired-holds-weaken-precise Aᴾ (target-entry a) ()

paired-holds-weaken-imprecise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (Aᴵ : Ty Δᴵ) (entry : SemanticEntry W Z mode)
  → PairedAtomHolds entry k Vᴵ Vᴾ
  → PairedAtomHolds (weaken-entry-imprecise Aᴵ entry) k
      (⇑ᵗᵐ Vᴵ) Vᴾ
paired-holds-weaken-imprecise Aᴵ (paired-entry a) (atom-holds holds) =
  atom-holds (imprecise-lift-related holds)
paired-holds-weaken-imprecise Aᴵ (dynamic-entry a) ()
paired-holds-weaken-imprecise Aᴵ (target-entry a) ()

dynamic-holds-weaken : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds entry eq k Vᴵ Vᴾ
  → DynamicAtomHolds (weaken-entry Aᴾ Aᴵ entry) eq k
      (⇑ᵗᵐ Vᴵ) (⇑ᵗᵐ Vᴾ)
dynamic-holds-weaken Aᴾ Aᴵ (paired-entry a) eq ()
dynamic-holds-weaken Aᴾ Aᴵ (dynamic-entry a) refl related =
  lift-related related
dynamic-holds-weaken Aᴾ Aᴵ (target-entry a) refl ()

dynamic-holds-weaken-precise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (Aᴾ : Ty Δᴾ) (entry : SemanticEntry W Z mode)
    (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds entry eq k Vᴵ Vᴾ
  → DynamicAtomHolds (weaken-entry-precise Aᴾ entry) eq k
      Vᴵ (⇑ᵗᵐ Vᴾ)
dynamic-holds-weaken-precise Aᴾ (paired-entry a) eq ()
dynamic-holds-weaken-precise Aᴾ (dynamic-entry a) refl related =
  precise-lift-related related
dynamic-holds-weaken-precise Aᴾ (target-entry a) refl ()

dynamic-holds-weaken-imprecise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z k Vᴵ Vᴾ}
    (Aᴵ : Ty Δᴵ) (entry : SemanticEntry W Z mode)
    (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds entry eq k Vᴵ Vᴾ
  → DynamicAtomHolds (weaken-entry-imprecise Aᴵ entry) eq k
      (⇑ᵗᵐ Vᴵ) Vᴾ
dynamic-holds-weaken-imprecise Aᴵ (paired-entry a) eq ()
dynamic-holds-weaken-imprecise Aᴵ (dynamic-entry a) refl related =
  imprecise-lift-related related
dynamic-holds-weaken-imprecise Aᴵ (target-entry a) refl ()

fresh-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
    (R : StepIndexedRelation (suc Δᴾ) (suc Δᴵ))
  → DownwardClosed R
  → (∀ {k Vᴵ Vᴾ}
      → R k Vᴵ Vᴾ
      → (Value Vᴵ ×
          ⟨ suc Δᴵ , store-bind (impreciseStore W) Aᴵ , [] ⟩
            ⊢ Vᴵ ⦂ ＇ Fin.zero)
        × (Value Vᴾ ×
          ⟨ suc Δᴾ , store-bind (preciseStore W) Aᴾ , [] ⟩
            ⊢ Vᴾ ⦂ ＇ Fin.zero))
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) Fin.zero
fresh-semantic-atom Aᴾ Aᴵ R down valid =
  semantic-atom Fin.zero Fin.zero refl refl R down valid

fresh-dynamic-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} (Aᴾ : Ty Δᴾ)
    (R : StepIndexedRelation (suc Δᴾ) Δᴵ)
  → DownwardClosed R
  → (∀ {k Vᴵ Vᴾ}
      → R k Vᴵ Vᴾ
      → (Value Vᴵ ×
          ⟨ Δᴵ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ ★)
        × (Value Vᴾ ×
          ⟨ suc Δᴾ , store-bind (preciseStore W) Aᴾ , [] ⟩
            ⊢ Vᴾ ⦂ ＇ Fin.zero))
  → DynamicSemanticAtom (preciseBindCore W Aᴾ) Fin.zero
fresh-dynamic-semantic-atom Aᴾ R down valid =
  dynamic-semantic-atom Fin.zero refl
    (λ { (Y , ()) }) R down valid

fresh-target-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} (Aᴵ : Ty Δᴵ)
  → TargetSemanticAtom (impreciseBindCore W Aᴵ) Fin.zero
fresh-target-semantic-atom Aᴵ =
  target-semantic-atom Fin.zero refl (λ { (X , ()) })

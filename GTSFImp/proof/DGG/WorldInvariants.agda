module proof.DGG.WorldInvariants where

-- File Charter:
--   * Defines the D16 Stage 1 companion invariants for five-field worlds.
--   * Uses direct store entries and the strict literal-dynamic condition for
--     unmatched targets.
--   * Establishes the companion for the empty initial world and core world
--     builders without changing World or requiring it from consumers.
--   * Derives variable-entry chain coherence from direct representations.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.Parked.ParkedWorldDef as PWD
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TargetExtend as TE
import proof.DGG.WorldDecay as WD
open import proof.ImprecisionConsistency using
  (refl⊑; rename-⊑; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (toRename-id-eq; toRename-keep-eq)


record WorldInvariants {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) : Set where
  constructor world-invariants
  field
    preciseMarksAligned :
      ∀ (Xᴸ : TyVar Δᴸ)
      → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar Δᴿ ]
          toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
            ≡ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ

    representationsImprecise :
      ∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
          ≡ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      → CTI2.impEnvʷ W ⊢
          renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W))
            (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)
          ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W))
            (lookupStore (CTI2.targetStoreʷ W) Xᴿ)

    unmatchedTargetsDynamic :
      ∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
            ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
      → lookupStore (CTI2.targetStoreʷ W) Xᴿ ≡ ★

open WorldInvariants public


CenterAligned : ∀ {Δᴸ Δᴿ Δ}
  → CTI2.World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned W Xᴸ Xᴿ =
  toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ ≡ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ

imprecision-cong : ∀ {Δ} {μ : ImpEnv Δ} {A A′ B B′ : Ty Δ}
  → A ≡ A′
  → B ≡ B′
  → μ ⊢ A ⊑ B
  → μ ⊢ A′ ⊑ B′
imprecision-cong refl refl A⊑B = A⊑B

variableHeadsAlign : ∀ {Δ} {μ : ImpEnv Δ} {X Y : TyVar Δ}
  → μ ⊢ ＇ X ⊑ ＇ Y
  → X ≡ Y
variableHeadsAlign X⊑X = refl

variableEntryChainCoherence : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ Yᴸ : TyVar Δᴸ} {Xᴿ Yᴿ : TyVar Δᴿ}
  → WorldInvariants W
  → CenterAligned W Xᴸ Xᴿ
  → lookupStore (CTI2.sourceStoreʷ W) Xᴸ ≡ ＇ Yᴸ
  → lookupStore (CTI2.targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ
  → CenterAligned W Yᴸ Yᴿ
    × (CTI2.impEnvʷ W ⊢
        renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W))
          (lookupStore (CTI2.sourceStoreʷ W) Yᴸ)
        ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W))
          (lookupStore (CTI2.targetStoreʷ W) Yᴿ))
variableEntryChainCoherence {W = W} {Yᴸ = Yᴸ} {Yᴿ = Yᴿ}
    inv aligned source-entry target-entry =
  heads-aligned , representationsImprecise inv heads-aligned
  where
  heads-aligned : CenterAligned W Yᴸ Yᴿ
  heads-aligned = variableHeadsAlign
    (imprecision-cong
      (cong (renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) source-entry)
      (cong (renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) target-entry)
      (representationsImprecise inv aligned))


emptyStore : (Δ : TyCtx) → TyStore Δ
emptyStore Nat.zero = store-empty
emptyStore (Nat.suc Δ) = store-lift (emptyStore Δ)

initialWorld : ∀ {Δ} → ImpEnv Δ → CTI2.World Δ Δ Δ
initialWorld {Δ} μ =
  CTI2.world id↪ᵗ id↪ᵗ μ (emptyStore Δ) (emptyStore Δ)

initialWorld-invariants : ∀ {Δ} (μ : ImpEnv Δ)
  → WorldInvariants (initialWorld μ)
initialWorld-invariants μ = world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → μ (toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ id↪ᵗ Xᴿ ≡ toRenameᵗ id↪ᵗ Xᴸ
  precise Xᴸ mark = Xᴸ , refl

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ id↪ᵗ Xᴸ ≡ toRenameᵗ id↪ᵗ Xᴿ
    → μ ⊢ renameᵗ (toRenameᵗ id↪ᵗ) (lookupStore (emptyStore _) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ id↪ᵗ) (lookupStore (emptyStore _) Xᴿ)
  reps {Xᴸ = Xᴸ} aligned
      with toRenameᵗ-injective id↪ᵗ aligned
  reps {Xᴸ = Xᴸ} aligned | refl = refl⊑ _

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ id↪ᵗ Xᴸ ≢ toRenameᵗ id↪ᵗ Xᴿ)
    → lookupStore (emptyStore _) Xᴿ ≡ ★
  unmatched Xᴿ no-source = ⊥-elim (no-source Xᴿ refl)

identityWorld-invariants : ∀ {Δ} (μ : ImpEnv Δ) (Σ : TyStore Δ)
  → WorldInvariants (CTI2.world id↪ᵗ id↪ᵗ μ Σ Σ)
identityWorld-invariants μ Σ = world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → μ (toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ id↪ᵗ Xᴿ ≡ toRenameᵗ id↪ᵗ Xᴸ
  precise Xᴸ mark = Xᴸ , refl

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ id↪ᵗ Xᴸ ≡ toRenameᵗ id↪ᵗ Xᴿ
    → μ ⊢ renameᵗ (toRenameᵗ id↪ᵗ) (lookupStore Σ Xᴸ)
        ⊑ renameᵗ (toRenameᵗ id↪ᵗ) (lookupStore Σ Xᴿ)
  reps {Xᴸ = Xᴸ} aligned
      with toRenameᵗ-injective id↪ᵗ aligned
  reps {Xᴸ = Xᴸ} aligned | refl = refl⊑ _

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ id↪ᵗ Xᴸ ≢ toRenameᵗ id↪ᵗ Xᴿ)
    → lookupStore Σ Xᴿ ≡ ★
  unmatched Xᴿ no-source = ⊥-elim (no-source Xᴿ refl)


private
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

  renameᵗ-keep-shift : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  renameᵗ-keep-shift η A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
      (renameᵗ-shift (toRenameᵗ η) A)

  renameᵗ-skip : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (skip η)) A
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  renameᵗ-skip η A =
    trans (renameᵗ-cong A (λ X → refl))
      (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc A))

  lift-old-representation : ∀ {Δ} {μ : ImpEnv Δ} {v}
      {A : Ty Δ} {B : Ty Δ}
    → μ ⊢ A ⊑ B
    → extendᵐ v μ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
  lift-old-representation {v = v} A⊑B =
    rename-⊑ Fin.suc fin-suc-injective
      (λ X eq → eq) A⊑B

  inst-old-representation : ∀ {Δ} {μ : ImpEnv Δ}
      {A : Ty Δ} {B : Ty Δ}
    → μ ⊢ A ⊑ B
    → instᵐ μ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
  inst-old-representation A⊑B =
    rename-⊑ Fin.suc fin-suc-injective
      (λ X eq → eq) A⊑B


liftWorldBoth-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (v : VarImp)
  → WorldInvariants W
  → WorldInvariants (CTI2.liftWorldBoth v W)
liftWorldBoth-invariants {W = W} v inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → extendᵐ v (CTI2.impEnvʷ W)
        (toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
        ≡ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ
    → extendᵐ v (CTI2.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
          (lookupStore (store-lift (CTI2.sourceStoreʷ W)) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (CTI2.ηᴿʷ W)))
          (lookupStore (store-lift (CTI2.targetStoreʷ W)) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned = X⊑X
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (CTI2.ηᴸʷ W)
        (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (CTI2.ηᴿʷ W)
        (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))
      (lift-old-representation (representationsImprecise inv
        (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ)
    → lookupStore (store-lift (CTI2.targetStoreʷ W)) Xᴿ ≡ ★
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source =
    cong ⇑ᵗ (unmatchedTargetsDynamic inv Xᴿ old-no-source)
    where
    old-no-source : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    old-no-source Xᴸ aligned =
      no-source (Fin.suc Xᴸ) (cong Fin.suc aligned)


liftWorldLeft-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (v : VarImp)
  → v ≡ X⊑★
  → WorldInvariants W
  → WorldInvariants (CTI2.liftWorldLeft v W)
liftWorldLeft-invariants {W = W} .X⊑★ refl inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → instᵐ (CTI2.impEnvʷ W)
        (toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (CTI2.ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
        ≡ toRenameᵗ (skip (CTI2.ηᴿʷ W)) Xᴿ
    → instᵐ (CTI2.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
          (lookupStore (store-lift (CTI2.sourceStoreʷ W)) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (CTI2.ηᴿʷ W)))
          (lookupStore (CTI2.targetStoreʷ W) Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (CTI2.ηᴸʷ W)
        (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-skip (CTI2.ηᴿʷ W)
        (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))
      (inst-old-representation (representationsImprecise inv
        (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (skip (CTI2.ηᴿʷ W)) Xᴿ)
    → lookupStore (CTI2.targetStoreʷ W) Xᴿ ≡ ★
  unmatched Xᴿ no-source = unmatchedTargetsDynamic inv Xᴿ old-no-source
    where
    old-no-source : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    old-no-source Xᴸ aligned =
      no-source (Fin.suc Xᴸ) (cong Fin.suc aligned)


leftOnlyWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (v : VarImp) (A : Ty Δᴸ)
  → v ≡ X⊑★
  → WorldInvariants W
  → WorldInvariants (CTI2.leftOnlyWorld v W A)
leftOnlyWorld-invariants {W = W} .X⊑★ A refl inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → instᵐ (CTI2.impEnvʷ W)
        (toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (CTI2.ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
        ≡ toRenameᵗ (skip (CTI2.ηᴿʷ W)) Xᴿ
    → instᵐ (CTI2.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
          (lookupStore (store-bind (CTI2.sourceStoreʷ W) A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (CTI2.ηᴿʷ W)))
          (lookupStore (CTI2.targetStoreʷ W) Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (CTI2.ηᴸʷ W)
        (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-skip (CTI2.ηᴿʷ W)
        (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))
      (inst-old-representation (representationsImprecise inv
        (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (skip (CTI2.ηᴿʷ W)) Xᴿ)
    → lookupStore (CTI2.targetStoreʷ W) Xᴿ ≡ ★
  unmatched Xᴿ no-source = unmatchedTargetsDynamic inv Xᴿ old-no-source
    where
    old-no-source : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    old-no-source Xᴸ aligned =
      no-source (Fin.suc Xᴸ) (cong Fin.suc aligned)


rightOnlyWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (B : Ty Δᴿ)
  → ⇑ᵗ B ≡ ★
  → WorldInvariants W
  → WorldInvariants (CTI2.rightOnlyWorld W B)
rightOnlyWorld-invariants {W = W} B fresh-dynamic inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → instᵐ (CTI2.impEnvʷ W)
        (toRenameᵗ (skip (CTI2.ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (skip (CTI2.ηᴸʷ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAligned inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (CTI2.ηᴸʷ W)) Xᴸ
        ≡ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ
    → instᵐ (CTI2.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (skip (CTI2.ηᴸʷ W)))
          (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (CTI2.ηᴿʷ W)))
          (lookupStore (store-bind (CTI2.targetStoreʷ W) B) Xᴿ)
  reps {Xᴸ} {Fin.zero} ()
  reps {Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (CTI2.ηᴸʷ W)
        (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (CTI2.ηᴿʷ W)
        (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))
      (inst-old-representation (representationsImprecise inv
        (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (skip (CTI2.ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ)
    → lookupStore (store-bind (CTI2.targetStoreʷ W) B) Xᴿ ≡ ★
  unmatched Fin.zero no-source = fresh-dynamic
  unmatched (Fin.suc Xᴿ) no-source =
    cong ⇑ᵗ (unmatchedTargetsDynamic inv Xᴿ old-no-source)
    where
    old-no-source : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    old-no-source Xᴸ aligned = no-source Xᴸ (cong Fin.suc aligned)


bothBindWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (v : VarImp)
    (A : Ty Δᴸ) (B : Ty Δᴿ)
  → A CTI2.⊑ᵂ⟨ W ⟩ B
  → WorldInvariants W
  → WorldInvariants (CTI2.bothBindWorld v W A B)
bothBindWorld-invariants {W = W} v A B A⊑B inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → extendᵐ v (CTI2.impEnvʷ W)
        (toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
        ≡ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ
    → extendᵐ v (CTI2.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
          (lookupStore (store-bind (CTI2.sourceStoreʷ W) A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (CTI2.ηᴿʷ W)))
          (lookupStore (store-bind (CTI2.targetStoreʷ W) B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (CTI2.ηᴸʷ W) A))
      (sym (renameᵗ-keep-shift (CTI2.ηᴿʷ W) B))
      (lift-old-representation A⊑B)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (CTI2.ηᴸʷ W)
        (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (CTI2.ηᴿʷ W)
        (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))
      (lift-old-representation (representationsImprecise inv
        (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (CTI2.ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Xᴿ)
    → lookupStore (store-bind (CTI2.targetStoreʷ W) B) Xᴿ ≡ ★
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source =
    cong ⇑ᵗ (unmatchedTargetsDynamic inv Xᴿ old-no-source)
    where
    old-no-source : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    old-no-source Xᴸ aligned =
      no-source (Fin.suc Xᴸ) (cong Fin.suc aligned)


parked-initial-invariants : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → WorldInvariants (CPI2.initialWorld μ Σ)
parked-initial-invariants {μ = μ} {Σ = Σ} = identityWorld-invariants μ Σ

parked-both-bind-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A CTI2.⊑ᵂ⟨ W ⟩ B
  → WorldInvariants W
  → WorldInvariants (CTI2.bothBindWorld X⊑X W A B)
parked-both-bind-invariants {A = A} {B = B} =
  bothBindWorld-invariants X⊑X A B

parked-left-bind-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {A : Ty Δᴸ}
  → WorldInvariants W
  → WorldInvariants (CTI2.leftOnlyWorld X⊑★ W A)
parked-left-bind-invariants {A = A} =
  leftOnlyWorld-invariants X⊑★ A refl

parked-right-bind-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ⇑ᵗ B ≡ ★
  → WorldInvariants W
  → WorldInvariants (CTI2.rightOnlyWorld W B)
parked-right-bind-invariants {B = B} = rightOnlyWorld-invariants B

parked-structural-right-insert-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → PWD.ParkedWorld W
  → WorldInvariants W
  → WorldInvariants W
parked-structural-right-insert-invariants parked inv = inv


parkedEvolve-end-invariants : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : R.StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : R.StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ′ Δᴿ′ Δ′}
  → PWD.ParkedEvolve χsᴸ χsᴿ W W′
  → WorldInvariants W′
  → WorldInvariants W′
parkedEvolve-end-invariants PWD.evolve-refl inv = inv
parkedEvolve-end-invariants (PWD.evolve-keepᴸ evol) inv = inv
parkedEvolve-end-invariants (PWD.evolve-keepᴿ evol) inv = inv
parkedEvolve-end-invariants (PWD.evolve-both-bind evol) inv = inv
parkedEvolve-end-invariants (PWD.evolve-left-bind evol) inv = inv
parkedEvolve-end-invariants (PWD.evolve-right-bind evol) inv = inv
parkedEvolve-end-invariants
    (PWD.evolve-structural-right-bind ins follows evol) inv = inv


renameWorld-invariants : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} (π : Δ ↪ᵗ Δ′)
  → WorldInvariants W
  → WorldInvariants (CR.renameWorld π W)
renameWorld-invariants {W = W} π inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → CR.renameEnv π (CTI2.impEnvʷ W)
        (toRenameᵗ (π CR.∘↪ CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (π CR.∘↪ CTI2.ηᴿʷ W) Xᴿ
          ≡ toRenameᵗ (π CR.∘↪ CTI2.ηᴸʷ W) Xᴸ
  precise Xᴸ mark with preciseMarksAligned inv Xᴸ old-mark
    where
    old-mark :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑X
    old-mark =
      trans (sym (CR.renameEnv-image π (CTI2.impEnvʷ W)
          (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)))
        (trans (cong (CR.renameEnv π (CTI2.impEnvʷ W))
          (sym (CR.toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ))) mark)
  precise Xᴸ mark | Xᴿ , aligned =
    Xᴿ , trans (CR.toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Xᴿ)
      (trans (cong (toRenameᵗ π) aligned)
        (sym (CR.toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ)))

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (π CR.∘↪ CTI2.ηᴸʷ W) Xᴸ
        ≡ toRenameᵗ (π CR.∘↪ CTI2.ηᴿʷ W) Xᴿ
    → CR.renameEnv π (CTI2.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (π CR.∘↪ CTI2.ηᴸʷ W))
          (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (π CR.∘↪ CTI2.ηᴿʷ W))
          (lookupStore (CTI2.targetStoreʷ W) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned =
    CR.rename-⊑ᵂ {W = W}
      {A = lookupStore (CTI2.sourceStoreʷ W) Xᴸ}
      {B = lookupStore (CTI2.targetStoreʷ W) Xᴿ}
      π (representationsImprecise inv old-aligned)
    where
    old-aligned : CenterAligned W Xᴸ Xᴿ
    old-aligned = toRenameᵗ-injective π
      (trans (sym (CR.toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ))
        (trans aligned
          (CR.toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Xᴿ)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (π CR.∘↪ CTI2.ηᴸʷ W) Xᴸ
          ≢ toRenameᵗ (π CR.∘↪ CTI2.ηᴿʷ W) Xᴿ)
    → lookupStore (CTI2.targetStoreʷ W) Xᴿ ≡ ★
  unmatched Xᴿ no-source = unmatchedTargetsDynamic inv Xᴿ old-no-source
    where
    old-no-source : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    old-no-source Xᴸ aligned = no-source Xᴸ
      (trans (CR.toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ)
        (trans (cong (toRenameᵗ π) aligned)
          (sym (CR.toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Xᴿ))))


decay-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
  → WD.EnvDecay W Wᵈ
  → WorldInvariants W
  → WorldInvariants Wᵈ
decay-invariants
    {W = CTI2.world ηᴸ ηᴿ μ Σᴸ Σᴿ}
    {Wᵈ = CTI2.world .ηᴸ .ηᴿ μᵈ .Σᴸ .Σᴿ}
    (WD.env-decay refl refl refl refl mono) inv =
  world-invariants precise reps (unmatchedTargetsDynamic inv)
  where
  precise : ∀ Xᴸ
    → μᵈ (toRenameᵗ ηᴸ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ ηᴿ Xᴿ ≡ toRenameᵗ ηᴸ Xᴸ
  precise Xᴸ preciseᵈ with μ (toRenameᵗ ηᴸ Xᴸ) in old-mark
  precise Xᴸ preciseᵈ | X⊑X = preciseMarksAligned inv Xᴸ old-mark
  precise Xᴸ preciseᵈ | X⊑★
      with trans (sym (mono (toRenameᵗ ηᴸ Xᴸ) old-mark)) preciseᵈ
  precise Xᴸ preciseᵈ | X⊑★ | ()

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ ηᴸ Xᴸ ≡ toRenameᵗ ηᴿ Xᴿ
    → μᵈ ⊢ renameᵗ (toRenameᵗ ηᴸ) (lookupStore Σᴸ Xᴸ)
        ⊑ renameᵗ (toRenameᵗ ηᴿ) (lookupStore Σᴿ Xᴿ)
  reps aligned = WD.⊑-env-mono mono (representationsImprecise inv aligned)


blendWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W′ Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
  → WorldInvariants W′
  → WorldInvariants (WD.blendWorld W′ Wᵈ)
blendWorld-invariants {W′ = W′} {Wᵈ = Wᵈ} =
  decay-invariants (WD.blend-decay {W′ = W′} {Wᵈ = Wᵈ})

honestify-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → WorldInvariants W
  → WorldInvariants (WD.honestify W)
honestify-invariants {W = W} = decay-invariants (WD.honestify-decay {W = W})

dynWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → WorldInvariants W
  → WorldInvariants (SPT.dynWorld W)
dynWorld-invariants {W = W} = decay-invariants (SPT.dynWorld-decay W)

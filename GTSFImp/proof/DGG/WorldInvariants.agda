module proof.DGG.WorldInvariants where

-- File Charter:
--   * Defines the D16 Stage 1 companion invariants for five-field worlds.
--   * Uses direct store entries and the strict literal-dynamic condition for
--     unmatched targets.
--   * Establishes the companion for the empty initial world and core world
--     builders without changing World or requiring it from consumers.
--   * Derives variable-entry chain coherence from direct representations.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; id↪ᵗ; wk↪ᵗ; toRenameᵗ)
open import Imprecision
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.Examples2 as Ex2
import proof.DGG.Parked.ParkedWorldDef as PWD
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TargetBindLift as TBL
import proof.DGG.TargetExtend as TE
import proof.DGG.WorldDecay as WD
open import proof.ImprecisionConsistency using
  (refl⊑; rename-⊑; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (renameᵗ-wk-eq; toRename-id-eq; toRename-keep-eq; toRename-wk-eq)


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


targetStoreAs-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (Σᴿ : TyStore Δᴿ)
  → WorldInvariants W
  → (∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ ≡ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      → CTI2.impEnvʷ W ⊢
          renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W))
            (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)
          ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W)) (lookupStore Σᴿ Xᴿ))
  → (∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
      → lookupStore Σᴿ Xᴿ ≡ ★)
  → WorldInvariants (TBL.targetStoreAs W Σᴿ)
targetStoreAs-invariants Σᴿ inv reps unmatched =
  world-invariants (preciseMarksAligned inv) reps unmatched


record TargetInsertDirect {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (ins : TE.TargetInsert ρ π W W′) : Set where
  constructor target-insert-direct
  field
    targetLookup-insert : ∀ Xᴿ
      → lookupStore (CTI2.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ)
        ≡ renameᵗ (toRenameᵗ ρ)
            (lookupStore (CTI2.targetStoreʷ W) Xᴿ)

    targetLookup-off : ∀ Xᴿ′
      → CR.preimage? π (toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ′) ≡ nothing
      → lookupStore (CTI2.targetStoreʷ W′) Xᴿ′ ≡ ★

open TargetInsertDirect public


targetInsert-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (ins : TE.TargetInsert ρ π W W′)
  → TargetInsertDirect ins
  → WorldInvariants W
  → WorldInvariants W′
targetInsert-invariants {ρ = ρ} {π = π} {W = W} {W′ = W′} ins direct inv =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → CTI2.impEnvʷ W′ (toRenameᵗ (CTI2.ηᴸʷ W′) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ′ ∈ TyVar _ ]
        toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ′
          ≡ toRenameᵗ (CTI2.ηᴸʷ W′) Xᴸ
  precise Xᴸ mark with preciseMarksAligned inv Xᴸ old-mark
    where
    old-mark :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑X
    old-mark = trans
      (sym (TE.impEnv-insert ins (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)))
      (subst≡ (λ Z → CTI2.impEnvʷ W′ Z ≡ X⊑X)
        (TE.source-insert ins Xᴸ) mark)
  precise Xᴸ mark | Xᴿ , aligned =
    toRenameᵗ ρ Xᴿ , sym (TE.align-insert ins (sym aligned))

  reps : ∀ {Xᴸ Xᴿ′}
    → CTI2.CenterAligned W′ Xᴸ Xᴿ′
    → CTI2.impEnvʷ W′ ⊢
        renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W′))
          (lookupStore (CTI2.sourceStoreʷ W′) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W′))
          (lookupStore (CTI2.targetStoreʷ W′) Xᴿ′)
  reps {Xᴸ} {Xᴿ′} aligned
      with TE.target-source-reflect ins aligned
  reps {Xᴸ} {Xᴿ′} aligned | Xᴿ , refl , old-aligned =
    imprecision-cong source-eq target-eq
      (TE.transport⊑ᵂ ins (representationsImprecise inv old-aligned))
    where
    source-eq :
      renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W′))
          (lookupStore (CTI2.sourceStoreʷ W) Xᴸ)
        ≡ renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W′))
          (lookupStore (CTI2.sourceStoreʷ W′) Xᴸ)
    source-eq = cong (renameᵗ (toRenameᵗ (CTI2.ηᴸʷ W′)))
      (sym (cong (λ Σ → lookupStore Σ Xᴸ) (TE.sourceStore-kept ins)))

    target-eq :
      renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W′))
          (renameᵗ (toRenameᵗ _) (lookupStore (CTI2.targetStoreʷ W) Xᴿ))
        ≡ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W′))
          (lookupStore (CTI2.targetStoreʷ W′) (toRenameᵗ _ Xᴿ))
    target-eq = cong (renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W′)))
      (sym (targetLookup-insert direct Xᴿ))

  unmatched : ∀ Xᴿ′
    → (∀ Xᴸ → CTI2.CenterAligned W′ Xᴸ Xᴿ′ → ⊥)
    → lookupStore (CTI2.targetStoreʷ W′) Xᴿ′ ≡ ★
  unmatched Xᴿ′ no-source
      with CR.preimage? π (toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ′) in pre
  unmatched Xᴿ′ no-source | nothing =
    targetLookup-off direct Xᴿ′ pre
  unmatched Xᴿ′ no-source | just Z
      with TE.target-center-reflect ins (CR.preimage?-sound π pre)
  unmatched Xᴿ′ no-source | just Z
      | Xᴿ , xᴿ′-eq , old-center =
    subst≡ (λ Y → lookupStore (CTI2.targetStoreʷ W′) Y ≡ ★)
      (sym xᴿ′-eq)
      (trans (targetLookup-insert direct Xᴿ)
        (cong (renameᵗ (toRenameᵗ ρ))
          (unmatchedTargetsDynamic inv Xᴿ old-no-source)))
    where
    old-no-source : ∀ Xᴸ → CTI2.CenterAligned W Xᴸ Xᴿ → ⊥
    old-no-source Xᴸ aligned = no-source Xᴸ
      (subst≡ (CTI2.CenterAligned W′ Xᴸ) (sym xᴿ′-eq)
        (TE.align-insert ins aligned))


parked-structural-right-insert-invariants : ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
  → PWD.ParkedWorld W
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → TargetInsertDirect ins
  → CTI2.targetStoreʷ W₁ ≡ R.applyStore (R.bind B) (CTI2.targetStoreʷ W)
  → WorldInvariants W
  → WorldInvariants W₁
parked-structural-right-insert-invariants parked ins direct follows inv =
  targetInsert-invariants ins direct inv


rightBindTargetInsert-direct : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ⇑ᵗ B ≡ ★
  → TargetInsertDirect (TE.rightBindTargetInsert {W = W} {B = B})
rightBindTargetInsert-direct {W = W} {B = B} fresh-dynamic =
  target-insert-direct old-entry fresh-entry
  where
  ins = TE.rightBindTargetInsert {W = W} {B = B}

  old-entry : ∀ Xᴿ
    → lookupStore (CTI2.targetStoreʷ (CTI2.rightOnlyWorld W B))
        (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ renameᵗ (toRenameᵗ wk↪ᵗ)
          (lookupStore (CTI2.targetStoreʷ W) Xᴿ)
  old-entry Xᴿ =
    trans (cong (lookupStore (store-bind (CTI2.targetStoreʷ W) B))
      (toRename-wk-eq Xᴿ))
      (sym (renameᵗ-wk-eq (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))

  fresh-entry : ∀ Xᴿ′
    → CR.preimage? wk↪ᵗ
        (toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Xᴿ′)
        ≡ nothing
    → lookupStore (CTI2.targetStoreʷ (CTI2.rightOnlyWorld W B)) Xᴿ′
        ≡ ★
  fresh-entry Fin.zero off = fresh-dynamic
  fresh-entry (Fin.suc Xᴿ) off = ⊥-elim (CR.just≢nothing impossible)
    where
    center-eq :
      toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) (Fin.suc Xᴿ)
        ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
    center-eq = trans
      (cong (toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)))
        (sym (toRename-wk-eq Xᴿ)))
      (TE.target-insert ins Xᴿ)

    impossible : just (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ) ≡ nothing
    impossible = trans
      (sym (CR.preimage?-image wk↪ᵗ
        (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)))
      (trans (cong (CR.preimage? wk↪ᵗ) (sym center-eq)) off)


liftBothTargetInsert-direct : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′} {v : VarImp}
  → (ins : TE.TargetInsert ρ π W W′)
  → TargetInsertDirect ins
  → TargetInsertDirect (TE.liftBothTargetInsert {v = v} ins)
liftBothTargetInsert-direct {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {v = v} ins direct = target-insert-direct old-entry fresh-entry
  where
  old-entry : ∀ Xᴿ
    → lookupStore
        (CTI2.targetStoreʷ (CTI2.liftWorldBoth v W′))
        (toRenameᵗ (keep ρ) Xᴿ)
      ≡ renameᵗ (toRenameᵗ (keep ρ))
          (lookupStore (CTI2.targetStoreʷ (CTI2.liftWorldBoth v W)) Xᴿ)
  old-entry Fin.zero = refl
  old-entry (Fin.suc Xᴿ) =
    trans (cong ⇑ᵗ (targetLookup-insert direct Xᴿ))
      (sym (renameᵗ-keep-shift ρ
        (lookupStore (CTI2.targetStoreʷ W) Xᴿ)))

  fresh-entry : ∀ Xᴿ′
    → CR.preimage? (keep π)
        (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W′)) Xᴿ′)
        ≡ nothing
    → lookupStore (CTI2.targetStoreʷ (CTI2.liftWorldBoth v W′)) Xᴿ′
        ≡ ★
  fresh-entry Fin.zero ()
  fresh-entry (Fin.suc Xᴿ′) off =
    cong ⇑ᵗ (targetLookup-off direct Xᴿ′
      (CR.sucMaybe-nothing _ off))


liftLeftTargetInsert-direct : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′} {v : VarImp}
  → (ins : TE.TargetInsert ρ π W W′)
  → TargetInsertDirect ins
  → TargetInsertDirect (TE.liftLeftTargetInsert {v = v} ins)
liftLeftTargetInsert-direct {π = π} {W′ = W′} {v = v} ins direct =
  target-insert-direct (targetLookup-insert direct) fresh-entry
  where
  fresh-entry : ∀ Xᴿ′
    → CR.preimage? (keep π)
        (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W′)) Xᴿ′)
        ≡ nothing
    → lookupStore (CTI2.targetStoreʷ (CTI2.liftWorldLeft v W′)) Xᴿ′
        ≡ ★
  fresh-entry Xᴿ′ off =
    targetLookup-off direct Xᴿ′ (CR.sucMaybe-nothing _ off)


smartAliasTargetInsert-direct : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TE.TargetInsert ρ π W W′)
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → TargetInsertDirect ins
  → TargetInsertDirect (TE.smartAliasTargetInsert ins guard)
smartAliasTargetInsert-direct {ρ = ρ} {W = W} {Wᵐ = Wᵐ} ins guard direct =
  target-insert-direct old-entry (targetLookup-off direct)
  where
  old-entry : ∀ Xᴿ
    → lookupStore
        (CTI2.targetStoreʷ (TE.smartAliasInsertWorld ins Wᵐ))
        (toRenameᵗ ρ Xᴿ)
      ≡ renameᵗ (toRenameᵗ ρ) (lookupStore (CTI2.targetStoreʷ Wᵐ) Xᴿ)
  old-entry Xᴿ = trans (targetLookup-insert direct Xᴿ)
    (cong (renameᵗ (toRenameᵗ ρ))
      (sym (cong (λ Σ → lookupStore Σ Xᴿ)
        (CTI2.SmartAliasMergeGuard.targetStore-same guard))))

smartAliasInsertWorld-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TE.TargetInsert ρ π W W′)
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → TargetInsertDirect ins
  → WorldInvariants Wᵐ
  → WorldInvariants (TE.smartAliasInsertWorld ins Wᵐ)
smartAliasInsertWorld-invariants ins guard direct inv =
  targetInsert-invariants (TE.smartAliasTargetInsert ins guard)
    (smartAliasTargetInsert-direct ins guard direct) inv


smartFreshTargetInsert-direct : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TE.TargetInsert ρ π W W′)
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → TargetInsertDirect ins
  → TargetInsertDirect (TE.smartFreshTargetInsert ins guard)
smartFreshTargetInsert-direct {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard direct = target-insert-direct old-entry fresh-entry
  where
  old = CTI2.SmartFreshBehindGuard.oldCenters guard
  po = CR.embeddingPushout π old
  πᵐ = CR.EmbeddingPushout.premise po

  old-entry : ∀ Xᴿ
    → lookupStore
        (CTI2.targetStoreʷ (TE.smartFreshInsertWorld ins guard))
        (toRenameᵗ ρ Xᴿ)
      ≡ renameᵗ (toRenameᵗ ρ) (lookupStore (CTI2.targetStoreʷ Wᵐ) Xᴿ)
  old-entry Xᴿ = trans (targetLookup-insert direct Xᴿ)
    (cong (renameᵗ (toRenameᵗ ρ))
      (sym (cong (λ Σ → lookupStore Σ Xᴿ)
        (CTI2.SmartFreshBehindGuard.targetStore-same guard))))

  input-center-off : ∀ Xᴿ′
    → CR.preimage? ρ Xᴿ′ ≡ nothing
    → CR.preimage? π (toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ′) ≡ nothing
  input-center-off Xᴿ′ no-old
      with CR.preimage? π (toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ′) in preπ
  input-center-off Xᴿ′ no-old | nothing = refl
  input-center-off Xᴿ′ no-old | just Z
      with TE.target-center-reflect ins (CR.preimage?-sound π preπ)
  input-center-off Xᴿ′ no-old | just Z
      | Xᴿ , xᴿ′-eq , old-center = ⊥-elim (CR.just≢nothing impossible)
    where
    impossible : just Xᴿ ≡ nothing
    impossible = trans
      (sym (CR.preimage?-image ρ Xᴿ))
      (trans (cong (CR.preimage? ρ) (sym xᴿ′-eq)) no-old)

  fresh-entry : ∀ Xᴿ′
    → CR.preimage? πᵐ
        (toRenameᵗ
          (CTI2.ηᴿʷ (TE.smartFreshInsertWorld ins guard)) Xᴿ′)
        ≡ nothing
    → lookupStore (CTI2.targetStoreʷ W′) Xᴿ′ ≡ ★
  fresh-entry Xᴿ′ off with CR.preimage? ρ Xᴿ′ in preρ
  fresh-entry Xᴿ′ off | just Xᴿ = ⊥-elim (CR.just≢nothing impossible)
    where
    xᴿ′-eq : Xᴿ′ ≡ toRenameᵗ ρ Xᴿ
    xᴿ′-eq = CR.preimage?-sound ρ preρ

    center-eq :
      toRenameᵗ (CTI2.ηᴿʷ (TE.smartFreshInsertWorld ins guard)) Xᴿ′
        ≡ toRenameᵗ πᵐ (toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Xᴿ)
    center-eq = trans
      (cong (toRenameᵗ
        (CTI2.ηᴿʷ (TE.smartFreshInsertWorld ins guard))) xᴿ′-eq)
      (TE.smartFresh-target-insert ins guard Xᴿ)

    impossible :
      just (toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Xᴿ) ≡ nothing
    impossible = trans
      (sym (CR.preimage?-image πᵐ
        (toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Xᴿ)))
      (trans (cong (CR.preimage? πᵐ) (sym center-eq)) off)
  fresh-entry Xᴿ′ off | nothing =
    targetLookup-off direct Xᴿ′ (input-center-off Xᴿ′ preρ)


smartFreshInsertWorld-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TE.TargetInsert ρ π W W′)
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → TargetInsertDirect ins
  → WorldInvariants Wᵐ
  → WorldInvariants (TE.smartFreshInsertWorld ins guard)
smartFreshInsertWorld-invariants ins guard direct inv =
  targetInsert-invariants (TE.smartFreshTargetInsert ins guard)
    (smartFreshTargetInsert-direct ins guard direct) inv


keepRightBindTargetInsert-direct : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {v : VarImp}
  → ⇑ᵗ B ≡ ★
  → TargetInsertDirect (TE.keepRightBindTargetInsert {W = W} {B = B} {v = v})
keepRightBindTargetInsert-direct {W = W} {B = B} {v = v} fresh-dynamic =
  liftBothTargetInsert-direct
    (TE.rightBindTargetInsert {W = W} {B = B})
    (rightBindTargetInsert-direct fresh-dynamic)


insertRebaseTargetInsert-direct : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {W⁺ : CTI2.World Δᴸ Δᴿ′ Δ′} {Xᴸ Xᴿ}
  → (ins : TE.TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → TargetInsertDirect ins
  → TargetInsertDirect (TE.insertRebaseTargetInsert ins rb)
insertRebaseTargetInsert-direct {ρ = ρ} {W = W} {Wᵖ = Wᵖ}
    ins rb direct = target-insert-direct old-entry (targetLookup-off direct)
  where
  old-entry : ∀ Yᴿ
    → lookupStore
        (CTI2.targetStoreʷ (TE.insertRebaseWorld ins Wᵖ))
        (toRenameᵗ ρ Yᴿ)
      ≡ renameᵗ (toRenameᵗ ρ) (lookupStore (CTI2.targetStoreʷ Wᵖ) Yᴿ)
  old-entry Yᴿ = trans (targetLookup-insert direct Yᴿ)
    (cong (renameᵗ (toRenameᵗ ρ))
      (sym (cong (λ Σ → lookupStore Σ Yᴿ)
        (CTI2.SameRuntime.targetStore-same
          (CTI2.RebaseAt.sameRuntime rb)))))


insertRebaseWorld-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {W⁺ : CTI2.World Δᴸ Δᴿ′ Δ′} {Xᴸ Xᴿ}
  → (ins : TE.TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → TargetInsertDirect ins
  → WorldInvariants Wᵖ
  → WorldInvariants (TE.insertRebaseWorld ins Wᵖ)
insertRebaseWorld-invariants ins rb direct inv =
  targetInsert-invariants (TE.insertRebaseTargetInsert ins rb)
    (insertRebaseTargetInsert-direct ins rb direct) inv


example12-left-path-world-X-invariants :
  WorldInvariants CTI2.example12-left-path-world-X
example12-left-path-world-X-invariants =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → CTI2.impEnvʷ CTI2.example12-left-path-world-X
        (toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-X) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 1 ]
        toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-X) Xᴿ
          ≡ toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-X) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) ()

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 1}
    → CenterAligned CTI2.example12-left-path-world-X Xᴸ Xᴿ
    → CTI2.impEnvʷ CTI2.example12-left-path-world-X ⊢
        renameᵗ (toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-X))
          (lookupStore (CTI2.sourceStoreʷ CTI2.example12-left-path-world-X) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-X))
          (lookupStore (CTI2.targetStoreʷ CTI2.example12-left-path-world-X) Xᴿ)
  reps {Fin.zero} {Fin.zero} refl = ι⊑★
  reps {Fin.suc Fin.zero} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → CenterAligned CTI2.example12-left-path-world-X Xᴸ Xᴿ → ⊥)
    → lookupStore (CTI2.targetStoreʷ CTI2.example12-left-path-world-X) Xᴿ ≡ ★
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)


example12-left-path-world-Y-invariants :
  WorldInvariants CTI2.example12-left-path-world-Y
example12-left-path-world-Y-invariants =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → CTI2.impEnvʷ CTI2.example12-left-path-world-Y
        (toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-Y) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 1 ]
        toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-Y) Xᴿ
          ≡ toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-Y) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) ()

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 1}
    → CenterAligned CTI2.example12-left-path-world-Y Xᴸ Xᴿ
    → CTI2.impEnvʷ CTI2.example12-left-path-world-Y ⊢
        renameᵗ (toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-Y))
          (lookupStore (CTI2.sourceStoreʷ CTI2.example12-left-path-world-Y) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-Y))
          (lookupStore (CTI2.targetStoreʷ CTI2.example12-left-path-world-Y) Xᴿ)
  reps {Fin.zero} {Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} refl = X⊑★ refl
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → CenterAligned CTI2.example12-left-path-world-Y Xᴸ Xᴿ → ⊥)
    → lookupStore (CTI2.targetStoreʷ CTI2.example12-left-path-world-Y) Xᴿ ≡ ★
  unmatched Fin.zero no-source =
    ⊥-elim (no-source (Fin.suc Fin.zero) refl)


example12-left-path-world-Z-invariants :
  WorldInvariants CTI2.example12-left-path-world-Z
example12-left-path-world-Z-invariants =
  world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → CTI2.impEnvʷ CTI2.example12-left-path-world-Z
        (toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-Z) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 1 ]
        toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-Z) Xᴿ
          ≡ toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-Z) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) ()

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 1}
    → CenterAligned CTI2.example12-left-path-world-Z Xᴸ Xᴿ
    → CTI2.impEnvʷ CTI2.example12-left-path-world-Z ⊢
        renameᵗ (toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-Z))
          (lookupStore (CTI2.sourceStoreʷ CTI2.example12-left-path-world-Z) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-Z))
          (lookupStore (CTI2.targetStoreʷ CTI2.example12-left-path-world-Z) Xᴿ)
  reps {Fin.zero} {Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} refl = ★⊑★

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → CenterAligned CTI2.example12-left-path-world-Z Xᴸ Xᴿ → ⊥)
    → lookupStore (CTI2.targetStoreʷ CTI2.example12-left-path-world-Z) Xᴿ ≡ ★
  unmatched Fin.zero no-source =
    ⊥-elim (no-source (Fin.suc (Fin.suc Fin.zero)) refl)


examples2-left-path-world₃-invariants : WorldInvariants Ex2.left-path-world₃
examples2-left-path-world₃-invariants = world-invariants precise reps unmatched
  where
  precise : ∀ Xᴸ
    → CTI2.impEnvʷ Ex2.left-path-world₃
        (toRenameᵗ (CTI2.ηᴸʷ Ex2.left-path-world₃) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 2 ]
        toRenameᵗ (CTI2.ηᴿʷ Ex2.left-path-world₃) Xᴿ
          ≡ toRenameᵗ (CTI2.ηᴸʷ Ex2.left-path-world₃) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) ()

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 2}
    → CenterAligned Ex2.left-path-world₃ Xᴸ Xᴿ
    → CTI2.impEnvʷ Ex2.left-path-world₃ ⊢
        renameᵗ (toRenameᵗ (CTI2.ηᴸʷ Ex2.left-path-world₃))
          (lookupStore (CTI2.sourceStoreʷ Ex2.left-path-world₃) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (CTI2.ηᴿʷ Ex2.left-path-world₃))
          (lookupStore (CTI2.targetStoreʷ Ex2.left-path-world₃) Xᴿ)
  reps {Fin.zero} {Fin.zero} refl = ι⊑★
  reps {Fin.zero} {Fin.suc Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.suc Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.suc Fin.zero} refl = ★⊑★

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → CenterAligned Ex2.left-path-world₃ Xᴸ Xᴿ → ⊥)
    → lookupStore (CTI2.targetStoreʷ Ex2.left-path-world₃) Xᴿ ≡ ★
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Fin.zero) no-source =
    ⊥-elim (no-source (Fin.suc (Fin.suc Fin.zero)) refl)

examples2-left-path-world₄-invariants : WorldInvariants Ex2.left-path-world₄
examples2-left-path-world₄-invariants = examples2-left-path-world₃-invariants

examples2-left-path-world₅-invariants : WorldInvariants Ex2.left-path-world₅
examples2-left-path-world₅-invariants = examples2-left-path-world₃-invariants

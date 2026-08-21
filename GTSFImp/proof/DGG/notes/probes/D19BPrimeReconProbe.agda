module D19BPrimeReconProbe where

-- File Charter:
--   * Checks D19 B-prime reconnaissance facts without changing live code.
--   * Exhibits matched-center decay in the current generic mark machinery.
--   * Checks that smart-alias's dynamic matched center is born in a
--     source-only smart-comma world.
--   * Type-checks, but does not prove, the four async-window peel statements.

open import Data.List using ([])
open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types using (Ty; TyCtx; TyVar; ＇_)
open import TyStore using (TyStore; store-empty; store-lift)
import Consistency as C
open import Imprecision using (ImpEnv; X⊑X; X⊑★)
import Imprecision as I
import Conversion as Conv
open import CastTerms using (Term; Value; _↑_; _↓_)
open import Reduction using (keep; _—→[_]_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.CtxImp as CTX
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.SimConcealRevealPeel as Peel
import proof.DGG.TargetBindLift as TBL
import proof.DGG.TermImpDecay as TID
import proof.DGG.WorldDecay as WD
import proof.DGG.WorldInvariants as WI

open CTX using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


------------------------------------------------------------------------
-- One matched center: generic decay really can erase a paired mark
------------------------------------------------------------------------

precise-env : ImpEnv 1
precise-env Fin.zero = X⊑X

dynamic-env : ImpEnv 1
dynamic-env Fin.zero = X⊑★

one-cell-store : TyStore 1
one-cell-store = store-lift store-empty

precise-world : World 1 1 1
precise-world =
  CTX.world (C.keep C.empty) (C.keep C.empty) precise-env
    one-cell-store one-cell-store

dynamic-world : World 1 1 1
dynamic-world =
  CTX.world (C.keep C.empty) (C.keep C.empty) dynamic-env
    one-cell-store one-cell-store

precise-center-matched :
  CTX.CenterAligned precise-world Fin.zero Fin.zero
precise-center-matched = refl

dynamic-center-matched :
  CTX.CenterAligned dynamic-world Fin.zero Fin.zero
dynamic-center-matched = refl

generic-mono-decays-matched : CTX.ImpEnvMono precise-world dynamic-world
generic-mono-decays-matched Fin.zero ()

generic-env-decay-decays-matched : WD.EnvDecay precise-world dynamic-world
generic-env-decay-decays-matched =
  WD.env-decay refl refl refl refl generic-mono-decays-matched

blend-decays-matched :
  CTX.impEnvʷ (WD.blendWorld precise-world dynamic-world) Fin.zero ≡ X⊑★
blend-decays-matched = refl

dyn-world-decays-matched :
  CTX.impEnvʷ (WD.honestify precise-world) Fin.zero ≡ X⊑★
dyn-world-decays-matched = refl

honestify-keeps-matched :
  CTX.impEnvʷ (WD.honestify precise-world) Fin.zero ≡ X⊑X
honestify-keeps-matched = refl

precise-world-invariants : WI.WorldInvariants precise-world
precise-world-invariants = WI.initialWorld-invariants precise-env

dynamic-lift-passes-live-invariants :
  WI.WorldInvariants (CTX.liftWorldBoth X⊑★ precise-world)
dynamic-lift-passes-live-invariants =
  WI.liftWorldBoth-invariants X⊑★ precise-world-invariants

generic-rebase-decays-matched :
  CTX.RebaseAt precise-world dynamic-world Fin.zero Fin.zero
generic-rebase-decays-matched =
  CTX.rebase-at (CTX.same-runtime refl refl)
    (λ neq → refl) (λ _ → refl) refl
    (CTX.store-rep-imp I.X⊑X)


------------------------------------------------------------------------
-- Builders and the explicit paired-binder decay
------------------------------------------------------------------------

lift-both-precise-head :
  CTX.impEnvʷ (CTX.liftWorldBoth X⊑X precise-world) Fin.zero ≡ X⊑X
lift-both-precise-head = refl

lift-both-dynamic-head :
  CTX.impEnvʷ (CTX.liftWorldBoth X⊑★ precise-world) Fin.zero ≡ X⊑★
lift-both-dynamic-head = refl

lift-both-head-matched :
  CTX.CenterAligned (CTX.liftWorldBoth X⊑★ precise-world)
    Fin.zero Fin.zero
lift-both-head-matched = refl

lift-left-dynamic-head :
  CTX.impEnvʷ (CTX.liftWorldLeft precise-world) Fin.zero ≡ X⊑★
lift-left-dynamic-head = refl

lift-left-head-not-target : ∀ Y
  → C.toRenameᵗ
      (CTX.ηᴿʷ (CTX.liftWorldLeft precise-world)) Y
    ≢ C.toRenameᵗ
      (CTX.ηᴸʷ (CTX.liftWorldLeft precise-world)) Fin.zero
lift-left-head-not-target Fin.zero ()

right-only-dynamic-head :
  CTX.impEnvʷ (CTX.rightOnlyWorld precise-world (＇ Fin.zero))
    Fin.zero ≡ X⊑★
right-only-dynamic-head = refl

right-only-head-not-source : ∀ X
  → C.toRenameᵗ
      (CTX.ηᴸʷ (CTX.rightOnlyWorld precise-world (＇ Fin.zero))) X
    ≢ C.toRenameᵗ
      (CTX.ηᴿʷ (CTX.rightOnlyWorld precise-world (＇ Fin.zero)))
        Fin.zero
right-only-head-not-source Fin.zero ()

both-bind-precise-head :
  CTX.impEnvʷ
    (CTX.bothBindWorld X⊑X precise-world (＇ Fin.zero) (＇ Fin.zero))
    Fin.zero ≡ X⊑X
both-bind-precise-head = refl

paired-binder-decay :
  WD.EnvDecay
    (CTX.liftWorldBoth X⊑X precise-world)
    (CTX.liftWorldBoth X⊑★ precise-world)
paired-binder-decay = TID.liftBothBinderDecay

paired-binder-decay-erases-head :
  CTX.impEnvʷ (CTX.liftWorldBoth X⊑★ precise-world) Fin.zero ≡ X⊑★
paired-binder-decay-erases-head = refl


------------------------------------------------------------------------
-- Rename and target-store movement preserve old marks
------------------------------------------------------------------------

rename-preserves-old-paired-mark :
  CTX.impEnvʷ (CR.renameWorld C.wk↪ᵗ precise-world)
    (Fin.suc Fin.zero) ≡ X⊑X
rename-preserves-old-paired-mark = refl

rename-fresh-center-is-dynamic :
  CTX.impEnvʷ (CR.renameWorld C.wk↪ᵗ precise-world) Fin.zero ≡ X⊑★
rename-fresh-center-is-dynamic = refl

target-store-as-preserves-mark :
  CTX.impEnvʷ (TBL.targetStoreAs precise-world one-cell-store)
    Fin.zero ≡ X⊑X
target-store-as-preserves-mark = refl


------------------------------------------------------------------------
-- Smart alias: matched and dynamic, but created by a source-only lift
------------------------------------------------------------------------

smart-alias-pending-matched : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → CTX.CenterAligned Wᵐ Fin.zero β
smart-alias-pending-matched {β = β} guard =
  trans (CTX.SmartAliasMergeGuard.pending-at-alias guard)
    (sym (CTX.SmartAliasMergeGuard.target-frozen guard β))

smart-alias-pending-mark-dynamic : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → CTX.impEnvʷ Wᵐ (C.toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero) ≡ X⊑★
smart-alias-pending-mark-dynamic {Wᵐ = Wᵐ} guard =
  trans
    (cong (CTX.impEnvʷ Wᵐ)
      (CTX.SmartAliasMergeGuard.pending-at-alias guard))
    (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard)

smart-fresh-pending-unmatched : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
  → CTX.SmartFreshBehindGuard W Wᵐ
  → ∀ Y
  → CTX.CenterAligned Wᵐ Fin.zero Y
  → ⊥
smart-fresh-pending-unmatched guard Y aligned =
  CTX.SmartFreshBehindGuard.fresh-not-target guard Y (sym aligned)


------------------------------------------------------------------------
-- The target-bind tower exposes the current matched-dynamic middle slot
------------------------------------------------------------------------

tower-middle-matched :
  CTX.CenterAligned (TBL.ΛLiftToBindFreshWorld X⊑★ precise-world)
    Fin.zero Fin.zero
tower-middle-matched = refl

tower-middle-dynamic :
  CTX.impEnvʷ (TBL.ΛLiftToBindFreshWorld X⊑★ precise-world)
    (Fin.suc Fin.zero) ≡ X⊑★
tower-middle-dynamic = refl


------------------------------------------------------------------------
-- Statement-only async-window inventory
------------------------------------------------------------------------

PairedConcealRevealPeelStatement : Set
PairedConcealRevealPeelStatement =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ Conv.seal Xᴸ R) ↑ Conv.unseal Xᴸ R)
      ⊑ ((V₀′ ↓ Conv.seal Xᴿ R′) ↑ Conv.unseal Xᴿ R′) ∶ q
  → ((V₀ ↓ Conv.seal Xᴸ R) ↑ Conv.unseal Xᴸ R)
      —→[ keep ] V₀
  → ((V₀′ ↓ Conv.seal Xᴿ R′) ↑ Conv.unseal Xᴿ R′)
      —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

SourceOnlyConcealRevealPeelStatement : Set
SourceOnlyConcealRevealPeelStatement =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {N′ V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Peel.TargetOpenedByConcealReveal N′ Xᴿ R′ V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ Conv.seal Xᴸ R) ↑ Conv.unseal Xᴸ R)
      ⊑ V₀′ ∶ q
  → ((V₀ ↓ Conv.seal Xᴸ R) ↑ Conv.unseal Xᴸ R)
      —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

PairedIdConcealPeelStatement : Set
PairedIdConcealPeelStatement =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      (V₀ ↓ Conv.id↓ A) ⊑ (V₀′ ↓ Conv.id↓ B) ∶ q
  → (V₀ ↓ Conv.id↓ A) —→[ keep ] V₀
  → (V₀′ ↓ Conv.id↓ B) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

SourceOpenedIdConcealPeelStatement : Set
SourceOpenedIdConcealPeelStatement =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢² (V₀ ↓ Conv.id↓ A) ⊑ V₀′ ∶ q
  → (V₀ ↓ Conv.id↓ A) —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

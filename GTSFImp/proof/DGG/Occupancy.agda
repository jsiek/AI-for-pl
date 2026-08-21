module proof.DGG.Occupancy where

-- File Charter:
--   * Collects transport facts for the live CTI2 target-occupancy
--     predicates.
--   * Occupancy is the image of the target embedding in the center context;
--     no-target facts are preserved only by evolutions that keep the relevant
--     center outside that image.
--   * Exports leaf lemmas used to audit S-OCC: initial worlds, left lifts,
--     right-only binds, target insertion, smart-comma lift guards, rebasing,
--     center rename, and decay.

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import TyStore using (TyStore)
open import Consistency using (_↪ᵗ_; id↪ᵗ; toRenameᵗ)
open import Imprecision using (ImpEnv; VarImp; X⊑★)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.TargetExtend as TE
import proof.DGG.WorldDecay as WD
open import proof.TypeInTermSubst using (toRename-id-eq)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; toRenameᵗ-injective)

------------------------------------------------------------------------
-- Initial and direct world constructors
------------------------------------------------------------------------

fin-image? : ∀ {m n}
  → (f : Fin.Fin m → Fin.Fin n)
  → (Z : Fin.Fin n)
  → Dec (Σ[ Y ∈ Fin.Fin m ] f Y ≡ Z)
fin-image? {m = Nat.zero} f Z =
  no (λ { (() , eq) })
fin-image? {m = Nat.suc m} f Z with FinP._≟_ (f Fin.zero) Z
fin-image? {m = Nat.suc m} f Z | yes eq =
  yes (Fin.zero , eq)
fin-image? {m = Nat.suc m} f Z | no neq
    with fin-image? (λ Y → f (Fin.suc Y)) Z
fin-image? {m = Nat.suc m} f Z | no neq | yes (Y , eq) =
  yes (Fin.suc Y , eq)
fin-image? {m = Nat.suc m} f Z | no neq | no no-tail =
  no no-image
  where
  no-image : (Σ[ Y ∈ Fin.Fin (Nat.suc m) ] f Y ≡ Z) → ⊥
  no-image (Fin.zero , eq) = neq eq
  no-image (Fin.suc Y , eq) = no-tail (Y , eq)

occupied? : ∀ {Δᴸ Δᴿ Δ}
  → (W : CTI2.World Δᴸ Δᴿ Δ)
  → (Z : TyVar Δ)
  → Dec (CTI2.Occupied W Z)
occupied? {Δᴿ = Δᴿ} W Z =
  fin-image? (toRenameᵗ (CTI2.ηᴿʷ W)) Z

occupied-at-source? : ∀ {Δᴸ Δᴿ Δ}
  → (W : CTI2.World Δᴸ Δᴿ Δ)
  → (X : TyVar Δᴸ)
  → Dec (CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X))
occupied-at-source? W X =
  occupied? W (toRenameᵗ (CTI2.ηᴸʷ W) X)

no-target-at-source? : ∀ {Δᴸ Δᴿ Δ}
  → (W : CTI2.World Δᴸ Δᴿ Δ)
  → (X : TyVar Δᴸ)
  → Dec (CTI2.NoTargetOccupantAtSource W X)
no-target-at-source? W X with occupied-at-source? W X
no-target-at-source? W X | yes occ =
  no (λ no-target → no-target occ)
no-target-at-source? W X | no no-occ =
  yes no-occ

initialWorldᴼ : ∀ {Δ}
  → ImpEnv Δ
  → CTI2.World Δ Δ Δ
initialWorldᴼ μ = CTI2.initialWorld μ

initial-every-center-occupiedᴼ : ∀ {Δ}
    {μ : ImpEnv Δ}
  → (Z : TyVar Δ)
  → CTI2.Occupied (initialWorldᴼ μ) Z
initial-every-center-occupiedᴼ {μ = μ} Z =
  Z , trans (cong (λ η → toRenameᵗ η Z) (CTI2.initialWorld-ηᴿ μ))
    (toRename-id-eq Z)

initial-no-see-through-emptyᴼ : ∀ {Δ}
    {μ : ImpEnv Δ}
  → (Z : TyVar Δ)
  → CTI2.NoTargetOccupant (initialWorldᴼ μ) Z
  → ⊥
initial-no-see-through-emptyᴼ {μ = μ} Z no-target =
  no-target (initial-every-center-occupiedᴼ {μ = μ} Z)

liftWorldLeft-fresh-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.NoTargetOccupant (CTI2.liftWorldLeft W) Fin.zero
liftWorldLeft-fresh-no-targetᴼ (Y , ())

liftWorldLeft-old-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant (CTI2.liftWorldLeft W) (Fin.suc Z)
liftWorldLeft-old-no-targetᴼ no-target (Y , eq) =
  no-target (Y , fin-suc-injective eq)

liftWorldLeft-old-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
  → CTI2.Occupied W Z
  → CTI2.Occupied (CTI2.liftWorldLeft W) (Fin.suc Z)
liftWorldLeft-old-occupiedᴼ (Y , eq) =
  Y , cong Fin.suc eq

liftWorldLeft-old-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {X}
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource
      (CTI2.liftWorldLeft W) (Fin.suc X)
liftWorldLeft-old-no-target-at-sourceᴼ {W = W} {X = X} =
  liftWorldLeft-old-no-targetᴼ
    {W = W} {Z = toRenameᵗ (CTI2.ηᴸʷ W) X}

liftWorldBoth-fresh-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (v : VarImp)
  → CTI2.Occupied (CTI2.liftWorldBoth v W) Fin.zero
liftWorldBoth-fresh-occupiedᴼ v = Fin.zero , refl

liftWorldBoth-old-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (v : VarImp)
  → CTI2.Occupied W Z
  → CTI2.Occupied (CTI2.liftWorldBoth v W) (Fin.suc Z)
liftWorldBoth-old-occupiedᴼ v (Y , eq) =
  Fin.suc Y , cong Fin.suc eq

liftWorldBoth-old-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (v : VarImp)
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant (CTI2.liftWorldBoth v W) (Fin.suc Z)
liftWorldBoth-old-no-targetᴼ v no-target (Fin.zero , ())
liftWorldBoth-old-no-targetᴼ v no-target (Fin.suc Y , eq) =
  no-target (Y , fin-suc-injective eq)

leftOnly-fresh-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (A : Ty Δᴸ)
  → CTI2.NoTargetOccupant
      (CTI2.leftOnlyWorld W A) Fin.zero
leftOnly-fresh-no-targetᴼ A (Y , ())

leftOnly-old-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (A : Ty Δᴸ)
  → CTI2.Occupied W Z
  → CTI2.Occupied (CTI2.leftOnlyWorld W A) (Fin.suc Z)
leftOnly-old-occupiedᴼ A (Y , eq) =
  Y , cong Fin.suc eq

leftOnly-old-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (A : Ty Δᴸ)
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant
      (CTI2.leftOnlyWorld W A) (Fin.suc Z)
leftOnly-old-no-targetᴼ A no-target (Y , eq) =
  no-target (Y , fin-suc-injective eq)

rightOnly-new-target-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (B : Ty Δᴿ)
    (fresh : CTI2.RightBindFresh W B)
  → CTI2.Occupied (CTI2.rightOnlyWorld W B fresh) Fin.zero
rightOnly-new-target-occupiedᴼ B fresh = Fin.zero , refl

rightOnly-old-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (B : Ty Δᴿ)
    (fresh : CTI2.RightBindFresh W B)
  → CTI2.Occupied W Z
  → CTI2.Occupied (CTI2.rightOnlyWorld W B fresh) (Fin.suc Z)
rightOnly-old-occupiedᴼ B fresh (Y , eq) =
  Fin.suc Y , cong Fin.suc eq

rightOnly-old-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (B : Ty Δᴿ)
    (fresh : CTI2.RightBindFresh W B)
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant
      (CTI2.rightOnlyWorld W B fresh) (Fin.suc Z)
rightOnly-old-no-targetᴼ B fresh no-target (Fin.zero , ())
rightOnly-old-no-targetᴼ B fresh no-target (Fin.suc Y , eq) =
  no-target (Y , fin-suc-injective eq)

rightOnly-old-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {X}
    (B : Ty Δᴿ)
    (fresh : CTI2.RightBindFresh W B)
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource (CTI2.rightOnlyWorld W B fresh) X
rightOnly-old-no-target-at-sourceᴼ {W = W} {X = X} B fresh =
  rightOnly-old-no-targetᴼ
    {W = W} {Z = toRenameᵗ (CTI2.ηᴸʷ W) X} B fresh

bothBind-new-target-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (A : Ty Δᴸ) (B : Ty Δᴿ) (A⊑B : A CTI2.⊑ᵂ⟨ W ⟩ B)
  → CTI2.Occupied (CTI2.bothBindWorld W A B A⊑B) Fin.zero
bothBind-new-target-occupiedᴼ A B A⊑B = Fin.zero , refl

bothBind-old-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (A : Ty Δᴸ) (B : Ty Δᴿ) (A⊑B : A CTI2.⊑ᵂ⟨ W ⟩ B)
  → CTI2.Occupied W Z
  → CTI2.Occupied (CTI2.bothBindWorld W A B A⊑B) (Fin.suc Z)
bothBind-old-occupiedᴼ A B A⊑B (Y , eq) =
  Fin.suc Y , cong Fin.suc eq

bothBind-old-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
    (A : Ty Δᴸ) (B : Ty Δᴿ) (A⊑B : A CTI2.⊑ᵂ⟨ W ⟩ B)
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant
      (CTI2.bothBindWorld W A B A⊑B) (Fin.suc Z)
bothBind-old-no-targetᴼ A B A⊑B no-target (Fin.zero , ())
bothBind-old-no-targetᴼ A B A⊑B no-target (Fin.suc Y , eq) =
  no-target (Y , fin-suc-injective eq)

------------------------------------------------------------------------
-- Rebasing and decay
------------------------------------------------------------------------

rebase-occupied-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.Occupied W Z
  → CTI2.Occupied W′ Z
rebase-occupied-forwardᴼ rb (Y , eq) =
  Y , trans (CTI2.RebaseAt.ηᴿ-frozen rb Y) eq

rebase-occupied-backwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.Occupied W′ Z
  → CTI2.Occupied W Z
rebase-occupied-backwardᴼ rb (Y , eq) =
  Y , trans (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y)) eq

rebase-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant W′ Z
rebase-no-target-forwardᴼ rb no-target occ′ =
  no-target (rebase-occupied-backwardᴼ rb occ′)

rebase-no-target-backwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.NoTargetOccupant W′ Z
  → CTI2.NoTargetOccupant W Z
rebase-no-target-backwardᴼ rb no-target occ =
  no-target (rebase-occupied-forwardᴼ rb occ)

rebaseᴸ-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Z}
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant W′ Z
rebaseᴸ-no-target-forwardᴼ CTI2.rebase-idᴸ no-target =
  no-target
rebaseᴸ-no-target-forwardᴼ (CTI2.rebase-varᴸ rb) no-target =
  rebase-no-target-forwardᴼ rb no-target
rebaseᴸ-no-target-forwardᴼ
    (CTI2.rebase-onlyᴸ _ _ _) no-target =
  no-target

rebaseᴿ-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ? Z}
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant W′ Z
rebaseᴿ-no-target-forwardᴼ CTI2.rebase-idᴿ no-target =
  no-target
rebaseᴿ-no-target-forwardᴼ (CTI2.rebase-varᴿ rb) no-target =
  rebase-no-target-forwardᴼ rb no-target

tag-rebase-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ? Z}
  → CTI2.TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant W′ Z
tag-rebase-no-target-forwardᴼ CTI2.tag-rebase-idᴸ no-target =
  no-target
tag-rebase-no-target-forwardᴼ (CTI2.tag-rebase-varᴸ rb) no-target =
  rebase-no-target-forwardᴼ rb no-target
tag-rebase-no-target-forwardᴼ
    (CTI2.tag-rebase-onlyᴸ _ _ _) no-target =
  no-target

decay-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ} {Z}
  → WD.EnvDecay W Wᵈ
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant Wᵈ Z
decay-no-target-forwardᴼ dec no-target (Y , eq) =
  no-target
    (Y , trans
      (sym (cong (λ η → toRenameᵗ η Y) (WD.ηᴿ-same dec))) eq)

decay-occupied-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ} {Z}
  → WD.EnvDecay W Wᵈ
  → CTI2.Occupied W Z
  → CTI2.Occupied Wᵈ Z
decay-occupied-forwardᴼ dec (Y , eq) =
  Y , trans
    (cong (λ η → toRenameᵗ η Y) (WD.ηᴿ-same dec)) eq

decay-occupied-backwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ} {Z}
  → WD.EnvDecay W Wᵈ
  → CTI2.Occupied Wᵈ Z
  → CTI2.Occupied W Z
decay-occupied-backwardᴼ dec (Y , eq) =
  Y , trans
    (sym (cong (λ η → toRenameᵗ η Y) (WD.ηᴿ-same dec))) eq

decay-no-target-at-source-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ} {X}
  → WD.EnvDecay W Wᵈ
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource Wᵈ X
decay-no-target-at-source-forwardᴼ {X = X}
    dec no-target (Y , aligned) =
  no-target (Y , old-aligned)
  where
  old-aligned =
    trans (sym (cong (λ η → toRenameᵗ η Y) (WD.ηᴿ-same dec)))
      (trans aligned
        (cong (λ η → toRenameᵗ η X) (WD.ηᴸ-same dec)))

------------------------------------------------------------------------
-- Center rename
------------------------------------------------------------------------

rename-no-target-occupantᴼ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Z}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant (CR.renameWorld π W) (toRenameᵗ π Z)
rename-no-target-occupantᴼ {W = W} {Z = Z} π no-target (Y , eq) =
  no-target (Y , target-eq)
  where
  target-eq :
    toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ Z
  target-eq =
    toRenameᵗ-injective π
      (trans (sym (CR.rename-ηᴿ-image π W Y)) eq)

rename-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {X}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource (CR.renameWorld π W) X
rename-no-target-at-sourceᴼ {W = W} {X = X} π no-target (Y , eq) =
  no-target (Y , target-eq)
  where
  target-eq :
    toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ toRenameᵗ (CTI2.ηᴸʷ W) X
  target-eq =
    toRenameᵗ-injective π
      (trans (sym (CR.rename-ηᴿ-image π W Y))
        (trans eq (CR.rename-ηᴸ-image π W X)))

------------------------------------------------------------------------
-- Target insertion
------------------------------------------------------------------------

target-insert-occupied-forwardᴼ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′} {Z}
  → (ins : TE.TargetInsert ρ π W W′)
  → CTI2.Occupied W Z
  → CTI2.Occupied W′ (toRenameᵗ π Z)
target-insert-occupied-forwardᴼ {ρ = ρ} {π = π} ins (Y , eq) =
  toRenameᵗ ρ Y , trans (TE.target-insert ins Y) (cong (toRenameᵗ π) eq)

target-insert-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′} {Z}
  → (ins : TE.TargetInsert ρ π W W′)
  → CTI2.NoTargetOccupant W Z
  → CTI2.NoTargetOccupant W′ (toRenameᵗ π Z)
target-insert-no-target-forwardᴼ ins no-target (Y′ , eq)
    with TE.target-center-reflect ins eq
target-insert-no-target-forwardᴼ ins no-target (Y′ , eq)
    | Y , _ , target-eq =
  no-target (Y , target-eq)

target-insert-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′} {X}
  → (ins : TE.TargetInsert ρ π W W′)
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource W′ X
target-insert-no-target-at-sourceᴼ {X = X} ins no-target (Y′ , eq)
    with TE.target-center-reflect ins (trans eq (TE.source-insert ins X))
target-insert-no-target-at-sourceᴼ {X = X} ins no-target (Y′ , eq)
    | Y , _ , target-eq =
  no-target (Y , target-eq)

------------------------------------------------------------------------
-- Smart-comma source lifts
------------------------------------------------------------------------

smartFreshBehind-fresh-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → CTI2.SmartFreshBehindGuard W Wᵐ
  → CTI2.NoTargetOccupantAtSource Wᵐ Fin.zero
smartFreshBehind-fresh-no-targetᴼ guard (Y , eq) =
  CTI2.SmartFreshBehindGuard.fresh-not-target guard Y eq

smartAliasMerge-fresh-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → CTI2.SmartAliasMergeGuard W Wᵐ β α
  → CTI2.Occupied Wᵐ (toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero)
smartAliasMerge-fresh-occupiedᴼ {β = β} guard =
  β , trans (CTI2.SmartAliasMergeGuard.target-frozen guard β)
            (sym (CTI2.SmartAliasMergeGuard.pending-at-alias guard))

smartFreshBehind-old-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ} {X}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource Wᵐ (Fin.suc X)
smartFreshBehind-old-no-target-at-sourceᴼ {W = W} {X = X}
    guard no-target (Y , eq) =
  no-target (Y , target-eq)
  where
  target-eq :
    toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ toRenameᵗ (CTI2.ηᴸʷ W) X
  target-eq =
    toRenameᵗ-injective
      (CTI2.SmartFreshBehindGuard.oldCenters guard)
      (trans (sym (CTI2.SmartFreshBehindGuard.target-frozen guard Y))
        (trans eq
          (CTI2.SmartFreshBehindGuard.old-source-frozen guard X)))

smartAliasMerge-old-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δ} {β α X}
  → CTI2.SmartAliasMergeGuard W Wᵐ β α
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource Wᵐ (Fin.suc X)
smartAliasMerge-old-no-target-at-sourceᴼ {W = W} {X = X}
    guard no-target (Y , eq) =
  no-target
    (Y , trans (sym (CTI2.SmartAliasMergeGuard.target-frozen guard Y))
      (trans eq
        (CTI2.SmartAliasMergeGuard.old-source-frozen guard X)))

smartCommaLift-old-no-target-at-sourceᴼ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ} {X}
  → CTI2.SmartCommaLiftᴸ W Wᵐ
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource Wᵐ (Fin.suc X)
smartCommaLift-old-no-target-at-sourceᴼ
    (CTI2.smart-fresh-behind guard) =
  smartFreshBehind-old-no-target-at-sourceᴼ guard
smartCommaLift-old-no-target-at-sourceᴼ
    (CTI2.smart-merge-alias guard) =
  smartAliasMerge-old-no-target-at-sourceᴼ guard

β-inst-allocation-occupies-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.Occupied (CTI2.rightOnlyWorld W ★ (inj₁ refl)) Fin.zero
β-inst-allocation-occupies-targetᴼ {W = W} =
  rightOnly-new-target-occupiedᴼ {W = W} ★ (inj₁ refl)

β-gen-allocation-occupies-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (C : Ty Δᴿ)
    (fresh : CTI2.RightBindFresh W C)
  → CTI2.Occupied (CTI2.rightOnlyWorld W C fresh) Fin.zero
β-gen-allocation-occupies-targetᴼ {W = W} C fresh =
  rightOnly-new-target-occupiedᴼ {W = W} C fresh

source-only-runtime-cell-remains-unoccupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.NoTargetOccupantAtSource (CTI2.liftWorldLeft W) Fin.zero
source-only-runtime-cell-remains-unoccupiedᴼ {W = W} =
  liftWorldLeft-fresh-no-targetᴼ {W = W}

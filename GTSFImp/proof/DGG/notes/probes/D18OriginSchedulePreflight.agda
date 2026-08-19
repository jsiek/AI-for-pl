module D18OriginSchedulePreflight where

-- File Charter:
--   * Pre-flights D18 Stage 1 and Stage 2 without changing the live World or
--     RebaseAt declarations.
--   * Computes originAt from an inductive world-construction schedule, with
--     one edge form for each World builder exported by CtxImp.
--   * Checks the tightened edge fields, stationary fixed points, the finite
--     Example12 schedule, and the two known conflicting shortcuts.
--   * Does not provide a broad rebase alias or a chain-to-rebase coercion.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Types using (TyCtx; TyVar)
open import Consistency using (toRenameᵗ)
import proof.DGG.CtxImp as CTX
import proof.DGG.Example12Worlds as Ex12
import proof.DGG.Examples2 as Ex2
import proof.DGG.SmartCommaWitness as Smart
import proof.DGG.TerminusRebuildProbe as T6


------------------------------------------------------------------------
-- Construction provenance and the computed origin schedule
------------------------------------------------------------------------

-- This list is exhaustive for definitions in CtxImp.agda that construct a
-- World: the raw `world` constructor and its five named World-valued builders.
-- SmartCommaLiftᴸ is evidence about caller-supplied worlds, not an additional
-- World-valued builder.

data WorldBuilder : Set where
  world-builder : WorldBuilder
  liftWorldBoth-builder : WorldBuilder
  liftWorldLeft-builder : WorldBuilder
  leftOnlyWorld-builder : WorldBuilder
  rightOnlyWorld-builder : WorldBuilder
  bothBindWorld-builder : WorldBuilder

-- An edge is admitted only as construction provenance.  Its raw geometric
-- evidence is the current live record, so this probe tests the real fields.
-- Later evidence-composition code cannot extend this schedule.

data OriginSchedule {Δᴸ Δᴿ Δ}
    (W′ : CTX.World Δᴸ Δᴿ Δ) : Set where
  stationary : OriginSchedule W′

  edge : ∀ {W : CTX.World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    → WorldBuilder
    → CTX.RebaseAt W W′ Xᴸ Xᴿ
    → OriginSchedule W′
    → OriginSchedule W′

originAtSchedule : ∀ {Δᴸ Δᴿ Δ} {W′ : CTX.World Δᴸ Δᴿ Δ}
  → OriginSchedule W′
  → TyVar Δᴸ
  → TyVar Δᴿ
  → CTX.World Δᴸ Δᴿ Δ
originAtSchedule {W′ = W′} stationary Xᴸ Xᴿ = W′
originAtSchedule (edge {W = W} {Xᴸ = X₀ᴸ} {Xᴿ = X₀ᴿ}
    builder rb rest) Xᴸ Xᴿ
    with Fin._≟_ Xᴸ X₀ᴸ | Fin._≟_ Xᴿ X₀ᴿ
originAtSchedule (edge {W = W} builder rb rest) ._ ._
    | yes refl | yes refl = W
originAtSchedule (edge builder rb rest) Xᴸ Xᴿ
    | yes Xᴸ≡X₀ᴸ | no Xᴿ≢X₀ᴿ = originAtSchedule rest Xᴸ Xᴿ
originAtSchedule (edge builder rb rest) Xᴸ Xᴿ
    | no Xᴸ≢X₀ᴸ | yes Xᴿ≡X₀ᴿ = originAtSchedule rest Xᴸ Xᴿ
originAtSchedule (edge builder rb rest) Xᴸ Xᴿ
    | no Xᴸ≢X₀ᴸ | no Xᴿ≢X₀ᴿ = originAtSchedule rest Xᴸ Xᴿ

record ScheduledWorld (Δᴸ Δᴿ Δ : TyCtx) : Set where
  constructor scheduled
  field
    rawWorld : CTX.World Δᴸ Δᴿ Δ
    provenance : OriginSchedule rawWorld

open ScheduledWorld public

originAt : ∀ {Δᴸ Δᴿ Δ}
  → ScheduledWorld Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → CTX.World Δᴸ Δᴿ Δ
originAt (scheduled W provenance) Xᴸ Xᴿ =
  originAtSchedule provenance Xᴸ Xᴿ

stationaryWorld : ∀ {Δᴸ Δᴿ Δ}
  → CTX.World Δᴸ Δᴿ Δ
  → ScheduledWorld Δᴸ Δᴿ Δ
stationaryWorld W = scheduled W stationary

originAt-stationary : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → originAt (stationaryWorld W) Xᴸ Xᴿ ≡ W
originAt-stationary = refl

originAt-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (builder : WorldBuilder)
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → originAt (scheduled W′ (edge builder rb rest)) Xᴸ Xᴿ ≡ W
originAt-edge {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} builder rb rest
    with Fin._≟_ Xᴸ Xᴸ | Fin._≟_ Xᴿ Xᴿ
originAt-edge builder rb rest | yes refl | yes refl = refl
originAt-edge builder rb rest | yes Xᴸ≡Xᴸ | no Xᴿ≢Xᴿ =
  ⊥-elim (Xᴿ≢Xᴿ refl)
originAt-edge builder rb rest | no Xᴸ≢Xᴸ | yes Xᴿ≡Xᴿ =
  ⊥-elim (Xᴸ≢Xᴸ refl)
originAt-edge builder rb rest | no Xᴸ≢Xᴸ | no Xᴿ≢Xᴿ =
  ⊥-elim (Xᴸ≢Xᴸ refl)


------------------------------------------------------------------------
-- Tightened sandbox relation and selected-origin properties
------------------------------------------------------------------------

record RebaseAt {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ)
    (W′ : ScheduledWorld Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    origin-determined : W ≡ originAt W′ Xᴸ Xᴿ
    sameRuntime : CTX.SameRuntime W (rawWorld W′)
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (CTX.ηᴸʷ (rawWorld W′)) Y
        ≡ toRenameᵗ (CTX.ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (CTX.ηᴿʷ (rawWorld W′)) Y
        ≡ toRenameᵗ (CTX.ηᴿʷ W) Y
    pivotAligned :
      toRenameᵗ (CTX.ηᴸʷ (rawWorld W′)) Xᴸ
        ≡ toRenameᵗ (CTX.ηᴿʷ (rawWorld W′)) Xᴿ
    storeRepresentations : CTX.StoreRepImp (rawWorld W′) Xᴸ Xᴿ

open RebaseAt public

edgeRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (builder : WorldBuilder)
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W (scheduled W′ (edge builder rb rest)) Xᴸ Xᴿ
edgeRebaseAt builder rb rest =
  rebase-at (sym (originAt-edge builder rb rest))
    (CTX.RebaseAt.sameRuntime rb)
    (CTX.RebaseAt.ηᴸ-off-pivot rb)
    (CTX.RebaseAt.ηᴿ-frozen rb)
    (CTX.RebaseAt.pivotAligned rb)
    (CTX.RebaseAt.storeRepresentations rb)

stationaryRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → RebaseAt W (stationaryWorld W) Xᴸ Xᴿ
stationaryRebaseAt aligned reps =
  rebase-at refl (CTX.same-runtime refl refl)
    (λ _ → refl) (λ _ → refl) aligned reps

selected-origin-sameRuntime : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : ScheduledWorld Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : RebaseAt W W′ Xᴸ Xᴿ)
  → CTX.SameRuntime (originAt W′ Xᴸ Xᴿ) (rawWorld W′)
selected-origin-sameRuntime rb =
  subst (λ O → CTX.SameRuntime O _) (origin-determined rb)
    (sameRuntime rb)

selected-origin-off-pivot : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : ScheduledWorld Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y : TyVar Δᴸ}
  → (rb : RebaseAt W W′ Xᴸ Xᴿ)
  → Y ≢ Xᴸ
  → toRenameᵗ (CTX.ηᴸʷ (rawWorld W′)) Y
    ≡ toRenameᵗ (CTX.ηᴸʷ (originAt W′ Xᴸ Xᴿ)) Y
selected-origin-off-pivot {W′ = W′} {Y = Y} rb Y≢Xᴸ =
  subst
    (λ O → toRenameᵗ (CTX.ηᴸʷ (rawWorld W′)) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ O) Y)
    (origin-determined rb) (ηᴸ-off-pivot rb Y≢Xᴸ)

selected-origin-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : ScheduledWorld Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ Y : TyVar Δᴿ}
  → (rb : RebaseAt W W′ Xᴸ Xᴿ)
  → toRenameᵗ (CTX.ηᴿʷ (rawWorld W′)) Y
    ≡ toRenameᵗ (CTX.ηᴿʷ (originAt W′ Xᴸ Xᴿ)) Y
selected-origin-target-frozen {W′ = W′} {Y = Y} rb =
  subst
    (λ O → toRenameᵗ (CTX.ηᴿʷ (rawWorld W′)) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ O) Y)
    (origin-determined rb) (ηᴿ-frozen rb _)

selected-origin-pivot-aligned : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : ScheduledWorld Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → RebaseAt W W′ Xᴸ Xᴿ
  → toRenameᵗ (CTX.ηᴸʷ (rawWorld W′)) Xᴸ
    ≡ toRenameᵗ (CTX.ηᴿʷ (rawWorld W′)) Xᴿ
selected-origin-pivot-aligned = pivotAligned

selected-origin-representations : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : ScheduledWorld Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → RebaseAt W W′ Xᴸ Xᴿ
  → CTX.StoreRepImp (rawWorld W′) Xᴸ Xᴿ
selected-origin-representations = storeRepresentations


------------------------------------------------------------------------
-- One checked edge rule per CtxImp World builder
------------------------------------------------------------------------

world-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W (scheduled W′ (edge world-builder rb rest)) Xᴸ Xᴿ
world-edge = edgeRebaseAt world-builder

liftWorldBoth-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W
      (scheduled W′ (edge liftWorldBoth-builder rb rest)) Xᴸ Xᴿ
liftWorldBoth-edge = edgeRebaseAt liftWorldBoth-builder

liftWorldLeft-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W
      (scheduled W′ (edge liftWorldLeft-builder rb rest)) Xᴸ Xᴿ
liftWorldLeft-edge = edgeRebaseAt liftWorldLeft-builder

leftOnlyWorld-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W
      (scheduled W′ (edge leftOnlyWorld-builder rb rest)) Xᴸ Xᴿ
leftOnlyWorld-edge = edgeRebaseAt leftOnlyWorld-builder

rightOnlyWorld-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W
      (scheduled W′ (edge rightOnlyWorld-builder rb rest)) Xᴸ Xᴿ
rightOnlyWorld-edge = edgeRebaseAt rightOnlyWorld-builder

bothBindWorld-edge : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (rb : CTX.RebaseAt W W′ Xᴸ Xᴿ)
  → (rest : OriginSchedule W′)
  → RebaseAt W
      (scheduled W′ (edge bothBindWorld-builder rb rest)) Xᴸ Xᴿ
bothBindWorld-edge = edgeRebaseAt bothBindWorld-builder


------------------------------------------------------------------------
-- Raw target-wrapper producer adapter used only at construction mints
------------------------------------------------------------------------

record TargetProducerPreflight {Δᴸ Δᴿ Δ}
    (W W′ : CTX.World Δᴸ Δᴿ Δ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor target-producer
  field
    producer-Xᴸ : TyVar Δᴸ
    producer-raw : CTX.RebaseAt W W′ producer-Xᴸ Xᴿ
    producer-tightened :
      RebaseAt W
        (scheduled W′ (edge world-builder producer-raw stationary))
        producer-Xᴸ Xᴿ

open TargetProducerPreflight public

target-producer-preflight : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ} {Xᴿ : TyVar Δᴿ}
  → CTX.RebaseAtᴿ W W′ (just Xᴿ)
  → TargetProducerPreflight W W′ Xᴿ
target-producer-preflight (CTX.rebase-varᴿ rb) =
  target-producer _ rb (world-edge rb stationary)

smart-comma-outer-preflight :
  TargetProducerPreflight Smart.a3-d1-alias-world
    Smart.a3-d1-name-world Smart.target-α
smart-comma-outer-preflight =
  target-producer-preflight Smart.a3-d1-outer-rebaseᴿ

smart-comma-inner-preflight :
  TargetProducerPreflight Smart.a3-d1-name-world
    Smart.a3-d1-alias-world Smart.target-β
smart-comma-inner-preflight =
  target-producer-preflight Smart.a3-d1-inner-rebaseᴿ

smart-comma-outer-origin-determined :
  Smart.a3-d1-alias-world ≡
    originAt
      (scheduled Smart.a3-d1-name-world
        (edge world-builder
          (producer-raw smart-comma-outer-preflight) stationary))
      (producer-Xᴸ smart-comma-outer-preflight) Smart.target-α
smart-comma-outer-origin-determined =
  origin-determined (producer-tightened smart-comma-outer-preflight)

smart-comma-inner-origin-determined :
  Smart.a3-d1-name-world ≡
    originAt
      (scheduled Smart.a3-d1-alias-world
        (edge world-builder
          (producer-raw smart-comma-inner-preflight) stationary))
      (producer-Xᴸ smart-comma-inner-preflight) Smart.target-β
smart-comma-inner-origin-determined =
  origin-determined (producer-tightened smart-comma-inner-preflight)


------------------------------------------------------------------------
-- Stage 2 finite schedule: Example12 X/Z/Y and the nat chain
------------------------------------------------------------------------

example12-world-Zᵀ : ScheduledWorld 1 3 3
example12-world-Zᵀ =
  scheduled Ex12.example12-world-Z
    (edge world-builder Ex12.example12-rebase-X-to-Z stationary)

example12-rebase-X-to-Zᵀ :
  RebaseAt Ex12.example12-world-X example12-world-Zᵀ
    Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-rebase-X-to-Zᵀ =
  world-edge Ex12.example12-rebase-X-to-Z stationary

example12-world-Yᵀ : ScheduledWorld 1 3 3
example12-world-Yᵀ =
  scheduled Ex12.example12-world-Y
    (edge world-builder Ex2.example12-rebase-Z-to-Y stationary)

example12-rebase-Z-to-Yᵀ :
  RebaseAt Ex12.example12-world-Z example12-world-Yᵀ
    Fin.zero (Fin.suc Fin.zero)
example12-rebase-Z-to-Yᵀ =
  world-edge Ex2.example12-rebase-Z-to-Y stationary

example12-nat-world-Yᵀ : ScheduledWorld 1 2 2
example12-nat-world-Yᵀ =
  scheduled Ex12.example12-nat-chain-world-Y
    (edge world-builder Ex12.example12-nat-chain-rebase-X-to-Y stationary)

example12-nat-rebase-X-to-Yᵀ :
  RebaseAt Ex12.example12-nat-chain-world-X example12-nat-world-Yᵀ
    Fin.zero Fin.zero
example12-nat-rebase-X-to-Yᵀ =
  world-edge Ex12.example12-nat-chain-rebase-X-to-Y stationary

example12-X-to-Z-origin-determined :
  Ex12.example12-world-X ≡
    originAt example12-world-Zᵀ Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-X-to-Z-origin-determined =
  origin-determined example12-rebase-X-to-Zᵀ

example12-Z-to-Y-origin-determined :
  Ex12.example12-world-Z ≡
    originAt example12-world-Yᵀ Fin.zero (Fin.suc Fin.zero)
example12-Z-to-Y-origin-determined =
  origin-determined example12-rebase-Z-to-Yᵀ

example12-nat-X-to-Y-origin-determined :
  Ex12.example12-nat-chain-world-X ≡
    originAt example12-nat-world-Yᵀ Fin.zero Fin.zero
example12-nat-X-to-Y-origin-determined =
  origin-determined example12-nat-rebase-X-to-Yᵀ


------------------------------------------------------------------------
-- Flags: no shortcut is inserted into the construction schedule
------------------------------------------------------------------------

zero≢suc : ∀ {n} {X : Fin.Fin n} → Fin.zero ≢ Fin.suc X
zero≢suc ()

example12-X≢Z : Ex12.example12-world-X ≢ Ex12.example12-world-Z
example12-X≢Z eq =
  zero≢suc
    (cong
      (λ W → toRenameᵗ (CTX.ηᴸʷ W) Fin.zero)
      eq)

example12-X-to-Y-not-origin-determined :
  ¬ (Ex12.example12-world-X ≡
    originAt example12-world-Yᵀ Fin.zero (Fin.suc Fin.zero))
example12-X-to-Y-not-origin-determined eq =
  example12-X≢Z
    (trans eq
      (originAt-edge world-builder Ex2.example12-rebase-Z-to-Y stationary))

terminus-stationary-Wᵀ : ScheduledWorld 1 2 2
terminus-stationary-Wᵀ = stationaryWorld T6.InstanceB.W

terminus-W≢Wᵖ : T6.InstanceB.W ≢ T6.InstanceB.Wᵖ
terminus-W≢Wᵖ eq =
  zero≢suc
    (cong
      (λ W → toRenameᵗ (CTX.ηᴸʷ W) T6.InstanceB.X)
      eq)

terminus-chain-not-origin-determined :
  ¬ (T6.InstanceB.Wᵖ ≡
    originAt terminus-stationary-Wᵀ T6.InstanceB.X T6.InstanceB.Y)
terminus-chain-not-origin-determined eq =
  terminus-W≢Wᵖ
    (sym (trans eq
      (originAt-stationary {W = T6.InstanceB.W}
        {Xᴸ = T6.InstanceB.X} {Xᴿ = T6.InstanceB.Y})))


------------------------------------------------------------------------
-- Machine-readable Stage 2 verdict ledger
------------------------------------------------------------------------

data ProducerStatus : Set where
  PROVEN-IN-SANDBOX : ProducerStatus
  FLAG:chain : ProducerStatus
  FLAG:D16-blocked : ProducerStatus

same-world-constructor-status : ProducerStatus
same-world-constructor-status = PROVEN-IN-SANDBOX

example12-X-to-Z-status : ProducerStatus
example12-X-to-Z-status = PROVEN-IN-SANDBOX

example12-Z-to-Y-status : ProducerStatus
example12-Z-to-Y-status = PROVEN-IN-SANDBOX

example12-nat-X-to-Y-status : ProducerStatus
example12-nat-X-to-Y-status = PROVEN-IN-SANDBOX

example12-X-to-Y-status : ProducerStatus
example12-X-to-Y-status = FLAG:chain

calibration-direct-producers-status : ProducerStatus
calibration-direct-producers-status = FLAG:D16-blocked

terminus-chain-status : ProducerStatus
terminus-chain-status = FLAG:D16-blocked

smart-comma-producers-status : ProducerStatus
smart-comma-producers-status = PROVEN-IN-SANDBOX

inst-inversion-route-producers-status : ProducerStatus
inst-inversion-route-producers-status = PROVEN-IN-SANDBOX

center-rename-producer-status : ProducerStatus
center-rename-producer-status = PROVEN-IN-SANDBOX

coherent-decay-producer-status : ProducerStatus
coherent-decay-producer-status = PROVEN-IN-SANDBOX

independent-decay-producer-status : ProducerStatus
independent-decay-producer-status = FLAG:chain

target-bind-lift-producers-status : ProducerStatus
target-bind-lift-producers-status = PROVEN-IN-SANDBOX

target-extend-producers-status : ProducerStatus
target-extend-producers-status = PROVEN-IN-SANDBOX

strip-chain-direct-producers-status : ProducerStatus
strip-chain-direct-producers-status = FLAG:chain

finite-same-world-producers-status : ProducerStatus
finite-same-world-producers-status = PROVEN-IN-SANDBOX

generic-strip-same-world-producers-status : ProducerStatus
generic-strip-same-world-producers-status = FLAG:chain

terminus-same-world-producers-status : ProducerStatus
terminus-same-world-producers-status = FLAG:D16-blocked

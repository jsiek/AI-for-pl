module T6D8a4PostMigrationOccurrenceProbe where

-- File Charter:
--   * Re-runs the D8a3 occurrence-feasibility counterexample after the D15
--     source-conceal migration.
--   * Reconstructs the old occurrence below the migrated function-conceal
--     shape and checks the result-witness obstruction.
--   * Checks both failure modes for the `seal X ★` open alternative: its
--     fixed star premise and its no-target-occupant gate.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (★; ＇_; `ℕ; ‵_; _⇒_)
open import Consistency using (toRenameᵗ)
open import Conversion using (Conv↓; unseal; _↦↓_; id↓)
import Imprecision as I
open import CastTerms using (Term; `_ ; ƛ_; _↓_)
import proof.DGG.CastTermImprecision2 as CTI2
import T6D8a2ClosedValueRebaseTransportProbe as P
import T6D8a4PostMigrationCallerSupplyProbe as Caller


root-context : CTI2.CtxImp P.W
root-context = CTI2.ctx-imp ★ ★ I.★⊑★ ∷ []

premise-context : CTI2.CtxImp P.Wᵖ
premise-context = CTI2.ctx-imp ★ ★ I.★⊑★ ∷ []

p-use : ★ CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ ★
p-use = I.★⊑★

p-premise-function :
  ((‵ `ℕ) ⇒ ★) CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ (★ ⇒ ★)
p-premise-function = I.⇒⊑⇒ I.ι⊑★ I.★⊑★

source-core : Term 1
source-core = ƛ (` 1)

target-core : Term 2
target-core = ƛ (` 1)

use-relation :
  P.Wᵖ CTI2.∣
    (CTI2.ctx-imp (‵ `ℕ) ★ I.ι⊑★ ∷ premise-context)
    ⊢² ` 1 ⊑ ` 1 ∶ p-use
use-relation = CTI2.x⊑x² (CTI2.Sʷ CTI2.Zʷ)

core-at-premise :
  P.Wᵖ CTI2.∣ premise-context ⊢²
    source-core ⊑ target-core ∶ p-premise-function
core-at-premise = CTI2.ƛ⊑ƛ² use-relation

source-ok-wrapper :
  Conv↓ 1 ((‵ `ℕ) ⇒ ★) ((＇ P.X) ⇒ ★)
source-ok-wrapper = unseal P.X (‵ `ℕ) ↦↓ id↓ ★

source-ok-wrapper-typed :
  CTI2.sourceStoreʷ P.W CTI2.⊢↓[ just P.X ] source-ok-wrapper
source-ok-wrapper-typed =
  CTI2.⊢↓-⇒ˣ CTI2.join-left
    (CTI2.⊢↑-unsealˣ P.source-entry) CTI2.⊢↓-idˣ

source-ok-body : Term 1
source-ok-body = source-core ↓ source-ok-wrapper

source-ok-root-type-empty :
  ((＇ P.X) ⇒ ★) CTI2.⊑ᵂ⟨ P.W ⟩ (★ ⇒ ★)
  → ⊥
source-ok-root-type-empty (I.⇒⊑⇒ (I.X⊑★ ()) pB)

source-ok-body-at-old-root-empty :
  ∀ {q : ((＇ P.X) ⇒ ★) CTI2.⊑ᵂ⟨ P.W ⟩ (★ ⇒ ★)}
  → P.W CTI2.∣ root-context ⊢²
      source-ok-body ⊑ target-core ∶ q
  → ⊥
source-ok-body-at-old-root-empty {q = q} rel =
  source-ok-root-type-empty q

harvested-obligation-still-empty :
  P.Wᵖ CTI2.∣ [] ⊢²
    Caller.source-argument ⊑ Caller.target-argument ∶ p-use
  → ⊥
harvested-obligation-still-empty = Caller.argument-at-Wᵖ-empty

open-premise-against-function-empty :
  ★ CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ (★ ⇒ ★)
  → ⊥
open-premise-against-function-empty ()

premise-source-pivot-occupied :
  CTI2.Occupied P.Wᵖ
    (toRenameᵗ (CTI2.ηᴸʷ P.Wᵖ) P.X)
premise-source-pivot-occupied = P.Y-fresh , refl

open-gate-at-premise-empty :
  CTI2.NoTargetOccupantAtSource P.Wᵖ P.X
  → ⊥
open-gate-at-premise-empty no-target =
  no-target premise-source-pivot-occupied

open-result-at-old-root-empty :
  (＇ P.X) CTI2.⊑ᵂ⟨ P.W ⟩ ★
  → ⊥
open-result-at-old-root-empty (I.X⊑★ ())

OccurrencePostMigrationVerdict : Set
OccurrencePostMigrationVerdict =
  (∀ {q : ((＇ P.X) ⇒ ★) CTI2.⊑ᵂ⟨ P.W ⟩ (★ ⇒ ★)}
    → P.W CTI2.∣ root-context ⊢²
        source-ok-body ⊑ target-core ∶ q
    → ⊥)
  × (★ CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ (★ ⇒ ★) → ⊥)
  × (CTI2.NoTargetOccupantAtSource P.Wᵖ P.X → ⊥)

occurrence-post-migration-verdict : OccurrencePostMigrationVerdict
occurrence-post-migration-verdict =
  source-ok-body-at-old-root-empty ,
  open-premise-against-function-empty ,
  open-gate-at-premise-empty

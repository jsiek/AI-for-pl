module T10Probe1ParkedWorldPreservation where

-- File Charter:
--   * Calibration probe for the D6 parked-world preservation questions.
--   * Builds one finite parked world `W` and one finite non-parked world
--     `Wᵖ` connected by forward and reversed rebase witnesses.
--   * The checked `ParkedWorld Wᵖ -> ⊥` refutes all four candidate
--     preservation statements without changing the live DGG development.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (TyVar; ★)
open import TyStore using (store-empty; store-bind)
open import Consistency using (empty; keep; skip; toRenameᵗ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; instᵐ; ★⊑★)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CompilePreservesImprecision2 as CPI2
open import proof.DGG.Parked.ParkedWorldDef using
  ( ParkedWorld
  ; parked-initial
  ; parked-both-bind
  ; parked-left-bind
  ; parked-right-bind
  )


empty-μ : ImpEnv 0
empty-μ ()

W₀ : CTI2.World 0 0 0
W₀ = CPI2.initialWorld empty-μ store-empty

W-paired : CTI2.World 1 1 1
W-paired = CTI2.bothBindWorld X⊑X W₀ ★ ★

W : CTI2.World 1 2 2
W = CTI2.rightOnlyWorld W-paired ★

parked-W : ParkedWorld W
parked-W = parked-right-bind (parked-both-bind parked-initial)

source-store : TyStore.TyStore 1
source-store = store-bind store-empty ★

target-store : TyStore.TyStore 2
target-store = store-bind (store-bind store-empty ★) ★

mark-X⊑★ : VarImp
mark-X⊑★ = X⊑★

mark-X⊑X : VarImp
mark-X⊑X = X⊑X

mark-X⊑★≢mark-X⊑X : mark-X⊑★ ≢ mark-X⊑X
mark-X⊑★≢mark-X⊑X ()

μ : ImpEnv 2
μ = instᵐ (extendᵐ X⊑X empty-μ)

ηᴸ-fresh : 1 Consistency.↪ᵗ 2
ηᴸ-fresh = keep empty

ηᴿ-id : 2 Consistency.↪ᵗ 2
ηᴿ-id = keep (keep empty)

Wᵖ : CTI2.World 1 2 2
Wᵖ = CTI2.world ηᴸ-fresh ηᴿ-id μ source-store target-store

X : TyVar 1
X = Fin.zero

Y-fresh : TyVar 2
Y-fresh = Fin.zero

Y-old : TyVar 2
Y-old = Fin.suc Fin.zero

fresh-representation : CTI2.StoreRepImp Wᵖ X Y-fresh
fresh-representation = CTI2.store-rep-imp ★⊑★

old-representation : CTI2.StoreRepImp W X Y-old
old-representation = CTI2.store-rep-imp ★⊑★

forward-rebase : CTI2.RebaseAt W Wᵖ X Y-fresh
forward-rebase =
  CTI2.rebase-at (CTI2.same-runtime refl refl)
    (λ { {Fin.zero} X≢X → ⊥-elim (X≢X refl) })
    (λ { Fin.zero → refl ; (Fin.suc Fin.zero) → refl })
    refl fresh-representation

reversed-rebase : CTI2.RebaseAt Wᵖ W X Y-old
reversed-rebase =
  CTI2.rebase-at (CTI2.same-runtime refl refl)
    (λ { {Fin.zero} X≢X → ⊥-elim (X≢X refl) })
    (λ { Fin.zero → refl ; (Fin.suc Fin.zero) → refl })
    refl old-representation

parked-head00-precise : ∀ {W′ : CTI2.World 1 2 2}
  → ParkedWorld W′
  → toRenameᵗ (CTI2.ηᴸʷ W′) Fin.zero ≡ Fin.zero
  → toRenameᵗ (CTI2.ηᴿʷ W′) Fin.zero ≡ Fin.zero
  → CTI2.impEnvʷ W′ Fin.zero ≡ X⊑X
parked-head00-precise (parked-both-bind pw) src-zero tgt-zero = refl
parked-head00-precise (parked-left-bind pw) src-zero ()
parked-head00-precise (parked-right-bind pw) () tgt-zero

not-parked-Wᵖ : ParkedWorld Wᵖ → ⊥
not-parked-Wᵖ pw =
  mark-X⊑★≢mark-X⊑X (parked-head00-precise pw refl refl)

claim-a-refuted :
  (ParkedWorld W → CTI2.RebaseAtᴸ W Wᵖ (just X) → ParkedWorld Wᵖ) → ⊥
claim-a-refuted claim =
  not-parked-Wᵖ (claim parked-W (CTI2.rebase-varᴸ forward-rebase))

claim-b-refuted :
  (ParkedWorld W → CTI2.RebaseAtᴿ W Wᵖ (just Y-fresh)
    → ParkedWorld Wᵖ)
  → ⊥
claim-b-refuted claim =
  not-parked-Wᵖ (claim parked-W (CTI2.rebase-varᴿ forward-rebase))

claim-c-refuted :
  (ParkedWorld W → CTI2.TagRebaseAtᴸ W Wᵖ (just X) (just Y-fresh)
    → ParkedWorld Wᵖ)
  → ⊥
claim-c-refuted claim =
  not-parked-Wᵖ (claim parked-W (CTI2.tag-rebase-varᴸ forward-rebase))

claim-d-refuted :
  (ParkedWorld W → CTI2.TagRebaseAtᴸ Wᵖ W (just X) (just Y-old)
    → ParkedWorld Wᵖ)
  → ⊥
claim-d-refuted claim =
  not-parked-Wᵖ (claim parked-W (CTI2.tag-rebase-varᴸ reversed-rebase))

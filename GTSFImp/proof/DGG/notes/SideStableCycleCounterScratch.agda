module proof.DGG.notes.SideStableCycleCounterScratch where

-- File Charter:
--   * Checks the finite geometry behind the M5 side-stable map repark
--     blocker.
--   * Exhibits a source re-park that is valid before the right/left
--     exchange but whose exchanged counterpart would require a non-OPE
--     source embedding.
--   * This is a scratch note only; it does not change the live relation.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym)

open import Types
open import TyStore using (TyStore; store-empty; store-bind)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Imprecision using (ImpEnv; X⊑★; ★⊑★)
import proof.DGG.CastTermImprecision2 as CTI2


scratch-source-store : TyStore 2
scratch-source-store =
  store-bind (store-bind store-empty ★) ★


scratch-target-store : TyStore 1
scratch-target-store = store-bind store-empty ★


scratch-env : ImpEnv 3
scratch-env Fin.zero = X⊑★
scratch-env (Fin.suc Fin.zero) = X⊑★
scratch-env (Fin.suc (Fin.suc Fin.zero)) = X⊑★


scratch-source-before : 2 ↪ᵗ 3
scratch-source-before = keep (skip (keep empty))


scratch-source-after : 2 ↪ᵗ 3
scratch-source-after = keep (keep empty)


scratch-target-before : 1 ↪ᵗ 3
scratch-target-before = skip (keep empty)


scratch-source-exchanged : 2 ↪ᵗ 3
scratch-source-exchanged = skip (keep (keep empty))


scratch-target-exchanged : 1 ↪ᵗ 3
scratch-target-exchanged = keep (skip empty)


scratch-world-before : CTI2.World 2 1 3
scratch-world-before =
  CTI2.world scratch-source-before scratch-target-before scratch-env
    scratch-source-store scratch-target-store


scratch-world-after : CTI2.World 2 1 3
scratch-world-after =
  CTI2.world scratch-source-after scratch-target-before scratch-env
    scratch-source-store scratch-target-store


scratch-world-exchanged : CTI2.World 2 1 3
scratch-world-exchanged =
  CTI2.world scratch-source-exchanged scratch-target-exchanged scratch-env
    scratch-source-store scratch-target-store


scratch-representation :
  CTI2.StoreRepImp scratch-world-after (Fin.suc Fin.zero) Fin.zero
scratch-representation = CTI2.store-rep-imp ★⊑★


scratch-rebase-before :
  CTI2.RebaseAt scratch-world-before scratch-world-after
    (Fin.suc Fin.zero) Fin.zero
scratch-rebase-before =
  CTI2.rebase-at
    (CTI2.same-runtime refl refl)
    source-off
    (λ { Fin.zero → refl })
    refl
    scratch-representation
  where
  source-off : ∀ {Y : Fin.Fin 2}
    → Y ≢ Fin.suc Fin.zero
    → toRenameᵗ scratch-source-after Y
      ≡ toRenameᵗ scratch-source-before Y
  source-off {Fin.zero} _ = refl
  source-off {Fin.suc Fin.zero} Y≢ =
    ⊥-elim (Y≢ refl)


no-ope-10 : ∀ (η : 2 ↪ᵗ 3)
  → toRenameᵗ η Fin.zero ≡ Fin.suc Fin.zero
  → toRenameᵗ η (Fin.suc Fin.zero) ≡ Fin.zero
  → ⊥
no-ope-10 (skip (keep (keep empty))) refl ()
no-ope-10 (keep (skip (keep empty))) ()
no-ope-10 (keep (keep empty)) ()


zero≢one : (Fin.zero {n = 1}) ≢ (Fin.suc (Fin.zero {n = 0}))
zero≢one ()


scratch-rebase-after-impossible : ∀ {W′ : CTI2.World 2 1 3}
  → CTI2.RebaseAt scratch-world-exchanged W′
    (Fin.suc Fin.zero) Fin.zero
  → ⊥
scratch-rebase-after-impossible {W′ = W′}
    (CTI2.rebase-at runtime offL frozenR aligned reps) =
  no-ope-10 (CTI2.ηᴸʷ W′)
    (trans (offL {Y = Fin.zero {n = 1}} zero≢one) refl)
    (trans (trans aligned (frozenR (Fin.zero {n = 0}))) refl)

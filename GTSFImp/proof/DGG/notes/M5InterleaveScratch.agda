module M5InterleaveScratch where

-- File Charter:
--   * Notes scratch for the M5 depth-1 interleaving question.
--   * Enumerates the six legal top-down peel orders of two source-only
--     `Λ⊑²` heads and two right-only generated reveals.
--   * Records finite refutations for the current rules, plus the concrete
--     candidate world whose inner source binder enters at target center β.
--   * This file is not imported by the live development.
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/M5InterleaveScratch.agda`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)

open import Types using (Ty; ★; ＇_; _⇒_; `∀)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
import Imprecision as I
open import Imprecision using (_⊢_⊑_)
open import proof.ImprecisionConsistency using (fin-suc-injective)
import proof.DGG.CtxImp as CTI2

------------------------------------------------------------------------
-- Shared finite instance: no old names, target α then target β.
------------------------------------------------------------------------

empty-imp : I.ImpEnv 0
empty-imp ()

base-world : CTI2.World 0 0 0
base-world =
  CTI2.world empty empty empty-imp store-empty store-empty

post-world : CTI2.World 0 2 2
post-world =
  CTI2.rightOnlyWorld (CTI2.rightOnlyWorld base-world ★) (＇ Fin.zero)

order-L-world : CTI2.World 1 2 3
order-L-world = CTI2.liftWorldLeft post-world

order-LL-world : CTI2.World 2 2 4
order-LL-world = CTI2.liftWorldLeft order-L-world

target-β : Fin.Fin 2
target-β = Fin.zero

target-α : Fin.Fin 2
target-α = Fin.suc Fin.zero

bodyTy : Ty 2
bodyTy = ＇ Fin.zero ⇒ ★

midTy : Ty 2
midTy = ＇ (Fin.suc Fin.zero) ⇒ ★

all-star₃ : I.ImpEnv 3
all-star₃ _ = I.X⊑★

all-star₄ : I.ImpEnv 4
all-star₄ _ = I.X⊑★

target-store-βα : TyStore 2
target-store-βα =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

------------------------------------------------------------------------
-- Leaf refutations used by the order split.
------------------------------------------------------------------------

no-var0⊑var3 : ∀ {Δ}
    {μ : I.ImpEnv (suc (suc (suc (suc Δ))))}
  → μ ⊢ ＇ Fin.zero
      ⊑ ＇ (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  → ⊥
no-var0⊑var3 ()

var-⊑-cong : ∀ {Δ} {μ : I.ImpEnv Δ} {X X′ Y Y′}
  → X ≡ X′
  → Y ≡ Y′
  → μ ⊢ ＇ X ⊑ ＇ Y
  → μ ⊢ ＇ X′ ⊑ ＇ Y′
var-⊑-cong refl refl p = p

no-ope-0↦2-1↦0 : ∀ {Δ Δ′}
    {η : suc (suc Δ) ↪ᵗ suc (suc (suc Δ′))}
  → toRenameᵗ η Fin.zero ≡ Fin.suc (Fin.suc Fin.zero)
  → toRenameᵗ η (Fin.suc Fin.zero) ≡ Fin.zero
  → ⊥
no-ope-0↦2-1↦0 {η = keep η} ()
no-ope-0↦2-1↦0 {η = skip η} eq₀ ()

no-ope-0↦3-1↦1 : ∀ {Δ Δ′}
    {η : suc (suc Δ) ↪ᵗ suc (suc (suc (suc Δ′)))}
  → toRenameᵗ η Fin.zero
      ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
  → toRenameᵗ η (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
  → ⊥
no-ope-0↦3-1↦1 {η = keep η} ()
no-ope-0↦3-1↦1 {η = skip η} eq₀ eq₁ =
  no-ope-0↦2-1↦0 (fin-suc-injective eq₀)
    (fin-suc-injective eq₁)

no-right-reveal-before-source : ∀ {W′}
  → CTI2.RebaseAtᴿ post-world W′ (just target-α)
  → ⊥
no-right-reveal-before-source (CTI2.rebase-varᴿ {Xᴸ = ()} rb)

------------------------------------------------------------------------
-- The `L R ...` prefix: the outer reveal can peel, but the next inner
-- source/reveal obligation asks fresh source 0 to relate to target α at 3.
------------------------------------------------------------------------

order-LR-world : CTI2.World 1 2 3
order-LR-world =
  CTI2.world
    (skip (skip (keep empty)))
    (skip (keep (keep empty)))
    all-star₃
    (store-lift store-empty)
    target-store-βα

order-LR-outer-rebaseᴿ :
  CTI2.RebaseAtᴿ order-L-world order-LR-world
    (just target-α)
order-LR-outer-rebaseᴿ =
  CTI2.rebase-varᴿ
    (CTI2.rebase-at (CTI2.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTI2.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTI2.ηᴸʷ order-LR-world) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ order-L-world) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)

order-LR-inner-source-q-empty : ∀ {W′}
  → CTI2.RebaseAtᴿ order-L-world W′ (just target-α)
  → (`∀ bodyTy) CTI2.⊑ᵂ⟨ W′ ⟩ midTy
  → ⊥
order-LR-inner-source-q-empty (CTI2.rebase-varᴿ rb)
    (I.∀⊑ _ _ (I.⇒⊑⇒ bad _))
    rewrite CTI2.RebaseAt.ηᴿ-frozen rb target-α =
  no-var0⊑var3 bad

order-LRLR-dies-at-inner-Λ :
  (`∀ bodyTy) CTI2.⊑ᵂ⟨ order-LR-world ⟩ midTy → ⊥
order-LRLR-dies-at-inner-Λ =
  order-LR-inner-source-q-empty order-LR-outer-rebaseᴿ

order-LRRL-dies-at-inner-reveal :
  (`∀ bodyTy) CTI2.⊑ᵂ⟨ order-LR-world ⟩ midTy → ⊥
order-LRRL-dies-at-inner-reveal =
  order-LR-inner-source-q-empty order-LR-outer-rebaseᴿ

------------------------------------------------------------------------
-- The `L L R ...` prefix: if the outer reveal tries to rebase the inner
-- source binder to α, order preservation is impossible; if it rebases the
-- outer source binder, the inner reveal's type obligation is empty.
------------------------------------------------------------------------

order-LLR-world : CTI2.World 2 2 4
order-LLR-world =
  CTI2.world
    (keep (skip (skip (keep empty))))
    (skip (skip (keep (keep empty))))
    all-star₄
    (store-lift (store-lift store-empty))
    target-store-βα

order-LLR-outer-rebaseᴿ :
  CTI2.RebaseAtᴿ order-LL-world order-LLR-world
    (just target-α)
order-LLR-outer-rebaseᴿ =
  CTI2.rebase-varᴿ
    (CTI2.rebase-at (CTI2.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTI2.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.suc Fin.zero
    → toRenameᵗ (CTI2.ηᴸʷ order-LLR-world) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ order-LL-world) Y
  source-off {Fin.zero} neq = refl
  source-off {Fin.suc Fin.zero} neq = ⊥-elim (neq refl)

order-LL-inner-reveal-after-outer-empty : ∀ {W′}
  → CTI2.RebaseAtᴿ order-LL-world W′ (just target-α)
  → bodyTy CTI2.⊑ᵂ⟨ W′ ⟩ midTy
  → ⊥
order-LL-inner-reveal-after-outer-empty
    (CTI2.rebase-varᴿ {Xᴸ = Fin.zero} rb) q =
  no-ope-0↦3-1↦1
    (trans (CTI2.RebaseAt.pivotAligned rb)
      (CTI2.RebaseAt.ηᴿ-frozen rb target-α))
    (CTI2.RebaseAt.ηᴸ-off-pivot rb {Y = Fin.suc Fin.zero} (λ ()))
order-LL-inner-reveal-after-outer-empty
    (CTI2.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero} rb)
    (I.⇒⊑⇒ bad _) =
  no-var0⊑var3
    (var-⊑-cong
      (CTI2.RebaseAt.ηᴸ-off-pivot rb {Y = Fin.zero} (λ ()))
      (CTI2.RebaseAt.ηᴿ-frozen rb target-α)
      bad)

order-LLRR-dies-at-inner-reveal :
  bodyTy CTI2.⊑ᵂ⟨ order-LLR-world ⟩ midTy → ⊥
order-LLRR-dies-at-inner-reveal =
  order-LL-inner-reveal-after-outer-empty order-LLR-outer-rebaseᴿ

------------------------------------------------------------------------
-- The six syntactically legal top-down orders.
------------------------------------------------------------------------

data PeelOrder : Set where
  LLRR : PeelOrder
  LRLR : PeelOrder
  LRRL : PeelOrder
  RLLR : PeelOrder
  RLRL : PeelOrder
  RRLL : PeelOrder

data DiesWhere : PeelOrder → Set where
  dies-LLRR-inner-reveal : DiesWhere LLRR
  dies-LRLR-inner-Λ : DiesWhere LRLR
  dies-LRRL-inner-reveal : DiesWhere LRRL
  dies-RLLR-first-reveal : DiesWhere RLLR
  dies-RLRL-first-reveal : DiesWhere RLRL
  dies-RRLL-first-reveal : DiesWhere RRLL

all-orders-die : (o : PeelOrder) → DiesWhere o
all-orders-die LLRR = dies-LLRR-inner-reveal
all-orders-die LRLR = dies-LRLR-inner-Λ
all-orders-die LRRL = dies-LRRL-inner-reveal
all-orders-die RLLR = dies-RLLR-first-reveal
all-orders-die RLRL = dies-RLRL-first-reveal
all-orders-die RRLL = dies-RRLL-first-reveal

------------------------------------------------------------------------
-- Claim 2: candidate lift-at-existing-center layout is representable.
------------------------------------------------------------------------

candidate-ηᴸ : 2 ↪ᵗ 3
candidate-ηᴸ = keep (skip (keep empty))

candidate-ηᴿ : 2 ↪ᵗ 3
candidate-ηᴿ = keep (keep (skip empty))

candidate-μ : I.ImpEnv 3
candidate-μ Fin.zero = I.X⊑X
candidate-μ (Fin.suc Fin.zero) = I.X⊑★
candidate-μ (Fin.suc (Fin.suc Fin.zero)) = I.X⊑★

candidate-source-store : TyStore 2
candidate-source-store = store-lift (store-lift store-empty)

candidate-target-store : TyStore 2
candidate-target-store = target-store-βα

candidate-world : CTI2.World 2 2 3
candidate-world =
  CTI2.world candidate-ηᴸ candidate-ηᴿ candidate-μ
    candidate-source-store candidate-target-store

candidate-inner-maps-cβ :
  toRenameᵗ candidate-ηᴸ Fin.zero ≡ Fin.zero
candidate-inner-maps-cβ = refl

candidate-outer-maps-ℓout :
  toRenameᵗ candidate-ηᴸ (Fin.suc Fin.zero)
    ≡ Fin.suc (Fin.suc Fin.zero)
candidate-outer-maps-ℓout = refl

candidate-β-maps-cβ :
  toRenameᵗ candidate-ηᴿ Fin.zero ≡ Fin.zero
candidate-β-maps-cβ = refl

candidate-α-maps-cα :
  toRenameᵗ candidate-ηᴿ (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
candidate-α-maps-cα = refl

candidate-β-store-entry :
  candidate-target-store ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
candidate-β-store-entry = Z∋ refl

candidate-α-store-entry :
  candidate-target-store ∋ Fin.suc Fin.zero ⦂ ★
candidate-α-store-entry = S-bind∋ (Z∋ refl) refl

candidate-cβ-mark :
  CTI2.impEnvʷ candidate-world Fin.zero ≡ I.X⊑X
candidate-cβ-mark = refl

candidate-ℓout-mark :
  CTI2.impEnvʷ candidate-world (Fin.suc (Fin.suc Fin.zero))
    ≡ I.X⊑★
candidate-ℓout-mark = refl

candidate-WFWorld : CTI2.WFWorld candidate-world
candidate-WFWorld Fin.zero eq = Fin.zero , refl
candidate-WFWorld (Fin.suc Fin.zero) ()

candidate-reveal-pivot-aligned :
  toRenameᵗ (CTI2.ηᴸʷ candidate-world) Fin.zero
    ≡ toRenameᵗ (CTI2.ηᴿʷ candidate-world) target-β
candidate-reveal-pivot-aligned = refl

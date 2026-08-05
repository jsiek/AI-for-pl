module proof.DGG.ExtraCastRight2Counterexample where

-- File Charter:
--   * Regression for the bare-seal case of right-injection inversion.
--   * Under the original design, where rebasing forced the premise and
--     conclusion worlds to agree on every imprecision mark, this file
--     proved a counterexample (commit 69fbef83): a valid input
--     derivation whose required output after target-tag cancellation
--     was uninhabited.  The culprit was a stale precise mark: the
--     outer conceal boundary rebases the target variable Y from U to
--     Z, leaving U precise but unaligned, and mark equality preserved
--     the staleness all the way down.
--   * The relation now carries ImpEnvMono instead: marks may decay
--     toward X⊑★ from conclusion to premise.  This file rebuilds the
--     same configuration and proves the previously-empty output
--     derivable, by descending into a dynamized premise world.
--   * Ties in the WFWorld invariant: the stale input world is not
--     mark-honest, the dynamized worlds are, and the repair is
--     exactly the re-marking that honesty demands.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; _!; id)
open import Imprecision
open import Conversion using (seal)
open import CastTerms
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _⊢↓[_]_; _∣_⊢²_⊑_∶_;
   RebaseAt; rebase-at; same-runtime; store-rep-imp; ⊢↓-sealˣ)

private
  Z : TyVar 2
  Z = Fin.zero

  U : TyVar 2
  U = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

source-store : TyStore 2
source-store = store-bind (store-bind store-empty (‵ `ℕ)) ★

target-store : TyStore 1
target-store = store-bind store-empty ★

source-Z∋ : source-store ∋ Z ⦂ ★
source-Z∋ = Z∋ refl

source-U∋ : source-store ∋ U ⦂ ‵ `ℕ
source-U∋ = S-bind∋ (Z∋ refl) refl

target-Y∋ : target-store ∋ Y ⦂ ★
target-Y∋ = Z∋ refl

source-η : 2 ↪ᵗ 2
source-η = keep (keep empty)

-- Before the outer Z/Y conceal boundary, Y is aligned with U.
target-η-U : 1 ↪ᵗ 2
target-η-U = skip (keep empty)

-- After that boundary, Y is aligned with Z.
target-η-Z : 1 ↪ᵗ 2
target-η-Z = keep empty

imp-env : ImpEnv 2
imp-env Fin.zero = X⊑★
imp-env (Fin.suc Fin.zero) = X⊑X

pre-world : World 2 1 2
pre-world = world source-η target-η-U imp-env source-store target-store

post-world : World 2 1 2
post-world = world source-η target-η-Z imp-env source-store target-store

Z-Y-representation : CTI2.StoreRepImp post-world Z Y
Z-Y-representation = store-rep-imp ★⊑★

Z-Y-rebase : RebaseAt pre-world post-world Z Y
Z-Y-rebase =
  rebase-at (same-runtime refl refl)
    (λ _ → refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) })
    refl
    Z-Y-representation

Z-seal-typed : source-store ⊢↓[ just Z ] seal Z ★
Z-seal-typed = ⊢↓-sealˣ source-Z∋

-- The three type obligations available at the conceal⊑² boundary of
-- the stale input.

premise-to-star : ★ ⊑ᵂ⟨ pre-world ⟩ ★
premise-to-star = ★⊑★

conclusion-to-star : ＇ Z ⊑ᵂ⟨ post-world ⟩ ★
conclusion-to-star = X⊑★ refl

conclusion-to-tag : ＇ Z ⊑ᵂ⟨ post-world ⟩ ＇ Y
conclusion-to-tag = X⊑X

-- In the stale pre-world, Y embeds with U, so the fourth obligation
-- that recursive inversion would want cannot be built there, and U's
-- precise mark also blocks the source-tag detour.  These two negative
-- facts are what made the original counterexample tick; they are
-- still true of the stale worlds and are kept as documentation.

no-premise-to-tag : ★ ⊑ᵂ⟨ pre-world ⟩ ＇ Y → ⊥
no-premise-to-tag ()

no-U-to-star : ＇ U ⊑ᵂ⟨ pre-world ⟩ ★ → ⊥
no-U-to-star (X⊑★ ())

-- The stale input world is not mark-honest: U's center is precise
-- but no target variable embeds there.

post-world-not-WF : CTI2.WFWorld post-world → ⊥
post-world-not-WF wf with wf U refl
post-world-not-WF wf | Fin.zero , ()

pre-world-WF : CTI2.WFWorld pre-world
pre-world-WF Fin.zero ()
pre-world-WF (Fin.suc Fin.zero) _ = Fin.zero , refl

------------------------------------------------------------------------
-- The stale input derivation
------------------------------------------------------------------------

U-Y-representation : CTI2.StoreRepImp pre-world U Y
U-Y-representation = store-rep-imp ι⊑★

U-Y-rebase : RebaseAt pre-world pre-world U Y
U-Y-rebase = CTI2.sameWorldRebaseAt refl U-Y-representation

source-U-seal-typed : source-store ⊢↓[ just U ] seal U (‵ `ℕ)
source-U-seal-typed = ⊢↓-sealˣ source-U∋

target-Y-seal-typed : target-store ⊢↓[ just Y ] seal Y ★
target-Y-seal-typed = ⊢↓-sealˣ target-Y∋

private
  source-env : Env∼ 2
  source-env _ = X∼★

  target-env : Env∼ 1
  target-env _ = X∼★

  ℕ! : target-env ⊢ (‵ `ℕ) ∼ ★
  ℕ! = id (‵ `ℕ) !

  U! : source-env ⊢ ＇ U ∼ ★
  U! = id {μ = source-env} (＇ U) !

  Y! : target-env ⊢ ＇ Y ∼ ★
  Y! = id {μ = target-env} (＇ Y) !

inner-base² : pre-world ∣ [] ⊢² $ (κℕ 0) ⊑ $ (κℕ 0) ∶ ι⊑ι
inner-base² = CTI2.κ⊑κ² (κℕ 0) ι⊑ι

inner-target-tag² : pre-world ∣ [] ⊢²
    $ (κℕ 0) ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ ι⊑★
inner-target-tag² = CTI2.⊑cast² ℕ! inner-base² ι⊑★

inner-seals² : pre-world ∣ [] ⊢²
    ($ (κℕ 0)) ↓ seal U (‵ `ℕ)
    ⊑ ($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★ ∶ X⊑X
inner-seals² =
  CTI2.conceal⊑conceal² (λ _ eq → eq) U-Y-rebase CTI2.same-[]
    source-U-seal-typed target-Y-seal-typed inner-target-tag² X⊑X

inner-paired-tags² : pre-world ∣ [] ⊢²
    (($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩
    ⊑ (($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★) ⟨ Y! ⟩ ∶ ★⊑★
inner-paired-tags² =
  CTI2.cast⊑cast² U! Y! inner-seals² ★⊑★

problematic-seal² : post-world ∣ [] ⊢²
    ((($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩) ↓ seal Z ★
    ⊑ (($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★) ⟨ Y! ⟩ ∶
      conclusion-to-star
problematic-seal² =
  CTI2.conceal⊑² (λ _ eq → eq) (CTI2.rebase-varᴸ Z-Y-rebase)
    CTI2.same-[] Z-seal-typed inner-paired-tags² conclusion-to-star

------------------------------------------------------------------------
-- The repair: descend into a mark-honest, dynamized premise world
------------------------------------------------------------------------

-- Re-marking U's center as dynamic records that below the Z/Y
-- boundary U has no target partner.  The dynamized worlds are
-- mark-honest, and ImpEnvMono admits the descent from the stale
-- conclusion world.

imp-env-dyn : ImpEnv 2
imp-env-dyn Fin.zero = X⊑★
imp-env-dyn (Fin.suc Fin.zero) = X⊑★

pre-worldᵈ : World 2 1 2
pre-worldᵈ =
  world source-η target-η-U imp-env-dyn source-store target-store

pre-worldᵈ-WF : CTI2.WFWorld pre-worldᵈ
pre-worldᵈ-WF Fin.zero ()
pre-worldᵈ-WF (Fin.suc Fin.zero) ()

dynamize : CTI2.ImpEnvMono post-world pre-worldᵈ
dynamize Fin.zero _ = refl
dynamize (Fin.suc Fin.zero) _ = refl

Z-Y-rebaseᵈ : RebaseAt pre-worldᵈ post-world Z Y
Z-Y-rebaseᵈ =
  rebase-at (same-runtime refl refl)
    (λ _ → refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) })
    refl
    Z-Y-representation

U-Y-representationᵈ : CTI2.StoreRepImp pre-worldᵈ U Y
U-Y-representationᵈ = store-rep-imp ι⊑★

U-Y-rebaseᵈ : RebaseAt pre-worldᵈ pre-worldᵈ U Y
U-Y-rebaseᵈ = CTI2.sameWorldRebaseAt refl U-Y-representationᵈ

-- The obligation that was empty in the stale pre-world is inhabited
-- in the dynamized one.

U-to-starᵈ : ＇ U ⊑ᵂ⟨ pre-worldᵈ ⟩ ★
U-to-starᵈ = X⊑★ refl

repaired-base² : pre-worldᵈ ∣ [] ⊢²
    $ (κℕ 0) ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ ι⊑★
repaired-base² = CTI2.⊑cast² ℕ! (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ι⊑★

repaired-seal² : pre-worldᵈ ∣ [] ⊢²
    ($ (κℕ 0)) ↓ seal U (‵ `ℕ) ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ U-to-starᵈ
repaired-seal² =
  CTI2.conceal⊑² (λ _ eq → eq) (CTI2.rebase-varᴸ U-Y-rebaseᵈ)
    CTI2.same-[] source-U-seal-typed repaired-base² U-to-starᵈ

repaired-tag² : pre-worldᵈ ∣ [] ⊢²
    (($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩ ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ ★⊑★
repaired-tag² = CTI2.cast⊑² U! repaired-seal² ★⊑★

-- The output relation demanded by right-injection inversion after the
-- target's Y! tag cancels.  Under mark equality this type was proved
-- empty; under monotone dynamization it is inhabited.

repaired-result² : post-world ∣ [] ⊢²
    ((($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩) ↓ seal Z ★
    ⊑ ($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★ ∶ conclusion-to-tag
repaired-result² =
  CTI2.conceal⊑conceal² dynamize Z-Y-rebaseᵈ CTI2.same-[]
    Z-seal-typed target-Y-seal-typed repaired-tag² conclusion-to-tag

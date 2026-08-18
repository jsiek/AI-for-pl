module proof.DGG.ExtraCastRight2Counterexample where

-- File Charter:
--   * Design record for the bare-seal stale-mark counterexample.
--   * The pre-M2 construction moved target variable `Y` from old source
--     center `U` to old source center `Z`.
--   * M2 removes that target-moving rebase: both the stale and dynamized
--     Z/Y outer rebases are empty by `ηᴿ-frozen`.
--   * The source-seal/direct-target repair attempted below is now a
--     design record of a removed admission: the source seal has
--     representation ℕ and the target partner is the bare `ℕ!` tag, so
--     the source-conceal side condition makes the shape empty.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
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

Z-Y-rebase-empty : RebaseAt pre-world post-world Z Y → ⊥
Z-Y-rebase-empty rb with CTI2.RebaseAt.ηᴿ-frozen rb Y
Z-Y-rebase-empty rb | ()

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
  CTI2.conceal⊑conceal²
    (CTI2.matched-seal-nonstar nonstar-ι)
    (λ _ eq → eq) U-Y-rebase CTI2.same-[]
    source-U-seal-typed target-Y-seal-typed inner-target-tag² X⊑X

inner-paired-tags² : pre-world ∣ [] ⊢²
    (($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩
    ⊑ (($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★) ⟨ Y! ⟩ ∶ ★⊑★
inner-paired-tags² =
  CTI2.cast⊑cast² U! Y! inner-seals² ★⊑★

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

Z-Y-rebaseᵈ-empty : RebaseAt pre-worldᵈ post-world Z Y → ⊥
Z-Y-rebaseᵈ-empty rb with CTI2.RebaseAt.ηᴿ-frozen rb Y
Z-Y-rebaseᵈ-empty rb | ()

U-Y-representationᵈ : CTI2.StoreRepImp pre-worldᵈ U Y
U-Y-representationᵈ = store-rep-imp ι⊑★

U-Y-rebaseᵈ : RebaseAt pre-worldᵈ pre-worldᵈ U Y
U-Y-rebaseᵈ = CTI2.sameWorldRebaseAt refl U-Y-representationᵈ

-- The obligation that was empty in the stale pre-world is inhabited
-- in the dynamized one.

U-to-starᵈ : ＇ U ⊑ᵂ⟨ pre-worldᵈ ⟩ ★
U-to-starᵈ = X⊑★ {X = U} refl

no-U-to-natᵈ : ＇ U ⊑ᵂ⟨ pre-worldᵈ ⟩ ‵ `ℕ → ⊥
no-U-to-natᵈ ()

no-star-to-natᵈ : ★ ⊑ᵂ⟨ pre-worldᵈ ⟩ ‵ `ℕ → ⊥
no-star-to-natᵈ ()

repaired-base² : pre-worldᵈ ∣ [] ⊢²
    $ (κℕ 0) ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ ι⊑★
repaired-base² = CTI2.⊑cast² ℕ! (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ι⊑★

repaired-seal-partner-empty : ∀ {Wᵖ : World 2 1 2} {P Xᴿ?}
  → CTI2.SourceConcealPartnerOK Wᵖ P (seal U (‵ `ℕ)) Xᴿ?
    (($ (κℕ 0)) ⟨ ℕ! ⟩)
  → ⊥
repaired-seal-partner-empty
    (CTI2.seal-partner-ok (CTI2.plain-target ()))

repaired-seal-ok-empty : ∀ {Wᵖ : World 2 1 2} {P Xᴿ?}
  → CTI2.SourceConcealOK Wᵖ P (seal U (‵ `ℕ)) Xᴿ?
    (($ (κℕ 0)) ⟨ ℕ! ⟩)
  → ⊥
repaired-seal-ok-empty
    (CTI2.seal-nonstar-plain-ok Rns ())

repaired-seal²-empty′ : ∀ {X}
  → (q : ＇ X ⊑ᵂ⟨ pre-worldᵈ ⟩ ★)
  → pre-worldᵈ ∣ [] ⊢²
      ($ (κℕ 0)) ↓ seal U (‵ `ℕ) ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ q
  → ⊥
repaired-seal²-empty′ q₀
    (CTI2.⊑cast² {p = p} c′ D .q₀) with p
repaired-seal²-empty′ (X⊑★ eq)
    (CTI2.⊑cast² {p = p} c′ D .(X⊑★ eq)) | ()
repaired-seal²-empty′ q₀
    (CTI2.conceal⊑² ok mono rb sc c⊢ D .q₀) =
  repaired-seal-partner-empty ok
repaired-seal²-empty′ q₀
    (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ D .q₀) =
  repaired-seal-ok-empty ok

repaired-seal²-empty :
  pre-worldᵈ ∣ [] ⊢²
    ($ (κℕ 0)) ↓ seal U (‵ `ℕ) ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶
      U-to-starᵈ
  → ⊥
repaired-seal²-empty = repaired-seal²-empty′ {X = U} U-to-starᵈ

repaired-tag²-empty :
  pre-worldᵈ ∣ [] ⊢²
    (($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩ ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ ★⊑★
  → ⊥
repaired-tag²-empty
    (CTI2.cast⊑cast² {C = ＇ .U} {C′ = ‵ `ℕ} {p = p}
      c c′ D .★⊑★) =
  no-U-to-natᵈ p
repaired-tag²-empty
    (CTI2.⊑cast² {A = ★} {B = ‵ `ℕ} {p = p} c′ D .★⊑★) =
  no-star-to-natᵈ p
repaired-tag²-empty
    (CTI2.cast⊑² {A = ＇ .U} {A′ = ★} {B = ★} {p = p}
      c D .★⊑★) =
  repaired-seal²-empty′ {X = U} p D

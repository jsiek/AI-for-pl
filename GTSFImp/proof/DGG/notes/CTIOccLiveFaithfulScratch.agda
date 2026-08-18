module CTIOccLiveFaithfulScratch where

-- File Charter:
--   * Notes-only S-OCC V1′ pre-flight scratch.
--   * Re-runs the occupancy calibration with LIVE-FAITHFUL cast rules:
--     `cast⊑castᴼ²`, `⊑castᴼ²`, and `cast⊑ᴼ²` carry only the bare
--     consistency derivation(s), premise relation, and conclusion witness.
--   * Keeps the adopted occupancy gate on the source-seal see-through
--     partner and checks the C1 reroutes plus generated/ground projection
--     catch-up by CTI inversion and syntactic analysis of consistency syntax.
--   * Divergence from live CTI2: the mini relation keeps the S-OCC scratch's
--     single-world/single-context conceal rules, rather than live CTI2's
--     W′/ImpEnvMono/Rebase/SameCtx transport premises.  The cast rule
--     premises are the part under review here and mirror the live shapes.
--     No live CTI2 or proof file is edited.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Data.Fin as Fin
import Data.Nat as Nat

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Consistency using
  (Env∼; X∼★; ★∼X; _⊢_∼_; _⊢_∼★; _⊢★∼_; _↪ᵗ_;
   ★∼Xᵍ; ★∼ι; empty; keep; id; idᵍ; _!; ？_; inst_; gen_)
open import Conversion using (seal)
import Conversion
open import Imprecision
open import CastTerms using
  (Term; Value; $; _⟨_⟩; _↓_; _《_》; inj)
import CastTerms as CT
open import Reduction using
  (StoreChanges; keep; _∷_; []; _—↠[_]_; _—→[_]⟨_⟩_; _∎[];
   pure-step; tag-untag)
open import Primitives using (κℕ)

import CTITighteningNarrowScratch as N
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.Imprecision as PI

open CTI2 using
  (World; world; CtxImp; _⊑ᵂ⟨_⟩_; RebaseAt; StoreRepImp;
   store-rep-imp)

------------------------------------------------------------------------
-- Occupancy states and partner gates
------------------------------------------------------------------------

data CellOccupancy : Set where
  source-only-cell : CellOccupancy
  target-occupied-cell : CellOccupancy

data NoTargetOccupant : CellOccupancy → Set where
  no-target-occupant : NoTargetOccupant source-only-cell

pre-occ : CellOccupancy
pre-occ = source-only-cell

aligned-occ : CellOccupancy
aligned-occ = target-occupied-cell

aligned-no-target-empty : NoTargetOccupant aligned-occ → ⊥
aligned-no-target-empty ()

data SealPartnerOKᴼ² {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (occ : CellOccupancy)
    (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-targetᴼ² : ∀ {P R Xᴿ? M′}
    → NoTargetOccupant occ
    → CTI2.Rep★PartnerOK W X P Xᴿ? M′
      ------------------------------------
    → SealPartnerOKᴼ² W occ X P R Xᴿ? M′

  plain-targetᴼ² : ∀ {P R Xᴿ? M′}
    → CTI2.NotTopTag M′
      ------------------------------------
    → SealPartnerOKᴼ² W occ X P R Xᴿ? M′

  name-protected-targetᴼ² : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → CTI2.CenterAligned W X Y
      ----------------------------------------------------
    → SealPartnerOKᴼ² W occ X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOKᴼ² {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (occ : CellOccupancy) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conversion.Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-okᴼ² : ∀ {P X R Xᴿ? M′}
    → SealPartnerOKᴼ² W occ X P R Xᴿ? M′
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ² W occ P (seal X R) Xᴿ? M′

  fun-conceal-targetᴼ² : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conversion.Conv↑ Δᴸ A′ A}
      {d : Conversion.Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ² W occ P (c Conversion.↦↓ d) Xᴿ? M′

  all-conceal-targetᴼ² : ∀ {P A B Xᴿ? M′}
      {c : Conversion.Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ² W occ P (Conversion.`∀↓ c) Xᴿ? M′

  id-conceal-targetᴼ² : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ² W occ P (Conversion.id↓ A) Xᴿ? M′

------------------------------------------------------------------------
-- LIVE-faithful S-OCC mini relation
------------------------------------------------------------------------

infix 4 _∣_⊢ᴼ²[_]_⊑_∶_

data _∣_⊢ᴼ²[_]_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) (occ : CellOccupancy) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  κ⊑κᴼ² : ∀ n
    → (p : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ))
      ----------------------------------------------------
    → W ∣ γ ⊢ᴼ²[ occ ] $ (κℕ n) ⊑ $ (κℕ n) ∶ p

  cast⊑castᴼ² : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      -------------------------------------
    → W ∣ γ ⊢ᴼ²[ occ ] M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑castᴼ² : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴿ}
    → (c′ : ν ⊢ B ∼ B′)
    → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ⟨ c′ ⟩ ∶ q

  cast⊑ᴼ² : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴸ}
    → (c : ν ⊢ A ∼ A′)
    → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢ᴼ²[ occ ] M ⟨ c ⟩ ⊑ M′ ∶ q

  conceal⊑ᴼ² : ∀
      {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W ⟩ B} {c : Conversion.Conv↓ Δᴸ A A′}
    → SourceConcealPartnerOKᴼ² W occ M c Xᴿ? M′
    → CTI2.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
    → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢ᴼ²[ occ ] M ↓ c ⊑ M′ ∶ q

  conceal⊑concealᴼ² : ∀
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ A′}
      {c : Conversion.Conv↓ Δᴸ A B}
      {c′ : Conversion.Conv↓ Δᴿ A′ B′}
    → CTI2.MatchedConcealPartnerOK W M c (just Xᴿ) M′
    → RebaseAt W W Xᴸ Xᴿ
    → CTI2.sourceStoreʷ W Conv.⊢↓[ just Xᴸ ] c
    → CTI2.targetStoreʷ W Conv.⊢↓[ just Xᴿ ] c′
    → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢ᴼ²[ occ ] M ↓ c ⊑ M′ ↓ c′ ∶ q

⊢ᴼ²-retarget : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {occ : CellOccupancy} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ p
  → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ q
⊢ᴼ²-retarget {W = W} {γ = γ} {occ = occ} {M = M}
    {M′ = M′} {p = p} {q = q} d =
  subst (λ r → W ∣ γ ⊢ᴼ²[ occ ] M ⊑ M′ ∶ r)
    (PI.⊑-unique p q) d

------------------------------------------------------------------------
-- A source-only pre-alignment world
------------------------------------------------------------------------

source-storeᵖ : TyStore 1
source-storeᵖ = store-bind store-empty ★

target-storeᵖ : TyStore 0
target-storeᵖ = store-empty

source-X∋ᵖ : source-storeᵖ ∋ Fin.zero ⦂ ★
source-X∋ᵖ = Z∋ refl

source-ηᵖ : 1 ↪ᵗ 1
source-ηᵖ = keep empty

target-ηᵖ : 0 ↪ᵗ 1
target-ηᵖ = empty

imp-envᵖ : ImpEnv 1
imp-envᵖ Fin.zero = X⊑★

Wᵖ : World 1 0 1
Wᵖ =
  world source-ηᵖ target-ηᵖ imp-envᵖ source-storeᵖ target-storeᵖ

X⊑★Wᵖ : ＇ Fin.zero ⊑ᵂ⟨ Wᵖ ⟩ ★
X⊑★Wᵖ = X⊑★ refl

source-seal-typedᵖ :
  source-storeᵖ Conv.⊢↓[ just Fin.zero ] seal Fin.zero ★
source-seal-typedᵖ = Conv.⊢↓-sealˣ source-X∋ᵖ

target-env-tagᵖ : Env∼ 0
target-env-tagᵖ ()

ℕ!ᵗᵖ : target-env-tagᵖ ⊢ (‵ `ℕ) ∼ ★
ℕ!ᵗᵖ = id (‵ `ℕ) !

raw-source : Term 1
raw-source = $ (κℕ 0)

raw-targetᵖ : Term 0
raw-targetᵖ = $ (κℕ 0)

base-targetᵖ : Term 0
base-targetᵖ = raw-targetᵖ ⟨ ℕ!ᵗᵖ ⟩

------------------------------------------------------------------------
-- C2 representatives in both occupancy regimes
------------------------------------------------------------------------

aligned-baseᴼ² : N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
  N.base-source ⊑ N.base-target ∶ ★⊑★
aligned-baseᴼ² =
  cast⊑castᴼ² N.ℕ!ˢ N.ℕ!ᵗ (κ⊑κᴼ² 0 ι⊑ι) ★⊑★

aligned-target-one-sided-baseᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ] raw-source ⊑ N.base-target ∶ ι⊑★
aligned-target-one-sided-baseᴼ² =
  ⊑castᴼ² N.ℕ!ᵗ (κ⊑κᴼ² 0 ι⊑ι) ι⊑★

aligned-source-one-sided-baseᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ] N.base-source ⊑ N.base-target ∶ ★⊑★
aligned-source-one-sided-baseᴼ² =
  cast⊑ᴼ² N.ℕ!ˢ aligned-target-one-sided-baseᴼ² ★⊑★

pre-baseᴼ² :
  Wᵖ ∣ [] ⊢ᴼ²[ pre-occ ] N.base-source ⊑ base-targetᵖ ∶ ★⊑★
pre-baseᴼ² =
  cast⊑castᴼ² N.ℕ!ˢ ℕ!ᵗᵖ (κ⊑κᴼ² 0 ι⊑ι) ★⊑★

pre-target-one-sided-baseᴼ² :
  Wᵖ ∣ [] ⊢ᴼ²[ pre-occ ] raw-source ⊑ base-targetᵖ ∶ ι⊑★
pre-target-one-sided-baseᴼ² =
  ⊑castᴼ² ℕ!ᵗᵖ (κ⊑κᴼ² 0 ι⊑ι) ι⊑★

pre-source-one-sided-baseᴼ² :
  Wᵖ ∣ [] ⊢ᴼ²[ pre-occ ] N.base-source ⊑ base-targetᵖ ∶ ★⊑★
pre-source-one-sided-baseᴼ² =
  cast⊑ᴼ² N.ℕ!ˢ pre-target-one-sided-baseᴼ² ★⊑★

------------------------------------------------------------------------
-- Positive aligned/pre-aligned controls
------------------------------------------------------------------------

prealignment-see-throughᴼ² :
  Wᵖ ∣ [] ⊢ᴼ²[ pre-occ ]
    N.source-sealed ⊑ base-targetᵖ ∶ X⊑★Wᵖ
prealignment-see-throughᴼ² =
  conceal⊑ᴼ² {Xᴸ? = just Fin.zero} {Xᴿ? = nothing}
    (seal-partner-okᴼ²
      (star-rep-targetᴼ² no-target-occupant
        (CTI2.rep★-nonvar-tag nonvar-base)))
    source-seal-typedᵖ pre-baseᴼ² X⊑★Wᵖ

prealignment-source-taggedᴼ² :
  Wᵖ ∣ [] ⊢ᴼ²[ pre-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⊑ base-targetᵖ ∶ ★⊑★
prealignment-source-taggedᴼ² =
  cast⊑ᴼ² N.X! prealignment-see-throughᴼ² ★⊑★

matching-outputᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ] N.source-sealed ⊑ N.target-sealed ∶ N.qXY
matching-outputᴼ² =
  conceal⊑concealᴼ²
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-nonvar-tag nonvar-base))
    N.X-Y-rebase N.source-seal-typed N.target-seal-typed
    aligned-baseᴼ² N.qXY

matching-inputᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
matching-inputᴼ² =
  ⊑castᴼ² N.Y! matching-outputᴼ² N.X⊑★W

matching-projectionᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
matching-projectionᴼ² =
  ⊑castᴼ² N.Y? matching-inputᴼ² N.qXY

good-generated-catchupᴼ²-live-replacement :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
good-generated-catchupᴼ²-live-replacement = matching-projectionᴼ²

------------------------------------------------------------------------
-- C1 emptiness and reroute closure in the aligned world
------------------------------------------------------------------------

aligned-seal-bare-partner-emptyᴼ² : ∀ {Xᴿ?}
  → SealPartnerOKᴼ² N.W aligned-occ Fin.zero
    N.base-source ★ Xᴿ? N.base-target
  → ⊥
aligned-seal-bare-partner-emptyᴼ² (star-rep-targetᴼ² no-target _) =
  aligned-no-target-empty no-target
aligned-seal-bare-partner-emptyᴼ² (plain-targetᴼ² ())

aligned-source-conceal-bare-emptyᴼ² : ∀ {Xᴿ?}
  → SourceConcealPartnerOKᴼ² N.W aligned-occ
    N.base-source (seal Fin.zero ★) Xᴿ? N.base-target
  → ⊥
aligned-source-conceal-bare-emptyᴼ²
    (seal-partner-okᴼ² partner) =
  aligned-seal-bare-partner-emptyᴼ² partner

bad-input-underivableᴼ² : ∀ {p : ＇ Fin.zero ⊑ᵂ⟨ N.W ⟩ ★}
  → N.W ∣ [] ⊢ᴼ²[ aligned-occ ] N.source-sealed
    ⊑ N.base-target ∶ p
  → ⊥
bad-input-underivableᴼ² (conceal⊑ᴼ² partner _ _ _) =
  aligned-source-conceal-bare-emptyᴼ² partner

route-X⊑X-variable-witness-closedᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ] N.source-sealed
    ⊑ N.base-target ∶ N.qXY
  → ⊥
route-X⊑X-variable-witness-closedᴼ²
    (conceal⊑ᴼ² partner _ _ _) =
  aligned-source-conceal-bare-emptyᴼ² partner

source-tagged-bare-underivableᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⊑ N.base-target ∶ ★⊑★
  → ⊥
source-tagged-bare-underivableᴼ²
    (cast⊑ᴼ² .N.X! prem _) =
  bad-input-underivableᴼ² prem

source-projected-bare-underivableᴼ² :
  ∀ {p : ＇ Fin.zero ⊑ᵂ⟨ N.W ⟩ ★}
  → N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ∶ p
  → ⊥
source-projected-bare-underivableᴼ²
    (cast⊑ᴼ² .N.X? prem _) =
  source-tagged-bare-underivableᴼ² (⊢ᴼ²-retarget prem)

bad-square-underivableᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ⟨ N.Y? ⟩ ∶ N.qXY
  → ⊥
bad-square-underivableᴼ²
    (cast⊑castᴼ² .N.X? .N.Y? prem _) =
  source-tagged-bare-underivableᴼ² (⊢ᴼ²-retarget prem)
bad-square-underivableᴼ²
    (⊑castᴼ² .N.Y? prem _) =
  source-projected-bare-underivableᴼ² prem

route-cast⊑-X!-then-X?-closedᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ⟨ N.Y? ⟩ ∶ N.qXY
  → ⊥
route-cast⊑-X!-then-X?-closedᴼ² = bad-square-underivableᴼ²

route-X⊑★-intermediate-closedᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ] N.source-sealed
    ⊑ N.base-target ∶ N.X⊑★W
  → ⊥
route-X⊑★-intermediate-closedᴼ² = bad-input-underivableᴼ²

route-★⊑★-intermediate-closedᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⊑ N.base-target ∶ ★⊑★
  → ⊥
route-★⊑★-intermediate-closedᴼ² = source-tagged-bare-underivableᴼ²

route-rep★-round-trip-closedᴼ² : ∀ {Xᴿ?}
  → SealPartnerOKᴼ² N.W aligned-occ Fin.zero
    (N.source-sealed ⟨ N.X! ⟩) ★ Xᴿ? N.base-target
  → ⊥
route-rep★-round-trip-closedᴼ² (star-rep-targetᴼ² no-target _) =
  aligned-no-target-empty no-target
route-rep★-round-trip-closedᴼ² (plain-targetᴼ² ())

var-tag-value-sealed-bare-target-closedᴼ² : ∀ {Xᴿ?}
  → SourceConcealPartnerOKᴼ² N.W aligned-occ
    (N.source-sealed ⟨ N.X! ⟩)
    (seal Fin.zero ★) Xᴿ? N.base-target
  → ⊥
var-tag-value-sealed-bare-target-closedᴼ²
    (seal-partner-okᴼ² partner) =
  route-rep★-round-trip-closedᴼ² partner

------------------------------------------------------------------------
-- Local values and projection routes
------------------------------------------------------------------------

source-base-valueᴼ² : Value N.base-source
source-base-valueᴼ² = $ (κℕ 0) 《 inj 》

source-sealed-valueᴼ² : Value N.source-sealed
source-sealed-valueᴼ² = source-base-valueᴼ² ↓ CT.seal

rawℕᴼ² : Term 1
rawℕᴼ² = $ (κℕ 0)

rawℕ-valueᴼ² : Value rawℕᴼ²
rawℕ-valueᴼ² = $ (κℕ 0)

target-Y-projection-routeᴼ² :
  N.target-name-tagged ⟨ N.Y? ⟩ —↠[ keep ∷ [] ] N.target-sealed
target-Y-projection-routeᴼ² =
  N.target-name-tagged ⟨ N.Y? ⟩
  —→[ keep ]⟨ pure-step (tag-untag N.target-sealed-value) ⟩
  N.target-sealed ∎[]

base-project-envᴼ² : Env∼ 1
base-project-envᴼ² _ = ★∼X

ℕ?ᴼ² : base-project-envᴼ² ⊢ ★ ∼ (‵ `ℕ)
ℕ?ᴼ² = ？ (idᵍ (‵ `ℕ))

ground-ℕ-projection-routeᴼ² :
  N.base-target ⟨ ℕ?ᴼ² ⟩ —↠[ keep ∷ [] ] rawℕᴼ²
ground-ℕ-projection-routeᴼ² =
  N.base-target ⟨ ℕ?ᴼ² ⟩
  —→[ keep ]⟨ pure-step (tag-untag rawℕ-valueᴼ²) ⟩
  rawℕᴼ² ∎[]

------------------------------------------------------------------------
-- Syntactic consistency views replacing TargetCastOK
------------------------------------------------------------------------

data VarTagCastSyntaxᴼ² (ν : Env∼ 1) :
    ν ⊢ ＇ Fin.zero ∼ ★ → Set where
  var-tag-cast-syntaxᴼ² :
      ∀ {Y∼★ : ν ⊢ (＇ Fin.zero) ∼★} {Ans}
    → VarTagCastSyntaxᴼ² ν
        (_! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = Y∼★ ⦄
          (id (＇ Fin.zero)) ⦃ Ans = Ans ⦄)

var-tag-cast-viewᴼ² : ∀ {ν : Env∼ 1}
  → (c : ν ⊢ ＇ Fin.zero ∼ ★)
  → VarTagCastSyntaxᴼ² ν c
var-tag-cast-viewᴼ²
    (_! ⦃ Gᵍ = ＇ .Fin.zero ⦄ (id (＇ .Fin.zero))) =
  var-tag-cast-syntaxᴼ²
var-tag-cast-viewᴼ²
    (_! {G = `∀ ★} (gen_ ⦃ z∈B = () ⦄ _ _))

data VarProjectCastSyntaxᴼ² (ν : Env∼ 1) :
    ν ⊢ ★ ∼ ＇ Fin.zero → Set where
  var-project-cast-syntaxᴼ² :
      ∀ {★∼Y : ν ⊢★∼ (＇ Fin.zero)} {Bns}
    → VarProjectCastSyntaxᴼ² ν
        (？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Y ⦄
          (id (＇ Fin.zero)) ⦃ Bns = Bns ⦄)

var-project-cast-viewᴼ² : ∀ {ν : Env∼ 1}
  → (c : ν ⊢ ★ ∼ ＇ Fin.zero)
  → VarProjectCastSyntaxᴼ² ν c
var-project-cast-viewᴼ²
    (？_ ⦃ Gᵍ = ＇ .Fin.zero ⦄ (id (＇ .Fin.zero))) =
  var-project-cast-syntaxᴼ²
var-project-cast-viewᴼ²
    (？_ {G = `∀ ★} (inst_ ⦃ z∈A = () ⦄ _ _))

data BaseTagCastSyntaxᴼ² (ν : Env∼ 1) :
    ν ⊢ (‵ `ℕ) ∼ ★ → Set where
  base-tag-cast-syntaxᴼ² :
      ∀ {ℕ∼★ : ν ⊢ (‵ `ℕ) ∼★} {Ans}
    → BaseTagCastSyntaxᴼ² ν
        (_! ⦃ Gᵍ = ‵ `ℕ ⦄ ⦃ G∼★ = ℕ∼★ ⦄
          (id (‵ `ℕ)) ⦃ Ans = Ans ⦄)

base-tag-cast-viewᴼ² : ∀ {ν : Env∼ 1}
  → (c : ν ⊢ (‵ `ℕ) ∼ ★)
  → BaseTagCastSyntaxᴼ² ν c
base-tag-cast-viewᴼ²
    (_! ⦃ Gᵍ = ‵ .`ℕ ⦄ (id (‵ .`ℕ))) =
  base-tag-cast-syntaxᴼ²
base-tag-cast-viewᴼ²
    (_! {G = `∀ ★} (gen_ ⦃ z∈B = () ⦄ _ _))

data BaseProjectCastSyntaxᴼ² (ν : Env∼ 1) :
    ν ⊢ ★ ∼ (‵ `ℕ) → Set where
  base-project-cast-syntaxᴼ² :
      ∀ {★∼ℕ : ν ⊢★∼ (‵ `ℕ)} {Bns}
    → BaseProjectCastSyntaxᴼ² ν
        (？_ ⦃ Gᵍ = ‵ `ℕ ⦄ ⦃ ★∼G = ★∼ℕ ⦄
          (id (‵ `ℕ)) ⦃ Bns = Bns ⦄)

base-project-cast-viewᴼ² : ∀ {ν : Env∼ 1}
  → (c : ν ⊢ ★ ∼ (‵ `ℕ))
  → BaseProjectCastSyntaxᴼ² ν c
base-project-cast-viewᴼ²
    (？_ ⦃ Gᵍ = ‵ .`ℕ ⦄ (id (‵ .`ℕ))) =
  base-project-cast-syntaxᴼ²
base-project-cast-viewᴼ²
    (？_ {G = `∀ ★} (inst_ ⦃ z∈A = () ⦄ _ _))

------------------------------------------------------------------------
-- Generated-name input inversion
------------------------------------------------------------------------

record ProjectionCatchupResultᴼ²
    (M′ : Term 1)
    (q : (＇ Fin.zero) ⊑ᵂ⟨ N.W ⟩ (＇ Fin.zero)) : Set where
  constructor projection-catchup-resultᴼ²
  field
    V′ : Term 1
    value′ : Value V′
    steps : M′ ⟨ N.Y? ⟩ —↠[ keep ∷ [] ] V′
    residual : N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
      N.source-sealed ⊑ V′ ∶ q

open ProjectionCatchupResultᴼ² public

base-source-to-target-sealed-emptyᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.base-source ⊑ N.target-sealed ∶ N.qXY
  → ⊥
base-source-to-target-sealed-emptyᴼ² ()

raw-source-to-target-sealed-emptyᴼ² :
  ∀ {p : (‵ `ℕ) ⊑ᵂ⟨ N.W ⟩ (＇ Fin.zero)}
  → N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    rawℕᴼ² ⊑ N.target-sealed ∶ p
  → ⊥
raw-source-to-target-sealed-emptyᴼ² {p = ()}

raw-source-to-target-name-tagged-emptyᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    rawℕᴼ² ⊑ N.target-name-tagged ∶ ι⊑★ {ι = `ℕ}
  → ⊥
raw-source-to-target-name-tagged-emptyᴼ²
    (⊑castᴼ² .N.Y! prem _) =
  raw-source-to-target-sealed-emptyᴼ² prem

base-source-to-target-name-tagged-emptyᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
    N.base-source ⊑ N.target-name-tagged ∶ ★⊑★
  → ⊥
base-source-to-target-name-tagged-emptyᴼ²
    (cast⊑ᴼ² .N.ℕ!ˢ prem _) =
  raw-source-to-target-name-tagged-emptyᴼ² (⊢ᴼ²-retarget prem)

aligned-Y-tag-input-inversionᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
      N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
  → Value N.target-name-tagged
  → ProjectionCatchupResultᴼ² N.target-name-tagged N.qXY
aligned-Y-tag-input-inversionᴼ²
    (⊑castᴼ² c′ prem _) _
    with var-tag-cast-viewᴼ² c′
aligned-Y-tag-input-inversionᴼ²
    (⊑castᴼ² c′ prem _) _ | var-tag-cast-syntaxᴼ² =
  projection-catchup-resultᴼ²
    N.target-sealed
    N.target-sealed-value
    target-Y-projection-routeᴼ²
    (⊢ᴼ²-retarget prem)
aligned-Y-tag-input-inversionᴼ²
    (conceal⊑ᴼ² (seal-partner-okᴼ² partner) _ prem _) vM′ =
  ⊥-elim (partner-empty partner (⊢ᴼ²-retarget prem) vM′)
  where
    partner-empty : ∀ {Xᴿ?}
      → SealPartnerOKᴼ² N.W aligned-occ Fin.zero
          N.base-source ★ Xᴿ? N.target-name-tagged
      → N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
          N.base-source ⊑ N.target-name-tagged ∶ ★⊑★
      → Value N.target-name-tagged
      → ⊥
    partner-empty (star-rep-targetᴼ² no-target _) _ _ =
      aligned-no-target-empty no-target
    partner-empty (plain-targetᴼ² ()) _ _
    partner-empty (name-protected-targetᴼ² _) prem _ =
      base-source-to-target-name-tagged-emptyᴼ² (⊢ᴼ²-retarget prem)

generated-Y-projection-catchupᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
      N.source-sealed ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
  → Value N.source-sealed
  → Value N.target-name-tagged
  → ProjectionCatchupResultᴼ² N.target-name-tagged N.qXY
generated-Y-projection-catchupᴼ²
    (⊑castᴼ² c′ prem _) _ vM′
    with var-project-cast-viewᴼ² c′
generated-Y-projection-catchupᴼ²
    (⊑castᴼ² c′ prem _) _ vM′ | var-project-cast-syntaxᴼ² =
  aligned-Y-tag-input-inversionᴼ² (⊢ᴼ²-retarget prem) vM′

generated-Y-projection-siteᴼ² :
  ProjectionCatchupResultᴼ² N.target-name-tagged N.qXY
generated-Y-projection-siteᴼ² =
  generated-Y-projection-catchupᴼ²
    matching-projectionᴼ² source-sealed-valueᴼ²
    (N.target-sealed-value 《 inj 》)

------------------------------------------------------------------------
-- Ground-tag projection
------------------------------------------------------------------------

ℕ⊑★ᴼ² : (‵ `ℕ) ⊑ᵂ⟨ N.W ⟩ ★
ℕ⊑★ᴼ² = ι⊑★ {ι = `ℕ}

ℕ⊑ℕᴼ² : (‵ `ℕ) ⊑ᵂ⟨ N.W ⟩ (‵ `ℕ)
ℕ⊑ℕᴼ² = ι⊑ι {ι = `ℕ}

record GroundProjectionCatchupResultᴼ² (M′ : Term 1) : Set where
  constructor ground-projection-catchup-resultᴼ²
  field
    V′ : Term 1
    value′ : Value V′
    steps : M′ ⟨ ℕ?ᴼ² ⟩ —↠[ keep ∷ [] ] V′
    residual : N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
      rawℕᴼ² ⊑ V′ ∶ ℕ⊑ℕᴼ²

open GroundProjectionCatchupResultᴼ² public

ground-ℕ-tag-input-inversionᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
      rawℕᴼ² ⊑ N.base-target ∶ ℕ⊑★ᴼ²
  → Value N.base-target
  → GroundProjectionCatchupResultᴼ² N.base-target
ground-ℕ-tag-input-inversionᴼ²
    (⊑castᴼ² c′ prem _) _
    with base-tag-cast-viewᴼ² c′
ground-ℕ-tag-input-inversionᴼ²
    (⊑castᴼ² c′ prem _) _ | base-tag-cast-syntaxᴼ² =
  ground-projection-catchup-resultᴼ²
    rawℕᴼ²
    rawℕ-valueᴼ²
    ground-ℕ-projection-routeᴼ²
    (⊢ᴼ²-retarget prem)

ground-ℕ-projection-catchupᴼ² :
  N.W ∣ [] ⊢ᴼ²[ aligned-occ ]
      rawℕᴼ² ⊑ N.base-target ⟨ ℕ?ᴼ² ⟩ ∶ ℕ⊑ℕᴼ²
  → Value rawℕᴼ²
  → Value N.base-target
  → GroundProjectionCatchupResultᴼ² N.base-target
ground-ℕ-projection-catchupᴼ²
    (⊑castᴼ² c′ prem _) _ vM′
    with base-project-cast-viewᴼ² c′
ground-ℕ-projection-catchupᴼ²
    (⊑castᴼ² c′ prem _) _ vM′ | base-project-cast-syntaxᴼ² =
  ground-ℕ-tag-input-inversionᴼ² (⊢ᴼ²-retarget prem) vM′

ground-ℕ-projection-siteᴼ² :
  GroundProjectionCatchupResultᴼ² N.base-target
ground-ℕ-projection-siteᴼ² =
  ground-ℕ-projection-catchupᴼ²
    (⊑castᴼ² ℕ?ᴼ² aligned-target-one-sided-baseᴼ² ℕ⊑ℕᴼ²)
    ($ (κℕ 0))
    N.base-target-value

------------------------------------------------------------------------
-- ExtraCastRight-style interface analogue
------------------------------------------------------------------------

record ExtraCastRightProjectionInputᴼ²
    (M M′ : Term 1)
    (p : (＇ Fin.zero) ⊑ᵂ⟨ N.W ⟩ ★)
    (q : (＇ Fin.zero) ⊑ᵂ⟨ N.W ⟩ (＇ Fin.zero)) : Set where
  constructor extra-cast-right-projection-inputᴼ²
  field
    premise : N.W ∣ [] ⊢ᴼ²[ aligned-occ ] M ⊑ M′ ∶ p
    source-value : Value M
    target-value : Value M′
    projection-result : ProjectionCatchupResultᴼ² M′ q

open ExtraCastRightProjectionInputᴼ² public

extra-cast-right-generated-Y-input-siteᴼ² :
  ExtraCastRightProjectionInputᴼ²
    N.source-sealed N.target-name-tagged N.X⊑★W N.qXY
extra-cast-right-generated-Y-input-siteᴼ² =
  extra-cast-right-projection-inputᴼ²
    matching-inputᴼ²
    source-sealed-valueᴼ²
    (N.target-sealed-value 《 inj 》)
    generated-Y-projection-siteᴼ²

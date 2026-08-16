module CTITighteningOccScratch where

-- File Charter:
--   * Notes-only calibration scratch for CTI tightening candidate S-OCC.
--   * Models two cell states: a source-only pre-alignment cell and the
--     runtime-aligned X/Y probe cell.
--   * Gates the source-seal star-representation see-through partner by
--     occupancy, while leaving ordinary cast witnesses, target projection
--     witnesses and matched seals unchanged; positive cast checkpoints now
--     use CTI reachability directly.
--   * Checks C1 emptiness/reroute closure and C2/C3 representative witnesses.
--     No live CTI2 or proof file is edited.

open import Data.Empty using (⊥)
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Consistency using
  (Env∼; X∼★; ★∼X; _⊢_∼_; _⊢_∼★; _⊢★∼_; _↪ᵗ_;
   empty; keep; toRenameᵗ; id; idᵍ; _!; ？_)
open import Conversion using (seal)
import Conversion
open import Imprecision
open import CastTerms using (Term; Value; _⟨_⟩; _↓_; _↑_; $)
import CastTerms as CT
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import CTITighteningNarrowScratch as N
import SourceReachabilityResultScratch as SR
import InitialPairScratch as IP

open CTI2 using
  (World; world; CtxImp; _⊑ᵂ⟨_⟩_; RebaseAt; StoreRepImp;
   store-rep-imp; ⊢↓-sealˣ)

------------------------------------------------------------------------
-- Occupancy states
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

------------------------------------------------------------------------
-- S-OCC seal partner discipline
------------------------------------------------------------------------

data SealPartnerOKᴼ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (occ : CellOccupancy)
    (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-targetᴼ : ∀ {P R Xᴿ? M′}
    → NoTargetOccupant occ
    → CTI2.Rep★PartnerOK W X P Xᴿ? M′
      ------------------------------------
    → SealPartnerOKᴼ W occ X P R Xᴿ? M′

  plain-targetᴼ : ∀ {P R Xᴿ? M′}
    → CTI2.NotTopTag M′
      ------------------------------------
    → SealPartnerOKᴼ W occ X P R Xᴿ? M′

  name-protected-targetᴼ : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → CTI2.CenterAligned W X Y
      ----------------------------------------------------
    → SealPartnerOKᴼ W occ X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOKᴼ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (occ : CellOccupancy) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conversion.Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-okᴼ : ∀ {P X R Xᴿ? M′}
    → SealPartnerOKᴼ W occ X P R Xᴿ? M′
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ W occ P (seal X R) Xᴿ? M′

  fun-conceal-targetᴼ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conversion.Conv↑ Δᴸ A′ A}
      {d : Conversion.Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ W occ P (c Conversion.↦↓ d) Xᴿ? M′

  all-conceal-targetᴼ : ∀ {P A B Xᴿ? M′}
      {c : Conversion.Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ W occ P (Conversion.`∀↓ c) Xᴿ? M′

  id-conceal-targetᴼ : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealPartnerOKᴼ W occ P (Conversion.id↓ A) Xᴿ? M′

------------------------------------------------------------------------
-- Miniature S-OCC relation
------------------------------------------------------------------------

infix 4 _∣_⊢ᴼ[_]_⊑_∶_

data _∣_⊢ᴼ[_]_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) (occ : CellOccupancy) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  κ⊑κᴼ : ∀ n
    → (p : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ))
      ----------------------------------------------------
    → W ∣ γ ⊢ᴼ[ occ ] $ (κℕ n) ⊑ $ (κℕ n) ∶ p

  cast⊑castᴼ : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
      {c : ν ⊢ C ∼ A} {c′ : ν′ ⊢ C′ ∼ A′}
    → N.PairedCastOK W {p = p} {q = q} c c′
    → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ p
      -------------------------------------
    → W ∣ γ ⊢ᴼ[ occ ] M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑castᴼ : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
      {ν : Env∼ Δᴿ} {c′ : ν ⊢ B ∼ B′}
    → N.TargetCastOK W {p = p} {q = q} c′
    → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ p
      -----------------------------
    → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ⟨ c′ ⟩ ∶ q

  cast⊑ᴼ : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
      {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ A′}
    → N.SourceCastOK W {p = p} {q = q} c
    → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ p
      -----------------------------
    → W ∣ γ ⊢ᴼ[ occ ] M ⟨ c ⟩ ⊑ M′ ∶ q

  conceal⊑ᴼ : ∀
      {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W ⟩ B} {c : Conversion.Conv↓ Δᴸ A A′}
    → SourceConcealPartnerOKᴼ W occ M c Xᴿ? M′
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
    → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢ᴼ[ occ ] M ↓ c ⊑ M′ ∶ q

  conceal⊑concealᴼ : ∀
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ A′}
      {c : Conversion.Conv↓ Δᴸ A B}
      {c′ : Conversion.Conv↓ Δᴿ A′ B′}
    → CTI2.MatchedConcealPartnerOK W M c (just Xᴿ) M′
    → RebaseAt W W Xᴸ Xᴿ
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ just Xᴸ ] c
    → CTI2.targetStoreʷ W CTI2.⊢↓[ just Xᴿ ] c′
    → W ∣ γ ⊢ᴼ[ occ ] M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢ᴼ[ occ ] M ↓ c ⊑ M′ ↓ c′ ∶ q

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
  source-storeᵖ CTI2.⊢↓[ just Fin.zero ] seal Fin.zero ★
source-seal-typedᵖ = ⊢↓-sealˣ source-X∋ᵖ

target-env-tagᵖ : Env∼ 0
target-env-tagᵖ ()

ℕ!ᵗᵖ : target-env-tagᵖ ⊢ (‵ `ℕ) ∼ ★
ℕ!ᵗᵖ = id (‵ `ℕ) !

ℕ!-shapeᵗᵖ : N.widening N.⊢ᶜ ℕ!ᵗᵖ ⦂ N.tagˢ (‵ `ℕ)
ℕ!-shapeᵗᵖ = N.shape-tag N.shape-idι

raw-source : Term 1
raw-source = $ (κℕ 0)

raw-targetᵖ : Term 0
raw-targetᵖ = $ (κℕ 0)

base-targetᵖ : Term 0
base-targetᵖ = raw-targetᵖ ⟨ ℕ!ᵗᵖ ⟩

------------------------------------------------------------------------
-- C2 representatives in both occupancy regimes
------------------------------------------------------------------------

aligned-baseᴼ : N.W ∣ [] ⊢ᴼ[ aligned-occ ]
  N.base-source ⊑ N.base-target ∶ ★⊑★
aligned-baseᴼ =
  cast⊑castᴼ
    (N.paired-widen-base-to★ N.ℕ!-shapeˢ N.ℕ!-shapeᵗ refl refl)
    (κ⊑κᴼ 0 ι⊑ι)

aligned-target-one-sided-baseᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ] raw-source ⊑ N.base-target ∶ ι⊑★
aligned-target-one-sided-baseᴼ =
  ⊑castᴼ (N.target-widen-base-to★ N.ℕ!-shapeᵗ refl refl)
    (κ⊑κᴼ 0 ι⊑ι)

aligned-source-one-sided-baseᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ] N.base-source ⊑ N.base-target ∶ ★⊑★
aligned-source-one-sided-baseᴼ =
  cast⊑ᴼ
    (N.source-widen-base-to★ N.ℕ!-shapeˢ refl refl)
    aligned-target-one-sided-baseᴼ

pre-baseᴼ :
  Wᵖ ∣ [] ⊢ᴼ[ pre-occ ] N.base-source ⊑ base-targetᵖ ∶ ★⊑★
pre-baseᴼ =
  cast⊑castᴼ
    (N.paired-widen-base-to★ N.ℕ!-shapeˢ ℕ!-shapeᵗᵖ refl refl)
    (κ⊑κᴼ 0 ι⊑ι)

pre-target-one-sided-baseᴼ :
  Wᵖ ∣ [] ⊢ᴼ[ pre-occ ] raw-source ⊑ base-targetᵖ ∶ ι⊑★
pre-target-one-sided-baseᴼ =
  ⊑castᴼ (N.target-widen-base-to★ ℕ!-shapeᵗᵖ refl refl)
    (κ⊑κᴼ 0 ι⊑ι)

pre-source-one-sided-baseᴼ :
  Wᵖ ∣ [] ⊢ᴼ[ pre-occ ] N.base-source ⊑ base-targetᵖ ∶ ★⊑★
pre-source-one-sided-baseᴼ =
  cast⊑ᴼ
    (N.source-widen-base-to★ N.ℕ!-shapeˢ refl refl)
    pre-target-one-sided-baseᴼ

------------------------------------------------------------------------
-- C3 pre-alignment and post-alignment good states
------------------------------------------------------------------------

prealignment-see-throughᴼ :
  Wᵖ ∣ [] ⊢ᴼ[ pre-occ ]
    N.source-sealed ⊑ base-targetᵖ ∶ X⊑★Wᵖ
prealignment-see-throughᴼ =
  conceal⊑ᴼ {Xᴸ? = just Fin.zero} {Xᴿ? = nothing}
    (seal-partner-okᴼ
      (star-rep-targetᴼ no-target-occupant
        (CTI2.rep★-nonvar-tag nonvar-base)))
    source-seal-typedᵖ pre-baseᴼ X⊑★Wᵖ

prealignment-source-taggedᴼ :
  Wᵖ ∣ [] ⊢ᴼ[ pre-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⊑ base-targetᵖ ∶ ★⊑★
prealignment-source-taggedᴼ =
  cast⊑ᴼ
    (N.source-widen-var-to★ N.X!-shape refl refl refl)
    prealignment-see-throughᴼ

matching-outputᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ] N.source-sealed ⊑ N.target-sealed ∶ N.qXY
matching-outputᴼ =
  conceal⊑concealᴼ
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-nonvar-tag nonvar-base))
    N.X-Y-rebase N.source-seal-typed N.target-seal-typed
    aligned-baseᴼ N.qXY

matching-inputᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
matching-inputᴼ =
  ⊑castᴼ (N.target-widen-var-to★ N.Y!-shape refl refl)
    matching-outputᴼ

matching-projectionᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
matching-projectionᴼ =
  ⊑castᴼ (N.target-narrow-★-to-var N.Y?-shape refl refl)
    matching-inputᴼ

good-generated-catchupᴼ-live-replacement :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
good-generated-catchupᴼ-live-replacement = matching-projectionᴼ

post-alignment-input-is-taggedᴼ :
  IP.Q-generated-tagged-input ≡ SR.target-sealed ⟨ IP.Q-Y! ⟩
post-alignment-input-is-taggedᴼ = SR.target-input-gate

target-catchup-routeᴼ = SR.target-route

------------------------------------------------------------------------
-- C1 emptiness and reroute closure in the aligned world
------------------------------------------------------------------------

aligned-seal-bare-partner-empty : ∀ {Xᴿ?}
  → SealPartnerOKᴼ N.W aligned-occ Fin.zero
    N.base-source ★ Xᴿ? N.base-target
  → ⊥
aligned-seal-bare-partner-empty (star-rep-targetᴼ no-target _) =
  aligned-no-target-empty no-target
aligned-seal-bare-partner-empty (plain-targetᴼ ())

aligned-source-conceal-bare-empty : ∀ {Xᴿ?}
  → SourceConcealPartnerOKᴼ N.W aligned-occ
    N.base-source (seal Fin.zero ★) Xᴿ? N.base-target
  → ⊥
aligned-source-conceal-bare-empty
    (seal-partner-okᴼ partner) =
  aligned-seal-bare-partner-empty partner

bad-input-underivableᴼ : ∀ {p : ＇ Fin.zero ⊑ᵂ⟨ N.W ⟩ ★}
  → N.W ∣ [] ⊢ᴼ[ aligned-occ ] N.source-sealed
    ⊑ N.base-target ∶ p
  → ⊥
bad-input-underivableᴼ (conceal⊑ᴼ partner _ _ _) =
  aligned-source-conceal-bare-empty partner

route-X⊑X-variable-witness-closedᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ] N.source-sealed
    ⊑ N.base-target ∶ N.qXY
  → ⊥
route-X⊑X-variable-witness-closedᴼ
    (conceal⊑ᴼ partner _ _ _) =
  aligned-source-conceal-bare-empty partner

source-tagged-bare-underivableᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⊑ N.base-target ∶ ★⊑★
  → ⊥
source-tagged-bare-underivableᴼ
    (cast⊑ᴼ (N.source-widen-var-to★ _ _ p≡ _) prem)
    rewrite p≡ =
  bad-input-underivableᴼ prem

source-projected-bare-underivableᴼ :
  ∀ {p : ＇ Fin.zero ⊑ᵂ⟨ N.W ⟩ ★}
  → N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ∶ p
  → ⊥
source-projected-bare-underivableᴼ
    (cast⊑ᴼ (N.source-narrow-★-to-var _ p≡ _ _) prem)
    rewrite p≡ =
  source-tagged-bare-underivableᴼ prem

bad-square-underivableᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ⟨ N.Y? ⟩ ∶ N.qXY
  → ⊥
bad-square-underivableᴼ
    (cast⊑castᴼ (N.paired-narrow-var-from★ _ _ p≡) prem)
    rewrite p≡ =
  source-tagged-bare-underivableᴼ prem
bad-square-underivableᴼ
    (⊑castᴼ (N.target-narrow-★-to-var _ _ _) prem) =
  source-projected-bare-underivableᴼ prem

route-cast⊑-X!-then-X?-closedᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ⟨ N.Y? ⟩ ∶ N.qXY
  → ⊥
route-cast⊑-X!-then-X?-closedᴼ = bad-square-underivableᴼ

route-X⊑★-intermediate-closedᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ] N.source-sealed
    ⊑ N.base-target ∶ N.X⊑★W
  → ⊥
route-X⊑★-intermediate-closedᴼ = bad-input-underivableᴼ

route-★⊑★-intermediate-closedᴼ :
  N.W ∣ [] ⊢ᴼ[ aligned-occ ]
    N.source-sealed ⟨ N.X! ⟩ ⊑ N.base-target ∶ ★⊑★
  → ⊥
route-★⊑★-intermediate-closedᴼ = source-tagged-bare-underivableᴼ

route-rep★-round-trip-closedᴼ : ∀ {Xᴿ?}
  → SealPartnerOKᴼ N.W aligned-occ Fin.zero
    (N.source-sealed ⟨ N.X! ⟩) ★ Xᴿ? N.base-target
  → ⊥
route-rep★-round-trip-closedᴼ (star-rep-targetᴼ no-target _) =
  aligned-no-target-empty no-target
route-rep★-round-trip-closedᴼ (plain-targetᴼ ())

var-tag-value-sealed-bare-target-closedᴼ : ∀ {Xᴿ?}
  → SourceConcealPartnerOKᴼ N.W aligned-occ
    (N.source-sealed ⟨ N.X! ⟩)
    (seal Fin.zero ★) Xᴿ? N.base-target
  → ⊥
var-tag-value-sealed-bare-target-closedᴼ
    (seal-partner-okᴼ partner) =
  route-rep★-round-trip-closedᴼ partner

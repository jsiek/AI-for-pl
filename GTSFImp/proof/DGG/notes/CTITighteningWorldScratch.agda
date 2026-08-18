module CTITighteningWorldScratch where

-- File Charter:
--   * Notes-only calibration scratch for CTI tightening candidate S-WORLD.
--   * Reuses the S-NARROW calibration world and terms, but gates world
--     endpoint witnesses through provenance/capability cells.
--   * Keeps ordinary cast rules type-level, with S-NARROW direction/shape
--     premises and no term-shaped generated-projection clause.
--   * Checks whether world-only tightening can block the C1 projection
--     mismatch without editing live CTI2 or DGG proof files.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (just)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Consistency using (Env∼; _⊢_∼_)
import Conversion
open import Imprecision
open import CastTerms using (Term; _⟨_⟩; _↓_; $)
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import CTITighteningNarrowScratch as N

open CTI2 using
  (World; CtxImp; _⊑ᵂ⟨_⟩_; RebaseAt; StoreRepImp)

------------------------------------------------------------------------
-- World-side provenance and capability discipline
------------------------------------------------------------------------

data BirthOrigin : Set where
  matched-birth : BirthOrigin
  source-only-birth : BirthOrigin

data CellMark : Set where
  mark-X⊑X : CellMark
  mark-X⊑★ : CellMark

data UseCapability : Set where
  matched-use : UseCapability
  source-star-use : UseCapability

data Occupancy : Set where
  matched-occupied : Occupancy
  source-open : Occupancy
  runtime-aligned : Occupancy

data CastAncestry : Set where
  no-cast-ancestry : CastAncestry
  matched-generated-cast : CastAncestry
  residual-after-cancel : CastAncestry

record CellProv : Set where
  constructor cell-prov
  field
    birth : BirthOrigin
    current : CellMark
    capability : UseCapability
    occupancy : Occupancy
    ancestry : CastAncestry

open CellProv public

decay-cell : CellProv → CellProv
decay-cell (cell-prov birth current capability occupancy ancestry) =
  cell-prov birth mark-X⊑★ capability occupancy ancestry

decay-preserves-capability : ∀ cell
  → capability (decay-cell cell) ≡ capability cell
decay-preserves-capability cell = refl

matched-cell : CellProv
matched-cell =
  cell-prov matched-birth mark-X⊑X matched-use matched-occupied
    no-cast-ancestry

probe-cell : CellProv
probe-cell =
  cell-prov source-only-birth mark-X⊑★ source-star-use runtime-aligned
    matched-generated-cast

probe-decay-preserves-capability :
  capability (decay-cell probe-cell) ≡ source-star-use
probe-decay-preserves-capability = refl

record SourceStarCapability (cell : CellProv) : Set where
  constructor source-star-capability
  field
    source-birth : birth cell ≡ source-only-birth
    source-current : current cell ≡ mark-X⊑★
    source-capability : capability cell ≡ source-star-use

probe-source-star-capability : SourceStarCapability probe-cell
probe-source-star-capability = source-star-capability refl refl refl

record RuntimeAlignment
    (W : World 1 1 1) (Xᴸ Xᴿ : TyVar 1) : Set where
  constructor runtime-alignment
  field
    cell : CellProv
    source-star : SourceStarCapability cell
    occupancy-witness : occupancy cell ≡ runtime-aligned
    store-witness : StoreRepImp W Xᴸ Xᴿ
    rebase-witness : RebaseAt W W Xᴸ Xᴿ
    cast-witness : ancestry cell ≡ matched-generated-cast

open RuntimeAlignment public

probe-runtime-alignment :
  RuntimeAlignment N.W Fin.zero Fin.zero
probe-runtime-alignment =
  runtime-alignment probe-cell probe-source-star-capability refl
    N.X-Y-representation N.X-Y-rebase refl

------------------------------------------------------------------------
-- Capability-gated uses of the probe world's endpoint witnesses
------------------------------------------------------------------------

data EndpointUseᵂ : ∀ {A B : Ty 1}
    → A ⊑ᵂ⟨ N.W ⟩ B → Set where

  use-★⊑★ : EndpointUseᵂ ★⊑★

  use-ι⊑ι : ∀ {ι}
    → EndpointUseᵂ (ι⊑ι {ι = ι})

  use-ι⊑★ : ∀ {ι}
    → EndpointUseᵂ (ι⊑★ {ι = ι})

  use-X⊑★ :
    SourceStarCapability probe-cell
      -----------------------------
    → EndpointUseᵂ N.X⊑★W

  use-runtime-aligned :
    RuntimeAlignment N.W Fin.zero Fin.zero
      ------------------------------------
    → EndpointUseᵂ N.qXY

-- A stricter matched-only reading of capability rejects the runtime-aligned
-- endpoint itself.  This blocks C1, but also blocks the good square.

data StrictEndpointUseᵂ : ∀ {A B : Ty 1}
    → A ⊑ᵂ⟨ N.W ⟩ B → Set where

  strict-use-★⊑★ : StrictEndpointUseᵂ ★⊑★

  strict-use-ι⊑ι : ∀ {ι}
    → StrictEndpointUseᵂ (ι⊑ι {ι = ι})

  strict-use-X⊑★ :
    SourceStarCapability probe-cell
      -----------------------------------
    → StrictEndpointUseᵂ N.X⊑★W

strict-runtime-endpoint-blocks-good-square :
  StrictEndpointUseᵂ N.qXY → ⊥
strict-runtime-endpoint-blocks-good-square ()

------------------------------------------------------------------------
-- S-NARROW cast premises, with every endpoint use capability-gated
------------------------------------------------------------------------

record SourceCastWorldOKᵂ
    {A A′ B : Ty 1} {μ : Env∼ 1}
    {p : A ⊑ᵂ⟨ N.W ⟩ B}
    {q : A′ ⊑ᵂ⟨ N.W ⟩ B}
    (c : μ ⊢ A ∼ A′) : Set where
  constructor source-cast-world-ok
  field
    premise-use : EndpointUseᵂ p
    conclusion-use : EndpointUseᵂ q
    shape-ok : N.SourceCastOK N.W {p = p} {q = q} c

record TargetCastWorldOKᵂ
    {A B B′ : Ty 1} {μ : Env∼ 1}
    {p : A ⊑ᵂ⟨ N.W ⟩ B}
    {q : A ⊑ᵂ⟨ N.W ⟩ B′}
    (c : μ ⊢ B ∼ B′) : Set where
  constructor target-cast-world-ok
  field
    premise-use : EndpointUseᵂ p
    conclusion-use : EndpointUseᵂ q
    shape-ok : N.TargetCastOK N.W {p = p} {q = q} c

record PairedCastWorldOKᵂ
    {C C′ A A′ : Ty 1} {μ μ′ : Env∼ 1}
    {p : C ⊑ᵂ⟨ N.W ⟩ C′}
    {q : A ⊑ᵂ⟨ N.W ⟩ A′}
    (c : μ ⊢ C ∼ A)
    (c′ : μ′ ⊢ C′ ∼ A′) : Set where
  constructor paired-cast-world-ok
  field
    premise-use : EndpointUseᵂ p
    conclusion-use : EndpointUseᵂ q
    shape-ok : N.PairedCastOK N.W {p = p} {q = q} c c′

target-project-Y?-OKᵂ :
  TargetCastWorldOKᵂ {p = N.X⊑★W} {q = N.qXY} N.Y?
target-project-Y?-OKᵂ =
  target-cast-world-ok
    (use-X⊑★ probe-source-star-capability)
    (use-runtime-aligned probe-runtime-alignment)
    (N.target-narrow-★-to-var N.Y?-shape refl refl)

------------------------------------------------------------------------
-- Miniature S-WORLD relation over the concrete probe world
------------------------------------------------------------------------

infix 4 _∣_⊢ᵂ_⊑_∶_

data _∣_⊢ᵂ_⊑_∶_ :
    (W : World 1 1 1) → CtxImp W → Term 1 → Term 1
    → {A B : Ty 1} → A ⊑ᵂ⟨ W ⟩ B → Set where

  κ⊑κᵂ : ∀ n
    → (p : (‵ `ℕ) ⊑ᵂ⟨ N.W ⟩ (‵ `ℕ))
    → EndpointUseᵂ p
      ----------------------------------------------------
    → N.W ∣ [] ⊢ᵂ $ (κℕ n) ⊑ $ (κℕ n) ∶ p

  cast⊑castᵂ : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ N.W ⟩ C′} {q : A ⊑ᵂ⟨ N.W ⟩ A′}
      {ν : Env∼ 1} {ν′ : Env∼ 1}
      {c : ν ⊢ C ∼ A} {c′ : ν′ ⊢ C′ ∼ A′}
    → PairedCastWorldOKᵂ {p = p} {q = q} c c′
    → N.W ∣ [] ⊢ᵂ M ⊑ M′ ∶ p
      -------------------------------------
    → N.W ∣ [] ⊢ᵂ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑castᵂ : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ N.W ⟩ B} {q : A ⊑ᵂ⟨ N.W ⟩ B′}
      {ν : Env∼ 1} {c′ : ν ⊢ B ∼ B′}
    → TargetCastWorldOKᵂ {p = p} {q = q} c′
    → N.W ∣ [] ⊢ᵂ M ⊑ M′ ∶ p
      -----------------------------
    → N.W ∣ [] ⊢ᵂ M ⊑ M′ ⟨ c′ ⟩ ∶ q

  cast⊑ᵂ : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ N.W ⟩ B} {q : A′ ⊑ᵂ⟨ N.W ⟩ B}
      {ν : Env∼ 1} {c : ν ⊢ A ∼ A′}
    → SourceCastWorldOKᵂ {p = p} {q = q} c
    → N.W ∣ [] ⊢ᵂ M ⊑ M′ ∶ p
      -----------------------------
    → N.W ∣ [] ⊢ᵂ M ⟨ c ⟩ ⊑ M′ ∶ q

  conceal⊑ᵂ : ∀ {M M′ A A′ B Xᴿ?}
      {p : A ⊑ᵂ⟨ N.W ⟩ B} {c : Conversion.Conv↓ 1 A A′}
    → CTI2.SourceConcealPartnerOK N.W M c Xᴿ? M′
    → CTI2.sourceStoreʷ N.W Conv.⊢↓[ just Fin.zero ] c
    → N.W ∣ [] ⊢ᵂ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ N.W ⟩ B)
    → EndpointUseᵂ q
      -----------------------------
    → N.W ∣ [] ⊢ᵂ M ↓ c ⊑ M′ ∶ q

  conceal⊑concealᵂ : ∀
      {M M′ A A′ B B′}
      {p : A ⊑ᵂ⟨ N.W ⟩ A′}
      {c : Conversion.Conv↓ 1 A B}
      {c′ : Conversion.Conv↓ 1 A′ B′}
    → CTI2.MatchedConcealPartnerOK N.W M c (just Fin.zero) M′
    → RebaseAt N.W N.W Fin.zero Fin.zero
    → CTI2.sourceStoreʷ N.W Conv.⊢↓[ just Fin.zero ] c
    → CTI2.targetStoreʷ N.W Conv.⊢↓[ just Fin.zero ] c′
    → N.W ∣ [] ⊢ᵂ M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ N.W ⟩ B′)
    → EndpointUseᵂ q
      -------------------------------------
    → N.W ∣ [] ⊢ᵂ M ↓ c ⊑ M′ ↓ c′ ∶ q

------------------------------------------------------------------------
-- C1/C2/C3 calibration witnesses
------------------------------------------------------------------------

baseᵂ : N.W ∣ [] ⊢ᵂ N.base-source ⊑ N.base-target ∶ ★⊑★
baseᵂ =
  cast⊑castᵂ
    (paired-cast-world-ok use-ι⊑ι use-★⊑★
      (N.paired-widen-base-to★ N.ℕ!-shapeˢ N.ℕ!-shapeᵗ refl refl))
    (κ⊑κᵂ 0 ι⊑ι use-ι⊑ι)

-- RESOLVED-BY-LG1: the world-only bad square depended on the live
-- source-seal/bare-target see-through partner for `N.base-target`.  That
-- direct partner is now closed by `N.aligned-live-bare-partner-empty`.

matching-outputᵂ :
  N.W ∣ [] ⊢ᵂ N.source-sealed ⊑ N.target-sealed ∶ N.qXY
matching-outputᵂ =
  conceal⊑concealᵂ
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-nonvar-tag nonvar-base))
    N.X-Y-rebase N.source-seal-typed N.target-seal-typed
    baseᵂ N.qXY (use-runtime-aligned probe-runtime-alignment)

matching-inputᵂ :
  N.W ∣ [] ⊢ᵂ N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
matching-inputᵂ =
  ⊑castᵂ
    (target-cast-world-ok
      (use-runtime-aligned probe-runtime-alignment)
      (use-X⊑★ probe-source-star-capability)
      (N.target-widen-var-to★ N.Y!-shape refl refl))
    matching-outputᵂ

matching-projectionᵂ :
  N.W ∣ [] ⊢ᵂ N.source-sealed
    ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
matching-projectionᵂ =
  ⊑castᵂ target-project-Y?-OKᵂ matching-inputᵂ

post-cancellation-residualᵂ :
  N.W ∣ [] ⊢ᵂ N.source-sealed ⊑ N.target-sealed ∶ N.qXY
post-cancellation-residualᵂ = matching-outputᵂ

compile-paired-base-siteᵂ :
  N.W ∣ [] ⊢ᵂ N.base-source ⊑ N.base-target ∶ ★⊑★
compile-paired-base-siteᵂ = baseᵂ

-- The source one-sided insertion into the bare target is closed by LG-1.

compile-target-one-sided-siteᵂ :
  N.W ∣ [] ⊢ᵂ N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
compile-target-one-sided-siteᵂ = matching-inputᵂ

good-generated-projection-siteᵂ :
  N.W ∣ [] ⊢ᵂ N.source-sealed
    ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
good-generated-projection-siteᵂ = matching-projectionᵂ

good-generated-catchupᵂ-live-replacement :
  N.W ∣ [] ⊢ᵂ N.source-sealed
    ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
good-generated-catchupᵂ-live-replacement = good-generated-projection-siteᵂ

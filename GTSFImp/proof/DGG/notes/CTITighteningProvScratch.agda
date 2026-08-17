module CTITighteningProvScratch where

-- File Charter:
--   * Notes-only calibration scratch for CTI tightening candidate S-PROV.
--   * Reuses the S-NARROW calibration world and runtime terms, but replaces
--     direction-only target projections with term-shaped provenance clauses.
--   * Checks that the projection mismatch is underivable, while the matching
--     generated-name projection and post-cancellation residual remain
--     derivable.  No live CTI2 or proof file is edited.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (just)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; _↪ᵗ_; id; idᵍ; _!; ？_;
   toRenameᵗ)
import Consistency as C
open import Conversion using (seal)
import Conversion
open import Imprecision
open import CastTerms using (Term; Value; _⟨_⟩; _↓_; $)
import CastTerms as CT
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import CTITighteningNarrowScratch as N

open CTI2 using
  (World; CtxImp; _⊑ᵂ⟨_⟩_; RebaseAt; StoreRepImp; store-rep-imp;
   ⊢↓-sealˣ)

------------------------------------------------------------------------
-- Miniature provenance carried by world cells
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

decayed-matched-cell : CellProv
decayed-matched-cell = decay-cell matched-cell

matched-decay-keeps-matched-use :
  capability decayed-matched-cell ≡ matched-use
matched-decay-keeps-matched-use = refl

runtime-aligned-cell : CellProv
runtime-aligned-cell =
  cell-prov source-only-birth mark-X⊑★ source-star-use runtime-aligned
    matched-generated-cast

record RuntimeAlignment {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor runtime-alignment
  field
    cell : CellProv
    occupancy-witness : occupancy cell ≡ runtime-aligned
    store-witness : StoreRepImp W Xᴸ Xᴿ
    rebase-witness : RebaseAt W W Xᴸ Xᴿ
    cast-witness : CastAncestry

open RuntimeAlignment public

X-Y-runtime-alignment : RuntimeAlignment N.W Fin.zero Fin.zero
X-Y-runtime-alignment =
  runtime-alignment runtime-aligned-cell refl N.X-Y-representation
    N.X-Y-rebase matched-generated-cast

------------------------------------------------------------------------
-- Restricted non-projection cast premises
------------------------------------------------------------------------

data TargetCastProvOK {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) :
    ∀ {A B B′ μ} {p : A ⊑ᵂ⟨ W ⟩ B}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
    → μ ⊢ B ∼ B′ → Set where

  target-idᴾ : ∀ {A B μ} {p q : A ⊑ᵂ⟨ W ⟩ B}
      {atom : Atom B}
      --------------------------------
    → TargetCastProvOK W {p = p} {q = q} (id {μ = μ} atom)

  target-widen-base-to★ᴾ : ∀ {μ ι}
      {p : (‵ ι) ⊑ᵂ⟨ W ⟩ (‵ ι)}
      {q : (‵ ι) ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ‵ ι ∼ ★}
    → N.widening N.⊢ᶜ c ⦂ N.tagˢ (‵ ι)
    → p ≡ ι⊑ι
    → q ≡ ι⊑★
      ------------------------------------
    → TargetCastProvOK W {p = p} {q = q} c

  target-widen-var-to★ᴾ : ∀ {X Y μ}
      {p : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ＇ Y ∼ ★}
    → N.widening N.⊢ᶜ c ⦂ N.tagˢ (＇ Y)
    → (mark :
        CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★)
    → q ≡ X⊑★ mark
      ------------------------------------
    → TargetCastProvOK W {p = p} {q = q} c

data PairedCastProvOK {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) :
    ∀ {C C′ A A′ μ μ′}
      {p : C ⊑ᵂ⟨ W ⟩ C′}
      {q : A ⊑ᵂ⟨ W ⟩ A′}
    → μ ⊢ C ∼ A
    → μ′ ⊢ C′ ∼ A′
    → Set where

  paired-idᴾ : ∀ {A B μ μ′}
      {p q : A ⊑ᵂ⟨ W ⟩ B} {atomA : Atom A} {atomB : Atom B}
      -------------------------------------------------------------
    → PairedCastProvOK W {p = p} {q = q}
        (id {μ = μ} atomA) (id {μ = μ′} atomB)

  paired-widen-base-to★ᴾ : ∀ {μ μ′ ι}
      {p : (‵ ι) ⊑ᵂ⟨ W ⟩ (‵ ι)}
      {q : ★ ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ‵ ι ∼ ★} {c′ : μ′ ⊢ ‵ ι ∼ ★}
    → N.widening N.⊢ᶜ c ⦂ N.tagˢ (‵ ι)
    → N.widening N.⊢ᶜ c′ ⦂ N.tagˢ (‵ ι)
    → p ≡ ι⊑ι
    → q ≡ ★⊑★
      ----------------------------------
    → PairedCastProvOK W {p = p} {q = q} c c′

------------------------------------------------------------------------
-- Miniature S-PROV relation
------------------------------------------------------------------------

infix 4 _∣_⊢ᴾ_⊑_∶_

mutual

  data TargetProjectionProv {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {A : Ty Δᴸ}
      (p : A ⊑ᵂ⟨ W ⟩ ★) :
      ∀ {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      → Term Δᴿ
      → ν ⊢ ★ ∼ B′
      → A ⊑ᵂ⟨ W ⟩ B′
      → Set where

    target-project-sameᴾ : ∀ {G : Ty Δᴿ} {μ ν : Env∼ Δᴿ}
        {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
        {★∼G : ν ⊢★∼ G} {N′ : Term Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ G}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → RuntimeAlignment W Xᴸ Xᴿ
      → Value N′
      → W ∣ γ ⊢ᴾ M ⊑
          N′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
              ⦃ C.ground-nonstar Gᵍ ⦄ ⟩ ∶ p
      → TargetProjectionProv p
          (N′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
              ⦃ C.ground-nonstar Gᵍ ⦄ ⟩)
          (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄)
          q

    target-project-residualᴾ : ∀ {G B′ : Ty Δᴿ}
        {μ ν : Env∼ Δᴿ} {Gᵍ : Ground G}
        {G∼★ : μ ⊢ G ∼★} {★∼G : ν ⊢★∼ G}
        {Bns : NonStar B′} {N′ : Term Δᴿ}
        {c′ : ν ⊢ G ∼ B′}
        {r : A ⊑ᵂ⟨ W ⟩ G} {q : A ⊑ᵂ⟨ W ⟩ B′}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → RuntimeAlignment W Xᴸ Xᴿ
      → Value N′
      → W ∣ γ ⊢ᴾ M ⊑
          N′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
              ⦃ C.ground-nonstar Gᵍ ⦄ ⟩ ∶ p
      → W ∣ γ ⊢ᴾ M ⊑ N′ ⟨ c′ ⟩ ∶ q
      → TargetProjectionProv p
          (N′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
              ⦃ C.ground-nonstar Gᵍ ⦄ ⟩)
          (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c′ ⦃ Bns ⦄)
          q

  data _∣_⊢ᴾ_⊑_∶_ {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
      Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B → Set where

    κ⊑κᴾ : ∀ n
      → (p : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ))
        ----------------------------------------------------
      → W ∣ γ ⊢ᴾ $ (κℕ n) ⊑ $ (κℕ n) ∶ p

    cast⊑castᴾ : ∀ {M M′ C C′ A A′}
        {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
        {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
        {c : ν ⊢ C ∼ A} {c′ : ν′ ⊢ C′ ∼ A′}
      → PairedCastProvOK W {p = p} {q = q} c c′
      → W ∣ γ ⊢ᴾ M ⊑ M′ ∶ p
        -------------------------------------
      → W ∣ γ ⊢ᴾ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

    ⊑castᴾ : ∀ {M M′ A B B′}
        {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
        {ν : Env∼ Δᴿ} {c′ : ν ⊢ B ∼ B′}
      → TargetCastProvOK W {p = p} {q = q} c′
      → W ∣ γ ⊢ᴾ M ⊑ M′ ∶ p
        -----------------------------
      → W ∣ γ ⊢ᴾ M ⊑ M′ ⟨ c′ ⟩ ∶ q

    ⊑projectᴾ : ∀ {M M′ A B′}
        {p : A ⊑ᵂ⟨ W ⟩ ★} {q : A ⊑ᵂ⟨ W ⟩ B′}
        {ν : Env∼ Δᴿ} {c′ : ν ⊢ ★ ∼ B′}
      → TargetProjectionProv {W = W} {γ = γ} {M = M} p M′ c′ q
        -----------------------------
      → W ∣ γ ⊢ᴾ M ⊑ M′ ⟨ c′ ⟩ ∶ q

    cast⊑ᴾ : ∀ {M M′ A A′ B}
        {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ A′}
      → N.SourceCastOK W {p = p} {q = q} c
      → W ∣ γ ⊢ᴾ M ⊑ M′ ∶ p
        -----------------------------
      → W ∣ γ ⊢ᴾ M ⟨ c ⟩ ⊑ M′ ∶ q

    conceal⊑ᴾ : ∀ {W′ : World Δᴸ Δᴿ Δ}
        {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conversion.Conv↓ Δᴸ A A′}
      → CTI2.SourceConcealPartnerOK W′ M c Xᴿ? M′
      → CTI2.ImpEnvMono W W′
      → CTI2.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
      → CTI2.SameCtx γ γ′
      → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
      → W′ ∣ γ′ ⊢ᴾ M ⊑ M′ ∶ p
      → (q : A′ ⊑ᵂ⟨ W ⟩ B)
        -----------------------------
      → W ∣ γ ⊢ᴾ M ↓ c ⊑ M′ ∶ q

    conceal⊑concealᴾ : ∀
        {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
        {M M′ A A′ B B′ Xᴸ Xᴿ}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
        {c : Conversion.Conv↓ Δᴸ A B}
        {c′ : Conversion.Conv↓ Δᴿ A′ B′}
      → CTI2.MatchedConcealPartnerOK Wᵖ M c (just Xᴿ) M′
      → CTI2.ImpEnvMono W Wᵖ
      → CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ
      → CTI2.SameCtx γ γᵖ
      → CTI2.sourceStoreʷ W CTI2.⊢↓[ just Xᴸ ] c
      → CTI2.targetStoreʷ W CTI2.⊢↓[ just Xᴿ ] c′
      → Wᵖ ∣ γᵖ ⊢ᴾ M ⊑ M′ ∶ p
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
        -------------------------------------
      → W ∣ γ ⊢ᴾ M ↓ c ⊑ M′ ↓ c′ ∶ q

------------------------------------------------------------------------
-- C1/C2/C3 calibration witnesses
------------------------------------------------------------------------

baseᴾ : N.W ∣ [] ⊢ᴾ N.base-source ⊑ N.base-target ∶ ★⊑★
baseᴾ =
  cast⊑castᴾ
    (paired-widen-base-to★ᴾ N.ℕ!-shapeˢ N.ℕ!-shapeᵗ refl refl)
    (κ⊑κᴾ 0 ι⊑ι)

-- RESOLVED-BY-LG1: the provenance-only bad input depended on the live
-- source-seal/bare-target see-through partner for `N.base-target`.  That
-- direct partner is now closed by `N.aligned-live-bare-partner-empty`.

matching-outputᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed ⊑ N.target-sealed ∶ N.qXY
matching-outputᴾ =
  conceal⊑concealᴾ
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-nonvar-tag nonvar-base))
    (λ _ eq → eq) N.X-Y-rebase CTI2.same-[]
    N.source-seal-typed N.target-seal-typed baseᴾ N.qXY

matching-inputᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
matching-inputᴾ =
  ⊑castᴾ (target-widen-var-to★ᴾ N.Y!-shape refl refl) matching-outputᴾ

matching-projectionᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed
    ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
matching-projectionᴾ =
  ⊑projectᴾ
    (target-project-sameᴾ X-Y-runtime-alignment N.target-sealed-value
      matching-inputᴾ)

post-cancellation-residualᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed ⊑ N.target-sealed ∶ N.qXY
post-cancellation-residualᴾ = matching-outputᴾ

bad-base-target-Y-project-clause-empty : ∀ {M}
    {p : ＇ Fin.zero ⊑ᵂ⟨ N.W ⟩ ★}
  → TargetProjectionProv {W = N.W} {γ = []} {M = M}
      p N.base-target N.Y? N.qXY
  → ⊥
bad-base-target-Y-project-clause-empty ()

bad-target-projection-underivable :
  N.W ∣ [] ⊢ᴾ N.source-sealed
    ⊑ N.base-target ⟨ N.Y? ⟩ ∶ N.qXY
  → ⊥
bad-target-projection-underivable
    (⊑projectᴾ projection) =
  bad-base-target-Y-project-clause-empty projection

bad-paired-projection-underivable :
  N.W ∣ [] ⊢ᴾ
    N.source-sealed ⟨ N.X! ⟩ ⟨ N.X? ⟩
    ⊑ N.base-target ⟨ N.Y? ⟩ ∶ N.qXY
  → ⊥
bad-paired-projection-underivable
    (⊑projectᴾ projection) =
  bad-base-target-Y-project-clause-empty projection

-- C2 representative compiler-emitted cast sites.  These cover the live
-- non-projection cast shapes: paired argument/primitive casts, source
-- one-sided insertion, and target one-sided insertion.  The audit note records
-- the separate dynamic-function projection caveat.

compile-paired-base-siteᴾ :
  N.W ∣ [] ⊢ᴾ N.base-source ⊑ N.base-target ∶ ★⊑★
compile-paired-base-siteᴾ = baseᴾ

-- The source one-sided insertion into the bare target is closed by LG-1.

compile-target-one-sided-siteᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed ⊑ N.target-name-tagged ∶ N.X⊑★W
compile-target-one-sided-siteᴾ = matching-inputᴾ

-- C3 runtime provenance checkpoints.

good-generated-projection-siteᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed
    ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
good-generated-projection-siteᴾ = matching-projectionᴾ

good-generated-catchupᴾ-live-replacement :
  N.W ∣ [] ⊢ᴾ N.source-sealed
    ⊑ N.target-name-tagged ⟨ N.Y? ⟩ ∶ N.qXY
good-generated-catchupᴾ-live-replacement = good-generated-projection-siteᴾ

residual-after-cancellation-siteᴾ :
  N.W ∣ [] ⊢ᴾ N.source-sealed ⊑ N.target-sealed ∶ N.qXY
residual-after-cancellation-siteᴾ = post-cancellation-residualᴾ

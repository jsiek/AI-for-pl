module M5SplitCalibrationScratch where

-- File Charter:
--   * Notes scratch for calibrating the M5 split finding against ES4 and the
--     source-left (SL) obstruction.
--   * Models S1, S2, and S3 at the finite center layouts from
--     M5-SPLIT-RAW-REPORT.md; no live relation constructor is edited here.
--   * S1/S2 are represented as Set-level candidate surfaces with explicit
--     split guards.  S3 is refuted by finite same-center and OPE failures.
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/M5SplitCalibrationScratch.agda`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Types using (Ty; ★; ＇_; _⇒_; `∀; _∈ᵗ_; var-∈; ∈-fun-left)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Term; Λ_; `_)
import Imprecision as I

import Conversion as Conv
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
import proof.DGG.Catchup.InstInversionDef as IID
import proof.DGG.Catchup.InstInversionProof as IIP
import proof.DGG.SmartCommaWitness as SC

------------------------------------------------------------------------
-- Shared finite target window.
------------------------------------------------------------------------

target-β : Fin.Fin 2
target-β = Fin.zero

target-α : Fin.Fin 2
target-α = Fin.suc Fin.zero

target-store-βα : TyStore 2
target-store-βα =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

target-β-entry :
  target-store-βα ∋ target-β ⦂ ＇ target-α
target-β-entry = Z∋ refl

target-α-entry :
  target-store-βα ∋ target-α ⦂ ★
target-α-entry = S-bind∋ (Z∋ refl) refl

all-star₃ : I.ImpEnv 3
all-star₃ _ = I.X⊑★

all-star₄ : I.ImpEnv 4
all-star₄ _ = I.X⊑★

shared-plus-left : I.ImpEnv 2
shared-plus-left Fin.zero = I.X⊑X
shared-plus-left (Fin.suc Fin.zero) = I.X⊑★

source-store₁ : TyStore 1
source-store₁ = store-lift store-empty

source-store₂ : TyStore 2
source-store₂ = store-lift source-store₁

target-store₁ : TyStore 1
target-store₁ = store-lift store-empty

------------------------------------------------------------------------
-- ES4 split placement: source α before target β/α.
------------------------------------------------------------------------

es4-source-split : 1 ↪ᵗ 3
es4-source-split = keep empty

es4-target-window : 2 ↪ᵗ 3
es4-target-window = skip (keep (keep empty))

es4-split-world : CTI2.World 1 2 3
es4-split-world =
  CTI2.world es4-source-split es4-target-window all-star₃
    source-store₁ target-store-βα

es4-split-WFWorld : CTI2.WFWorld es4-split-world
es4-split-WFWorld Fin.zero ()

es4-source-at-ℓᵢ :
  toRenameᵗ (CTI2.ηᴸʷ es4-split-world) Fin.zero ≡ Fin.zero
es4-source-at-ℓᵢ = refl

es4-target-β-at-cβ :
  toRenameᵗ (CTI2.ηᴿʷ es4-split-world) target-β
    ≡ Fin.suc Fin.zero
es4-target-β-at-cβ = refl

es4-target-α-at-cα :
  toRenameᵗ (CTI2.ηᴿʷ es4-split-world) target-α
    ≡ Fin.suc (Fin.suc Fin.zero)
es4-target-α-at-cα = refl

es4-source-β-separate :
  toRenameᵗ (CTI2.ηᴸʷ es4-split-world) Fin.zero
    ≢ toRenameᵗ (CTI2.ηᴿʷ es4-split-world) target-β
es4-source-β-separate ()

------------------------------------------------------------------------
-- SL input and post placements.
------------------------------------------------------------------------

sl-input-source : 2 ↪ᵗ 2
sl-input-source = keep (keep empty)

sl-input-target : 1 ↪ᵗ 2
sl-input-target = keep empty

sl-shared-input-world : CTI2.World 2 1 2
sl-shared-input-world =
  CTI2.world sl-input-source sl-input-target shared-plus-left
    source-store₂ target-store₁

sl-shared-input-WFWorld : CTI2.WFWorld sl-shared-input-world
sl-shared-input-WFWorld Fin.zero refl = Fin.zero , refl
sl-shared-input-WFWorld (Fin.suc Fin.zero) ()

sl-source-split : 2 ↪ᵗ 4
sl-source-split = keep (keep empty)

sl-target-window : 2 ↪ᵗ 4
sl-target-window = skip (skip (keep (keep empty)))

sl-split-post-world : CTI2.World 2 2 4
sl-split-post-world =
  CTI2.world sl-source-split sl-target-window all-star₄
    source-store₂ target-store-βα

sl-split-post-WFWorld : CTI2.WFWorld sl-split-post-world
sl-split-post-WFWorld Fin.zero ()
sl-split-post-WFWorld (Fin.suc Fin.zero) ()

sl-inner-at-ℓᵢ :
  toRenameᵗ (CTI2.ηᴸʷ sl-split-post-world) Fin.zero ≡ Fin.zero
sl-inner-at-ℓᵢ = refl

sl-prefix-at-ℓₒ :
  toRenameᵗ (CTI2.ηᴸʷ sl-split-post-world) (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
sl-prefix-at-ℓₒ = refl

sl-target-β-at-cβ :
  toRenameᵗ (CTI2.ηᴿʷ sl-split-post-world) target-β
    ≡ Fin.suc (Fin.suc Fin.zero)
sl-target-β-at-cβ = refl

sl-target-α-at-cα :
  toRenameᵗ (CTI2.ηᴿʷ sl-split-post-world) target-α
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
sl-target-α-at-cα = refl

sl-inner-β-separate :
  toRenameᵗ (CTI2.ηᴸʷ sl-split-post-world) Fin.zero
    ≢ toRenameᵗ (CTI2.ηᴿʷ sl-split-post-world) target-β
sl-inner-β-separate ()

------------------------------------------------------------------------
-- Generated reveal typing and split-guard bookkeeping.
------------------------------------------------------------------------

es4-source-body : Ty 1
es4-source-body = ＇ Fin.zero ⇒ ＇ Fin.zero

es4-target-body : Ty 2
es4-target-body = ＇ target-β ⇒ ＇ target-β

sl-source-body : Ty 2
sl-source-body = ＇ Fin.zero ⇒ ★

sl-target-body : Ty 2
sl-target-body = ＇ target-β ⇒ ★

record GeneratedReveals {Δᴸ Δ} (W : CTI2.World Δᴸ 2 Δ)
    (Bβ Bα : Ty 2) : Set where
  constructor generated-reveals
  field
    inner-⊢↑ :
      target-store-βα Conv.⊢↑[ just target-β ]
        〖 target-β , ＇ target-α ↑ Bβ 〗
    outer-⊢↑ :
      target-store-βα Conv.⊢↑[ just target-α ]
        〖 target-α , ★ ↑ Bα 〗
    β-dynamic :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴿʷ W) target-β) ≡ I.X⊑★
    α-dynamic :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴿʷ W) target-α) ≡ I.X⊑★

es4-reveals-ok :
  GeneratedReveals es4-split-world
    es4-target-body (＇ target-α ⇒ ＇ target-α)
es4-reveals-ok =
  generated-reveals
    (IIP.generated-reveal-⊢↑-present
      (∈-fun-left var-∈) target-β-entry)
    (IIP.generated-reveal-⊢↑-present
      (∈-fun-left var-∈) target-α-entry)
    refl refl

sl-reveals-ok :
  GeneratedReveals sl-split-post-world
    sl-target-body (＇ target-α ⇒ ★)
sl-reveals-ok =
  generated-reveals
    (IIP.generated-reveal-⊢↑-present
      (∈-fun-left var-∈) target-β-entry)
    (IIP.generated-reveal-⊢↑-present
      (∈-fun-left var-∈) target-α-entry)
    refl refl

record SplitBinderPair {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (Xᴸ : Fin.Fin Δᴸ) (Xᴿ : Fin.Fin Δᴿ) : Set where
  constructor split-binder-pair
  field
    source-dynamic :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ I.X⊑★
    target-dynamic :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ) ≡ I.X⊑★
    separate :
      toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ

es4-split-pair :
  SplitBinderPair es4-split-world Fin.zero target-β
es4-split-pair = split-binder-pair refl refl es4-source-β-separate

sl-split-pair :
  SplitBinderPair sl-split-post-world Fin.zero target-β
sl-split-pair = split-binder-pair refl refl sl-inner-β-separate

data SplitTyRel {Δᴸ Δᴿ Δ} (W : CTI2.World Δᴸ Δᴿ Δ) :
    Ty Δᴸ → Ty Δᴿ → Set where
  split-★ :
      SplitTyRel W ★ ★
  split-var :
      ∀ {Xᴸ Xᴿ}
    → SplitBinderPair W Xᴸ Xᴿ
      -----------------------------
    → SplitTyRel W (＇ Xᴸ) (＇ Xᴿ)
  split-⇒ :
      ∀ {A A′ B B′}
    → SplitTyRel W A A′
    → SplitTyRel W B B′
      -----------------------------
    → SplitTyRel W (A ⇒ B) (A′ ⇒ B′)

es4-type-leaf-ok :
  SplitTyRel es4-split-world es4-source-body es4-target-body
es4-type-leaf-ok =
  split-⇒ (split-var es4-split-pair) (split-var es4-split-pair)

sl-type-leaf-ok :
  SplitTyRel sl-split-post-world sl-source-body sl-target-body
sl-type-leaf-ok = split-⇒ (split-var sl-split-pair) split-★

record SplitTermVarLeaf {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (Xᴸ : Fin.Fin Δᴸ) (Xᴿ : Fin.Fin Δᴿ) : Set where
  constructor split-term-var-leaf
  field
    binder-pair : SplitBinderPair W Xᴸ Xᴿ

es4-term-var-leaf-ok :
  SplitTermVarLeaf es4-split-world Fin.zero target-β
es4-term-var-leaf-ok = split-term-var-leaf es4-split-pair

sl-term-var-leaf-ok :
  SplitTermVarLeaf sl-split-post-world Fin.zero target-β
sl-term-var-leaf-ok = split-term-var-leaf sl-split-pair

------------------------------------------------------------------------
-- S1: second syntax-directed Λ/Λ constructor.
------------------------------------------------------------------------

record S1SplitGuard {Δᴸ Δ}
    (W : CTI2.World Δᴸ 2 Δ)
    (Xᴸ : Fin.Fin Δᴸ) (Xᴿ : Fin.Fin 2) : Set where
  constructor s1-split-guard
  field
    wf : CTI2.WFWorld W
    reveals : GeneratedReveals W (＇ Xᴿ ⇒ ★) (＇ target-α ⇒ ★)
    type-leaf : SplitTyRel W (＇ Xᴸ ⇒ ★) (＇ Xᴿ ⇒ ★)
    term-leaf : SplitTermVarLeaf W Xᴸ Xᴿ

s1-sl-guard-ok : S1SplitGuard sl-split-post-world Fin.zero target-β
s1-sl-guard-ok =
  s1-split-guard sl-split-post-WFWorld sl-reveals-ok
    sl-type-leaf-ok sl-term-var-leaf-ok

record S1ES4SplitGuard : Set where
  constructor s1-es4-split-guard
  field
    wf : CTI2.WFWorld es4-split-world
    reveals : GeneratedReveals es4-split-world
      es4-target-body (＇ target-α ⇒ ＇ target-α)
    type-leaf : SplitTyRel es4-split-world es4-source-body es4-target-body
    term-leaf : SplitTermVarLeaf es4-split-world Fin.zero target-β

s1-es4-guard-ok : S1ES4SplitGuard
s1-es4-guard-ok =
  s1-es4-split-guard es4-split-WFWorld es4-reveals-ok
    es4-type-leaf-ok es4-term-var-leaf-ok

s1-coexistence-depth0-transport-ok :
  IID.Λ⊑Λ²PostBodyTransportᵀ
s1-coexistence-depth0-transport-ok =
  IIP.Λ⊑Λ²-post-body-transport

s1-coexistence-k1-smart-ok :
  (outer∈ : Fin.zero ∈ᵗ `∀ SC.d1-source-body)
  → SC.W₂ ∣ SC.γ₂ ⊢² Λ (Λ SC.d1-source-lam) ⊑ SC.post
      ∶ SC.p₂ outer∈
s1-coexistence-k1-smart-ok = SC.d1-top-smart-live

data S1ΛΛCase : Set where
  s1-shared-ΛΛ :
      IID.Λ⊑Λ²PostBodyTransportᵀ
      ---------------------------
    → S1ΛΛCase
  s1-split-ΛΛ :
      S1SplitGuard sl-split-post-world Fin.zero target-β
      --------------------------------------------------
    → S1ΛΛCase

data S1RightInjΛView : Set where
  s1-view-shared :
      IID.Λ⊑Λ²PostBodyTransportᵀ
      ---------------------------
    → S1RightInjΛView
  s1-view-split :
      S1SplitGuard sl-split-post-world Fin.zero target-β
      --------------------------------------------------
    → S1RightInjΛView

s1-right-inj-Λ-skeleton-ok : S1ΛΛCase → S1RightInjΛView
s1-right-inj-Λ-skeleton-ok (s1-shared-ΛΛ tr) = s1-view-shared tr
s1-right-inj-Λ-skeleton-ok (s1-split-ΛΛ guard) = s1-view-split guard

------------------------------------------------------------------------
-- S2: one Λ⊑Λ² constructor indexed by placement.
------------------------------------------------------------------------

data ΛΛPlacement : Set where
  shared-front : ΛΛPlacement
  split-behind-prefix : ΛΛPlacement

record S2PlacementEvidence (pl : ΛΛPlacement) : Set where
  constructor s2-placement-evidence
  field
    keeps-existing-base :
      pl ≡ shared-front → IID.Λ⊑Λ²PostBodyTransportᵀ
    split-sl :
      pl ≡ split-behind-prefix
      → S1SplitGuard sl-split-post-world Fin.zero target-β

s2-shared-evidence : S2PlacementEvidence shared-front
s2-shared-evidence =
  s2-placement-evidence
    (λ _ → IIP.Λ⊑Λ²-post-body-transport)
    (λ ())

s2-split-evidence : S2PlacementEvidence split-behind-prefix
s2-split-evidence =
  s2-placement-evidence
    (λ ())
    (λ _ → s1-sl-guard-ok)

s2-es4-world-ok : CTI2.WFWorld es4-split-world
s2-es4-world-ok = es4-split-WFWorld

s2-es4-reveals-ok :
  GeneratedReveals es4-split-world
    es4-target-body (＇ target-α ⇒ ＇ target-α)
s2-es4-reveals-ok = es4-reveals-ok

s2-es4-type-leaf-ok :
  SplitTyRel es4-split-world es4-source-body es4-target-body
s2-es4-type-leaf-ok = es4-type-leaf-ok

s2-es4-term-var-leaf-ok :
  SplitTermVarLeaf es4-split-world Fin.zero target-β
s2-es4-term-var-leaf-ok = es4-term-var-leaf-ok

s2-sl-world-ok : CTI2.WFWorld sl-split-post-world
s2-sl-world-ok = sl-split-post-WFWorld

s2-sl-reveals-ok :
  GeneratedReveals sl-split-post-world
    sl-target-body (＇ target-α ⇒ ★)
s2-sl-reveals-ok = sl-reveals-ok

s2-sl-type-leaf-ok :
  SplitTyRel sl-split-post-world sl-source-body sl-target-body
s2-sl-type-leaf-ok = sl-type-leaf-ok

s2-sl-term-var-leaf-ok :
  SplitTermVarLeaf sl-split-post-world Fin.zero target-β
s2-sl-term-var-leaf-ok = sl-term-var-leaf-ok

s2-coexistence-base-transport-ok :
  shared-front ≡ shared-front → IID.Λ⊑Λ²PostBodyTransportᵀ
s2-coexistence-base-transport-ok =
  S2PlacementEvidence.keeps-existing-base s2-shared-evidence

s2-coexistence-k1-smart-ok :
  (outer∈ : Fin.zero ∈ᵗ `∀ SC.d1-source-body)
  → SC.W₂ ∣ SC.γ₂ ⊢² Λ (Λ SC.d1-source-lam) ⊑ SC.post
      ∶ SC.p₂ outer∈
s2-coexistence-k1-smart-ok = SC.d1-top-smart-live

data S2ΛΛCase : Set where
  s2-ΛΛ :
      (pl : ΛΛPlacement)
    → S2PlacementEvidence pl
      ----------------------
    → S2ΛΛCase

data S2RightInjΛView : Set where
  s2-view :
      (pl : ΛΛPlacement)
    → S2PlacementEvidence pl
      ----------------------
    → S2RightInjΛView

s2-right-inj-Λ-skeleton-ok : S2ΛΛCase → S2RightInjΛView
s2-right-inj-Λ-skeleton-ok (s2-ΛΛ pl ev) = s2-view pl ev

------------------------------------------------------------------------
-- S3: re-park liberalization.  The finite shapes refute it.
------------------------------------------------------------------------

data SameCenterNeeded {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (Xᴸ : Fin.Fin Δᴸ) (Xᴿ : Fin.Fin Δᴿ) : Set where
  same-center-needed :
      toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≡ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      --------------------------
    → SameCenterNeeded W Xᴸ Xᴿ

s3-es4-term-var-refuted :
  SameCenterNeeded es4-split-world Fin.zero target-β → ⊥
s3-es4-term-var-refuted (same-center-needed eq) =
  es4-source-β-separate eq

s3-es4-live-type-leaf-refuted :
  es4-source-body CTI2.⊑ᵂ⟨ es4-split-world ⟩ es4-target-body
  → ⊥
s3-es4-live-type-leaf-refuted (I.⇒⊑⇒ () _)

s3-sl-term-var-refuted :
  SameCenterNeeded sl-split-post-world Fin.zero target-β → ⊥
s3-sl-term-var-refuted (same-center-needed eq) =
  sl-inner-β-separate eq

s3-sl-live-type-leaf-refuted :
  sl-source-body CTI2.⊑ᵂ⟨ sl-split-post-world ⟩ sl-target-body
  → ⊥
s3-sl-live-type-leaf-refuted (I.⇒⊑⇒ () _)

no-ope-0↦2-1↦1 :
  (ρ : 2 ↪ᵗ 4)
  → toRenameᵗ ρ Fin.zero ≡ Fin.suc (Fin.suc Fin.zero)
  → toRenameᵗ ρ (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
  → ⊥
no-ope-0↦2-1↦1 (keep ρ) ()
no-ope-0↦2-1↦1 (skip (keep ρ)) ()
no-ope-0↦2-1↦1 (skip (skip ρ)) eq₀ ()

no-ope-0↦3-1↦1 :
  (ρ : 2 ↪ᵗ 4)
  → toRenameᵗ ρ Fin.zero ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
  → toRenameᵗ ρ (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
  → ⊥
no-ope-0↦3-1↦1 (keep ρ) ()
no-ope-0↦3-1↦1 (skip (keep ρ)) ()
no-ope-0↦3-1↦1 (skip (skip ρ)) eq₀ ()

s3-sl-repark-to-alias-refuted :
  Σ[ ρ ∈ (2 ↪ᵗ 4) ]
    ((toRenameᵗ ρ Fin.zero ≡ Fin.suc (Fin.suc Fin.zero))
     × (toRenameᵗ ρ (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero))
  → ⊥
s3-sl-repark-to-alias-refuted (ρ , eq₀ , eq₁) =
  no-ope-0↦2-1↦1 ρ eq₀ eq₁

s3-sl-repark-to-name-refuted :
  Σ[ ρ ∈ (2 ↪ᵗ 4) ]
    ((toRenameᵗ ρ Fin.zero ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero)))
     × (toRenameᵗ ρ (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero))
  → ⊥
s3-sl-repark-to-name-refuted (ρ , eq₀ , eq₁) =
  no-ope-0↦3-1↦1 ρ eq₀ eq₁

s3-sl-same-split-rebase-β-refuted :
  CTI2.RebaseAtᴿ sl-split-post-world sl-split-post-world
    (just target-β)
  → ⊥
s3-sl-same-split-rebase-β-refuted
    (CTI2.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
  sl-inner-β-separate (CTI2.RebaseAt.pivotAligned rb)
s3-sl-same-split-rebase-β-refuted
    (CTI2.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero} rb) =
  prefix-β-impossible (CTI2.RebaseAt.pivotAligned rb)
  where
  prefix-β-impossible :
    toRenameᵗ (CTI2.ηᴸʷ sl-split-post-world) (Fin.suc Fin.zero)
      ≢ toRenameᵗ (CTI2.ηᴿʷ sl-split-post-world) target-β
  prefix-β-impossible ()

s3-es4-same-split-rebase-β-refuted :
  CTI2.RebaseAtᴿ es4-split-world es4-split-world
    (just target-β)
  → ⊥
s3-es4-same-split-rebase-β-refuted
    (CTI2.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
  es4-source-β-separate (CTI2.RebaseAt.pivotAligned rb)

------------------------------------------------------------------------
-- A compact checked verdict index for the prose matrix.
------------------------------------------------------------------------

data Verdict : Set where
  CHECKED-OK REFUTED BLOCKED-WHY : Verdict

data Approach : Set where
  S1 S2 S3 : Approach

data Example : Set where
  ES4 SL : Example

data Cell : Set where
  world reveal type-leaf term-var coexist inversion-cost : Cell

matrix : Approach → Example → Cell → Verdict
matrix S1 ES4 world = CHECKED-OK
matrix S1 ES4 reveal = CHECKED-OK
matrix S1 ES4 type-leaf = CHECKED-OK
matrix S1 ES4 term-var = CHECKED-OK
matrix S1 ES4 coexist = CHECKED-OK
matrix S1 ES4 inversion-cost = CHECKED-OK
matrix S1 SL world = CHECKED-OK
matrix S1 SL reveal = CHECKED-OK
matrix S1 SL type-leaf = CHECKED-OK
matrix S1 SL term-var = CHECKED-OK
matrix S1 SL coexist = CHECKED-OK
matrix S1 SL inversion-cost = CHECKED-OK
matrix S2 ES4 world = CHECKED-OK
matrix S2 ES4 reveal = CHECKED-OK
matrix S2 ES4 type-leaf = CHECKED-OK
matrix S2 ES4 term-var = CHECKED-OK
matrix S2 ES4 coexist = CHECKED-OK
matrix S2 ES4 inversion-cost = CHECKED-OK
matrix S2 SL world = CHECKED-OK
matrix S2 SL reveal = CHECKED-OK
matrix S2 SL type-leaf = CHECKED-OK
matrix S2 SL term-var = CHECKED-OK
matrix S2 SL coexist = CHECKED-OK
matrix S2 SL inversion-cost = CHECKED-OK
matrix S3 ES4 world = REFUTED
matrix S3 ES4 reveal = REFUTED
matrix S3 ES4 type-leaf = REFUTED
matrix S3 ES4 term-var = REFUTED
matrix S3 ES4 coexist = CHECKED-OK
matrix S3 ES4 inversion-cost = BLOCKED-WHY
matrix S3 SL world = REFUTED
matrix S3 SL reveal = REFUTED
matrix S3 SL type-leaf = REFUTED
matrix S3 SL term-var = REFUTED
matrix S3 SL coexist = CHECKED-OK
matrix S3 SL inversion-cost = BLOCKED-WHY

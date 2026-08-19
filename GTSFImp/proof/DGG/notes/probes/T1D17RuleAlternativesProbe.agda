module T1D17RuleAlternativesProbe where

-- File Charter:
--   * Checks declaration-only alternatives for the D17 non-star source-seal
--     classifier; it does not change the live term-imprecision relation.
--   * Checks the target identity-conceal replay row for a target-type-indexed
--     before-step classifier, an administrative endpoint classifier, and a
--     world-occupancy classifier.
--   * Restates the D16 companion fields needed to explain how the world-level
--     option composes with the world-invariants work.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (Maybe; just)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind)
open import Consistency
open import Conversion
open import Imprecision
open import CastTerms using (Term; Value; _⟨_⟩; _↑_; _↓_)

import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World; CtxImp; _⊑ᵂ⟨_⟩_; ImpEnvMono; TagRebaseAtᴸ; SameCtx;
   CenterAligned; NoTargetOccupantAtSource; NotTopTag)

------------------------------------------------------------------------
-- Option (a): classify before the step with a stable target-type fact
------------------------------------------------------------------------

module BeforeStep where

  data SourceConcealOK {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) :
      Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
      → Maybe (TyVar Δᴿ) → Term Δᴿ → Ty Δᴿ → Set where
    seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′ B}
      → NonStar R
      → NonStar B
        ----------------------------------------------------
      → SourceConcealOK W P (seal X R) Xᴿ? M′ B

    seal-nonstar-name-protected-ok : ∀ {P X R Y S M B μ}
        {c : μ ⊢ (＇ Y) ∼ ★}
      → NonStar R
      → CenterAligned W X Y
        ----------------------------------------------------
      → SourceConcealOK W P (seal X R) (just Y)
          ((M ↓ seal Y S) ⟨ c ⟩) B

    fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′ C}
        {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
        ----------------------------------------------------
      → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′ C

    all-conceal-ok : ∀ {P A B Xᴿ? M′ C}
        {c : Conv↓ (Nat.suc Δᴸ) A B}
        ----------------------------------------------------
      → SourceConcealOK W P (`∀↓ c) Xᴿ? M′ C

    id-conceal-ok : ∀ {P A Xᴿ? M′ B}
        ----------------------------------------------------
      → SourceConcealOK W P (id↓ A) Xᴿ? M′ B

  infix 4 _∣_⊢ᴬ_⊑_∶_

  data _∣_⊢ᴬ_⊑_∶_ {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) ( γ : CtxImp W) :
      Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B → Set where
    live : ∀ {M M′ A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      → W CTI2.∣ γ ⊢² M ⊑ M′ ∶ p
        --------------------------------
      → W ∣ γ ⊢ᴬ M ⊑ M′ ∶ p

    conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
        {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
      → SourceConcealOK W′ M c Xᴿ? M′ B
      → ImpEnvMono W W′
      → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
      → SameCtx γ γ′
      → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
      → W′ ∣ γ′ ⊢ᴬ M ⊑ M′ ∶ p
      → (q : A′ ⊑ᵂ⟨ W ⟩ B)
        -----------------------------
      → W ∣ γ ⊢ᴬ M ↓ c ⊑ M′ ∶ q

  seal-target-id-conceal-replay : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {P : Term Δᴸ} {N : Term Δᴿ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ} {B : Ty Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {p : R ⊑ᵂ⟨ W′ ⟩ B} {q : ＇ X ⊑ᵂ⟨ W ⟩ B}
    → NonStar R
    → NonStar B
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → SameCtx γ γ′
    → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X R
    → W′ ∣ γ′ ⊢ᴬ P ⊑ N ∶ p
    → W ∣ γ ⊢ᴬ P ↓ seal X R ⊑ N ∶ q
  seal-target-id-conceal-replay {q = q} Rns Bns mono rb sc c⊢ prem =
    conceal⊑²-source-ok
      (seal-nonstar-plain-ok Rns Bns) mono rb sc c⊢ prem q

  dynamic-target-type-rejected : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ}
      {Xᴿ? : Maybe (TyVar Δᴿ)} {N : Term Δᴿ}
    → SourceConcealOK W P (seal X R) Xᴿ?
        (N ↓ id↓ ★) ★
    → ⊥
  dynamic-target-type-rejected (seal-nonstar-plain-ok Rns ())

------------------------------------------------------------------------
-- Option (b): classify the value exposed after administrative keeps
------------------------------------------------------------------------

module AfterStep where

  data TargetValueBeneath {Δ : TyCtx} : Term Δ → Term Δ → Set where
    target-value-here : ∀ {V}
      → Value V
        ----------------------
      → TargetValueBeneath V V

    target-id-reveal : ∀ {V A}
      → Value V
        -------------------------------------
      → TargetValueBeneath (V ↑ id↑ A) V

    target-id-conceal : ∀ {V A}
      → Value V
        -------------------------------------
      → TargetValueBeneath (V ↓ id↓ A) V

    target-conceal-reveal : ∀ {V X R}
      → Value V
        ---------------------------------------------------
      → TargetValueBeneath
          ((V ↓ seal X R) ↑ unseal X R) V

  data SourceConcealOK {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) :
      Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
      → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
    seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
      → NonStar R
      → NotTopTag M′
        ----------------------------------------------------
      → SourceConcealOK W P (seal X R) Xᴿ? M′

    seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
        {c : μ ⊢ (＇ Y) ∼ ★}
      → NonStar R
      → CenterAligned W X Y
        ----------------------------------------------------
      → SourceConcealOK W P (seal X R) (just Y)
          ((M ↓ seal Y S) ⟨ c ⟩)

    fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
        {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
        ----------------------------------------------------
      → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

    all-conceal-ok : ∀ {P A B Xᴿ? M′}
        {c : Conv↓ (Nat.suc Δᴸ) A B}
        ----------------------------------------------------
      → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

    id-conceal-ok : ∀ {P A Xᴿ? M′}
        ----------------------------------------------------
      → SourceConcealOK W P (id↓ A) Xᴿ? M′

  infix 4 _∣_⊢ᴮ_⊑_∶_

  data _∣_⊢ᴮ_⊑_∶_ {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
      Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B → Set where
    live : ∀ {M M′ A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      → W CTI2.∣ γ ⊢² M ⊑ M′ ∶ p
        --------------------------------
      → W ∣ γ ⊢ᴮ M ⊑ M′ ∶ p

    conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
        {γ′ : CtxImp W′} {M M′ V′ A A′ B Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
      → TargetValueBeneath M′ V′
      → SourceConcealOK W′ M c Xᴿ? V′
      → ImpEnvMono W W′
      → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
      → SameCtx γ γ′
      → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
      → W′ ∣ γ′ ⊢ᴮ M ⊑ M′ ∶ p
      → (q : A′ ⊑ᵂ⟨ W ⟩ B)
        -----------------------------
      → W ∣ γ ⊢ᴮ M ↓ c ⊑ M′ ∶ q

  seal-target-id-conceal-replay : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {P : Term Δᴸ} {N : Term Δᴿ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ} {B : Ty Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {p : R ⊑ᵂ⟨ W′ ⟩ B} {q : ＇ X ⊑ᵂ⟨ W ⟩ B}
    → Value N
    → NonStar R
    → NotTopTag N
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → SameCtx γ γ′
    → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X R
    → W′ ∣ γ′ ⊢ᴮ P ⊑ N ∶ p
    → W ∣ γ ⊢ᴮ P ↓ seal X R ⊑ N ∶ q
  seal-target-id-conceal-replay {q = q} vN Rns not-top mono rb sc c⊢ prem =
    conceal⊑²-source-ok
      (target-value-here vN) (seal-nonstar-plain-ok Rns not-top)
      mono rb sc c⊢ prem q

------------------------------------------------------------------------
-- Option (c): replace target syntax with source-pivot occupancy
------------------------------------------------------------------------

module WorldLevel where

  data SourceConcealOK {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) :
      Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
      → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
    seal-nonstar-unmatched-ok : ∀ {P X R Xᴿ? M′}
      → NonStar R
      → NoTargetOccupantAtSource W X
        ----------------------------------------------------
      → SourceConcealOK W P (seal X R) Xᴿ? M′

    seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
        {c : μ ⊢ (＇ Y) ∼ ★}
      → NonStar R
      → CenterAligned W X Y
        ----------------------------------------------------
      → SourceConcealOK W P (seal X R) (just Y)
          ((M ↓ seal Y S) ⟨ c ⟩)

    fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
        {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
        ----------------------------------------------------
      → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

    all-conceal-ok : ∀ {P A B Xᴿ? M′}
        {c : Conv↓ (Nat.suc Δᴸ) A B}
        ----------------------------------------------------
      → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

    id-conceal-ok : ∀ {P A Xᴿ? M′}
        ----------------------------------------------------
      → SourceConcealOK W P (id↓ A) Xᴿ? M′

  infix 4 _∣_⊢ᵂ_⊑_∶_

  data _∣_⊢ᵂ_⊑_∶_ {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
      Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B → Set where
    live : ∀ {M M′ A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      → W CTI2.∣ γ ⊢² M ⊑ M′ ∶ p
        --------------------------------
      → W ∣ γ ⊢ᵂ M ⊑ M′ ∶ p

    conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
        {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
      → SourceConcealOK W′ M c Xᴿ? M′
      → ImpEnvMono W W′
      → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
      → SameCtx γ γ′
      → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
      → W′ ∣ γ′ ⊢ᵂ M ⊑ M′ ∶ p
      → (q : A′ ⊑ᵂ⟨ W ⟩ B)
        -----------------------------
      → W ∣ γ ⊢ᵂ M ↓ c ⊑ M′ ∶ q

  seal-target-id-conceal-replay : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {P : Term Δᴸ} {N : Term Δᴿ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ} {B : Ty Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {p : R ⊑ᵂ⟨ W′ ⟩ B} {q : ＇ X ⊑ᵂ⟨ W ⟩ B}
    → NonStar R
    → NoTargetOccupantAtSource W′ X
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → SameCtx γ γ′
    → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X R
    → W′ ∣ γ′ ⊢ᵂ P ⊑ N ∶ p
    → W ∣ γ ⊢ᵂ P ↓ seal X R ⊑ N ∶ q
  seal-target-id-conceal-replay {q = q} Rns no-target mono rb sc c⊢ prem =
    conceal⊑²-source-ok
      (seal-nonstar-unmatched-ok Rns no-target)
      mono rb sc c⊢ prem q

  aligned-refutes-unmatched : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → CenterAligned W X Y
    → NoTargetOccupantAtSource W X
    → ⊥
  aligned-refutes-unmatched {Y = Y} aligned no-target =
    no-target (Y , sym aligned)

------------------------------------------------------------------------
-- D16 companion interaction for option (c)
------------------------------------------------------------------------

lookupStore : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
lookupStore (store-lift Σ) Fin.zero = ＇ Fin.zero
lookupStore (store-lift Σ) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)
lookupStore (store-bind Σ A) Fin.zero = ⇑ᵗ A
lookupStore (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)

record D16Companion {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) : Set where
  field
    preciseMarksAligned :
      ∀ (Xᴸ : TyVar Δᴸ)
      → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar Δᴿ ]
          toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≡
            toRenameᵗ (CTX.ηᴸʷ W) Xᴸ

    representationsImprecise :
      ∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → CenterAligned W Xᴸ Xᴿ
      → CTX.impEnvʷ W ⊢
          renameᵗ (toRenameᵗ (CTX.ηᴸʷ W))
            (lookupStore (CTX.sourceStoreʷ W) Xᴸ)
          ⊑ renameᵗ (toRenameᵗ (CTX.ηᴿʷ W))
            (lookupStore (CTX.targetStoreʷ W) Xᴿ)

    unmatchedTargetsDynamic :
      ∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≢
            toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)
      → lookupStore (CTX.targetStoreʷ W) Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar Δᴿ ]
            (lookupStore (CTX.targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar Δᴸ)
              → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≢
                toRenameᵗ (CTX.ηᴿʷ W) Yᴿ)

open D16Companion public

no-target-mark-dynamic : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → D16Companion W
  → NoTargetOccupantAtSource W X
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) X) ≡ X⊑★
no-target-mark-dynamic {W = W} {X = X} invariants no-target =
  not-precise-is-dynamic not-precise
  where
  not-precise :
    CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) X) ≢ X⊑X
  not-precise precise with preciseMarksAligned invariants X precise
  not-precise precise | Y , aligned = no-target (Y , aligned)

  not-precise-is-dynamic : ∀ {v : VarImp} → v ≢ X⊑X → v ≡ X⊑★
  not-precise-is-dynamic {X⊑X} not-equal = ⊥-elim (not-equal refl)
  not-precise-is-dynamic {X⊑★} not-equal = refl

matched-pivot-representations : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → D16Companion W
  → CenterAligned W X Y
  → CTX.impEnvʷ W ⊢
      renameᵗ (toRenameᵗ (CTX.ηᴸʷ W))
        (lookupStore (CTX.sourceStoreʷ W) X)
      ⊑ renameᵗ (toRenameᵗ (CTX.ηᴿʷ W))
        (lookupStore (CTX.targetStoreʷ W) Y)
matched-pivot-representations invariants aligned =
  representationsImprecise invariants aligned

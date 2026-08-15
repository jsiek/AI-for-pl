module CTITighteningNarrowScratch where

-- File Charter:
--   * Notes-only calibration scratch for CTI tightening candidate S-NARROW.
--   * Defines a miniature CTI2 relation whose three ordinary cast rules carry
--     direction/shape-composition premises.
--   * Checks the projection-mismatch calibration and matching-provenance
--     controls without editing the live CTI2 relation or live DGG proofs.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Consistency using
  (Env∼; X∼★; ★∼X; _⊢_∼_; _⊢_∼★; _⊢★∼_; _↪ᵗ_;
   empty; keep; flipᵐ; toRenameᵗ; id; idᵍ; _!; ？_; _↦_)
open import Conversion using (seal)
import Conversion
open import Imprecision
open import CastTerms using (Term; _⟨_⟩; _↓_; $)
import CastTerms as CT
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR

open CTI2 using
  (World; world; CtxImp; _⊑ᵂ⟨_⟩_; RebaseAt; StoreRepImp;
   store-rep-imp; ⊢↓-sealˣ)

------------------------------------------------------------------------
-- CTI2-oriented cast shapes
------------------------------------------------------------------------

data CastDirection : Set where
  widening : CastDirection
  narrowing : CastDirection

opposite : CastDirection → CastDirection
opposite widening = narrowing
opposite narrowing = widening

data CastShape (Δ : TyCtx) : Set where
  id★ˢ : CastShape Δ
  idιˢ : Base → CastShape Δ
  idˣˢ : TyVar Δ → CastShape Δ
  tagˢ : Ty Δ → CastShape Δ
  _↦ˢ_ : CastShape Δ → CastShape Δ → CastShape Δ
  ∀ˢ_ : CastShape (Nat.suc Δ) → CastShape Δ
  instˢ_ : CastShape (Nat.suc Δ) → CastShape Δ
  genˢ_ : CastShape (Nat.suc Δ) → CastShape Δ

infix 4 _⊢ᶜ_⦂_

data _⊢ᶜ_⦂_ :
    CastDirection → ∀ {Δ μ A B} → μ ⊢ A ∼ B
    → CastShape Δ → Set where

  shape-id★ : ∀ {direction Δ μ}
      -------------------------------------------
    → direction ⊢ᶜ id {Δ = Δ} {μ = μ} ★ ⦂ id★ˢ

  shape-idι : ∀ {direction Δ μ ι}
      ------------------------------------------------
    → direction ⊢ᶜ id {Δ = Δ} {μ = μ} (‵ ι) ⦂ idιˢ ι

  shape-idˣ : ∀ {direction Δ μ X}
      -------------------------------------------------
    → direction ⊢ᶜ id {Δ = Δ} {μ = μ} (＇ X) ⦂ idˣˢ X

  shape-↦ : ∀ {direction Δ μ A A′ B B′}
      {p q : CastShape Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A}
      {d : μ ⊢ B ∼ B′}
    → opposite direction ⊢ᶜ c ⦂ p
    → direction ⊢ᶜ d ⦂ q
      -------------------------------------
    → direction ⊢ᶜ (c ↦ d) ⦂ p ↦ˢ q

  shape-tag : ∀ {Δ μ A G} {s : CastShape Δ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → widening ⊢ᶜ c ⦂ s
      ---------------------------------------------------------------
    → widening ⊢ᶜ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄
        ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄ ⦂ tagˢ G

  shape-project : ∀ {Δ μ G B} {s : CastShape Δ}
      {Gᵍ : Ground G} {★∼G : μ ⊢★∼ G}
      {c : μ ⊢ G ∼ B} {Bns : NonStar B}
    → narrowing ⊢ᶜ c ⦂ s
      ---------------------------------------------------------------
    → narrowing ⊢ᶜ ？_ {G = G} ⦃ Gᵍ = Gᵍ ⦄
        ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns = Bns ⦄ ⦂ tagˢ G

-- Shape composition against the world-indexed type-imprecision witnesses.
-- `SourceCastOK c p q` means casting the source endpoint of `p` with `c`
-- yields conclusion witness `q`.  `TargetCastOK` is the target analogue.

infix 4 SourceCastOK TargetCastOK

data SourceCastOK {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) :
    ∀ {A A′ B μ} {p : A ⊑ᵂ⟨ W ⟩ B}
      {q : A′ ⊑ᵂ⟨ W ⟩ B}
    → μ ⊢ A ∼ A′ → Set where

  source-id : ∀ {A B μ} {p q : A ⊑ᵂ⟨ W ⟩ B}
      {atom : Atom A}
      --------------------------------
    → SourceCastOK W {p = p} {q = q} (id {μ = μ} atom)

  source-widen-base-to★ : ∀ {μ ι}
      {p : (‵ ι) ⊑ᵂ⟨ W ⟩ ★} {q : ★ ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ‵ ι ∼ ★}
    → widening ⊢ᶜ c ⦂ tagˢ (‵ ι)
    → p ≡ ι⊑★
    → q ≡ ★⊑★
      ------------------------------------
    → SourceCastOK W {p = p} {q = q} c

  source-widen-var-to★ : ∀ {X μ}
      {p : (＇ X) ⊑ᵂ⟨ W ⟩ ★} {q : ★ ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ＇ X ∼ ★}
    → widening ⊢ᶜ c ⦂ tagˢ (＇ X)
    → (mark :
        CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★)
    → p ≡ X⊑★ mark
    → q ≡ ★⊑★
      ------------------------------------
    → SourceCastOK W {p = p} {q = q} c

  source-narrow-★-to-var : ∀ {X μ}
      {p : ★ ⊑ᵂ⟨ W ⟩ ★} {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ★ ∼ ＇ X}
    → narrowing ⊢ᶜ c ⦂ tagˢ (＇ X)
    → p ≡ ★⊑★
    → (mark :
        CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★)
    → q ≡ X⊑★ mark
      ------------------------------------
    → SourceCastOK W {p = p} {q = q} c

data TargetCastOK {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) :
    ∀ {A B B′ μ} {p : A ⊑ᵂ⟨ W ⟩ B}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
    → μ ⊢ B ∼ B′ → Set where

  target-id : ∀ {A B μ} {p q : A ⊑ᵂ⟨ W ⟩ B}
      {atom : Atom B}
      --------------------------------
    → TargetCastOK W {p = p} {q = q} (id {μ = μ} atom)

  target-widen-base-to★ : ∀ {μ ι}
      {p : (‵ ι) ⊑ᵂ⟨ W ⟩ (‵ ι)}
      {q : (‵ ι) ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ‵ ι ∼ ★}
    → widening ⊢ᶜ c ⦂ tagˢ (‵ ι)
    → p ≡ ι⊑ι
    → q ≡ ι⊑★
      ------------------------------------
    → TargetCastOK W {p = p} {q = q} c

  target-widen-var-to★ : ∀ {X Y μ}
      {p : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ＇ Y ∼ ★}
    → widening ⊢ᶜ c ⦂ tagˢ (＇ Y)
    → (mark :
        CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★)
    → q ≡ X⊑★ mark
      ------------------------------------
    → TargetCastOK W {p = p} {q = q} c

  target-narrow-★-to-var : ∀ {X Y μ}
      {p : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      {c : μ ⊢ ★ ∼ ＇ Y}
    → narrowing ⊢ᶜ c ⦂ tagˢ (＇ Y)
    → (mark :
        CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★)
    → p ≡ X⊑★ mark
      ------------------------------------
    → TargetCastOK W {p = p} {q = q} c

data PairedCastOK {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) :
    ∀ {C C′ A A′ μ μ′}
      {p : C ⊑ᵂ⟨ W ⟩ C′}
      {q : A ⊑ᵂ⟨ W ⟩ A′}
    → μ ⊢ C ∼ A
    → μ′ ⊢ C′ ∼ A′
    → Set where

  paired-id : ∀ {A B μ μ′}
      {p q : A ⊑ᵂ⟨ W ⟩ B} {atomA : Atom A} {atomB : Atom B}
      -------------------------------------------------------------
    → PairedCastOK W {p = p} {q = q}
        (id {μ = μ} atomA) (id {μ = μ′} atomB)

  paired-widen-base-to★ : ∀ {μ μ′ ι}
      {p : (‵ ι) ⊑ᵂ⟨ W ⟩ (‵ ι)}
      {q : ★ ⊑ᵂ⟨ W ⟩ ★}
      {c : μ ⊢ ‵ ι ∼ ★} {c′ : μ′ ⊢ ‵ ι ∼ ★}
    → widening ⊢ᶜ c ⦂ tagˢ (‵ ι)
    → widening ⊢ᶜ c′ ⦂ tagˢ (‵ ι)
    → p ≡ ι⊑ι
    → q ≡ ★⊑★
      ----------------------------------
    → PairedCastOK W {p = p} {q = q} c c′

  paired-narrow-var-from★ : ∀ {X Y μ μ′}
      {p : ★ ⊑ᵂ⟨ W ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      {c : μ ⊢ ★ ∼ ＇ X} {c′ : μ′ ⊢ ★ ∼ ＇ Y}
    → narrowing ⊢ᶜ c ⦂ tagˢ (＇ X)
    → narrowing ⊢ᶜ c′ ⦂ tagˢ (＇ Y)
    → p ≡ ★⊑★
      ----------------------------------
    → PairedCastOK W {p = p} {q = q} c c′

------------------------------------------------------------------------
-- Miniature tightened relation
------------------------------------------------------------------------

infix 4 _∣_⊢ᴺ_⊑_∶_

data _∣_⊢ᴺ_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  κ⊑κᴺ : ∀ n
    → (p : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ))
      ----------------------------------------------------
    → W ∣ γ ⊢ᴺ $ (κℕ n) ⊑ $ (κℕ n) ∶ p

  cast⊑castᴺ : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
      {c : ν ⊢ C ∼ A} {c′ : ν′ ⊢ C′ ∼ A′}
    → PairedCastOK W {p = p} {q = q} c c′
    → W ∣ γ ⊢ᴺ M ⊑ M′ ∶ p
      -------------------------------------
    → W ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑castᴺ : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
      {ν : Env∼ Δᴿ} {c′ : ν ⊢ B ∼ B′}
    → TargetCastOK W {p = p} {q = q} c′
    → W ∣ γ ⊢ᴺ M ⊑ M′ ∶ p
      -----------------------------
    → W ∣ γ ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ∶ q

  cast⊑ᴺ : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
      {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ A′}
    → SourceCastOK W {p = p} {q = q} c
    → W ∣ γ ⊢ᴺ M ⊑ M′ ∶ p
      -----------------------------
    → W ∣ γ ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ∶ q

  conceal⊑ᴺ : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conversion.Conv↓ Δᴸ A A′}
    → CTI2.SourceConcealPartnerOK W′ M c Xᴿ? M′
    → CTI2.ImpEnvMono W W′
    → CTI2.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → CTI2.SameCtx γ γ′
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢ᴺ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢ᴺ M ↓ c ⊑ M′ ∶ q

  conceal⊑concealᴺ : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conversion.Conv↓ Δᴸ A B}
      {c′ : Conversion.Conv↓ Δᴿ A′ B′}
    → CTI2.MatchedConcealPartnerOK Wᵖ M c (just Xᴿ) M′
    → CTI2.ImpEnvMono W Wᵖ
    → CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ
    → CTI2.SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ just Xᴸ ] c
    → CTI2.targetStoreʷ W CTI2.⊢↓[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢ᴺ M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢ᴺ M ↓ c ⊑ M′ ↓ c′ ∶ q

------------------------------------------------------------------------
-- Concrete calibration world
------------------------------------------------------------------------

private
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 1
  Y = Fin.zero

source-store : TyStore 1
source-store = store-bind store-empty ★

target-store : TyStore 1
target-store = store-bind store-empty ★

source-X∋ : source-store ∋ X ⦂ ★
source-X∋ = Z∋ refl

target-Y∋ : target-store ∋ Y ⦂ ★
target-Y∋ = Z∋ refl

source-η : 1 ↪ᵗ 1
source-η = keep empty

target-η : 1 ↪ᵗ 1
target-η = keep empty

imp-env-dyn : ImpEnv 1
imp-env-dyn Fin.zero = X⊑★

W : World 1 1 1
W = world source-η target-η imp-env-dyn source-store target-store

source-env-tag : Env∼ 1
source-env-tag _ = X∼★

target-env-tag : Env∼ 1
target-env-tag _ = X∼★

source-env-project : Env∼ 1
source-env-project _ = ★∼X

target-env-project : Env∼ 1
target-env-project _ = ★∼X

ℕ!ˢ : source-env-tag ⊢ (‵ `ℕ) ∼ ★
ℕ!ˢ = id (‵ `ℕ) !

ℕ!ᵗ : target-env-tag ⊢ (‵ `ℕ) ∼ ★
ℕ!ᵗ = id (‵ `ℕ) !

X! : source-env-tag ⊢ ＇ X ∼ ★
X! = id (＇ X) !

Y! : target-env-tag ⊢ ＇ Y ∼ ★
Y! = id (＇ Y) !

X? : source-env-project ⊢ ★ ∼ ＇ X
X? = ？ (idᵍ (＇ X))

Y? : target-env-project ⊢ ★ ∼ ＇ Y
Y? = ？ (idᵍ (＇ Y))

ℕ!-shapeˢ : widening ⊢ᶜ ℕ!ˢ ⦂ tagˢ (‵ `ℕ)
ℕ!-shapeˢ = shape-tag shape-idι

ℕ!-shapeᵗ : widening ⊢ᶜ ℕ!ᵗ ⦂ tagˢ (‵ `ℕ)
ℕ!-shapeᵗ = shape-tag shape-idι

X!-shape : widening ⊢ᶜ X! ⦂ tagˢ (＇ X)
X!-shape = shape-tag shape-idˣ

Y!-shape : widening ⊢ᶜ Y! ⦂ tagˢ (＇ Y)
Y!-shape = shape-tag shape-idˣ

X?-shape : narrowing ⊢ᶜ X? ⦂ tagˢ (＇ X)
X?-shape = shape-project shape-idˣ

Y?-shape : narrowing ⊢ᶜ Y? ⦂ tagˢ (＇ Y)
Y?-shape = shape-project shape-idˣ

qXY : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
qXY = X⊑X

X⊑★W : ＇ X ⊑ᵂ⟨ W ⟩ ★
X⊑★W = X⊑★ refl

source-seal-typed : source-store CTI2.⊢↓[ just X ] seal X ★
source-seal-typed = ⊢↓-sealˣ source-X∋

target-seal-typed : target-store CTI2.⊢↓[ just Y ] seal Y ★
target-seal-typed = ⊢↓-sealˣ target-Y∋

X-Y-representation : StoreRepImp W X Y
X-Y-representation = store-rep-imp ★⊑★

X-Y-rebase : RebaseAt W W X Y
X-Y-rebase = CTI2.sameWorldRebaseAt refl X-Y-representation

base-source : Term 1
base-source = ($ (κℕ 0)) ⟨ ℕ!ˢ ⟩

base-target : Term 1
base-target = ($ (κℕ 0)) ⟨ ℕ!ᵗ ⟩

source-sealed : Term 1
source-sealed = base-source ↓ seal X ★

target-sealed : Term 1
target-sealed = base-target ↓ seal Y ★

target-name-tagged : Term 1
target-name-tagged = target-sealed ⟨ Y! ⟩

target-mismatched : Term 1
target-mismatched = base-target ⟨ Y? ⟩

base-target-value : CT.Value base-target
base-target-value = CT.$ (κℕ 0) CT.《 CT.inj 》

target-sealed-value : CT.Value target-sealed
target-sealed-value = base-target-value CT.↓ CT.seal

baseᴺ : W ∣ [] ⊢ᴺ base-source ⊑ base-target ∶ ★⊑★
baseᴺ =
  cast⊑castᴺ
    (paired-widen-base-to★ ℕ!-shapeˢ ℕ!-shapeᵗ refl refl)
    (κ⊑κᴺ 0 ι⊑ι)

bad-inputᴺ : W ∣ [] ⊢ᴺ source-sealed ⊑ base-target ∶ X⊑★W
bad-inputᴺ =
  conceal⊑ᴺ
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target (CTI2.rep★-nonvar-tag nonvar-base)))
    (λ _ eq → eq)
    (CTI2.tag-rebase-varᴸ X-Y-rebase)
    CTI2.same-[] source-seal-typed baseᴺ X⊑★W

source-taggedᴺ : W ∣ [] ⊢ᴺ source-sealed ⟨ X! ⟩ ⊑ base-target ∶ ★⊑★
source-taggedᴺ =
  cast⊑ᴺ (source-widen-var-to★ X!-shape refl refl refl) bad-inputᴺ

-- C1 negative attempt.  This should be impossible if S-NARROW fixed the
-- projection mismatch.  It is still derivable: the paired projections compose
-- through the intermediate `X ⊑ ★` witness.
projection-mismatch-still-derivableᴺ :
  W ∣ [] ⊢ᴺ source-sealed ⟨ X! ⟩ ⟨ X? ⟩
    ⊑ base-target ⟨ Y? ⟩ ∶ qXY
projection-mismatch-still-derivableᴺ =
  cast⊑castᴺ
    (paired-narrow-var-from★ X?-shape Y?-shape refl)
    source-taggedᴺ

matching-outputᴺ : W ∣ [] ⊢ᴺ source-sealed ⊑ target-sealed ∶ qXY
matching-outputᴺ =
  conceal⊑concealᴺ
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-nonvar-tag nonvar-base))
    (λ _ eq → eq) X-Y-rebase CTI2.same-[]
    source-seal-typed target-seal-typed baseᴺ qXY

matching-inputᴺ : W ∣ [] ⊢ᴺ source-sealed ⊑ target-name-tagged ∶ X⊑★W
matching-inputᴺ =
  ⊑castᴺ (target-widen-var-to★ Y!-shape refl refl) matching-outputᴺ

matching-projectionᴺ :
  W ∣ [] ⊢ᴺ source-sealed
    ⊑ target-name-tagged ⟨ Y? ⟩ ∶ qXY
matching-projectionᴺ =
  ⊑castᴺ (target-narrow-★-to-var Y?-shape refl refl) matching-inputᴺ

------------------------------------------------------------------------
-- C2/C3 calibration records
------------------------------------------------------------------------

record CastSiteOK : Set₁ where
  field
    name : Set
    checked : name

-- Representative compiler-emitted paired argument/primitive cast:
-- the same base cast is emitted on both sides, and the new paired premise
-- composes through the shared `ℕ ⊑ ★` intermediate.
compile-paired-base-site : W ∣ [] ⊢ᴺ base-source ⊑ base-target ∶ ★⊑★
compile-paired-base-site = baseᴺ

-- Representative one-sided source insertion used by source-side inst/gen
-- catch-up: the source `X!` changes `X ⊑ ★` to `★ ⊑ ★`.
compile-source-one-sided-site :
  W ∣ [] ⊢ᴺ source-sealed ⟨ X! ⟩ ⊑ base-target ∶ ★⊑★
compile-source-one-sided-site = source-taggedᴺ

-- Representative one-sided target insertion used by applications and
-- generated-name catch-up: target `Y!` changes `X ⊑ Y` to `X ⊑ ★`.
compile-target-one-sided-site :
  W ∣ [] ⊢ᴺ source-sealed ⊑ target-name-tagged ∶ X⊑★W
compile-target-one-sided-site = matching-inputᴺ

-- C3 positive checkpoint: matching generated-name projection remains
-- derivable under the restricted target-cast premise.
good-generated-projection-site :
  W ∣ [] ⊢ᴺ source-sealed ⊑ target-name-tagged ⟨ Y? ⟩ ∶ qXY
good-generated-projection-site = matching-projectionᴺ

good-generated-catchup :
  ECR.CatchupCast {W = W} {A = ＇ X}
    X⊑★W target-name-tagged Y? qXY
good-generated-catchup =
  ECR.catchup-projection
    (ECR.generated-project-same target-sealed-value)

bad-square-is-not-refuted : ⊥ → ⊥
bad-square-is-not-refuted z = z

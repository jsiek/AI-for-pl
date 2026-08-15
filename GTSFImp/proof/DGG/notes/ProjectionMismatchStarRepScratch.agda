module ProjectionMismatchStarRepScratch where

-- Scratch probe: source seal representation is literally `★`, so the
-- refined partner predicate permits a direct target tag.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Consistency using
  (Env∼; X∼★; ★∼X; _⊢_∼_; _⊢★∼_; _↪ᵗ_; empty; keep;
   id; idᵍ; _!; ？_)
open import Conversion using (seal)
open import Imprecision
open import CastTerms using
  (Term; Value; $; _⟨_⟩; _↓_; blame; _《_》; inj)
open import Reduction
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.ExtraCastRight2 using
  (ExtraCastRight²; CatchupCast; catchup-projection)
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_; RebaseAt;
   store-rep-imp; ⊢↓-sealˣ)

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

source-η : 1 ↪ᵗ 1
source-η = keep empty

target-η : 1 ↪ᵗ 1
target-η = keep empty

imp-env-dyn : ImpEnv 1
imp-env-dyn Fin.zero = X⊑★

probe-world : World 1 1 1
probe-world = world source-η target-η imp-env-dyn source-store target-store

target-env-tag : Env∼ 1
target-env-tag _ = X∼★

source-env-tag : Env∼ 1
source-env-tag _ = X∼★

target-env-proj : Env∼ 1
target-env-proj _ = ★∼X

ℕ! : target-env-tag ⊢ (‵ `ℕ) ∼ ★
ℕ! = id (‵ `ℕ) !

ℕ!ˢ : source-env-tag ⊢ (‵ `ℕ) ∼ ★
ℕ!ˢ = id (‵ `ℕ) !

Y? : target-env-proj ⊢ ★ ∼ ＇ Y
Y? = ？ (idᵍ (＇ Y))

X! : source-env-tag ⊢ ＇ X ∼ ★
X! = id (＇ X) !

X? : target-env-proj ⊢ ★ ∼ ＇ X
X? = ？ (idᵍ (＇ X))

source-X-seal-typed : source-store CTI2.⊢↓[ just X ] seal X ★
source-X-seal-typed = ⊢↓-sealˣ source-X∋

X-Y-representation : CTI2.StoreRepImp probe-world X Y
X-Y-representation = store-rep-imp ★⊑★

X-Y-rebase : RebaseAt probe-world probe-world X Y
X-Y-rebase = CTI2.sameWorldRebaseAt refl X-Y-representation

probe-p : ＇ X ⊑ᵂ⟨ probe-world ⟩ ★
probe-p = X⊑★ refl

probe-q : ＇ X ⊑ᵂ⟨ probe-world ⟩ ＇ Y
probe-q = X⊑X

source-term : Term 1
source-term = (($ (κℕ 0)) ⟨ ℕ!ˢ ⟩) ↓ seal X ★

target-untagged : Term 1
target-untagged = $ (κℕ 0)

target-tagged : Term 1
target-tagged = target-untagged ⟨ ℕ! ⟩

mismatch-term : Term 1
mismatch-term = target-tagged ⟨ Y? ⟩

source-value : Value source-term
source-value = (($ (κℕ 0)) CastTerms.《 CastTerms.inj 》) ↓
  CastTerms.seal

target-untagged-value : Value target-untagged
target-untagged-value = $ (κℕ 0)

target-tagged-value : Value target-tagged
target-tagged-value = target-untagged-value 《 inj 》

input-relation :
  probe-world ∣ [] ⊢² source-term ⊑ target-tagged ∶ probe-p
input-relation =
  CTI2.conceal⊑²
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target (CTI2.rep★-nonvar-tag nonvar-base)))
    (λ _ eq → eq)
    (CTI2.tag-rebase-varᴸ X-Y-rebase)
    CTI2.same-[]
    source-X-seal-typed
    (CTI2.cast⊑cast² ℕ!ˢ ℕ! (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★)
    probe-p

-- The unrestricted paired-cast constructor accepts this square.  The left
-- cast checks the abstract X tag, whereas the right cast checks the unrelated
-- Y tag.  The result types are nevertheless related because X and Y share
-- their center variable in probe-world.
projection-mismatch² :
  probe-world ∣ [] ⊢²
    source-term ⟨ X! ⟩ ⟨ X? ⟩
    ⊑ target-tagged ⟨ Y? ⟩ ∶ probe-q
projection-mismatch² =
  CTI2.cast⊑cast² X? Y?
    (CTI2.cast⊑² X! input-relation ★⊑★) probe-q

source-projection-returns :
  source-term ⟨ X! ⟩ ⟨ X? ⟩
    —↠[ keep ∷ [] ] source-term
source-projection-returns =
  source-term ⟨ X! ⟩ ⟨ X? ⟩
  —→[ keep ]⟨ pure-step (tag-untag source-value) ⟩
  source-term ∎[]

ℕ-type : Ty 1
ℕ-type = ‵ `ℕ

Y-type : Ty 1
Y-type = ＇ Y

ℕ≢Y : ℕ-type ≢ Y-type
ℕ≢Y ()

mismatch-steps-to-blame : mismatch-term —↠[ keep ∷ [] ] blame
mismatch-steps-to-blame =
  mismatch-term
  —→[ keep ]⟨
    pure-step
      (tag-untag-bad
        {μ = target-env-tag}
        {ν = target-env-proj}
        {G = ‵ `ℕ}
        {H = ＇ Y}
        ⦃ Gᵍ = ‵ `ℕ ⦄
        ⦃ Hᵍ = ＇ Y ⦄
        ⦃ G∼★ = Consistency.ι∼★ ⦄
        ⦃ ★∼H = Consistency.★∼Xᵍ refl ⦄
        ⦃ Gns = nonstar-ι ⦄
        ⦃ Hns = nonstar-X ⦄
        target-untagged-value ℕ≢Y)
  ⟩
  blame ∎[]

blame-not-value : ∀ {Δ} → Value (blame {Δ}) → ⊥
blame-not-value ()

mismatch-not-value : Value mismatch-term → ⊥
mismatch-not-value (v 《 () 》)

const-no-pure-step : ∀ {Δ} {N : Term Δ}
  → $ {Δ = Δ} (κℕ 0) —→ N
  → ⊥
const-no-pure-step ()

const-no-step : ∀ {Δ′} {χ : StoreChange 1 Δ′} {N : Term Δ′}
  → $ {Δ = 1} (κℕ 0) —→[ χ ] N
  → ⊥
const-no-step (pure-step step) = const-no-pure-step step

blame-no-pure-step : ∀ {Δ} {N : Term Δ}
  → blame {Δ} —→ N
  → ⊥
blame-no-pure-step ()

blame-no-step : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → blame {Δ} —→[ χ ] N
  → ⊥
blame-no-step (pure-step step) = blame-no-pure-step step

blame-no-value-reduct : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′}
    {N : Term Δ′}
  → blame {Δ} —↠[ χs ] N
  → Value N
  → ⊥
blame-no-value-reduct ↠-refl vN = blame-not-value vN
blame-no-value-reduct (↠-step step rest) vN =
  blame-no-step step

inner-tag-no-pure-step : ∀ {N : Term 1}
  → target-tagged —→ N
  → ⊥
inner-tag-no-pure-step (ground v ℕ≢ℕ) = ℕ≢ℕ refl

inner-tag-no-step : ∀ {Δ′} {χ : StoreChange 1 Δ′} {N : Term Δ′}
  → target-tagged —→[ χ ] N
  → ⊥
inner-tag-no-step (pure-step step) = inner-tag-no-pure-step step
inner-tag-no-step (ξ-⟨⟩ step refl) = const-no-step step

mismatch-no-value-reduct : ∀ {Δ′} {χs : StoreChanges 1 Δ′}
    {N : Term Δ′}
  → mismatch-term —↠[ χs ] N
  → Value N
  → ⊥
mismatch-no-value-reduct ↠-refl vN = mismatch-not-value vN
mismatch-no-value-reduct
    (↠-step (pure-step (expand v G≢G)) rest) vN =
  G≢G refl
mismatch-no-value-reduct
    (↠-step (pure-step (tag-untag-bad v G≢H)) rest) vN =
  blame-no-value-reduct rest vN
mismatch-no-value-reduct
    (↠-step (ξ-⟨⟩ step refl) rest) vN =
  inner-tag-no-step step

projection-mismatch-violates-provenance :
  CatchupCast {W = probe-world} {A = ＇ X}
    probe-p target-tagged Y? probe-q
  → ⊥
projection-mismatch-violates-provenance (catchup-projection ())

extra-cast-right²-contradiction : ExtraCastRight²
  → CatchupCast {W = probe-world} {A = ＇ X}
      probe-p target-tagged Y? probe-q
  → ⊥
extra-cast-right²-contradiction ecr generated
    with ecr input-relation source-value target-tagged-value
      Y? probe-q generated
extra-cast-right²-contradiction ecr generated
    | Δᴿ′ , χs , Δ′ , W′ , ext , N′ , vN′ , M↠N′ , M⊑N′ =
  mismatch-no-value-reduct M↠N′ vN′

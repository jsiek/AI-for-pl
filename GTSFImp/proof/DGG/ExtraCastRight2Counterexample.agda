module proof.DGG.ExtraCastRight2Counterexample where

-- File Charter:
--   * Isolates the type-level obstruction in the bare-seal case of
--     right-injection inversion for CastTermImprecision2.
--   * Builds a valid pivot-local rebase and source seal for which the
--     premise-to-star, conclusion-to-star, and conclusion-to-ground
--     obligations all exist, but the premise-to-ground obligation needed
--     by recursive inversion does not.
--   * Realizes that obstruction with a closed term-imprecision derivation and
--     proves that the relation required after target-tag cancellation is
--     empty when the displaced source variable has a precise center.
--   * Depends only on the version-2 world/rebase definitions and the core
--     type-imprecision relation; it does not change the live relation.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

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
    (λ _ → refl)
    refl
    Z-Y-representation

Z-seal-typed : source-store ⊢↓[ just Z ] seal Z ★
Z-seal-typed = ⊢↓-sealˣ source-Z∋

-- These are exactly the three type obligations available in the
-- conceal⊑² branch of right-injection inversion.

premise-to-star : ★ ⊑ᵂ⟨ pre-world ⟩ ★
premise-to-star = ★⊑★

conclusion-to-star : ＇ Z ⊑ᵂ⟨ post-world ⟩ ★
conclusion-to-star = X⊑★ refl

conclusion-to-tag : ＇ Z ⊑ᵂ⟨ post-world ⟩ ＇ Y
conclusion-to-tag = X⊑X

-- Recursive inversion would need this fourth obligation.  It cannot be
-- built: before the boundary, Y embeds with U, so its target is a variable,
-- while the source seal representation is dynamic.

no-premise-to-tag : ★ ⊑ᵂ⟨ pre-world ⟩ ＇ Y → ⊥
no-premise-to-tag ()

-- The missing premise-to-tag obligation is not merely a type-level corner:
-- paired source/target injections can hide it.  The following closed value
-- relation realizes all the premises of the problematic source-seal branch.

U-Y-representation : CTI2.StoreRepImp pre-world U Y
U-Y-representation = store-rep-imp ι⊑★

U-Y-rebase : RebaseAt pre-world pre-world U Y
U-Y-rebase = CTI2.sameWorldRebaseAt refl U-Y-representation

source-U∈ : source-store ∋ U ⦂ ‵ `ℕ
source-U∈ = source-U∋

source-U-seal-typed : source-store ⊢↓[ just U ] seal U (‵ `ℕ)
source-U-seal-typed = ⊢↓-sealˣ source-U∈

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
  CTI2.conceal⊑conceal² U-Y-rebase CTI2.same-[]
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
  CTI2.conceal⊑² (CTI2.rebase-varᴸ Z-Y-rebase) CTI2.same-[]
    Z-seal-typed inner-paired-tags² conclusion-to-star

-- Unlike Z's center, U's center is precise.  The natural reassociation
-- would need the following obligation, which is therefore empty.

no-U-to-star : ＇ U ⊑ᵂ⟨ pre-world ⟩ ★ → ⊥
no-U-to-star (X⊑★ ())

private
  U≢Z : U ≢ Z
  U≢Z ()

  UPrecise : World 2 1 2 → Set
  UPrecise W =
    CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) U) ≡ X⊑X

  post-U-precise : UPrecise post-world
  post-U-precise = refl

  var-identity-not-star : _≡_ {A = VarImp} X⊑X X⊑★ → ⊥
  var-identity-not-star ()

  U-precise-rebase-back : ∀ {Wᵖ W : World 2 1 2} {Y′}
    → RebaseAt Wᵖ W Z Y′
    → UPrecise W
    → UPrecise Wᵖ
  U-precise-rebase-back {Wᵖ = Wᵖ} {W = W} rb precise =
    trans
      (sym (cong (CTI2.impEnvʷ Wᵖ)
        (CTI2.RebaseAt.ηᴸ-off-pivot rb U≢Z)))
      (trans
        (sym (CTI2.RebaseAt.sameImpEnv rb
          (toRenameᵗ (CTI2.ηᴸʷ W) U)))
        precise)

  U-precise-rebaseᴸ-back : ∀ {Wᵖ W : World 2 1 2}
    → CTI2.RebaseAtᴸ Wᵖ W (just Z)
    → UPrecise W
    → UPrecise Wᵖ
  U-precise-rebaseᴸ-back (CTI2.rebase-varᴸ rb) precise =
    U-precise-rebase-back rb precise
  U-precise-rebaseᴸ-back
      (CTI2.rebase-onlyᴸ to-star disaligned represented) precise =
    precise

  no-U-to-star-at : ∀ {W : World 2 1 2}
    → UPrecise W
    → ＇ U ⊑ᵂ⟨ W ⟩ ★
    → ⊥
  no-U-to-star-at precise (X⊑★ eq) =
    var-identity-not-star (trans (sym precise) eq)

  variable-not-base : ∀ {W : World 2 1 2} {X : TyVar 2}
    → ＇ X ⊑ᵂ⟨ W ⟩ ‵ `ℕ
    → ⊥
  variable-not-base ()

  star-not-base : ∀ {W : World 2 1 2}
    → ★ ⊑ᵂ⟨ W ⟩ ‵ `ℕ
    → ⊥
  star-not-base ()

  star-not-variable : ∀ {W : World 2 1 2}
    → ★ ⊑ᵂ⟨ W ⟩ ＇ Y
    → ⊥
  star-not-variable ()

  no-inner-tags : ∀ {W : World 2 1 2} {γ : CTI2.CtxImp W}
      {p : ★ ⊑ᵂ⟨ W ⟩ ★}
    → UPrecise W
    → W ∣ γ ⊢² (($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩
        ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ p
    → ⊥
  no-inner-tags {W = W} precise
      (CTI2.cast⊑cast² {p = p} c c′ prem q) =
    variable-not-base {W = W} {X = U} p
  no-inner-tags {W = W} precise
      (CTI2.⊑cast² {p = p} c′ prem q) =
    star-not-base {W = W} p
  no-inner-tags {W = W} precise
      (CTI2.cast⊑² {p = p} c prem q) =
    no-U-to-star-at {W = W} precise p

  no-outer-vs-tag : ∀ {W : World 2 1 2} {γ : CTI2.CtxImp W}
      {p : ＇ Z ⊑ᵂ⟨ W ⟩ ★}
    → UPrecise W
    → W ∣ γ ⊢²
        ((($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩) ↓ seal Z ★
        ⊑ $ (κℕ 0) ⟨ ℕ! ⟩ ∶ p
    → ⊥
  no-outer-vs-tag {W = W} precise
      (CTI2.⊑cast² {p = p} c′ prem q) =
    variable-not-base {W = W} {X = Z} p
  no-outer-vs-tag precise
      (CTI2.conceal⊑² rb sc (CTI2.⊢↓-sealˣ x∋) prem q) =
    no-inner-tags (U-precise-rebaseᴸ-back rb precise) prem

  target-rebase-source : ∀ {Wᵖ : World 2 1 2}
    → CTI2.RebaseAtᴿ Wᵖ post-world (just Y)
    → RebaseAt Wᵖ post-world Z Y
  target-rebase-source
      (CTI2.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
    rb
  target-rebase-source
      (CTI2.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero} rb)
      with CTI2.RebaseAt.pivotAligned rb
  target-rebase-source
      (CTI2.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero} rb) | ()

no-problematic-result :
    post-world ∣ [] ⊢²
      ((($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩) ↓ seal Z ★
      ⊑ ($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★ ∶ conclusion-to-tag
    → ⊥
no-problematic-result
    (CTI2.⊑conceal² rb sc (CTI2.⊢↓-sealˣ x∋) prem q) =
  no-outer-vs-tag
    (U-precise-rebase-back (target-rebase-source rb) post-U-precise)
    prem
no-problematic-result
    (CTI2.conceal⊑² {W′ = W′} {p = p} rb sc c⊢ prem q) =
  star-not-variable {W = W′} p
no-problematic-result
    (CTI2.conceal⊑conceal² rb sc
      (CTI2.⊢↓-sealˣ x∋) (CTI2.⊢↓-sealˣ y∋) prem q) =
  no-inner-tags (U-precise-rebase-back rb post-U-precise) prem

-- Thus no bare-seal extension of right-injection inversion can cover this
-- valid input derivation.  Type-imprecision proof irrelevance cannot repair
-- the failure: the required conclusion has no inhabitant at all.

no-bare-seal-right-inj² :
    (post-world ∣ [] ⊢²
        ((($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩) ↓ seal Z ★
        ⊑ (($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★) ⟨ Y! ⟩ ∶
          conclusion-to-star
      → post-world ∣ [] ⊢²
        ((($ (κℕ 0)) ↓ seal U (‵ `ℕ)) ⟨ U! ⟩) ↓ seal Z ★
        ⊑ ($ (κℕ 0) ⟨ ℕ! ⟩) ↓ seal Y ★ ∶ conclusion-to-tag)
    → ⊥
no-bare-seal-right-inj² invert =
  no-problematic-result (invert problematic-seal²)

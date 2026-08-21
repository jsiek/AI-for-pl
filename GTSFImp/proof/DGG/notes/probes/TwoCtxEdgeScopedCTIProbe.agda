{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxEdgeScopedCTIProbe where

-- File Charter:
--   * Extends one exact administrative alias edge with a constructor-form,
--     mode-indexed cast-term-imprecision surface.
--   * Ordinary syntax preserves the current mode.  Exact direct target
--     reveal/conceal boundaries push or pop one focus.
--   * Source-only conceal requires a directly typed conversion at a source
--     pivot that has no stable target occupant.  Paired conversions need no
--     predicate inspecting either child term.
--   * Checks beta := alpha := star reveals and a scoped lambda/body variable.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; TyVar; ★; ＇_; ‵_; _⇒_; renameᵗ)
open import TyStore using (_∋_⦂_; Z∋; S-bind∋)
import TermCtx as TC
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Conversion using (unseal; seal)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; `_; ƛ_; _·_; _↑_; _↓_)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxEdgeIndexedModeProbe using
  (ExactAliasEdgeᵉ; edge-head; edgeEmbed; edge-beta-fresh)


module EdgeScopedCTI {Cᴸ C C⁺} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (name-focus : TargetNameFocusᶠ₀ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺) where

  data Mode : Set where
    stable : Mode
    push-focus : Mode → TyVar (Δᵉ C⁺) → Mode

  data TargetVarView : Mode → TyVar (Δᵉ C⁺) →
      TyVar (centerᶜ₀ W) → Set where
    stable-old : ∀ {Y Y⁺ Z}
      → edgeEmbed edge Y ≡ Y⁺
      → toRenameᵗ (ηᴿᶜ₀ W) Y ≡ Z
      → TargetVarView stable Y⁺ Z

    focus-here : ∀ {m Y Z}
      → toRenameᵗ (ηᴸᶜ₀ W) X ≡ Z
      → TargetVarView (push-focus m Y) Y Z

    focus-there : ∀ {m Y Y′ Z}
      → Y ≢ Y′
      → TargetVarView m Y′ Z
      → TargetVarView (push-focus m Y) Y′ Z

  stable-beta-unavailable : ∀ {Z}
    → TargetVarView stable beta Z → ⊥
  stable-beta-unavailable
      (stable-old {Y = Y} edge-eq center-eq) =
    edge-beta-fresh edge Y edge-eq

  data TargetTypeView (m : Mode) :
      Ty (Δᵉ C⁺) → Ty (centerᶜ₀ W) → Set where
    view-var : ∀ {Y Z}
      → TargetVarView m Y Z
      → TargetTypeView m (＇ Y) (＇ Z)

    view-base : ∀ {ι}
      → TargetTypeView m (‵ ι) (‵ ι)

    view-star : TargetTypeView m ★ ★

    view-fun : ∀ {A B A′ B′}
      → TargetTypeView m A A′
      → TargetTypeView m B B′
      → TargetTypeView m (A ⇒ B) (A′ ⇒ B′)

  data ScopedType (m : Mode) :
      Ty (Δᵉ Cᴸ) → Ty (Δᵉ C⁺) → Set where
    scoped-type : ∀ {A B Bᶜ}
      → TargetTypeView m B Bᶜ
      → I._⊢_⊑_ (marksᶜ₀ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A) Bᶜ
      → ScopedType m A B

  scoped-fun : ∀ {m A B A′ B′}
    → ScopedType m A A′
    → ScopedType m B B′
    → ScopedType m (A ⇒ B) (A′ ⇒ B′)
  scoped-fun (scoped-type view-A pA) (scoped-type view-B pB) =
    scoped-type (view-fun view-A view-B) (I.⇒⊑⇒ pA pB)

  focused-var : ∀ {m Y}
    → ScopedType (push-focus m Y) (＇ X) (＇ Y)
  focused-var = scoped-type (view-var (focus-here refl)) I.X⊑X

  data ExactTargetBoundary (m : Mode) :
      (Y : TyVar (Δᵉ C⁺)) (R : Ty (Δᵉ C⁺))
      → ScopedType m (＇ X) R → Set where
    direct-target : ∀ {Y R q}
      → Σᵉ C⁺ ∋ Y ⦂ R
      → ExactTargetBoundary m Y R q

  data ValidMode : Mode → Set where
    stable-valid : ValidMode stable
    push-valid : ∀ {m Y R q}
      → ValidMode m
      → ExactTargetBoundary m Y R q
      → ValidMode (push-focus m Y)

  -- Each term binding remembers the mode in which its endpoint types are
  -- related.  Thus an ambient x : beta remains available while a result type
  -- is revealed outward through beta, alpha, and star.

  data ScopedWorld : Ctx → Ctx → Set where
    scoped-root : ScopedWorld Cᴸ C⁺

    scoped-bind : ∀ {Gammaᴸ Gammaᴿ A B m}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      → (ok : ValidMode m)
      → (p : ScopedType m A B)
      → ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , A ∷ Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , B ∷ Gammaᴿ ⟩

  data ScopedEntry : ∀ {Gammaᴸ Gammaᴿ}
      (S : ScopedWorld
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩)
      (x : Nat.ℕ) {m : Mode} (ok : ValidMode m)
      {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ C⁺)}
      (p : ScopedType m A B) → Set where
    entry-here : ∀ {Gammaᴸ Gammaᴿ A B m}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {ok : ValidMode m} {p : ScopedType m A B}
      → ScopedEntry (scoped-bind {S = S} ok p) Nat.zero ok p

    entry-there : ∀ {Gammaᴸ Gammaᴿ x A B A₀ B₀ m m₀}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {ok : ValidMode m} {ok₀ : ValidMode m₀}
        {p : ScopedType m A B} {p₀ : ScopedType m₀ A₀ B₀}
      → ScopedEntry S x ok p
      → ScopedEntry (scoped-bind {S = S} ok₀ p₀) (Nat.suc x) ok p

  SourcePivotUnoccupied : Mode → TyVar (Δᵉ Cᴸ) → Set
  SourcePivotUnoccupied m Z = ∀ {Y Zᶜ}
    → TargetVarView m Y Zᶜ
    → toRenameᵗ (ηᴸᶜ₀ W) Z ≢ Zᶜ

  data ScopedCTI :
      (m : Mode) → ValidMode m → ∀ {Gammaᴸ Gammaᴿ}
      (S : ScopedWorld
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩)
      → Term (Δᵉ Cᴸ) → Term (Δᵉ C⁺)
      → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ C⁺)}
      → ScopedType m A B → Set where

    var⊑var : ∀ {m ok Gammaᴸ Gammaᴿ x A B p}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      → ScopedEntry {Gammaᴸ} {Gammaᴿ} S x ok p
      → ScopedCTI m ok S (` x) (` x) {A} {B} p

    lambda⊑lambda : ∀
        {m ok Gammaᴸ Gammaᴿ M M′ A A′ B B′}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {pA : ScopedType m A A′} {pB : ScopedType m B B′}
      → ScopedCTI m ok (scoped-bind {S = S} ok pA) M M′ pB
      → ScopedCTI m ok S (ƛ M) (ƛ M′) (scoped-fun pA pB)

    app⊑app : ∀
        {m ok Gammaᴸ Gammaᴿ L L′ M M′ A A′ B B′}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {pA : ScopedType m A A′} {pB : ScopedType m B B′}
      → ScopedCTI m ok S L L′ (scoped-fun pA pB)
      → ScopedCTI m ok S M M′ pA
      → ScopedCTI m ok S (L · M) (L′ · M′) pB

    target-reveal : ∀ {m ok Gammaᴸ Gammaᴿ M M′ Y R q}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      → (boundary : ExactTargetBoundary m Y R q)
      → ScopedCTI (push-focus m Y) (push-valid ok boundary)
          S M M′ focused-var
      → ScopedCTI m ok S M (M′ ↑ unseal Y R) q

    target-conceal : ∀ {m ok Gammaᴸ Gammaᴿ M M′ Y R q}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      → (boundary : ExactTargetBoundary m Y R q)
      → ScopedCTI m ok S M M′ q
      → ScopedCTI (push-focus m Y) (push-valid ok boundary)
          S M (M′ ↓ seal Y R) focused-var

    source-conceal : ∀
        {m ok Gammaᴸ Gammaᴿ M M′ Z R B}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {p : ScopedType m (＇ Z) B} {q : ScopedType m R B}
      → SourcePivotUnoccupied m Z
      → Σᵉ Cᴸ ∋ Z ⦂ R
      → ScopedCTI m ok S M M′ q
      → ScopedCTI m ok S (M ↓ seal Z R) M′
          {A = ＇ Z} {B = B} p

    paired-reveal : ∀
        {m ok Gammaᴸ Gammaᴿ M M′ Z Y R R′}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {p : ScopedType m (＇ Z) (＇ Y)}
        {q : ScopedType m R R′}
      → Σᵉ Cᴸ ∋ Z ⦂ R
      → Σᵉ C⁺ ∋ Y ⦂ R′
      → ScopedCTI m ok S M M′ p
      → ScopedCTI m ok S
          (M ↑ unseal Z R) (M′ ↑ unseal Y R′) q

    paired-conceal : ∀
        {m ok Gammaᴸ Gammaᴿ M M′ Z Y R R′}
        {S : ScopedWorld
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
        {p : ScopedType m (＇ Z) (＇ Y)}
        {q : ScopedType m R R′}
      → Σᵉ Cᴸ ∋ Z ⦂ R
      → Σᵉ C⁺ ∋ Y ⦂ R′
      → ScopedCTI m ok S M M′ q
      → ScopedCTI m ok S
          (M ↓ seal Z R) (M′ ↓ seal Y R′) p


head-edge : ExactAliasEdgeᵉ
  target-alpha-context target-alpha-beta-context
  target-alpha target-beta target-alpha⁺
head-edge = edge-head refl

module StrictCTI = EdgeScopedCTI strict-lambda-focus head-edge

open StrictCTI

stable-X-star : ScopedType stable (＇ source-X) ★
stable-X-star = scoped-type view-star (I.X⊑★ refl)

target-alpha-member :
  Σᵉ target-alpha-beta-context ∋ target-alpha⁺ ⦂ ★
target-alpha-member = S-bind∋ (Z∋ refl) refl

alpha-boundary : ExactTargetBoundary stable target-alpha⁺ ★ stable-X-star
alpha-boundary = direct-target target-alpha-member

alpha-mode : Mode
alpha-mode = push-focus stable target-alpha⁺

alpha-valid : ValidMode alpha-mode
alpha-valid = push-valid stable-valid alpha-boundary

alpha-type : ScopedType alpha-mode
  (＇ source-X) (＇ target-alpha⁺)
alpha-type = focused-var

target-beta-member :
  Σᵉ target-alpha-beta-context ∋ target-beta ⦂ ＇ target-alpha⁺
target-beta-member = Z∋ refl

beta-boundary : ExactTargetBoundary alpha-mode target-beta
  (＇ target-alpha⁺) alpha-type
beta-boundary = direct-target target-beta-member

beta-mode : Mode
beta-mode = push-focus alpha-mode target-beta

beta-valid : ValidMode beta-mode
beta-valid = push-valid alpha-valid beta-boundary

beta-type : ScopedType beta-mode (＇ source-X) (＇ target-beta)
beta-type = focused-var

beta-scope : ScopedWorld
  ⟨ Δᵉ source-X-context , Σᵉ source-X-context ,
    (＇ source-X) ∷ [] ⟩
  ⟨ Δᵉ target-alpha-beta-context ,
    Σᵉ target-alpha-beta-context , (＇ target-beta) ∷ [] ⟩
beta-scope = scoped-bind {S = scoped-root} beta-valid beta-type

beta-entry : ScopedEntry beta-scope Nat.zero beta-valid beta-type
beta-entry = entry-here {S = scoped-root}

beta-variable : ScopedCTI beta-mode beta-valid beta-scope
  (` Nat.zero) (` Nat.zero) beta-type
beta-variable = var⊑var beta-entry

beta-reveal : ScopedCTI alpha-mode alpha-valid beta-scope
  (` Nat.zero) ((` Nat.zero) ↑ unseal target-beta (＇ target-alpha⁺))
  alpha-type
beta-reveal = target-reveal beta-boundary beta-variable

beta-alpha-reveals : ScopedCTI stable stable-valid beta-scope
  (` Nat.zero)
  (((` Nat.zero) ↑ unseal target-beta (＇ target-alpha⁺))
    ↑ unseal target-alpha⁺ ★)
  stable-X-star
beta-alpha-reveals = target-reveal alpha-boundary beta-reveal

alpha-conceal-after-reveals : ScopedCTI alpha-mode alpha-valid beta-scope
  (` Nat.zero)
  ((((` Nat.zero) ↑ unseal target-beta (＇ target-alpha⁺))
    ↑ unseal target-alpha⁺ ★) ↓ seal target-alpha⁺ ★)
  alpha-type
alpha-conceal-after-reveals =
  target-conceal alpha-boundary beta-alpha-reveals

beta-lambda-body : ScopedCTI beta-mode beta-valid beta-scope
  (` Nat.zero) (` Nat.zero) beta-type
beta-lambda-body = var⊑var beta-entry

beta-lambda : ScopedCTI beta-mode beta-valid scoped-root
  (ƛ (` Nat.zero)) (ƛ (` Nat.zero)) (scoped-fun beta-type beta-type)
beta-lambda = lambda⊑lambda {S = scoped-root} beta-lambda-body

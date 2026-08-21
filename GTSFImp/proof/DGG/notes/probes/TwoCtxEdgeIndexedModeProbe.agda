{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxEdgeIndexedModeProbe where

-- File Charter:
--   * Indexes a two-state alias-focus mode by one structural direct edge.
--   * The edge records stable alpha, boundary beta, and boundary alpha and is
--     closed under lift prefixes.
--   * Checks head and lifted behavior plus a focused scoped variable leaf.

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (_∷_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl)

open import Types using (Ty; TyVar; ★; ＇_; _⇒_; renameᵗ)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
import Imprecision as I
open import Consistency using (toRenameᵗ)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; `_; ⇑ᵉᵗ)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxScopedTermBoundaryProbe using
  (boundary-world)


data ExactAliasEdgeᵉ :
    (C C⁺ : Ctx) → TyVar (Δᵉ C) →
    TyVar (Δᵉ C⁺) → TyVar (Δᵉ C⁺) → Set where
  edge-head : ∀ {Δ} {Σ : TyStore Δ} {Γ : TC.TermCtx Δ}
      {Γ⁺ : TC.TermCtx (Nat.suc Δ)} {alpha : TyVar Δ}
    → Γ⁺ ≡ TC.⇑ᶜ Γ
    → ExactAliasEdgeᵉ
        ⟨ Δ , Σ , Γ ⟩
        ⟨ Nat.suc Δ , store-bind Σ (＇ alpha) , Γ⁺ ⟩
        alpha zero (suc alpha)

  edge-lift : ∀ {C C⁺ alpha beta alpha⁺}
    → ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺
    → ExactAliasEdgeᵉ (⇑ᵉᵗ C) (⇑ᵉᵗ C⁺)
        (suc alpha) (suc beta) (suc alpha⁺)


edgeEmbed : ∀ {C C⁺ alpha beta alpha⁺}
  → ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺
  → TyVar (Δᵉ C) → TyVar (Δᵉ C⁺)
edgeEmbed (edge-head eq) Y = suc Y
edgeEmbed (edge-lift edge) zero = zero
edgeEmbed (edge-lift edge) (suc Y) = suc (edgeEmbed edge Y)

edge-alpha : ∀ {C C⁺ alpha beta alpha⁺}
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → edgeEmbed edge alpha ≡ alpha⁺
edge-alpha (edge-head eq) = refl
edge-alpha (edge-lift edge) = cong suc (edge-alpha edge)

edge-beta-fresh : ∀ {C C⁺ alpha beta alpha⁺}
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺) Y
  → edgeEmbed edge Y ≢ beta
edge-beta-fresh (edge-head eq) Y ()
edge-beta-fresh (edge-lift edge) zero ()
edge-beta-fresh (edge-lift edge) (suc Y) eq =
  edge-beta-fresh edge Y (suc-injective eq)
  where
  suc-injective : ∀ {n} {X Y : Fin n} → suc X ≡ suc Y → X ≡ Y
  suc-injective refl = refl


module EdgeMode {Cᴸ C C⁺} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : TargetNameFocusᶠ₀ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺) where

  data Mode : Set where
    stable focused : Mode

  data TargetVarView : Mode → TyVar (Δᵉ C⁺) →
      TyVar (centerᶜ₀ W) → Set where
    stable-old : ∀ {Y Y⁺ Z}
      → edgeEmbed edge Y ≡ Y⁺
      → toRenameᵗ (ηᴿᶜ₀ W) Y ≡ Z
      → TargetVarView stable Y⁺ Z

    focus-beta : ∀ {Z}
      → toRenameᵗ (ηᴸᶜ₀ W) X ≡ Z
      → TargetVarView focused beta Z

    focus-old : ∀ {Y Y⁺ Z}
      → edgeEmbed edge Y ≡ Y⁺
      → toRenameᵗ (ηᴿᶜ₀ W) Y ≡ Z
      → TargetVarView focused Y⁺ Z

  stable-beta-unavailable : ∀ {Z}
    → TargetVarView stable beta Z → ⊥
  stable-beta-unavailable (stable-old {Y = Y} edge-eq center-eq) =
    edge-beta-fresh edge Y edge-eq

  data TargetTypeView (m : Mode) :
      Ty (Δᵉ C⁺) → Ty (centerᶜ₀ W) → Set where
    view-var : ∀ {Y Z} → TargetVarView m Y Z
      → TargetTypeView m (＇ Y) (＇ Z)
    view-star : TargetTypeView m ★ ★
    view-fun : ∀ {A B A′ B′}
      → TargetTypeView m A A′ → TargetTypeView m B B′
      → TargetTypeView m (A ⇒ B) (A′ ⇒ B′)

  data ScopedType (m : Mode) :
      Ty (Δᵉ Cᴸ) → Ty (Δᵉ C⁺) → Set where
    scoped-type : ∀ {A B Bᶜ}
      → TargetTypeView m B Bᶜ
      → I._⊢_⊑_ (marksᶜ₀ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A) Bᶜ
      → ScopedType m A B

  beta-type : ScopedType focused (＇ X) (＇ beta)
  beta-type = scoped-type (view-var (focus-beta refl)) I.X⊑X

  data ScopedWorld (m : Mode) : Ctx → Ctx → Set where
    scoped-root : ScopedWorld m Cᴸ C⁺
    scoped-bind : ∀ {Γᴸ Γᴿ A B}
      → ScopedWorld m
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Γᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Γᴿ ⟩
      → ScopedType m A B
      → ScopedWorld m
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , A ∷ Γᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , B ∷ Γᴿ ⟩

  beta-body-world = scoped-bind scoped-root beta-type

  data ScopedEntry {m} : ∀ {Γᴸ Γᴿ}
      (S : ScopedWorld m
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Γᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Γᴿ ⟩) →
      (x : Nat.ℕ) → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ C⁺)} →
      ScopedType m A B → Set where
    entry-here : ∀ {Γᴸ Γᴿ A B}
        {S : ScopedWorld m
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Γᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Γᴿ ⟩}
        {p : ScopedType m A B}
      → ScopedEntry (scoped-bind S p) Nat.zero p

    entry-there : ∀ {Γᴸ Γᴿ x A B A₀ B₀}
        {S : ScopedWorld m
          ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Γᴸ ⟩
          ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Γᴿ ⟩}
        {p : ScopedType m A B} {p₀ : ScopedType m A₀ B₀}
      → ScopedEntry S x p
      → ScopedEntry (scoped-bind S p₀) (Nat.suc x) p

  beta-body-entry : ScopedEntry beta-body-world Nat.zero beta-type
  beta-body-entry = entry-here

  data VariableLeaf {m Γᴸ Γᴿ}
      (S : ScopedWorld m
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Γᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Γᴿ ⟩) :
      Term (Δᵉ Cᴸ) → Term (Δᵉ C⁺) → Set where
    beta-var : ∀ {x A B} {p : ScopedType m A B}
      → ScopedEntry S x p
      → VariableLeaf S (` x) (` x)

  beta-variable : VariableLeaf beta-body-world (` Nat.zero) (` Nat.zero)
  beta-variable = beta-var beta-body-entry


head-edge : ExactAliasEdgeᵉ
  target-alpha-context target-alpha-beta-context
  target-alpha target-beta target-alpha⁺
head-edge = edge-head refl

module HeadMode = EdgeMode strict-lambda-focus head-edge

lifted-edge = edge-lift head-edge
lifted-world = liftBothᶜ₀ I.X⊑X stable-world

lifted-focus : TargetNameFocusᶠ₀ lifted-world
  (suc source-X) (suc target-alpha)
lifted-focus = target-name-focusᶠ₀ separated refl (I.X⊑★ refl)
  where
  separated :
    toRenameᵗ (ηᴸᶜ₀ lifted-world) (suc source-X) ≢
    toRenameᵗ (ηᴿᶜ₀ lifted-world) (suc target-alpha)
  separated ()

module LiftedMode = EdgeMode lifted-focus lifted-edge

lifted-beta-variable : LiftedMode.VariableLeaf
  LiftedMode.beta-body-world (` Nat.zero) (` Nat.zero)
lifted-beta-variable = LiftedMode.beta-variable

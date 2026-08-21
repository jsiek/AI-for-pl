{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxGlobalIndexedCTIProbe where

-- File Charter:
--   * Globalizes the two-Ctx edge-scoped CTI state so universal recursion may
--     change every endpoint, world, focus, edge, mode, and term-context index.
--   * Gives structural one-prefix lifts for focus modes, valid boundaries,
--     scoped types, heterogeneous term worlds, and term entries.
--   * Checks ordinary terms, genuine Lambda, and type application without a
--     compatibility wrapper around the earlier fixed-parameter probe.
--   * Covers primitive application and both paired and source-only type
--     application, matching the syntax-directed compiler surface.
--   * Keeps source-only conceal unoccupied and paired seal rules independent
--     of term shape.

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; sym; trans)

open import Types using
  (Ty; TyCtx; TyVar; ★; ＇_; ‵_; _⇒_; `∀; extᵗ; ⇑ᵗ; renameᵗ;
   _[_]ᵗ; renameᵗ-cong; renameᵗ-comp; renameᵗ-shift)
open import TyStore using
  (TyStore; lookupStore; store-lift; _∋_⦂_; Z∋; S-lift∋; S-bind∋)
import TermCtx as TC
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; keep; toRenameᵗ)
import Imprecision as I
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _⊢↑[_]_; _⊢↓[_]_; ⊢↑-unsealˣ;
   ⊢↓-sealˣ; ⊢↑-⇒ˣ; join-both)
open import Primitives using
  (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; Value; `_; ƛ_; Λ_;
   _·_; $; _⊕[_]_; _⟨_⟩; _⦂∀_[_]; _↑_; _↓_; blame; ⇑ᵉᵗ; _⊢_⦂_)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.DGG.World
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe using
  (source-X-context; target-alpha-context; target-alpha-beta-context;
   stable-world; source-X; target-alpha; target-beta; target-alpha⁺;
   stable-X-alpha-separated; stable-X-self;
   stable-direct-representations-proof)
open import proof.DGG.notes.probes.TwoCtxEdgeIndexedModeProbe using
  (ExactAliasEdgeᵉ; edge-head; edge-lift; edgeEmbed)


private
  fin-suc-injective : ∀ {n} {X Y : Fin n}
    → suc X ≡ suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

  imprecision-cong : ∀ {Delta} {mu : I.ImpEnv Delta}
      {A A′ B B′ : Ty Delta}
    → A ≡ A′
    → B ≡ B′
    → I._⊢_⊑_ mu A B
    → I._⊢_⊑_ mu A′ B′
  imprecision-cong refl refl p = p

  rename-keep-shift : ∀ {Delta₀ Delta}
      (eta : Delta₀ ↪ᵗ Delta) (A : Ty Delta₀)
    → renameᵗ (toRenameᵗ (keep eta)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ eta) A)
  rename-keep-shift eta A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq eta))
      (renameᵗ-shift (toRenameᵗ eta) A)

  lift-imprecision : ∀ {Delta} {mu : I.ImpEnv Delta} {v A B}
    → I._⊢_⊑_ mu A B
    → I._⊢_⊑_ (I.extendᵐ v mu) (⇑ᵗ A) (⇑ᵗ B)
  lift-imprecision p = rename-⊑ suc fin-suc-injective (λ X eq → eq) p


data NameFocusᵍ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ Cᴿ) → Set where
  name-focusᵍ : ∀ {X alpha}
    → toRenameᵗ (ηᴸᶜ W) X ≢ toRenameᵗ (ηᴿᶜ W) alpha
    → lookupStore (Σᵉ Cᴸ) X ≡ ＇ X
    → lookupStore (Σᵉ Cᴸ) X ⊑ᵀ⟨ W ⟩
        lookupStore (Σᵉ Cᴿ) alpha
    → NameFocusᵍ W X alpha


liftNameFocusᵍ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {X alpha}
  → NameFocusᵍ W X alpha
  → NameFocusᵍ (liftBothᶜ I.X⊑X W) (suc X) (suc alpha)
liftNameFocusᵍ {Cᴸ} {Cᴿ} {W} {X} {alpha}
    (name-focusᵍ separated self reps) =
  name-focusᵍ lifted-separated (cong ⇑ᵗ self) lifted-reps
  where
  lifted-separated :
    toRenameᵗ (ηᴸᶜ (liftBothᶜ I.X⊑X W)) (suc X)
      ≢ toRenameᵗ (ηᴿᶜ (liftBothᶜ I.X⊑X W))
          (suc alpha)
  lifted-separated eq = separated (fin-suc-injective eq)

  lifted-reps :
    lookupStore (Σᵉ (⇑ᵉᵗ Cᴸ)) (suc X)
      ⊑ᵀ⟨ liftBothᶜ I.X⊑X W ⟩
    lookupStore (Σᵉ (⇑ᵉᵗ Cᴿ)) (suc alpha)
  lifted-reps =
    imprecision-cong
      (sym (rename-keep-shift (ηᴸᶜ W)
        (lookupStore (Σᵉ Cᴸ) X)))
      (sym (rename-keep-shift (ηᴿᶜ W)
        (lookupStore (Σᵉ Cᴿ) alpha)))
      (lift-imprecision reps)


data Modeᵍ {C C⁺ : Ctx} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺) : Set where
  stableᵍ : Modeᵍ edge
  push-focusᵍ : Modeᵍ edge → TyVar (Δᵉ C⁺) → Modeᵍ edge


data ModeLiftᵍ {C C⁺ alpha beta alpha⁺}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺} :
    Modeᵍ edge → Modeᵍ (edge-lift edge) → Set where
  lift-stableᵍ : ModeLiftᵍ stableᵍ stableᵍ
  lift-pushᵍ : ∀ {m m⁺ Y}
    → ModeLiftᵍ m m⁺
    → ModeLiftᵍ (push-focusᵍ m Y)
        (push-focusᵍ m⁺ (suc Y))


data LiftPrefixᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocusᵍ W X alpha
  → ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺
  → Set where
  prefix-hereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → LiftPrefixᵍ focus edge

  prefix-underᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → LiftPrefixᵍ focus edge
    → LiftPrefixᵍ (liftNameFocusᵍ focus) (edge-lift edge)


insertWorldᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
  → LiftPrefixᵍ focus edge
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ ⇑ᵉᵗ C
insertWorldᵍ {W = W} prefix-hereᵍ = liftBothᶜ I.X⊑X W
insertWorldᵍ (prefix-underᵍ prefix) =
  liftBothᶜ I.X⊑X (insertWorldᵍ prefix)


insertSourceᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
  → LiftPrefixᵍ focus edge
  → TyVar (Δᵉ Cᴸ) → TyVar (Nat.suc (Δᵉ Cᴸ))
insertSourceᵍ prefix-hereᵍ Y = suc Y
insertSourceᵍ (prefix-underᵍ prefix) zero = zero
insertSourceᵍ (prefix-underᵍ prefix) (suc Y) =
  suc (insertSourceᵍ prefix Y)


insertStableᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
  → LiftPrefixᵍ focus edge
  → TyVar (Δᵉ C) → TyVar (Nat.suc (Δᵉ C))
insertStableᵍ prefix-hereᵍ Y = suc Y
insertStableᵍ (prefix-underᵍ prefix) zero = zero
insertStableᵍ (prefix-underᵍ prefix) (suc Y) =
  suc (insertStableᵍ prefix Y)


insertTargetᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
  → LiftPrefixᵍ focus edge
  → TyVar (Δᵉ C⁺) → TyVar (Nat.suc (Δᵉ C⁺))
insertTargetᵍ prefix-hereᵍ Y = suc Y
insertTargetᵍ (prefix-underᵍ prefix) zero = zero
insertTargetᵍ (prefix-underᵍ prefix) (suc Y) =
  suc (insertTargetᵍ prefix Y)


insertCenterᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge)
  → TyVar (centerᶜ W)
  → TyVar (centerᶜ (insertWorldᵍ prefix))
insertCenterᵍ prefix-hereᵍ Y = suc Y
insertCenterᵍ (prefix-underᵍ prefix) zero = zero
insertCenterᵍ (prefix-underᵍ prefix) (suc Y) =
  suc (insertCenterᵍ prefix Y)


insertFocusᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge)
  → NameFocusᵍ (insertWorldᵍ prefix)
      (insertSourceᵍ prefix X) (insertStableᵍ prefix alpha)
insertFocusᵍ {focus = focus} prefix-hereᵍ =
  liftNameFocusᵍ focus
insertFocusᵍ (prefix-underᵍ prefix) =
  liftNameFocusᵍ (insertFocusᵍ prefix)


insertEdgeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge)
  → ExactAliasEdgeᵉ (⇑ᵉᵗ C) (⇑ᵉᵗ C⁺)
      (insertStableᵍ prefix alpha)
      (insertTargetᵍ prefix beta)
      (insertTargetᵍ prefix alpha⁺)
insertEdgeᵍ {edge = edge} prefix-hereᵍ = edge-lift edge
insertEdgeᵍ (prefix-underᵍ prefix) =
  edge-lift (insertEdgeᵍ prefix)


insertModeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge)
  → Modeᵍ edge → Modeᵍ (insertEdgeᵍ prefix)
insertModeᵍ prefix stableᵍ = stableᵍ
insertModeᵍ prefix (push-focusᵍ m Y) =
  push-focusᵍ (insertModeᵍ prefix m) (insertTargetᵍ prefix Y)


insertModeLiftᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) {m : Modeᵍ edge}
    {m⁺ : Modeᵍ (edge-lift edge)}
  → ModeLiftᵍ m m⁺
  → ModeLiftᵍ (insertModeᵍ prefix m)
      (insertModeᵍ (prefix-underᵍ prefix) m⁺)
insertModeLiftᵍ prefix lift-stableᵍ = lift-stableᵍ
insertModeLiftᵍ prefix (lift-pushᵍ mode-lift) =
  lift-pushᵍ (insertModeLiftᵍ prefix mode-lift)


prefix-here-mode-liftᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge)
  → ModeLiftᵍ m
      (insertModeᵍ (prefix-hereᵍ {focus = focus} {edge = edge}) m)
prefix-here-mode-liftᵍ focus edge stableᵍ = lift-stableᵍ
prefix-here-mode-liftᵍ focus edge (push-focusᵍ m Y) =
  lift-pushᵍ (prefix-here-mode-liftᵍ focus edge m)


insertSource-injectiveᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) {Y Z}
  → insertSourceᵍ prefix Y ≡ insertSourceᵍ prefix Z
  → Y ≡ Z
insertSource-injectiveᵍ prefix-hereᵍ eq = fin-suc-injective eq
insertSource-injectiveᵍ (prefix-underᵍ prefix)
    {zero} {zero} eq = refl
insertSource-injectiveᵍ (prefix-underᵍ prefix)
    {zero} {suc Z} ()
insertSource-injectiveᵍ (prefix-underᵍ prefix)
    {suc Y} {zero} ()
insertSource-injectiveᵍ (prefix-underᵍ prefix)
    {suc Y} {suc Z} eq =
  cong suc (insertSource-injectiveᵍ prefix
    (fin-suc-injective eq))


insertTarget-injectiveᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) {Y Z}
  → insertTargetᵍ prefix Y ≡ insertTargetᵍ prefix Z
  → Y ≡ Z
insertTarget-injectiveᵍ prefix-hereᵍ eq = fin-suc-injective eq
insertTarget-injectiveᵍ (prefix-underᵍ prefix)
    {zero} {zero} eq = refl
insertTarget-injectiveᵍ (prefix-underᵍ prefix)
    {zero} {suc Z} ()
insertTarget-injectiveᵍ (prefix-underᵍ prefix)
    {suc Y} {zero} ()
insertTarget-injectiveᵍ (prefix-underᵍ prefix)
    {suc Y} {suc Z} eq =
  cong suc (insertTarget-injectiveᵍ prefix
    (fin-suc-injective eq))


insertCenter-injectiveᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) {Y Z}
  → insertCenterᵍ prefix Y ≡ insertCenterᵍ prefix Z
  → Y ≡ Z
insertCenter-injectiveᵍ prefix-hereᵍ eq = fin-suc-injective eq
insertCenter-injectiveᵍ (prefix-underᵍ prefix)
    {zero} {zero} eq = refl
insertCenter-injectiveᵍ (prefix-underᵍ prefix)
    {zero} {suc Z} ()
insertCenter-injectiveᵍ (prefix-underᵍ prefix)
    {suc Y} {zero} ()
insertCenter-injectiveᵍ (prefix-underᵍ prefix)
    {suc Y} {suc Z} eq =
  cong suc (insertCenter-injectiveᵍ prefix
    (fin-suc-injective eq))


insert-ηᴸᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (Y : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ (insertWorldᵍ prefix))
      (insertSourceᵍ prefix Y)
    ≡ insertCenterᵍ prefix (toRenameᵗ (ηᴸᶜ W) Y)
insert-ηᴸᵍ prefix-hereᵍ Y = refl
insert-ηᴸᵍ (prefix-underᵍ prefix) zero = refl
insert-ηᴸᵍ (prefix-underᵍ prefix) (suc Y) =
  cong suc (insert-ηᴸᵍ prefix Y)


insert-ηᴿᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (Y : TyVar (Δᵉ C))
  → toRenameᵗ (ηᴿᶜ (insertWorldᵍ prefix))
      (insertStableᵍ prefix Y)
    ≡ insertCenterᵍ prefix (toRenameᵗ (ηᴿᶜ W) Y)
insert-ηᴿᵍ prefix-hereᵍ Y = refl
insert-ηᴿᵍ (prefix-underᵍ prefix) zero = refl
insert-ηᴿᵍ (prefix-underᵍ prefix) (suc Y) =
  cong suc (insert-ηᴿᵍ prefix Y)


insert-edge-embedᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (Y : TyVar (Δᵉ C))
  → edgeEmbed (insertEdgeᵍ prefix) (insertStableᵍ prefix Y)
    ≡ insertTargetᵍ prefix (edgeEmbed edge Y)
insert-edge-embedᵍ prefix-hereᵍ Y = refl
insert-edge-embedᵍ (prefix-underᵍ prefix) zero = refl
insert-edge-embedᵍ (prefix-underᵍ prefix) (suc Y) =
  cong suc (insert-edge-embedᵍ prefix Y)


insert-marksᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (Y : TyVar (centerᶜ W))
  → marksᶜ (insertWorldᵍ prefix) (insertCenterᵍ prefix Y)
    ≡ marksᶜ W Y
insert-marksᵍ prefix-hereᵍ Y = refl
insert-marksᵍ (prefix-underᵍ prefix) zero = refl
insert-marksᵍ (prefix-underᵍ prefix) (suc Y) =
  insert-marksᵍ prefix Y


data TargetVarViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocusᵍ W X alpha
  → (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Modeᵍ edge
  → TyVar (Δᵉ C⁺) → TyVar (centerᶜ W) → Set where
  stable-oldᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {Y Y⁺ Z}
    → edgeEmbed edge Y ≡ Y⁺
    → toRenameᵗ (ηᴿᶜ W) Y ≡ Z
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge stableᵍ Y⁺ Z

  focus-hereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {m Y Z}
    → toRenameᵗ (ηᴸᶜ W) X ≡ Z
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge (push-focusᵍ m Y) Y Z

  focus-thereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {m Y Y′ Z}
    → Y ≢ Y′
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m Y′ Z
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge (push-focusᵍ m Y) Y′ Z


data TargetTypeViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocusᵍ W X alpha
  → (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Modeᵍ edge
  → Ty (Δᵉ C⁺) → Ty (centerᶜ W) → Set where
  view-varᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m Y Z}
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m Y Z
    → TargetTypeViewᵍ focus edge m (＇ Y) (＇ Z)

  view-baseᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m ι}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m (‵ ι) (‵ ι)

  view-starᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m ★ ★

  view-funᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
      {A B A′ B′}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m A A′
    → TargetTypeViewᵍ focus edge m B B′
    → TargetTypeViewᵍ focus edge m (A ⇒ B) (A′ ⇒ B′)


insertTargetVarViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {Y Z}
    (prefix : LiftPrefixᵍ focus edge)
  → TargetVarViewᵍ focus edge m Y Z
  → TargetVarViewᵍ (insertFocusᵍ prefix)
      (insertEdgeᵍ prefix) (insertModeᵍ prefix m)
      (insertTargetᵍ prefix Y) (insertCenterᵍ prefix Z)
insertTargetVarViewᵍ prefix
    (stable-oldᵍ {Y = Y} edge-eq center-eq) =
  stable-oldᵍ
    (trans (insert-edge-embedᵍ prefix Y)
      (cong (insertTargetᵍ prefix) edge-eq))
    (trans (insert-ηᴿᵍ prefix Y)
      (cong (insertCenterᵍ prefix) center-eq))
insertTargetVarViewᵍ {X = X} prefix (focus-hereᵍ center-eq) =
  focus-hereᵍ
    (trans (insert-ηᴸᵍ prefix X)
      (cong (insertCenterᵍ prefix) center-eq))
insertTargetVarViewᵍ prefix (focus-thereᵍ neq view) =
  focus-thereᵍ
    (λ eq → neq (insertTarget-injectiveᵍ prefix eq))
    (insertTargetVarViewᵍ prefix view)


insertTargetTypeViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {A B}
    (prefix : LiftPrefixᵍ focus edge)
  → TargetTypeViewᵍ focus edge m A B
  → TargetTypeViewᵍ (insertFocusᵍ prefix)
      (insertEdgeᵍ prefix) (insertModeᵍ prefix m)
      (renameᵗ (insertTargetᵍ prefix) A)
      (renameᵗ (insertCenterᵍ prefix) B)
insertTargetTypeViewᵍ prefix (view-varᵍ view) =
  view-varᵍ (insertTargetVarViewᵍ prefix view)
insertTargetTypeViewᵍ prefix view-baseᵍ = view-baseᵍ
insertTargetTypeViewᵍ prefix view-starᵍ = view-starᵍ
insertTargetTypeViewᵍ prefix (view-funᵍ view-A view-B) =
  view-funᵍ (insertTargetTypeViewᵍ prefix view-A)
    (insertTargetTypeViewᵍ prefix view-B)


data ScopedTypeᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge) → Ty (Δᵉ Cᴸ) → Ty (Δᵉ C⁺) → Set
    where
  scoped-typeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
      {A B Bᶜ}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m B Bᶜ
    → I._⊢_⊑_ (marksᶜ W)
        (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) Bᶜ
    → ScopedTypeᵍ W focus edge m A B

  scoped-allᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m m⁺ A B}
    → ModeLiftᵍ {edge = edge} m m⁺
    → ScopedTypeᵍ (liftBothᶜ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge) m⁺ A B
    → ScopedTypeᵍ W focus edge m (`∀ A) (`∀ B)

  scoped-funᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m A A′ B B′}
    → ScopedTypeᵍ W focus edge m A A′
    → ScopedTypeᵍ W focus edge m B B′
    → ScopedTypeᵍ W focus edge m (A ⇒ B) (A′ ⇒ B′)


insert-imprecisionᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {A B : Ty (centerᶜ W)}
    (prefix : LiftPrefixᵍ focus edge)
  → I._⊢_⊑_ (marksᶜ W) A B
  → I._⊢_⊑_ (marksᶜ (insertWorldᵍ prefix))
      (renameᵗ (insertCenterᵍ prefix) A)
      (renameᵗ (insertCenterᵍ prefix) B)
insert-imprecisionᵍ prefix p =
  rename-⊑ (insertCenterᵍ prefix)
    (insertCenter-injectiveᵍ prefix)
    (λ Y eq → trans (insert-marksᵍ prefix Y) eq) p


insert-left-renameᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (A : Ty (Δᵉ Cᴸ))
  → renameᵗ (toRenameᵗ (ηᴸᶜ (insertWorldᵍ prefix)))
      (renameᵗ (insertSourceᵍ prefix) A)
    ≡ renameᵗ (insertCenterᵍ prefix)
        (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A)
insert-left-renameᵍ {W = W} prefix A =
  trans
    (renameᵗ-comp (insertSourceᵍ prefix)
      (toRenameᵗ (ηᴸᶜ (insertWorldᵍ prefix))) A)
    (trans
      (renameᵗ-cong A (insert-ηᴸᵍ prefix))
      (sym (renameᵗ-comp (toRenameᵗ (ηᴸᶜ W))
        (insertCenterᵍ prefix) A)))


insertSource-underᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (Y : TyVar (Nat.suc (Δᵉ Cᴸ)))
  → insertSourceᵍ (prefix-underᵍ prefix) Y
    ≡ extᵗ (insertSourceᵍ prefix) Y
insertSource-underᵍ prefix zero = refl
insertSource-underᵍ prefix (suc Y) = refl


insertTarget-underᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge) (Y : TyVar (Nat.suc (Δᵉ C⁺)))
  → insertTargetᵍ (prefix-underᵍ prefix) Y
    ≡ extᵗ (insertTargetᵍ prefix) Y
insertTarget-underᵍ prefix zero = refl
insertTarget-underᵍ prefix (suc Y) = refl


scopedType-congᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {A A′ B B′}
  → A ≡ A′
  → B ≡ B′
  → ScopedTypeᵍ W focus edge m A B
  → ScopedTypeᵍ W focus edge m A′ B′
scopedType-congᵍ refl refl p = p


insertScopedTypeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {A B}
    (prefix : LiftPrefixᵍ focus edge)
  → ScopedTypeᵍ W focus edge m A B
  → ScopedTypeᵍ (insertWorldᵍ prefix) (insertFocusᵍ prefix)
      (insertEdgeᵍ prefix) (insertModeᵍ prefix m)
      (renameᵗ (insertSourceᵍ prefix) A)
      (renameᵗ (insertTargetᵍ prefix) B)
insertScopedTypeᵍ {A = A} prefix (scoped-typeᵍ view p) =
  scoped-typeᵍ (insertTargetTypeViewᵍ prefix view)
    (imprecision-cong (sym (insert-left-renameᵍ prefix A)) refl
      (insert-imprecisionᵍ prefix p))
insertScopedTypeᵍ {A = `∀ A} {B = `∀ B} prefix
    (scoped-allᵍ mode-lift p) =
  scoped-allᵍ (insertModeLiftᵍ prefix mode-lift)
    (scopedType-congᵍ
      (renameᵗ-cong A (insertSource-underᵍ prefix))
      (renameᵗ-cong B (insertTarget-underᵍ prefix))
      (insertScopedTypeᵍ (prefix-underᵍ prefix) p))
insertScopedTypeᵍ prefix (scoped-funᵍ p q) =
  scoped-funᵍ (insertScopedTypeᵍ prefix p)
    (insertScopedTypeᵍ prefix q)


data ExactTargetBoundaryᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge) (Y : TyVar (Δᵉ C⁺))
    (R : Ty (Δᵉ C⁺))
  → ScopedTypeᵍ W focus edge m (＇ X) R → Set where
  direct-targetᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m Y R Rᶜ}
      {view : TargetTypeViewᵍ focus edge m R Rᶜ}
      {p : I._⊢_⊑_ (marksᶜ W)
        (renameᵗ (toRenameᵗ (ηᴸᶜ W)) (＇ X)) Rᶜ}
    → Σᵉ C⁺ ∋ Y ⦂ R
    → ExactTargetBoundaryᵍ W focus edge m Y R
        (scoped-typeᵍ view p)


data ValidModeᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Modeᵍ edge → Set where
  stable-validᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → ValidModeᵍ W focus edge stableᵍ

  push-validᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m Y R q}
    → ValidModeᵍ W focus edge m
    → ExactTargetBoundaryᵍ W focus edge m Y R q
    → ValidModeᵍ W focus edge (push-focusᵍ m Y)


insertStoreMemberᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {Y : TyVar (Δᵉ C⁺)} {R : Ty (Δᵉ C⁺)}
    (prefix : LiftPrefixᵍ focus edge)
  → Σᵉ C⁺ ∋ Y ⦂ R
  → Σᵉ (⇑ᵉᵗ C⁺) ∋ insertTargetᵍ prefix Y
      ⦂ renameᵗ (insertTargetᵍ prefix) R
insertStoreMemberᵍ prefix-hereᵍ member = S-lift∋ member refl
insertStoreMemberᵍ (prefix-underᵍ prefix)
    (S-lift∋ {A = A} member eq) =
  S-lift∋ (insertStoreMemberᵍ prefix member)
    (trans (renameᵗ-cong _ (insertTarget-underᵍ prefix))
      (trans (cong (renameᵗ (extᵗ (insertTargetᵍ prefix))) eq)
        (renameᵗ-shift (insertTargetᵍ prefix) A)))


insertBoundaryᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {Y R q}
    (prefix : LiftPrefixᵍ focus edge)
  → ExactTargetBoundaryᵍ W focus edge m Y R q
  → ExactTargetBoundaryᵍ (insertWorldᵍ prefix)
      (insertFocusᵍ prefix) (insertEdgeᵍ prefix)
      (insertModeᵍ prefix m) (insertTargetᵍ prefix Y)
      (renameᵗ (insertTargetᵍ prefix) R)
      (insertScopedTypeᵍ prefix q)
insertBoundaryᵍ {q = scoped-typeᵍ view p} prefix
    (direct-targetᵍ member) =
  direct-targetᵍ (insertStoreMemberᵍ prefix member)


insertValidModeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} (prefix : LiftPrefixᵍ focus edge)
  → ValidModeᵍ W focus edge m
  → ValidModeᵍ (insertWorldᵍ prefix) (insertFocusᵍ prefix)
      (insertEdgeᵍ prefix) (insertModeᵍ prefix m)
insertValidModeᵍ prefix stable-validᵍ = stable-validᵍ
insertValidModeᵍ prefix (push-validᵍ ok boundary) =
  push-validᵍ (insertValidModeᵍ prefix ok)
    (insertBoundaryᵍ prefix boundary)


data ScopedWorldᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Ctx → Ctx → Set where
  scoped-rootᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → ScopedWorldᵍ W focus edge Cᴸ C⁺

  scoped-bindᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {Gammaᴸ Gammaᴿ A B m}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    → (ok : ValidModeᵍ W focus edge m)
    → (p : ScopedTypeᵍ W focus edge m A B)
    → ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , A ∷ Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , B ∷ Gammaᴿ ⟩


data ScopedWorldInsertᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (prefix : LiftPrefixᵍ focus edge)
    {Dᴸ Dᴿ Eᴸ Eᴿ : Ctx}
  → ScopedWorldᵍ W focus edge Dᴸ Dᴿ
  → ScopedWorldᵍ (insertWorldᵍ prefix) (insertFocusᵍ prefix)
      (insertEdgeᵍ prefix) Eᴸ Eᴿ
  → Set where
  insert-rootᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {prefix : LiftPrefixᵍ focus edge}
    → ScopedWorldInsertᵍ prefix scoped-rootᵍ scoped-rootᵍ

  insert-bindᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {prefix : LiftPrefixᵍ focus edge}
      {Gammaᴸ : TC.TermCtx (Δᵉ Cᴸ)}
      {Gammaᴿ : TC.TermCtx (Δᵉ C⁺)}
      {Gammaᴸᶦ : TC.TermCtx (Nat.suc (Δᵉ Cᴸ))}
      {Gammaᴿᶦ : TC.TermCtx (Nat.suc (Δᵉ C⁺))}
      {A B m}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {Sᶦ : ScopedWorldᵍ (insertWorldᵍ prefix)
        (insertFocusᵍ prefix) (insertEdgeᵍ prefix)
        ⟨ Nat.suc (Δᵉ Cᴸ) , store-lift (Σᵉ Cᴸ) , Gammaᴸᶦ ⟩
        ⟨ Nat.suc (Δᵉ C⁺) , store-lift (Σᵉ C⁺) , Gammaᴿᶦ ⟩}
      {ok : ValidModeᵍ W focus edge m}
      {p : ScopedTypeᵍ W focus edge m A B}
    → ScopedWorldInsertᵍ prefix S Sᶦ
    → ScopedWorldInsertᵍ prefix
        (scoped-bindᵍ {S = S} ok p)
        (scoped-bindᵍ {S = Sᶦ} (insertValidModeᵍ prefix ok)
          (insertScopedTypeᵍ prefix p))


data ScopedEntryᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {Gammaᴸ Gammaᴿ}
    (S : ScopedWorldᵍ W focus edge
      ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
      ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩)
    (x : Nat.ℕ) {m : Modeᵍ edge}
    (ok : ValidModeᵍ W focus edge m)
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ C⁺)}
    (p : ScopedTypeᵍ W focus edge m A B) → Set where
  entry-hereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {Gammaᴸ Gammaᴿ A B m}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {ok : ValidModeᵍ W focus edge m}
      {p : ScopedTypeᵍ W focus edge m A B}
    → ScopedEntryᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} {focus} {edge}
        (scoped-bindᵍ {S = S} ok p) Nat.zero ok p

  entry-thereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {Gammaᴸ Gammaᴿ x A B A₀ B₀ m m₀}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {ok : ValidModeᵍ W focus edge m}
      {ok₀ : ValidModeᵍ W focus edge m₀}
      {p : ScopedTypeᵍ W focus edge m A B}
      {p₀ : ScopedTypeᵍ W focus edge m₀ A₀ B₀}
    → ScopedEntryᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} {focus} {edge} S x ok p
    → ScopedEntryᵍ
        (scoped-bindᵍ {S = S} ok₀ p₀) (Nat.suc x) ok p


insertScopedEntryᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {prefix : LiftPrefixᵍ focus edge}
    {Gammaᴸ : TC.TermCtx (Δᵉ Cᴸ)}
    {Gammaᴿ : TC.TermCtx (Δᵉ C⁺)}
    {Gammaᴸᶦ : TC.TermCtx (Nat.suc (Δᵉ Cᴸ))}
    {Gammaᴿᶦ : TC.TermCtx (Nat.suc (Δᵉ C⁺))}
    {S : ScopedWorldᵍ W focus edge
      ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
      ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    {Sᶦ : ScopedWorldᵍ (insertWorldᵍ prefix)
      (insertFocusᵍ prefix) (insertEdgeᵍ prefix)
      ⟨ Nat.suc (Δᵉ Cᴸ) , store-lift (Σᵉ Cᴸ) , Gammaᴸᶦ ⟩
      ⟨ Nat.suc (Δᵉ C⁺) , store-lift (Σᵉ C⁺) , Gammaᴿᶦ ⟩}
    {x m A B}
    {ok : ValidModeᵍ W focus edge m}
    {p : ScopedTypeᵍ W focus edge m A B}
  → ScopedWorldInsertᵍ prefix S Sᶦ
  → ScopedEntryᵍ S x ok p
  → ScopedEntryᵍ Sᶦ x (insertValidModeᵍ prefix ok)
      (insertScopedTypeᵍ prefix p)
insertScopedEntryᵍ (insert-bindᵍ world-insert) entry-hereᵍ =
  entry-hereᵍ
insertScopedEntryᵍ (insert-bindᵍ world-insert)
    (entry-thereᵍ entry) =
  entry-thereᵍ (insertScopedEntryᵍ world-insert entry)


SourcePivotUnoccupiedᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge) (Z : TyVar (Δᵉ Cᴸ)) → Set
SourcePivotUnoccupiedᵍ {W = W} focus edge m Z = ∀ {Y Zᶜ}
  → TargetVarViewᵍ focus edge m Y Zᶜ
  → toRenameᵗ (ηᴸᶜ W) Z ≢ Zᶜ


data ScopedCTIᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge) (ok : ValidModeᵍ W focus edge m)
    {Gammaᴸ Gammaᴿ}
    (S : ScopedWorldᵍ W focus edge
      ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
      ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩)
  → Term (Δᵉ Cᴸ) → Term (Δᵉ C⁺)
  → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ C⁺)}
  → ScopedTypeᵍ W focus edge m A B → Set where
  var⊑varᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ S x A B p}
    → ScopedEntryᵍ {Gammaᴸ = Gammaᴸ} {Gammaᴿ = Gammaᴿ}
        S x ok p
    → ScopedCTIᵍ W focus edge m ok S (` x) (` x) {A} {B} p

  lambda⊑lambdaᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ A A′ B B′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {pA : ScopedTypeᵍ W focus edge m A A′}
      {pB : ScopedTypeᵍ W focus edge m B B′}
    → ScopedCTIᵍ W focus edge m ok
        (scoped-bindᵍ {S = S} ok pA) M M′ pB
    → ScopedCTIᵍ W focus edge m ok S (ƛ M) (ƛ M′)
        (scoped-funᵍ pA pB)

  app⊑appᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ L L′ M M′ A A′ B B′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {pA : ScopedTypeᵍ W focus edge m A A′}
      {pB : ScopedTypeᵍ W focus edge m B B′}
    → ScopedCTIᵍ W focus edge m ok S L L′ (scoped-funᵍ pA pB)
    → ScopedCTIᵍ W focus edge m ok S M M′ pA
    → ScopedCTIᵍ W focus edge m ok S (L · M) (L′ · M′) pB

  constant⊑constantᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    → (kappa : Const)
    → (p : ScopedTypeᵍ W focus edge m
        (constTy kappa) (constTy kappa))
    → ScopedCTIᵍ W focus edge m ok S ($ kappa) ($ kappa) p

  primitive⊑primitiveᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ L L′ M M′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {op : Prim}
      {p q : ScopedTypeᵍ W focus edge m
        (primArgTy op) (primArgTy op)}
    → ScopedCTIᵍ W focus edge m ok S L L′ p
    → ScopedCTIᵍ W focus edge m ok S M M′ q
    → (r : ScopedTypeᵍ W focus edge m
        (primResultTy op) (primResultTy op))
    → ScopedCTIᵍ W focus edge m ok S
        (L ⊕[ op ] M) (L′ ⊕[ op ] M′) r

  blame⊑ᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M′ A B}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    → ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩ ⊢ M′ ⦂ B
    → (p : ScopedTypeᵍ W focus edge m A B)
    → ScopedCTIᵍ W focus edge m ok S blame M′ p

  cast⊑castᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ A A′ B B′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {p : ScopedTypeᵍ W focus edge m A A′}
      {q : ScopedTypeᵍ W focus edge m B B′}
      {ν : Env∼ (Δᵉ Cᴸ)} {ν′ : Env∼ (Δᵉ C⁺)}
    → (c : ν ⊢ A ∼ B)
    → (c′ : ν′ ⊢ A′ ∼ B′)
    → ScopedCTIᵍ W focus edge m ok S M M′ p
    → ScopedCTIᵍ W focus edge m ok S (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) q

  cast⊑ᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ A A′ B}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {p : ScopedTypeᵍ W focus edge m A B}
      {q : ScopedTypeᵍ W focus edge m A′ B}
      {ν : Env∼ (Δᵉ Cᴸ)}
    → (c : ν ⊢ A ∼ A′)
    → ScopedCTIᵍ W focus edge m ok S M M′ p
    → ScopedCTIᵍ W focus edge m ok S (M ⟨ c ⟩) M′ q

  ⊑castᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ A B B′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {p : ScopedTypeᵍ W focus edge m A B}
      {q : ScopedTypeᵍ W focus edge m A B′}
      {ν′ : Env∼ (Δᵉ C⁺)}
    → (c′ : ν′ ⊢ B ∼ B′)
    → ScopedCTIᵍ W focus edge m ok S M M′ p
    → ScopedCTIᵍ W focus edge m ok S M (M′ ⟨ c′ ⟩) q

  all⊑allᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m : Modeᵍ edge} {ok : ValidModeᵍ W focus edge m}
      {Gammaᴸ Gammaᴿ}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {S⁺ : ScopedWorldᵍ (liftBothᶜ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge)
        ⟨ Nat.suc (Δᵉ Cᴸ) , store-lift (Σᵉ Cᴸ) ,
          TC.⇑ᶜ Gammaᴸ ⟩
        ⟨ Nat.suc (Δᵉ C⁺) , store-lift (Σᵉ C⁺) ,
          TC.⇑ᶜ Gammaᴿ ⟩}
      {V : Term (Nat.suc (Δᵉ Cᴸ))}
      {V′ : Term (Nat.suc (Δᵉ C⁺))}
      {A : Ty (Nat.suc (Δᵉ Cᴸ))}
      {B : Ty (Nat.suc (Δᵉ C⁺))}
      {p : ScopedTypeᵍ (liftBothᶜ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge)
        (insertModeᵍ prefix-hereᵍ m) A B}
    → ScopedWorldInsertᵍ prefix-hereᵍ S S⁺
    → Value V
    → Value V′
    → ScopedCTIᵍ (liftBothᶜ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge)
        (insertModeᵍ prefix-hereᵍ m)
        (insertValidModeᵍ prefix-hereᵍ ok) S⁺ V V′ p
    → ScopedCTIᵍ W focus edge m ok S (Λ V) (Λ V′)
        (scoped-allᵍ (prefix-here-mode-liftᵍ focus edge m) p)

  target-revealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m : Modeᵍ edge} {ok : ValidModeᵍ W focus edge m}
      {Gammaᴸ Gammaᴿ M M′ Y R A B B′ edgeq p q}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {c : Conv↑ (Δᵉ C⁺) B B′}
    → (boundary : ExactTargetBoundaryᵍ W focus edge m Y R edgeq)
    → Σᵉ C⁺ ⊢↑[ just Y ] c
    → ScopedCTIᵍ W focus edge (push-focusᵍ m Y)
        (push-validᵍ ok boundary) S M M′ {A = A} {B = B} p
    → ScopedCTIᵍ W focus edge m ok S M (M′ ↑ c)
        {A = A} {B = B′} q

  target-concealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m : Modeᵍ edge} {ok : ValidModeᵍ W focus edge m}
      {Gammaᴸ Gammaᴿ M M′ Y R A B B′ edgeq p q}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {c : Conv↓ (Δᵉ C⁺) B B′}
    → (boundary : ExactTargetBoundaryᵍ W focus edge m Y R edgeq)
    → Σᵉ C⁺ ⊢↓[ just Y ] c
    → ScopedCTIᵍ W focus edge m ok S M M′
        {A = A} {B = B} q
    → ScopedCTIᵍ W focus edge (push-focusᵍ m Y)
        (push-validᵍ ok boundary) S M (M′ ↓ c)
        {A = A} {B = B′} p

  source-concealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ Z R B}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {p : ScopedTypeᵍ W focus edge m (＇ Z) B}
      {q : ScopedTypeᵍ W focus edge m R B}
    → SourcePivotUnoccupiedᵍ focus edge m Z
    → Σᵉ Cᴸ ∋ Z ⦂ R
    → ScopedCTIᵍ W focus edge m ok S M M′ q
    → ScopedCTIᵍ W focus edge m ok S
        (M ↓ seal Z R) M′ p

  paired-revealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ Z Y R R′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {p : ScopedTypeᵍ W focus edge m (＇ Z) (＇ Y)}
      {q : ScopedTypeᵍ W focus edge m R R′}
    → Σᵉ Cᴸ ∋ Z ⦂ R
    → Σᵉ C⁺ ∋ Y ⦂ R′
    → ScopedCTIᵍ W focus edge m ok S M M′ p
    → ScopedCTIᵍ W focus edge m ok S
        (M ↑ unseal Z R) (M′ ↑ unseal Y R′) q

  paired-concealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ M M′ Z Y R R′}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {p : ScopedTypeᵍ W focus edge m (＇ Z) (＇ Y)}
      {q : ScopedTypeᵍ W focus edge m R R′}
    → Σᵉ Cᴸ ∋ Z ⦂ R
    → Σᵉ C⁺ ∋ Y ⦂ R′
    → ScopedCTIᵍ W focus edge m ok S M M′ q
    → ScopedCTIᵍ W focus edge m ok S
        (M ↓ seal Z R) (M′ ↓ seal Y R′) p

  type-app⊑type-appᵍ : ∀ {Cᴸ C C⁺ : Ctx}
      {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m : Modeᵍ edge} {ok : ValidModeᵍ W focus edge m}
      {Gammaᴸ Gammaᴿ}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ C⁺)}
      {D : Ty (Nat.suc (Δᵉ Cᴸ))}
      {D′ : Ty (Nat.suc (Δᵉ C⁺))}
      {A : Ty (Δᵉ Cᴸ)} {A′ : Ty (Δᵉ C⁺)}
      {p : ScopedTypeᵍ W focus edge m (`∀ D) (`∀ D′)}
    → ScopedCTIᵍ W focus edge m ok S M M′ p
    → (q : ScopedTypeᵍ W focus edge m A A′)
    → (r : ScopedTypeᵍ W focus edge m
        (D [ A ]ᵗ) (D′ [ A′ ]ᵗ))
    → ScopedCTIᵍ W focus edge m ok S
        (M ⦂∀ D [ A ]) (M′ ⦂∀ D′ [ A′ ]) r

  type-app⊑ᵍ : ∀ {Cᴸ C C⁺ : Ctx}
      {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m : Modeᵍ edge} {ok : ValidModeᵍ W focus edge m}
      {Gammaᴸ Gammaᴿ}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ C⁺)}
      {D : Ty (Nat.suc (Δᵉ Cᴸ))}
      {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ C⁺)}
      {p : ScopedTypeᵍ W focus edge m (`∀ D) B}
    → ScopedCTIᵍ W focus edge m ok S M M′ p
    → (q : ScopedTypeᵍ W focus edge m A ★)
    → (r : ScopedTypeᵍ W focus edge m (D [ A ]ᵗ) B)
    → ScopedCTIᵍ W focus edge m ok S (M ⦂∀ D [ A ]) M′ r


concrete-focusᵍ : NameFocusᵍ stable-world source-X target-alpha
concrete-focusᵍ =
  name-focusᵍ stable-X-alpha-separated stable-X-self
    stable-direct-representations-proof


concrete-edgeᵍ : ExactAliasEdgeᵉ
  target-alpha-context target-alpha-beta-context
  target-alpha target-beta target-alpha⁺
concrete-edgeᵍ = edge-head refl


concrete-rootᵍ : ScopedWorldᵍ stable-world concrete-focusᵍ
  concrete-edgeᵍ source-X-context target-alpha-beta-context
concrete-rootᵍ = scoped-rootᵍ


concrete-inner-rootᵍ : ScopedWorldᵍ
  (liftBothᶜ I.X⊑X stable-world)
  (liftNameFocusᵍ concrete-focusᵍ) (edge-lift concrete-edgeᵍ)
  (⇑ᵉᵗ source-X-context) (⇑ᵉᵗ target-alpha-beta-context)
concrete-inner-rootᵍ = scoped-rootᵍ


concrete-root-insertᵍ : ScopedWorldInsertᵍ prefix-hereᵍ
  concrete-rootᵍ concrete-inner-rootᵍ
concrete-root-insertᵍ = insert-rootᵍ


concrete-inner-atomᵍ : ScopedTypeᵍ
  (liftBothᶜ I.X⊑X stable-world)
  (liftNameFocusᵍ concrete-focusᵍ) (edge-lift concrete-edgeᵍ)
  stableᵍ (＇ zero) (＇ zero)
concrete-inner-atomᵍ =
  scoped-typeᵍ (view-varᵍ (stable-oldᵍ refl refl)) I.X⊑X


concrete-inner-bodyᵍ : ScopedWorldᵍ
  (liftBothᶜ I.X⊑X stable-world)
  (liftNameFocusᵍ concrete-focusᵍ) (edge-lift concrete-edgeᵍ)
  ⟨ Nat.suc (Δᵉ source-X-context) ,
    store-lift (Σᵉ source-X-context) , ＇ zero ∷ [] ⟩
  ⟨ Nat.suc (Δᵉ target-alpha-beta-context) ,
    store-lift (Σᵉ target-alpha-beta-context) , ＇ zero ∷ [] ⟩
concrete-inner-bodyᵍ =
  scoped-bindᵍ {S = concrete-inner-rootᵍ}
    stable-validᵍ concrete-inner-atomᵍ


concrete-inner-entryᵍ : ScopedEntryᵍ concrete-inner-bodyᵍ
  Nat.zero stable-validᵍ concrete-inner-atomᵍ
concrete-inner-entryᵍ = entry-hereᵍ


concrete-inner-varᵍ : ScopedCTIᵍ
  (liftBothᶜ I.X⊑X stable-world)
  (liftNameFocusᵍ concrete-focusᵍ) (edge-lift concrete-edgeᵍ)
  stableᵍ stable-validᵍ concrete-inner-bodyᵍ
  (` Nat.zero) (` Nat.zero) concrete-inner-atomᵍ
concrete-inner-varᵍ = var⊑varᵍ concrete-inner-entryᵍ


concrete-inner-funᵍ : ScopedTypeᵍ
  (liftBothᶜ I.X⊑X stable-world)
  (liftNameFocusᵍ concrete-focusᵍ) (edge-lift concrete-edgeᵍ)
  stableᵍ (＇ zero ⇒ ＇ zero) (＇ zero ⇒ ＇ zero)
concrete-inner-funᵍ =
  scoped-funᵍ concrete-inner-atomᵍ concrete-inner-atomᵍ


concrete-inner-lambdaᵍ : ScopedCTIᵍ
  (liftBothᶜ I.X⊑X stable-world)
  (liftNameFocusᵍ concrete-focusᵍ) (edge-lift concrete-edgeᵍ)
  stableᵍ stable-validᵍ concrete-inner-rootᵍ
  (ƛ (` Nat.zero)) (ƛ (` Nat.zero)) concrete-inner-funᵍ
concrete-inner-lambdaᵍ =
  lambda⊑lambdaᵍ {S = concrete-inner-rootᵍ} concrete-inner-varᵍ


concrete-allᵍ : ScopedCTIᵍ stable-world concrete-focusᵍ
  concrete-edgeᵍ stableᵍ stable-validᵍ concrete-rootᵍ
  (Λ (ƛ (` Nat.zero))) (Λ (ƛ (` Nat.zero)))
  (scoped-allᵍ
    (prefix-here-mode-liftᵍ concrete-focusᵍ concrete-edgeᵍ stableᵍ)
    concrete-inner-funᵍ)
concrete-allᵍ =
  all⊑allᵍ concrete-root-insertᵍ (ƛ (` Nat.zero))
    (ƛ (` Nat.zero)) concrete-inner-lambdaᵍ


concrete-starᵍ : ScopedTypeᵍ stable-world concrete-focusᵍ
  concrete-edgeᵍ stableᵍ ★ ★
concrete-starᵍ = scoped-typeᵍ view-starᵍ I.★⊑★


concrete-star-funᵍ : ScopedTypeᵍ stable-world concrete-focusᵍ
  concrete-edgeᵍ stableᵍ (★ ⇒ ★) (★ ⇒ ★)
concrete-star-funᵍ =
  scoped-funᵍ concrete-starᵍ concrete-starᵍ


concrete-type-appᵍ : ScopedCTIᵍ stable-world concrete-focusᵍ
  concrete-edgeᵍ stableᵍ stable-validᵍ concrete-rootᵍ
  ((Λ (ƛ (` Nat.zero))) ⦂∀ (＇ zero ⇒ ＇ zero) [ ★ ])
  ((Λ (ƛ (` Nat.zero))) ⦂∀ (＇ zero ⇒ ＇ zero) [ ★ ])
  concrete-star-funᵍ
concrete-type-appᵍ =
  type-app⊑type-appᵍ concrete-allᵍ concrete-starᵍ
    concrete-star-funᵍ

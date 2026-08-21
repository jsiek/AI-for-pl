{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxGlobalIndexedCTIProbe where

-- File Charter:
--   * Globalizes the two-Ctx edge-scoped CTI state so universal recursion may
--     change every endpoint, world, focus, edge, mode, and term-context index.
--   * Gives structural one-prefix lifts for focus modes, valid boundaries,
--     scoped types, heterogeneous term worlds, and term entries.
--   * Checks genuine Lambda and type-application constructors without a
--     compatibility wrapper around the earlier fixed-parameter probe.

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; sym; trans)

open import Types using
  (Ty; TyCtx; TyVar; ★; ＇_; ‵_; _⇒_; `∀; ⇑ᵗ; renameᵗ;
   _[_]ᵗ; renameᵗ-cong; renameᵗ-comp; renameᵗ-shift)
open import TyStore using
  (TyStore; lookupStore; store-lift; _∋_⦂_; Z∋; S-lift∋; S-bind∋)
import TermCtx as TC
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ)
import Imprecision as I
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _⊢↑[_]_; _⊢↓[_]_; ⊢↑-unsealˣ;
   ⊢↓-sealˣ; ⊢↑-⇒ˣ; join-both)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; Value; `_; ƛ_; Λ_;
   _⦂∀_[_]; _↑_; _↓_; ⇑ᵉᵗ)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe using
  (source-X-context; target-alpha-context; target-alpha-beta-context;
   source-X; target-alpha; target-beta; target-alpha⁺)
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


data NameFocusᵍ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ₀ Cᴿ) :
    TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ Cᴿ) → Set where
  name-focusᵍ : ∀ {X alpha}
    → toRenameᵗ (ηᴸᶜ₀ W) X ≢ toRenameᵗ (ηᴿᶜ₀ W) alpha
    → lookupStore (Σᵉ Cᴸ) X ≡ ＇ X
    → lookupStore (Σᵉ Cᴸ) X ⊑ᵀ₀⟨ W ⟩
        lookupStore (Σᵉ Cᴿ) alpha
    → NameFocusᵍ W X alpha


liftNameFocusᵍ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {X alpha}
  → NameFocusᵍ W X alpha
  → NameFocusᵍ (liftBothᶜ₀ I.X⊑X W) (suc X) (suc alpha)
liftNameFocusᵍ {Cᴸ} {Cᴿ} {W} {X} {alpha}
    (name-focusᵍ separated self reps) =
  name-focusᵍ lifted-separated (cong ⇑ᵗ self) lifted-reps
  where
  lifted-separated :
    toRenameᵗ (ηᴸᶜ₀ (liftBothᶜ₀ I.X⊑X W)) (suc X)
      ≢ toRenameᵗ (ηᴿᶜ₀ (liftBothᶜ₀ I.X⊑X W))
          (suc alpha)
  lifted-separated eq = separated (fin-suc-injective eq)

  lifted-reps :
    lookupStore (Σᵉ (⇑ᵉᵗ Cᴸ)) (suc X)
      ⊑ᵀ₀⟨ liftBothᶜ₀ I.X⊑X W ⟩
    lookupStore (Σᵉ (⇑ᵉᵗ Cᴿ)) (suc alpha)
  lifted-reps =
    imprecision-cong
      (sym (rename-keep-shift (ηᴸᶜ₀ W)
        (lookupStore (Σᵉ Cᴸ) X)))
      (sym (rename-keep-shift (ηᴿᶜ₀ W)
        (lookupStore (Σᵉ Cᴿ) alpha)))
      (lift-imprecision reps)


data Modeᵍ {C C⁺ : Ctx} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺) : Set where
  stableᵍ : Modeᵍ edge
  push-focusᵍ : Modeᵍ edge → TyVar (Δᵉ C⁺) → Modeᵍ edge


liftModeᵍ : ∀ {C C⁺ alpha beta alpha⁺}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
  → Modeᵍ edge
  → Modeᵍ (edge-lift edge)
liftModeᵍ stableᵍ = stableᵍ
liftModeᵍ (push-focusᵍ m Y) =
  push-focusᵍ (liftModeᵍ m) (suc Y)


data ModeLiftᵍ {C C⁺ alpha beta alpha⁺}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺} :
    Modeᵍ edge → Modeᵍ (edge-lift edge) → Set where
  lift-stableᵍ : ModeLiftᵍ stableᵍ stableᵍ
  lift-pushᵍ : ∀ {m m⁺ Y}
    → ModeLiftᵍ m m⁺
    → ModeLiftᵍ (push-focusᵍ m Y)
        (push-focusᵍ m⁺ (suc Y))


modeLiftᵍ : ∀ {C C⁺ alpha beta alpha⁺}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    (m : Modeᵍ edge)
  → ModeLiftᵍ m (liftModeᵍ m)
modeLiftᵍ stableᵍ = lift-stableᵍ
modeLiftᵍ (push-focusᵍ m Y) = lift-pushᵍ (modeLiftᵍ m)


data TargetVarViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocusᵍ W X alpha
  → (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Modeᵍ edge
  → TyVar (Δᵉ C⁺) → TyVar (centerᶜ₀ W) → Set where
  stable-oldᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {Y Y⁺ Z}
    → edgeEmbed edge Y ≡ Y⁺
    → toRenameᵗ (ηᴿᶜ₀ W) Y ≡ Z
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge stableᵍ Y⁺ Z

  focus-hereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {m Y Z}
    → toRenameᵗ (ηᴸᶜ₀ W) X ≡ Z
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge (push-focusᵍ m Y) Y Z

  focus-thereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {m Y Y′ Z}
    → Y ≢ Y′
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m Y′ Z
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge (push-focusᵍ m Y) Y′ Z


liftTargetVarViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {Y Z}
  → TargetVarViewᵍ focus edge m Y Z
  → TargetVarViewᵍ (liftNameFocusᵍ focus) (edge-lift edge)
      (liftModeᵍ m) (suc Y) (suc Z)
liftTargetVarViewᵍ (stable-oldᵍ {Y = Y} edge-eq center-eq) =
  stable-oldᵍ {Y = suc Y}
    (cong suc edge-eq) (cong suc center-eq)
liftTargetVarViewᵍ (focus-hereᵍ center-eq) =
  focus-hereᵍ (cong suc center-eq)
liftTargetVarViewᵍ (focus-thereᵍ neq view) =
  focus-thereᵍ (lifted-neq neq) (liftTargetVarViewᵍ view)
  where
  lifted-neq : ∀ {n} {Y Y′ : Fin n} → Y ≢ Y′ → suc Y ≢ suc Y′
  lifted-neq neq refl = neq refl


data TargetTypeViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocusᵍ W X alpha
  → (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Modeᵍ edge
  → Ty (Δᵉ C⁺) → Ty (centerᶜ₀ W) → Set where
  view-varᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m Y Z}
    → TargetVarViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m Y Z
    → TargetTypeViewᵍ focus edge m (＇ Y) (＇ Z)

  view-baseᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m ι}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m (‵ ι) (‵ ι)

  view-starᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m ★ ★

  view-funᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
      {A B A′ B′}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m A A′
    → TargetTypeViewᵍ focus edge m B B′
    → TargetTypeViewᵍ focus edge m (A ⇒ B) (A′ ⇒ B′)


liftTargetTypeViewᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {A B}
  → TargetTypeViewᵍ focus edge m A B
  → TargetTypeViewᵍ (liftNameFocusᵍ focus) (edge-lift edge)
      (liftModeᵍ m) (⇑ᵗ A) (⇑ᵗ B)
liftTargetTypeViewᵍ (view-varᵍ view) =
  view-varᵍ (liftTargetVarViewᵍ view)
liftTargetTypeViewᵍ view-baseᵍ = view-baseᵍ
liftTargetTypeViewᵍ view-starᵍ = view-starᵍ
liftTargetTypeViewᵍ (view-funᵍ view-A view-B) =
  view-funᵍ (liftTargetTypeViewᵍ view-A)
    (liftTargetTypeViewᵍ view-B)


data ScopedTypeᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge) → Ty (Δᵉ Cᴸ) → Ty (Δᵉ C⁺) → Set
    where
  scoped-typeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
      {A B Bᶜ}
    → TargetTypeViewᵍ {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m B Bᶜ
    → I._⊢_⊑_ (marksᶜ₀ W)
        (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A) Bᶜ
    → ScopedTypeᵍ W focus edge m A B

  scoped-allᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m m⁺ A B}
    → ModeLiftᵍ {edge = edge} m m⁺
    → ScopedTypeᵍ (liftBothᶜ₀ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge) m⁺ A B
    → ScopedTypeᵍ W focus edge m (`∀ A) (`∀ B)


liftScopedAtomicᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge} {A B Bᶜ}
  → TargetTypeViewᵍ focus edge m B Bᶜ
  → I._⊢_⊑_ (marksᶜ₀ W)
      (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A) Bᶜ
  → ScopedTypeᵍ (liftBothᶜ₀ I.X⊑X W)
      (liftNameFocusᵍ focus) (edge-lift edge) (liftModeᵍ m)
      (⇑ᵗ A) (⇑ᵗ B)
liftScopedAtomicᵍ {W = W} {A = A} view p =
  scoped-typeᵍ (liftTargetTypeViewᵍ view)
    (imprecision-cong
      (sym (rename-keep-shift (ηᴸᶜ₀ W) A)) refl
      (lift-imprecision p))


data ExactTargetBoundaryᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
    (m : Modeᵍ edge) (Y : TyVar (Δᵉ C⁺))
    (R : Ty (Δᵉ C⁺))
  → ScopedTypeᵍ W focus edge m (＇ X) R → Set where
  direct-targetᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m Y R Rᶜ}
      {view : TargetTypeViewᵍ focus edge m R Rᶜ}
      {p : I._⊢_⊑_ (marksᶜ₀ W)
        (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) (＇ X)) Rᶜ}
    → Σᵉ C⁺ ∋ Y ⦂ R
    → ExactTargetBoundaryᵍ W focus edge m Y R
        (scoped-typeᵍ view p)


data ValidModeᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Modeᵍ edge → Set where
  stable-validᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → ValidModeᵍ W focus edge stableᵍ

  push-validᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m Y R q}
    → ValidModeᵍ W focus edge m
    → ExactTargetBoundaryᵍ W focus edge m Y R q
    → ValidModeᵍ W focus edge (push-focusᵍ m Y)


liftBoundaryᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m Y R Rᶜ}
    {view : TargetTypeViewᵍ focus edge m R Rᶜ}
    {p : I._⊢_⊑_ (marksᶜ₀ W)
      (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) (＇ X)) Rᶜ}
  → ExactTargetBoundaryᵍ W focus edge m Y R
      (scoped-typeᵍ view p)
  → ExactTargetBoundaryᵍ (liftBothᶜ₀ I.X⊑X W)
      (liftNameFocusᵍ focus) (edge-lift edge) (liftModeᵍ m)
      (suc Y) (⇑ᵗ R) (liftScopedAtomicᵍ view p)
liftBoundaryᵍ (direct-targetᵍ member) =
  direct-targetᵍ (S-lift∋ member refl)


liftValidModeᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Modeᵍ edge}
  → ValidModeᵍ W focus edge m
  → ValidModeᵍ (liftBothᶜ₀ I.X⊑X W)
      (liftNameFocusᵍ focus) (edge-lift edge) (liftModeᵍ m)
liftValidModeᵍ stable-validᵍ = stable-validᵍ
liftValidModeᵍ {W = W}
    (push-validᵍ ok
      (direct-targetᵍ {view = view} {p = p} member)) =
  push-validᵍ (liftValidModeᵍ ok)
    (direct-targetᵍ
      {view = liftTargetTypeViewᵍ view}
      {p = imprecision-cong
        (sym (rename-keep-shift (ηᴸᶜ₀ W) (＇ _))) refl
        (lift-imprecision p)}
      (S-lift∋ member refl))


data ScopedWorldᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocusᵍ W X alpha)
    (edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺)
  → Ctx → Ctx → Set where
  scoped-rootᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → ScopedWorldᵍ W focus edge Cᴸ C⁺

  scoped-bindᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
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


data ScopedWorldLiftᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {Dᴸ Dᴿ : Ctx}
  → ScopedWorldᵍ W focus edge Dᴸ Dᴿ
  → ScopedWorldᵍ (liftBothᶜ₀ I.X⊑X W)
      (liftNameFocusᵍ focus) (edge-lift edge)
      (⇑ᵉᵗ Dᴸ) (⇑ᵉᵗ Dᴿ)
  → Set where
  lift-rootᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    → ScopedWorldLiftᵍ {focus = focus} {edge = edge}
        scoped-rootᵍ scoped-rootᵍ

  lift-bind-atomicᵍ : ∀ {Cᴸ C C⁺ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {Gammaᴸ Gammaᴿ A B Bᶜ m}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {S⁺ : ScopedWorldᵍ (liftBothᶜ₀ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge)
        ⟨ Nat.suc (Δᵉ Cᴸ) , store-lift (Σᵉ Cᴸ) ,
          TC.⇑ᶜ Gammaᴸ ⟩
        ⟨ Nat.suc (Δᵉ C⁺) , store-lift (Σᵉ C⁺) ,
          TC.⇑ᶜ Gammaᴿ ⟩}
      {ok : ValidModeᵍ W focus edge m}
      {view : TargetTypeViewᵍ focus edge m B Bᶜ}
      {p : I._⊢_⊑_ (marksᶜ₀ W)
        (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A) Bᶜ}
    → ScopedWorldLiftᵍ S S⁺
    → ScopedWorldLiftᵍ
        (scoped-bindᵍ {S = S} ok (scoped-typeᵍ view p))
        (scoped-bindᵍ {S = S⁺} (liftValidModeᵍ ok)
          (liftScopedAtomicᵍ view p))


data ScopedEntryᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ C}
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
  entry-hereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
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

  entry-thereᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
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


liftScopedEntryAtomicᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ₀ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {Gammaᴸ Gammaᴿ x A B Bᶜ m}
    {S : ScopedWorldᵍ W focus edge
      ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
      ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    {S⁺ : ScopedWorldᵍ (liftBothᶜ₀ I.X⊑X W)
      (liftNameFocusᵍ focus) (edge-lift edge)
      ⟨ Nat.suc (Δᵉ Cᴸ) , store-lift (Σᵉ Cᴸ) ,
        TC.⇑ᶜ Gammaᴸ ⟩
      ⟨ Nat.suc (Δᵉ C⁺) , store-lift (Σᵉ C⁺) ,
        TC.⇑ᶜ Gammaᴿ ⟩}
    {ok : ValidModeᵍ W focus edge m}
    {view : TargetTypeViewᵍ focus edge m B Bᶜ}
    {p : I._⊢_⊑_ (marksᶜ₀ W)
      (renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A) Bᶜ}
  → ScopedWorldLiftᵍ S S⁺
  → ScopedEntryᵍ S x ok (scoped-typeᵍ view p)
  → ScopedEntryᵍ S⁺ x (liftValidModeᵍ ok)
      (liftScopedAtomicᵍ view p)
liftScopedEntryAtomicᵍ (lift-bind-atomicᵍ scope-lift) entry-hereᵍ =
  entry-hereᵍ
liftScopedEntryAtomicᵍ (lift-bind-atomicᵍ scope-lift)
    (entry-thereᵍ entry) =
  entry-thereᵍ (liftScopedEntryAtomicᵍ scope-lift entry)


data ScopedCTIᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ C)
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
  var⊑varᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m ok Gammaᴸ Gammaᴿ S x A B p}
    → ScopedEntryᵍ {Gammaᴸ = Gammaᴸ} {Gammaᴿ = Gammaᴿ}
        S x ok p
    → ScopedCTIᵍ W focus edge m ok S (` x) (` x) {A} {B} p

  lambda⊑lambdaᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
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
      {pFun : ScopedTypeᵍ W focus edge m (A ⇒ B) (A′ ⇒ B′)}
    → ScopedCTIᵍ W focus edge m ok
        (scoped-bindᵍ {S = S} ok pA) M M′ pB
    → ScopedCTIᵍ W focus edge m ok S (ƛ M) (ƛ M′) pFun

  all⊑allᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {focus : NameFocusᵍ W X alpha}
      {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
      {m : Modeᵍ edge} {ok : ValidModeᵍ W focus edge m}
      {Gammaᴸ Gammaᴿ}
      {S : ScopedWorldᵍ W focus edge
        ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
        ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
      {S⁺ : ScopedWorldᵍ (liftBothᶜ₀ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge)
        ⟨ Nat.suc (Δᵉ Cᴸ) , store-lift (Σᵉ Cᴸ) ,
          TC.⇑ᶜ Gammaᴸ ⟩
        ⟨ Nat.suc (Δᵉ C⁺) , store-lift (Σᵉ C⁺) ,
          TC.⇑ᶜ Gammaᴿ ⟩}
      {V : Term (Nat.suc (Δᵉ Cᴸ))}
      {V′ : Term (Nat.suc (Δᵉ C⁺))}
      {A : Ty (Nat.suc (Δᵉ Cᴸ))}
      {B : Ty (Nat.suc (Δᵉ C⁺))}
      {p : ScopedTypeᵍ (liftBothᶜ₀ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge) (liftModeᵍ m) A B}
    → ScopedWorldLiftᵍ S S⁺
    → Value V
    → Value V′
    → ScopedCTIᵍ (liftBothᶜ₀ I.X⊑X W)
        (liftNameFocusᵍ focus) (edge-lift edge) (liftModeᵍ m)
        (liftValidModeᵍ ok) S⁺ V V′ p
    → ScopedCTIᵍ W focus edge m ok S (Λ V) (Λ V′)
        (scoped-allᵍ (modeLiftᵍ m) p)

  target-revealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
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

  target-concealᵍ : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ₀ C}
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

  type-app⊑type-appᵍ : ∀ {Cᴸ C C⁺ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ C}
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

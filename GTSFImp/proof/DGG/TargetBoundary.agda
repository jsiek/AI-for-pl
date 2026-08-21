{-# OPTIONS --safe #-}

module proof.DGG.TargetBoundary where

-- File Charter:
--   * Defines the boundary-local target view used while one exact
--     administrative alias edge is pending.
--   * Keeps the stable two-Ctx world unchanged and exposes pending target
--     names only through an explicitly indexed focus-mode stack.
--   * Defines structural target-variable and target-type views, including
--     universal types, plus exact direct-store boundary evidence and mode
--     validity without a packaged type-imprecision relation.
--   * Indexes each exact target boundary by its target name, direct store
--     representation, and center view so conversion typing can share those
--     values directly without a projection wrapper.
--   * Proves stable fresh-name exclusion and functionality of both target
--     views.  Term imprecision, term contexts, and concrete fixtures live
--     elsewhere.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Types using
  (Ty; TyVar; ★; ＇_; ‵_; _⇒_; `∀; ⇑ᵗ; renameᵗ;
   renameᵗ-cong; renameᵗ-shift)
open import TyStore using (lookupStore; _∋_⦂_)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import CastTerms using (Ctx; Δᵉ; Σᵉ)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.DGG.World
open import proof.DGG.TargetAliasEdge


private
  fin-suc-injective : ∀ {n} {X Y : TyVar n}
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
      (eta : Consistency._↪ᵗ_ Delta₀ Delta) (A : Ty Delta₀)
    → renameᵗ (toRenameᵗ (Consistency.keep eta)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ eta) A)
  rename-keep-shift eta A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq eta))
      (renameᵗ-shift (toRenameᵗ eta) A)

  lift-imprecision : ∀ {Delta} {mu : I.ImpEnv Delta} {v A B}
    → I._⊢_⊑_ mu A B
    → I._⊢_⊑_ (I.extendᵐ v mu) (⇑ᵗ A) (⇑ᵗ B)
  lift-imprecision p =
    rename-⊑ suc fin-suc-injective (λ X eq → eq) p


data NameFocus {Cᴸ C : Ctx} (W : Cᴸ ⊑ᶜ C) :
    TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ C) → Set where

  name-focus : ∀ {X alpha}
    → toRenameᵗ (ηᴸᶜ W) X ≢ toRenameᵗ (ηᴿᶜ W) alpha
    → lookupStore (Σᵉ Cᴸ) X ≡ ＇ X
    → lookupStore (Σᵉ Cᴸ) X ⊑ᵀ⟨ W ⟩
        lookupStore (Σᵉ C) alpha
    → NameFocus W X alpha


liftNameFocus : ∀ {Cᴸ C} {W : Cᴸ ⊑ᶜ C} {X alpha}
  → NameFocus W X alpha
  → NameFocus (liftBothᶜ I.X⊑X W) (suc X) (suc alpha)
liftNameFocus {Cᴸ} {C} {W} {X} {alpha}
    (name-focus separated self represented) =
  name-focus lifted-separated (cong ⇑ᵗ self) lifted-represented
  where
  lifted-separated :
    toRenameᵗ (ηᴸᶜ (liftBothᶜ I.X⊑X W)) (suc X)
      ≢ toRenameᵗ (ηᴿᶜ (liftBothᶜ I.X⊑X W)) (suc alpha)
  lifted-separated eq = separated (fin-suc-injective eq)

  lifted-represented :
    lookupStore (Σᵉ (CastTerms.⇑ᵉᵗ Cᴸ)) (suc X)
      ⊑ᵀ⟨ liftBothᶜ I.X⊑X W ⟩
    lookupStore (Σᵉ (CastTerms.⇑ᵉᵗ C)) (suc alpha)
  lifted-represented =
    imprecision-cong
      (sym (rename-keep-shift (ηᴸᶜ W)
        (lookupStore (Σᵉ Cᴸ) X)))
      (sym (rename-keep-shift (ηᴿᶜ W)
        (lookupStore (Σᵉ C) alpha)))
      (lift-imprecision represented)


data Mode {C C⁺ : Ctx} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺) : Set where
  stable : Mode edge
  push-focus : Mode edge → TyVar (Δᵉ C⁺) → Mode edge


liftMode : ∀ {C C⁺ alpha beta alpha⁺}
    {edge : ExactAliasEdge C C⁺ alpha beta alpha⁺}
  → Mode edge
  → Mode (liftAliasEdge edge)
liftMode stable = stable
liftMode (push-focus m Y) = push-focus (liftMode m) (suc Y)


data TargetVarView : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocus W X alpha
  → (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
  → Mode edge
  → TyVar (Δᵉ C⁺) → TyVar (centerᶜ W) → Set where

  stable-old : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {Y Y⁺ Z}
    → edgeEmbed edge Y ≡ Y⁺
    → toRenameᵗ (ηᴿᶜ W) Y ≡ Z
    → TargetVarView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge stable Y⁺ Z

  focus-here : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {m Y Z}
    → toRenameᵗ (ηᴸᶜ W) X ≡ Z
    → TargetVarView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge (push-focus m Y) Y Z

  focus-there : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
      {m Y Y′ Z}
    → Y ≢ Y′
    → TargetVarView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m Y′ Z
    → TargetVarView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge (push-focus m Y) Y′ Z


data TargetTypeView : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → NameFocus W X alpha
  → (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
  → Mode edge
  → Ty (Δᵉ C⁺) → Ty (centerᶜ W) → Set where

  view-var : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m Y Z}
    → TargetVarView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m Y Z
    → TargetTypeView focus edge m (＇ Y) (＇ Z)

  view-base : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m iota}
    → TargetTypeView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m (‵ iota) (‵ iota)

  view-star : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
    → TargetTypeView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m ★ ★

  view-fun : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m}
      {A B A′ B′}
    → TargetTypeView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m A A′
    → TargetTypeView focus edge m B B′
    → TargetTypeView focus edge m (A ⇒ B) (A′ ⇒ B′)

  view-all : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m A B}
    → TargetTypeView (liftNameFocus focus) (liftAliasEdge edge)
        (liftMode m) A B
    → TargetTypeView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m (`∀ A) (`∀ B)


data ExactTargetBoundary : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocus W X alpha)
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
    (m : Mode edge) (Y : TyVar (Δᵉ C⁺))
    (R : Ty (Δᵉ C⁺)) (Rᶜ : Ty (centerᶜ W)) → Set where

  direct-target : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m Y R Rᶜ}
    → Σᵉ C⁺ ∋ Y ⦂ R
    → TargetTypeView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m R Rᶜ
    → I._⊢_⊑_ (marksᶜ W)
        (renameᵗ (toRenameᵗ (ηᴸᶜ W)) (＇ X)) Rᶜ
    → ExactTargetBoundary {Cᴸ} {C} {C⁺} W focus edge m Y R Rᶜ


data ValidMode : ∀ {Cᴸ C C⁺ : Ctx}
    (W : Cᴸ ⊑ᶜ C)
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    (focus : NameFocus W X alpha)
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
  → Mode edge → Set where

  stable-valid : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge}
    → ValidMode {Cᴸ} {C} {C⁺} W {X} {alpha} {beta} {alpha⁺}
        focus edge stable

  push-valid : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m Y R Rᶜ}
    → ValidMode {Cᴸ} {C} {C⁺} W {X} {alpha} {beta} {alpha⁺}
        focus edge m
    → ExactTargetBoundary {Cᴸ} {C} {C⁺} W {X} {alpha}
        {beta} {alpha⁺} focus edge m Y R Rᶜ
    → ValidMode {Cᴸ} {C} {C⁺} W {X} {alpha} {beta} {alpha⁺}
        focus edge (push-focus m Y)


stable-beta-unavailable : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge Z}
  → TargetVarView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
      {beta} {alpha⁺} focus edge stable beta Z
  → ⊥
stable-beta-unavailable {edge = edge}
    (stable-old {Y = Y} edge-eq center-eq) =
  edge-beta-fresh edge Y edge-eq


target-var-view-functional : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C} {X : TyVar (Δᵉ Cᴸ)}
    {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocus W X alpha}
    {edge : ExactAliasEdge C C⁺ alpha beta alpha⁺}
    {m Y Z Z′}
  → TargetVarView focus edge m Y Z
  → TargetVarView focus edge m Y Z′
  → Z ≡ Z′
target-var-view-functional {W = W} {edge = edge}
    (stable-old edge-eq center-eq)
    (stable-old edge-eq′ center-eq′) =
  trans (sym center-eq)
    (trans (cong (toRenameᵗ (ηᴿᶜ W)) old-eq) center-eq′)
  where
  old-eq = edgeEmbed-injective edge (trans edge-eq (sym edge-eq′))
target-var-view-functional (focus-here center-eq)
    (focus-here center-eq′) =
  trans (sym center-eq) center-eq′
target-var-view-functional (focus-here center-eq)
    (focus-there different view) =
  ⊥-elim (different refl)
target-var-view-functional (focus-there different view)
    (focus-here center-eq) =
  ⊥-elim (different refl)
target-var-view-functional (focus-there different view)
    (focus-there different′ view′) =
  target-var-view-functional view view′


target-type-view-functional : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C} {X : TyVar (Δᵉ Cᴸ)}
    {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : NameFocus W X alpha}
    {edge : ExactAliasEdge C C⁺ alpha beta alpha⁺}
    {m A B B′}
  → TargetTypeView focus edge m A B
  → TargetTypeView focus edge m A B′
  → B ≡ B′
target-type-view-functional (view-var view) (view-var view′) =
  cong ＇_ (target-var-view-functional view view′)
target-type-view-functional view-base view-base = refl
target-type-view-functional view-star view-star = refl
target-type-view-functional (view-fun view-A view-B)
    (view-fun view-A′ view-B′) =
  cong₂ _⇒_ (target-type-view-functional view-A view-A′)
    (target-type-view-functional view-B view-B′)
target-type-view-functional (view-all view) (view-all view′) =
  cong `∀ (target-type-view-functional view view′)

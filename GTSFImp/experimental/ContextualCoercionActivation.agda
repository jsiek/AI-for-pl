module experimental.ContextualCoercionActivation where

-- File Charter:
--   * Proves that an instantiation-bound contextual coercion can switch from
--     pending to active without changing its raw `Coercion` syntax.
--   * Uses freshness of the unaffected endpoint to orient the phase switch.
--   * Reuses the live substitution and occurrence infrastructure for binders.
--   * Leaves the live GTSFImp development unchanged.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
import Data.Nat as Nat
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types renaming (`∀ to `∀ᵗ)
open import Conversion using (replaceTy)
open import proof.ImprecisionConsistency using
  (shift-not-occurs; zero-absent-shift; subst-zero-occurs-exts)
import proof.TypeSafety.Preservation as Preservation
import Consistency as C
open import experimental.ContextualCoercion

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- A one-entry pending-to-active context change
------------------------------------------------------------------------

record OutActivation {X : TyVar Δ} (κ κ′ : CastCtx Δ) : Set where
  constructor out-activation
  field
    pending-out-at : κ X ≡ inst-out-bound pending
    active-out-at : κ′ X ≡ inst-out-bound active
    same-out-away : ∀ {Y} → X ≢ Y → κ Y ≡ κ′ Y

record InActivation {X : TyVar Δ} (κ κ′ : CastCtx Δ) : Set where
  constructor in-activation
  field
    pending-in-at : κ X ≡ inst-in-bound pending
    active-in-at : κ′ X ≡ inst-in-bound active
    same-in-away : ∀ {Y} → X ≢ Y → κ Y ≡ κ′ Y

open OutActivation
open InActivation

flip-out-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → InActivation {X = X} (flipCtx κ) (flipCtx κ′)
flip-out-activation (out-activation old new away) =
  in-activation (cong flipEntry old) (cong flipEntry new)
    (λ X≠Y → cong flipEntry (away X≠Y))

flip-in-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → OutActivation {X = X} (flipCtx κ) (flipCtx κ′)
flip-in-activation (in-activation old new away) =
  out-activation (cong flipEntry old) (cong flipEntry new)
    (λ X≠Y → cong flipEntry (away X≠Y))

ext-out-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → OutActivation {X = suc X} (extCtx κ) (extCtx κ′)
ext-out-activation {X = X} (out-activation old new away) =
  out-activation old new away′
  where
  away′ : ∀ {Y} → suc X ≢ Y → extCtx _ Y ≡ extCtx _ Y
  away′ {zero} sucX≠zero = refl
  away′ {suc Y} sucX≠sucY =
    away (λ X≡Y → sucX≠sucY (cong suc X≡Y))

ext-in-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → InActivation {X = suc X} (extCtx κ) (extCtx κ′)
ext-in-activation {X = X} (in-activation old new away) =
  in-activation old new away′
  where
  away′ : ∀ {Y} → suc X ≢ Y → extCtx _ Y ≡ extCtx _ Y
  away′ {zero} sucX≠zero = refl
  away′ {suc Y} sucX≠sucY =
    away (λ X≡Y → sucX≠sucY (cong suc X≡Y))

inst-out-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → OutActivation {X = suc X}
      (instCtx pending κ) (instCtx pending κ′)
inst-out-activation {X = X} (out-activation old new away) =
  out-activation old new away′
  where
  away′ : ∀ {Y} → suc X ≢ Y
    → instCtx pending _ Y ≡ instCtx pending _ Y
  away′ {zero} sucX≠zero = refl
  away′ {suc Y} sucX≠sucY =
    away (λ X≡Y → sucX≠sucY (cong suc X≡Y))

inst-in-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → InActivation {X = suc X}
      (instCtx pending κ) (instCtx pending κ′)
inst-in-activation {X = X} (in-activation old new away) =
  in-activation old new away′
  where
  away′ : ∀ {Y} → suc X ≢ Y
    → instCtx pending _ Y ≡ instCtx pending _ Y
  away′ {zero} sucX≠zero = refl
  away′ {suc Y} sucX≠sucY =
    away (λ X≡Y → sucX≠sucY (cong suc X≡Y))

gen-out-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → OutActivation {X = suc X} (genCtx κ) (genCtx κ′)
gen-out-activation {X = X} (out-activation old new away) =
  out-activation old new away′
  where
  away′ : ∀ {Y} → suc X ≢ Y → genCtx _ Y ≡ genCtx _ Y
  away′ {zero} sucX≠zero = refl
  away′ {suc Y} sucX≠sucY =
    away (λ X≡Y → sucX≠sucY (cong suc X≡Y))

gen-in-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → InActivation {X = suc X} (genCtx κ) (genCtx κ′)
gen-in-activation {X = X} (in-activation old new away) =
  in-activation old new away′
  where
  away′ : ∀ {Y} → suc X ≢ Y → genCtx _ Y ≡ genCtx _ Y
  away′ {zero} sucX≠zero = refl
  away′ {suc Y} sucX≠sucY =
    away (λ X≡Y → sucX≠sucY (cong suc X≡Y))

out-entry-mode-eq : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → ∀ Y → entryMode (κ Y) ≡ entryMode (κ′ Y)
out-entry-mode-eq {X = X} activation Y with X ≟ Y
out-entry-mode-eq {X = X} activation .X | yes refl =
  trans (cong entryMode (pending-out-at activation))
    (sym (cong entryMode (active-out-at activation)))
out-entry-mode-eq {X = X} activation Y | no X≠Y =
  cong entryMode (same-out-away activation X≠Y)

in-entry-mode-eq : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → ∀ Y → entryMode (κ Y) ≡ entryMode (κ′ Y)
in-entry-mode-eq {X = X} activation Y with X ≟ Y
in-entry-mode-eq {X = X} activation .X | yes refl =
  trans (cong entryMode (pending-in-at activation))
    (sym (cong entryMode (active-in-at activation)))
in-entry-mode-eq {X = X} activation Y | no X≠Y =
  cong entryMode (same-in-away activation X≠Y)

toEnv∼-out-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → C.Env∼Eq (toEnv∼ κ) (toEnv∼ κ′)
toEnv∼-out-activation = out-entry-mode-eq

toEnv∼-in-activation : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → C.Env∼Eq (toEnv∼ κ) (toEnv∼ κ′)
toEnv∼-in-activation = in-entry-mode-eq

------------------------------------------------------------------------
-- Type replacement and generic-ground support
------------------------------------------------------------------------

replace-not-occurs : ∀ {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → replaceTy X ★ A ≡ A
replace-not-occurs {X = X} (∉-var {Y = Y} X≠Y) with X ≟ Y
replace-not-occurs (∉-var X≠X) | yes refl =
  ⊥-elim (≢ᶠ→≢ X≠X refl)
replace-not-occurs (∉-var X≠Y) | no X≠Y′ = refl
replace-not-occurs ∉-base = refl
replace-not-occurs ∉-star = refl
replace-not-occurs (∉-fun X∉A X∉B) =
  cong₂ _⇒_ (replace-not-occurs X∉A) (replace-not-occurs X∉B)
replace-not-occurs (∉-all X∉A) =
  cong `∀ᵗ (replace-not-occurs X∉A)

replace-nonvar : ∀ {X : TyVar Δ} {A : Ty Δ}
  → NonVar A
  → NonVar (replaceTy X ★ A)
replace-nonvar nonvar-base = nonvar-base
replace-nonvar nonvar-star = nonvar-star
replace-nonvar nonvar-fun = nonvar-fun
replace-nonvar nonvar-all = nonvar-all

replace-nonstar : ∀ {X : TyVar Δ} {A : Ty Δ}
  → NonStar A
  → A ≢ ＇ X
  → NonStar (replaceTy X ★ A)
replace-nonstar {X = X} (nonstar-X {X = Y}) Y≠X with X ≟ Y
replace-nonstar {X = X} (nonstar-X {X = .X}) Y≠X | yes refl =
  ⊥-elim (Y≠X refl)
replace-nonstar {X = X} (nonstar-X {X = Y}) Y≠X | no X≠Y =
  nonstar-X
replace-nonstar nonstar-ι A≠X = nonstar-ι
replace-nonstar nonstar-⇒ A≠X = nonstar-⇒
replace-nonstar nonstar-∀ A≠X = nonstar-∀

nonstar-from-≢★ : ∀ {A : Ty Δ} → A ≢ ★ → NonStar A
nonstar-from-≢★ {A = ＇ X} A≠★ = nonstar-X
nonstar-from-≢★ {A = ‵ ι} A≠★ = nonstar-ι
nonstar-from-≢★ {A = ★} A≠★ = ⊥-elim (A≠★ refl)
nonstar-from-≢★ {A = A ⇒ B} A≠★ = nonstar-⇒
nonstar-from-≢★ {A = `∀ᵗ A} A≠★ = nonstar-∀

replace-nonstar-from-≢ : ∀ {X : TyVar Δ} {A : Ty Δ}
  → A ≢ ★
  → A ≢ ＇ X
  → replaceTy X ★ A ≢ ★
replace-nonstar-from-≢ A≠★ A≠X =
  nonStar≢★ (replace-nonstar (nonstar-from-≢★ A≠★) A≠X)

replace-shift : ∀ {X : TyVar Δ} (A : Ty Δ)
  → replaceTy (suc X) ★ (⇑ᵗ A) ≡ ⇑ᵗ (replaceTy X ★ A)
replace-shift {X = X} A =
  trans (Preservation.replaceTy-subst (suc X) ★ (⇑ᵗ A))
    (trans
      (substᵗ-cong (⇑ᵗ A) (Preservation.replaceEnv-ext X ★))
      (trans (substᵗ-shift (Preservation.replaceEnv X ★) A)
        (cong (λ B → ⇑ᵗ B)
          (sym (Preservation.replaceTy-subst X ★ A)))))

replace-suc-zero-occurs : ∀ {X : TyVar Δ} {A : Ty (Nat.suc Δ)}
  → zero ∈ᵗ A
  → zero ∈ᵗ replaceTy (suc X) ★ A
replace-suc-zero-occurs {X = X} {A = A} zero∈A =
  subst (zero ∈ᵗ_)
    (sym
      (trans (Preservation.replaceTy-subst (suc X) ★ A)
        (substᵗ-cong A (Preservation.replaceEnv-ext X ★))))
    (subst-zero-occurs-exts zero∈A)

ordinary-away-out : ∀ {X Y : TyVar Δ} {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → OrdinaryVariable κ Y
  → X ≢ Y
ordinary-away-out activation (ordinary-entry mode ordinary-Y) refl
    with trans (sym (pending-out-at activation)) ordinary-Y
ordinary-away-out activation (ordinary-entry mode ordinary-Y) refl | ()

ordinary-away-in : ∀ {X Y : TyVar Δ} {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → OrdinaryVariable κ Y
  → X ≢ Y
ordinary-away-in activation (ordinary-entry mode ordinary-Y) refl
    with trans (sym (pending-in-at activation)) ordinary-Y
ordinary-away-in activation (ordinary-entry mode ordinary-Y) refl | ()

activate-generic-out : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ} {G}
  → OutActivation {X = X} κ κ′
  → GenericGround κ G
  → GenericGround κ′ G
activate-generic-out activation generic-⇒ = generic-⇒
activate-generic-out activation generic-ι = generic-ι
activate-generic-out activation
    (generic-X (ordinary-entry mode ordinary-Y)) =
  generic-X (ordinary-entry mode ordinary-Y′)
  where
  X≠Y = ordinary-away-out activation (ordinary-entry mode ordinary-Y)
  ordinary-Y′ =
    trans (sym (same-out-away activation X≠Y)) ordinary-Y
activate-generic-out activation generic-∀ = generic-∀

activate-generic-in : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ} {G}
  → InActivation {X = X} κ κ′
  → GenericGround κ G
  → GenericGround κ′ G
activate-generic-in activation generic-⇒ = generic-⇒
activate-generic-in activation generic-ι = generic-ι
activate-generic-in activation
    (generic-X (ordinary-entry mode ordinary-Y)) =
  generic-X (ordinary-entry mode ordinary-Y′)
  where
  X≠Y = ordinary-away-in activation (ordinary-entry mode ordinary-Y)
  ordinary-Y′ =
    trans (sym (same-in-away activation X≠Y)) ordinary-Y
activate-generic-in activation generic-∀ = generic-∀

generic-fresh-out : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ} {G}
  → OutActivation {X = X} κ κ′
  → GenericGround κ G
  → X ∉ᵗ G
generic-fresh-out activation generic-⇒ = ∉-fun ∉-star ∉-star
generic-fresh-out activation generic-ι = ∉-base
generic-fresh-out activation (generic-X ordinary-Y) =
  ∉-var (≢→≢ᶠ (ordinary-away-out activation ordinary-Y))
generic-fresh-out activation generic-∀ = ∉-all ∉-star

generic-fresh-in : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ} {G}
  → InActivation {X = X} κ κ′
  → GenericGround κ G
  → X ∉ᵗ G
generic-fresh-in activation generic-⇒ = ∉-fun ∉-star ∉-star
generic-fresh-in activation generic-ι = ∉-base
generic-fresh-in activation (generic-X ordinary-Y) =
  ∉-var (≢→≢ᶠ (ordinary-away-in activation ordinary-Y))
generic-fresh-in activation generic-∀ = ∉-all ∉-star

generic-not-star : ∀ {κ : CastCtx Δ} {G}
  → GenericGround κ G
  → G ≢ ★
generic-not-star generic-⇒ ()
generic-not-star generic-ι ()
generic-not-star (generic-X ordinary-X) ()
generic-not-star generic-∀ ()

absent-present : ∀ {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → X ∈ᵗ A
  → ⊥
absent-present (∉-var X≠Y) var-∈ = ≢ᶠ→≢ X≠Y refl
absent-present ∉-base ()
absent-present ∉-star ()
absent-present (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
  absent-present X∉A X∈A
absent-present (∉-fun X∉A X∉B)
    (∈-fun-right X∉A′ X∈B) =
  absent-present X∉B X∈B
absent-present (∉-all X∉A) (∈-all X∈A) =
  absent-present X∉A X∈A

generic-not-focus-out : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {G}
  → OutActivation {X = X} κ κ′
  → GenericGround κ G
  → G ≢ ＇ X
generic-not-focus-out {X = X} activation generic G≡X =
  absent-present
    (subst (X ∉ᵗ_) G≡X (generic-fresh-out activation generic))
    var-∈

generic-not-focus-in : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {G}
  → InActivation {X = X} κ κ′
  → GenericGround κ G
  → G ≢ ＇ X
generic-not-focus-in {X = X} activation generic G≡X =
  absent-present
    (subst (X ∉ᵗ_) G≡X (generic-fresh-in activation generic))
    var-∈

activate-to-star-out : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {G}
  → OutActivation {X = X} κ κ′
  → C._⊢_∼★ (toEnv∼ κ) G
  → C._⊢_∼★ (toEnv∼ κ′) G
activate-to-star-out activation =
  C.transport-∼★ (toEnv∼-out-activation activation)

activate-to-star-in : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {G}
  → InActivation {X = X} κ κ′
  → C._⊢_∼★ (toEnv∼ κ) G
  → C._⊢_∼★ (toEnv∼ κ′) G
activate-to-star-in activation =
  C.transport-∼★ (toEnv∼-in-activation activation)

activate-from-star-out : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {G}
  → OutActivation {X = X} κ κ′
  → C._⊢★∼_ (toEnv∼ κ) G
  → C._⊢★∼_ (toEnv∼ κ′) G
activate-from-star-out activation =
  C.transport-★∼ (toEnv∼-out-activation activation)

activate-from-star-in : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {G}
  → InActivation {X = X} κ κ′
  → C._⊢★∼_ (toEnv∼ κ) G
  → C._⊢★∼_ (toEnv∼ κ′) G
activate-from-star-in activation =
  C.transport-★∼ (toEnv∼-in-activation activation)

nonvar-variable-impossible : ∀ {X : TyVar Δ} → NonVar (＇ X) → ⊥
nonvar-variable-impossible ()

occurs-star-impossible : ∀ {X : TyVar Δ} → X ∈ᵗ ★ → ⊥
occurs-star-impossible ()

tag-source-not-focus : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {c A G}
  → OutActivation {X = X} κ κ′
  → GenericGround κ G
  → κ ⊢ c ∶ A ⇒ G
  → A ≢ ＇ X
tag-source-not-focus {κ = κ} {G = G} activation generic c⊢ A≡X
    with source-variable-shape
      (subst (λ T → C._⊢_∼_ (toEnv∼ κ) T G)
        A≡X (coercion→consistency c⊢))
tag-source-not-focus activation generic c⊢ A≡X | inj₁ G≡X =
  ⊥-elim (generic-not-focus-out activation generic G≡X)
tag-source-not-focus activation generic c⊢ A≡X | inj₂ G≡★ =
  ⊥-elim (generic-not-star generic G≡★)

untag-target-not-focus : ∀ {X : TyVar Δ}
    {κ κ′ : CastCtx Δ} {c G B}
  → InActivation {X = X} κ κ′
  → GenericGround κ G
  → κ ⊢ c ∶ G ⇒ B
  → B ≢ ＇ X
untag-target-not-focus {κ = κ} {G = G} activation generic c⊢ B≡X
    with target-variable-shape
      (subst (λ T → C._⊢_∼_ (toEnv∼ κ) G T)
        B≡X (coercion→consistency c⊢))
untag-target-not-focus activation generic c⊢ B≡X | inj₁ G≡X =
  ⊥-elim (generic-not-focus-in activation generic G≡X)
untag-target-not-focus activation generic c⊢ B≡X | inj₂ G≡★ =
  ⊥-elim (generic-not-star generic G≡★)

gen-source-not-focus : ∀ {X : TyVar Δ}
    {κ : CastCtx (Nat.suc Δ)} {c A B}
  → κ ⊢ c ∶ ⇑ᵗ A ⇒ B
  → NonVar B
  → zero ∈ᵗ B
  → A ≢ ＇ X
gen-source-not-focus {κ = κ} {B = B} c⊢ nonvar occurs A≡X
    with source-variable-shape
      (subst (λ T → C._⊢_∼_ (toEnv∼ κ) T B)
        (cong (λ T → ⇑ᵗ T) A≡X)
        (coercion→consistency c⊢))
gen-source-not-focus c⊢ nonvar occurs A≡X | inj₁ B≡X =
  ⊥-elim (nonvar-variable-impossible (subst NonVar B≡X nonvar))
gen-source-not-focus c⊢ nonvar occurs A≡X | inj₂ B≡★ =
  ⊥-elim
    (occurs-star-impossible (subst (zero ∈ᵗ_) B≡★ occurs))

inst-target-not-focus : ∀ {X : TyVar Δ}
    {κ : CastCtx (Nat.suc Δ)} {c A B}
  → κ ⊢ c ∶ A ⇒ ⇑ᵗ B
  → NonVar A
  → zero ∈ᵗ A
  → B ≢ ＇ X
inst-target-not-focus {κ = κ} {A = A} c⊢ nonvar occurs B≡X
    with target-variable-shape
      (subst (λ T → C._⊢_∼_ (toEnv∼ κ) A T)
        (cong (λ T → ⇑ᵗ T) B≡X)
        (coercion→consistency c⊢))
inst-target-not-focus c⊢ nonvar occurs B≡X | inj₁ A≡X =
  ⊥-elim (nonvar-variable-impossible (subst NonVar A≡X nonvar))
inst-target-not-focus c⊢ nonvar occurs B≡X | inj₂ A≡★ =
  ⊥-elim
    (occurs-star-impossible (subst (zero ∈ᵗ_) A≡★ occurs))

------------------------------------------------------------------------
-- Specialized leaves under activation
------------------------------------------------------------------------

activate-out-out-pending : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → κ Y ≡ inst-out-bound pending
  → κ′ ⊢ inst-out Y ∶ replaceTy X ★ (＇ Y) ⇒ ★
activate-out-out-pending {X = X} {Y = Y} activation eq with X ≟ Y
activate-out-out-pending {X = X} {Y = .X} activation eq | yes refl =
  ⊢inst-out-active (active-out-at activation)
activate-out-out-pending {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-out-pending
    (trans (sym (same-out-away activation X≠Y)) eq)

activate-out-out-active : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → κ Y ≡ inst-out-bound active
  → κ′ ⊢ inst-out Y ∶ replaceTy X ★ ★ ⇒ ★
activate-out-out-active {X = X} {Y = Y} activation eq with X ≟ Y
activate-out-out-active {X = X} {Y = .X} activation eq | yes refl
    with trans (sym (pending-out-at activation)) eq
activate-out-out-active {X = X} {Y = .X} activation eq | yes refl | ()
activate-out-out-active {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-out-active
    (trans (sym (same-out-away activation X≠Y)) eq)

activate-out-in-pending : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → κ Y ≡ inst-in-bound pending
  → κ′ ⊢ inst-in Y ∶ replaceTy X ★ ★ ⇒ ＇ Y
activate-out-in-pending {X = X} {Y = Y} activation eq with X ≟ Y
activate-out-in-pending {X = X} {Y = .X} activation eq | yes refl
    with trans (sym (pending-out-at activation)) eq
activate-out-in-pending {X = X} {Y = .X} activation eq | yes refl | ()
activate-out-in-pending {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-in-pending
    (trans (sym (same-out-away activation X≠Y)) eq)

activate-out-in-active : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → OutActivation {X = X} κ κ′
  → κ Y ≡ inst-in-bound active
  → κ′ ⊢ inst-in Y ∶ replaceTy X ★ ★ ⇒ ★
activate-out-in-active {X = X} {Y = Y} activation eq with X ≟ Y
activate-out-in-active {X = X} {Y = .X} activation eq | yes refl
    with trans (sym (pending-out-at activation)) eq
activate-out-in-active {X = X} {Y = .X} activation eq | yes refl | ()
activate-out-in-active {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-in-active
    (trans (sym (same-out-away activation X≠Y)) eq)

activate-in-in-pending : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → κ Y ≡ inst-in-bound pending
  → κ′ ⊢ inst-in Y ∶ ★ ⇒ replaceTy X ★ (＇ Y)
activate-in-in-pending {X = X} {Y = Y} activation eq with X ≟ Y
activate-in-in-pending {X = X} {Y = .X} activation eq | yes refl =
  ⊢inst-in-active (active-in-at activation)
activate-in-in-pending {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-in-pending
    (trans (sym (same-in-away activation X≠Y)) eq)

activate-in-in-active : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → κ Y ≡ inst-in-bound active
  → κ′ ⊢ inst-in Y ∶ ★ ⇒ replaceTy X ★ ★
activate-in-in-active {X = X} {Y = Y} activation eq with X ≟ Y
activate-in-in-active {X = X} {Y = .X} activation eq | yes refl
    with trans (sym (pending-in-at activation)) eq
activate-in-in-active {X = X} {Y = .X} activation eq | yes refl | ()
activate-in-in-active {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-in-active
    (trans (sym (same-in-away activation X≠Y)) eq)

activate-in-out-pending : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → κ Y ≡ inst-out-bound pending
  → κ′ ⊢ inst-out Y ∶ ＇ Y ⇒ replaceTy X ★ ★
activate-in-out-pending {X = X} {Y = Y} activation eq with X ≟ Y
activate-in-out-pending {X = X} {Y = .X} activation eq | yes refl
    with trans (sym (pending-in-at activation)) eq
activate-in-out-pending {X = X} {Y = .X} activation eq | yes refl | ()
activate-in-out-pending {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-out-pending
    (trans (sym (same-in-away activation X≠Y)) eq)

activate-in-out-active : ∀ {X Y : TyVar Δ}
    {κ κ′ : CastCtx Δ}
  → InActivation {X = X} κ κ′
  → κ Y ≡ inst-out-bound active
  → κ′ ⊢ inst-out Y ∶ ★ ⇒ replaceTy X ★ ★
activate-in-out-active {X = X} {Y = Y} activation eq with X ≟ Y
activate-in-out-active {X = X} {Y = .X} activation eq | yes refl
    with trans (sym (pending-in-at activation)) eq
activate-in-out-active {X = X} {Y = .X} activation eq | yes refl | ()
activate-in-out-active {X = X} {Y = Y} activation eq | no X≠Y =
  ⊢inst-out-active
    (trans (sym (same-in-away activation X≠Y)) eq)

------------------------------------------------------------------------
-- Phase activation preserves the raw coercion
------------------------------------------------------------------------

mutual
  activate-out : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
      {c A B}
    → OutActivation {X = X} κ κ′
    → X ∉ᵗ B
    → κ ⊢ c ∶ A ⇒ B
    → κ′ ⊢ c ∶ replaceTy X ★ A ⇒ B
  activate-out {κ′ = κ′} {A = A} activation fresh (⊢id atom) =
    transport-coercion-typing (sym (replace-not-occurs fresh)) refl
      (⊢id atom)
  activate-out activation (∉-fun X∉A′ X∉B′) (⊢↦ c⊢ d⊢) =
    ⊢↦
      (activate-in (flip-out-activation activation) X∉A′ c⊢)
      (activate-out activation X∉B′ d⊢)
  activate-out activation (∉-all X∉B) (⊢∀ c⊢) =
    ⊢∀ (activate-out (ext-out-activation activation) X∉B c⊢)
  activate-out activation fresh
      (⊢inj generic gate c⊢ nonstar) =
    ⊢inj (activate-generic-out activation generic)
      (activate-to-star-out activation gate)
      (activate-out activation (generic-fresh-out activation generic) c⊢)
      (replace-nonstar nonstar
        (tag-source-not-focus activation generic c⊢))
  activate-out activation fresh
      (⊢proj generic gate c⊢ nonstar) =
    ⊢proj (activate-generic-out activation generic)
      (activate-from-star-out activation gate)
      (transport-coercion-typing
        (replace-not-occurs (generic-fresh-out activation generic)) refl
        (activate-out activation fresh c⊢))
      nonstar
  activate-out activation fresh (⊢inst-out-pending eq) =
    activate-out-out-pending activation eq
  activate-out activation fresh (⊢inst-out-active eq) =
    activate-out-out-active activation eq
  activate-out activation fresh (⊢inst-in-pending eq) =
    activate-out-in-pending activation eq
  activate-out activation fresh (⊢inst-in-active eq) =
    activate-out-in-active activation eq
  activate-out activation fresh
      (⊢inst nonvar occurs c⊢ B≠★) =
    ⊢inst (replace-nonvar nonvar) (replace-suc-zero-occurs occurs)
      (activate-out (inst-out-activation activation)
        (shift-not-occurs fresh) c⊢)
      B≠★
  activate-out {X = X} activation (∉-all X∉B)
      (⊢gen {A = A} nonvar occurs c⊢ A≠★) =
    ⊢gen nonvar occurs
      (transport-coercion-typing (replace-shift A) refl
        (activate-out (gen-out-activation activation) X∉B c⊢))
      (replace-nonstar-from-≢ A≠★
        (gen-source-not-focus c⊢ nonvar occurs))
  activate-out activation fresh ⊢bot-elim = ⊢bot-elim
  activate-out activation fresh ⊢bot-intro = ⊢bot-intro

  activate-in : ∀ {X : TyVar Δ} {κ κ′ : CastCtx Δ}
      {c A B}
    → InActivation {X = X} κ κ′
    → X ∉ᵗ A
    → κ ⊢ c ∶ A ⇒ B
    → κ′ ⊢ c ∶ A ⇒ replaceTy X ★ B
  activate-in {κ′ = κ′} {A = A} activation fresh (⊢id atom) =
    transport-coercion-typing refl (sym (replace-not-occurs fresh))
      (⊢id atom)
  activate-in activation (∉-fun X∉A X∉B) (⊢↦ c⊢ d⊢) =
    ⊢↦
      (activate-out (flip-in-activation activation) X∉A c⊢)
      (activate-in activation X∉B d⊢)
  activate-in activation (∉-all X∉A) (⊢∀ c⊢) =
    ⊢∀ (activate-in (ext-in-activation activation) X∉A c⊢)
  activate-in activation fresh
      (⊢inj generic gate c⊢ nonstar) =
    ⊢inj (activate-generic-in activation generic)
      (activate-to-star-in activation gate)
      (transport-coercion-typing refl
        (replace-not-occurs (generic-fresh-in activation generic))
        (activate-in activation fresh c⊢))
      nonstar
  activate-in activation fresh
      (⊢proj generic gate c⊢ nonstar) =
    ⊢proj (activate-generic-in activation generic)
      (activate-from-star-in activation gate)
      (activate-in activation
        (generic-fresh-in activation generic) c⊢)
      (replace-nonstar nonstar
        (untag-target-not-focus activation generic c⊢))
  activate-in activation fresh (⊢inst-out-pending eq) =
    activate-in-out-pending activation eq
  activate-in activation fresh (⊢inst-out-active eq) =
    activate-in-out-active activation eq
  activate-in activation fresh (⊢inst-in-pending eq) =
    activate-in-in-pending activation eq
  activate-in activation fresh (⊢inst-in-active eq) =
    activate-in-in-active activation eq
  activate-in {X = X} activation (∉-all X∉A)
      (⊢inst {B = B} nonvar occurs c⊢ B≠★) =
    ⊢inst nonvar occurs
      (transport-coercion-typing refl (replace-shift B)
        (activate-in (inst-in-activation activation) X∉A c⊢))
      (replace-nonstar-from-≢ B≠★
        (inst-target-not-focus c⊢ nonvar occurs))
  activate-in activation fresh
      (⊢gen nonvar occurs c⊢ A≠★) =
    ⊢gen (replace-nonvar nonvar) (replace-suc-zero-occurs occurs)
      (activate-in (gen-in-activation activation)
        (shift-not-occurs fresh) c⊢)
      A≠★
  activate-in activation fresh ⊢bot-elim = ⊢bot-elim
  activate-in activation fresh ⊢bot-intro = ⊢bot-intro

newest-out-activation : ∀ {Δ} {κ : CastCtx Δ}
  → OutActivation {X = zero}
      (instCtx pending κ) (instCtx active κ)
newest-out-activation = out-activation refl refl away
  where
  away : ∀ {Δ} {κ : CastCtx Δ} {Y}
    → zero ≢ Y
    → instCtx pending κ Y ≡ instCtx active κ Y
  away {Y = zero} zero≠zero = ⊥-elim (zero≠zero refl)
  away {Y = suc Y} zero≠sucY = refl

activate-newest-typing : ∀ {Δ} {κ : CastCtx Δ}
    {c : Coercion (Nat.suc Δ)} {A : Ty (Nat.suc Δ)} {B : Ty Δ}
  → instCtx pending κ ⊢ c ∶ A ⇒ ⇑ᵗ B
  → instCtx active κ ⊢ c ∶ replaceTy zero ★ A ⇒ ⇑ᵗ B
activate-newest-typing {B = B} c⊢ =
  activate-out newest-out-activation (zero-absent-shift B) c⊢

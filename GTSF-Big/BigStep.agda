module BigStep where

-- File Charter:
--   * Structural big-step semantics for Nu GTSF terms.
--   * Records the exact store-change trace and shifts suspended syntax after
--     allocation in the same way as the existing small-step semantics.
--   * Reuses only the pure root-reduction relation from `NuReduction`; the
--     evaluation order and recursive evaluation rules are defined here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Coercions using (Coercion; Inert)
open import NuReduction using
  ( StoreChanges
  ; Shiftable
  ; applyCoercion
  ; applyCoercionUnderTyBinder
  ; applyTerm
  ; applyTerms
  ; applyTys
  ; bind
  ; keep
  ; _—→_
  )
open import NuTerms

------------------------------------------------------------------------
-- Lifting syntax through a trace below a type binder
------------------------------------------------------------------------

applyCoercions : StoreChanges → Coercion → Coercion
applyCoercions [] c = c
applyCoercions (χ ∷ χs) c =
  applyCoercions χs (applyCoercion χ c)

applyCoercionsUnderTyBinders : StoreChanges → Coercion → Coercion
applyCoercionsUnderTyBinders [] c = c
applyCoercionsUnderTyBinders (χ ∷ χs) c =
  applyCoercionsUnderTyBinders χs
    (applyCoercionUnderTyBinder χ c)

data TraceShiftable : StoreChanges → Term → Set where
  shiftable-[] :
    ∀ {M} →
    TraceShiftable [] M

  shiftable-∷ :
    ∀ {χ χs M} →
    Shiftable χ M →
    TraceShiftable χs (applyTerm χ M) →
    TraceShiftable (χ ∷ χs) M

------------------------------------------------------------------------
-- Structural call-by-value evaluation
------------------------------------------------------------------------

infix 2 _⇓[_]_

data _⇓[_]_ : Term → StoreChanges → Term → Set where

  ⇓-value :
    ∀ {V} →
    Value V →
    V ⇓[ [] ] V

  ⇓-blame :
    blame ⇓[ [] ] blame

  ⇓-app-left-blame :
    ∀ {L M χsL} →
    L ⇓[ χsL ] blame →
    TraceShiftable χsL M →
    L · M ⇓[ χsL ++ (keep ∷ []) ] blame

  ⇓-app-right-blame :
    ∀ {L M V χsL χsM} →
    L ⇓[ χsL ] V →
    Value V →
    TraceShiftable χsL M →
    applyTerms χsL M ⇓[ χsM ] blame →
    TraceShiftable χsM V →
    L · M ⇓[ χsL ++ (χsM ++ (keep ∷ [])) ] blame

  ⇓-app :
    ∀ {L M V W N R χsL χsM χsN} →
    L ⇓[ χsL ] V →
    Value V →
    TraceShiftable χsL M →
    applyTerms χsL M ⇓[ χsM ] W →
    Value W →
    TraceShiftable χsM V →
    applyTerms χsM V · W —→ N →
    N ⇓[ χsN ] R →
    L · M ⇓[ χsL ++ (χsM ++ (keep ∷ χsN)) ] R

  ⇓-type-app :
    ∀ {M N R χsN} →
    M • —→ N →
    N ⇓[ χsN ] R →
    M • ⇓[ keep ∷ χsN ] R

  ⇓-nu-blame :
    ∀ {A L c χsL} →
    L ⇓[ χsL ] blame →
    ν A L c ⇓[ χsL ++ (keep ∷ []) ] blame

  ⇓-nu :
    ∀ {A L c V R χsL χsN} →
    L ⇓[ χsL ] V →
    Value V →
    No• V →
    ((⇑ᵗᵐ V) •)
      ⟨ applyCoercionsUnderTyBinders χsL c ⟩
      ⇓[ χsN ] R →
    ν A L c
      ⇓[ χsL ++ (bind (applyTys χsL A) ∷ χsN) ] R

  ⇓-prim-left-blame :
    ∀ {L M op χsL} →
    L ⇓[ χsL ] blame →
    TraceShiftable χsL M →
    L ⊕[ op ] M ⇓[ χsL ++ (keep ∷ []) ] blame

  ⇓-prim-right-blame :
    ∀ {L M op V χsL χsM} →
    L ⇓[ χsL ] V →
    Value V →
    TraceShiftable χsL M →
    applyTerms χsL M ⇓[ χsM ] blame →
    TraceShiftable χsM V →
    L ⊕[ op ] M
      ⇓[ χsL ++ (χsM ++ (keep ∷ [])) ] blame

  ⇓-prim :
    ∀ {L M op V W N R χsL χsM χsN} →
    L ⇓[ χsL ] V →
    Value V →
    TraceShiftable χsL M →
    applyTerms χsL M ⇓[ χsM ] W →
    Value W →
    TraceShiftable χsM V →
    applyTerms χsM V ⊕[ op ] W —→ N →
    N ⇓[ χsN ] R →
    L ⊕[ op ] M
      ⇓[ χsL ++ (χsM ++ (keep ∷ χsN)) ] R

  ⇓-cast-blame :
    ∀ {M c χsM} →
    M ⇓[ χsM ] blame →
    M ⟨ c ⟩ ⇓[ χsM ++ (keep ∷ []) ] blame

  ⇓-cast-inert :
    ∀ {M c V χsM} →
    M ⇓[ χsM ] V →
    Value V →
    Inert (applyCoercions χsM c) →
    M ⟨ c ⟩ ⇓[ χsM ] V ⟨ applyCoercions χsM c ⟩

  ⇓-cast-active :
    ∀ {M c V N R χsM χsN} →
    M ⇓[ χsM ] V →
    Value V →
    V ⟨ applyCoercions χsM c ⟩ —→ N →
    N ⇓[ χsN ] R →
    M ⟨ c ⟩ ⇓[ χsM ++ (keep ∷ χsN) ] R

------------------------------------------------------------------------
-- Every derivation returns an observable result
------------------------------------------------------------------------

Final : Term → Set
Final R = Value R ⊎ R ≡ blame

big-step-final :
  ∀ {M χs R} →
  M ⇓[ χs ] R →
  Final R
big-step-final (⇓-value vV) = inj₁ vV
big-step-final ⇓-blame = inj₂ refl
big-step-final (⇓-app-left-blame M⇓ shiftM) = inj₂ refl
big-step-final (⇓-app-right-blame L⇓ vV shiftM M⇓ shiftV) =
  inj₂ refl
big-step-final (⇓-app L⇓ vV shiftM M⇓ vW shiftV root N⇓) =
  big-step-final N⇓
big-step-final (⇓-type-app root N⇓) = big-step-final N⇓
big-step-final (⇓-nu-blame L⇓) = inj₂ refl
big-step-final (⇓-nu L⇓ vV noV N⇓) = big-step-final N⇓
big-step-final (⇓-prim-left-blame L⇓ shiftM) = inj₂ refl
big-step-final (⇓-prim-right-blame L⇓ vV shiftM M⇓ shiftV) =
  inj₂ refl
big-step-final (⇓-prim L⇓ vV shiftM M⇓ vW shiftV root N⇓) =
  big-step-final N⇓
big-step-final (⇓-cast-blame M⇓) = inj₂ refl
big-step-final (⇓-cast-inert M⇓ vV inert-c) =
  inj₁ (vV ⟨ inert-c ⟩)
big-step-final (⇓-cast-active M⇓ vV root N⇓) =
  big-step-final N⇓

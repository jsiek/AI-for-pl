module experimental.ContextualCoercion where

-- File Charter:
--   * Defines raw `Coercion` syntax separately from contextual typing.
--   * Realizes instantiation-bound variables only at `inst-out` and
--     `inst-in` leaves; all structural typing rules use ordinary endpoints.
--   * Prevents generic injection and projection from handling an
--     instantiation-bound ground variable.
--   * Relates contextual coercion typing to live consistency.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)

open import Types renaming (`∀ to `∀ᵗ)
import Consistency as C

private
  variable
    Δ : TyCtx
    A A′ B B′ : Ty Δ

------------------------------------------------------------------------
-- Raw coercions
------------------------------------------------------------------------

infixr 7 _↦_
infix 8 _! ？_

data Coercion : (Δ : TyCtx) → Set where
  id : Coercion Δ
  _↦_ : Coercion Δ → Coercion Δ → Coercion Δ
  `∀_ : Coercion (suc Δ) → Coercion Δ
  _! : Coercion Δ → Coercion Δ
  ？_ : Coercion Δ → Coercion Δ
  inst-out : TyVar Δ → Coercion Δ
  inst-in : TyVar Δ → Coercion Δ
  inst : Coercion (suc Δ) → Coercion Δ
  gen : Coercion (suc Δ) → Coercion Δ
  bot-elim : Coercion Δ
  bot-intro : Coercion Δ

------------------------------------------------------------------------
-- Cast contexts and consistency environments
------------------------------------------------------------------------

data Phase : Set where
  pending active : Phase

data Entry : Set where
  ordinary : C.Var∼ → Entry
  inst-out-bound : Phase → Entry
  inst-in-bound : Phase → Entry

CastCtx : TyCtx → Set
CastCtx Δ = TyVar Δ → Entry

entryMode : Entry → C.Var∼
entryMode (ordinary mode) = mode
entryMode (inst-out-bound phase) = C.X∼★
entryMode (inst-in-bound phase) = C.★∼X

toEnv∼ : CastCtx Δ → C.Env∼ Δ
toEnv∼ κ X = entryMode (κ X)

fromEnv∼ : C.Env∼ Δ → CastCtx Δ
fromEnv∼ μ X = ordinary (μ X)

toEnv∼-fromEnv∼ : ∀ {μ : C.Env∼ Δ}
  → C.Env∼Eq (toEnv∼ (fromEnv∼ μ)) μ
toEnv∼-fromEnv∼ X = refl

ordinaryCtx : ∀ {Δ} → CastCtx Δ
ordinaryCtx = fromEnv∼ C.idᶜ

flipEntry : Entry → Entry
flipEntry (ordinary mode) = ordinary (C.flipVar∼ mode)
flipEntry (inst-out-bound phase) = inst-in-bound phase
flipEntry (inst-in-bound phase) = inst-out-bound phase

flipCtx : CastCtx Δ → CastCtx Δ
flipCtx κ X = flipEntry (κ X)

extCtx : CastCtx Δ → CastCtx (suc Δ)
extCtx κ zero = ordinary C.X∼X
extCtx κ (suc X) = κ X

instCtx : Phase → CastCtx Δ → CastCtx (suc Δ)
instCtx phase κ zero = inst-out-bound phase
instCtx phase κ (suc X) = κ X

genCtx : CastCtx Δ → CastCtx (suc Δ)
genCtx κ zero = ordinary C.★∼X
genCtx κ (suc X) = κ X

toEnv∼-flip : ∀ {κ : CastCtx Δ}
  → C.Env∼Eq (toEnv∼ (flipCtx κ)) (C.flipᵐ (toEnv∼ κ))
toEnv∼-flip {κ = κ} X = entry-flip (κ X)
  where
  entry-flip : ∀ entry
    → entryMode (flipEntry entry) ≡ C.flipVar∼ (entryMode entry)
  entry-flip (ordinary C.X∼X) = refl
  entry-flip (ordinary C.X∼★) = refl
  entry-flip (ordinary C.★∼X) = refl
  entry-flip (ordinary C.★∼X∼★) = refl
  entry-flip (inst-out-bound phase) = refl
  entry-flip (inst-in-bound phase) = refl

toEnv∼-ext : ∀ {κ : CastCtx Δ}
  → C.Env∼Eq (toEnv∼ (extCtx κ)) (C.extᵐ (toEnv∼ κ))
toEnv∼-ext zero = refl
toEnv∼-ext (suc X) = refl

toEnv∼-inst : ∀ phase {κ : CastCtx Δ}
  → C.Env∼Eq (toEnv∼ (instCtx phase κ)) (C.instᵐ (toEnv∼ κ))
toEnv∼-inst phase zero = refl
toEnv∼-inst phase (suc X) = refl

toEnv∼-gen : ∀ {κ : CastCtx Δ}
  → C.Env∼Eq (toEnv∼ (genCtx κ)) (C.genᵐ (toEnv∼ κ))
toEnv∼-gen zero = refl
toEnv∼-gen (suc X) = refl

------------------------------------------------------------------------
-- Leaf-local realization and generic-ground gate
------------------------------------------------------------------------

phaseType : ∀ {Δ} → Phase → TyVar Δ → Ty Δ
phaseType pending X = ＇ X
phaseType active X = ★

data OrdinaryVariable {Δ : TyCtx} (κ : CastCtx Δ)
    (X : TyVar Δ) : Set where
  ordinary-entry : ∀ mode
    → κ X ≡ ordinary mode
    → OrdinaryVariable κ X

data GenericGround {Δ : TyCtx} (κ : CastCtx Δ) : Ty Δ → Set where
  generic-⇒ : GenericGround κ (★ ⇒ ★)
  generic-ι : ∀ {ι} → GenericGround κ (‵ ι)
  generic-X : ∀ {X}
    → OrdinaryVariable κ X
    → GenericGround κ (＇ X)
  generic-∀ : GenericGround κ (`∀ᵗ ★)

generic-ground : ∀ {κ : CastCtx Δ} {G}
  → GenericGround κ G
  → Ground G
generic-ground generic-⇒ = ★⇒★
generic-ground generic-ι = ‵ _
generic-ground (generic-X {X = X} ordinary-X) = ＇ X
generic-ground generic-∀ = ∀★

------------------------------------------------------------------------
-- Context-dependent coercion typing
------------------------------------------------------------------------

infix 4 _⊢_∶_⇒_

data _⊢_∶_⇒_ {Δ : TyCtx} (κ : CastCtx Δ) :
    Coercion Δ → Ty Δ → Ty Δ → Set where

  ⊢id : ∀ {A}
    → Atom A
    → κ ⊢ id ∶ A ⇒ A

  ⊢↦ : ∀ {c d A A′ B B′}
    → flipCtx κ ⊢ c ∶ A′ ⇒ A
    → κ ⊢ d ∶ B ⇒ B′
    → κ ⊢ c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

  ⊢∀ : ∀ {c A B}
    → extCtx κ ⊢ c ∶ A ⇒ B
    → κ ⊢ `∀ c ∶ `∀ᵗ A ⇒ `∀ᵗ B

  ⊢inj : ∀ {c A G}
    → GenericGround κ G
    → C._⊢_∼★ (toEnv∼ κ) G
    → κ ⊢ c ∶ A ⇒ G
    → NonStar A
    → κ ⊢ c ! ∶ A ⇒ ★

  ⊢proj : ∀ {c G B}
    → GenericGround κ G
    → C._⊢★∼_ (toEnv∼ κ) G
    → κ ⊢ c ∶ G ⇒ B
    → NonStar B
    → κ ⊢ ？ c ∶ ★ ⇒ B

  ⊢inst-out-pending : ∀ {X}
    → κ X ≡ inst-out-bound pending
    → κ ⊢ inst-out X ∶ ＇ X ⇒ ★

  ⊢inst-out-active : ∀ {X}
    → κ X ≡ inst-out-bound active
    → κ ⊢ inst-out X ∶ ★ ⇒ ★

  ⊢inst-in-pending : ∀ {X}
    → κ X ≡ inst-in-bound pending
    → κ ⊢ inst-in X ∶ ★ ⇒ ＇ X

  ⊢inst-in-active : ∀ {X}
    → κ X ≡ inst-in-bound active
    → κ ⊢ inst-in X ∶ ★ ⇒ ★

  ⊢inst : ∀ {A B c}
    → NonVar A
    → zero ∈ᵗ A
    → instCtx pending κ ⊢ c ∶ A ⇒ ⇑ᵗ B
    → B ≢ ★
    → κ ⊢ inst c ∶ `∀ᵗ A ⇒ B

  ⊢gen : ∀ {A B c}
    → NonVar B
    → zero ∈ᵗ B
    → genCtx κ ⊢ c ∶ ⇑ᵗ A ⇒ B
    → A ≢ ★
    → κ ⊢ gen c ∶ A ⇒ `∀ᵗ B

  ⊢bot-elim : κ ⊢ bot-elim ∶ `∀ᵗ (＇ zero) ⇒ `∀ᵗ ★

  ⊢bot-intro : κ ⊢ bot-intro ∶ `∀ᵗ ★ ⇒ `∀ᵗ (＇ zero)

------------------------------------------------------------------------
-- Forward correspondence with live consistency
------------------------------------------------------------------------

transport-consistency : ∀ {μ ν : C.Env∼ Δ} {A B}
  → C.Env∼Eq μ ν
  → C._⊢_∼_ μ A B
  → C._⊢_∼_ ν A B
transport-consistency = C.transport-env∼

inst-out-leaf-consistency : ∀ {κ : CastCtx Δ} {X phase}
  → κ X ≡ inst-out-bound phase
  → C._⊢_∼_ (toEnv∼ κ) (phaseType phase X) ★
inst-out-leaf-consistency {X = X} {phase = pending} eq =
  C._! ⦃ Gᵍ = ＇ X ⦄
    ⦃ G∼★ = C.X∼★ᵍ (cong entryMode eq) ⦄
    (C.id (＇ X)) ⦃ Ans = nonstar-X ⦄
inst-out-leaf-consistency {phase = active} eq = C.id ★

inst-in-leaf-consistency : ∀ {κ : CastCtx Δ} {X phase}
  → κ X ≡ inst-in-bound phase
  → C._⊢_∼_ (toEnv∼ κ) ★ (phaseType phase X)
inst-in-leaf-consistency {X = X} {phase = pending} eq =
  C.？_ ⦃ Gᵍ = ＇ X ⦄
    ⦃ ★∼G = C.★∼Xᵍ (cong entryMode eq) ⦄
    (C.id (＇ X)) ⦃ Bns = nonstar-X ⦄
inst-in-leaf-consistency {phase = active} eq = C.id ★

coercion→consistency : ∀ {κ : CastCtx Δ} {c A B}
  → κ ⊢ c ∶ A ⇒ B
  → C._⊢_∼_ (toEnv∼ κ) A B
coercion→consistency (⊢id atom) = C.id atom
coercion→consistency {κ = κ} (⊢↦ c⊢ d⊢) =
  C._↦_
    (transport-consistency (toEnv∼-flip {κ = κ})
      (coercion→consistency c⊢))
    (coercion→consistency d⊢)
coercion→consistency {κ = κ} (⊢∀ c⊢) =
  C.∀ᶜ (transport-consistency (toEnv∼-ext {κ = κ})
    (coercion→consistency c⊢))
coercion→consistency (⊢inj generic G∼★ c⊢ nonstar) =
  C._! ⦃ Gᵍ = generic-ground generic ⦄ ⦃ G∼★ = G∼★ ⦄
    (coercion→consistency c⊢) ⦃ Ans = nonstar ⦄
coercion→consistency (⊢proj generic ★∼G c⊢ nonstar) =
  C.？_ ⦃ Gᵍ = generic-ground generic ⦄ ⦃ ★∼G = ★∼G ⦄
    (coercion→consistency c⊢) ⦃ Bns = nonstar ⦄
coercion→consistency {κ = κ} (⊢inst-out-pending {X = X} eq) =
  inst-out-leaf-consistency {κ = κ} {X = X} {phase = pending} eq
coercion→consistency {κ = κ} (⊢inst-out-active {X = X} eq) =
  inst-out-leaf-consistency {κ = κ} {X = X} {phase = active} eq
coercion→consistency {κ = κ} (⊢inst-in-pending {X = X} eq) =
  inst-in-leaf-consistency {κ = κ} {X = X} {phase = pending} eq
coercion→consistency {κ = κ} (⊢inst-in-active {X = X} eq) =
  inst-in-leaf-consistency {κ = κ} {X = X} {phase = active} eq
coercion→consistency {κ = κ}
    (⊢inst nonvar occurs c⊢ B≢★) =
  C.inst_ ⦃ Anv = nonvar ⦄ ⦃ z∈A = occurs ⦄
    (transport-consistency (toEnv∼-inst pending {κ = κ})
      (coercion→consistency c⊢)) B≢★
coercion→consistency {κ = κ}
    (⊢gen nonvar occurs c⊢ A≢★) =
  C.gen_ ⦃ Bnv = nonvar ⦄ ⦃ z∈B = occurs ⦄
    (transport-consistency (toEnv∼-gen {κ = κ})
      (coercion→consistency c⊢)) A≢★
coercion→consistency ⊢bot-elim = C.bot-elim
coercion→consistency ⊢bot-intro = C.bot-intro

------------------------------------------------------------------------
-- Reverse correspondence for pending contexts
------------------------------------------------------------------------

data PendingEntry {Δ : TyCtx} (κ : CastCtx Δ)
    (X : TyVar Δ) : Set where
  pending-ordinary : ∀ mode
    → κ X ≡ ordinary mode
    → PendingEntry κ X
  pending-out :
      κ X ≡ inst-out-bound pending
    → PendingEntry κ X
  pending-in :
      κ X ≡ inst-in-bound pending
    → PendingEntry κ X

PendingCtx : ∀ {Δ} → CastCtx Δ → Set
PendingCtx κ = ∀ X → PendingEntry κ X

fromEnv∼-pending : ∀ {μ : C.Env∼ Δ}
  → PendingCtx (fromEnv∼ μ)
fromEnv∼-pending X = pending-ordinary _ refl

flip-pending : ∀ {κ : CastCtx Δ}
  → PendingCtx κ
  → PendingCtx (flipCtx κ)
flip-pending pendingκ X with pendingκ X
flip-pending pendingκ X | pending-ordinary mode eq =
  pending-ordinary (C.flipVar∼ mode) (cong flipEntry eq)
flip-pending pendingκ X | pending-out eq =
  pending-in (cong flipEntry eq)
flip-pending pendingκ X | pending-in eq =
  pending-out (cong flipEntry eq)

ext-pending : ∀ {κ : CastCtx Δ}
  → PendingCtx κ
  → PendingCtx (extCtx κ)
ext-pending pendingκ zero = pending-ordinary C.X∼X refl
ext-pending pendingκ (suc X) with pendingκ X
ext-pending pendingκ (suc X) | pending-ordinary mode eq =
  pending-ordinary mode eq
ext-pending pendingκ (suc X) | pending-out eq = pending-out eq
ext-pending pendingκ (suc X) | pending-in eq = pending-in eq

inst-pending : ∀ {κ : CastCtx Δ}
  → PendingCtx κ
  → PendingCtx (instCtx pending κ)
inst-pending pendingκ zero = pending-out refl
inst-pending pendingκ (suc X) with pendingκ X
inst-pending pendingκ (suc X) | pending-ordinary mode eq =
  pending-ordinary mode eq
inst-pending pendingκ (suc X) | pending-out eq = pending-out eq
inst-pending pendingκ (suc X) | pending-in eq = pending-in eq

gen-pending : ∀ {κ : CastCtx Δ}
  → PendingCtx κ
  → PendingCtx (genCtx κ)
gen-pending pendingκ zero = pending-ordinary C.★∼X refl
gen-pending pendingκ (suc X) with pendingκ X
gen-pending pendingκ (suc X) | pending-ordinary mode eq =
  pending-ordinary mode eq
gen-pending pendingκ (suc X) | pending-out eq = pending-out eq
gen-pending pendingκ (suc X) | pending-in eq = pending-in eq

data ToStarView {Δ : TyCtx} (κ : CastCtx Δ)
    (X : TyVar Δ) : Set where
  ordinary-to-star :
      OrdinaryVariable κ X
    → ToStarView κ X
  bound-to-star :
      κ X ≡ inst-out-bound pending
    → ToStarView κ X

to-star-view : ∀ {κ : CastCtx Δ} {X}
  → PendingCtx κ
  → toEnv∼ κ X ≡ C.X∼★
  → ToStarView κ X
to-star-view {X = X} pendingκ mode with pendingκ X
to-star-view pendingκ mode | pending-ordinary entry eq =
  ordinary-to-star (ordinary-entry entry eq)
to-star-view pendingκ mode | pending-out eq = bound-to-star eq
to-star-view pendingκ mode | pending-in eq
    with trans (sym (cong entryMode eq)) mode
to-star-view pendingκ mode | pending-in eq | ()

data FromStarView {Δ : TyCtx} (κ : CastCtx Δ)
    (X : TyVar Δ) : Set where
  ordinary-from-star :
      OrdinaryVariable κ X
    → FromStarView κ X
  bound-from-star :
      κ X ≡ inst-in-bound pending
    → FromStarView κ X

from-star-view : ∀ {κ : CastCtx Δ} {X}
  → PendingCtx κ
  → toEnv∼ κ X ≡ C.★∼X
  → FromStarView κ X
from-star-view {X = X} pendingκ mode with pendingκ X
from-star-view pendingκ mode | pending-ordinary entry eq =
  ordinary-from-star (ordinary-entry entry eq)
from-star-view pendingκ mode | pending-out eq
    with trans (sym (cong entryMode eq)) mode
from-star-view pendingκ mode | pending-out eq | ()
from-star-view pendingκ mode | pending-in eq = bound-from-star eq

cross-to-star-ordinary : ∀ {κ : CastCtx Δ} {X}
  → PendingCtx κ
  → toEnv∼ κ X ≡ C.★∼X∼★
  → OrdinaryVariable κ X
cross-to-star-ordinary {X = X} pendingκ mode with pendingκ X
cross-to-star-ordinary pendingκ mode | pending-ordinary entry eq =
  ordinary-entry entry eq
cross-to-star-ordinary pendingκ mode | pending-out eq
    with trans (sym (cong entryMode eq)) mode
cross-to-star-ordinary pendingκ mode | pending-out eq | ()
cross-to-star-ordinary pendingκ mode | pending-in eq
    with trans (sym (cong entryMode eq)) mode
cross-to-star-ordinary pendingκ mode | pending-in eq | ()

cross-from-star-ordinary : ∀ {κ : CastCtx Δ} {X}
  → PendingCtx κ
  → toEnv∼ κ X ≡ C.★∼X∼★
  → OrdinaryVariable κ X
cross-from-star-ordinary = cross-to-star-ordinary

target-variable-shape : ∀ {μ : C.Env∼ Δ} {A X}
  → C._⊢_∼_ μ A (＇ X)
  → (A ≡ ＇ X) ⊎ (A ≡ ★)
target-variable-shape (C.id (＇ X)) = inj₁ refl
target-variable-shape (C.？_ c) = inj₂ refl
target-variable-shape
    (C.inst_ ⦃ Anv = nonvar ⦄ ⦃ z∈A = occurs ⦄ c B≢★)
    with target-variable-shape c
target-variable-shape
    (C.inst_ ⦃ Anv = () ⦄ ⦃ z∈A = occurs ⦄ c B≢★)
    | inj₁ refl
target-variable-shape
    (C.inst_ ⦃ Anv = nonvar ⦄ ⦃ z∈A = () ⦄ c B≢★)
    | inj₂ refl

source-variable-shape : ∀ {μ : C.Env∼ Δ} {B X}
  → C._⊢_∼_ μ (＇ X) B
  → (B ≡ ＇ X) ⊎ (B ≡ ★)
source-variable-shape c = target-variable-shape (C.sym∼ c)

nonstar-not-star : ∀ {A : Ty Δ}
  → NonStar A
  → A ≡ ★
  → ⊥
nonstar-not-star nonstar refl = nonStar≢★ nonstar refl

bound-injection-source : ∀ {μ : C.Env∼ Δ} {A X}
  → C._⊢_∼_ μ A (＇ X)
  → NonStar A
  → A ≡ ＇ X
bound-injection-source c nonstar with target-variable-shape c
bound-injection-source c nonstar | inj₁ eq = eq
bound-injection-source c nonstar | inj₂ eq =
  ⊥-elim (nonstar-not-star nonstar eq)

bound-projection-target : ∀ {μ : C.Env∼ Δ} {B X}
  → C._⊢_∼_ μ (＇ X) B
  → NonStar B
  → B ≡ ＇ X
bound-projection-target c nonstar with source-variable-shape c
bound-projection-target c nonstar | inj₁ eq = eq
bound-projection-target c nonstar | inj₂ eq =
  ⊥-elim (nonstar-not-star nonstar eq)

transport-coercion-typing : ∀ {κ : CastCtx Δ} {c A B A′ B′}
  → A ≡ A′
  → B ≡ B′
  → κ ⊢ c ∶ A ⇒ B
  → κ ⊢ c ∶ A′ ⇒ B′
transport-coercion-typing refl refl c⊢ = c⊢

EnvAgrees : ∀ {Δ} → C.Env∼ Δ → CastCtx Δ → Set
EnvAgrees μ κ = ∀ X → μ X ≡ toEnv∼ κ X

flip-agrees : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ}
  → EnvAgrees μ κ
  → EnvAgrees (C.flipᵐ μ) (flipCtx κ)
flip-agrees {κ = κ} agrees X =
  trans (cong C.flipVar∼ (agrees X))
    (sym (toEnv∼-flip {κ = κ} X))

ext-agrees : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ}
  → EnvAgrees μ κ
  → EnvAgrees (C.extᵐ μ) (extCtx κ)
ext-agrees agrees zero = refl
ext-agrees agrees (suc X) = agrees X

inst-agrees : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ}
  → EnvAgrees μ κ
  → EnvAgrees (C.instᵐ μ) (instCtx pending κ)
inst-agrees agrees zero = refl
inst-agrees agrees (suc X) = agrees X

gen-agrees : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ}
  → EnvAgrees μ κ
  → EnvAgrees (C.genᵐ μ) (genCtx κ)
gen-agrees agrees zero = refl
gen-agrees agrees (suc X) = agrees X

transport-∼★ : ∀ {μ ν : C.Env∼ Δ} {G}
  → C.Env∼Eq μ ν
  → C._⊢_∼★ μ G
  → C._⊢_∼★ ν G
transport-∼★ = C.transport-∼★

transport-★∼ : ∀ {μ ν : C.Env∼ Δ} {G}
  → C.Env∼Eq μ ν
  → C._⊢★∼_ μ G
  → C._⊢★∼_ ν G
transport-★∼ = C.transport-★∼

aligned-mode : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ} {X mode}
  → EnvAgrees μ κ
  → μ X ≡ mode
  → toEnv∼ κ X ≡ mode
aligned-mode {X = X} agrees mode = trans (sym (agrees X)) mode

aligned-∼★ : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ} {G}
  → EnvAgrees μ κ
  → C._⊢_∼★ μ G
  → C._⊢_∼★ (toEnv∼ κ) G
aligned-∼★ {κ = κ} agrees = transport-∼★ agrees

aligned-★∼ : ∀ {μ : C.Env∼ Δ} {κ : CastCtx Δ} {G}
  → EnvAgrees μ κ
  → C._⊢★∼_ μ G
  → C._⊢★∼_ (toEnv∼ κ) G
aligned-★∼ {κ = κ} agrees = transport-★∼ agrees

consistency→coercion-with : ∀ {μ : C.Env∼ Δ}
    {κ : CastCtx Δ} {A B}
  → EnvAgrees μ κ
  → PendingCtx κ
  → C._⊢_∼_ μ A B
  → Σ[ c ∈ Coercion Δ ] (κ ⊢ c ∶ A ⇒ B)
consistency→coercion-with agrees pendingκ (C.id atom) =
  id , ⊢id atom
consistency→coercion-with {κ = κ} agrees pendingκ (c C.↦ d)
    with consistency→coercion-with (flip-agrees {κ = κ} agrees)
      (flip-pending pendingκ) c
       | consistency→coercion-with agrees pendingκ d
consistency→coercion-with agrees pendingκ (c C.↦ d)
    | c′ , c′⊢ | d′ , d′⊢ =
  c′ ↦ d′ , ⊢↦ c′⊢ d′⊢
consistency→coercion-with agrees pendingκ (C.∀ᶜ c)
    with consistency→coercion-with (ext-agrees agrees)
      (ext-pending pendingκ) c
consistency→coercion-with agrees pendingκ (C.∀ᶜ c) | c′ , c′⊢ =
  `∀ c′ , ⊢∀ c′⊢
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.⇒∼★ ⦄ c ⦃ Ans = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.⇒∼★ ⦄ c ⦃ Ans = nonstar ⦄)
    | c′ , c′⊢ =
  c′ ! , ⊢inj generic-⇒
    (aligned-∼★ {κ = κ} agrees C.⇒∼★) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.ι∼★ ⦄ c ⦃ Ans = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.ι∼★ ⦄ c ⦃ Ans = nonstar ⦄)
    | c′ , c′⊢ =
  c′ ! , ⊢inj generic-ι
    (aligned-∼★ {κ = κ} agrees C.ι∼★) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.X∼★ᵍ {X = X} mode ⦄ c
      ⦃ Ans = nonstar ⦄)
    with to-star-view pendingκ (aligned-mode {κ = κ} agrees mode)
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.X∼★ᵍ mode ⦄ c ⦃ Ans = nonstar ⦄)
    | ordinary-to-star ordinary-X
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.X∼★ᵍ mode ⦄ c ⦃ Ans = nonstar ⦄)
    | ordinary-to-star ordinary-X | c′ , c′⊢ =
  c′ ! , ⊢inj (generic-X ordinary-X)
    (C.X∼★ᵍ (aligned-mode {κ = κ} agrees mode)) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.X∼★ᵍ {X = X} mode ⦄ c
      ⦃ Ans = nonstar ⦄)
    | bound-to-star bound-X =
  inst-out X ,
    transport-coercion-typing (sym source-eq) refl
      (⊢inst-out-pending bound-X)
  where
  source-eq = bound-injection-source c nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.X∼★ᶜ {X = X} mode ⦄ c
      ⦃ Ans = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.X∼★ᶜ {X = X} mode ⦄ c
      ⦃ Ans = nonstar ⦄)
    | c′ , c′⊢ =
  c′ ! , ⊢inj
    (generic-X
      (cross-to-star-ordinary pendingκ (aligned-mode {κ = κ} agrees mode)))
    (C.X∼★ᶜ (aligned-mode {κ = κ} agrees mode)) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.∀∼★ ⦄ c ⦃ Ans = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C._! ⦃ G∼★ = C.∀∼★ ⦄ c ⦃ Ans = nonstar ⦄)
    | c′ , c′⊢ =
  c′ ! , ⊢inj generic-∀
    (aligned-∼★ {κ = κ} agrees C.∀∼★) c′⊢ nonstar

consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼⇒ ⦄ c ⦃ Bns = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼⇒ ⦄ c ⦃ Bns = nonstar ⦄)
    | c′ , c′⊢ =
  ？ c′ , ⊢proj generic-⇒
    (aligned-★∼ {κ = κ} agrees C.★∼⇒) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼ι ⦄ c ⦃ Bns = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼ι ⦄ c ⦃ Bns = nonstar ⦄)
    | c′ , c′⊢ =
  ？ c′ , ⊢proj generic-ι
    (aligned-★∼ {κ = κ} agrees C.★∼ι) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼Xᵍ {X = X} mode ⦄ c
      ⦃ Bns = nonstar ⦄)
    with from-star-view pendingκ (aligned-mode {κ = κ} agrees mode)
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼Xᵍ mode ⦄ c ⦃ Bns = nonstar ⦄)
    | ordinary-from-star ordinary-X
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼Xᵍ mode ⦄ c ⦃ Bns = nonstar ⦄)
    | ordinary-from-star ordinary-X | c′ , c′⊢ =
  ？ c′ , ⊢proj (generic-X ordinary-X)
    (C.★∼Xᵍ (aligned-mode {κ = κ} agrees mode)) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼Xᵍ {X = X} mode ⦄ c
      ⦃ Bns = nonstar ⦄)
    | bound-from-star bound-X =
  inst-in X ,
    transport-coercion-typing refl (sym target-eq)
      (⊢inst-in-pending bound-X)
  where
  target-eq = bound-projection-target c nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼Xᶜ {X = X} mode ⦄ c
      ⦃ Bns = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼Xᶜ {X = X} mode ⦄ c
      ⦃ Bns = nonstar ⦄)
    | c′ , c′⊢ =
  ？ c′ , ⊢proj
    (generic-X
      (cross-from-star-ordinary pendingκ (aligned-mode {κ = κ} agrees mode)))
    (C.★∼Xᶜ (aligned-mode {κ = κ} agrees mode)) c′⊢ nonstar
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼∀ ⦄ c ⦃ Bns = nonstar ⦄)
    with consistency→coercion-with agrees pendingκ c
consistency→coercion-with {κ = κ} agrees pendingκ
    (C.？_ ⦃ ★∼G = C.★∼∀ ⦄ c ⦃ Bns = nonstar ⦄)
    | c′ , c′⊢ =
  ？ c′ , ⊢proj generic-∀
    (aligned-★∼ {κ = κ} agrees C.★∼∀) c′⊢ nonstar
consistency→coercion-with agrees pendingκ
    (C.inst_ ⦃ Anv = nonvar ⦄ ⦃ z∈A = occurs ⦄ c B≠★)
    with consistency→coercion-with (inst-agrees agrees)
      (inst-pending pendingκ) c
consistency→coercion-with agrees pendingκ
    (C.inst_ ⦃ Anv = nonvar ⦄ ⦃ z∈A = occurs ⦄ c B≠★)
    | c′ , c′⊢ =
  inst c′ , ⊢inst nonvar occurs c′⊢ B≠★
consistency→coercion-with agrees pendingκ
    (C.gen_ ⦃ Bnv = nonvar ⦄ ⦃ z∈B = occurs ⦄ c A≠★)
    with consistency→coercion-with (gen-agrees agrees)
      (gen-pending pendingκ) c
consistency→coercion-with agrees pendingκ
    (C.gen_ ⦃ Bnv = nonvar ⦄ ⦃ z∈B = occurs ⦄ c A≠★)
    | c′ , c′⊢ =
  gen c′ , ⊢gen nonvar occurs c′⊢ A≠★
consistency→coercion-with agrees pendingκ C.bot-elim =
  bot-elim , ⊢bot-elim
consistency→coercion-with agrees pendingκ C.bot-intro =
  bot-intro , ⊢bot-intro

consistency→coercion : ∀ {κ : CastCtx Δ} {A B}
  → PendingCtx κ
  → C._⊢_∼_ (toEnv∼ κ) A B
  → Σ[ c ∈ Coercion Δ ] (κ ⊢ c ∶ A ⇒ B)
consistency→coercion pendingκ c =
  consistency→coercion-with (λ X → refl) pendingκ c

consistency→fromEnv∼-coercion : ∀ {μ : C.Env∼ Δ} {A B}
  → C._⊢_∼_ μ A B
  → Σ[ c ∈ Coercion Δ ] (fromEnv∼ μ ⊢ c ∶ A ⇒ B)
consistency→fromEnv∼-coercion c =
  consistency→coercion-with (λ X → refl) fromEnv∼-pending c

fromEnv∼-coercion→consistency : ∀ {μ : C.Env∼ Δ} {c A B}
  → fromEnv∼ μ ⊢ c ∶ A ⇒ B
  → C._⊢_∼_ μ A B
fromEnv∼-coercion→consistency c⊢ =
  transport-consistency toEnv∼-fromEnv∼
    (coercion→consistency c⊢)

------------------------------------------------------------------------
-- Focused identity-function experiment
------------------------------------------------------------------------

X : Ty 1
X = ＇ zero

X⇒X : Ty 1
X⇒X = X ⇒ X

Dyn⇒Dyn : Ty 1
Dyn⇒Dyn = ★ ⇒ ★

identity-body-coercion : Coercion 1
identity-body-coercion = inst-in zero ↦ inst-out zero

pending0 : CastCtx 1
pending0 = instCtx pending (ordinaryCtx {Δ = 0})

active0 : CastCtx 1
active0 = instCtx active (ordinaryCtx {Δ = 0})

zero-pending-out : pending0 zero ≡ inst-out-bound pending
zero-pending-out = refl

zero-pending-in :
  flipCtx pending0 zero ≡ inst-in-bound pending
zero-pending-in = refl

identity-body-pending :
  pending0 ⊢ identity-body-coercion ∶ X⇒X ⇒ Dyn⇒Dyn
identity-body-pending =
  ⊢↦ (⊢inst-in-pending zero-pending-in)
    (⊢inst-out-pending zero-pending-out)

zero-active-out : active0 zero ≡ inst-out-bound active
zero-active-out = refl

zero-active-in : flipCtx active0 zero ≡ inst-in-bound active
zero-active-in = refl

identity-body-active :
  active0 ⊢ identity-body-coercion ∶ Dyn⇒Dyn ⇒ Dyn⇒Dyn
identity-body-active =
  ⊢↦ (⊢inst-in-active zero-active-in)
    (⊢inst-out-active zero-active-out)

identity-body-consistency :
  C._⊢_∼_ (C.instᵐ (C.idᶜ {Δ = 0})) X⇒X Dyn⇒Dyn
identity-body-consistency =
  transport-consistency (toEnv∼-inst pending)
    (coercion→consistency identity-body-pending)

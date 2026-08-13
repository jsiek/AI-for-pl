module SplitPf where

-- File Charter:
--   Notes preflight scratch for the source-consistency crossable/strict
--   split.  This file models the four-valued variable mode relation, checks
--   the five calibration judgments from SRCCONSIST-DOSSIER.md section 9, and
--   records the proof-shape obligations for ground-cast-target, CrossFree,
--   totality, and substitution environments.  It intentionally imports only
--   the shared type syntax, not the live GTSFImp consistency relation.
--   Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--   -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--   GTSFImp/proof/DGG/notes/SplitPf.agda`.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Nat as Nat
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

open import Types

private
  variable
    Δ Δ′ : TyCtx
    A A′ B B′ C G : Ty Δ

infix 4 _⊢_∼★₅ _⊢★∼₅_ _⊢_∼₅_ _⊢_⊑₅_
infixr 7 _↦₅_ _⇒ᵢ₅_

------------------------------------------------------------------------
-- Four-valued source-consistency modes
------------------------------------------------------------------------

data Var∼₅ : Set where
  ★∼X∼★ : Var∼₅
  X∼X : Var∼₅
  X∼★ : Var∼₅
  ★∼X : Var∼₅

flipVar∼₅ : Var∼₅ → Var∼₅
flipVar∼₅ ★∼X∼★ = ★∼X∼★
flipVar∼₅ X∼X = X∼X
flipVar∼₅ X∼★ = ★∼X
flipVar∼₅ ★∼X = X∼★

flip-cross₅ : flipVar∼₅ ★∼X∼★ ≡ ★∼X∼★
flip-cross₅ = refl

flip-strict₅ : flipVar∼₅ X∼X ≡ X∼X
flip-strict₅ = refl

flipVar∼-involutive₅ : ∀ v → flipVar∼₅ (flipVar∼₅ v) ≡ v
flipVar∼-involutive₅ ★∼X∼★ = refl
flipVar∼-involutive₅ X∼X = refl
flipVar∼-involutive₅ X∼★ = refl
flipVar∼-involutive₅ ★∼X = refl

X∼X≢X∼★₅ : X∼X ≢ X∼★
X∼X≢X∼★₅ ()

X∼X≢★∼X₅ : X∼X ≢ ★∼X
X∼X≢★∼X₅ ()

X∼X≢★∼X∼★₅ : X∼X ≢ ★∼X∼★
X∼X≢★∼X∼★₅ ()

Env∼₅ : TyCtx → Set
Env∼₅ Δ = TyVar Δ → Var∼₅

idᶜ₅ : ∀ {Δ} → Env∼₅ Δ
idᶜ₅ X = ★∼X∼★

extᵐ₅ : Env∼₅ Δ → Env∼₅ (Nat.suc Δ)
extᵐ₅ μ zero = X∼X
extᵐ₅ μ (suc X) = μ X

instᵐ₅ : Env∼₅ Δ → Env∼₅ (Nat.suc Δ)
instᵐ₅ μ zero = X∼★
instᵐ₅ μ (suc X) = μ X

genᵐ₅ : Env∼₅ Δ → Env∼₅ (Nat.suc Δ)
genᵐ₅ μ zero = ★∼X
genᵐ₅ μ (suc X) = μ X

flipᵐ₅ : Env∼₅ Δ → Env∼₅ Δ
flipᵐ₅ μ X = flipVar∼₅ (μ X)

------------------------------------------------------------------------
-- Star gates: dynamic gates plus crossable gates, but no strict gates
------------------------------------------------------------------------

data _⊢_∼★₅ {Δ : TyCtx} (μ : Env∼₅ Δ) : Ty Δ → Set where
  ⇒∼★₅ : μ ⊢ (★ ⇒ ★) ∼★₅
  ι∼★₅ : ∀ {ι} → μ ⊢ ‵ ι ∼★₅
  X∼★ᵍ₅ : ∀ {X}
    → μ X ≡ X∼★
    → μ ⊢ ＇ X ∼★₅
  X∼★ᶜ₅ : ∀ {X}
    → μ X ≡ ★∼X∼★
    → μ ⊢ ＇ X ∼★₅
  ∀∼★₅ : μ ⊢ (`∀ ★) ∼★₅

data _⊢★∼₅_ {Δ : TyCtx} (μ : Env∼₅ Δ) : Ty Δ → Set where
  ★∼⇒₅ : μ ⊢★∼₅ (★ ⇒ ★)
  ★∼ι₅ : ∀ {ι} → μ ⊢★∼₅ ‵ ι
  ★∼Xᵍ₅ : ∀ {X}
    → μ X ≡ ★∼X
    → μ ⊢★∼₅ ＇ X
  ★∼Xᶜ₅ : ∀ {X}
    → μ X ≡ ★∼X∼★
    → μ ⊢★∼₅ ＇ X
  ★∼∀₅ : μ ⊢★∼₅ (`∀ ★)

no-strict-to-star-gate₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → ¬ (extᵐ₅ μ ⊢ ＇ zero ∼★₅)
no-strict-to-star-gate₅ (X∼★ᵍ₅ ())
no-strict-to-star-gate₅ (X∼★ᶜ₅ ())

no-strict-from-star-gate₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → ¬ (extᵐ₅ μ ⊢★∼₅ ＇ zero)
no-strict-from-star-gate₅ (★∼Xᵍ₅ ())
no-strict-from-star-gate₅ (★∼Xᶜ₅ ())

strict-mode-no-to-star-gate₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X}
  → μ X ≡ X∼X
  → μ ⊢ ＇ X ∼★₅
  → ⊥
strict-mode-no-to-star-gate₅ same (X∼★ᵍ₅ eq) =
  X∼X≢X∼★₅ (trans (sym same) eq)
strict-mode-no-to-star-gate₅ same (X∼★ᶜ₅ eq) =
  X∼X≢★∼X∼★₅ (trans (sym same) eq)

strict-mode-no-from-star-gate₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X}
  → μ X ≡ X∼X
  → μ ⊢★∼₅ ＇ X
  → ⊥
strict-mode-no-from-star-gate₅ same (★∼Xᵍ₅ eq) =
  X∼X≢★∼X₅ (trans (sym same) eq)
strict-mode-no-from-star-gate₅ same (★∼Xᶜ₅ eq) =
  X∼X≢★∼X∼★₅ (trans (sym same) eq)

------------------------------------------------------------------------
-- Consistency model
------------------------------------------------------------------------

data _⊢_∼₅_ {Δ : TyCtx} (μ : Env∼₅ Δ) :
    Ty Δ → Ty Δ → Set where

  id₅ : ∀ {A}
    → Atom A
    → μ ⊢ A ∼₅ A

  _↦₅_ : ∀ {A A′ B B′}
    → flipᵐ₅ μ ⊢ A′ ∼₅ A
    → μ ⊢ B ∼₅ B′
    → μ ⊢ (A ⇒ B) ∼₅ (A′ ⇒ B′)

  ∀ᶜ₅_ : ∀ {A B}
    → extᵐ₅ μ ⊢ A ∼₅ B
    → μ ⊢ (`∀ A) ∼₅ (`∀ B)

  tag₅ : ∀ {A G}
    → Ground G
    → μ ⊢ G ∼★₅
    → μ ⊢ A ∼₅ G
    → NonStar A
    → μ ⊢ A ∼₅ ★

  proj₅ : ∀ {G B}
    → Ground G
    → μ ⊢★∼₅ G
    → μ ⊢ G ∼₅ B
    → NonStar B
    → μ ⊢ ★ ∼₅ B

  inst₅ : ∀ {A B}
    → NonVar A
    → zero ∈ᵗ A
    → instᵐ₅ μ ⊢ A ∼₅ ⇑ᵗ B
    → B ≢ ★
    → μ ⊢ (`∀ A) ∼₅ B

  gen₅ : ∀ {A B}
    → NonVar B
    → zero ∈ᵗ B
    → genᵐ₅ μ ⊢ ⇑ᵗ A ∼₅ B
    → A ≢ ★
    → μ ⊢ A ∼₅ (`∀ B)

  bot-elim₅ :
    μ ⊢ (`∀ (＇ zero)) ∼₅ (`∀ ★)

  bot-intro₅ :
    μ ⊢ (`∀ ★) ∼₅ (`∀ (＇ zero))

refl∼₅ : ∀ {Δ} {μ : Env∼₅ Δ} (A : Ty Δ) → μ ⊢ A ∼₅ A
refl∼₅ (＇ X) = id₅ (＇ X)
refl∼₅ (‵ ι) = id₅ (‵ ι)
refl∼₅ ★ = id₅ ★
refl∼₅ (A ⇒ B) = refl∼₅ A ↦₅ refl∼₅ B
refl∼₅ (`∀ A) = ∀ᶜ₅ refl∼₅ A

var-to-star-dyn₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X : TyVar Δ}
  → μ X ≡ X∼★
  → μ ⊢ ＇ X ∼₅ ★
var-to-star-dyn₅ eq = tag₅ (＇ _) (X∼★ᵍ₅ eq) (id₅ (＇ _)) nonstar-X

star-to-var-dyn₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X
  → μ ⊢ ★ ∼₅ ＇ X
star-to-var-dyn₅ eq = proj₅ (＇ _) (★∼Xᵍ₅ eq) (id₅ (＇ _)) nonstar-X

var-to-star-cross₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X∼★
  → μ ⊢ ＇ X ∼₅ ★
var-to-star-cross₅ eq =
  tag₅ (＇ _) (X∼★ᶜ₅ eq) (id₅ (＇ _)) nonstar-X

star-to-var-cross₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X∼★
  → μ ⊢ ★ ∼₅ ＇ X
star-to-var-cross₅ eq =
  proj₅ (＇ _) (★∼Xᶜ₅ eq) (id₅ (＇ _)) nonstar-X

strict-mode-var-not-to-star₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X}
  → μ X ≡ X∼X
  → ¬ (μ ⊢ ＇ X ∼₅ ★)
strict-mode-var-not-to-star₅ same
    (tag₅ (＇ _) G∼★ (id₅ (＇ _)) nonstar-X) =
  strict-mode-no-to-star-gate₅ same G∼★
strict-mode-var-not-to-star₅ same
    (tag₅ ∀★ ∀∼★₅ (gen₅ nonvar-star () c A≢★) nonstar-X)

strict-var-not-to-star₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → ¬ (extᵐ₅ μ ⊢ ＇ zero ∼₅ ★)
strict-var-not-to-star₅ = strict-mode-var-not-to-star₅ refl

strict-mode-var-not-from-star₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X}
  → μ X ≡ X∼X
  → ¬ (μ ⊢ ★ ∼₅ ＇ X)
strict-mode-var-not-from-star₅ same
    (proj₅ (＇ _) ★∼G (id₅ (＇ _)) nonstar-X) =
  strict-mode-no-from-star-gate₅ same ★∼G
strict-mode-var-not-from-star₅ same
    (proj₅ ∀★ ★∼∀₅ (inst₅ nonvar-star () c B≢★) nonstar-X)

strict-var-not-from-star₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → ¬ (extᵐ₅ μ ⊢ ★ ∼₅ ＇ zero)
strict-var-not-from-star₅ = strict-mode-var-not-from-star₅ refl

no-zero∼suc-zero₅ : ∀ {Δ} {μ : Env∼₅ (Nat.suc (Nat.suc Δ))}
  → ¬ (μ ⊢ ＇ zero ∼₅ ＇ (suc zero))
no-zero∼suc-zero₅ ()

no-suc-zero∼zero₅ : ∀ {Δ} {μ : Env∼₅ (Nat.suc (Nat.suc Δ))}
  → ¬ (μ ⊢ ＇ (suc zero) ∼₅ ＇ zero)
no-suc-zero∼zero₅ ()

------------------------------------------------------------------------
-- The five calibration judgments from dossier section 9
------------------------------------------------------------------------

X⇒X₅ : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒X₅ = ＇ zero ⇒ ＇ zero

X⇒★₅ : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒★₅ = ＇ zero ⇒ ★

∀X⇒X₅ : Ty 0
∀X⇒X₅ = `∀ X⇒X₅

∀X⇒★₅ : Ty 0
∀X⇒★₅ = `∀ X⇒★₅

calibration-1₅ : idᶜ₅ {Δ = 1} ⊢ ＇ zero ∼₅ ★
calibration-1₅ = var-to-star-cross₅ refl

calibration-3₅ : idᶜ₅ {Δ = 0} ⊢ ∀X⇒X₅ ∼₅ (★ ⇒ ★)
calibration-3₅ =
  inst₅ nonvar-fun (∈-fun-left var-∈)
    (star-to-var-dyn₅ refl ↦₅ var-to-star-dyn₅ refl)
    (λ ())

left4-body₅ : Ty 1
left4-body₅ = ★ ⇒ (＇ zero ⇒ ★)

right4-body₅ : Ty 1
right4-body₅ = ＇ zero ⇒ (★ ⇒ ＇ zero)

calibration-4-body₅ :
  genᵐ₅ (instᵐ₅ (idᶜ₅ {Δ = 0}))
    ⊢ (★ ⇒ (＇ (suc zero) ⇒ ★))
    ∼₅ (＇ zero ⇒ (★ ⇒ ＇ zero))
calibration-4-body₅ =
  var-to-star-dyn₅ refl ↦₅
    (star-to-var-dyn₅ refl ↦₅ star-to-var-dyn₅ refl)

calibration-4-gen₅ :
  instᵐ₅ (idᶜ₅ {Δ = 0}) ⊢ left4-body₅ ∼₅ ⇑ᵗ (`∀ right4-body₅)
calibration-4-gen₅ =
  gen₅ nonvar-fun (∈-fun-left var-∈) calibration-4-body₅ (λ ())

calibration-4₅ :
  idᶜ₅ {Δ = 0}
    ⊢ (`∀ left4-body₅) ∼₅ (`∀ right4-body₅)
calibration-4₅ =
  inst₅ nonvar-fun (∈-fun-right ∉-star (∈-fun-left var-∈))
    calibration-4-gen₅
    (λ ())

left5-body₅ : Ty 2
left5-body₅ = ＇ (suc zero) ⇒ ＇ zero

right5-body₅ : Ty 2
right5-body₅ = ★ ⇒ ＇ zero

calibration-5₅ :
  idᶜ₅ {Δ = 1}
    ⊢ (`∀ left5-body₅) ∼₅ (`∀ right5-body₅)
calibration-5₅ =
  ∀ᶜ₅ (star-to-var-cross₅ refl ↦₅ id₅ (＇ zero))

calibration-2-strict-route₅ :
  ¬ (extᵐ₅ (idᶜ₅ {Δ = 0}) ⊢ X⇒X₅ ∼₅ X⇒★₅)
calibration-2-strict-route₅ (dom ↦₅ cod) =
  strict-var-not-to-star₅ cod

calibration-2-inst-inner₅ :
  ¬ (genᵐ₅ (instᵐ₅ (idᶜ₅ {Δ = 0}))
       ⊢ (＇ (suc zero) ⇒ ＇ (suc zero))
       ∼₅ (＇ zero ⇒ ★))
calibration-2-inst-inner₅ (dom ↦₅ cod) = no-zero∼suc-zero₅ dom

calibration-2-inst-route₅ :
  ¬ (instᵐ₅ (idᶜ₅ {Δ = 0}) ⊢ X⇒X₅ ∼₅ ⇑ᵗ ∀X⇒★₅)
calibration-2-inst-route₅
    (gen₅ nonvar-fun (∈-fun-left var-∈) c A≢★) =
  calibration-2-inst-inner₅ c

calibration-2-gen-inner₅ :
  ¬ (instᵐ₅ (genᵐ₅ (idᶜ₅ {Δ = 0}))
       ⊢ (＇ zero ⇒ ＇ zero)
       ∼₅ (＇ (suc zero) ⇒ ★))
calibration-2-gen-inner₅ (dom ↦₅ cod) = no-suc-zero∼zero₅ dom

calibration-2-gen-route₅ :
  ¬ (genᵐ₅ (idᶜ₅ {Δ = 0}) ⊢ ⇑ᵗ ∀X⇒X₅ ∼₅ X⇒★₅)
calibration-2-gen-route₅
    (inst₅ nonvar-fun (∈-fun-left var-∈) c B≢★) =
  calibration-2-gen-inner₅ c
calibration-2-gen-route₅
    (inst₅ nonvar-fun (∈-fun-right ∉-var≢ c∈) c B≢★) =
  calibration-2-gen-inner₅ c

calibration-2₅ :
  ¬ (idᶜ₅ {Δ = 0} ⊢ ∀X⇒X₅ ∼₅ ∀X⇒★₅)
calibration-2₅ (∀ᶜ₅ c) = calibration-2-strict-route₅ c
calibration-2₅
    (inst₅ nonvar-fun (∈-fun-left var-∈) c B≢★) =
  calibration-2-inst-route₅ c
calibration-2₅
    (inst₅ nonvar-fun (∈-fun-right (∉-var neq) var-∈) c B≢★) =
  ⊥-elim (neq refl)
calibration-2₅
    (gen₅ nonvar-fun (∈-fun-left var-∈) c A≢★) =
  calibration-2-gen-route₅ c

------------------------------------------------------------------------
-- Ground-cast-target forall case: strict slot restores occurrence transport
------------------------------------------------------------------------

blocked-ground-cast-body₅ : Ty 1
blocked-ground-cast-body₅ = ＇ zero ⇒ ★

blocked-ground-cast-occurs₅ : zero ∈ᵗ blocked-ground-cast-body₅
blocked-ground-cast-occurs₅ = ∈-fun-left var-∈

blocked-ground-cast-body-unformable₅ :
  ¬ (extᵐ₅ (idᶜ₅ {Δ = 0}) ⊢ blocked-ground-cast-body₅ ∼₅ ★)
blocked-ground-cast-body-unformable₅
    (tag₅ ★⇒★ ⇒∼★₅ (dom ↦₅ cod) nonstar-⇒) =
  strict-mode-var-not-from-star₅ refl dom
blocked-ground-cast-body-unformable₅
    (tag₅ ∀★ ∀∼★₅ (gen₅ nonvar-star () c A≢★) nonstar-⇒)

blocked-ground-cast-inst-route-unformable₅ :
  ¬ (instᵐ₅ (idᶜ₅ {Δ = 0})
       ⊢ blocked-ground-cast-body₅ ∼₅ ⇑ᵗ (`∀ ★))
blocked-ground-cast-inst-route-unformable₅
    (gen₅ nonvar-star () c A≢★)

blocked-ground-cast-forall-direct-unformable₅ :
  ¬ (idᶜ₅ {Δ = 0}
       ⊢ (`∀ blocked-ground-cast-body₅) ∼₅ (`∀ ★))
blocked-ground-cast-forall-direct-unformable₅ (∀ᶜ₅ c) =
  blocked-ground-cast-body-unformable₅ c
blocked-ground-cast-forall-direct-unformable₅
    (inst₅ nonvar-fun (∈-fun-left var-∈) c B≢★) =
  blocked-ground-cast-inst-route-unformable₅ c

------------------------------------------------------------------------
-- CrossFree common-lower interface
------------------------------------------------------------------------

data CrossFree∼★₅ : ∀ {Δ : TyCtx} {μ : Env∼₅ Δ} {G : Ty Δ}
    → μ ⊢ G ∼★₅ → Set where
  cf-⇒∼★₅ : ∀ {Δ} {μ : Env∼₅ Δ}
    → CrossFree∼★₅ (⇒∼★₅ {μ = μ})
  cf-ι∼★₅ : ∀ {Δ} {μ : Env∼₅ Δ} {ι}
    → CrossFree∼★₅ (ι∼★₅ {μ = μ} {ι = ι})
  cf-X∼★ᵍ₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X} {eq : μ X ≡ X∼★}
    → CrossFree∼★₅ (X∼★ᵍ₅ {μ = μ} {X = X} eq)
  cf-∀∼★₅ : ∀ {Δ} {μ : Env∼₅ Δ}
    → CrossFree∼★₅ (∀∼★₅ {μ = μ})

data CrossFree★∼₅ : ∀ {Δ : TyCtx} {μ : Env∼₅ Δ} {G : Ty Δ}
    → μ ⊢★∼₅ G → Set where
  cf-★∼⇒₅ : ∀ {Δ} {μ : Env∼₅ Δ}
    → CrossFree★∼₅ (★∼⇒₅ {μ = μ})
  cf-★∼ι₅ : ∀ {Δ} {μ : Env∼₅ Δ} {ι}
    → CrossFree★∼₅ (★∼ι₅ {μ = μ} {ι = ι})
  cf-★∼Xᵍ₅ : ∀ {Δ} {μ : Env∼₅ Δ} {X} {eq : μ X ≡ ★∼X}
    → CrossFree★∼₅ (★∼Xᵍ₅ {μ = μ} {X = X} eq)
  cf-★∼∀₅ : ∀ {Δ} {μ : Env∼₅ Δ}
    → CrossFree★∼₅ (★∼∀₅ {μ = μ})

data CrossFree₅ : ∀ {Δ : TyCtx} {μ : Env∼₅ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼₅ B → Set where
  cf-id₅ : ∀ {Δ} {μ : Env∼₅ Δ} {A} {a : Atom A}
    → CrossFree₅ (id₅ {μ = μ} a)
  cf-↦₅ : ∀ {Δ} {μ : Env∼₅ Δ} {A A′ B B′}
      {c : flipᵐ₅ μ ⊢ A′ ∼₅ A} {d : μ ⊢ B ∼₅ B′}
    → CrossFree₅ c
    → CrossFree₅ d
    → CrossFree₅ (c ↦₅ d)
  cf-∀ᶜ₅ : ∀ {Δ} {μ : Env∼₅ Δ} {A B}
      {c : extᵐ₅ μ ⊢ A ∼₅ B}
    → CrossFree₅ c
    → CrossFree₅ (∀ᶜ₅ c)
  cf-!₅ : ∀ {Δ} {μ : Env∼₅ Δ} {A G}
      {g : Ground G} {G∼★ : μ ⊢ G ∼★₅}
      {c : μ ⊢ A ∼₅ G} {Ans : NonStar A}
    → CrossFree∼★₅ G∼★
    → CrossFree₅ c
    → CrossFree₅ (tag₅ g G∼★ c Ans)
  cf-？₅ : ∀ {Δ} {μ : Env∼₅ Δ} {G B}
      {g : Ground G} {★∼G : μ ⊢★∼₅ G}
      {c : μ ⊢ G ∼₅ B} {Bns : NonStar B}
    → CrossFree★∼₅ ★∼G
    → CrossFree₅ c
    → CrossFree₅ (proj₅ g ★∼G c Bns)
  cf-inst₅ : ∀ {Δ} {μ : Env∼₅ Δ} {A B}
      {Anv : NonVar A} {z∈A : zero ∈ᵗ A}
      {c : instᵐ₅ μ ⊢ A ∼₅ ⇑ᵗ B} {B≢★ : B ≢ ★}
    → CrossFree₅ c
    → CrossFree₅ (inst₅ Anv z∈A c B≢★)
  cf-gen₅ : ∀ {Δ} {μ : Env∼₅ Δ} {A B}
      {Bnv : NonVar B} {z∈B : zero ∈ᵗ B}
      {c : genᵐ₅ μ ⊢ ⇑ᵗ A ∼₅ B} {A≢★ : A ≢ ★}
    → CrossFree₅ c
    → CrossFree₅ (gen₅ Bnv z∈B c A≢★)
  cf-bot-elim₅ : ∀ {Δ} {μ : Env∼₅ Δ}
    → CrossFree₅ (bot-elim₅ {μ = μ})
  cf-bot-intro₅ : ∀ {Δ} {μ : Env∼₅ Δ}
    → CrossFree₅ (bot-intro₅ {μ = μ})

crossable-counterexample-excluded₅ :
  CrossFree₅ calibration-1₅ → ⊥
crossable-counterexample-excluded₅ (cf-!₅ () cf-id₅)

data VarImp₅ : Set where
  X⊑X₅ : VarImp₅
  X⊑★₅ : VarImp₅

ImpEnv₅ : TyCtx → Set
ImpEnv₅ Δ = TyVar Δ → VarImp₅

idᵢ₅ : ∀ {Δ} → ImpEnv₅ Δ
idᵢ₅ X = X⊑X₅

extᵢ₅ : ImpEnv₅ Δ → ImpEnv₅ (Nat.suc Δ)
extᵢ₅ μ zero = X⊑X₅
extᵢ₅ μ (suc X) = μ X

instᵢ₅ : ImpEnv₅ Δ → ImpEnv₅ (Nat.suc Δ)
instᵢ₅ μ zero = X⊑★₅
instᵢ₅ μ (suc X) = μ X

data _⊢_⊑₅_ {Δ : TyCtx} (μ : ImpEnv₅ Δ) :
    Ty Δ → Ty Δ → Set where
  ★⊑★₅ : μ ⊢ ★ ⊑₅ ★
  ι⊑ι₅ : ∀ {ι} → μ ⊢ ‵ ι ⊑₅ ‵ ι
  X⊑X₅ : ∀ {X} → μ ⊢ ＇ X ⊑₅ ＇ X
  ⇒⊑⇒₅ : ∀ {A A′ B B′}
    → μ ⊢ A ⊑₅ A′
    → μ ⊢ B ⊑₅ B′
    → μ ⊢ (A ⇒ B) ⊑₅ (A′ ⇒ B′)
  ∀⊑∀₅ : ∀ {A B}
    → extᵢ₅ μ ⊢ A ⊑₅ B
    → μ ⊢ (`∀ A) ⊑₅ (`∀ B)
  ι⊑★₅ : ∀ {ι} → μ ⊢ ‵ ι ⊑₅ ★
  X⊑★₅ : ∀ {X}
    → μ X ≡ X⊑★₅
    → μ ⊢ ＇ X ⊑₅ ★
  _⇒ᵢ₅_ : ∀ {A B}
    → μ ⊢ A ⊑₅ ★
    → μ ⊢ B ⊑₅ ★
    → μ ⊢ (A ⇒ B) ⊑₅ ★
  ∀★⊑★₅ : μ ⊢ (`∀ ★) ⊑₅ ★

data VarLower₅ : Var∼₅ → VarImp₅ → VarImp₅ → Set where
  lower-cross-refl₅ : VarLower₅ ★∼X∼★ X⊑X₅ X⊑X₅
  lower-strict-refl₅ : VarLower₅ X∼X X⊑X₅ X⊑X₅
  lower-to-star₅ : VarLower₅ X∼★ X⊑X₅ X⊑★₅
  lower-from-star₅ : VarLower₅ ★∼X X⊑★₅ X⊑X₅

LowerEnv₅ : Env∼₅ Δ → ImpEnv₅ Δ → ImpEnv₅ Δ → Set
LowerEnv₅ μ φ ψ = ∀ X → VarLower₅ (μ X) (φ X) (ψ X)

extend-lower-env₅ : ∀ {Δ} {μ : Env∼₅ Δ} {φ ψ}
  → LowerEnv₅ μ φ ψ
  → LowerEnv₅ (extᵐ₅ μ) (extᵢ₅ φ) (extᵢ₅ ψ)
extend-lower-env₅ h zero = lower-strict-refl₅
extend-lower-env₅ h (suc X) = h X

CommonLowerStatement₅ : Set
CommonLowerStatement₅ =
  ∀ {Δ} {μ : Env∼₅ Δ} {φ ψ : ImpEnv₅ Δ} {A B : Ty Δ}
  → LowerEnv₅ μ φ ψ
  → (c : μ ⊢ A ∼₅ B)
  → CrossFree₅ c
  → Σ[ D ∈ Ty Δ ] (φ ⊢ D ⊑₅ A × ψ ⊢ D ⊑₅ B)

consistent-common-lower-∀ᶜ-clause₅ :
  ∀ {Δ} {μ : Env∼₅ Δ} {φ ψ : ImpEnv₅ Δ} {A B : Ty (Nat.suc Δ)}
  → (Σ[ D ∈ Ty (Nat.suc Δ) ]
       (extᵢ₅ φ ⊢ D ⊑₅ A × extᵢ₅ ψ ⊢ D ⊑₅ B))
  → Σ[ D ∈ Ty Δ ]
       (φ ⊢ D ⊑₅ (`∀ A) × ψ ⊢ D ⊑₅ (`∀ B))
consistent-common-lower-∀ᶜ-clause₅ (D , D⊑A , D⊑B) =
  `∀ D , ∀⊑∀₅ D⊑A , ∀⊑∀₅ D⊑B

right-star-from-var-lower₅ : ∀ {r p q}
  → VarLower₅ r p q
  → r ≡ X∼★
  → q ≡ X⊑★₅
right-star-from-var-lower₅ lower-to-star₅ refl = refl

left-star-from-var-lower₅ : ∀ {r p q}
  → VarLower₅ r p q
  → r ≡ ★∼X
  → p ≡ X⊑★₅
left-star-from-var-lower₅ lower-from-star₅ refl = refl

common-lower-dynamic-to-star-var₅ :
  ∀ {Δ} {μ : Env∼₅ Δ} {φ ψ : ImpEnv₅ Δ} {X}
  → LowerEnv₅ μ φ ψ
  → μ X ≡ X∼★
  → Σ[ D ∈ Ty Δ ] (φ ⊢ D ⊑₅ ＇ X × ψ ⊢ D ⊑₅ ★)
common-lower-dynamic-to-star-var₅ {X = X} h eq =
  ＇ X , X⊑X₅ , X⊑★₅ (right-star-from-var-lower₅ (h X) eq)

common-lower-dynamic-from-star-var₅ :
  ∀ {Δ} {μ : Env∼₅ Δ} {φ ψ : ImpEnv₅ Δ} {X}
  → LowerEnv₅ μ φ ψ
  → μ X ≡ ★∼X
  → Σ[ D ∈ Ty Δ ] (φ ⊢ D ⊑₅ ★ × ψ ⊢ D ⊑₅ ＇ X)
common-lower-dynamic-from-star-var₅ {X = X} h eq =
  ＇ X , X⊑★₅ (left-star-from-var-lower₅ (h X) eq) , X⊑X₅

------------------------------------------------------------------------
-- Mode-restricted totality: no strict variables on that side
------------------------------------------------------------------------

mutual
  data To★OK₅ {Δ : TyCtx} (μ : Env∼₅ Δ) : Ty Δ → Set where
    to★-X∼★₅ : ∀ {X}
      → μ X ≡ X∼★
      → To★OK₅ μ (＇ X)
    to★-★∼X∼★₅ : ∀ {X}
      → μ X ≡ ★∼X∼★
      → To★OK₅ μ (＇ X)
    to★-ι₅ : ∀ {ι} → To★OK₅ μ (‵ ι)
    to★-★₅ : To★OK₅ μ ★
    to★-⇒₅ : ∀ {A B}
      → From★OK₅ (flipᵐ₅ μ) A
      → To★OK₅ μ B
      → To★OK₅ μ (A ⇒ B)
    to★-∀₅ : ∀ {A}
      → To★OK₅ (extᵐ₅ μ) A
      → To★OK₅ μ (`∀ A)

  data From★OK₅ {Δ : TyCtx} (μ : Env∼₅ Δ) : Ty Δ → Set where
    from★-★∼X₅ : ∀ {X}
      → μ X ≡ ★∼X
      → From★OK₅ μ (＇ X)
    from★-★∼X∼★₅ : ∀ {X}
      → μ X ≡ ★∼X∼★
      → From★OK₅ μ (＇ X)
    from★-ι₅ : ∀ {ι} → From★OK₅ μ (‵ ι)
    from★-★₅ : From★OK₅ μ ★
    from★-⇒₅ : ∀ {A B}
      → To★OK₅ (flipᵐ₅ μ) A
      → From★OK₅ μ B
      → From★OK₅ μ (A ⇒ B)
    from★-∀₅ : ∀ {A}
      → From★OK₅ (extᵐ₅ μ) A
      → From★OK₅ μ (`∀ A)

mutual
  to-★₅ : ∀ {Δ} {μ : Env∼₅ Δ} {C : Ty Δ}
    → To★OK₅ μ C
    → μ ⊢ C ∼₅ ★
  to-★₅ (to★-X∼★₅ eq) = var-to-star-dyn₅ eq
  to-★₅ (to★-★∼X∼★₅ eq) = var-to-star-cross₅ eq
  to-★₅ to★-ι₅ = tag₅ (‵ _) ι∼★₅ (id₅ (‵ _)) nonstar-ι
  to-★₅ to★-★₅ = id₅ ★
  to-★₅ (to★-⇒₅ A-ok B-ok) =
    tag₅ ★⇒★ ⇒∼★₅ (from-★₅ A-ok ↦₅ to-★₅ B-ok) nonstar-⇒
  to-★₅ (to★-∀₅ A-ok) =
    tag₅ ∀★ ∀∼★₅ (∀ᶜ₅ to-★₅ A-ok) nonstar-∀

  from-★₅ : ∀ {Δ} {μ : Env∼₅ Δ} {C : Ty Δ}
    → From★OK₅ μ C
    → μ ⊢ ★ ∼₅ C
  from-★₅ (from★-★∼X₅ eq) = star-to-var-dyn₅ eq
  from-★₅ (from★-★∼X∼★₅ eq) = star-to-var-cross₅ eq
  from-★₅ from★-ι₅ = proj₅ (‵ _) ★∼ι₅ (id₅ (‵ _)) nonstar-ι
  from-★₅ from★-★₅ = id₅ ★
  from-★₅ (from★-⇒₅ A-ok B-ok) =
    proj₅ ★⇒★ ★∼⇒₅ (to-★₅ A-ok ↦₅ from-★₅ B-ok) nonstar-⇒
  from-★₅ (from★-∀₅ A-ok) =
    proj₅ ∀★ ★∼∀₅ (∀ᶜ₅ from-★₅ A-ok) nonstar-∀

to★-crossable-var-ok₅ : To★OK₅ (idᶜ₅ {Δ = 1}) (＇ zero)
to★-crossable-var-ok₅ = to★-★∼X∼★₅ refl

from★-crossable-var-ok₅ : From★OK₅ (idᶜ₅ {Δ = 1}) (＇ zero)
from★-crossable-var-ok₅ = from★-★∼X∼★₅ refl

to★-dynamic-var-ok₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → To★OK₅ (instᵐ₅ μ) (＇ zero)
to★-dynamic-var-ok₅ = to★-X∼★₅ refl

from★-dynamic-var-ok₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → From★OK₅ (genᵐ₅ μ) (＇ zero)
from★-dynamic-var-ok₅ = from★-★∼X₅ refl

to★-strict-var-impossible₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → To★OK₅ (extᵐ₅ μ) (＇ zero) → ⊥
to★-strict-var-impossible₅ (to★-X∼★₅ ())
to★-strict-var-impossible₅ (to★-★∼X∼★₅ ())

from★-strict-var-impossible₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → From★OK₅ (extᵐ₅ μ) (＇ zero) → ⊥
from★-strict-var-impossible₅ (from★-★∼X₅ ())
from★-strict-var-impossible₅ (from★-★∼X∼★₅ ())

------------------------------------------------------------------------
-- Substitution environments: rigid fields re-key to crossable only
------------------------------------------------------------------------

record SubstEnv∼₅ {Δ Δ′ : TyCtx}
    (μ : Env∼₅ Δ) (ν : Env∼₅ Δ′) (σ : Δ ⇒ˢ Δ′) : Set where
  constructor subst-env∼₅
  field
    self : ∀ X → ν ⊢ σ X ∼₅ σ X
    to-★ᵍ : ∀ X → μ X ≡ X∼★ → ν ⊢ σ X ∼₅ ★
    from-★ᵍ : ∀ X → μ X ≡ ★∼X → ν ⊢ ★ ∼₅ σ X
    cross-to-★ : ∀ X → μ X ≡ ★∼X∼★ → ν ⊢ σ X ∼₅ ★
    cross-from-★ : ∀ X → μ X ≡ ★∼X∼★ → ν ⊢ ★ ∼₅ σ X

open SubstEnv∼₅

subst-env-cross-to-star₅ : ∀ {Δ Δ′} {μ : Env∼₅ Δ}
    {ν : Env∼₅ Δ′} {σ : Δ ⇒ˢ Δ′} {X}
  → SubstEnv∼₅ μ ν σ
  → μ X ≡ ★∼X∼★
  → ν ⊢ σ X ∼₅ ★
subst-env-cross-to-star₅ s eq = cross-to-★ s _ eq

subst-env-cross-from-star₅ : ∀ {Δ Δ′} {μ : Env∼₅ Δ}
    {ν : Env∼₅ Δ′} {σ : Δ ⇒ˢ Δ′} {X}
  → SubstEnv∼₅ μ ν σ
  → μ X ≡ ★∼X∼★
  → ν ⊢ ★ ∼₅ σ X
subst-env-cross-from-star₅ s eq = cross-from-★ s _ eq

open-to-★-strict-slot-impossible₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → extᵐ₅ μ zero ≡ X∼★ → ⊥
open-to-★-strict-slot-impossible₅ ()

open-from-★-strict-slot-impossible₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → extᵐ₅ μ zero ≡ ★∼X → ⊥
open-from-★-strict-slot-impossible₅ ()

open-cross-to-★-strict-slot-impossible₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → extᵐ₅ μ zero ≡ ★∼X∼★ → ⊥
open-cross-to-★-strict-slot-impossible₅ ()

open-strict-slot-is-strict₅ : ∀ {Δ} {μ : Env∼₅ Δ}
  → extᵐ₅ μ zero ≡ X∼X
open-strict-slot-is-strict₅ = refl

module ConsistencyProperties where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc)

open import Types
open import Consistency

------------------------------------------------------------------------
-- No free type variables (de Bruijn-depth aware)
------------------------------------------------------------------------

infix 4 _<ᵈ_

data _<ᵈ_ : ∀{Δ} → TyVar Δ → ℕ → Set where
  Z< : ∀{Δ}{d} → _<ᵈ_ {Δ = suc Δ} Zᵗ (suc d)
  S< : ∀{Δ}{d}{X : TyVar Δ} → X <ᵈ d → Sᵗ X <ᵈ suc d

data NoFreeXᵈ : ∀{Δ}{Ψ} → ℕ → Ty Δ Ψ → Set where
  nx-var :
    ∀{Δ}{Ψ}{d}{X : TyVar Δ} →
    X <ᵈ d →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (＇ X)

  nx-seal :
    ∀{Δ}{Ψ}{d}{α : Seal Ψ} →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (｀ α)

  nx-base :
    ∀{Δ}{Ψ}{d}{ι : Base} →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (‵ ι)

  nx-star :
    ∀{Δ}{Ψ}{d} →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d `★

  nx-arr :
    ∀{Δ}{Ψ}{d}{A B : Ty Δ Ψ} →
    NoFreeXᵈ d A →
    NoFreeXᵈ d B →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (A ⇒ B)

  nx-all :
    ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ} →
    NoFreeXᵈ {Δ = suc Δ} {Ψ = Ψ} (suc d) A →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (`∀ A)

NoFreeX : ∀{Δ}{Ψ} → Ty Δ Ψ → Set
NoFreeX = NoFreeXᵈ 0

varTy : ∀{Δ}{Ψ} → TyVar Δ → Ty Δ Ψ
varTy X = ＇ X

data SealsAt★ : ∀{Δ}{Ψ} → Store Ψ → Ty Δ Ψ → Set where
  sX :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{X : TyVar Δ} →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (＇ X)

  sα :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ} →
    Σ ∋ˢ α ⦂ `★ →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (｀ α)

  s-base :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{ι : Base} →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (‵ ι)

  s-star :
    ∀{Δ}{Ψ}{Σ : Store Ψ} →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ `★

  s-arr :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    SealsAt★ Σ A →
    SealsAt★ Σ B →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (A ⇒ B)

  s-all :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ} →
    SealsAt★ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (`∀ A)

<ᵈ-zero-impossible : ∀{Δ}{X : TyVar Δ} → X <ᵈ 0 → ⊥
<ᵈ-zero-impossible ()

RenPres :
  ∀{Δ}{Δ′} →
  ℕ →
  ℕ →
  Renameᵗ Δ Δ′ →
  Set
RenPres d d′ ρ = ∀{X} → X <ᵈ d → ρ X <ᵈ d′

RenPres-ext :
  ∀{Δ}{Δ′}{d}{d′}{ρ : Renameᵗ Δ Δ′} →
  RenPres d d′ ρ →
  RenPres (suc d) (suc d′) (extᵗ ρ)
RenPres-ext hρ Z< = Z<
RenPres-ext hρ (S< p) = S< (hρ p)

NoFreeXᵈ-rename :
  ∀{Δ}{Δ′}{Ψ}{d}{d′}{ρ : Renameᵗ Δ Δ′}{A : Ty Δ Ψ} →
  RenPres d d′ ρ →
  NoFreeXᵈ d A →
  NoFreeXᵈ d′ (renameᵗ ρ A)
NoFreeXᵈ-rename hρ (nx-var p) = nx-var (hρ p)
NoFreeXᵈ-rename hρ nx-seal = nx-seal
NoFreeXᵈ-rename hρ nx-base = nx-base
NoFreeXᵈ-rename hρ nx-star = nx-star
NoFreeXᵈ-rename hρ (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-rename hρ nxA) (NoFreeXᵈ-rename hρ nxB)
NoFreeXᵈ-rename hρ (nx-all nxA) =
  nx-all (NoFreeXᵈ-rename (RenPres-ext hρ) nxA)

NoFreeXᵈ-rename-S :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ d A →
  NoFreeXᵈ (suc d) (renameᵗ Sᵗ A)
NoFreeXᵈ-rename-S =
  NoFreeXᵈ-rename (λ p → S< p)

NoFreeXᵈ-⇑ˢ :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ d A →
  NoFreeXᵈ d (⇑ˢ A)
NoFreeXᵈ-⇑ˢ (nx-var p) = nx-var p
NoFreeXᵈ-⇑ˢ nx-seal = nx-seal
NoFreeXᵈ-⇑ˢ nx-base = nx-base
NoFreeXᵈ-⇑ˢ nx-star = nx-star
NoFreeXᵈ-⇑ˢ (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-⇑ˢ nxA) (NoFreeXᵈ-⇑ˢ nxB)
NoFreeXᵈ-⇑ˢ (nx-all nxA) =
  nx-all (NoFreeXᵈ-⇑ˢ nxA)

SubstOKᵈ :
  ∀{Δ}{Δ′}{Ψ} →
  ℕ →
  Substᵗ Δ Δ′ Ψ →
  Set
SubstOKᵈ d σ = ∀{X} → X <ᵈ suc d → NoFreeXᵈ d (σ X)

SubstOKᵈ-exts :
  ∀{Δ}{Δ′}{Ψ}{d}{σ : Substᵗ Δ Δ′ Ψ} →
  SubstOKᵈ d σ →
  SubstOKᵈ (suc d) (extsᵗ σ)
SubstOKᵈ-exts hσ {X = Zᵗ} p = nx-var Z<
SubstOKᵈ-exts hσ {X = Sᵗ X} (S< p) =
  NoFreeXᵈ-rename-S (hσ p)

NoFreeXᵈ-substᵗ :
  ∀{Δ}{Δ′}{Ψ}{d}{A : Ty Δ Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  NoFreeXᵈ (suc d) A →
  SubstOKᵈ d σ →
  NoFreeXᵈ d (substᵗ σ A)
NoFreeXᵈ-substᵗ (nx-var p) hσ = hσ p
NoFreeXᵈ-substᵗ nx-seal hσ = nx-seal
NoFreeXᵈ-substᵗ nx-base hσ = nx-base
NoFreeXᵈ-substᵗ nx-star hσ = nx-star
NoFreeXᵈ-substᵗ (nx-arr nxA nxB) hσ =
  nx-arr (NoFreeXᵈ-substᵗ nxA hσ) (NoFreeXᵈ-substᵗ nxB hσ)
NoFreeXᵈ-substᵗ (nx-all nxA) hσ =
  nx-all (NoFreeXᵈ-substᵗ nxA (SubstOKᵈ-exts hσ))

SubstOKᵈ-single-var :
  ∀{Δ}{Ψ}{d}{V : TyVar Δ} →
  V <ᵈ d →
  SubstOKᵈ d (singleTyEnv {Δ = Δ} {Ψ = Ψ} (varTy {Ψ = Ψ} V))
SubstOKᵈ-single-var v< {X = Zᵗ} p = nx-var v<
SubstOKᵈ-single-var v< {X = Sᵗ X} (S< p) = nx-var p

SubstOKᵈ-single-seal :
  ∀{Δ}{Ψ}{d}{α : Seal Ψ} →
  SubstOKᵈ d (singleTyEnv {Δ = Δ} (｀ α))
SubstOKᵈ-single-seal {X = Zᵗ} p = nx-seal
SubstOKᵈ-single-seal {X = Sᵗ X} (S< p) = nx-var p

NoFreeXᵈ-subst-var :
  ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ}{X : TyVar Δ} →
  NoFreeXᵈ (suc d) A →
  X <ᵈ d →
  NoFreeXᵈ d (A [ ＇ X ]ᵗ)
NoFreeXᵈ-subst-var {Δ = Δ} {Ψ = Ψ} {d = d} {X = X} nxA x< =
  NoFreeXᵈ-substᵗ {d = d} {σ = singleTyEnv {Δ = Δ} {Ψ = Ψ} (varTy {Ψ = Ψ} X)}
    nxA
    (SubstOKᵈ-single-var {Ψ = Ψ} x<)

NoFreeXᵈ-subst-seal :
  ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  NoFreeXᵈ (suc d) A →
  NoFreeXᵈ d (A [ ｀ α ]ᵗ)
NoFreeXᵈ-subst-seal {Δ = Δ} {d = d} {α = α} nxA =
  NoFreeXᵈ-substᵗ {d = d} {σ = singleTyEnv {Δ = Δ} (｀ α)}
    nxA
    SubstOKᵈ-single-seal

------------------------------------------------------------------------
-- If A has no free X and all free seals in A map to ★, then ★ ~ A.
------------------------------------------------------------------------

mutual
  ★~-closed :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    SealsAt★ Σ A →
    Σ ⊢ `★ ~ A
  ★~-closed {A = ＇ X} (nx-var nxX) sX = ⊥-elim (<ᵈ-zero-impossible nxX)
  ★~-closed {A = ｀ α} nx-seal (sα hα) = A~α hα refl
  ★~-closed {A = ‵ ι} nx-base s-base = ★~G (‵ ι)
  ★~-closed {A = `★} nx-star s-star = ★~★
  ★~-closed (nx-arr nxA nxB) (s-arr hA hB) =
    ★~⇒ (~★-closed nxA hA) (★~-closed nxB hB)
  ★~-closed {A = `∀ A} (nx-all nxA) (s-all hA) =
    ~∀ (★~-closed (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA)) hA)

  ~★-closed :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    SealsAt★ Σ A →
    Σ ⊢ A ~ `★
  ~★-closed {A = ＇ X} (nx-var nxX) sX = ⊥-elim (<ᵈ-zero-impossible nxX)
  ~★-closed {A = ｀ α} nx-seal (sα hα) = α~A hα refl
  ~★-closed {A = ‵ ι} nx-base s-base = G~★ (‵ ι)
  ~★-closed {A = `★} nx-star s-star = ★~★
  ~★-closed (nx-arr nxA nxB) (s-arr hA hB) =
    ⇒~★ (★~-closed nxA hA) (~★-closed nxB hB)
  ~★-closed {A = `∀ A} (nx-all nxA) (s-all hA) =
    ∀~ (~★-closed (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA)) hA)

------------------------------------------------------------------------
-- Consistency is symmetric
------------------------------------------------------------------------

~-sym :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ~ B →
  Σ ⊢ B ~ A
~-sym X~X = X~X
~-sym α~α = α~α
~-sym ι~ι = ι~ι
~-sym ★~★ = ★~★
~-sym (★~G g) = G~★ g
~-sym (G~★ g) = ★~G g
~-sym (★~⇒ A~★ ★~B) = ⇒~★ (~-sym A~★) (~-sym ★~B)
~-sym (⇒~★ ★~A B~★) = ★~⇒ (~-sym ★~A) (~-sym B~★)
~-sym (A~α h eq) = α~A h eq
~-sym (α~A h eq) = A~α h eq
~-sym (↦~↦ c d) = ↦~↦ (~-sym c) (~-sym d)
~-sym (∀~∀ c) = ∀~∀ (~-sym c)
~-sym (∀~ c) = ~∀ (~-sym c)
~-sym (~∀ c) = ∀~ (~-sym c)

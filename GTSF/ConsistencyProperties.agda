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
    NoFreeXᵈ {Δ = Δ} {Ψ = suc Ψ} d ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (`∀ A)

NoFreeX : ∀{Δ}{Ψ} → Ty Δ Ψ → Set
NoFreeX = NoFreeXᵈ 0

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
    ~∀ (★~-closed nxA hA)

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
    ∀~ (~★-closed nxA hA)

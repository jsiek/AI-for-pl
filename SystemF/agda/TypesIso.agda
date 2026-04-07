module TypesIso where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Nat.Base using (zero; suc; _<_; z<s; s<s)
open import Data.Product using (Σ; _,_)

open import intrinsic.Types as I
  renaming (`_ to ivar; `Nat to iNat; `ℕ to iℕ; `Bool to iBool; _⇒_ to _i⇒_; `∀_ to i∀)
open import curry.Types as E
  renaming (`_ to evar; `ℕ to eℕ; `Bool to eBool; _⇒_ to _e⇒_; `∀ to e∀)

eraseTyCtx : I.TyCtx → E.TyCtx
eraseTyCtx I.∅ = zero
eraseTyCtx (Δ I.,α) = suc (eraseTyCtx Δ)

eraseVar : ∀ {Δ} → I.TyVar Δ → E.Var
eraseVar I.Z = zero
eraseVar (I.S_ x) = suc (eraseVar x)

eraseVar< : ∀ {Δ} (x : I.TyVar Δ) → eraseVar x < eraseTyCtx Δ
eraseVar< I.Z = z<s
eraseVar< (I.S_ x) = s<s (eraseVar< x)

erase : ∀ {Δ} → I.Type Δ → E.Ty
erase (ivar x) = evar (eraseVar x)
erase iNat = eℕ
erase iBool = eBool
erase (A i⇒ B) = erase A e⇒ erase B
erase (i∀ A) = e∀ (erase A)

eraseWf : ∀ {Δ} (A : I.Type Δ) → E.WfTy (eraseTyCtx Δ) (erase A)
eraseWf (ivar x) = E.wfVar (eraseVar< x)
eraseWf iNat = E.wf`ℕ
eraseWf iBool = E.wf`Bool
eraseWf (A i⇒ B) = E.wfFn (eraseWf A) (eraseWf B)
eraseWf (i∀ A) = E.wf`∀ (eraseWf A)

eraseΣ : ∀ {Δ} (A : I.Type Δ) → Σ E.Ty (E.WfTy (eraseTyCtx Δ))
eraseΣ A = erase A , eraseWf A

lt→TyVar : ∀ {Δ X} → X < eraseTyCtx Δ → I.TyVar Δ
lt→TyVar {I.∅} ()
lt→TyVar {Δ I.,α} {zero} z<s = I.Z
lt→TyVar {Δ I.,α} {suc X} (s<s X<Δ) = I.S_ (lt→TyVar {Δ} {X} X<Δ)

unerase : ∀ {Δ A} → E.WfTy (eraseTyCtx Δ) A → I.Type Δ
unerase (E.wfVar X<Δ) = ivar (lt→TyVar X<Δ)
unerase E.wf`ℕ = iℕ
unerase E.wf`Bool = iBool
unerase (E.wfFn hA hB) = unerase hA i⇒ unerase hB
unerase {Δ = Δ} (E.wf`∀ hA) = i∀ (unerase {Δ = Δ I.,α} hA)

eraseVar-lt→TyVar : ∀ {Δ X} (X<Δ : X < eraseTyCtx Δ) → eraseVar (lt→TyVar X<Δ) ≡ X
eraseVar-lt→TyVar {I.∅} ()
eraseVar-lt→TyVar {Δ I.,α} {zero} z<s = refl
eraseVar-lt→TyVar {Δ I.,α} {suc X} (s<s X<Δ) = cong suc (eraseVar-lt→TyVar {Δ} {X} X<Δ)

lt→TyVar-eraseVar : ∀ {Δ} (x : I.TyVar Δ) → lt→TyVar (eraseVar< x) ≡ x
lt→TyVar-eraseVar I.Z = refl
lt→TyVar-eraseVar (I.S_ x) = cong I.S_ (lt→TyVar-eraseVar x)

erase∘unerase : ∀ {Δ A} (hA : E.WfTy (eraseTyCtx Δ) A) → erase (unerase hA) ≡ A
erase∘unerase (E.wfVar X<Δ) = cong evar (eraseVar-lt→TyVar X<Δ)
erase∘unerase E.wf`ℕ = refl
erase∘unerase E.wf`Bool = refl
erase∘unerase (E.wfFn hA hB) = cong₂ _e⇒_ (erase∘unerase hA) (erase∘unerase hB)
erase∘unerase {Δ = Δ} (E.wf`∀ hA) = cong e∀ (erase∘unerase {Δ = Δ I.,α} hA)

unerase∘erase : ∀ {Δ} (A : I.Type Δ) → unerase (eraseWf A) ≡ A
unerase∘erase (ivar x) = cong ivar (lt→TyVar-eraseVar x)
unerase∘erase iNat = refl
unerase∘erase iBool = refl
unerase∘erase (A i⇒ B) = cong₂ _i⇒_ (unerase∘erase A) (unerase∘erase B)
unerase∘erase (i∀ A) = cong i∀ (unerase∘erase A)

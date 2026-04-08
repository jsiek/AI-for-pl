module TermsIso where

open import Relation.Binary.PropositionalEquality
            using (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

open import TypesIso as T
  using (eraseTyCtx; erase; eraseWf)

open import intrinsic.Types as I
  renaming (`_ to ivar; `Nat to iNat; `Bool to iBool; _⇒_ to _i⇒_; `∀_ to i∀)
open import intrinsic.Ctx as IC
open import intrinsic.Terms as IT

open import curry.Types as E
  renaming (`_ to evar; `ℕ to eℕ; `Bool to eBool; _⇒_ to _e⇒_; `∀ to e∀)
open import curry.Reduction as ET

eraseCtx : ∀ {Δ} → IC.Ctx Δ → E.Ctx
eraseCtx IC.∅ = []
eraseCtx (Γ IC., A) = erase A ∷ eraseCtx Γ

eraseTmVar : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ} → Γ IC.∋ A → E.Var
eraseTmVar IC.Z = zero
eraseTmVar (IC.S_ x) = suc (eraseTmVar x)

erase∋ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → (x : Γ IC.∋ A) → eraseCtx Γ E.∋ eraseTmVar x ⦂ erase A
erase∋ IC.Z = E.Z
erase∋ (IC.S_ x) = E.S (erase∋ x)

eraseTerm : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ} → IT._;_⊢_ Δ Γ A → ET.Term
eraseTerm IT.`true = ET.`true
eraseTerm IT.`false = ET.`false
eraseTerm IT.`zero = ET.`zero
eraseTerm (IT.`suc_ M) = ET.`suc_ (eraseTerm M)
eraseTerm (IT.`case-nat L M N) = ET.case_[zero⇒_|suc⇒_] (eraseTerm L) (eraseTerm M) (eraseTerm N)
eraseTerm (IT.`if_then_else L M N) = ET.`if_then_else (eraseTerm L) (eraseTerm M) (eraseTerm N)
eraseTerm (IT.` x) = ET.` (eraseTmVar x)
eraseTerm (IT.ƛ A ˙ N) = ET.ƛ_ (eraseTerm N)
eraseTerm (IT._·_ L M) = ET._·_ (eraseTerm L) (eraseTerm M)
eraseTerm (IT.Λ_ N) = ET.Λ_ (eraseTerm N)
eraseTerm (IT._∙_ M B) = ET._·[] (eraseTerm M)

postulate
  eraseCtx-⇑ᶜ : ∀ {Δ} (Γ : IC.Ctx Δ) → eraseCtx (IC.⇑ᶜ Γ) ≡ E.⤊ (eraseCtx Γ)

postulate
  erase-[]ᵗ : ∀ {Δ} (A : I.Type (Δ I.,α)) (B : I.Type Δ)
    → erase (A I.[ B ]ᵗ) ≡ (erase A) E.[ erase B ]ᵗ

erase⊢ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → (M : IT._;_⊢_ Δ Γ A)
  → ET._⊢_⊢_⦂_ (eraseTyCtx Δ) (eraseCtx Γ) (eraseTerm M) (erase A)
erase⊢ IT.`true = ET.⊢true
erase⊢ IT.`false = ET.⊢false
erase⊢ IT.`zero = ET.⊢zero
erase⊢ (IT.`suc_ M) = ET.⊢suc (erase⊢ M)
erase⊢ (IT.`case-nat L M N) = ET.⊢case (erase⊢ L) (erase⊢ M) (erase⊢ N)
erase⊢ (IT.`if_then_else L M N) = ET.⊢if (erase⊢ L) (erase⊢ M) (erase⊢ N)
erase⊢ (IT.` x) = ET.⊢` (erase∋ x)
erase⊢ (IT.ƛ A ˙ N) = ET.⊢ƛ (eraseWf A) (erase⊢ N)
erase⊢ (IT._·_ L M) = ET.⊢· (erase⊢ L) (erase⊢ M)
erase⊢ {Γ = Γ} (IT.Λ_ N) = ET.⊢Λ (substEq
  (λ Ψ → ET._⊢_⊢_⦂_ _ Ψ (eraseTerm N) _)
  (eraseCtx-⇑ᶜ Γ)
  (erase⊢ N))
erase⊢ {Δ = Δ} (IT._∙_ {A = A} M B) = substEq
  (λ T → ET._⊢_⊢_⦂_ (eraseTyCtx Δ) (eraseCtx _) (eraseTerm (IT._∙_ {A = A} M B)) T)
  (sym (erase-[]ᵗ A B))
  (ET.⊢·[] (erase⊢ M) (eraseWf B))

record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ x → from (to x) ≡ x
    to∘from : ∀ y → to (from y) ≡ y

IntrinsicWT : ∀ {Δ} → IC.Ctx Δ → I.Type Δ → Set
IntrinsicWT Γ A = IT._;_⊢_ _ Γ A

CurryWT : ∀ {Δ} → IC.Ctx Δ → I.Type Δ → Set
CurryWT {Δ} Γ A =
  Σ ET.Term (λ M → Σ (IT._;_⊢_ Δ Γ A) (λ m → eraseTerm m ≡ M))

toCurry : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → IntrinsicWT Γ A → CurryWT Γ A
toCurry m = ⟨ eraseTerm m , ⟨ m , refl ⟩ ⟩

fromCurry : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → CurryWT Γ A → IntrinsicWT Γ A
fromCurry ⟨ M , ⟨ m , eq ⟩ ⟩ = m

from∘to-Curry : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → (m : IntrinsicWT Γ A)
  → fromCurry (toCurry m) ≡ m
from∘to-Curry m = refl

to∘from-Curry : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → (e : CurryWT Γ A)
  → toCurry (fromCurry e) ≡ e
to∘from-Curry ⟨ .(eraseTerm m) , ⟨ m , refl ⟩ ⟩ = refl

termsIso : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → IntrinsicWT Γ A ≃ CurryWT Γ A
termsIso = record
  { to = toCurry
  ; from = fromCurry
  ; from∘to = from∘to-Curry
  ; to∘from = to∘from-Curry
  }

curryTerm : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → CurryWT {Δ} Γ A → ET.Term
curryTerm ⟨ M , ⟨ m , eq ⟩ ⟩ = M

curryTyping : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  → (e : CurryWT {Δ} Γ A)
  → ET._⊢_⊢_⦂_ (eraseTyCtx Δ) (eraseCtx Γ) (curryTerm e) (erase A)
curryTyping {Δ} {Γ} {A} ⟨ M , ⟨ m , eq ⟩ ⟩ =
  substEq
    (λ N → ET._⊢_⊢_⦂_ (eraseTyCtx Δ) (eraseCtx Γ) N (erase A))
    eq
    (erase⊢ m)

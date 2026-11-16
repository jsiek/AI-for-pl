module Subst.examples.MultiSortedF where

-- File Charter:
--   * Example: multi-sorted syntax (Saffrich, "Abstractions for
--     Multi-Sorted Substitutions", ITP 2024) on the one-level kit library,
--     with no change to the library.  An extrinsically typed System F where
--     expressions and types share one syntax `S ⊢ s` and one scope `S`, a
--     list of the sorts of the variables (`ctxScope Sort`).
--   * One traversal `trav` substitutes term and type variables at once, and
--     two inductions (`fuse`, `sub-id`) give all the library's lemmas.
--     Type instantiation is the same single substitution `N [ M ]` as β for
--     λ, and it needs no casts.
--   * See Subst/notes/ITP2024-comparison.md for the comparison with the
--     two-level library `Subst.Poly`, which intrinsically typed System F
--     needs.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;
  cong₂)
open import Subst.Scope using (ctxScope; Ctx; ∅; _,_; _∋_; Z; S_)

-- the sorts of variables: expressions and types
data Sort : Set where
  𝕖 𝕥 : Sort

infix  4 _⊢_
infixr 7 _⇒_
infixl 7 _·_ _∙_
infix  9 `_

data _⊢_ (S : Ctx Sort) : Sort → Set where
  `_   : ∀ {s} → S ∋ s → S ⊢ s
  ƛ_˙_ : S ⊢ 𝕥 → S , 𝕖 ⊢ 𝕖 → S ⊢ 𝕖
  _·_  : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖
  Λ_   : S , 𝕥 ⊢ 𝕖 → S ⊢ 𝕖
  _∙_  : S ⊢ 𝕖 → S ⊢ 𝕥 → S ⊢ 𝕖
  `Nat : S ⊢ 𝕥
  _⇒_  : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥
  `∀_  : S , 𝕥 ⊢ 𝕥 → S ⊢ 𝕥

open import Subst.Kit (ctxScope Sort) _⊢_ `_ public

-- One traversal for expressions and types, and for both sorts of variable.
trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Γ ⊢ A → Δ ⊢ A
trav 𝒦 σ (` x) = Kit.tm 𝒦 (σ x)
trav 𝒦 σ (ƛ A ˙ N) = ƛ trav 𝒦 σ A ˙ trav 𝒦 (exts 𝒦 σ) N
trav 𝒦 σ (L · M) = trav 𝒦 σ L · trav 𝒦 σ M
trav 𝒦 σ (Λ N) = Λ trav 𝒦 (exts 𝒦 σ) N
trav 𝒦 σ (M ∙ B) = trav 𝒦 σ M ∙ trav 𝒦 σ B
trav 𝒦 σ `Nat = `Nat
trav 𝒦 σ (A ⇒ B) = trav 𝒦 σ A ⇒ trav 𝒦 σ B
trav 𝒦 σ (`∀ A) = `∀ trav 𝒦 (exts 𝒦 σ) A

open Substitution trav public

open import Subst.proof.Kit (ctxScope Sort) _⊢_ `_ using (module Traversal)
open Traversal trav (λ _ _ _ → refl) using (sub-id-exts; module Lemmas)

fuse : Fuse
fuse 𝒦₁ 𝒦₂ 𝒦₃ R R-exts R-var = go
  where
  go : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
    → R σ₁ σ₂ σ₃ → ∀ {A} (M : Γ ⊢ A)
    → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  go r (` x) = R-var r x
  go r (ƛ A ˙ N) = cong₂ ƛ_˙_ (go r A) (go (R-exts r) N)
  go r (L · M) = cong₂ _·_ (go r L) (go r M)
  go r (Λ N) = cong Λ_ (go (R-exts r) N)
  go r (M ∙ B) = cong₂ _∙_ (go r M) (go r B)
  go r `Nat = refl
  go r (A ⇒ B) = cong₂ _⇒_ (go r A) (go r B)
  go r (`∀ A) = cong `∀_ (go (R-exts r) A)

sub-id : SubId
sub-id h (` x) = h x
sub-id h (ƛ A ˙ N) = cong₂ ƛ_˙_ (sub-id h A) (sub-id (sub-id-exts h) N)
sub-id h (L · M) = cong₂ _·_ (sub-id h L) (sub-id h M)
sub-id h (Λ N) = cong Λ_ (sub-id (sub-id-exts h) N)
sub-id h (M ∙ B) = cong₂ _∙_ (sub-id h M) (sub-id h B)
sub-id h `Nat = refl
sub-id h (A ⇒ B) = cong₂ _⇒_ (sub-id h A) (sub-id h B)
sub-id h (`∀ A) = cong `∀_ (sub-id (sub-id-exts h) A)

open Lemmas fuse sub-id public

-- The running example: Λα. λ(f : ∀β. β ⇒ β). f ∙ α
-- In the body, scope ∅ , 𝕥 , 𝕖: `Z` is f (sort 𝕖), `S Z` is α (sort 𝕥).
body : ∅ , 𝕥 ⊢ 𝕖
body = ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ ` (S Z))

poly : ∅ ⊢ 𝕖
poly = Λ body

-- β for type application is the same single substitution `_[_]` as β for
-- term application, at the sort 𝕥, and it computes with no cast.
inst : body [ `Nat ] ≡ ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ `Nat)
inst = refl

-- The substitution lemma, used at both sorts: one lemma, no casts.
sub-[]ᵗ : ∀ {Γ Δ} (σ : Sub tmK Γ Δ) (N : Γ , 𝕥 ⊢ 𝕖) (B : Γ ⊢ 𝕥)
  → sub σ (N [ B ]) ≡ sub (exts tmK σ) N [ sub σ B ]
sub-[]ᵗ = sub-[]

sub-[]ᵉ : ∀ {Γ Δ} (σ : Sub tmK Γ Δ) (N : Γ , 𝕖 ⊢ 𝕖) (M : Γ ⊢ 𝕖)
  → sub σ (N [ M ]) ≡ sub (exts tmK σ) N [ sub σ M ]
sub-[]ᵉ = sub-[]

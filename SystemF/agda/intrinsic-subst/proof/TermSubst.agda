module intrinsic-subst.proof.TermSubst where

-- File Charter:
--   * Private substitution metatheory for System F terms, from the library
--     for polymorphic languages (Subst/proof/Poly.agda).  This file proves
--     the laws that need induction on terms:
--       - `fuseᵀ`: two traversals of the type variables of a term fuse;
--       - `idᵀ`: a traversal of the type variables that is the identity on
--         variables is the identity;
--       - `commute`: a traversal of the term variables after one of the
--         type variables is one of the type variables after one of the
--         term variables;
--       - `fuse`: two traversals of the term variables fuse;
--       - `sub-id`: the identity substitution of terms;
--     and the library derives the rest (`ren-ren`, `sub-sub`, `ren-sub`,
--     `sub-ren`, `sub-⇑ᵀ`, `exts-[]`, `sub-[]`, `travᵀ-[]`, `⇑ᵀ-[]ᵀ`, ...).
--   * The laws of `travᵀ` change the types of terms by equations that hold
--     only propositionally, so they are stated with heterogeneous equality.
--   * No function extensionality: substitutions are compared pointwise.

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;
  cong₂)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.proof.TypeSubst using (fuseᵗ; sub-idᵗ)
import Subst.proof.Poly

module PL = Subst.proof.Poly tyScope tt Typ `_ travᵗ (λ _ _ _ → refl)
  fuseᵗ sub-idᵗ
module TmLaws = PL.TermLaws Tm (λ x → ` x)
module TyLaws = TmLaws.TypeLaws travᵀ (λ _ _ _ _ → refl)
module SubLaws = TyLaws.TermSubstLaws trav (λ _ _ _ → refl)

open PL using (FuseHypᵀ; IdHypᵀ; fuseᵀ-ty; fuseᵀ-ext; fuseᵀ-⇑; idᵀ-ty;
  idᵀ-ext; idᵀ-⇑)
open TmLaws using (`-≅; convᵀ-≅)

------------------------------------------------------------------------
-- Congruences of the term constructors, heterogeneously
------------------------------------------------------------------------

private
  module _ {Δ : TyCtx} {Γ Γ' : Ctx Δ} where

    true-≅ : Γ ≡ Γ' → `true {Γ = Γ} ≅ `true {Γ = Γ'}
    true-≅ refl = refl

    false-≅ : Γ ≡ Γ' → `false {Γ = Γ} ≅ `false {Γ = Γ'}
    false-≅ refl = refl

    zero-≅ : Γ ≡ Γ' → `zero {Γ = Γ} ≅ `zero {Γ = Γ'}
    zero-≅ refl = refl

    suc-≅ : ∀ {M : Δ ∣ Γ ⊢ `Nat} {M' : Δ ∣ Γ' ⊢ `Nat}
      → Γ ≡ Γ' → M ≅ M' → `suc M ≅ `suc M'
    suc-≅ refl refl = refl

    case-≅ : ∀ {A A' : Type Δ} {L : Δ ∣ Γ ⊢ `Nat} {L' : Δ ∣ Γ' ⊢ `Nat}
      {M : Δ ∣ Γ ⊢ A} {M' : Δ ∣ Γ' ⊢ A'}
      {N : Δ ∣ Γ , `Nat ⊢ A} {N' : Δ ∣ Γ' , `Nat ⊢ A'}
      → Γ ≡ Γ' → A ≡ A' → L ≅ L' → M ≅ M' → N ≅ N'
      → `case-nat L M N ≅ `case-nat L' M' N'
    case-≅ refl refl refl refl refl = refl

    if-≅ : ∀ {A A' : Type Δ} {L : Δ ∣ Γ ⊢ `Bool} {L' : Δ ∣ Γ' ⊢ `Bool}
      {M N : Δ ∣ Γ ⊢ A} {M' N' : Δ ∣ Γ' ⊢ A'}
      → Γ ≡ Γ' → A ≡ A' → L ≅ L' → M ≅ M' → N ≅ N'
      → `if_then_else L M N ≅ `if_then_else L' M' N'
    if-≅ refl refl refl refl refl = refl

    ƛ-≅ : ∀ {A A' B B' : Type Δ}
      {N : Δ ∣ Γ , A ⊢ B} {N' : Δ ∣ Γ' , A' ⊢ B'}
      → Γ ≡ Γ' → A ≡ A' → B ≡ B' → N ≅ N'
      → ƛ A ˙ N ≅ ƛ A' ˙ N'
    ƛ-≅ refl refl refl refl = refl

    ·-≅ : ∀ {A A' B B' : Type Δ}
      {L : Δ ∣ Γ ⊢ A ⇒ B} {L' : Δ ∣ Γ' ⊢ A' ⇒ B'}
      {M : Δ ∣ Γ ⊢ A} {M' : Δ ∣ Γ' ⊢ A'}
      → Γ ≡ Γ' → A ≡ A' → B ≡ B' → L ≅ L' → M ≅ M'
      → L · M ≅ L' · M'
    ·-≅ refl refl refl refl refl = refl

    Λ-≅ : ∀ {A A' : Type (Δ ,α)}
      {N : Δ ,α ∣ ⇑ᶜ Γ ⊢ A} {N' : Δ ,α ∣ ⇑ᶜ Γ' ⊢ A'}
      → Γ ≡ Γ' → A ≡ A' → N ≅ N'
      → Λ N ≅ Λ N'
    Λ-≅ refl refl refl = refl

    ∙-≅ : ∀ {A A' : Type (Δ ,α)} {B B' : Type Δ}
      {M : Δ ∣ Γ ⊢ `∀ A} {M' : Δ ∣ Γ' ⊢ `∀ A'}
      → Γ ≡ Γ' → A ≡ A' → B ≡ B' → M ≅ M'
      → M ∙ B ≅ M' ∙ B'
    ∙-≅ refl refl refl refl = refl

  travᵀ-conv : ∀ (𝒯 : TyKit) {Δ Δ'} (θ : TK.Sub (TyKit.kit 𝒯) Δ Δ')
    {Γ : Ctx Δ} {Γ' : Ctx Δ'} (ρ : TyRen 𝒯 θ Γ Γ') {A B : Type Δ}
    (p : A ≡ B) (M : Δ ∣ Γ ⊢ A)
    → travᵀ 𝒯 θ ρ (convᵀ p M) ≅ travᵀ 𝒯 θ ρ M
  travᵀ-conv 𝒯 θ ρ refl M = refl

  trav-conv : ∀ (𝒦 : Kit) {Δ} {Γ Γ' : Ctx Δ} (σ : Sub 𝒦 Γ Γ')
    {A B : Type Δ} (p : A ≡ B) (M : Δ ∣ Γ ⊢ A)
    → trav 𝒦 σ (convᵀ p M) ≡ convᵀ p (trav 𝒦 σ M)
  trav-conv 𝒦 σ refl M = refl

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x' y y' z z'}
    → x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
  cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- Two traversals of the type variables fuse
------------------------------------------------------------------------

fuseᵀ : TyLaws.Fuseᵀ
fuseᵀ h `true = true-≅ (FuseHypᵀ.ctx h)
fuseᵀ h `false = false-≅ (FuseHypᵀ.ctx h)
fuseᵀ h `zero = zero-≅ (FuseHypᵀ.ctx h)
fuseᵀ h (`suc M) = suc-≅ (FuseHypᵀ.ctx h) (fuseᵀ h M)
fuseᵀ h (`case-nat {A = A} L M N) =
  case-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h A) (fuseᵀ h L) (fuseᵀ h M)
    (fuseᵀ (fuseᵀ-ext h) N)
fuseᵀ h (`if_then_else {A = A} L M N) =
  if-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h A) (fuseᵀ h L) (fuseᵀ h M) (fuseᵀ h N)
fuseᵀ h (`_ {A = A} x) =
  `-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h A) (FuseHypᵀ.var h x)
fuseᵀ h (ƛ_˙_ {B = B} A N) =
  ƛ-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h A) (fuseᵀ-ty h B) (fuseᵀ (fuseᵀ-ext h) N)
fuseᵀ h (_·_ {A = A} {B = B} L M) =
  ·-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty h A) (fuseᵀ-ty h B) (fuseᵀ h L)
    (fuseᵀ h M)
fuseᵀ h (Λ_ {A = A} N) =
  Λ-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty (fuseᵀ-⇑ h) A) (fuseᵀ (fuseᵀ-⇑ h) N)
fuseᵀ {𝒯₁ = 𝒯₁} {𝒯₂} {𝒯₃} {θ₁ = θ₁} {θ₂} {θ₃} {ρ₁ = ρ₁} {ρ₂} {ρ₃} h
  (_∙_ {A = A} M B) =
  H.trans
    (travᵀ-conv 𝒯₂ θ₂ ρ₂ (sym (act-[] 𝒯₁ θ₁ A B))
      (travᵀ 𝒯₁ θ₁ ρ₁ M ∙ act 𝒯₁ θ₁ B))
    (H.trans
      (convᵀ-≅
        (sym (act-[] 𝒯₂ θ₂ (act 𝒯₁ (TK.exts (TyKit.kit 𝒯₁) θ₁) A)
                (act 𝒯₁ θ₁ B)))
        (travᵀ 𝒯₂ θ₂ ρ₂ (travᵀ 𝒯₁ θ₁ ρ₁ M) ∙ act 𝒯₂ θ₂ (act 𝒯₁ θ₁ B)))
      (H.trans
        (∙-≅ (FuseHypᵀ.ctx h) (fuseᵀ-ty (fuseᵀ-⇑ h) A) (fuseᵀ-ty h B)
          (fuseᵀ h M))
        (H.sym (convᵀ-≅ (sym (act-[] 𝒯₃ θ₃ A B))
                 (travᵀ 𝒯₃ θ₃ ρ₃ M ∙ act 𝒯₃ θ₃ B)))))
  where open Relation.Binary.PropositionalEquality using (sym)

------------------------------------------------------------------------
-- A traversal of the type variables that is the identity on variables
------------------------------------------------------------------------

idᵀ : TyLaws.Idᵀ
idᵀ h `true = true-≅ (IdHypᵀ.ctx h)
idᵀ h `false = false-≅ (IdHypᵀ.ctx h)
idᵀ h `zero = zero-≅ (IdHypᵀ.ctx h)
idᵀ h (`suc M) = suc-≅ (IdHypᵀ.ctx h) (idᵀ h M)
idᵀ h (`case-nat {A = A} L M N) =
  case-≅ (IdHypᵀ.ctx h) (idᵀ-ty h A) (idᵀ h L) (idᵀ h M) (idᵀ (idᵀ-ext h) N)
idᵀ h (`if_then_else {A = A} L M N) =
  if-≅ (IdHypᵀ.ctx h) (idᵀ-ty h A) (idᵀ h L) (idᵀ h M) (idᵀ h N)
idᵀ h (`_ {A = A} x) = `-≅ (IdHypᵀ.ctx h) (idᵀ-ty h A) (IdHypᵀ.var h x)
idᵀ h (ƛ_˙_ {B = B} A N) =
  ƛ-≅ (IdHypᵀ.ctx h) (idᵀ-ty h A) (idᵀ-ty h B) (idᵀ (idᵀ-ext h) N)
idᵀ h (_·_ {A = A} {B = B} L M) =
  ·-≅ (IdHypᵀ.ctx h) (idᵀ-ty h A) (idᵀ-ty h B) (idᵀ h L) (idᵀ h M)
idᵀ h (Λ_ {A = A} N) =
  Λ-≅ (IdHypᵀ.ctx h) (idᵀ-ty (idᵀ-⇑ h) A) (idᵀ (idᵀ-⇑ h) N)
idᵀ {𝒯 = 𝒯} {θ = θ} {ρ = ρ} h (_∙_ {A = A} M B) =
  H.trans (convᵀ-≅ (sym (act-[] 𝒯 θ A B)) (travᵀ 𝒯 θ ρ M ∙ act 𝒯 θ B))
    (∙-≅ (IdHypᵀ.ctx h) (idᵀ-ty (idᵀ-⇑ h) A) (idᵀ-ty h B) (idᵀ h M))
  where open Relation.Binary.PropositionalEquality using (sym)

------------------------------------------------------------------------
-- Traversals of the term variables commute with those of the type
-- variables
------------------------------------------------------------------------

commute : SubLaws.Commute
commute 𝒦 𝒯 R R-exts R-⇑ R-var = go
  where
  go : ∀ {Δ Δ'} {θ : TK.Sub (TyKit.kit 𝒯) Δ Δ'}
    {Γ Γ₁ : Ctx Δ} {Γ' Γ₁' : Ctx Δ'}
    {σ : Sub 𝒦 Γ Γ₁} {ρ : TyRen 𝒯 θ Γ Γ'}
    {ρ₁ : TyRen 𝒯 θ Γ₁ Γ₁'} {σ' : Sub 𝒦 Γ' Γ₁'}
    → R σ ρ ρ₁ σ'
    → ∀ {A} (M : Δ ∣ Γ ⊢ A)
    → trav 𝒦 σ' (travᵀ 𝒯 θ ρ M) ≡ travᵀ 𝒯 θ ρ₁ (trav 𝒦 σ M)
  go r `true = refl
  go r `false = refl
  go r `zero = refl
  go r (`suc M) = cong `suc_ (go r M)
  go r (`case-nat L M N) =
    cong₃ `case-nat (go r L) (go r M) (go (R-exts r) N)
  go r (`if_then_else L M N) =
    cong₃ `if_then_else (go r L) (go r M) (go r N)
  go r (` x) = R-var r x
  go r (ƛ A ˙ N) = cong (ƛ _ ˙_) (go (R-exts r) N)
  go r (L · M) = cong₂ _·_ (go r L) (go r M)
  go r (Λ N) = cong Λ_ (go (R-⇑ r) N)
  go {θ = θ} {ρ = ρ} {σ' = σ'} r (_∙_ {A = A} M B) =
    trans (trav-conv 𝒦 σ' _ (travᵀ 𝒯 θ ρ M ∙ act 𝒯 θ B))
      (cong (λ X → convᵀ _ (X ∙ act 𝒯 θ B)) (go r M))
    where open Relation.Binary.PropositionalEquality using (trans)

------------------------------------------------------------------------
-- Two traversals of the term variables fuse
------------------------------------------------------------------------

fuse : SubLaws.Fuse
fuse 𝒦₁ 𝒦₂ 𝒦₃ R R-exts R-⇑ R-var = go
  where
  go : ∀ {Δ} {Γ Γ' Γ'' : Ctx Δ}
    {σ₁ : Sub 𝒦₁ Γ Γ'} {σ₂ : Sub 𝒦₂ Γ' Γ''} {σ₃ : Sub 𝒦₃ Γ Γ''}
    → R σ₁ σ₂ σ₃
    → ∀ {A} (M : Δ ∣ Γ ⊢ A)
    → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  go r `true = refl
  go r `false = refl
  go r `zero = refl
  go r (`suc M) = cong `suc_ (go r M)
  go r (`case-nat L M N) =
    cong₃ `case-nat (go r L) (go r M) (go (R-exts r) N)
  go r (`if_then_else L M N) =
    cong₃ `if_then_else (go r L) (go r M) (go r N)
  go r (` x) = R-var r x
  go r (ƛ A ˙ N) = cong (ƛ A ˙_) (go (R-exts r) N)
  go r (L · M) = cong₂ _·_ (go r L) (go r M)
  go r (Λ N) = cong Λ_ (go (R-⇑ r) N)
  go r (M ∙ B) = cong (_∙ B) (go r M)

------------------------------------------------------------------------
-- The identity substitution of terms
------------------------------------------------------------------------

sub-id : SubLaws.SubId
sub-id h `true = refl
sub-id h `false = refl
sub-id h `zero = refl
sub-id h (`suc M) = cong `suc_ (sub-id h M)
sub-id h (`case-nat L M N) =
  cong₃ `case-nat (sub-id h L) (sub-id h M)
    (sub-id (SubLaws.sub-id-exts h) N)
sub-id h (`if_then_else L M N) =
  cong₃ `if_then_else (sub-id h L) (sub-id h M) (sub-id h N)
sub-id h (` x) = h x
sub-id h (ƛ A ˙ N) = cong (ƛ A ˙_) (sub-id (SubLaws.sub-id-exts h) N)
sub-id h (L · M) = cong₂ _·_ (sub-id h L) (sub-id h M)
sub-id h (Λ N) = cong Λ_ (sub-id (SubLaws.sub-id-⇑s h) N)
sub-id h (M ∙ B) = cong (_∙ B) (sub-id h M)

------------------------------------------------------------------------
-- Everything else comes from the library
------------------------------------------------------------------------

open TyLaws.TypeLemmas fuseᵀ idᵀ public
open SubLaws.Lemmas fuseᵀ commute fuse sub-id public

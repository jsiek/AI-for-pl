module TermImprecisionIndexed where

-- File Charter:
--   * Structural term imprecision for extrinsic-inst PolyUpDown, indexed by
--   * context-indexed type imprecision.
--   * Defines precision contexts and the term-precision judgment without the
--   * cast-specific compatibility rules.
--   * Provides projections back to ordinary left/right typing derivations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; z≤n)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import ImprecisionIndexed
open import UpDown
open import Terms
open import TypeProperties
  using
    ( substᵗ-renameᵗ
    ; substᵗ-id
    ; renameᵗ-⇑ˢ
    ; renameᵗ-ν-src
    )

------------------------------------------------------------------------
-- Precision contexts
------------------------------------------------------------------------

Prec : ICtx → Set
Prec Ξ = Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] (Ξ ⊢ A ⊑ᵢ B)

PCtx : ICtx → Set
PCtx Ξ = List (Prec Ξ)

record TPEnv : Set where
  constructor ⟪_,_,_,_,_⟫
  field
    Δ : TyCtx
    Ψ : SealCtx
    store : Store
    Ξ : ICtx
    Γ : PCtx Ξ
open TPEnv public

extendᴾ : (E : TPEnv) → Prec (TPEnv.Ξ E) → TPEnv
extendᴾ E P =
  ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E , TPEnv.Ξ E , P ∷ TPEnv.Γ E ⟫

leftTy : ∀ {Ξ} → Prec Ξ → Ty
leftTy (A , B , p) = A

rightTy : ∀ {Ξ} → Prec Ξ → Ty
rightTy (A , B , p) = B

leftCtx : ∀ {Ξ} → PCtx Ξ → Ctx
leftCtx [] = []
leftCtx (P ∷ Γ) = leftTy P ∷ leftCtx Γ

rightCtx : ∀ {Ξ} → PCtx Ξ → Ctx
rightCtx [] = []
rightCtx (P ∷ Γ) = rightTy P ∷ rightCtx Γ

infix 4 _∋ₚ_⦂_
data _∋ₚ_⦂_ {Ξ : ICtx} : PCtx Ξ → Var → Prec Ξ → Set where
  Zₚ : ∀ {Γ P} →
    (P ∷ Γ) ∋ₚ zero ⦂ P

  Sₚ : ∀ {Γ P Q x} →
    Γ ∋ₚ x ⦂ P →
    (Q ∷ Γ) ∋ₚ suc x ⦂ P

lookup-left : ∀ {Ξ} {Γ : PCtx Ξ} {x A B} {p : Ξ ⊢ A ⊑ᵢ B} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  leftCtx Γ ∋ x ⦂ A
lookup-left Zₚ = Z
lookup-left (Sₚ h) = S (lookup-left h)

lookup-right : ∀ {Ξ} {Γ : PCtx Ξ} {x A B} {p : Ξ ⊢ A ⊑ᵢ B} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  rightCtx Γ ∋ x ⦂ B
lookup-right Zₚ = Z
lookup-right (Sₚ h) = S (lookup-right h)

------------------------------------------------------------------------
-- Type-binder lifting of precision contexts
------------------------------------------------------------------------

subst-as-renameᵗ : (ρ : Renameᵗ) → (A : Ty) → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
subst-as-renameᵗ ρ A =
  trans
    (sym (substᵗ-renameᵗ ρ (λ X → ＇ X) A))
    (substᵗ-id (renameᵗ ρ A))

⇑ᵗᴾ : ∀ {Ξ} → PCtx Ξ → PCtx (plain ∷ Ξ)
⇑ᵗᴾ [] = []
⇑ᵗᴾ ((A , B , p) ∷ Γ) = (⇑ᵗ A , ⇑ᵗ B , plain-weaken⊑ᵢ p) ∷ ⇑ᵗᴾ Γ

leftCtx-⇑ᵗᴾ : ∀ {Ξ} → (Γ : PCtx Ξ) → leftCtx (⇑ᵗᴾ Γ) ≡ ⤊ᵗ (leftCtx Γ)
leftCtx-⇑ᵗᴾ [] = refl
leftCtx-⇑ᵗᴾ ((A , B , p) ∷ Γ) = cong (renameᵗ suc A ∷_) (leftCtx-⇑ᵗᴾ Γ)

rightCtx-⇑ᵗᴾ : ∀ {Ξ} → (Γ : PCtx Ξ) → rightCtx (⇑ᵗᴾ Γ) ≡ ⤊ᵗ (rightCtx Γ)
rightCtx-⇑ᵗᴾ [] = refl
rightCtx-⇑ᵗᴾ ((A , B , p) ∷ Γ) = cong (renameᵗ suc B ∷_) (rightCtx-⇑ᵗᴾ Γ)

⇑ᵗᴱ : TPEnv → TPEnv
⇑ᵗᴱ E =
  ⟪ suc (TPEnv.Δ E) , TPEnv.Ψ E , ⟰ᵗ (TPEnv.store E) ,
    plain ∷ TPEnv.Ξ E , ⇑ᵗᴾ (TPEnv.Γ E) ⟫

------------------------------------------------------------------------
-- Term imprecision
------------------------------------------------------------------------

infix 4 _⊢_⊑_⦂_
data _⊢_⊑_⦂_ (E : TPEnv) :
    Term → Term → ∀ {A B} → TPEnv.Ξ E ⊢ A ⊑ᵢ B → Set where

  ⊑` : ∀ {x A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
    TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
    E ⊢ (` x) ⊑ (` x) ⦂ p

  ⊑ƛ : ∀ {A A′ B B′ M M′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A′ →
    extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ pB →
    E ⊢ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ ⊑ᵢ-⇒ A A′ B B′ pA pB

  ⊑· : ∀ {A A′ B B′ L L′ M M′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
    E ⊢ L ⊑ L′ ⦂ ⊑ᵢ-⇒ A A′ B B′ pA pB →
    E ⊢ M ⊑ M′ ⦂ pA →
    E ⊢ (L · M) ⊑ (L′ · M′) ⦂ pB

  ⊑Λ : ∀ {A B M M′} {p : (plain ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ B} →
    Value M →
    Value M′ →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    ⇑ᵗᴱ E ⊢ M ⊑ M′ ⦂ p →
    E ⊢ (Λ M) ⊑ (Λ M′) ⦂ ⊑ᵢ-∀ A B p

  ⊑⦂∀ : ∀ {A B M M′ T} {p : (plain ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ B} →
    E ⊢ M ⊑ M′ ⦂ ⊑ᵢ-∀ A B p →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂ substPlain⊑ᵢ T p

  ⊑⦂∀-ν : ∀ (A B : Ty) {M M′ T}
      (p : (ν-bound ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ ⇑ᵗ B) →
    {pT : TPEnv.Ξ E ⊢ A [ T ]ᵗ ⊑ᵢ B} →
    E ⊢ M ⊑ M′ ⦂ (⊑ᵢ-ν A B p) →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    (hT : WfTy 0 (TPEnv.Ψ E) T) →
    νClosedInstᵢ p pT →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ pT

  ⊑$ : ∀ {n} →
    E ⊢ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ (⊑ᵢ-‵ `ℕ)

  ⊑⊕ : ∀ {L L′ M M′} {op : Prim} →
    E ⊢ L ⊑ L′ ⦂ (⊑ᵢ-‵ `ℕ) →
    E ⊢ M ⊑ M′ ⦂ (⊑ᵢ-‵ `ℕ) →
    E ⊢ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ (⊑ᵢ-‵ `ℕ)

  ⊑up : ∀ {M M′ A A′ B B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} {u : Up} {u′ : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    E ⊢ (M up u) ⊑ (M′ up u′) ⦂ pB

  ⊑upL : ∀ {M M′ A A′ B}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ A′} {u : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
    E ⊢ (M up u) ⊑ M′ ⦂ pB

  ⊑upR : ∀ {M M′ A A′ B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ A ⊑ᵢ B′} {u′ : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    E ⊢ M ⊑ (M′ up u′) ⦂ pB

  ⊑down : ∀ {M M′ A A′ B B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} {d : Down} {d′ : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    E ⊢ (M down d) ⊑ (M′ down d′) ⦂ pB

  ⊑downL : ∀ {M M′ A A′ B}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ A′} {d : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
    E ⊢ (M down d) ⊑ M′ ⦂ pB

  ⊑downR : ∀ {M M′ A A′ B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ A ⊑ᵢ B′} {d′ : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    E ⊢ M ⊑ (M′ down d′) ⦂ pB

  ⊑blameR : ∀ {M A B ℓ} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A →
    E ⊢ M ⊑ (blame ℓ) ⦂ p

------------------------------------------------------------------------
-- Projections back to ordinary typing
------------------------------------------------------------------------

⊑-left-typed :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A
⊑-left-typed (⊑` h) = ⊢` (lookup-left h)
⊑-left-typed (⊑ƛ hA hA′ rel) = ⊢ƛ hA (⊑-left-typed rel)
⊑-left-typed (⊑· relL relM) = ⊢· (⊑-left-typed relL) (⊑-left-typed relM)
⊑-left-typed {E = E} (⊑Λ vM vM′ wfA wfB rel) =
  ⊢Λ vM
    (cong-⊢⦂ refl (leftCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl (⊑-left-typed rel))
⊑-left-typed (⊑⦂∀ rel wfA wfB hT) =
  ⊢• (⊑-left-typed rel) wfA hT
⊑-left-typed (⊑⦂∀-ν A B {T = T} p rel wfA hT inst) =
  ⊢• (⊑-left-typed rel) wfA (WfTy-weakenᵗ hT z≤n)
⊑-left-typed (⊑$ {n}) = ⊢$ (κℕ n)
⊑-left-typed (⊑⊕ {op = op} relL relM) = ⊢⊕ (⊑-left-typed relL) op (⊑-left-typed relM)
⊑-left-typed (⊑up Φ lenΦ rel hu hu′) = ⊢up Φ lenΦ (⊑-left-typed rel) hu
⊑-left-typed (⊑upL Φ lenΦ rel hu) = ⊢up Φ lenΦ (⊑-left-typed rel) hu
⊑-left-typed (⊑upR Φ lenΦ rel hu′) = ⊑-left-typed rel
⊑-left-typed (⊑down Φ lenΦ rel hd hd′) = ⊢down Φ lenΦ (⊑-left-typed rel) hd
⊑-left-typed (⊑downL Φ lenΦ rel hd) = ⊢down Φ lenΦ (⊑-left-typed rel) hd
⊑-left-typed (⊑downR Φ lenΦ rel hd′) = ⊑-left-typed rel
⊑-left-typed (⊑blameR hM) = hM

⊑-right-typed :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ rightCtx (TPEnv.Γ E) ⊢ M′ ⦂ B
⊑-right-typed (⊑` h) = ⊢` (lookup-right h)
⊑-right-typed (⊑ƛ hA hA′ rel) = ⊢ƛ hA′ (⊑-right-typed rel)
⊑-right-typed (⊑· relL relM) = ⊢· (⊑-right-typed relL) (⊑-right-typed relM)
⊑-right-typed {E = E} (⊑Λ vM vM′ wfA wfB rel) =
  ⊢Λ vM′
    (cong-⊢⦂ refl (rightCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl (⊑-right-typed rel))
⊑-right-typed (⊑⦂∀ rel wfA wfB hT) =
  ⊢• (⊑-right-typed rel) wfB hT
⊑-right-typed (⊑⦂∀-ν A B {T = T} p rel wfA hT inst) =
  ⊑-right-typed rel
⊑-right-typed (⊑$ {n}) = ⊢$ (κℕ n)
⊑-right-typed (⊑⊕ {op = op} relL relM) = ⊢⊕ (⊑-right-typed relL) op (⊑-right-typed relM)
⊑-right-typed (⊑up Φ lenΦ rel hu hu′) = ⊢up Φ lenΦ (⊑-right-typed rel) hu′
⊑-right-typed (⊑upL Φ lenΦ rel hu) = ⊑-right-typed rel
⊑-right-typed (⊑upR Φ lenΦ rel hu′) = ⊢up Φ lenΦ (⊑-right-typed rel) hu′
⊑-right-typed (⊑down Φ lenΦ rel hd hd′) = ⊢down Φ lenΦ (⊑-right-typed rel) hd′
⊑-right-typed (⊑downL Φ lenΦ rel hd) = ⊑-right-typed rel
⊑-right-typed (⊑downR Φ lenΦ rel hd′) = ⊢down Φ lenΦ (⊑-right-typed rel) hd′
⊑-right-typed (⊑blameR hM) = ⊢blame _

⊑-type-imprecision :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Ξ E ⊢ A ⊑ᵢ B
⊑-type-imprecision {p = p} rel = p

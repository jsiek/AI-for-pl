module TermImprecisionIndexed where

-- File Charter:
--   * Structural term imprecision for extrinsic-inst PolyUpDown, indexed by
--     context-indexed type imprecision.
--   * Defines imprecision contexts and the term-imprecision judgment without 
--     the cast-specific compatibility rules.
--   * Provides projections back to ordinary left/right typing derivations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import ImprecisionIndexed
open import Store using (_⊆ˢ_)
open import UpDown
open import Terms
open import TypeProperties
  using
    ( substᵗ-renameᵗ
    ; substᵗ-id
    ; renameᵗ-⇑ˢ
    ; renameᵗ-ν-src
    )
open import PreservationFresh
  using
    ( length-append-tag
    ; wkΨ-term-suc
    ; wkΨ-cast-tag-⊑
    ; wkΨ-cast-tag-⊒
    )

------------------------------------------------------------------------
-- Imprecision contexts
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
-- Type-binder lifting of imprecision contexts
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
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ rightCtx (TPEnv.Γ E) ⊢ M ⦂ B →
    E ⊢ (blame ℓ) ⊑ M ⦂ p

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
⊑-left-typed (⊑blameR hM) = ⊢blame _

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
⊑-right-typed (⊑blameR hM) = hM

⊑-type-imprecision :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Ξ E ⊢ A ⊑ᵢ B
⊑-type-imprecision {p = p} rel = p

------------------------------------------------------------------------
-- Store and seal-context weakening
------------------------------------------------------------------------

wkΣ-⊑ :
  ∀ {E Σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , TPEnv.Ψ E , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΣ-⊑ w (⊑` h) = ⊑` h
wkΣ-⊑ w (⊑ƛ hA hA′ rel) = ⊑ƛ hA hA′ (wkΣ-⊑ w rel)
wkΣ-⊑ w (⊑· relL relM) = ⊑· (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ vM vM′ wfA wfB (wkΣ-⊑ (inst-⟰ᵗ-⊆ˢ w) rel)
wkΣ-⊑ w (⊑⦂∀ rel wfA wfB hT) = ⊑⦂∀ (wkΣ-⊑ w rel) wfA wfB hT
wkΣ-⊑ w (⊑⦂∀-ν A B p rel wfA hT inst) =
  ⊑⦂∀-ν A B p (wkΣ-⊑ w rel) wfA hT inst
wkΣ-⊑ w (⊑$ {n}) = ⊑$
wkΣ-⊑ w (⊑⊕ relL relM) = ⊑⊕ (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑up Φ lenΦ rel hu hu′) =
  ⊑up Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu) (wk⊑ w hu′)
wkΣ-⊑ w (⊑upL Φ lenΦ rel hu) = ⊑upL Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu)
wkΣ-⊑ w (⊑upR Φ lenΦ rel hu′) = ⊑upR Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu′)
wkΣ-⊑ w (⊑down Φ lenΦ rel hd hd′) =
  ⊑down Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd) (wk⊒ w hd′)
wkΣ-⊑ w (⊑downL Φ lenΦ rel hd) =
  ⊑downL Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd)
wkΣ-⊑ w (⊑downR Φ lenΦ rel hd′) =
  ⊑downR Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd′)
wkΣ-⊑ w (⊑blameR hM) = ⊑blameR (wkΣ-term w hM)

wkΨ-⊑-suc :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , suc (TPEnv.Ψ E) , TPEnv.store E ,
    TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΨ-⊑-suc (⊑` h) = ⊑` h
wkΨ-⊑-suc (⊑ƛ hA hA′ rel) =
  ⊑ƛ (WfTy-weakenˢ hA (n≤1+n _))
      (WfTy-weakenˢ hA′ (n≤1+n _))
      (wkΨ-⊑-suc rel)
wkΨ-⊑-suc (⊑· relL relM) = ⊑· (wkΨ-⊑-suc relL) (wkΨ-⊑-suc relM)
wkΨ-⊑-suc (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ vM vM′
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ wfB (n≤1+n _))
    (wkΨ-⊑-suc rel)
wkΨ-⊑-suc (⊑⦂∀ rel wfA wfB hT) =
  ⊑⦂∀ (wkΨ-⊑-suc rel)
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ wfB (n≤1+n _))
    (WfTy-weakenˢ hT (n≤1+n _))
wkΨ-⊑-suc {E = E} {M = M} {M′ = M′}
    (⊑⦂∀-ν A B {T = T} p rel wfA hT inst) =
  ⊑⦂∀-ν A B p
    (wkΨ-⊑-suc rel)
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ hT (n≤1+n _))
    inst
wkΨ-⊑-suc (⊑$ {n}) = ⊑$
wkΨ-⊑-suc (⊑⊕ relL relM) = ⊑⊕ (wkΨ-⊑-suc relL) (wkΨ-⊑-suc relM)
wkΨ-⊑-suc (⊑up Φ lenΦ rel hu hu′) =
  ⊑up
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu)
    (wkΨ-cast-tag-⊑ hu′)
wkΨ-⊑-suc (⊑upL Φ lenΦ rel hu) =
  ⊑upL
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu)
wkΨ-⊑-suc (⊑upR Φ lenΦ rel hu′) =
  ⊑upR
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu′)
wkΨ-⊑-suc (⊑down Φ lenΦ rel hd hd′) =
  ⊑down
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd)
    (wkΨ-cast-tag-⊒ hd′)
wkΨ-⊑-suc (⊑downL Φ lenΦ rel hd) =
  ⊑downL
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd)
wkΨ-⊑-suc (⊑downR Φ lenΦ rel hd′) =
  ⊑downR
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd′)
wkΨ-⊑-suc (⊑blameR hM) = ⊑blameR (wkΨ-term-suc hM)

wkΨ-⊑-+ :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  (k : ℕ) →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , (k + TPEnv.Ψ E) , TPEnv.store E ,
    TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΨ-⊑-+ zero rel = rel
wkΨ-⊑-+ (suc k) rel = wkΨ-⊑-suc (wkΨ-⊑-+ k rel)

wkΨ-⊑-≤ :
  ∀ {E Ψ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Ψ E ≤ Ψ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , Ψ′ , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΨ-⊑-≤ {E} {Ψ′} Ψ≤ rel =
  subst
    (λ q →
      (⟪ TPEnv.Δ E , q , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
        _ ⊑ _ ⦂ _)
    (trans (+-comm (Ψ′ ∸ TPEnv.Ψ E) (TPEnv.Ψ E))
           (m+[n∸m]≡n Ψ≤))
    (wkΨ-⊑-+ (Ψ′ ∸ TPEnv.Ψ E) rel)

wkΨΣ-⊑ :
  ∀ {E Ψ′ Σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Ψ E ≤ Ψ′ →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , Ψ′ , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΨΣ-⊑ Ψ≤ w rel = wkΣ-⊑ w (wkΨ-⊑-≤ Ψ≤ rel)

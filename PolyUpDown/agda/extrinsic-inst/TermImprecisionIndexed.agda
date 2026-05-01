module TermImprecisionIndexed where

-- File Charter:
--   * Structural term imprecision for extrinsic-inst PolyUpDown, indexed by
--     the endpoint types of context-indexed type imprecision.
--   * Defines imprecision contexts and the term-imprecision judgment without 
--     the cast-specific compatibility rules.
--   * Provides projections back to ordinary left/right typing derivations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; z<s; s<s; s≤s)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeCheckDec using (raiseVarFrom)
open import Ctx using (⤊ᵗ)
open import ImprecisionIndexed
open import Store using (_⊆ˢ_)
open import Store using (renameStoreᵗ-ext-⟰ᵗ)
open import UpDown
open import Terms
open import TermProperties using
  ( Renameˣ
  ; Renameˣ-wt
  ; Substˣ
  ; Substˣ-wt
  ; substˣ-term
  ; renameˣᵐ
  ; renameˣᵐ-value
  ; renameᵗᵐ-cong
  ; renameˣ-term-wt
  ; substˣ-term-value
  ; substˣ-term-wt
  ; extʳ
  ; liftᵗʳ
  ; extˣ
  ; ↑ᵗᵐ
  ; wkʳ
  ; singleVarEnv
  ; _[_]
  )
open import TypeProperties
  using
    ( substᵗ-renameᵗ
    ; substᵗ-cong
    ; substᵗ-id
    ; renameᵗ-substᵗ
    ; renameᵗ-preserves-WfTy
    ; TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
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
  constructor ⟪_,_,_,_,_,_,_⟫
  field
    Δ : TyCtx
    Ψ : SealCtx
    store : Store
    Ξ : ICtx
    Γ : PCtx Ξ
    plainΞ : PlainCtx Ξ
    lenΞ : Δ ≡ length Ξ
open TPEnv public

TPEnv-refl⊑ᵢ :
  ∀ E {T} →
  WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
  TPEnv.Ξ E ⊢ T ⊑ᵢ T
TPEnv-refl⊑ᵢ E {T} hT =
  ⊑ᵢ-refl-plain (TPEnv.plainΞ E)
    (subst (λ Δ → WfTy Δ (TPEnv.Ψ E) T) (TPEnv.lenΞ E) hT)

extendᴾ : (E : TPEnv) → Prec (TPEnv.Ξ E) → TPEnv
extendᴾ E P =
  ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E , TPEnv.Ξ E ,
    P ∷ TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫

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
    plain ∷ TPEnv.Ξ E , ⇑ᵗᴾ (TPEnv.Γ E) ,
    plain-∷ (TPEnv.plainΞ E) , cong suc (TPEnv.lenΞ E) ⟫

------------------------------------------------------------------------
-- Term imprecision
------------------------------------------------------------------------

infix 4 _⊢_⊑_⦂_⊑_
data _⊢_⊑_⦂_⊑_ (E : TPEnv) :
    Term → Term → Ty → Ty → Set where

  ⊑` : ∀ {x A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
    TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
    E ⊢ (` x) ⊑ (` x) ⦂ A ⊑ B

  ⊑ƛ : ∀ {A A′ B B′ M M′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A′ →
    extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
    E ⊢ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ A ⇒ B ⊑ A′ ⇒ B′

  ⊑· : ∀ {A A′ B B′ L L′ M M′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
    E ⊢ L ⊑ L′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    E ⊢ (L · M) ⊑ (L′ · M′) ⦂ B ⊑ B′

  ⊑Λ : ∀ {A B M M′} {p : (plain ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ B} →
    Value M →
    Value M′ →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    ⇑ᵗᴱ E ⊢ M ⊑ M′ ⦂ A ⊑ B →
    E ⊢ (Λ M) ⊑ (Λ M′) ⦂ `∀ A ⊑ `∀ B

  ⊑⦂∀ : ∀ {A B M M′ T} {p : (plain ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ B} →
    E ⊢ M ⊑ M′ ⦂ `∀ A ⊑ `∀ B →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    (hT : WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T) →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂
      A [ T ]ᵗ ⊑ B [ T ]ᵗ

  ⊑⦂∀-ν : ∀ (A B : Ty) {M M′ T}
      (p : (ν-bound ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ ⇑ᵗ B) →
    {occ : occurs zero A ≡ true} →
    {pT : TPEnv.Ξ E ⊢ A [ T ]ᵗ ⊑ᵢ B} →
    E ⊢ M ⊑ M′ ⦂ `∀ A ⊑ B →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    (hT : WfTy 0 (TPEnv.Ψ E) T) →
    νClosedInstᵢ p pT →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ A [ T ]ᵗ ⊑ B

  ⊑$ : ∀ {n} →
    E ⊢ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ ‵ `ℕ ⊑ ‵ `ℕ

  ⊑⊕ : ∀ {L L′ M M′} {op : Prim} →
    E ⊢ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ →
    E ⊢ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ →
    E ⊢ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ ‵ `ℕ ⊑ ‵ `ℕ

  ⊑up : ∀ {M M′ A A′ B B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} {u : Up} {u′ : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    E ⊢ (M up u) ⊑ (M′ up u′) ⦂ B ⊑ B′

  ⊑upL : ∀ {M M′ A A′ B}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ A′} {u : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
    E ⊢ (M up u) ⊑ M′ ⦂ B ⊑ A′

  ⊑upR : ∀ {M M′ A A′ B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ A ⊑ᵢ B′} {u′ : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    E ⊢ M ⊑ (M′ up u′) ⦂ A ⊑ B′

  ⊑down : ∀ {M M′ A A′ B B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} {d : Down} {d′ : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    E ⊢ (M down d) ⊑ (M′ down d′) ⦂ B ⊑ B′

  ⊑downL : ∀ {M M′ A A′ B}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ A′} {d : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
    E ⊢ (M down d) ⊑ M′ ⦂ B ⊑ A′

  ⊑downR : ∀ {M M′ A A′ B′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ A ⊑ᵢ B′} {d′ : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    E ⊢ M ⊑ (M′ down d′) ⦂ A ⊑ B′

  ⊑blameR : ∀ {M A B ℓ} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ rightCtx (TPEnv.Γ E) ⊢ M ⦂ B →
    E ⊢ (blame ℓ) ⊑ M ⦂ A ⊑ B

⊑-transport-env :
  ∀ {E E′ M M′ A B} →
  (eqE : E ≡ E′) →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  E′ ⊢ M ⊑ M′ ⦂ A ⊑ B
⊑-transport-env refl rel = rel

⊑-index-cast :
  ∀ {E M M′ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  E ⊢ M ⊑ M′ ⦂ A′ ⊑ B′
⊑-index-cast refl refl rel = rel

------------------------------------------------------------------------
-- Projections back to ordinary typing
------------------------------------------------------------------------

⊑-left-typed :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
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
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
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
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  TPEnv.Ξ E ⊢ A ⊑ᵢ B
⊑-type-imprecision (⊑` {p = p} h) = p
⊑-type-imprecision (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ᵢ-⇒ _ _ _ _ pA pB
⊑-type-imprecision (⊑· {pB = pB} relL relM) = pB
⊑-type-imprecision (⊑Λ {p = p} vM vM′ wfA wfB rel) = ⊑ᵢ-∀ _ _ p
⊑-type-imprecision {E = E} (⊑⦂∀ {T = T} {p = p} rel wfA wfB hT) =
  substPlain⊑ᵢ T (TPEnv-refl⊑ᵢ E hT) p
⊑-type-imprecision (⊑⦂∀-ν A B p {pT = pT} rel wfA hT inst) = pT
⊑-type-imprecision ⊑$ = ⊑ᵢ-‵ `ℕ
⊑-type-imprecision (⊑⊕ relL relM) = ⊑ᵢ-‵ `ℕ
⊑-type-imprecision (⊑up {pB = pB} Φ lenΦ rel hu hu′) = pB
⊑-type-imprecision (⊑upL {pB = pB} Φ lenΦ rel hu) = pB
⊑-type-imprecision (⊑upR {pB = pB} Φ lenΦ rel hu′) = pB
⊑-type-imprecision (⊑down {pB = pB} Φ lenΦ rel hd hd′) = pB
⊑-type-imprecision (⊑downL {pB = pB} Φ lenΦ rel hd) = pB
⊑-type-imprecision (⊑downR {pB = pB} Φ lenΦ rel hd′) = pB
⊑-type-imprecision (⊑blameR {p = p} hM) = p

------------------------------------------------------------------------
-- Term-variable renaming and substitution for term imprecision
------------------------------------------------------------------------

replaceΓᴾ : (E : TPEnv) → PCtx (TPEnv.Ξ E) → TPEnv
replaceΓᴾ E Γ′ =
  ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E , TPEnv.Ξ E ,
    Γ′ , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫

Renameᴾ : ∀ {Ξ} → PCtx Ξ → PCtx Ξ → Renameˣ → Set
Renameᴾ Γ Γ′ ρ =
  ∀ {x P} →
  Γ ∋ₚ x ⦂ P →
  Γ′ ∋ₚ ρ x ⦂ P

PCtxRel : ∀ {Ξ} → PCtx Ξ → PCtx Ξ → Set
PCtxRel {Ξ} Γ Γ′ =
  ∀ {x A B p} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ] Σ[ q ∈ (Ξ ⊢ A′ ⊑ᵢ B′) ]
    (A ≡ A′ × B ≡ B′ × Γ′ ∋ₚ x ⦂ (A′ , B′ , q))

renameˣᵐ-id-on :
  ∀ ρ →
  (∀ x → ρ x ≡ x) →
  ∀ M →
  renameˣᵐ ρ M ≡ M
renameˣᵐ-id-on ρ hρ (` x) = cong (λ y → ` y) (hρ x)
renameˣᵐ-id-on ρ hρ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_) (renameˣᵐ-id-on (extʳ ρ) h-ext M)
  where
    h-ext : ∀ x → extʳ ρ x ≡ x
    h-ext zero = refl
    h-ext (suc x) = cong suc (hρ x)
renameˣᵐ-id-on ρ hρ (L · M) =
  cong₂ _·_ (renameˣᵐ-id-on ρ hρ L) (renameˣᵐ-id-on ρ hρ M)
renameˣᵐ-id-on ρ hρ (Λ M) =
  cong (λ N → Λ N) (renameˣᵐ-id-on (liftᵗʳ ρ) hρ M)
renameˣᵐ-id-on ρ hρ (M ⦂∀ B [ T ]) =
  cong (λ N → N ⦂∀ B [ T ]) (renameˣᵐ-id-on ρ hρ M)
renameˣᵐ-id-on ρ hρ ($ κ) = refl
renameˣᵐ-id-on ρ hρ (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
        (renameˣᵐ-id-on ρ hρ L) (renameˣᵐ-id-on ρ hρ M)
renameˣᵐ-id-on ρ hρ (M up p) =
  cong (_up p) (renameˣᵐ-id-on ρ hρ M)
renameˣᵐ-id-on ρ hρ (M down p) =
  cong (_down p) (renameˣᵐ-id-on ρ hρ M)
renameˣᵐ-id-on ρ hρ (blame ℓ) = refl

renameˣᵐ-id :
  ∀ M →
  renameˣᵐ (λ x → x) M ≡ M
renameˣᵐ-id M = renameˣᵐ-id-on (λ x → x) (λ x → refl) M

lookup-right-inv :
  ∀ {Ξ} {Γ : PCtx Ξ} {x B} →
  rightCtx Γ ∋ x ⦂ B →
  Σ[ A ∈ Ty ] Σ[ p ∈ (Ξ ⊢ A ⊑ᵢ B) ] (Γ ∋ₚ x ⦂ (A , B , p))
lookup-right-inv {Γ = (A , B , p) ∷ Γ} Z = A , p , Zₚ
lookup-right-inv {Γ = P ∷ Γ} (S h) with lookup-right-inv {Γ = Γ} h
lookup-right-inv {Γ = P ∷ Γ} (S h) | A , p , hₚ = A , p , Sₚ hₚ

renameᴾ-right-wt :
  ∀ {Ξ} {Γ Γ′ : PCtx Ξ} {ρ} →
  Renameᴾ Γ Γ′ ρ →
  Renameˣ-wt (rightCtx Γ) (rightCtx Γ′) ρ
renameᴾ-right-wt hρ h with lookup-right-inv h
renameᴾ-right-wt hρ h | A , p , hₚ = lookup-right (hρ hₚ)

PCtxRel-right-wt :
  ∀ {Ξ} {Γ Γ′ : PCtx Ξ} →
  PCtxRel Γ Γ′ →
  Renameˣ-wt (rightCtx Γ) (rightCtx Γ′) (λ x → x)
PCtxRel-right-wt hΓ h with lookup-right-inv h
PCtxRel-right-wt hΓ h | A , p , hₚ with hΓ hₚ
PCtxRel-right-wt hΓ h | A , p , hₚ | A′ , B′ , q , eqA , eqB , hₚ′ =
  subst (λ T → rightCtx _ ∋ _ ⦂ T) (sym eqB) (lookup-right hₚ′)

extʳᴾ :
  ∀ {Ξ Γ Γ′ ρ P} →
  Renameᴾ {Ξ} Γ Γ′ ρ →
  Renameᴾ (P ∷ Γ) (P ∷ Γ′) (extʳ ρ)
extʳᴾ hρ Zₚ = Zₚ
extʳᴾ hρ (Sₚ h) = Sₚ (hρ h)

⇑ᵗᴾ-∋ :
  ∀ {Ξ Γ x A B} {p : Ξ ⊢ A ⊑ᵢ B} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  ⇑ᵗᴾ Γ ∋ₚ x ⦂ (⇑ᵗ A , ⇑ᵗ B , plain-weaken⊑ᵢ p)
⇑ᵗᴾ-∋ Zₚ = Zₚ
⇑ᵗᴾ-∋ (Sₚ h) = Sₚ (⇑ᵗᴾ-∋ h)

⇑ᵗᴾ-un∋ :
  ∀ {Ξ Γ x P} →
  ⇑ᵗᴾ Γ ∋ₚ x ⦂ P →
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ[ p ∈ (Ξ ⊢ A ⊑ᵢ B) ]
    (P ≡ (⇑ᵗ A , ⇑ᵗ B , plain-weaken⊑ᵢ p) ×
     Γ ∋ₚ x ⦂ (A , B , p))
⇑ᵗᴾ-un∋ {Γ = (A , B , p) ∷ Γ} Zₚ = A , B , p , refl , Zₚ
⇑ᵗᴾ-un∋ {Γ = P ∷ Γ} (Sₚ h) with ⇑ᵗᴾ-un∋ h
⇑ᵗᴾ-un∋ {Γ = P ∷ Γ} (Sₚ h) | A , B , p , eq , h′ =
  A , B , p , eq , Sₚ h′

liftᵗʳᴾ :
  ∀ {Ξ Γ Γ′ ρ} →
  Renameᴾ {Ξ} Γ Γ′ ρ →
  Renameᴾ (⇑ᵗᴾ Γ) (⇑ᵗᴾ Γ′) ρ
liftᵗʳᴾ hρ h with ⇑ᵗᴾ-un∋ h
liftᵗʳᴾ hρ h | A , B , p , refl , h′ = ⇑ᵗᴾ-∋ (hρ h′)

ext-PCtxRel :
  ∀ {Ξ} {Γ Γ′ : PCtx Ξ} {A B} {p : Ξ ⊢ A ⊑ᵢ B} →
  PCtxRel Γ Γ′ →
  PCtxRel ((A , B , p) ∷ Γ) ((A , B , p) ∷ Γ′)
ext-PCtxRel hΓ Zₚ = _ , _ , _ , refl , refl , Zₚ
ext-PCtxRel hΓ (Sₚ h) with hΓ h
ext-PCtxRel hΓ (Sₚ h) | A′ , B′ , q , eqA , eqB , h′ =
  A′ , B′ , q , eqA , eqB , Sₚ h′

liftᵗ-PCtxRel :
  ∀ {Ξ} {Γ Γ′ : PCtx Ξ} →
  PCtxRel Γ Γ′ →
  PCtxRel (⇑ᵗᴾ Γ) (⇑ᵗᴾ Γ′)
liftᵗ-PCtxRel hΓ h with ⇑ᵗᴾ-un∋ h
liftᵗ-PCtxRel hΓ h | A , B , p , refl , h′ with hΓ h′
liftᵗ-PCtxRel hΓ h | A , B , p , refl , h′
  | A′ , B′ , q , eqA , eqB , h″ =
  ⇑ᵗ A′ , ⇑ᵗ B′ , plain-weaken⊑ᵢ q ,
  cong ⇑ᵗ eqA , cong ⇑ᵗ eqB , ⇑ᵗᴾ-∋ h″

⊑-transport-PCtx :
  ∀ {E Γ′ M M′ A B} →
  PCtxRel (TPEnv.Γ E) Γ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  replaceΓᴾ E Γ′ ⊢ M ⊑ M′ ⦂ A ⊑ B
⊑-transport-PCtx hΓ (⊑` h) with hΓ h
⊑-transport-PCtx hΓ (⊑` h) | A′ , B′ , q , eqA , eqB , h′ =
  ⊑-index-cast (sym eqA) (sym eqB) (⊑` h′)
⊑-transport-PCtx hΓ (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB} hA hA′
    (⊑-transport-PCtx (ext-PCtxRel hΓ) rel)
⊑-transport-PCtx hΓ (⊑· {pA = pA} {pB = pB} relL relM) =
  ⊑· {pA = pA} {pB = pB}
    (⊑-transport-PCtx hΓ relL)
    (⊑-transport-PCtx hΓ relM)
⊑-transport-PCtx hΓ (⊑Λ {p = p} vM vM′ wfA wfB rel) =
  ⊑Λ {p = p} vM vM′ wfA wfB
    (⊑-transport-PCtx (liftᵗ-PCtxRel hΓ) rel)
⊑-transport-PCtx hΓ (⊑⦂∀ {p = p} rel wfA wfB hT) =
  ⊑⦂∀ {p = p} (⊑-transport-PCtx hΓ rel) wfA wfB hT
⊑-transport-PCtx hΓ (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (⊑-transport-PCtx hΓ rel) wfA hT inst
⊑-transport-PCtx hΓ ⊑$ = ⊑$
⊑-transport-PCtx hΓ (⊑⊕ relL relM) =
  ⊑⊕ (⊑-transport-PCtx hΓ relL) (⊑-transport-PCtx hΓ relM)
⊑-transport-PCtx hΓ (⊑up {pA = pA} {pB = pB} Φ lenΦ rel hu hu′) =
  ⊑up {pA = pA} {pB = pB} Φ lenΦ
    (⊑-transport-PCtx hΓ rel) hu hu′
⊑-transport-PCtx hΓ (⊑upL {pA = pA} {pB = pB} Φ lenΦ rel hu) =
  ⊑upL {pA = pA} {pB = pB} Φ lenΦ
    (⊑-transport-PCtx hΓ rel) hu
⊑-transport-PCtx hΓ (⊑upR {pA = pA} {pB = pB} Φ lenΦ rel hu′) =
  ⊑upR {pA = pA} {pB = pB} Φ lenΦ
    (⊑-transport-PCtx hΓ rel) hu′
⊑-transport-PCtx hΓ (⊑down {pA = pA} {pB = pB} Φ lenΦ rel hd hd′) =
  ⊑down {pA = pA} {pB = pB} Φ lenΦ
    (⊑-transport-PCtx hΓ rel) hd hd′
⊑-transport-PCtx hΓ (⊑downL {pA = pA} {pB = pB} Φ lenΦ rel hd) =
  ⊑downL {pA = pA} {pB = pB} Φ lenΦ
    (⊑-transport-PCtx hΓ rel) hd
⊑-transport-PCtx hΓ (⊑downR {pA = pA} {pB = pB} Φ lenΦ rel hd′) =
  ⊑downR {pA = pA} {pB = pB} Φ lenΦ
    (⊑-transport-PCtx hΓ rel) hd′
⊑-transport-PCtx {M′ = M′} hΓ (⊑blameR {p = p} hM) =
  ⊑blameR {p = p}
    (cong-⊢⦂ refl refl (renameˣᵐ-id M′) refl
      (renameˣ-term-wt (λ x → x) (PCtxRel-right-wt hΓ) hM))

renameˣ-⊑ :
  ∀ {E Γ′ ρ M M′ A B} →
  Renameᴾ (TPEnv.Γ E) Γ′ ρ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  replaceΓᴾ E Γ′ ⊢ renameˣᵐ ρ M ⊑ renameˣᵐ ρ M′ ⦂ A ⊑ B
renameˣ-⊑ hρ (⊑` {p = p} h) = ⊑` {p = p} (hρ h)
renameˣ-⊑ hρ (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB} hA hA′ (renameˣ-⊑ (extʳᴾ hρ) rel)
renameˣ-⊑ hρ (⊑· {pA = pA} {pB = pB} relL relM) =
  ⊑· {pA = pA} {pB = pB} (renameˣ-⊑ hρ relL) (renameˣ-⊑ hρ relM)
renameˣ-⊑ hρ (⊑Λ {p = p} vM vM′ wfA wfB rel) =
  ⊑Λ {p = p}
    (renameˣᵐ-value _ vM)
    (renameˣᵐ-value _ vM′)
    wfA
    wfB
    (renameˣ-⊑ (liftᵗʳᴾ hρ) rel)
renameˣ-⊑ hρ (⊑⦂∀ {p = p} rel wfA wfB hT) =
  ⊑⦂∀ {p = p} (renameˣ-⊑ hρ rel) wfA wfB hT
renameˣ-⊑ hρ (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (renameˣ-⊑ hρ rel) wfA hT inst
renameˣ-⊑ hρ (⊑$ {n}) = ⊑$
renameˣ-⊑ hρ (⊑⊕ relL relM) =
  ⊑⊕ (renameˣ-⊑ hρ relL) (renameˣ-⊑ hρ relM)
renameˣ-⊑ hρ (⊑up {pA = pA} {pB = pB} Φ lenΦ rel hu hu′) =
  ⊑up {pA = pA} {pB = pB} Φ lenΦ (renameˣ-⊑ hρ rel) hu hu′
renameˣ-⊑ hρ (⊑upL {pA = pA} {pB = pB} Φ lenΦ rel hu) =
  ⊑upL {pA = pA} {pB = pB} Φ lenΦ (renameˣ-⊑ hρ rel) hu
renameˣ-⊑ hρ (⊑upR {pA = pA} {pB = pB} Φ lenΦ rel hu′) =
  ⊑upR {pA = pA} {pB = pB} Φ lenΦ (renameˣ-⊑ hρ rel) hu′
renameˣ-⊑ hρ (⊑down {pA = pA} {pB = pB} Φ lenΦ rel hd hd′) =
  ⊑down {pA = pA} {pB = pB} Φ lenΦ (renameˣ-⊑ hρ rel) hd hd′
renameˣ-⊑ hρ (⊑downL {pA = pA} {pB = pB} Φ lenΦ rel hd) =
  ⊑downL {pA = pA} {pB = pB} Φ lenΦ (renameˣ-⊑ hρ rel) hd
renameˣ-⊑ hρ (⊑downR {pA = pA} {pB = pB} Φ lenΦ rel hd′) =
  ⊑downR {pA = pA} {pB = pB} Φ lenΦ (renameˣ-⊑ hρ rel) hd′
renameˣ-⊑ hρ (⊑blameR {p = p} hM) =
  ⊑blameR {p = p} (renameˣ-term-wt _ (renameᴾ-right-wt hρ) hM)

length-insertPlainAt-≤ :
  ∀ k Γ →
  k ≤ length Γ →
  length (insertPlainAt k Γ) ≡ suc (length Γ)
length-insertPlainAt-≤ zero Γ k≤ = refl
length-insertPlainAt-≤ (suc k) [] ()
length-insertPlainAt-≤ (suc k) (m ∷ Γ) (s≤s k≤) =
  cong suc (length-insertPlainAt-≤ k Γ k≤)

insertPlainAt-PlainCtx :
  ∀ k {Ξ} →
  k ≤ length Ξ →
  PlainCtx Ξ →
  PlainCtx (insertPlainAt k Ξ)
insertPlainAt-PlainCtx zero k≤ plainΞ = plain-∷ plainΞ
insertPlainAt-PlainCtx (suc k) {[]} () plain-[]
insertPlainAt-PlainCtx (suc k) {plain ∷ Ξ} (s≤s k≤) (plain-∷ plainΞ) =
  plain-∷ (insertPlainAt-PlainCtx k k≤ plainΞ)

raiseVarFrom-Wf :
  ∀ k {Δ} →
  TyRenameWf Δ (suc Δ) (raiseVarFrom k)
raiseVarFrom-Wf zero X<Δ = s<s X<Δ
raiseVarFrom-Wf (suc k) {X = zero} z<s = z<s
raiseVarFrom-Wf (suc k) {X = suc X} (s<s X<Δ) =
  s<s (raiseVarFrom-Wf k X<Δ)

raiseVarFrom-Wf0 :
  ∀ k →
  TyRenameWf 0 0 (raiseVarFrom k)
raiseVarFrom-Wf0 k ()

UIP :
  ∀ {A : Set} {x y : A} →
  (p q : x ≡ y) →
  p ≡ q
UIP refl refl = refl

renameStoreᵗ-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  ∀ Σ →
  renameStoreᵗ ρ Σ ≡ renameStoreᵗ ρ′ Σ
renameStoreᵗ-cong h [] = refl
renameStoreᵗ-cong h ((α , A) ∷ Σ) =
  cong₂ _∷_ (cong₂ _,_ refl (renameᵗ-cong h A))
    (renameStoreᵗ-cong h Σ)

renameᵗ-single-subst :
  ∀ ρ T A →
  (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ T ]ᵗ ≡
  renameᵗ ρ (A [ T ]ᵗ)
renameᵗ-single-subst ρ T A =
  trans
    (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (renameᵗ ρ T)) A)
    (trans (substᵗ-cong env A)
      (sym (renameᵗ-substᵗ ρ (singleTyEnv T) A)))
  where
    env :
      ∀ X →
      singleTyEnv (renameᵗ ρ T) (extᵗ ρ X) ≡
      renameᵗ ρ (singleTyEnv T X)
    env zero = refl
    env (suc X) = refl

plain-weakenAtᴾ : ∀ k {Ξ} → PCtx Ξ → PCtx (insertPlainAt k Ξ)
plain-weakenAtᴾ k [] = []
plain-weakenAtᴾ k ((A , B , p) ∷ Γ) =
  ( renameᵗ (raiseVarFrom k) A
  , renameᵗ (raiseVarFrom k) B
  , plain-weakenAt⊑ᵢ k p
  ) ∷ plain-weakenAtᴾ k Γ

plain-weakenAtᴾ-∋ :
  ∀ k {Ξ Γ x A B} {p : Ξ ⊢ A ⊑ᵢ B} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  plain-weakenAtᴾ k Γ ∋ₚ x ⦂
    ( renameᵗ (raiseVarFrom k) A
    , renameᵗ (raiseVarFrom k) B
    , plain-weakenAt⊑ᵢ k p
    )
plain-weakenAtᴾ-∋ k Zₚ = Zₚ
plain-weakenAtᴾ-∋ k (Sₚ h) = Sₚ (plain-weakenAtᴾ-∋ k h)

leftCtx-plain-weakenAtᴾ :
  ∀ k {Ξ} →
  (Γ : PCtx Ξ) →
  leftCtx (plain-weakenAtᴾ k Γ) ≡
  map (renameᵗ (raiseVarFrom k)) (leftCtx Γ)
leftCtx-plain-weakenAtᴾ k [] = refl
leftCtx-plain-weakenAtᴾ k ((A , B , p) ∷ Γ) =
  cong (renameᵗ (raiseVarFrom k) A ∷_) (leftCtx-plain-weakenAtᴾ k Γ)

rightCtx-plain-weakenAtᴾ :
  ∀ k {Ξ} →
  (Γ : PCtx Ξ) →
  rightCtx (plain-weakenAtᴾ k Γ) ≡
  map (renameᵗ (raiseVarFrom k)) (rightCtx Γ)
rightCtx-plain-weakenAtᴾ k [] = refl
rightCtx-plain-weakenAtᴾ k ((A , B , p) ∷ Γ) =
  cong (renameᵗ (raiseVarFrom k) B ∷_) (rightCtx-plain-weakenAtᴾ k Γ)

Prec-cast-eq :
  ∀ {Ξ A A′ B B′}
    {p : Ξ ⊢ A ⊑ᵢ B} {q : Ξ ⊢ A′ ⊑ᵢ B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  ⊑ᵢ-cast eqA eqB p ≡ q →
  (A , B , p) ≡ (A′ , B′ , q)
Prec-cast-eq refl refl refl = refl

plain-weakenAtᴾ-⇑-rel :
  ∀ k {Ξ} →
  (Γ : PCtx Ξ) →
  PCtxRel
    (plain-weakenAtᴾ (suc k) (⇑ᵗᴾ Γ))
    (⇑ᵗᴾ (plain-weakenAtᴾ k Γ))
plain-weakenAtᴾ-⇑-rel k [] ()
plain-weakenAtᴾ-⇑-rel k ((A , B , p) ∷ Γ) Zₚ =
  ⇑ᵗ (renameᵗ (raiseVarFrom k) A) ,
  ⇑ᵗ (renameᵗ (raiseVarFrom k) B) ,
  plain-weaken⊑ᵢ (plain-weakenAt⊑ᵢ k p) ,
  rename-raise-⇑ᵗ k A , rename-raise-⇑ᵗ k B , Zₚ
plain-weakenAtᴾ-⇑-rel k ((A , B , p) ∷ Γ) (Sₚ h)
    with plain-weakenAtᴾ-⇑-rel k Γ h
plain-weakenAtᴾ-⇑-rel k ((A , B , p) ∷ Γ) (Sₚ h)
    | A′ , B′ , q , eqA , eqB , h′ =
  A′ , B′ , q , eqA , eqB , Sₚ h′

plain-weakenAtᴱ :
  (E : TPEnv) →
  (k : ℕ) →
  k ≤ length (TPEnv.Ξ E) →
  TPEnv
plain-weakenAtᴱ E k k≤ =
  ⟪ suc (TPEnv.Δ E)
  , TPEnv.Ψ E
  , renameStoreᵗ (raiseVarFrom k) (TPEnv.store E)
  , insertPlainAt k (TPEnv.Ξ E)
  , plain-weakenAtᴾ k (TPEnv.Γ E)
  , insertPlainAt-PlainCtx k k≤ (TPEnv.plainΞ E)
  , trans (cong suc (TPEnv.lenΞ E))
      (sym (length-insertPlainAt-≤ k (TPEnv.Ξ E) k≤))
  ⟫

plain-weakenAtᴱ-⇑-srcΓ :
  ∀ k {E}
    (k≤ : k ≤ length (TPEnv.Ξ E)) →
  plain-weakenAtᴱ (⇑ᵗᴱ E) (suc k) (s≤s k≤) ≡
  replaceΓᴾ (⇑ᵗᴱ (plain-weakenAtᴱ E k k≤))
    (plain-weakenAtᴾ (suc k) (⇑ᵗᴾ (TPEnv.Γ E)))
plain-weakenAtᴱ-⇑-srcΓ k
    {E = ⟪ Δ , Ψ , Σ , Ξ , Γ , plainΞ , lenΞ ⟫} k≤
  rewrite trans
            (renameStoreᵗ-cong (λ X → sym (raise-ext k X)) (⟰ᵗ Σ))
            (renameStoreᵗ-ext-⟰ᵗ (raiseVarFrom k) Σ) =
  cong
    (λ len →
      ⟪ suc (suc Δ) , Ψ , ⟰ᵗ (renameStoreᵗ (raiseVarFrom k) Σ)
      , plain ∷ insertPlainAt k Ξ
      , plain-weakenAtᴾ (suc k) (⇑ᵗᴾ Γ)
      , plain-∷ (insertPlainAt-PlainCtx k k≤ plainΞ)
      , len
      ⟫)
    (UIP _ _)

plain-weakenAtᴾ-zero :
  ∀ {Ξ} →
  (Γ : PCtx Ξ) →
  plain-weakenAtᴾ zero Γ ≡ ⇑ᵗᴾ Γ
plain-weakenAtᴾ-zero [] = refl
plain-weakenAtᴾ-zero ((A , B , p) ∷ Γ) =
  cong₂ _∷_ refl (plain-weakenAtᴾ-zero Γ)

plain-weakenAtᴱ-zero :
  ∀ E →
  plain-weakenAtᴱ E zero z≤n ≡ ⇑ᵗᴱ E
plain-weakenAtᴱ-zero ⟪ Δ , Ψ , Σ , Ξ , Γ , plainΞ , lenΞ ⟫
  rewrite plain-weakenAtᴾ-zero Γ =
  cong
    (λ len →
      ⟪ suc Δ , Ψ , ⟰ᵗ Σ , plain ∷ Ξ , ⇑ᵗᴾ Γ ,
        plain-∷ plainΞ , len ⟫)
    (UIP _ _)

plain-weakenAt-⊑ :
  ∀ k {E M M′ A B}
    (k≤ : k ≤ length (TPEnv.Ξ E)) →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  plain-weakenAtᴱ E k k≤ ⊢
    renameᵗᵐ (raiseVarFrom k) M ⊑
    renameᵗᵐ (raiseVarFrom k) M′ ⦂
    renameᵗ (raiseVarFrom k) A ⊑ renameᵗ (raiseVarFrom k) B
plain-weakenAt-⊑ k k≤ (⊑` {p = p} h) =
  ⊑` {p = plain-weakenAt⊑ᵢ k p} (plain-weakenAtᴾ-∋ k h)
plain-weakenAt-⊑ k k≤ (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ƛ {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB}
    (renameᵗ-preserves-WfTy hA (raiseVarFrom-Wf k))
    (renameᵗ-preserves-WfTy hA′ (raiseVarFrom-Wf k))
    (plain-weakenAt-⊑ k k≤ rel)
plain-weakenAt-⊑ k k≤ (⊑· {pA = pA} {pB = pB} relL relM) =
  ⊑· {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB}
    (plain-weakenAt-⊑ k k≤ relL)
    (plain-weakenAt-⊑ k k≤ relM)
plain-weakenAt-⊑ k {E = E} {M = Λ M} {M′ = Λ M′}
    k≤ (⊑Λ {A = A} {B = B} {p = p} vM vM′ wfA wfB rel) =
  ⊑Λ
    {p =
      ⊑ᵢ-cast
        (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
        (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
        (plain-weakenAt⊑ᵢ (suc k) p)}
    (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM)
    (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM′)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseVarFrom-Wf k)))
    (renameᵗ-preserves-WfTy wfB (TyRenameWf-ext (raiseVarFrom-Wf k)))
    (⊑-transport-PCtx
      (plain-weakenAtᴾ-⇑-rel k (TPEnv.Γ E))
      (⊑-transport-env
        (plain-weakenAtᴱ-⇑-srcΓ k k≤)
        (⊑-index-cast
          (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
          (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
          (subst
            (λ N′ →
              plain-weakenAtᴱ (⇑ᵗᴱ E) (suc k) (s≤s k≤) ⊢
                renameᵗᵐ (extᵗ (raiseVarFrom k)) M ⊑ N′ ⦂
                renameᵗ (raiseVarFrom (suc k)) A ⊑
                renameᵗ (raiseVarFrom (suc k)) B)
            (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M′)
            (subst
              (λ N →
                plain-weakenAtᴱ (⇑ᵗᴱ E) (suc k) (s≤s k≤) ⊢
                  N ⊑ renameᵗᵐ (raiseVarFrom (suc k)) M′ ⦂
                  renameᵗ (raiseVarFrom (suc k)) A ⊑
                  renameᵗ (raiseVarFrom (suc k)) B)
              (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M)
              (plain-weakenAt-⊑ (suc k) (s≤s k≤) rel))))))
plain-weakenAt-⊑ k k≤ (⊑⦂∀ {A = A} {B = B} {T = T} {p = p}
    rel wfA wfB hT) =
  ⊑-index-cast
    (renameᵗ-single-subst (raiseVarFrom k) T A)
    (renameᵗ-single-subst (raiseVarFrom k) T B)
    (⊑⦂∀
      {p =
        ⊑ᵢ-cast
          (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
          (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
          (plain-weakenAt⊑ᵢ (suc k) p)}
      (plain-weakenAt-⊑ k k≤ rel)
      (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseVarFrom-Wf k)))
      (renameᵗ-preserves-WfTy wfB (TyRenameWf-ext (raiseVarFrom-Wf k)))
      (renameᵗ-preserves-WfTy hT (raiseVarFrom-Wf k)))
plain-weakenAt-⊑ k k≤
    (⊑⦂∀-ν A B {T = T} p {occ = occ} rel wfA hT inst) =
  ⊑-index-cast
    (renameᵗ-single-subst (raiseVarFrom k) T A)
    refl
    (⊑⦂∀-ν
      (renameᵗ (extᵗ (raiseVarFrom k)) A)
      (renameᵗ (raiseVarFrom k) B)
      (⊑ᵢ-cast
        (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
        (rename-raise-⇑ᵗ k B)
        (plain-weakenAt⊑ᵢ (suc k) p))
      {occ = trans (occurs-zero-rename-ext-raise k A) occ}
      (plain-weakenAt-⊑ k k≤ rel)
      (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseVarFrom-Wf k)))
      (renameᵗ-preserves-WfTy hT (raiseVarFrom-Wf0 k))
      (ν-close-inst-evidenceᵢ
        (renameᵗ-preserves-WfTy hT (raiseVarFrom-Wf0 k))
        (⊑ᵢ-cast
          (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
          (rename-raise-⇑ᵗ k B)
          (plain-weakenAt⊑ᵢ (suc k) p))))
plain-weakenAt-⊑ k k≤ (⊑$ {n}) = ⊑$
plain-weakenAt-⊑ k k≤ (⊑⊕ relL relM) =
  ⊑⊕
    (plain-weakenAt-⊑ k k≤ relL)
    (plain-weakenAt-⊑ k k≤ relM)
plain-weakenAt-⊑ k k≤ (⊑up {pA = pA} {pB = pB} Φ lenΦ rel hu hu′) =
  ⊑up {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB} Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu′)
plain-weakenAt-⊑ k k≤ (⊑upL {pA = pA} {pB = pB} Φ lenΦ rel hu) =
  ⊑upL {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB} Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu)
plain-weakenAt-⊑ k k≤ (⊑upR {pA = pA} {pB = pB} Φ lenΦ rel hu′) =
  ⊑upR {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB} Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu′)
plain-weakenAt-⊑ k k≤ (⊑down {pA = pA} {pB = pB} Φ lenΦ rel hd hd′) =
  ⊑down {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB} Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd′)
plain-weakenAt-⊑ k k≤ (⊑downL {pA = pA} {pB = pB} Φ lenΦ rel hd) =
  ⊑downL {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB} Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd)
plain-weakenAt-⊑ k k≤ (⊑downR {pA = pA} {pB = pB} Φ lenΦ rel hd′) =
  ⊑downR {pA = plain-weakenAt⊑ᵢ k pA}
    {pB = plain-weakenAt⊑ᵢ k pB} Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd′)
plain-weakenAt-⊑ k {E = E} k≤ (⊑blameR {p = p} hM) =
  ⊑blameR {p = plain-weakenAt⊑ᵢ k p}
    (cong-⊢⦂
      refl
      (sym (rightCtx-plain-weakenAtᴾ k (TPEnv.Γ E)))
      refl
      refl
      (renameᵗ-term (raiseVarFrom k) (raiseVarFrom-Wf k) hM))

plain-weaken-⊑ :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  ⇑ᵗᴱ E ⊢ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
plain-weaken-⊑ {E = E} rel =
  ⊑-transport-env
    (plain-weakenAtᴱ-zero E)
    (plain-weakenAt-⊑ zero {E = E} z≤n rel)

Substᴾ : (E : TPEnv) → PCtx (TPEnv.Ξ E) → Substˣ → Substˣ → Set
Substᴾ E Γ′ σ σ′ =
  ∀ {x A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
  replaceΓᴾ E Γ′ ⊢ σ x ⊑ σ′ x ⦂ A ⊑ B

substᴾ-right-wt :
  ∀ {E Γ′ σ σ′} →
  Substᴾ E Γ′ σ σ′ →
  Substˣ-wt {TPEnv.Δ E} {TPEnv.Ψ E} {TPEnv.store E}
    {rightCtx (TPEnv.Γ E)} {rightCtx Γ′} σ′
substᴾ-right-wt hσ h with lookup-right-inv h
substᴾ-right-wt hσ h | A , p , hₚ = ⊑-right-typed (hσ hₚ)

extˣᴾ :
  ∀ {E Γ′ σ σ′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  Substᴾ E Γ′ σ σ′ →
  Substᴾ (extendᴾ E (A , B , p)) ((A , B , p) ∷ Γ′)
    (extˣ σ) (extˣ σ′)
extˣᴾ hσ Zₚ = ⊑` Zₚ
extˣᴾ hσ (Sₚ h) = renameˣ-⊑ (λ q → Sₚ q) (hσ h)

↑ᵗᵐᴾ :
  ∀ {E Γ′ σ σ′} →
  Substᴾ E Γ′ σ σ′ →
  Substᴾ (⇑ᵗᴱ E) (⇑ᵗᴾ Γ′) (↑ᵗᵐ σ) (↑ᵗᵐ σ′)
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ξ , [] , plainΞ , lenΞ ⟫} hσ ()
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ξ , (A , B , p) ∷ Γ , plainΞ , lenΞ ⟫}
  hσ Zₚ =
  plain-weaken-⊑ (hσ Zₚ)
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ξ , P ∷ Γ , plainΞ , lenΞ ⟫}
  hσ (Sₚ h) =
  ↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ξ , Γ , plainΞ , lenΞ ⟫}
    (λ q → hσ (Sₚ q))
    h

subst-⊑ :
  ∀ {E Γ′ σ σ′ M M′ A B} →
  Substᴾ E Γ′ σ σ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  replaceΓᴾ E Γ′ ⊢ substˣ-term σ M ⊑ substˣ-term σ′ M′ ⦂ A ⊑ B
subst-⊑ hσ (⊑` {p = p} h) = hσ h
subst-⊑ hσ (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB} hA hA′ (subst-⊑ (extˣᴾ hσ) rel)
subst-⊑ hσ (⊑· {pA = pA} {pB = pB} relL relM) =
  ⊑· {pA = pA} {pB = pB} (subst-⊑ hσ relL) (subst-⊑ hσ relM)
subst-⊑ hσ (⊑Λ {p = p} vM vM′ wfA wfB rel) =
  ⊑Λ {p = p}
    (substˣ-term-value _ vM)
    (substˣ-term-value _ vM′)
    wfA
    wfB
    (subst-⊑ (↑ᵗᵐᴾ hσ) rel)
subst-⊑ hσ (⊑⦂∀ {p = p} rel wfA wfB hT) =
  ⊑⦂∀ {p = p} (subst-⊑ hσ rel) wfA wfB hT
subst-⊑ hσ (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (subst-⊑ hσ rel) wfA hT inst
subst-⊑ hσ (⊑$ {n}) = ⊑$
subst-⊑ hσ (⊑⊕ relL relM) =
  ⊑⊕ (subst-⊑ hσ relL) (subst-⊑ hσ relM)
subst-⊑ hσ (⊑up {pA = pA} {pB = pB} Φ lenΦ rel hu hu′) =
  ⊑up {pA = pA} {pB = pB} Φ lenΦ (subst-⊑ hσ rel) hu hu′
subst-⊑ hσ (⊑upL {pA = pA} {pB = pB} Φ lenΦ rel hu) =
  ⊑upL {pA = pA} {pB = pB} Φ lenΦ (subst-⊑ hσ rel) hu
subst-⊑ hσ (⊑upR {pA = pA} {pB = pB} Φ lenΦ rel hu′) =
  ⊑upR {pA = pA} {pB = pB} Φ lenΦ (subst-⊑ hσ rel) hu′
subst-⊑ hσ (⊑down {pA = pA} {pB = pB} Φ lenΦ rel hd hd′) =
  ⊑down {pA = pA} {pB = pB} Φ lenΦ (subst-⊑ hσ rel) hd hd′
subst-⊑ hσ (⊑downL {pA = pA} {pB = pB} Φ lenΦ rel hd) =
  ⊑downL {pA = pA} {pB = pB} Φ lenΦ (subst-⊑ hσ rel) hd
subst-⊑ hσ (⊑downR {pA = pA} {pB = pB} Φ lenΦ rel hd′) =
  ⊑downR {pA = pA} {pB = pB} Φ lenΦ (subst-⊑ hσ rel) hd′
subst-⊑ hσ (⊑blameR {p = p} hM) =
  ⊑blameR {p = p} (substˣ-term-wt _ (substᴾ-right-wt hσ) hM)

singleSubstᴾ :
  ∀ {E A A′ W W′} {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} →
  E ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Substᴾ (extendᴾ E (A , A′ , pA)) (TPEnv.Γ E)
    (singleVarEnv W) (singleVarEnv W′)
singleSubstᴾ W⊑W′ Zₚ = W⊑W′
singleSubstᴾ W⊑W′ (Sₚ h) = ⊑` h

[]-⊑ :
  ∀ {E A A′ B B′ M M′ W W′}
    {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
  extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
  E ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  E ⊢ M [ W ] ⊑ M′ [ W′ ] ⦂ B ⊑ B′
[]-⊑ rel W⊑W′ = subst-⊑ (singleSubstᴾ W⊑W′) rel

------------------------------------------------------------------------
-- Store and seal-context weakening
------------------------------------------------------------------------

wkΣ-⊑ :
  ∀ {E Σ′ M M′ A B} →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (⟪ TPEnv.Δ E , TPEnv.Ψ E , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ,
    TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ M ⊑ M′ ⦂ A ⊑ B
wkΣ-⊑ w (⊑` {p = p} h) = ⊑` {p = p} h
wkΣ-⊑ w (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB} hA hA′ (wkΣ-⊑ w rel)
wkΣ-⊑ w (⊑· {pA = pA} {pB = pB} relL relM) =
  ⊑· {pA = pA} {pB = pB} (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑Λ {p = p} vM vM′ wfA wfB rel) =
  ⊑Λ {p = p} vM vM′ wfA wfB (wkΣ-⊑ (inst-⟰ᵗ-⊆ˢ w) rel)
wkΣ-⊑ w (⊑⦂∀ {p = p} rel wfA wfB hT) =
  ⊑⦂∀ {p = p} (wkΣ-⊑ w rel) wfA wfB hT
wkΣ-⊑ w (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (wkΣ-⊑ w rel) wfA hT inst
wkΣ-⊑ w (⊑$ {n}) = ⊑$
wkΣ-⊑ w (⊑⊕ relL relM) = ⊑⊕ (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑up {pA = pA} {pB = pB} Φ lenΦ rel hu hu′) =
  ⊑up {pA = pA} {pB = pB} Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu) (wk⊑ w hu′)
wkΣ-⊑ w (⊑upL {pA = pA} {pB = pB} Φ lenΦ rel hu) =
  ⊑upL {pA = pA} {pB = pB} Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu)
wkΣ-⊑ w (⊑upR {pA = pA} {pB = pB} Φ lenΦ rel hu′) =
  ⊑upR {pA = pA} {pB = pB} Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu′)
wkΣ-⊑ w (⊑down {pA = pA} {pB = pB} Φ lenΦ rel hd hd′) =
  ⊑down {pA = pA} {pB = pB} Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd) (wk⊒ w hd′)
wkΣ-⊑ w (⊑downL {pA = pA} {pB = pB} Φ lenΦ rel hd) =
  ⊑downL {pA = pA} {pB = pB} Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd)
wkΣ-⊑ w (⊑downR {pA = pA} {pB = pB} Φ lenΦ rel hd′) =
  ⊑downR {pA = pA} {pB = pB} Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd′)
wkΣ-⊑ w (⊑blameR {p = p} hM) = ⊑blameR {p = p} (wkΣ-term w hM)

wkΨ-⊑-suc :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (⟪ TPEnv.Δ E , suc (TPEnv.Ψ E) , TPEnv.store E ,
    TPEnv.Ξ E , TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢
    M ⊑ M′ ⦂ A ⊑ B
wkΨ-⊑-suc (⊑` {p = p} h) = ⊑` {p = p} h
wkΨ-⊑-suc (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB}
      (WfTy-weakenˢ hA (n≤1+n _))
      (WfTy-weakenˢ hA′ (n≤1+n _))
      (wkΨ-⊑-suc rel)
wkΨ-⊑-suc (⊑· {pA = pA} {pB = pB} relL relM) =
  ⊑· {pA = pA} {pB = pB} (wkΨ-⊑-suc relL) (wkΨ-⊑-suc relM)
wkΨ-⊑-suc (⊑Λ {p = p} vM vM′ wfA wfB rel) =
  ⊑Λ {p = p} vM vM′
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ wfB (n≤1+n _))
    (wkΨ-⊑-suc rel)
wkΨ-⊑-suc (⊑⦂∀ {p = p} rel wfA wfB hT) =
  ⊑⦂∀ {p = p} (wkΨ-⊑-suc rel)
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ wfB (n≤1+n _))
    (WfTy-weakenˢ hT (n≤1+n _))
wkΨ-⊑-suc {E = E} {M = M} {M′ = M′}
    (⊑⦂∀-ν A B {T = T} p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ}
    (wkΨ-⊑-suc rel)
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ hT (n≤1+n _))
    inst
wkΨ-⊑-suc (⊑$ {n}) = ⊑$
wkΨ-⊑-suc (⊑⊕ relL relM) = ⊑⊕ (wkΨ-⊑-suc relL) (wkΨ-⊑-suc relM)
wkΨ-⊑-suc (⊑up {pA = pA} {pB = pB} Φ lenΦ rel hu hu′) =
  ⊑up {pA = pA} {pB = pB}
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu)
    (wkΨ-cast-tag-⊑ hu′)
wkΨ-⊑-suc (⊑upL {pA = pA} {pB = pB} Φ lenΦ rel hu) =
  ⊑upL {pA = pA} {pB = pB}
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu)
wkΨ-⊑-suc (⊑upR {pA = pA} {pB = pB} Φ lenΦ rel hu′) =
  ⊑upR {pA = pA} {pB = pB}
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu′)
wkΨ-⊑-suc (⊑down {pA = pA} {pB = pB} Φ lenΦ rel hd hd′) =
  ⊑down {pA = pA} {pB = pB}
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd)
    (wkΨ-cast-tag-⊒ hd′)
wkΨ-⊑-suc (⊑downL {pA = pA} {pB = pB} Φ lenΦ rel hd) =
  ⊑downL {pA = pA} {pB = pB}
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd)
wkΨ-⊑-suc (⊑downR {pA = pA} {pB = pB} Φ lenΦ rel hd′) =
  ⊑downR {pA = pA} {pB = pB}
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd′)
wkΨ-⊑-suc (⊑blameR {p = p} hM) = ⊑blameR {p = p} (wkΨ-term-suc hM)

wkΨ-⊑-+ :
  ∀ {E M M′ A B} →
  (k : ℕ) →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (⟪ TPEnv.Δ E , (k + TPEnv.Ψ E) , TPEnv.store E ,
    TPEnv.Ξ E , TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢
    M ⊑ M′ ⦂ A ⊑ B
wkΨ-⊑-+ zero rel = rel
wkΨ-⊑-+ (suc k) rel = wkΨ-⊑-suc (wkΨ-⊑-+ k rel)

wkΨ-⊑-≤ :
  ∀ {E Ψ′ M M′ A B} →
  TPEnv.Ψ E ≤ Ψ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (⟪ TPEnv.Δ E , Ψ′ , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ,
    TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ M ⊑ M′ ⦂ A ⊑ B
wkΨ-⊑-≤ {E} {Ψ′} Ψ≤ rel =
  subst
    (λ q →
      (⟪ TPEnv.Δ E , q , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ,
        TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ _ ⊑ _ ⦂ _ ⊑ _)
    (trans (+-comm (Ψ′ ∸ TPEnv.Ψ E) (TPEnv.Ψ E))
           (m+[n∸m]≡n Ψ≤))
    (wkΨ-⊑-+ (Ψ′ ∸ TPEnv.Ψ E) rel)

wkΨΣ-⊑ :
  ∀ {E Ψ′ Σ′ M M′ A B} →
  TPEnv.Ψ E ≤ Ψ′ →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (⟪ TPEnv.Δ E , Ψ′ , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ,
    TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ M ⊑ M′ ⦂ A ⊑ B
wkΨΣ-⊑ Ψ≤ w rel = wkΣ-⊑ w (wkΨ-⊑-≤ Ψ≤ rel)

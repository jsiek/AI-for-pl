module TermImprecisionIndexed where

-- File Charter:
--   * Structural term imprecision for extrinsic-inst PolyUpDown, indexed by
--     context-indexed type imprecision.
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
    (hT : WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T) →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂
      substPlain⊑ᵢ T (TPEnv-refl⊑ᵢ E hT) p

  ⊑⦂∀-ν : ∀ (A B : Ty) {M M′ T}
      (p : (ν-bound ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ ⇑ᵗ B) →
    {occ : occurs zero A ≡ true} →
    {pT : TPEnv.Ξ E ⊢ A [ T ]ᵗ ⊑ᵢ B} →
    E ⊢ M ⊑ M′ ⦂ (⊑ᵢ-ν A B occ p) →
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

⊑-transport-env :
  ∀ {E E′ M M′ A B}
    {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B}
    {p′ : TPEnv.Ξ E′ ⊢ A ⊑ᵢ B} →
  (eqE : E ≡ E′) →
  subst (λ F → TPEnv.Ξ F ⊢ A ⊑ᵢ B) eqE p ≡ p′ →
  E ⊢ M ⊑ M′ ⦂ p →
  E′ ⊢ M ⊑ M′ ⦂ p′
⊑-transport-env refl refl rel = rel

⊑-index-cast :
  ∀ {E M M′ A A′ B B′}
    {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  E ⊢ M ⊑ M′ ⦂ p →
  E ⊢ M ⊑ M′ ⦂ ⊑ᵢ-cast eqA eqB p
⊑-index-cast refl refl rel = rel

⊑-index-irrel :
  ∀ {E M M′ A B}
    {p q : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  E ⊢ M ⊑ M′ ⦂ q
⊑-index-irrel {p = p} {q = q} rel =
  subst (λ r → _ ⊢ _ ⊑ _ ⦂ r) (⊑ᵢ-proof-irrel p q) rel

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

renameˣ-⊑ :
  ∀ {E Γ′ ρ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  Renameᴾ (TPEnv.Γ E) Γ′ ρ →
  E ⊢ M ⊑ M′ ⦂ p →
  replaceΓᴾ E Γ′ ⊢ renameˣᵐ ρ M ⊑ renameˣᵐ ρ M′ ⦂ p
renameˣ-⊑ hρ (⊑` h) = ⊑` (hρ h)
renameˣ-⊑ hρ (⊑ƛ hA hA′ rel) =
  ⊑ƛ hA hA′ (renameˣ-⊑ (extʳᴾ hρ) rel)
renameˣ-⊑ hρ (⊑· relL relM) =
  ⊑· (renameˣ-⊑ hρ relL) (renameˣ-⊑ hρ relM)
renameˣ-⊑ hρ (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ
    (renameˣᵐ-value _ vM)
    (renameˣᵐ-value _ vM′)
    wfA
    wfB
    (renameˣ-⊑ (liftᵗʳᴾ hρ) rel)
renameˣ-⊑ hρ (⊑⦂∀ rel wfA wfB hT) =
  ⊑⦂∀ (renameˣ-⊑ hρ rel) wfA wfB hT
renameˣ-⊑ hρ (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (renameˣ-⊑ hρ rel) wfA hT inst
renameˣ-⊑ hρ (⊑$ {n}) = ⊑$
renameˣ-⊑ hρ (⊑⊕ relL relM) =
  ⊑⊕ (renameˣ-⊑ hρ relL) (renameˣ-⊑ hρ relM)
renameˣ-⊑ hρ (⊑up Φ lenΦ rel hu hu′) =
  ⊑up Φ lenΦ (renameˣ-⊑ hρ rel) hu hu′
renameˣ-⊑ hρ (⊑upL Φ lenΦ rel hu) =
  ⊑upL Φ lenΦ (renameˣ-⊑ hρ rel) hu
renameˣ-⊑ hρ (⊑upR Φ lenΦ rel hu′) =
  ⊑upR Φ lenΦ (renameˣ-⊑ hρ rel) hu′
renameˣ-⊑ hρ (⊑down Φ lenΦ rel hd hd′) =
  ⊑down Φ lenΦ (renameˣ-⊑ hρ rel) hd hd′
renameˣ-⊑ hρ (⊑downL Φ lenΦ rel hd) =
  ⊑downL Φ lenΦ (renameˣ-⊑ hρ rel) hd
renameˣ-⊑ hρ (⊑downR Φ lenΦ rel hd′) =
  ⊑downR Φ lenΦ (renameˣ-⊑ hρ rel) hd′
renameˣ-⊑ hρ (⊑blameR hM) =
  ⊑blameR (renameˣ-term-wt _ (renameᴾ-right-wt hρ) hM)

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

plain-weakenAtᴾ-⇑ :
  ∀ k {Ξ} →
  (Γ : PCtx Ξ) →
  plain-weakenAtᴾ (suc k) (⇑ᵗᴾ Γ) ≡
  ⇑ᵗᴾ (plain-weakenAtᴾ k Γ)
plain-weakenAtᴾ-⇑ k [] = refl
plain-weakenAtᴾ-⇑ k ((A , B , p) ∷ Γ) =
  cong₂ _∷_
    (Prec-cast-eq
      (rename-raise-⇑ᵗ k A)
      (rename-raise-⇑ᵗ k B)
      (⊑ᵢ-proof-irrel
        (⊑ᵢ-cast
          (rename-raise-⇑ᵗ k A)
          (rename-raise-⇑ᵗ k B)
          (plain-weakenAt⊑ᵢ (suc k) (plain-weaken⊑ᵢ p)))
        (plain-weaken⊑ᵢ (plain-weakenAt⊑ᵢ k p))))
    (plain-weakenAtᴾ-⇑ k Γ)

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

plain-weakenAtᴱ-⇑ :
  ∀ k {E}
    (k≤ : k ≤ length (TPEnv.Ξ E)) →
  plain-weakenAtᴱ (⇑ᵗᴱ E) (suc k) (s≤s k≤) ≡
  ⇑ᵗᴱ (plain-weakenAtᴱ E k k≤)
plain-weakenAtᴱ-⇑ k
    {E = ⟪ Δ , Ψ , Σ , Ξ , Γ , plainΞ , lenΞ ⟫} k≤
  rewrite trans
            (renameStoreᵗ-cong (λ X → sym (raise-ext k X)) (⟰ᵗ Σ))
            (renameStoreᵗ-ext-⟰ᵗ (raiseVarFrom k) Σ)
        | plain-weakenAtᴾ-⇑ k Γ =
  cong
    (λ len →
      ⟪ suc (suc Δ) , Ψ , ⟰ᵗ (renameStoreᵗ (raiseVarFrom k) Σ)
      , plain ∷ insertPlainAt k Ξ
      , ⇑ᵗᴾ (plain-weakenAtᴾ k Γ)
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
    (k≤ : k ≤ length (TPEnv.Ξ E))
    {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  plain-weakenAtᴱ E k k≤ ⊢
    renameᵗᵐ (raiseVarFrom k) M ⊑
    renameᵗᵐ (raiseVarFrom k) M′ ⦂
    plain-weakenAt⊑ᵢ k p
plain-weakenAt-⊑ k k≤ (⊑` h) = ⊑` (plain-weakenAtᴾ-∋ k h)
plain-weakenAt-⊑ k k≤ (⊑ƛ hA hA′ rel) =
  ⊑ƛ
    (renameᵗ-preserves-WfTy hA (raiseVarFrom-Wf k))
    (renameᵗ-preserves-WfTy hA′ (raiseVarFrom-Wf k))
    (plain-weakenAt-⊑ k k≤ rel)
plain-weakenAt-⊑ k k≤ (⊑· relL relM) =
  ⊑·
    (plain-weakenAt-⊑ k k≤ relL)
    (plain-weakenAt-⊑ k k≤ relM)
plain-weakenAt-⊑ k {E = E} {M = Λ M} {M′ = Λ M′}
    k≤ {p = ⊑ₒ-∀ A B p}
    (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ
    (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM)
    (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM′)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseVarFrom-Wf k)))
    (renameᵗ-preserves-WfTy wfB (TyRenameWf-ext (raiseVarFrom-Wf k)))
    (⊑-transport-env
      (plain-weakenAtᴱ-⇑ k k≤)
      (⊑ᵢ-proof-irrel
        (subst
          (λ F →
            TPEnv.Ξ F ⊢
              renameᵗ (extᵗ (raiseVarFrom k)) A ⊑ᵢ
              renameᵗ (extᵗ (raiseVarFrom k)) B)
          (plain-weakenAtᴱ-⇑ k k≤)
          (⊑ᵢ-cast
            (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
            (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
            (plain-weakenAt⊑ᵢ (suc k) p)))
        (⊑ᵢ-cast
          (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
          (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
          (plain-weakenAt⊑ᵢ (suc k) p)))
      (⊑-index-cast
        (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
        (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
        (subst
          (λ N′ →
            plain-weakenAtᴱ (⇑ᵗᴱ E) (suc k) (s≤s k≤) ⊢
              renameᵗᵐ (extᵗ (raiseVarFrom k)) M ⊑ N′ ⦂
              plain-weakenAt⊑ᵢ (suc k) p)
          (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M′)
          (subst
            (λ N →
              plain-weakenAtᴱ (⇑ᵗᴱ E) (suc k) (s≤s k≤) ⊢
                N ⊑ renameᵗᵐ (raiseVarFrom (suc k)) M′ ⦂
                plain-weakenAt⊑ᵢ (suc k) p)
            (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M)
            (plain-weakenAt-⊑ (suc k) (s≤s k≤) rel)))))
plain-weakenAt-⊑ k k≤ (⊑⦂∀ {A = A} {B = B} {T = T}
    rel wfA wfB hT) =
  ⊑-index-irrel
    (⊑-index-cast
      (renameᵗ-single-subst (raiseVarFrom k) T A)
      (renameᵗ-single-subst (raiseVarFrom k) T B)
      (⊑⦂∀
        (plain-weakenAt-⊑ k k≤ rel)
        (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseVarFrom-Wf k)))
        (renameᵗ-preserves-WfTy wfB (TyRenameWf-ext (raiseVarFrom-Wf k)))
        (renameᵗ-preserves-WfTy hT (raiseVarFrom-Wf k))))
plain-weakenAt-⊑ k k≤
    (⊑⦂∀-ν A B {T = T} p {occ = occ} rel wfA hT inst) =
  ⊑-index-irrel
    (⊑-index-cast
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
            (plain-weakenAt⊑ᵢ (suc k) p)))))
plain-weakenAt-⊑ k k≤ (⊑$ {n}) = ⊑$
plain-weakenAt-⊑ k k≤ (⊑⊕ relL relM) =
  ⊑⊕
    (plain-weakenAt-⊑ k k≤ relL)
    (plain-weakenAt-⊑ k k≤ relM)
plain-weakenAt-⊑ k k≤ (⊑up Φ lenΦ rel hu hu′) =
  ⊑up Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu′)
plain-weakenAt-⊑ k k≤ (⊑upL Φ lenΦ rel hu) =
  ⊑upL Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu)
plain-weakenAt-⊑ k k≤ (⊑upR Φ lenΦ rel hu′) =
  ⊑upR Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊑-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hu′)
plain-weakenAt-⊑ k k≤ (⊑down Φ lenΦ rel hd hd′) =
  ⊑down Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd′)
plain-weakenAt-⊑ k k≤ (⊑downL Φ lenΦ rel hd) =
  ⊑downL Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd)
plain-weakenAt-⊑ k k≤ (⊑downR Φ lenΦ rel hd′) =
  ⊑downR Φ lenΦ
    (plain-weakenAt-⊑ k k≤ rel)
    (⊒-renameᵗ-wt (raiseVarFrom k) (raiseVarFrom-Wf k) hd′)
plain-weakenAt-⊑ k {E = E} k≤ (⊑blameR hM) =
  ⊑blameR
    (cong-⊢⦂
      refl
      (sym (rightCtx-plain-weakenAtᴾ k (TPEnv.Γ E)))
      refl
      refl
      (renameᵗ-term (raiseVarFrom k) (raiseVarFrom-Wf k) hM))

plain-weaken-⊑ :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  ⇑ᵗᴱ E ⊢ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′ ⦂ plain-weaken⊑ᵢ p
plain-weaken-⊑ {E = E} {p = p} rel =
  ⊑-transport-env
    (plain-weakenAtᴱ-zero E)
    (⊑ᵢ-proof-irrel
      (subst
        (λ F →
          TPEnv.Ξ F ⊢ renameᵗ suc _ ⊑ᵢ renameᵗ suc _)
        (plain-weakenAtᴱ-zero E)
        (plain-weakenAt⊑ᵢ zero p))
      (plain-weaken⊑ᵢ p))
    (plain-weakenAt-⊑ zero {E = E} z≤n rel)

Substᴾ : (E : TPEnv) → PCtx (TPEnv.Ξ E) → Substˣ → Substˣ → Set
Substᴾ E Γ′ σ σ′ =
  ∀ {x A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
  replaceΓᴾ E Γ′ ⊢ σ x ⊑ σ′ x ⦂ p

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
  ∀ {E Γ′ σ σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  Substᴾ E Γ′ σ σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  replaceΓᴾ E Γ′ ⊢ substˣ-term σ M ⊑ substˣ-term σ′ M′ ⦂ p
subst-⊑ hσ (⊑` h) = hσ h
subst-⊑ hσ (⊑ƛ hA hA′ rel) =
  ⊑ƛ hA hA′ (subst-⊑ (extˣᴾ hσ) rel)
subst-⊑ hσ (⊑· relL relM) =
  ⊑· (subst-⊑ hσ relL) (subst-⊑ hσ relM)
subst-⊑ hσ (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ
    (substˣ-term-value _ vM)
    (substˣ-term-value _ vM′)
    wfA
    wfB
    (subst-⊑ (↑ᵗᵐᴾ hσ) rel)
subst-⊑ hσ (⊑⦂∀ rel wfA wfB hT) =
  ⊑⦂∀ (subst-⊑ hσ rel) wfA wfB hT
subst-⊑ hσ (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (subst-⊑ hσ rel) wfA hT inst
subst-⊑ hσ (⊑$ {n}) = ⊑$
subst-⊑ hσ (⊑⊕ relL relM) =
  ⊑⊕ (subst-⊑ hσ relL) (subst-⊑ hσ relM)
subst-⊑ hσ (⊑up Φ lenΦ rel hu hu′) =
  ⊑up Φ lenΦ (subst-⊑ hσ rel) hu hu′
subst-⊑ hσ (⊑upL Φ lenΦ rel hu) =
  ⊑upL Φ lenΦ (subst-⊑ hσ rel) hu
subst-⊑ hσ (⊑upR Φ lenΦ rel hu′) =
  ⊑upR Φ lenΦ (subst-⊑ hσ rel) hu′
subst-⊑ hσ (⊑down Φ lenΦ rel hd hd′) =
  ⊑down Φ lenΦ (subst-⊑ hσ rel) hd hd′
subst-⊑ hσ (⊑downL Φ lenΦ rel hd) =
  ⊑downL Φ lenΦ (subst-⊑ hσ rel) hd
subst-⊑ hσ (⊑downR Φ lenΦ rel hd′) =
  ⊑downR Φ lenΦ (subst-⊑ hσ rel) hd′
subst-⊑ hσ (⊑blameR hM) =
  ⊑blameR (substˣ-term-wt _ (substᴾ-right-wt hσ) hM)

singleSubstᴾ :
  ∀ {E A A′ W W′} {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} →
  E ⊢ W ⊑ W′ ⦂ pA →
  Substᴾ (extendᴾ E (A , A′ , pA)) (TPEnv.Γ E)
    (singleVarEnv W) (singleVarEnv W′)
singleSubstᴾ W⊑W′ Zₚ = W⊑W′
singleSubstᴾ W⊑W′ (Sₚ h) = ⊑` h

[]-⊑ :
  ∀ {E A A′ B B′ M M′ W W′}
    {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
  extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ pB →
  E ⊢ W ⊑ W′ ⦂ pA →
  E ⊢ M [ W ] ⊑ M′ [ W′ ] ⦂ pB
[]-⊑ rel W⊑W′ = subst-⊑ (singleSubstᴾ W⊑W′) rel

------------------------------------------------------------------------
-- Store and seal-context weakening
------------------------------------------------------------------------

wkΣ-⊑ :
  ∀ {E Σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , TPEnv.Ψ E , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ,
    TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΣ-⊑ w (⊑` h) = ⊑` h
wkΣ-⊑ w (⊑ƛ hA hA′ rel) = ⊑ƛ hA hA′ (wkΣ-⊑ w rel)
wkΣ-⊑ w (⊑· relL relM) = ⊑· (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ vM vM′ wfA wfB (wkΣ-⊑ (inst-⟰ᵗ-⊆ˢ w) rel)
wkΣ-⊑ w (⊑⦂∀ rel wfA wfB hT) =
  ⊑⦂∀ (wkΣ-⊑ w rel) wfA wfB hT
wkΣ-⊑ w (⊑⦂∀-ν A B p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ} (wkΣ-⊑ w rel) wfA hT inst
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
    TPEnv.Ξ E , TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢
    M ⊑ M′ ⦂ p
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
wkΨ-⊑-suc {E = E} (⊑⦂∀ {A = A} {B = B} {T = T} {p = p}
    rel wfA wfB hT) =
  subst
    (λ q →
      (⟪ TPEnv.Δ E , suc (TPEnv.Ψ E) , TPEnv.store E ,
        TPEnv.Ξ E , TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢
        _ ⊑ _ ⦂ q)
    (⊑ᵢ-proof-irrel
      (substPlain⊑ᵢ T
        (TPEnv-refl⊑ᵢ
          (⟪ TPEnv.Δ E , suc (TPEnv.Ψ E) , TPEnv.store E ,
            TPEnv.Ξ E , TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫)
          (WfTy-weakenˢ hT (n≤1+n _)))
        p)
      (substPlain⊑ᵢ T (TPEnv-refl⊑ᵢ E hT) p))
    (⊑⦂∀ (wkΨ-⊑-suc rel)
      (WfTy-weakenˢ wfA (n≤1+n _))
      (WfTy-weakenˢ wfB (n≤1+n _))
      (WfTy-weakenˢ hT (n≤1+n _)))
wkΨ-⊑-suc {E = E} {M = M} {M′ = M′}
    (⊑⦂∀-ν A B {T = T} p {occ = occ} rel wfA hT inst) =
  ⊑⦂∀-ν A B p {occ = occ}
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
    TPEnv.Ξ E , TPEnv.Γ E , TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΨ-⊑-+ zero rel = rel
wkΨ-⊑-+ (suc k) rel = wkΨ-⊑-suc (wkΨ-⊑-+ k rel)

wkΨ-⊑-≤ :
  ∀ {E Ψ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Ψ E ≤ Ψ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , Ψ′ , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ,
    TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΨ-⊑-≤ {E} {Ψ′} Ψ≤ rel =
  subst
    (λ q →
      (⟪ TPEnv.Δ E , q , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ,
        TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ _ ⊑ _ ⦂ _)
    (trans (+-comm (Ψ′ ∸ TPEnv.Ψ E) (TPEnv.Ψ E))
           (m+[n∸m]≡n Ψ≤))
    (wkΨ-⊑-+ (Ψ′ ∸ TPEnv.Ψ E) rel)

wkΨΣ-⊑ :
  ∀ {E Ψ′ Σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Ψ E ≤ Ψ′ →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , Ψ′ , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ,
    TPEnv.plainΞ E , TPEnv.lenΞ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΨΣ-⊑ Ψ≤ w rel = wkΣ-⊑ w (wkΨ-⊑-≤ Ψ≤ rel)

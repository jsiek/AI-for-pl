module TermImprecision where

-- File Charter:
--   * Structural term imprecision for extrinsic-inst PolyConvert.
--   * Defines imprecision-aware term contexts, a context-indexed term
--     imprecision judgment, and projections back to ordinary typing.
--   * The relation is oriented like `Imprecision`: the left endpoint is more
--     precise and the right endpoint is less precise.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
open import Conversion
open import Store using (renameStoreᵗ-ext-⟰ᵗ)
open import Primitives
open import Terms
open import proof.PreservationTermSubst using (wkImp-extend-X⊑X)

------------------------------------------------------------------------
-- Imprecision contexts
------------------------------------------------------------------------

Prec : TyCtx → SealCtx → Set
Prec Δ Ψ =
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (Ψ ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B)

PCtx : TyCtx → SealCtx → Set
PCtx Δ Ψ = List (Prec Δ Ψ)

record TPEnv : Set where
  constructor ⟪_,_,_,_,_,_⟫
  field
    Δ : TyCtx
    -- Left seal/store world. Imprecision evidence is stated in this world.
    Ψ : SealCtx
    store : Store
    -- Right seal/store world. The less precise endpoint is typed here.
    Ψʳ : SealCtx
    storeʳ : Store
    Γ : PCtx Δ Ψ
open TPEnv public

extendᴾ : (E : TPEnv) → Prec (TPEnv.Δ E) (TPEnv.Ψ E) → TPEnv
extendᴾ E P =
  ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E ,
    TPEnv.Ψʳ E , TPEnv.storeʳ E , P ∷ TPEnv.Γ E ⟫

leftTy : ∀ {Δ Ψ} → Prec Δ Ψ → Ty
leftTy (A , B , p , p⊢) = A

rightTy : ∀ {Δ Ψ} → Prec Δ Ψ → Ty
rightTy (A , B , p , p⊢) = B

leftCtx : ∀ {Δ Ψ} → PCtx Δ Ψ → Ctx
leftCtx [] = []
leftCtx (P ∷ Γ) = leftTy P ∷ leftCtx Γ

rightCtx : ∀ {Δ Ψ} → PCtx Δ Ψ → Ctx
rightCtx [] = []
rightCtx (P ∷ Γ) = rightTy P ∷ rightCtx Γ

infix 4 _∋ₚ_⦂_
data _∋ₚ_⦂_ {Δ : TyCtx} {Ψ : SealCtx} :
    PCtx Δ Ψ → Var → Prec Δ Ψ → Set where

  Zₚ : ∀ {Γ P} →
    (P ∷ Γ) ∋ₚ zero ⦂ P

  Sₚ : ∀ {Γ P Q x} →
    Γ ∋ₚ x ⦂ P →
    (Q ∷ Γ) ∋ₚ suc x ⦂ P

lookup-left :
  ∀ {Δ Ψ} {Γ : PCtx Δ Ψ} {x A B p p⊢} →
  Γ ∋ₚ x ⦂ (A , B , p , p⊢) →
  leftCtx Γ ∋ x ⦂ A
lookup-left Zₚ = Z
lookup-left (Sₚ h) = S (lookup-left h)

lookup-right :
  ∀ {Δ Ψ} {Γ : PCtx Δ Ψ} {x A B p p⊢} →
  Γ ∋ₚ x ⦂ (A , B , p , p⊢) →
  rightCtx Γ ∋ x ⦂ B
lookup-right Zₚ = Z
lookup-right (Sₚ h) = S (lookup-right h)

------------------------------------------------------------------------
-- Type-binder lifting of imprecision contexts
------------------------------------------------------------------------

⇑ᵗᴾ : ∀ {Δ Ψ} → PCtx Δ Ψ → PCtx (suc Δ) Ψ
⇑ᵗᴾ [] = []
⇑ᵗᴾ ((A , B , p , p⊢) ∷ Γ) =
  (⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImp-extend-X⊑X zero p⊢) ∷ ⇑ᵗᴾ Γ

leftCtx-⇑ᵗᴾ :
  ∀ {Δ Ψ} → (Γ : PCtx Δ Ψ) →
  leftCtx (⇑ᵗᴾ Γ) ≡ ⤊ᵗ (leftCtx Γ)
leftCtx-⇑ᵗᴾ [] = refl
leftCtx-⇑ᵗᴾ ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ A ∷_) (leftCtx-⇑ᵗᴾ Γ)

rightCtx-⇑ᵗᴾ :
  ∀ {Δ Ψ} → (Γ : PCtx Δ Ψ) →
  rightCtx (⇑ᵗᴾ Γ) ≡ ⤊ᵗ (rightCtx Γ)
rightCtx-⇑ᵗᴾ [] = refl
rightCtx-⇑ᵗᴾ ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ B ∷_) (rightCtx-⇑ᵗᴾ Γ)

⇑ᵗᴱ : TPEnv → TPEnv
⇑ᵗᴱ E =
  ⟪ suc (TPEnv.Δ E) , TPEnv.Ψ E , ⟰ᵗ (TPEnv.store E) ,
    TPEnv.Ψʳ E , ⟰ᵗ (TPEnv.storeʳ E) ,
    ⇑ᵗᴾ (TPEnv.Γ E) ⟫

------------------------------------------------------------------------
-- Term imprecision
------------------------------------------------------------------------

infix 4 _⊢_⊑_⦂_⊑_
data _⊢_⊑_⦂_⊑_ (E : TPEnv) :
    Term → Term → Ty → Ty → Set where

  ⊑` : ∀ {x A B p p⊢} →
    TPEnv.Γ E ∋ₚ x ⦂ (A , B , p , p⊢) →
    E ⊢ (` x) ⊑ (` x) ⦂ A ⊑ B

  ⊑ƛ : ∀ {A A′ B B′ M M′ pA pB}
      {pA⊢ : TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pA ⦂ A ⊑ A′}
      {pB⊢ : TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ B′} →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A′ →
    extendᴾ E (A , A′ , pA , pA⊢) ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
    E ⊢ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ A ⇒ B ⊑ A′ ⇒ B′

  ⊑· : ∀ {A A′ B B′ L L′ M M′} →
    E ⊢ L ⊑ L′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    E ⊢ (L · M) ⊑ (L′ · M′) ⦂ B ⊑ B′

  ⊑Λ : ∀ {A B M M′} →
    Value M →
    Value M′ →
    ⇑ᵗᴱ E ⊢ M ⊑ M′ ⦂ A ⊑ B →
    E ⊢ (Λ M) ⊑ (Λ M′) ⦂ `∀ A ⊑ `∀ B

  ⊑⦂∀ : ∀ {A B M M′ T pT} →
    E ⊢ M ⊑ M′ ⦂ `∀ A ⊑ `∀ B →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pT ⦂
      A [ T ]ᵗ ⊑ B [ T ]ᵗ →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂
      A [ T ]ᵗ ⊑ B [ T ]ᵗ

  ⊑⦂∀-ν : ∀ {A B M M′ T pT} →
    E ⊢ M ⊑ M′ ⦂ `∀ A ⊑ B →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pT ⦂ A [ T ]ᵗ ⊑ B →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ A [ T ]ᵗ ⊑ B

  ⊑$ : ∀ {n} →
    E ⊢ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ ‵ `ℕ ⊑ ‵ `ℕ

  ⊑⊕ : ∀ {L L′ M M′ op} →
    E ⊢ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ →
    E ⊢ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ →
    E ⊢ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ ‵ `ℕ ⊑ ‵ `ℕ

  ⊑⇑ : ∀ {M M′ A A′ B B′ p p′ pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ A ⊑ B →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p′ ⦂ A′ ⊑ B′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ B′ →
    E ⊢ (M ⇑ p) ⊑ (M′ ⇑ p′) ⦂ B ⊑ B′

  ⊑⇑L : ∀ {M M′ A A′ B p pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ A ⊑ B →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ A′ →
    E ⊢ (M ⇑ p) ⊑ M′ ⦂ B ⊑ A′

  ⊑⇑R : ∀ {M M′ A A′ B′ p′ pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p′ ⦂ A′ ⊑ B′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ A ⊑ B′ →
    E ⊢ M ⊑ (M′ ⇑ p′) ⦂ A ⊑ B′

  ⊑⇓ : ∀ {M M′ A A′ B B′ p p′ pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ A ⊒ B →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p′ ⦂ A′ ⊒ B′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ B′ →
    E ⊢ (M ⇓ p) ⊑ (M′ ⇓ p′) ⦂ B ⊑ B′

  ⊑⇓L : ∀ {M M′ A A′ B p pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ A ⊒ B →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ A′ →
    E ⊢ (M ⇓ p) ⊑ M′ ⦂ B ⊑ A′

  ⊑⇓R : ∀ {M M′ A A′ B′ p′ pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p′ ⦂ A′ ⊒ B′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ A ⊑ B′ →
    E ⊢ M ⊑ (M′ ⇓ p′) ⦂ A ⊑ B′

  ⊑↑ : ∀ {M M′ A A′ B B′ c c′ pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ⊢ c ⦂ A ↑ˢ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ⊢ c′ ⦂ A′ ↑ˢ B′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ B′ →
    E ⊢ (M ↑ c) ⊑ (M′ ↑ c′) ⦂ B ⊑ B′

  ⊑↓ : ∀ {M M′ A A′ B B′ c c′ pB} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ⊢ c ⦂ A ↓ˢ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ⊢ c′ ⦂ A′ ↓ˢ B′ →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ pB ⦂ B ⊑ B′ →
    E ⊢ (M ↓ c) ⊑ (M′ ↓ c′) ⦂ B ⊑ B′

  ⊑blameL : ∀ {M A B p ℓ} →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
      rightCtx (TPEnv.Γ E) ⊢ M ⦂ B →
    TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ A ⊑ B →
    E ⊢ (blame ℓ) ⊑ M ⦂ A ⊑ B

⊑-index-cast :
  ∀ {E M M′ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
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
⊑-left-typed (⊑· relL relM) =
  ⊢· (⊑-left-typed relL) (⊑-left-typed relM)
⊑-left-typed {E = E} (⊑Λ vM vM′ rel) =
  ⊢Λ vM
    (cong-⊢⦂ refl (leftCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl
      (⊑-left-typed rel))
⊑-left-typed (⊑⦂∀ rel wfA wfB wfT pT⊢) =
  ⊢• (⊑-left-typed rel) wfA wfT
⊑-left-typed (⊑⦂∀-ν rel wfA wfT pT⊢) =
  ⊢• (⊑-left-typed rel) wfA wfT
⊑-left-typed (⊑$ {n}) = ⊢$ (κℕ n)
⊑-left-typed (⊑⊕ {op = op} relL relM) =
  ⊢⊕ (⊑-left-typed relL) op (⊑-left-typed relM)
⊑-left-typed (⊑⇑ rel p⊢ p′⊢ pB⊢) = ⊢up p⊢ (⊑-left-typed rel)
⊑-left-typed (⊑⇑L rel p⊢ pB⊢) = ⊢up p⊢ (⊑-left-typed rel)
⊑-left-typed (⊑⇑R rel p′⊢ pB⊢) = ⊑-left-typed rel
⊑-left-typed (⊑⇓ rel p⊢ p′⊢ pB⊢) = ⊢down p⊢ (⊑-left-typed rel)
⊑-left-typed (⊑⇓L rel p⊢ pB⊢) = ⊢down p⊢ (⊑-left-typed rel)
⊑-left-typed (⊑⇓R rel p′⊢ pB⊢) = ⊑-left-typed rel
⊑-left-typed (⊑↑ rel c⊢ c′⊢ pB⊢) = ⊢reveal c⊢ (⊑-left-typed rel)
⊑-left-typed (⊑↓ rel c⊢ c′⊢ pB⊢) = ⊢conceal c⊢ (⊑-left-typed rel)
⊑-left-typed (⊑blameL hM p⊢) = ⊢blame _

⊑-right-typed :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ rightCtx (TPEnv.Γ E) ⊢ M′ ⦂ B
⊑-right-typed (⊑` h) = ⊢` (lookup-right h)
⊑-right-typed (⊑ƛ hA hA′ rel) = ⊢ƛ hA′ (⊑-right-typed rel)
⊑-right-typed (⊑· relL relM) =
  ⊢· (⊑-right-typed relL) (⊑-right-typed relM)
⊑-right-typed {E = E} (⊑Λ vM vM′ rel) =
  ⊢Λ vM′
    (cong-⊢⦂ refl (rightCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl
      (⊑-right-typed rel))
⊑-right-typed (⊑⦂∀ rel wfA wfB wfT pT⊢) =
  ⊢• (⊑-right-typed rel) wfB wfT
⊑-right-typed (⊑⦂∀-ν rel wfA wfT pT⊢) = ⊑-right-typed rel
⊑-right-typed (⊑$ {n}) = ⊢$ (κℕ n)
⊑-right-typed (⊑⊕ {op = op} relL relM) =
  ⊢⊕ (⊑-right-typed relL) op (⊑-right-typed relM)
⊑-right-typed (⊑⇑ rel p⊢ p′⊢ pB⊢) = ⊢up p′⊢ (⊑-right-typed rel)
⊑-right-typed (⊑⇑L rel p⊢ pB⊢) = ⊑-right-typed rel
⊑-right-typed (⊑⇑R rel p′⊢ pB⊢) = ⊢up p′⊢ (⊑-right-typed rel)
⊑-right-typed (⊑⇓ rel p⊢ p′⊢ pB⊢) = ⊢down p′⊢ (⊑-right-typed rel)
⊑-right-typed (⊑⇓L rel p⊢ pB⊢) = ⊑-right-typed rel
⊑-right-typed (⊑⇓R rel p′⊢ pB⊢) = ⊢down p′⊢ (⊑-right-typed rel)
⊑-right-typed (⊑↑ rel c⊢ c′⊢ pB⊢) = ⊢reveal c′⊢ (⊑-right-typed rel)
⊑-right-typed (⊑↓ rel c⊢ c′⊢ pB⊢) = ⊢conceal c′⊢ (⊑-right-typed rel)
⊑-right-typed (⊑blameL hM p⊢) = hM

⊑-type-imprecision :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  Σ[ p ∈ Imp ] (TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ A ⊑ B)
⊑-type-imprecision (⊑` {p = p} {p⊢ = p⊢} h) = p , p⊢
⊑-type-imprecision
  (⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢} hA hA′ rel) =
  A⇒B-⊑-A′⇒B′ pA pB , ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
⊑-type-imprecision (⊑· relL relM) with ⊑-type-imprecision relL
... | A⇒B-⊑-A′⇒B′ pA pB , ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢ = pB , pB⊢
⊑-type-imprecision (⊑Λ relM relM′ rel) with ⊑-type-imprecision rel
... | p , p⊢ = ∀A-⊑-∀B p , ⊢∀A-⊑-∀B p⊢
⊑-type-imprecision (⊑⦂∀ rel wfA wfB wfT pT⊢) = _ , pT⊢
⊑-type-imprecision (⊑⦂∀-ν rel wfA wfT pT⊢) = _ , pT⊢
⊑-type-imprecision ⊑$ = ι-⊑-ι `ℕ , ⊢ι-⊑-ι
⊑-type-imprecision (⊑⊕ relL relM) = ι-⊑-ι `ℕ , ⊢ι-⊑-ι
⊑-type-imprecision (⊑⇑ rel p⊢ p′⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑⇑L rel p⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑⇑R rel p′⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑⇓ rel p⊢ p′⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑⇓L rel p⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑⇓R rel p′⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑↑ rel c⊢ c′⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑↓ rel c⊢ c′⊢ pB⊢) = _ , pB⊢
⊑-type-imprecision (⊑blameL hM p⊢) = _ , p⊢

module Compile where

-- File Charter:
--   * Compilation from source gradual GTSF terms to target explicit-coercion terms.
--   * Exports the maximal-lower-bound cast-plan specification, `compile`, and
--     `compile-value`.
--   * The store is empty at compile time; target reduction allocates store cells
--     later for polymorphic/seal behavior.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import Coercions using (Coercion; _∣_⊢_∶_=⇒_)
open import Imprecision using (_⊢_⊑_; _⊢_~_; idᵢ; id★; _↦_; tag_⇒_)
open import Primitives using (Const; Prim; constTy)
open import proof.TermProperties using (CtxWf-⤊)

open import GradualTerms
  using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·_ to _·ᴳ_
    ; Λ_ to Λᴳ_
    ; _`[_] to _`ᴳ[_]
    ; $ to $ᴳ
    ; _⊕[_]_ to _⊕ᴳ[_]_
    ; Value to Valueᴳ
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )
open import Terms
  using (Term)
  renaming
    ( `_ to `ᵀ_
    ; ƛ_ to ƛᵀ_
    ; _·_ to _·ᵀ_
    ; Λ_ to Λᵀ_
    ; _⦂∀_•_ to _⦂∀ᵀ_•_
    ; $ to $ᵀ
    ; _⊕[_]_ to _⊕ᵀ[_]_
    ; _⟨_⟩ to _⟨ᵀ_⟩
    ; Value to Valueᵀ
    ; _∣_∣_⊢_⦂_ to _∣_∣_⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢· to ⊢ᵀ·
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢• to ⊢ᵀ•
    ; ⊢$ to ⊢ᵀ$
    ; ⊢⊕ to ⊢ᵀ⊕
    ; ⊢up to ⊢ᵀup
    )

------------------------------------------------------------------------
-- Maximal lower bounds for compiling consistency
------------------------------------------------------------------------

CommonLowerBound : TyCtx → Ty → Ty → Ty → Set
CommonLowerBound Δ A B C =
  idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B

StrictlyBelow : TyCtx → Ty → Ty → Set
StrictlyBelow Δ C D =
  idᵢ Δ ⊢ C ⊑ D × ¬ (idᵢ Δ ⊢ D ⊑ C)

record MaximalLowerBound (Δ : TyCtx) (A B : Ty) : Set where
  field
    lower : Ty
    lower-left : idᵢ Δ ⊢ lower ⊑ A
    lower-right : idᵢ Δ ⊢ lower ⊑ B
    maximal :
      ∀ {D} →
      CommonLowerBound Δ A B D →
      ¬ StrictlyBelow Δ lower D

open MaximalLowerBound public

record CastPlan (Δ : TyCtx) (Σ : Store) (A B : Ty) : Set₁ where
  field
    mlb : MaximalLowerBound Δ A B

    down : Coercion
    down⊢ : Δ ∣ Σ ⊢ down ∶ A =⇒ lower mlb

    up : Coercion
    up⊢ : Δ ∣ Σ ⊢ up ∶ lower mlb =⇒ B

open CastPlan public

-- TODO: implement this boundary with the maximal-lower-bound search and
-- coercion synthesis from the two imprecision witnesses.
postulate
  consistency-cast-plan :
    ∀ {Δ A B} →
    Δ ⊢ A ~ B →
    CastPlan Δ [] A B

~-sym :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  Δ ⊢ B ~ A
~-sym (C , C⊑A , C⊑B) = C , C⊑B , C⊑A

arrow★-consistent :
  ∀ {Δ A} →
  Δ ⊢ A ~ ★ →
  Δ ⊢ (A ⇒ ★) ~ ★
arrow★-consistent (C , C⊑A , C⊑★) =
  C ⇒ ★ , (C⊑A ↦ id★) , (tag C⊑★ ⇒ id★)

cast :
  ∀ {Δ A B} →
  CastPlan Δ [] A B →
  Term →
  Term
cast plan M =
  (M ⟨ᵀ down plan ⟩) ⟨ᵀ up plan ⟩

cast⊢ :
  ∀ {Δ Γ A B M} →
  (plan : CastPlan Δ [] A B) →
  Δ ∣ [] ∣ Γ ⊢ᵀ M ⦂ A →
  Δ ∣ [] ∣ Γ ⊢ᵀ cast plan M ⦂ B
cast⊢ plan M⊢ =
  ⊢ᵀup (up⊢ plan) (⊢ᵀup (down⊢ plan) M⊢)

------------------------------------------------------------------------
-- Compilation
------------------------------------------------------------------------

compile :
  ∀ {Δ Γ M A} →
  CtxWf Δ Γ →
  Δ ∣ Γ ⊢ᴳ M ⦂ A →
  Σ[ N ∈ Term ] Δ ∣ [] ∣ Γ ⊢ᵀ N ⦂ A

compile-value :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (vM : Valueᴳ M) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  Valueᵀ (proj₁ (compile hΓ M⊢))

compile hΓ (⊢ᴳ` x∈) =
  `ᵀ _ , ⊢ᵀ` x∈
compile hΓ (⊢ᴳƛ wfA M⊢) with compile (ctxWf-∷ wfA hΓ) M⊢
compile hΓ (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N , ⊢ᵀƛ wfA N⊢
compile hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    with compile hΓ L⊢ | compile hΓ M⊢ | consistency-cast-plan (~-sym A~A′)
compile hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  L′ ·ᵀ cast plan M′ ,
  ⊢ᵀ· L′⊢ (cast⊢ plan M′⊢)
compile hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan (~-sym (arrow★-consistent A′~★))
compile hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  cast plan L′ ·ᵀ M′ ,
  ⊢ᵀ· (cast⊢ plan L′⊢) M′⊢
compile hΓ (⊢ᴳΛ {occ = occ} vM M⊢)
    with compile (CtxWf-⤊ hΓ) M⊢
       | compile-value (CtxWf-⤊ hΓ) vM M⊢
compile hΓ (⊢ᴳΛ {occ = occ} vM M⊢) | N , N⊢ | vN =
  Λᵀ N , ⊢ᵀΛ {occ = occ} vN N⊢
compile hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA) with compile hΓ M⊢
compile hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA) | M′ , M′⊢ =
  M′ ⦂∀ᵀ B • A , ⊢ᵀ• M′⊢ wfA
compile hΓ (⊢ᴳ$ κ) =
  $ᵀ κ , ⊢ᵀ$ κ
compile hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan A~ℕ | consistency-cast-plan B~ℕ
compile hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | M′ , M′⊢ | planL | planM =
  cast planL L′ ⊕ᵀ[ op ] cast planM M′ ,
  ⊢ᵀ⊕ (cast⊢ planL L′⊢) op (cast⊢ planM M′⊢)

compile-value hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢)
    with compile (ctxWf-∷ wfA hΓ) M⊢
compile-value hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N
compile-value hΓ ($ᴳ κ) (⊢ᴳ$ .κ) =
  $ᵀ κ
compile-value hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢)
    with compile (CtxWf-⤊ hΓ) M⊢
       | compile-value (CtxWf-⤊ hΓ) vM M⊢
compile-value hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢) | N , N⊢ | vN =
  Λᵀ vN

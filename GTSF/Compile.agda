module Compile where

-- File Charter:
--   * Compilation from source gradual GTSF terms to target explicit-coercion terms.
--   * Exports the common-lower-bound cast-plan specification, `compile`, and
--     `compile-value`.
--   * The store is empty at compile time; target reduction allocates store cells
--     later for polymorphic/seal behavior.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([])
open import Data.Product using (Σ-syntax; _,_; proj₁)

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import Coercions using (Label; Coercion; _∣_⊢_∶_=⇒_)
open import Imprecision using (_⊢_~_; id★; _↦_; tag_⇒_)
open import Primitives using (Const; Prim; constTy)
open import proof.CompileCoercions using (coerce-up; coerce-down; realizes-idᵢ)
open import proof.ImprecisionProperties
  using (⊑-src-wf-idᵢ; ⊑-tgt-wf-idᵢ; ~-sym)
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
-- Cast plans for compiling consistency
------------------------------------------------------------------------

record CastPlan (Δ : TyCtx) (Σ : Store) (A B : Ty) : Set₁ where
  field
    lower : Ty
    down : Coercion
    down⊢ : Δ ∣ Σ ⊢ down ∶ A =⇒ lower

    up : Coercion
    up⊢ : Δ ∣ Σ ⊢ up ∶ lower =⇒ B

open CastPlan public

consistency-cast-plan :
  ∀ {Δ A B} →
  Label →
  Δ ⊢ A ~ B →
  CastPlan Δ [] A B
consistency-cast-plan {Δ = Δ} ℓ (C , C⊑A , C⊑B)
    with coerce-down ℓ
           (⊑-src-wf-idᵢ C⊑A)
           (⊑-tgt-wf-idᵢ C⊑A)
           (realizes-idᵢ Δ)
           C⊑A
       | coerce-up ℓ
           (⊑-src-wf-idᵢ C⊑B)
           (⊑-tgt-wf-idᵢ C⊑B)
           (realizes-idᵢ Δ)
           C⊑B
consistency-cast-plan {Δ = Δ} ℓ (C , C⊑A , C⊑B)
    | down , down⊢ | up , up⊢ =
  record
    { lower = C
    ; down = down
    ; down⊢ = down⊢
    ; up = up
    ; up⊢ = up⊢
    }

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
  Label →
  CtxWf Δ Γ →
  Δ ∣ Γ ⊢ᴳ M ⦂ A →
  Σ[ N ∈ Term ] Δ ∣ [] ∣ Γ ⊢ᵀ N ⦂ A

compile-value :
  ∀ {Δ Γ M A} →
  (ℓ : Label) →
  (hΓ : CtxWf Δ Γ) →
  (vM : Valueᴳ M) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  Valueᵀ (proj₁ (compile ℓ hΓ M⊢))

compile ℓ hΓ (⊢ᴳ` x∈) =
  `ᵀ _ , ⊢ᵀ` x∈
compile ℓ hΓ (⊢ᴳƛ wfA M⊢) with compile ℓ (ctxWf-∷ wfA hΓ) M⊢
compile ℓ hΓ (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N , ⊢ᵀƛ wfA N⊢
compile ℓ hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    with compile ℓ hΓ L⊢ | compile ℓ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~A′)
compile ℓ hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  L′ ·ᵀ cast plan M′ ,
  ⊢ᵀ· L′⊢ (cast⊢ plan M′⊢)
compile ℓ hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    with compile ℓ hΓ L⊢ | compile ℓ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym (arrow★-consistent A′~★))
compile ℓ hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  cast plan L′ ·ᵀ M′ ,
  ⊢ᵀ· (cast⊢ plan L′⊢) M′⊢
compile ℓ hΓ (⊢ᴳΛ {occ = occ} vM M⊢)
    with compile ℓ (CtxWf-⤊ hΓ) M⊢
       | compile-value ℓ (CtxWf-⤊ hΓ) vM M⊢
compile ℓ hΓ (⊢ᴳΛ {occ = occ} vM M⊢) | N , N⊢ | vN =
  Λᵀ N , ⊢ᵀΛ {occ = occ} vN N⊢
compile ℓ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA)
    with compile ℓ hΓ M⊢
compile ℓ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA) | M′ , M′⊢ =
  M′ ⦂∀ᵀ B • A , ⊢ᵀ• M′⊢ wfA
compile ℓ hΓ (⊢ᴳ$ κ) =
  $ᵀ κ , ⊢ᵀ$ κ
compile ℓ hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with compile ℓ hΓ L⊢ | compile ℓ hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ | consistency-cast-plan ℓ B~ℕ
compile ℓ hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | M′ , M′⊢ | planL | planM =
  cast planL L′ ⊕ᵀ[ op ] cast planM M′ ,
  ⊢ᵀ⊕ (cast⊢ planL L′⊢) op (cast⊢ planM M′⊢)

compile-value ℓ hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢)
    with compile ℓ (ctxWf-∷ wfA hΓ) M⊢
compile-value ℓ hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N
compile-value ℓ hΓ ($ᴳ κ) (⊢ᴳ$ .κ) =
  $ᵀ κ
compile-value ℓ hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢)
    with compile ℓ (CtxWf-⤊ hΓ) M⊢
       | compile-value ℓ (CtxWf-⤊ hΓ) vM M⊢
compile-value ℓ hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢) | N , N⊢ | vN =
  Λᵀ vN

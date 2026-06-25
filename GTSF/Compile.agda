module Compile where

-- File Charter:
--   * Compilation from source gradual GTSF terms to target explicit-coercion terms.
--   * Exports the common-lower-bound cast-plan specification, `compile`, and
--     `compile-value`.
--   * The store is empty at compile time; target reduction allocates store cells
--     later for polymorphic/seal behavior.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import Coercions
  using
    ( Label
    ; Coercion
    ; _∣_⊢_∶_=⇒_
    ; _∣_∣_⊢_∶_=⇒_
    ; reveal
    )
open import Imprecision using (_⊢_~_; id★; _↦_; tag_⇒_)
open import Primitives using (Const; Prim; constTy)
open import proof.CompileCoercions using (coerce-up; coerce-down; realizes-idᵢ)
open import proof.CoercionProperties
  using
    ( RevealEnv
    ; reveal-typing-env
    ; rv-hit
    ; rv-miss
    ; singleSealᵈ
    ; singleSealMode
    )
open import proof.ImprecisionProperties
  using (⊑-src-wf-idᵢ; ⊑-tgt-wf-idᵢ; ~-sym)
open import proof.NuTermProperties using (CtxWf-⤊)
open import proof.TypeProperties
  using
    ( TySubstWf
    ; TyRenameWf-suc
    ; renameᵗ-id
    ; rename-subst
    ; renameᵗ-preserves-WfTy
    ; subst-cong
    )

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
open import NuTerms
  using (Term)
  renaming
    ( `_ to `ᵀ_
    ; ƛ_ to ƛᵀ_
    ; _·_ to _·ᵀ_
    ; Λ_ to Λᵀ_
    ; ν to νᵀ
    ; $ to $ᵀ
    ; _⊕[_]_ to _⊕ᵀ[_]_
    ; _⟨_⟩ to _⟨ᵀ_⟩
    ; Value to Valueᵀ
    ; _∣_∣_⊢_⦂_ to _∣_∣_⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢· to ⊢ᵀ·
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢ν to ⊢ᵀν
    ; ⊢$ to ⊢ᵀ$
    ; ⊢⊕ to ⊢ᵀ⊕
    ; ⊢⟨⟩ to ⊢ᵀ⟨⟩
    )

------------------------------------------------------------------------
-- Nu coercion for source type application
------------------------------------------------------------------------

ν-subst : Ty → Substᵗ
ν-subst A zero = ⇑ᵗ A
ν-subst A (suc X) = ＇ suc X

ν-subst-target :
  ∀ A B →
  substᵗ (ν-subst A) B ≡ ⇑ᵗ (B [ A ]ᵗ)
ν-subst-target A B =
  trans
    (sym (subst-cong env-eq B))
    (sym (rename-subst suc (singleTyEnv A) B))
  where
    env-eq :
      ∀ X →
      renameᵗ suc (singleTyEnv A X) ≡ ν-subst A X
    env-eq zero = refl
    env-eq (suc X) = refl

ν-subst-wf :
  ∀ {Δ A} →
  WfTy Δ A →
  TySubstWf (suc Δ) (suc Δ) (ν-subst A)
ν-subst-wf hA {zero} z<s =
  renameᵗ-preserves-WfTy hA TyRenameWf-suc
ν-subst-wf hA {suc X} (s<s X<Δ) =
  wfVar (s<s X<Δ)

ν-reveal-env :
  ∀ {Δ A} →
  RevealEnv (suc Δ) zero (⇑ᵗ A) (λ X → X) (ν-subst A)
ν-reveal-env {X = zero} z<s =
  rv-hit refl refl
ν-reveal-env {X = suc X} (s<s X<Δ) =
  rv-miss (λ ()) refl

ν-reveal-typing :
  ∀ {Δ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  singleSealᵈ zero ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ []
    ⊢ reveal B zero (⇑ᵗ A) ∶ B =⇒ ⇑ᵗ (B [ A ]ᵗ)
ν-reveal-typing {A = A} {B = B} hA hB =
  subst
    (λ T →
      singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal B zero (⇑ᵗ A)
        ∶ B =⇒ T)
    (ν-subst-target A B)
    revealed
  where
    revealed′ :
      singleSealᵈ zero ∣ _ ∣ _ ⊢
        reveal (renameᵗ (λ X → X) B) zero (⇑ᵗ A)
        ∶ renameᵗ (λ X → X) B =⇒ substᵗ (ν-subst A) B
    revealed′ =
      reveal-typing-env
        hB
        (λ X<Δ → X<Δ)
        (ν-subst-wf hA)
        ν-reveal-env
        (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
        (here refl)
        singleSealMode

    revealed :
      singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal B zero (⇑ᵗ A)
        ∶ B =⇒ substᵗ (ν-subst A) B
    revealed =
      subst
        (λ S →
          singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal S zero (⇑ᵗ A)
            ∶ S =⇒ substᵗ (ν-subst A) B)
        (renameᵗ-id B)
        revealed′

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
cast⊢ plan M⊢ with down⊢ plan | up⊢ plan
cast⊢ plan M⊢ | _ , down⊢ᵐ | _ , up⊢ᵐ =
  ⊢ᵀ⟨⟩ up⊢ᵐ (⊢ᵀ⟨⟩ down⊢ᵐ M⊢)

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
  Λᵀ N , ⊢ᵀΛ vN N⊢
compile ℓ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA)
    with compile ℓ hΓ M⊢
compile ℓ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA) | M′ , M′⊢ =
  νᵀ A M′ (reveal B zero (⇑ᵗ A)) ,
  ⊢ᵀν wfA M′⊢ (ν-reveal-typing wfA wfB)
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

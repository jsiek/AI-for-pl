{-# OPTIONS --allow-unsolved-metas #-}
module proof.StaticGradualGuarantee where

-- File Charter:
--   * First static gradual guarantee formulation for gradual extrinsic terms.
--   * Defines gradual precision contexts and the `static-gradual-guarantee-indexed`
--     proof.
--   * Depends on gradual term syntax/typing and type imprecision/consistency
--     metatheory.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; zero; suc; z<s; s<s)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( extend-X⊑X
    ; VarPrecCtx
    ; X⊑X
    ; X⊑★
    ; _∋_∶_
    ; _∣_⊢_⦂_⊑_
    ; Imp
    ; ★-⊑-★
    ; X-⊑-★
    ; A-⊑-★
    ; X-⊑-X
    ; α-⊑-α
    ; reflImp
    ; renameImp
    ; ι-⊑-ι
    ; A⇒B-⊑-A′⇒B′
    ; ∀A-⊑-∀B
    ; ∀A-⊑-B
    ; ⊢★-⊑-★
    ; ⊢X-⊑-★
    ; ⊢A-⊑-★
    ; ⊢X-⊑-X
    ; ⊢α-⊑-α
    ; ⊢A⇒B-⊑-A′⇒B′
    ; ⊢∀A-⊑-∀B
    ; ⊢∀A-⊑-B
    ; ⊢ι-⊑-ι
    )
open import Imprecision as Imprecision
open import Consistency
open import GradualTerms
open import Primitives
  using (Const; Prim; constTy; κℕ; constTy-renameᵗ; constTy-⇑ᵗ)
open import Terms
open import proof.ConsistencyProperties
open import proof.GradualTermProperties
open import proof.ImprecisionConsistent
open import proof.ImprecisionProperties
open import proof.TypeProperties
  using
    ( raiseVarFrom-<-inv
    ; raise-ext
    ; rename-raise-ext
    ; rename-raise-⇑ᵗ
    ; renameᵗ-ground-id
    ; renameᵗ-inv-WfTy
    )
open import proof.PreservationImpSubst
  using
    ( ⊑-substᵗ-wt
    ; []⊑ᵗ-rel-wt
    ; singleTyEnv-TySubstWf-extend-X⊑X
    ; singleTyEnv-ImpSubstWt
    ; tysubst-right-⊑
    )
open import proof.PreservationTermSubst
  using (renameᵗ-[]ᵗ; unmap∋-⤊ᵗ; wkImp-extend-X⊑X)

------------------------------------------------------------------------
-- Static gradual guarantee, first formulation
------------------------------------------------------------------------

SGGResult : (Δ : TyCtx) → (Φ : VarPrecCtx) → GPCtx Φ → GTerm → Ty → Set
SGGResult Δ Φ Γ M′ A =
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    ((Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) ×
     (0 ∣ Φ ⊢ p ⦂ A ⊑ B))

static-gradual-guarantee-indexed :
  ∀ {Δ Φ} {Γ : GPCtx Φ} {M M′ A} →
  length Φ ≡ Δ →
  Δ ∣ Φ ⊢ᴳ M ⊑ M′ →
  Δ ∣ leftGCtx Γ ⊢ M ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) × (0 ∣ Φ ⊢ p ⦂ A ⊑ B)

arrow-app-sgg :
  ∀ {Δ Φ} {Γ : GPCtx Φ} {L′ M′ A B A′ D C pF pArg} →
  length Φ ≡ Δ →
  Δ ∣ rightGCtx Γ ⊢ L′ ⦂ D →
  0 ∣ Φ ⊢ pF ⦂ (A ⇒ B) ⊑ D →
  Δ ∣ rightGCtx Γ ⊢ M′ ⦂ C →
  0 ∣ Φ ⊢ pArg ⦂ A′ ⊑ C →
  extend-X~X Δ [] ⊢ A ~ A′ →
  SGGResult Δ Φ Γ (L′ · M′) B
arrow-app-sgg lenΦ L′⊢ (⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢) M′⊢ pArg⊢ A~A′ =
  _ , _ ,
  ⊢· L′⊢ M′⊢ (app-consistencyᵢ lenΦ pA⊢ A~A′ pArg⊢) ,
  pB⊢
arrow-app-sgg lenΦ L′⊢ (⊢A-⊑-★ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢)) M′⊢ pArg⊢ A~A′ =
  ★ , _ ,
  ⊢·★ L′⊢ M′⊢
    (app-consistencyᵢ lenΦ pArg⊢ (extend-X~X-sym A~A′) pA⊢) ,
  pB⊢

star-app-sgg :
  ∀ {Δ Φ} {Γ : GPCtx Φ} {L′ M′ A′ D C pF pArg} →
  length Φ ≡ Δ →
  Δ ∣ rightGCtx Γ ⊢ L′ ⦂ D →
  0 ∣ Φ ⊢ pF ⦂ ★ ⊑ D →
  Δ ∣ rightGCtx Γ ⊢ M′ ⦂ C →
  0 ∣ Φ ⊢ pArg ⦂ A′ ⊑ C →
  extend-X~X Δ [] ⊢ A′ ~ ★ →
  SGGResult Δ Φ Γ (L′ · M′) ★
star-app-sgg lenΦ L′⊢ ⊢★-⊑-★ M′⊢ pArg⊢ A′~★ =
  ★ , ★-⊑-★ ,
  ⊢·★ L′⊢ M′⊢ (app-consistencyᵢ lenΦ pArg⊢ A′~★ ⊢★-⊑-★) ,
  ⊢★-⊑-★
star-app-sgg lenΦ L′⊢ (⊢A-⊑-★ (｀ α) ()) M′⊢ pArg⊢ A′~★
star-app-sgg lenΦ L′⊢ (⊢A-⊑-★ (‵ ι) ()) M′⊢ pArg⊢ A′~★
star-app-sgg lenΦ L′⊢ (⊢A-⊑-★ ★⇒★ ()) M′⊢ pArg⊢ A′~★

static-gradual-guarantee-indexed lenΦ ⊑` (⊢` x∈) with lookup-leftᴳ-inv x∈
static-gradual-guarantee-indexed lenΦ ⊑` (⊢` x∈) | B , p , p⊢ , hᴳ =
  B , p , ⊢` (lookup-rightᴳ hᴳ) , p⊢
static-gradual-guarantee-indexed {Γ = Γ} lenΦ
    (⊑ƛ {A = A} {A′ = A′} {pA = pA} pA⊢ M⊑M′)
    (⊢ƛ wfA M⊢)
    with static-gradual-guarantee-indexed
      {Γ = (A , A′ , pA , pA⊢) ∷ Γ}
      lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (⊑ƛ {A′ = A′} {pA = pA} pA⊢ M⊑M′) (⊢ƛ wfA M⊢)
    | B′ , pB , M′⊢ , pB⊢ =
  A′ ⇒ B′ , A⇒B-⊑-A′⇒B′ pA pB ,
  ⊢ƛ (subst (λ n → WfTy n 0 A′) lenΦ (⊑-tgt-wf pA⊢)) M′⊢ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
static-gradual-guarantee-indexed
    lenΦ
    (⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′)
    with static-gradual-guarantee-indexed lenΦ L⊑L′ L⊢
       | static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′)
    | D , pF , L′⊢ , pF⊢ | C , pArg , M′⊢ , pArg⊢ =
  arrow-app-sgg lenΦ L′⊢ pF⊢ M′⊢ pArg⊢ A~A′
static-gradual-guarantee-indexed
    lenΦ
    (⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★)
    with static-gradual-guarantee-indexed lenΦ L⊑L′ L⊢
       | static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★)
    | D , pF , L′⊢ , pF⊢ | C , pArg , M′⊢ , pArg⊢ =
  star-app-sgg lenΦ L′⊢ pF⊢ M′⊢ pArg⊢ A′~★
static-gradual-guarantee-indexed {Γ = Γ} lenΦ
    (⊑Λ vM vM′ M⊑M′) (⊢Λ vM₀ M⊢)
    with static-gradual-guarantee-indexed
      {Γ = ⇑ᵗᴳPCtx {m = X⊑X} Γ}
      (cong suc lenΦ)
      M⊑M′
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (sym (leftGCtx-⇑ᵗᴳPCtx Γ)) M⊢)
static-gradual-guarantee-indexed {Γ = Γ} lenΦ (⊑Λ vM vM′ M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′⊢ , pB⊢ =
  `∀ B′ , ∀A-⊑-∀B pB ,
  ⊢Λ vM′
    (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
      (rightGCtx-⇑ᵗᴳPCtx Γ) M′⊢) ,
  ⊢∀A-⊑-∀B pB⊢
static-gradual-guarantee-indexed {Γ = Γ} lenΦ
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    with static-gradual-guarantee-indexed
      {Γ = ⇑ᵗᴳPCtx {m = X⊑★} Γ}
      (cong suc lenΦ)
      M⊑M′
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (sym (leftGCtx-⇑ᵗᴳPCtx Γ)) M⊢)
static-gradual-guarantee-indexed {Δ = Δ} {Γ = Γ} lenΦ
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′↑⊢ , pB⊢
    with drop-renameᵗᴳ-wt
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (rightGCtx-⇑ᵗᴳPCtx Γ) M′↑⊢)
static-gradual-guarantee-indexed {Δ = Δ} {Γ = Γ} lenΦ
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′↑⊢ , pB⊢ | B , refl , M′⊢
    =
  B , ∀A-⊑-B B pB , M′⊢ ,
  ⊢∀A-⊑-B (drop-⇑ᵗ-WfTy-extend-X⊑X (⊑-tgt-wf pB⊢)) pB⊢
static-gradual-guarantee-indexed lenΦ
    (⊑`[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    with static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed lenΦ
    (⊑`[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    | `∀ B′ , ∀A-⊑-∀B p , M′⊢ , ⊢∀A-⊑-∀B p⊢
    with []⊑ᵗ-rel-wt p⊢
      (⊑-tgt-wf pT⊢)
      pT⊢
static-gradual-guarantee-indexed lenΦ
    (⊑`[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    | `∀ B′ , ∀A-⊑-∀B p , M′⊢ , ⊢∀A-⊑-∀B p⊢
    | q , q⊢ =
  B′ [ _ ]ᵗ , q ,
  ⊢• M′⊢
    (subst (λ n → WfTy (suc n) 0 B′) lenΦ (⊑-tgt-wf p⊢))
    (subst (λ n → WfTy n 0 _) lenΦ (⊑-tgt-wf pT⊢)) ,
  q⊢
static-gradual-guarantee-indexed lenΦ
    (⊑`[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    | B′ , p , M′⊢ , p⊢ =
  {!!}
static-gradual-guarantee-indexed lenΦ
    (⊑`[]L M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    with static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed lenΦ
    (⊑`[]L M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    | B′ , p , M′⊢ , p⊢ =
  {!!}
static-gradual-guarantee-indexed lenΦ ⊑$ (⊢$ (κℕ n)) =
  ‵ `ℕ , ι-⊑-ι `ℕ , ⊢$ (κℕ n) , ⊢ι-⊑-ι
static-gradual-guarantee-indexed
    lenΦ
    (⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with static-gradual-guarantee-indexed lenΦ L⊑L′ L⊢
       | static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | C , pL , L′⊢ , pL⊢ | D , pM , M′⊢ , pM⊢ =
  ‵ `ℕ , ι-⊑-ι `ℕ ,
  ⊢⊕ L′⊢ (app-consistencyᵢ lenΦ pL⊢ A~ℕ ⊢ι-⊑-ι)
    op M′⊢ (app-consistencyᵢ lenΦ pM⊢ B~ℕ ⊢ι-⊑-ι) ,
  ⊢ι-⊑-ι

static-gradual-guarantee :
  ∀ {Δ} {Γ : GPCtx (extend-X⊑X Δ [])} {M M′ A} →
  Δ ∣ extend-X⊑X Δ [] ⊢ᴳ M ⊑ M′ →
  Δ ∣ leftGCtx Γ ⊢ M ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) × (0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B)
static-gradual-guarantee {Δ = Δ} =
  static-gradual-guarantee-indexed (length-extend-X⊑X[] Δ)

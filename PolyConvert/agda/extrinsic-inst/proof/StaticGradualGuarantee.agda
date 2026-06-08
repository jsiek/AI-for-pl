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
    ; id★
    ; ‵_!
    ; _!
    ; idₓ_
    ; idₛ_
    ; reflImp
    ; rename⊑
    ; idι_
    ; _↦_
    ; ‵∀_
    ; ν_
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
open import GradualTermImprecision
open import Primitives
  using (Const; Prim; constTy; κℕ; constTy-renameᵗ; constTy-⇑ᵗ)
open import proof.ConsistencyProperties
open import proof.GradualTermProperties
open import proof.ImprecisionConsistent
open import proof.ImprecisionProperties
open import proof.PreservationImpSubst using ([]⊑ᵢ-rel-wt; []⊑ᵢ-star-rel-wt)
open import proof.TypeProperties
  using
    ( inst★-renameᵗ-suc
    ; raiseVarFrom-<-inv
    ; raise-ext
    ; rename-raise-ext
    ; rename-raise-⇑ᵗ
    ; renameᵗ-ground-id
    ; renameᵗ-inv-WfTy
    )

------------------------------------------------------------------------
-- Static gradual guarantee, first formulation
------------------------------------------------------------------------

SGGResult : (Δ : TyCtx) → (Φ : VarPrecCtx) → GPCtx Φ →
  GTerm → Ty → Imp → Set₁
SGGResult Δ Φ Γ M′ A p =
  Σ[ B ∈ Ty ]
    ((Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) ×
     (0 ∣ Φ ⊢ p ⦂ A ⊑ B))

static-gradual-guarantee-indexed :
  ∀ {Δ Φ} {Γ : GPCtx Φ} {M M′ A p} →
  length Φ ≡ Δ →
  Δ ∣ Φ ∣ impGCtx Γ ⊢ᴳ M ⊑ M′ ⦂ p →
  Δ ∣ leftGCtx Γ ⊢ M ⦂ A →
  SGGResult Δ Φ Γ M′ A p

arrow-app-sgg :
  ∀ {Δ Φ} {Γ : GPCtx Φ} {L′ M′ A B A′ A″ B′ C pA pB pArg} →
  length Φ ≡ Δ →
  Δ ∣ rightGCtx Γ ⊢ L′ ⦂ (A″ ⇒ B′) →
  0 ∣ Φ ⊢ pA ↦ pB ⦂ (A ⇒ B) ⊑ (A″ ⇒ B′) →
  Δ ∣ rightGCtx Γ ⊢ M′ ⦂ C →
  0 ∣ Φ ⊢ pArg ⦂ A′ ⊑ C →
  extend-X~X Δ [] ⊢ A ~ A′ →
  SGGResult Δ Φ Γ (L′ · M′) B pB
arrow-app-sgg lenΦ L′⊢ (⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢) M′⊢ pArg⊢ A~A′ =
  _ ,
  ⊢· L′⊢ M′⊢ (app-consistencyᵢ lenΦ pA⊢ A~A′ pArg⊢) ,
  pB⊢

star-app-sgg :
  ∀ {Δ Φ} {Γ : GPCtx Φ} {L′ M′ A′ D C pF pArg} →
  length Φ ≡ Δ →
  Δ ∣ rightGCtx Γ ⊢ L′ ⦂ D →
  0 ∣ Φ ⊢ pF ⦂ ★ ⊑ D →
  Δ ∣ rightGCtx Γ ⊢ M′ ⦂ C →
  0 ∣ Φ ⊢ pArg ⦂ A′ ⊑ C →
  extend-X~X Δ [] ⊢ A′ ~ ★ →
  SGGResult Δ Φ Γ (L′ · M′) ★ id★
star-app-sgg lenΦ L′⊢ ⊢★-⊑-★ M′⊢ pArg⊢ A′~★ =
  ★ ,
  ⊢·★ L′⊢ M′⊢ (app-consistencyᵢ lenΦ pArg⊢ A′~★ ⊢★-⊑-★) ,
  ⊢★-⊑-★
star-app-sgg lenΦ L′⊢ (⊢A-⊑-★ (｀ α) ()) M′⊢ pArg⊢ A′~★
star-app-sgg lenΦ L′⊢ (⊢A-⊑-★ (‵ ι) ()) M′⊢ pArg⊢ A′~★
star-app-sgg lenΦ L′⊢ (⊢A-⊑-★ ★⇒★ ()) M′⊢ pArg⊢ A′~★

static-gradual-guarantee-indexed lenΦ (x⊑x p∈) (⊢` x∈)
    with lookup-imp-leftᴳ-inv x∈ p∈
static-gradual-guarantee-indexed lenΦ (x⊑x p∈) (⊢` x∈) | B , p⊢ , hᴳ =
  B , ⊢` (lookup-rightᴳ hᴳ) , p⊢
static-gradual-guarantee-indexed {Γ = Γ} lenΦ
    (ƛ⊑ƛ {A = A} {A′ = A′} {pA = pA} pA⊢ M⊑M′)
    (⊢ƛ wfA M⊢)
    with static-gradual-guarantee-indexed
      {Γ = (A , A′ , pA , pA⊢) ∷ Γ}
      lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (ƛ⊑ƛ {A′ = A′} {pA = pA} pA⊢ M⊑M′) (⊢ƛ wfA M⊢)
    | B′ , M′⊢ , pB⊢ =
  A′ ⇒ B′ ,
  ⊢ƛ (subst (λ n → WfTy n 0 A′) lenΦ (⊑-tgt-wf pA⊢)) M′⊢ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
static-gradual-guarantee-indexed
    lenΦ
    (·⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′)
    with static-gradual-guarantee-indexed lenΦ L⊑L′ L⊢
       | static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (·⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′)
    | A″ ⇒ B′ , L′⊢ , ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
    | C , M′⊢ , pArg⊢ =
  B′ ,
  ⊢· L′⊢ M′⊢ (app-consistencyᵢ lenΦ pA⊢ A~A′ pArg⊢) ,
  pB⊢
static-gradual-guarantee-indexed
    lenΦ
    (·⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★)
    with static-gradual-guarantee-indexed lenΦ L⊑L′ L⊢
       | static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (·⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★)
    | D , L′⊢ , () | C , M′⊢ , pArg⊢
static-gradual-guarantee-indexed {Γ = Γ} lenΦ
    (Λ⊑Λ vM vM′ M⊑M′) (⊢Λ vM₀ M⊢)
    with static-gradual-guarantee-indexed
      {Γ = ⇑ᵗᴳPCtx {m = X⊑X} Γ}
      (cong suc lenΦ)
      (subst (λ Π → _ ∣ _ ∣ Π ⊢ᴳ _ ⊑ _ ⦂ _)
        (sym (impGCtx-⇑ᵗᴳPCtx Γ)) M⊑M′)
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (sym (leftGCtx-⇑ᵗᴳPCtx Γ)) M⊢)
static-gradual-guarantee-indexed {Γ = Γ} lenΦ (Λ⊑Λ vM vM′ M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , M′⊢ , pB⊢ =
  `∀ B′ ,
  ⊢Λ vM′
    (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
      (rightGCtx-⇑ᵗᴳPCtx Γ) M′⊢) ,
  ⊢∀A-⊑-∀B pB⊢
static-gradual-guarantee-indexed {Γ = Γ} lenΦ
    (Λ⊑ vM occA M⊑M′) (⊢Λ vM₀ M⊢)
    with static-gradual-guarantee-indexed
      {Γ = ⇑ᵗᴳPCtx {m = X⊑★} Γ}
      (cong suc lenΦ)
      (subst (λ Π → _ ∣ _ ∣ Π ⊢ᴳ _ ⊑ _ ⦂ _)
        (sym (impGCtx-⇑ᵗᴳPCtx Γ)) M⊑M′)
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (sym (leftGCtx-⇑ᵗᴳPCtx Γ)) M⊢)
static-gradual-guarantee-indexed {Δ = Δ} {Γ = Γ} lenΦ
    (Λ⊑ vM occA M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , M′↑⊢ , pB⊢
    with drop-renameᵗᴳ-wt
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (rightGCtx-⇑ᵗᴳPCtx Γ) M′↑⊢)
static-gradual-guarantee-indexed {Δ = Δ} {Γ = Γ} lenΦ
    (Λ⊑ vM occA M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , M′↑⊢ , pB⊢ | B , refl , M′⊢
    =
  B , M′⊢ ,
  ⊢∀A-⊑-B
    (trans (sym (cong (occurs zero) (src⊑-correct pB⊢))) occA)
    (drop-⇑ᵗ-WfTy-extend-X⊑X (⊑-tgt-wf pB⊢))
    pB⊢
static-gradual-guarantee-indexed lenΦ
    ([]⊑[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    with static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed lenΦ
    ([]⊑[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    | `∀ B′ , M′⊢ , ⊢∀A-⊑-∀B p⊢ =
  B′ [ _ ]ᵗ ,
  ⊢• M′⊢
    (subst (λ n → WfTy (suc n) 0 B′) lenΦ (⊑-tgt-wf p⊢))
    (subst (λ n → WfTy n 0 _) lenΦ (⊑-tgt-wf pT⊢)) ,
  []⊑ᵢ-rel-wt p⊢ (⊑-tgt-wf pT⊢) pT⊢
static-gradual-guarantee-indexed lenΦ
    ([]⊑ M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    with static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed lenΦ
    ([]⊑ M⊑M′ pT⊢) (⊢• M⊢ wfB wfT)
    | B′ , M′⊢ , ⊢∀A-⊑-B occB′ pB′⊢ p⊢ =
  B′ , M′⊢ ,
  cong-⊢⊑ refl (inst★-renameᵗ-suc B′) ([]⊑ᵢ-star-rel-wt p⊢ pT⊢)
static-gradual-guarantee-indexed lenΦ $⊑$ (⊢$ (κℕ n)) =
  ‵ `ℕ , ⊢$ (κℕ n) , ⊢ι-⊑-ι
static-gradual-guarantee-indexed
    lenΦ
    (⊕⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with static-gradual-guarantee-indexed lenΦ L⊑L′ L⊢
       | static-gradual-guarantee-indexed lenΦ M⊑M′ M⊢
static-gradual-guarantee-indexed
    lenΦ
    (⊕⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | C , L′⊢ , pL⊢ | D , M′⊢ , pM⊢ =
  ‵ `ℕ ,
  ⊢⊕ L′⊢ (app-consistencyᵢ lenΦ pL⊢ A~ℕ ⊢ι-⊑-ι)
    op M′⊢ (app-consistencyᵢ lenΦ pM⊢ B~ℕ ⊢ι-⊑-ι) ,
  ⊢ι-⊑-ι

static-gradual-guarantee :
  ∀ {M M′ A p} →
  0 ∣ [] ∣ [] ⊢ᴳ M ⊑ M′ ⦂ p →
  0 ∣ [] ⊢ M ⦂ A →
  Σ[ B ∈ Ty ] (0 ∣ [] ⊢ M′ ⦂ B) × (0 ∣ [] ⊢ p ⦂ A ⊑ B)
static-gradual-guarantee = static-gradual-guarantee-indexed refl

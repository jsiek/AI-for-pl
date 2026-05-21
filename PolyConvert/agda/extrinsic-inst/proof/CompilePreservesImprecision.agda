module proof.CompilePreservesImprecision where

-- File Charter:
--   * Compile-imprecision preservation scaffolding for gradual terms.
--   * Proves the formerly blocking polymorphic `Λ⊑` example using the new
--     target `⊑Λν` rule.
--   * States the closed compile-preservation theorem shape and isolates the
--     remaining compatibility obligations needed for the full structural proof.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Primitives using (κℕ)
open import Imprecision
  using
    ( Imp
    ; VarPrecCtx
    ; ν_
    ; ‵∀_
    ; idι_
    ; _↦_
    ; extend-X⊑X
    ; X⊑X
    ; X⊑★
    ; _∣_⊢_⦂_⊑_
    ; ⊢A⇒B-⊑-A′⇒B′
    ; ⊢∀A-⊑-∀B
    ; ⊢∀A-⊑-B
    ; ⊢ι-⊑-ι
    )
open import Compile using (compile)
open import Consistency using (_⊢_~_; extend-X~X; coerce-⊒; coerce-⊑)
open import GradualTermImprecision using (_∣_∣_⊢ᴳ_⊑_⦂_; Λ⊑; $⊑$)
open import GradualTerms
  renaming
    ( Λ_ to Λᴳ_
    ; $ to $ᴳ
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    )
open import Terms
  renaming
    ( Λ_ to Λᵀ_
    ; $ to $ᵀ
    ; ⊢$ to ⊢ᵀ$
    )
open import TermImprecision
  using
    ( TPEnv
    ; mkTPEnv
    ; ⟪_,_,_,_,_,_⟫
    ; _⊢_⊑_⦂_⊑_
    ; ⊑$
    ; ⊑Λν
    ; ⊑·
    ; ⊑⦂∀
    ; ⊑⦂∀-ν
    ; ⊑⊕
    ; ⊑⇑
    ; ⊑⇓
    ; ⊑-type-imprecision
    )
open import proof.ImprecisionConsistent
  using (coerce-wt-extend-X⊑X; coerce-glbᵢ; plain≤ᵢ)
open import proof.PreservationImpSubst
  using ([]⊑ᵢ-rel-wt; []⊑ᵢ-star-rel-wt)
open import proof.ImprecisionProperties using (cong-⊢⊑; trans-ctx-⊑)
open import proof.TypeProperties using (inst★-renameᵗ-suc)

CompileEnv : ∀ {Φ : VarPrecCtx} → GPCtx Φ → TPEnv
CompileEnv {Φ} Γ = mkTPEnv (length Φ) Φ zero [] zero [] Γ

domain-⊑ :
  ∀ {Ψ Φ A A′ B B′ p q} →
  Ψ ∣ Φ ⊢ p ↦ q ⦂ A ⇒ B ⊑ A′ ⇒ B′ →
  Ψ ∣ Φ ⊢ p ⦂ A ⊑ A′
domain-⊑ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) = p⊢

coerce-midpoint-⊑ :
  ∀ {Φ A A′ C C′ B B′ p⊒ p⊑ pA pC}
    (A~C : extend-X~X (length Φ) [] ⊢ A ~ C)
    (A′~C′ : extend-X~X (length Φ) [] ⊢ A′ ~ C′) →
  zero ∣ extend-X⊑X (length Φ) [] ⊢ p⊒ ⦂ B ⊑ A →
  zero ∣ extend-X⊑X (length Φ) [] ⊢ p⊑ ⦂ B ⊑ C →
  zero ∣ extend-X⊑X (length Φ) [] ⊢ coerce-⊒ A′~C′ ⦂ B′ ⊑ A′ →
  zero ∣ extend-X⊑X (length Φ) [] ⊢ coerce-⊑ A′~C′ ⦂ B′ ⊑ C′ →
  zero ∣ Φ ⊢ pA ⦂ A ⊑ A′ →
  zero ∣ Φ ⊢ pC ⦂ C ⊑ C′ →
  Σ[ r ∈ Imp ] zero ∣ Φ ⊢ r ⦂ B ⊑ B′
coerce-midpoint-⊑ {Φ = Φ} A~C A′~C′ p⊒ p⊑ p′⊒ p′⊑ pA⊢ pC⊢
    with trans-ctx-⊑ (plain≤ᵢ refl) p⊒ pA⊢
       | trans-ctx-⊑ (plain≤ᵢ refl) p⊑ pC⊢
... | pBA′ , pBA′⊢ | pBC′ , pBC′⊢ =
  coerce-glbᵢ A′~C′ p′⊒ p′⊑ pBA′⊢ pBC′⊢ refl refl

wrap-⇓⇑-compat :
  ∀ {E M M′ A A′ B B′ C C′ p p′ q q′ r s} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
  TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p ⦂ B ⊑ A →
  TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ p′ ⦂ B′ ⊑ A′ →
  TPEnv.Ψ E ∣ TPEnv.Φ E ⊢ r ⦂ B ⊑ B′ →
  TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ q ⦂ B ⊑ C →
  TPEnv.Ψ E ∣ extend-X⊑X (TPEnv.Δ E) [] ⊢ q′ ⦂ B′ ⊑ C′ →
  TPEnv.Ψ E ∣ TPEnv.Φ E ⊢ s ⦂ C ⊑ C′ →
  E ⊢ (M ⇓ p) ⇑ q ⊑ (M′ ⇓ p′) ⇑ q′ ⦂ C ⊑ C′
wrap-⇓⇑-compat rel p⊢ p′⊢ r⊢ q⊢ q′⊢ s⊢ =
  ⊑⇑ (⊑⇓ rel p⊢ p′⊢ r⊢) q⊢ q′⊢ s⊢

compiled-coerce-left-compat :
  ∀ {Φ Γ M M′ A A′ C C′ pC}
    (C~A : extend-X~X (length Φ) [] ⊢ C ~ A)
    (C′~A′ : extend-X~X (length Φ) [] ⊢ C′ ~ A′) →
  CompileEnv Γ ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
  zero ∣ Φ ⊢ pC ⦂ C ⊑ C′ →
  CompileEnv Γ ⊢
    (M ⇓ coerce-⊑ C~A) ⇑ coerce-⊒ C~A ⊑
    (M′ ⇓ coerce-⊑ C′~A′) ⇑ coerce-⊒ C′~A′ ⦂ C ⊑ C′
compiled-coerce-left-compat C~A C′~A′ rel pC⊢
    with coerce-wt-extend-X⊑X C~A
       | coerce-wt-extend-X⊑X C′~A′
       | ⊑-type-imprecision rel
compiled-coerce-left-compat C~A C′~A′ rel pC⊢
    | B , B⊑C , B⊑A | B′ , B′⊑C′ , B′⊑A′ | pA , pA⊢
    with coerce-midpoint-⊑ C~A C′~A′ B⊑C B⊑A B′⊑C′ B′⊑A′ pC⊢ pA⊢
compiled-coerce-left-compat C~A C′~A′ rel pC⊢
    | B , B⊑C , B⊑A | B′ , B′⊑C′ , B′⊑A′ | pA , pA⊢
    | r , r⊢ =
  wrap-⇓⇑-compat rel B⊑A B′⊑A′ r⊢ B⊑C B′⊑C′ pC⊢

compiled-coerce-right-compat :
  ∀ {Φ Γ M M′ A A′ C C′ pC}
    (A~C : extend-X~X (length Φ) [] ⊢ A ~ C)
    (A′~C′ : extend-X~X (length Φ) [] ⊢ A′ ~ C′) →
  CompileEnv Γ ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
  zero ∣ Φ ⊢ pC ⦂ C ⊑ C′ →
  CompileEnv Γ ⊢
    (M ⇓ coerce-⊒ A~C) ⇑ coerce-⊑ A~C ⊑
    (M′ ⇓ coerce-⊒ A′~C′) ⇑ coerce-⊑ A′~C′ ⦂ C ⊑ C′
compiled-coerce-right-compat A~C A′~C′ rel pC⊢
    with coerce-wt-extend-X⊑X A~C
       | coerce-wt-extend-X⊑X A′~C′
       | ⊑-type-imprecision rel
compiled-coerce-right-compat A~C A′~C′ rel pC⊢
    | B , B⊑A , B⊑C | B′ , B′⊑A′ , B′⊑C′ | pA , pA⊢
    with coerce-midpoint-⊑ A~C A′~C′ B⊑A B⊑C B′⊑A′ B′⊑C′ pA⊢ pC⊢
compiled-coerce-right-compat A~C A′~C′ rel pC⊢
    | B , B⊑A , B⊑C | B′ , B′⊑A′ , B′⊑C′ | pA , pA⊢
    | r , r⊢ =
  wrap-⇓⇑-compat rel B⊑A B′⊑A′ r⊢ B⊑C B′⊑C′ pC⊢

app-compat :
  ∀ {E L L′ M M′ A A′ B B′} →
  E ⊢ L ⊑ L′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
  E ⊢ L · M ⊑ L′ · M′ ⦂ B ⊑ B′
app-compat = ⊑·

compiled-app-compat :
  ∀ {Φ Γ L L′ M M′ A A′ B B′ C C′}
    (C~A : extend-X~X (length Φ) [] ⊢ C ~ A)
    (C′~A′ : extend-X~X (length Φ) [] ⊢ C′ ~ A′) →
  CompileEnv Γ ⊢ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ →
  CompileEnv Γ ⊢ M ⊑ M′ ⦂ A ⊑ A′ →
  CompileEnv Γ ⊢
    L · ((M ⇓ coerce-⊑ C~A) ⇑ coerce-⊒ C~A) ⊑
    L′ · ((M′ ⇓ coerce-⊑ C′~A′) ⇑ coerce-⊒ C′~A′) ⦂
    B ⊑ B′
compiled-app-compat {Φ = Φ} {Γ = Γ} C~A C′~A′ relL relM
    with ⊑-type-imprecision relL
... | (pC ↦ pB) , pCB⊢ =
  ⊑· relL
    (compiled-coerce-left-compat {Φ = Φ} {Γ = Γ}
      C~A C′~A′ relM (domain-⊑ pCB⊢))

type-app-compat :
  ∀ {Φ Γ M M′ A B T T′ p pT}
    (M⊢ : length Φ ∣ leftGCtx Γ ⊢ᴳ M ⦂ `∀ A)
    (M′⊢ : length Φ ∣ rightGCtx Γ ⊢ᴳ M′ ⦂ `∀ B) →
  CompileEnv Γ ⊢ proj₁ (compile M⊢) ⊑ proj₁ (compile M′⊢) ⦂
    `∀ A ⊑ `∀ B →
  zero ∣ X⊑X ∷ Φ ⊢ p ⦂ A ⊑ B →
  (wfA : WfTy (suc (length Φ)) zero A) →
  (wfB : WfTy (suc (length Φ)) zero B) →
  (wfT : WfTy (length Φ) zero T) →
  (wfT′ : WfTy (length Φ) zero T′) →
  zero ∣ Φ ⊢ pT ⦂ T ⊑ T′ →
  CompileEnv Γ ⊢
    proj₁ (compile (⊢ᴳ• M⊢ wfA wfT)) ⊑
    proj₁ (compile (⊢ᴳ• M′⊢ wfB wfT′)) ⦂
    A [ T ]ᵗ ⊑ B [ T′ ]ᵗ
type-app-compat M⊢ M′⊢ rel p⊢ wfA wfB wfT wfT′ pT⊢ =
  ⊑⦂∀ rel wfA wfB wfT wfT′ ([]⊑ᵢ-rel-wt p⊢ wfT′ pT⊢)

type-app-ν-compat :
  ∀ {Φ Γ M M′ A B T p pT}
    (M⊢ : length Φ ∣ leftGCtx Γ ⊢ᴳ M ⦂ `∀ A)
    (M′⊢ : length Φ ∣ rightGCtx Γ ⊢ᴳ M′ ⦂ B) →
  CompileEnv Γ ⊢ proj₁ (compile M⊢) ⊑ proj₁ (compile M′⊢) ⦂
    `∀ A ⊑ B →
  zero ∣ X⊑★ ∷ Φ ⊢ p ⦂ A ⊑ ⇑ᵗ B →
  (wfA : WfTy (suc (length Φ)) zero A) →
  (wfT : WfTy (length Φ) zero T) →
  zero ∣ Φ ⊢ pT ⦂ T ⊑ ★ →
  CompileEnv Γ ⊢
    proj₁ (compile (⊢ᴳ• M⊢ wfA wfT)) ⊑ proj₁ (compile M′⊢) ⦂
    A [ T ]ᵗ ⊑ B
type-app-ν-compat {B = B} M⊢ M′⊢ rel p⊢ wfA wfT pT⊢ =
  ⊑⦂∀-ν rel wfA wfT
    (cong-⊢⊑ refl (inst★-renameᵗ-suc B) ([]⊑ᵢ-star-rel-wt p⊢ pT⊢))

prim-compat :
  ∀ {E L L′ M M′ op} →
  E ⊢ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ →
  E ⊢ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ →
  E ⊢ L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ
prim-compat = ⊑⊕

ℕᵗ : Ty
ℕᵗ = ‵ `ℕ

compiled-prim-compat :
  ∀ {Φ Γ L L′ M M′ A A′ B B′ op}
    (A~ℕ : extend-X~X (length Φ) [] ⊢ A ~ ℕᵗ)
    (A′~ℕ : extend-X~X (length Φ) [] ⊢ A′ ~ ℕᵗ)
    (B~ℕ : extend-X~X (length Φ) [] ⊢ B ~ ℕᵗ)
    (B′~ℕ : extend-X~X (length Φ) [] ⊢ B′ ~ ℕᵗ) →
  CompileEnv Γ ⊢ L ⊑ L′ ⦂ A ⊑ A′ →
  CompileEnv Γ ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
  CompileEnv Γ ⊢
    (((L ⇓ coerce-⊒ A~ℕ) ⇑ coerce-⊑ A~ℕ) ⊕[ op ]
      ((M ⇓ coerce-⊒ B~ℕ) ⇑ coerce-⊑ B~ℕ)) ⊑
    (((L′ ⇓ coerce-⊒ A′~ℕ) ⇑ coerce-⊑ A′~ℕ) ⊕[ op ]
      ((M′ ⇓ coerce-⊒ B′~ℕ) ⇑ coerce-⊑ B′~ℕ)) ⦂
    ℕᵗ ⊑ ℕᵗ
compiled-prim-compat {Φ = Φ} {Γ = Γ} A~ℕ A′~ℕ B~ℕ B′~ℕ relL relM =
  ⊑⊕
    (compiled-coerce-right-compat {Φ = Φ} {Γ = Γ}
      A~ℕ A′~ℕ relL ⊢ι-⊑-ι)
    (compiled-coerce-right-compat {Φ = Φ} {Γ = Γ}
      B~ℕ B′~ℕ relM ⊢ι-⊑-ι)

source-Λ⊑$ :
  zero ∣ [] ∣ [] ⊢ᴳ (Λᴳ ($ᴳ (κℕ zero))) ⊑ ($ᴳ (κℕ zero)) ⦂
    ν (idι `ℕ)
source-Λ⊑$ = Λ⊑ ($ᴳ (κℕ zero)) $⊑$

source-left-typed :
  zero ∣ [] ⊢ᴳ Λᴳ ($ᴳ (κℕ zero)) ⦂ `∀ ℕᵗ
source-left-typed = ⊢ᴳΛ ($ᴳ (κℕ zero)) (⊢ᴳ$ (κℕ zero))

source-right-typed :
  zero ∣ [] ⊢ᴳ $ᴳ (κℕ zero) ⦂ ℕᵗ
source-right-typed = ⊢ᴳ$ (κℕ zero)

compiled-Λ⊑$ :
  ⟪ zero , zero , [] , zero , [] , [] ⟫ ⊢
    proj₁ (compile source-left-typed) ⊑
    proj₁ (compile source-right-typed) ⦂ `∀ ℕᵗ ⊑ ℕᵗ
compiled-Λ⊑$ =
  ⊑Λν
    ($ᵀ (κℕ zero))
    wfBase
    (⊢ᵀ$ (κℕ zero))
    ⊑$
    ⊢ι-⊑-ι

ClosedCompilePreservation : Set₁
ClosedCompilePreservation =
  ∀ {M M′ A B p} →
  zero ∣ [] ∣ [] ⊢ᴳ M ⊑ M′ ⦂ p →
  (M⊢ : zero ∣ [] ⊢ᴳ M ⦂ A) →
  (M′⊢ : zero ∣ [] ⊢ᴳ M′ ⦂ B) →
  ⟪ zero , zero , [] , zero , [] , [] ⟫ ⊢
    proj₁ (compile M⊢) ⊑ proj₁ (compile M′⊢) ⦂ A ⊑ B

postulate
  closed-compile-preservation :
    ClosedCompilePreservation

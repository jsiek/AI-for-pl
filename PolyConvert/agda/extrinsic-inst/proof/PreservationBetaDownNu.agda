module proof.PreservationBetaDownNu where

-- File Charter:
--   * Worker file for the PolyConvert β-down-ν preservation redex.
--   * Opens the ν-bound imprecision evidence at the freshly allocated seal
--     and types the final reveal conversion from that seal back to the
--     type-application instantiation.
--   * Depends on the local β-up-ν fresh-opening infrastructure, but not on
--     the store-threaded preservation induction hypothesis.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (n≤1+n; _≟_)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym)

open import Types
open import proof.TypeProperties using
  ( TySubstWf
  ; TySubstWf-exts
  ; WfTy-weakenˢ
  ; singleTyEnv-Wf
  )
open import Store using (StoreWf; drop; ⊆ˢ-refl; renameLookupᵗ)
open import Imprecision
open import Conversion
open import Terms
open import proof.PreservationBetaRevealConceal using (cong-⊢↑; cong-⊢↓)
open import proof.PreservationBetaUpNu
  using (length-plains[]; len<suc-StoreWf; open-fresh-ν⊑)
open import proof.PreservationWkTerm using (wk-term)

------------------------------------------------------------------------
-- Local conversion typing for fresh type-variable instantiation
------------------------------------------------------------------------

plainSubstVarFrom-self-seal :
  ∀ X α →
  plainSubstVarFrom X (｀ α) X ≡ ｀ α
plainSubstVarFrom-self-seal zero α = refl
plainSubstVarFrom-self-seal (suc X) α =
  cong (renameᵗ suc) (plainSubstVarFrom-self-seal X α)

plainSubstVarFrom-≢ :
  ∀ X Y (S₁ T₁ : Ty) →
  X ≢ Y →
  plainSubstVarFrom X S₁ Y ≡ plainSubstVarFrom X T₁ Y
plainSubstVarFrom-≢ zero zero S₁ T₁ neq = ⊥-elim (neq refl)
plainSubstVarFrom-≢ zero (suc Y) S₁ T₁ neq = refl
plainSubstVarFrom-≢ (suc X) zero S₁ T₁ neq = refl
plainSubstVarFrom-≢ (suc X) (suc Y) S₁ T₁ neq =
  cong (renameᵗ suc) (plainSubstVarFrom-≢ X Y S₁ T₁ neq′)
  where
    neq′ : X ≢ Y
    neq′ eq = neq (cong suc eq)

mutual
  convert↑At-wt :
    ∀ {Δ Ψ}{Σ : Store}{X α}{T B : Ty} →
    Σ ∋ˢ α ⦂ plainSubstVarFrom X T X →
    TySubstWf (suc Δ) Δ Ψ (plainSubstVarFrom X (｀ α)) →
    TySubstWf (suc Δ) Δ Ψ (plainSubstVarFrom X T) →
    WfTy (suc Δ) Ψ B →
    Δ ∣ Ψ ∣ Σ ⊢ convert↑At X B α ⦂
      substᵗ (plainSubstVarFrom X (｀ α)) B ↑ˢ
      substᵗ (plainSubstVarFrom X T) B
  convert↑At-wt {X = X} {α = α} {T = T} {B = ＇ Y}
    α∈ hSeal hT (wfVar Y<) with X ≟ Y
  convert↑At-wt {X = X} {α = α} {T = T} {B = ＇ .X}
    α∈ hSeal hT (wfVar Y<) | yes refl =
    cong-⊢↑ refl refl (sym (plainSubstVarFrom-self-seal X α)) refl
      (⊢↑-unseal α∈)
  convert↑At-wt {X = X} {α = α} {T = T} {B = ＇ Y}
    α∈ hSeal hT (wfVar Y<) | no neq =
    cong-⊢↑ refl refl refl (plainSubstVarFrom-≢ X Y (｀ α) T neq)
      (⊢↑-id (hSeal Y<))
  convert↑At-wt α∈ hSeal hT (wfSeal α<Ψ) = ⊢↑-id (wfSeal α<Ψ)
  convert↑At-wt α∈ hSeal hT wfBase = ⊢↑-id wfBase
  convert↑At-wt α∈ hSeal hT wf★ = ⊢↑-id wf★
  convert↑At-wt α∈ hSeal hT (wf⇒ wfA wfB) =
    ⊢↑-⇒ (convert↓At-wt α∈ hSeal hT wfA)
          (convert↑At-wt α∈ hSeal hT wfB)
  convert↑At-wt α∈ hSeal hT (wf∀ wfB) =
    ⊢↑-∀
      (convert↑At-wt
        (renameLookupᵗ suc α∈)
        (TySubstWf-exts hSeal)
        (TySubstWf-exts hT)
        wfB)

  convert↓At-wt :
    ∀ {Δ Ψ}{Σ : Store}{X α}{T B : Ty} →
    Σ ∋ˢ α ⦂ plainSubstVarFrom X T X →
    TySubstWf (suc Δ) Δ Ψ (plainSubstVarFrom X (｀ α)) →
    TySubstWf (suc Δ) Δ Ψ (plainSubstVarFrom X T) →
    WfTy (suc Δ) Ψ B →
    Δ ∣ Ψ ∣ Σ ⊢ convert↓At X B α ⦂
      substᵗ (plainSubstVarFrom X T) B ↓ˢ
      substᵗ (plainSubstVarFrom X (｀ α)) B
  convert↓At-wt {X = X} {α = α} {T = T} {B = ＇ Y}
    α∈ hSeal hT (wfVar Y<) with X ≟ Y
  convert↓At-wt {X = X} {α = α} {T = T} {B = ＇ .X}
    α∈ hSeal hT (wfVar Y<) | yes refl =
    cong-⊢↓ refl refl refl (sym (plainSubstVarFrom-self-seal X α))
      (⊢↓-seal α∈)
  convert↓At-wt {X = X} {α = α} {T = T} {B = ＇ Y}
    α∈ hSeal hT (wfVar Y<) | no neq =
    cong-⊢↓ refl refl (plainSubstVarFrom-≢ X Y (｀ α) T neq) refl
      (⊢↓-id (hSeal Y<))
  convert↓At-wt α∈ hSeal hT (wfSeal α<Ψ) = ⊢↓-id (wfSeal α<Ψ)
  convert↓At-wt α∈ hSeal hT wfBase = ⊢↓-id wfBase
  convert↓At-wt α∈ hSeal hT wf★ = ⊢↓-id wf★
  convert↓At-wt α∈ hSeal hT (wf⇒ wfA wfB) =
    ⊢↓-⇒ (convert↑At-wt α∈ hSeal hT wfA)
          (convert↓At-wt α∈ hSeal hT wfB)
  convert↓At-wt α∈ hSeal hT (wf∀ wfB) =
    ⊢↓-∀
      (convert↓At-wt
        (renameLookupᵗ suc α∈)
        (TySubstWf-exts hSeal)
        (TySubstWf-exts hT)
        wfB)

------------------------------------------------------------------------
-- β-down-ν preservation
------------------------------------------------------------------------

preserve-β-down-ν :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B C : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ⇓ (`∀A⊑B B p)) ⦂∀ C [ A ]) ⦂ C [ A ]ᵗ →
  Δ ∣ suc Ψ ∣ ((length Σ , A) ∷ Σ) ∣ Γ ⊢
    ((V ⇓ (p [ ｀ (length Σ) ]⊑)) ↑
      (convert↑ (src⊑ p) (length Σ))) ⦂ C [ A ]ᵗ
preserve-β-down-ν {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
  {V = V} {A = A} {C = C} {p = p} wfΣ vV
  (⊢• (⊢down (⊑-ν {A = Aν} {B = Bν} wfB occ p⊢) V⊢)
      wfC wfA) =
  cong-⊢⦂ refl refl refl
    (cong (λ B → B [ A ]ᵗ) (src⊑-correct p⊢))
    (⊢reveal c⊢ inner⊢)
  where
    len = length Σ

    top : ((len , A) ∷ Σ) ∋ˢ len ⦂ A
    top = Z∋ˢ refl refl

    hSeal :
      TySubstWf (suc Δ) Δ (suc Ψ)
        (plainSubstVarFrom zero (｀ len))
    hSeal =
      singleTyEnv-Wf (｀ len) (wfSeal (len<suc-StoreWf wfΣ))

    hA :
      TySubstWf (suc Δ) Δ (suc Ψ)
        (plainSubstVarFrom zero A)
    hA =
      singleTyEnv-Wf A (WfTy-weakenˢ wfA (n≤1+n Ψ))

    wf-src :
      WfTy (suc Δ) (suc Ψ) (src⊑ p)
    wf-src =
      WfTy-weakenˢ
        (subst
          (λ B → WfTy (suc Δ) Ψ B)
          (sym (src⊑-correct p⊢))
          (subst
            (λ n → WfTy n Ψ Aν)
            (cong suc (length-plains[] Δ))
            (⊑-src-wf p⊢)))
        (n≤1+n Ψ)

    c⊢ :
      Δ ∣ suc Ψ ∣ ((len , A) ∷ Σ) ⊢
        convert↑ (src⊑ p) len ⦂
        (src⊑ p [ ｀ len ]ᵗ) ↑ˢ (src⊑ p [ A ]ᵗ)
    c⊢ = convert↑At-wt top hSeal hA wf-src

    p⊢′ :
      suc Ψ ∣ plains Δ [] ⊢ p [ ｀ len ]⊑ ⦂
        (Aν [ ｀ len ]ᵗ) ⊑ Bν
    p⊢′ = open-fresh-ν⊑ wfΣ p⊢

    V⊢′ :
      Δ ∣ suc Ψ ∣ ((len , A) ∷ Σ) ∣ Γ ⊢ V ⦂ Bν
    V⊢′ = wk-term (n≤1+n Ψ) (drop ⊆ˢ-refl) V⊢

    inner⊢ :
      Δ ∣ suc Ψ ∣ ((len , A) ∷ Σ) ∣ Γ ⊢
        V ⇓ (p [ ｀ len ]⊑) ⦂ src⊑ p [ ｀ len ]ᵗ
    inner⊢ =
      cong-⊢⦂ refl refl refl
        (cong (λ B → B [ ｀ len ]ᵗ) (sym (src⊑-correct p⊢)))
        (⊢down p⊢′ V⊢′)

module proof.PreservationBetaDownForall where

-- File Charter:
--   * Worker proof file for the PolyConvert β-down-∀ preservation redex.
--   * Opens the ∀-bound imprecision evidence with a fresh seal and proves
--     that `convert↑At` converts the opened source body from the fresh seal
--     endpoint to the original type-instantiation endpoint.
--   * Does not depend on the store-threaded preservation induction hypothesis.

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_<_; _≤_; suc; zero; z<s; s<s)
open import Data.Nat.Properties using (_≟_; <-≤-trans; n≤1+n)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym; trans)

open import Types
open import proof.TypeProperties using
  ( TySubstWf
  ; TySubstWf-exts
  ; singleTyEnv-Wf
  ; WfTy-weakenˢ
  ; substᵗ-ground
  ; substᵗ-preserves-WfTy
  )
open import Store
open import Imprecision
open import Conversion
open import Terms
open import proof.PreservationBetaRevealConceal using (cong-⊢↑; cong-⊢↓)
open import proof.PreservationBetaUpNu
  using
    ( VarSubst
    ; cong-⊢⊑
    ; len<suc-StoreWf
    ; length-plains[]
    ; lookup-mode
    ; occurs-substVarFrom-<
    ; plain-var-subst
    ; wk-VarSubst
    )
open import proof.PreservationWkTerm using (wk-term)

------------------------------------------------------------------------
-- Small substitution facts for `plainSubstVarFrom`
------------------------------------------------------------------------

plainSubstVarFrom-seal-self :
  ∀ X α →
  plainSubstVarFrom X (｀ α) X ≡ ｀ α
plainSubstVarFrom-seal-self zero α = refl
plainSubstVarFrom-seal-self (suc X) α =
  cong (renameᵗ suc) (plainSubstVarFrom-seal-self X α)

plainSubstVarFrom-≢ :
  ∀ X Y s t →
  X ≢ Y →
  plainSubstVarFrom X s Y ≡ plainSubstVarFrom X t Y
plainSubstVarFrom-≢ zero zero s t X≢Y = ⊥-elim (X≢Y refl)
plainSubstVarFrom-≢ zero (suc Y) s t X≢Y = refl
plainSubstVarFrom-≢ (suc X) zero s t X≢Y = refl
plainSubstVarFrom-≢ (suc X) (suc Y) s t X≢Y =
  cong (renameᵗ suc)
    (plainSubstVarFrom-≢ X Y s t (λ eq → X≢Y (cong suc eq)))

------------------------------------------------------------------------
-- Conversion typing for fresh ∀ opening
------------------------------------------------------------------------

mutual
  convert↑At-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{X : TyVar}{A T : Ty}{α : Seal} →
    TySubstWf Δ Δ′ Ψ (plainSubstVarFrom X (｀ α)) →
    TySubstWf Δ Δ′ Ψ (plainSubstVarFrom X T) →
    Σ ∋ˢ α ⦂ plainSubstVarFrom X T X →
    WfTy Δ Ψ A →
    Δ′ ∣ Ψ ∣ Σ ⊢ convert↑At X A α ⦂
      substᵗ (plainSubstVarFrom X (｀ α)) A ↑ˢ
      substᵗ (plainSubstVarFrom X T) A
  convert↑At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    with X ≟ Y
  convert↑At-wt {X = X} hSeal hT hα (wfVar {X = .X} X<Δ)
    | yes refl =
    cong-⊢↑ refl refl (sym (plainSubstVarFrom-seal-self X _)) refl
      (⊢↑-unseal hα)
  convert↑At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    | no X≢Y =
    cong-⊢↑ refl refl refl (plainSubstVarFrom-≢ X Y (｀ _) _ X≢Y)
      (⊢↑-id (hSeal Y<Δ))
  convert↑At-wt hSeal hT hα (wfSeal α<Ψ) = ⊢↑-id (wfSeal α<Ψ)
  convert↑At-wt hSeal hT hα wfBase = ⊢↑-id wfBase
  convert↑At-wt hSeal hT hα wf★ = ⊢↑-id wf★
  convert↑At-wt hSeal hT hα (wf⇒ wfA wfB) =
    ⊢↑-⇒ (convert↓At-wt hSeal hT hα wfA)
          (convert↑At-wt hSeal hT hα wfB)
  convert↑At-wt hSeal hT hα (wf∀ wfA) =
    ⊢↑-∀
      (convert↑At-wt
        (TySubstWf-exts hSeal)
        (TySubstWf-exts hT)
        (renameLookupᵗ suc hα)
        wfA)

  convert↓At-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{X : TyVar}{A T : Ty}{α : Seal} →
    TySubstWf Δ Δ′ Ψ (plainSubstVarFrom X (｀ α)) →
    TySubstWf Δ Δ′ Ψ (plainSubstVarFrom X T) →
    Σ ∋ˢ α ⦂ plainSubstVarFrom X T X →
    WfTy Δ Ψ A →
    Δ′ ∣ Ψ ∣ Σ ⊢ convert↓At X A α ⦂
      substᵗ (plainSubstVarFrom X T) A ↓ˢ
      substᵗ (plainSubstVarFrom X (｀ α)) A
  convert↓At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    with X ≟ Y
  convert↓At-wt {X = X} hSeal hT hα (wfVar {X = .X} X<Δ)
    | yes refl =
    cong-⊢↓ refl refl refl (sym (plainSubstVarFrom-seal-self X _))
      (⊢↓-seal hα)
  convert↓At-wt {X = X} hSeal hT hα (wfVar {X = Y} Y<Δ)
    | no X≢Y =
    cong-⊢↓ refl refl (plainSubstVarFrom-≢ X Y (｀ _) _ X≢Y) refl
      (⊢↓-id (hSeal Y<Δ))
  convert↓At-wt hSeal hT hα (wfSeal α<Ψ) = ⊢↓-id (wfSeal α<Ψ)
  convert↓At-wt hSeal hT hα wfBase = ⊢↓-id wfBase
  convert↓At-wt hSeal hT hα wf★ = ⊢↓-id wf★
  convert↓At-wt hSeal hT hα (wf⇒ wfA wfB) =
    ⊢↓-⇒ (convert↑At-wt hSeal hT hα wfA)
          (convert↓At-wt hSeal hT hα wfB)
  convert↓At-wt hSeal hT hα (wf∀ wfA) =
    ⊢↓-∀
      (convert↓At-wt
        (TySubstWf-exts hSeal)
        (TySubstWf-exts hT)
        (renameLookupᵗ suc hα)
        wfA)

convert↑-fresh-wt :
  ∀ {Δ Ψ}{Σ : Store}{A T : Ty} →
  StoreWf Δ Ψ Σ →
  WfTy (suc Δ) Ψ A →
  WfTy Δ Ψ T →
  Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ⊢
    convert↑ A (length Σ) ⦂
    A [ ｀ (length Σ) ]ᵗ ↑ˢ A [ T ]ᵗ
convert↑-fresh-wt wfΣ wfA wfT =
  convert↑At-wt
    (singleTyEnv-Wf (｀ _) (wfSeal (len<suc-StoreWf wfΣ)))
    (singleTyEnv-Wf _ (WfTy-weakenˢ wfT (n≤1+n _)))
    (Z∋ˢ refl refl)
    (WfTy-weakenˢ wfA (n≤1+n _))

------------------------------------------------------------------------
-- Opening ∀-bound imprecision evidence with a fresh seal
------------------------------------------------------------------------

subst-var-plain-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ X m} →
  StoreWf Δ Ψ Σ →
  (Φ ++ plain ∷ plains Δ []) ∋ X ∶ m →
  VarSubst (suc Ψ) (Φ ++ plains Δ [])
    (plainSubstVarFrom (length Φ) (｀ (length Σ)) X) m
subst-var-plain-prefix {Φ = []} wfΣ here =
  ⊑-｀ (wfSeal (len<suc-StoreWf wfΣ))
subst-var-plain-prefix {Ψ = Ψ} {Φ = []} wfΣ (there x∈) =
  plain-var-subst {Ψ = suc Ψ} x∈
subst-var-plain-prefix {Φ = plain ∷ Φ} wfΣ here = ⊑-＇ here
subst-var-plain-prefix {Φ = plain ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-plain-prefix {Φ = Φ} wfΣ x∈)
subst-var-plain-prefix {Φ = ν-bound ∷ Φ} wfΣ here = ⊑-★ν here
subst-var-plain-prefix {Φ = ν-bound ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-plain-prefix {Φ = Φ} wfΣ x∈)

varSubst-wf :
  ∀ {Ψ Γ A m} →
  VarSubst Ψ Γ A m →
  WfTy (length Γ) Ψ A
varSubst-wf {m = plain} h = ⊑-src-wf h
varSubst-wf {m = ν-bound} h = ⊑-src-wf h

substWf-plain-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ} →
  StoreWf Δ Ψ Σ →
  TySubstWf
    (length (Φ ++ plain ∷ plains Δ []))
    (length (Φ ++ plains Δ []))
    (suc Ψ)
    (plainSubstVarFrom (length Φ) (｀ (length Σ)))
substWf-plain-prefix {Φ = Φ} wfΣ X<len =
  varSubst-wf
    (subst-var-plain-prefix {Φ = Φ} wfΣ (proj₂ (lookup-mode _ X<len)))

open-fresh-∀⊑-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ : ICtx}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (Φ ++ plain ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ (Φ ++ plains Δ []) ⊢
    substPlainAtImp (length Φ) (｀ (length Σ)) p ⦂
    substᵗ (plainSubstVarFrom (length Φ) (｀ (length Σ))) A ⊑
    substᵗ (plainSubstVarFrom (length Φ) (｀ (length Σ))) B
open-fresh-∀⊑-prefix wfΣ ⊑-★★ = ⊑-★★
open-fresh-∀⊑-prefix wfΣ (⊑-★ν xν) =
  subst-var-plain-prefix wfΣ xν
open-fresh-∀⊑-prefix wfΣ (⊑-★ g p⊢) =
  ⊑-★ (substᵗ-ground _ g) (open-fresh-∀⊑-prefix wfΣ p⊢)
open-fresh-∀⊑-prefix wfΣ (⊑-＇ x∈) =
  subst-var-plain-prefix wfΣ x∈
open-fresh-∀⊑-prefix wfΣ (⊑-｀ (wfSeal α<Ψ)) =
  ⊑-｀ (wfSeal (<-≤-trans α<Ψ (n≤1+n _)))
open-fresh-∀⊑-prefix wfΣ ⊑-‵ = ⊑-‵
open-fresh-∀⊑-prefix wfΣ (⊑-⇒ p⊢ q⊢) =
  ⊑-⇒ (open-fresh-∀⊑-prefix wfΣ p⊢)
       (open-fresh-∀⊑-prefix wfΣ q⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊑-∀ p⊢) =
  ⊑-∀ (open-fresh-∀⊑-prefix {Φ = plain ∷ Φ} wfΣ p⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊑-ν {A = A} {B = B} wfB occ p⊢) =
  ⊑-ν
    (substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (n≤1+n _))
      (substWf-plain-prefix {Φ = Φ} wfΣ))
    (trans
      (occurs-substVarFrom-< (suc (length Φ)) zero (｀ _) A z<s)
      occ)
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc
        (plainSubstVarFrom (length Φ) (｀ _))
        B)
      (open-fresh-∀⊑-prefix {Φ = ν-bound ∷ Φ} wfΣ p⊢))

open-fresh-∀⊑ :
  ∀ {Δ Ψ}{Σ : Store}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (plain ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ plains Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
    A [ ｀ (length Σ) ]ᵗ ⊑ B [ ｀ (length Σ) ]ᵗ
open-fresh-∀⊑ wfΣ p⊢ =
  open-fresh-∀⊑-prefix {Φ = []} wfΣ p⊢

------------------------------------------------------------------------
-- β-down-∀ preservation
------------------------------------------------------------------------

preserve-β-down-∀ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ⇓ (`∀A⊑∀B p)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
  Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ Γ ⊢
    (((V ⦂∀ (tgt⊑ p) [ ｀ (length Σ) ]) ⇓
      (p [ ｀ (length Σ) ]⊑)) ↑ (convert↑ (src⊑ p) (length Σ)))
    ⦂ B [ T ]ᵗ
preserve-β-down-∀ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {V = V} {T = T} {p = p}
  wfΣ vV
  (⊢• (⊢down (⊑-∀ {A = Aₚ} {B = Bₚ} p⊢) V⊢) wfB wfT) =
  cong-⊢⦂ refl refl refl (cong (λ A → A [ T ]ᵗ) eq-src)
    (⊢reveal c⊢ (⊢down p-open⊢ app⊢))
  where
    eq-src = src⊑-correct p⊢
    eq-tgt = tgt⊑-correct p⊢

    wf-src : WfTy (suc Δ) Ψ (src⊑ p)
    wf-src =
      subst
        (λ A → WfTy (suc Δ) Ψ A)
        (sym eq-src)
        (subst
          (λ n → WfTy n Ψ Aₚ)
          (cong suc (length-plains[] Δ))
          (⊑-src-wf p⊢))

    wf-tgt : WfTy (suc Δ) Ψ (tgt⊑ p)
    wf-tgt =
      subst
        (λ A → WfTy (suc Δ) Ψ A)
        (sym eq-tgt)
        (subst
          (λ n → WfTy n Ψ Bₚ)
          (cong suc (length-plains[] Δ))
          (⊑-tgt-wf p⊢))

    V⊢′ :
      _ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ _ ⊢ V ⦂ `∀ (tgt⊑ p)
    V⊢′ =
      cong-⊢⦂ refl refl refl (cong `∀ (sym eq-tgt))
        (wk-term (n≤1+n Ψ) (drop ⊆ˢ-refl) V⊢)

    app⊢ :
      _ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ _ ⊢
      V ⦂∀ tgt⊑ p [ ｀ (length Σ) ] ⦂
      tgt⊑ p [ ｀ (length Σ) ]ᵗ
    app⊢ =
      ⊢•
        V⊢′
        (WfTy-weakenˢ wf-tgt (n≤1+n Ψ))
        (wfSeal (len<suc-StoreWf wfΣ))

    p-open⊢ :
      suc Ψ ∣ plains Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
      tgt⊑ p [ ｀ (length Σ) ]ᵗ ⊒
      src⊑ p [ ｀ (length Σ) ]ᵗ
    p-open⊢ =
      cong-⊢⊑
        (cong (λ A → A [ ｀ (length Σ) ]ᵗ) (sym eq-src))
        (cong (λ A → A [ ｀ (length Σ) ]ᵗ) (sym eq-tgt))
        (open-fresh-∀⊑ wfΣ p⊢)

    c⊢ :
      _ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ⊢
      convert↑ (src⊑ p) (length Σ) ⦂
      src⊑ p [ ｀ (length Σ) ]ᵗ ↑ˢ src⊑ p [ T ]ᵗ
    c⊢ = convert↑-fresh-wt wfΣ wf-src wfT

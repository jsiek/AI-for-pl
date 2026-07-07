{-# OPTIONS --allow-unsolved-metas #-}

module proof.CatchupMediated where

-- File Charter:
--   * The left catchup lemma over the mediated narrowing relation:
--     the source term reduces to a value while the relation is
--     transported across the accumulated left store changes.
--   * Port of `proof.CatchupSeparated.catchup-lemmaˡ` (whose proof
--     skeleton is likewise open).  The decisive difference is in the
--     statement: the returned relation keeps the ORIGINAL coercion
--     index `p` — under the mediated judgment a source store change
--     never rewrites the index raw (`left-changes-transportᵐ`) —
--     where the old statement had to return `applyCoercions χs p`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Types
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; leftStore-applyLeftChanges
  )
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; narrowing-dual¹-applyCoercions
  ; rightStore-applyLeftChanges
  )
open import proof.DGGStoreChangeMediated using
  ( applyLeftChanges-⇑ʳᶜorr
  ; corr-⇑ʳᶜorr-inv
  )

catchup-zeroᵐ :
  ∀ {ΔL ΔR ρ M V p A B} →
  Value M →
  No• M →
  ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ V ∶ p ⦂ A ⊒ᵐ B →
  ∃[ χs ] ∃[ W ] ∃[ ΔL′ ]
    Value W ×
    No• W ×
    (M —↠[ χs ] W) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) ×
    (leftStore (applyLeftChanges χs ρ) ≡
      applyStores χs (leftStore ρ)) ×
    (rightStore (applyLeftChanges χs ρ) ≡ rightStore ρ) ×
    (ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ p ∶ᶜ applyTys χs A ⊒ᵐ B) ×
    ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
      ⊢ W ⊒ V ∶ p ⦂ applyTys χs A ⊒ᵐ B
catchup-zeroᵐ {ΔL = ΔL} vM noM pᶜ M⊒V =
  [] , _ , ΔL , vM , noM , ↠-refl , refl ,
  narrowing-store-corrᵐᶜ pᶜ , refl , refl , pᶜ , M⊒V

catchup-lemmaᵐ :
  ∀ {ΔL ΔR ρ M V p A B} →
  RuntimeOK M →
  Value V →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ V ∶ p ⦂ A ⊒ᵐ B →
  ∃[ χs ] ∃[ W ] ∃[ ΔL′ ]
    Value W ×
    No• W ×
    (M —↠[ χs ] W) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) ×
    (leftStore (applyLeftChanges χs ρ) ≡
      applyStores χs (leftStore ρ)) ×
    (rightStore (applyLeftChanges χs ρ) ≡ rightStore ρ) ×
    (ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ p ∶ᶜ applyTys χs A ⊒ᵐ B) ×
    ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
      ⊢ W ⊒ V ∶ p ⦂ applyTys χs A ⊒ᵐ B
catchup-lemmaᵐ (ok-no noM) () (⊒blameᵗ M⊢ q⊒)
catchup-lemmaᵐ (ok-no noM) () (x⊒xᵗ qᶜ x∋q)
catchup-lemmaᵐ (ok-no noM) (ƛ N′) rel@(ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  catchup-zeroᵐ (ƛ _) noM p↦qᶜ rel
catchup-lemmaᵐ (ok-no noM) () (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
catchup-lemmaᵐ (ok-no noM) (Λ vV′) rel@(Λ⊒Λᵗ allᶜ vV vV′₁ V⊒V′) =
  catchup-zeroᵐ (Λ vV) noM allᶜ rel
catchup-lemmaᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    (ok-no noM) (Λ vV′)
    (⊒Λᵗ {N = N} {V′ = V′} {p = p} {A = A} {Aʳ = Aʳ} {B = B}
      N⊢ genᶜ vV′₁ N⊒V′) =
  let
    χs , W , ΔL′ , vW , noW , N↠W , ΔL′≡ , corr⇑₀ ,
      left⇑≡ , right⇑≡ , pᶜ′ , W⊒V′₀ =
      catchup-lemmaᵐ (ok-no noM) vV′ N⊒V′

    ρ⇑≡ :
      applyLeftChanges χs (⇑ʳᶜorr ρ) ≡
        ⇑ʳᶜorr (applyLeftChanges χs ρ)
    ρ⇑≡ = applyLeftChanges-⇑ʳᶜorr χs ρ

    corr⇑ :
      StoreCorr ΔL′ (suc ΔR) (⇑ʳᶜorr (applyLeftChanges χs ρ))
    corr⇑ = subst (λ ρ₀ → StoreCorr ΔL′ (suc ΔR) ρ₀) ρ⇑≡ corr⇑₀

    corr : StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ)
    corr = corr-⇑ʳᶜorr-inv corr⇑

    corr₀ : StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corr₀ = subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χs ρ)) ΔL′≡ corr

    genᶜ′ : ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ gen Aʳ p ∶ᶜ applyTys χs A ⊒ᵐ `∀ B
    genᶜ′ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χs ρ
            ⊢ gen Aʳ p ∶ᶜ applyTys χs A ⊒ᵐ `∀ B)
        (sym ΔL′≡)
        (left-changes-transportᵐ χs corr₀ genᶜ)

    W⊒V′ :
      ΔL′ ∣ suc ΔR ∣ ⇑ʳᶜorr (applyLeftChanges χs ρ) ∣ []
        ⊢ W ⊒ V′ ∶ p ⦂ applyTys χs A ⊒ᵐ B
    W⊒V′ =
      subst
        (λ ρ₀ →
          ΔL′ ∣ suc ΔR ∣ ρ₀ ∣ []
            ⊢ W ⊒ V′ ∶ p ⦂ applyTys χs A ⊒ᵐ B)
        ρ⇑≡
        W⊒V′₀

    W⊢⇑ :
      ΔL′ ∣ leftStore (⇑ʳᶜorr (applyLeftChanges χs ρ)) ∣ [] ⊢
        W ⦂ applyTys χs A
    W⊢⇑ = typed-term-narrowing-source-typingᵐᶜ W⊒V′

    W⊢ :
      ΔL′ ∣ leftStore (applyLeftChanges χs ρ) ∣ [] ⊢ W ⦂ applyTys χs A
    W⊢ = subst (λ Σ → ΔL′ ∣ Σ ∣ [] ⊢ W ⦂ applyTys χs A)
                (leftStore-⇑ʳᶜorr (applyLeftChanges χs ρ)) W⊢⇑

    W⊒ΛV′ :
      ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ W ⊒ Λ V′ ∶ gen Aʳ p ⦂ applyTys χs A ⊒ᵐ `∀ B
    W⊒ΛV′ = ⊒Λᵗ W⊢ genᶜ′ vV′ W⊒V′
  in
  χs , W , ΔL′ , vW , noW , N↠W , ΔL′≡ , corr ,
  leftStore-applyLeftChanges χs ρ , rightStore-applyLeftChanges χs ρ ,
  genᶜ′ , W⊒ΛV′
catchup-lemmaᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    (ok-no noM) (vV′ ⟨ gen Aʳ s ⟩)
    (⊒⟨ν⟩ᵗ {N = N} {V′ = V′} {p = p} {s = s} {A = A}
      {Aʳ = Aʳ} {B = B} {η = η} N⊢ genS⊢ V′⊢ genᶜ i N⊒V′s) =
  let
    χs , W , ΔL′ , vW , noW , N↠W , ΔL′≡ , corr⇑₀ ,
      left⇑≡ , right⇑≡ , pᶜ′ , W⊒V′s₀ =
      catchup-lemmaᵐ (ok-no noM) (vV′ ⟨ i ⟩) N⊒V′s

    ρ⇑≡ :
      applyLeftChanges χs (⇑ʳᶜorr ρ) ≡
        ⇑ʳᶜorr (applyLeftChanges χs ρ)
    ρ⇑≡ = applyLeftChanges-⇑ʳᶜorr χs ρ

    corr⇑ :
      StoreCorr ΔL′ (suc ΔR) (⇑ʳᶜorr (applyLeftChanges χs ρ))
    corr⇑ = subst (λ ρ₀ → StoreCorr ΔL′ (suc ΔR) ρ₀) ρ⇑≡ corr⇑₀

    corr : StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ)
    corr = corr-⇑ʳᶜorr-inv corr⇑

    corr₀ : StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corr₀ = subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χs ρ)) ΔL′≡ corr

    genᶜ′ : ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ gen Aʳ p ∶ᶜ applyTys χs A ⊒ᵐ `∀ B
    genᶜ′ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χs ρ
            ⊢ gen Aʳ p ∶ᶜ applyTys χs A ⊒ᵐ `∀ B)
        (sym ΔL′≡)
        (left-changes-transportᵐ χs corr₀ genᶜ)

    W⊒V′s :
      ΔL′ ∣ suc ΔR ∣ ⇑ʳᶜorr (applyLeftChanges χs ρ) ∣ []
        ⊢ W ⊒ V′ ⟨ s ⟩ ∶ p ⦂ applyTys χs A ⊒ᵐ B
    W⊒V′s =
      subst
        (λ ρ₀ →
          ΔL′ ∣ suc ΔR ∣ ρ₀ ∣ []
            ⊢ W ⊒ V′ ⟨ s ⟩ ∶ p ⦂ applyTys χs A ⊒ᵐ B)
        ρ⇑≡
        W⊒V′s₀

    W⊢⇑ :
      ΔL′ ∣ leftStore (⇑ʳᶜorr (applyLeftChanges χs ρ)) ∣ [] ⊢
        W ⦂ applyTys χs A
    W⊢⇑ = typed-term-narrowing-source-typingᵐᶜ W⊒V′s

    W⊢ :
      ΔL′ ∣ leftStore (applyLeftChanges χs ρ) ∣ [] ⊢ W ⦂ applyTys χs A
    W⊢ = subst (λ Σ → ΔL′ ∣ Σ ∣ [] ⊢ W ⦂ applyTys χs A)
                (leftStore-⇑ʳᶜorr (applyLeftChanges χs ρ)) W⊢⇑

    genS⊢′ :
      η ∣ ΔR ∣ rightStore (applyLeftChanges χs ρ) ⊢ gen Aʳ s ∶ Aʳ ⊒ `∀ B
    genS⊢′ =
      subst
        (λ Σ → η ∣ ΔR ∣ Σ ⊢ gen Aʳ s ∶ Aʳ ⊒ `∀ B)
        (sym (rightStore-applyLeftChanges χs ρ))
        genS⊢

    V′⊢′ : ΔR ∣ rightStore (applyLeftChanges χs ρ) ∣ [] ⊢ V′ ⦂ Aʳ
    V′⊢′ = subst (λ Σ → ΔR ∣ Σ ∣ [] ⊢ V′ ⦂ Aʳ)
                 (sym (rightStore-applyLeftChanges χs ρ)) V′⊢

    W⊒target :
      ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ W ⊒ V′ ⟨ gen Aʳ s ⟩
          ∶ gen Aʳ p ⦂ applyTys χs A ⊒ᵐ `∀ B
    W⊒target = ⊒⟨ν⟩ᵗ W⊢ genS⊢′ V′⊢′ genᶜ′ i W⊒V′s
  in
  χs , W , ΔL′ , vW , noW , N↠W , ΔL′≡ , corr ,
  leftStore-applyLeftChanges χs ρ , rightStore-applyLeftChanges χs ρ ,
  genᶜ′ , W⊒target
catchup-lemmaᵐ (ok-no noM) () (α⊒αᵗ vL noL vL′ noL′ qᶜ pᶜ L⊒L′)
catchup-lemmaᵐ (ok-no noM) () (⊒αᵗ vL′ noL′ pᶜ L⊒L′)
catchup-lemmaᵐ (ok-no noM) () (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
catchup-lemmaᵐ (ok-no noM) () (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
catchup-lemmaᵐ (ok-no noM) ($ κ) rel@(κ⊒κᵗ κ qᶜ) =
  catchup-zeroᵐ ($ κ) noM qᶜ rel
catchup-lemmaᵐ (ok-no noM) () (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′)
catchup-lemmaᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    (ok-no noM) (vM′ ⟨ i ⟩)
    (⊒cast+ᵗ {M′ = M′} {p = p} {t = t} {A = A} {B = B} {C = C}
      {η = η} pᶜ rᶜ t⊒ M⊒M′) =
  let
    χs , W , ΔL′ , vW , noW , M↠W , ΔL′≡ , corr ,
      left≡ , right≡ , rᶜ′ , W⊒M′ =
      catchup-lemmaᵐ (ok-no noM) vM′ M⊒M′

    corr₀ : StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corr₀ = subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χs ρ)) ΔL′≡ corr

    pᶜ′ : ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ p ∶ᶜ applyTys χs A ⊒ᵐ C
    pᶜ′ =
      subst
        (λ Δ → Δ ∣ ΔR ∣ applyLeftChanges χs ρ
          ⊢ p ∶ᶜ applyTys χs A ⊒ᵐ C)
        (sym ΔL′≡)
        (left-changes-transportᵐ χs corr₀ pᶜ)

    t⊒′ : η ∣ ΔR ∣ rightStore (applyLeftChanges χs ρ) ⊢ t ∶ C ⊒ B
    t⊒′ = subst (λ Σ → η ∣ ΔR ∣ Σ ⊢ t ∶ C ⊒ B)
                 (sym (rightStore-applyLeftChanges χs ρ)) t⊒

    dual≡ : narrowing-dual¹ t⊒′ ≡ narrowing-dual¹ t⊒
    dual≡ = narrowing-dual¹-applyCoercions [] t⊒ t⊒′

    W⊒target :
      ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ W ⊒ M′ ⟨ narrowing-dual¹ t⊒ ⟩ ∶ p
          ⦂ applyTys χs A ⊒ᵐ C
    W⊒target =
      subst
        (λ d →
          ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ W ⊒ M′ ⟨ d ⟩ ∶ p ⦂ applyTys χs A ⊒ᵐ C)
        dual≡
        (⊒cast+ᵗ pᶜ′ rᶜ′ t⊒′ W⊒M′)
  in
  χs , W , ΔL′ , vW , noW , M↠W , ΔL′≡ , corr ,
  left≡ , right≡ , pᶜ′ , W⊒target
catchup-lemmaᵐ (ok-no noM) vV (⊒cast-ᵗ pᶜ rᶜ t⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-no noM) vV (cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-no noM) vV (cast-⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-• vW noW) vV ()
catchup-lemmaᵐ (ok-·₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-·₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-ν okL) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⊕₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⊕₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⟨⟩ okM) vV M⊒V = {! ? !}

{-# OPTIONS --allow-unsolved-metas #-}

module proof.DGGPrimitiveMediated where

-- File Charter:
--   * Mediated-store DGG helpers for primitive addition delta steps.
--   * Packages operand catchup and constant delta reduction.
--   * Exported by proof.DynamicGradualGuaranteeMediated for the main DGG.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using (cross; id-‵)
open import Primitives using (addℕ; κℕ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.NuProgress using (canonical-ℕ; nv-const)
open import proof.LeftChangeNarrowingSeparated using
  (applyTerms-preserves-RuntimeOK)
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyTerms-const
  ; applyTyCtxs-++
  ; applyTys-++
  ; applyTys-ℕ
  ; applyTys-ℕ-applyTys
  ; ⊕₁-↠
  ; ⊕₂-↠
  ; ↠-trans
  )

id-ℕ-narrowingᵐᶜ :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  ΔL ∣ ΔR ∣ ρ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ᵐ ‵ `ℕ
id-ℕ-narrowingᵐᶜ stores =
  stores ,
  wfBase ,
  wfBase ,
  ‵ `ℕ ,
  med-base ,
  (cast-id wfBase refl , cross (id-‵ `ℕ))

constant-⊕-δ-step :
  ∀ {χsL χsR L R m n} →
  L ≡ $ (κℕ m) →
  R ≡ $ (κℕ n) →
  applyTerms χsL L ⊕[ addℕ ] applyTerms χsR R
    —↠[ keep ∷ [] ] $ (κℕ (m + n))
constant-⊕-δ-step {χsL = χsL} {χsR = χsR} {m = m} {n = n}
    L≡ R≡
    rewrite L≡ | applyTerms-const χsL (κℕ m)
          | R≡ | applyTerms-const χsR (κℕ n) =
  ↠-step (pure-step δ-⊕) ↠-refl

const-narrowing-targetᵐᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B m n} →
  M ≡ $ (κℕ m) →
  M′ ≡ $ (κℕ n) →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  m ≡ n
const-narrowing-targetᵐᶜ eqM () (⊒blameᵗ M⊢ pᶜ)
const-narrowing-targetᵐᶜ () eqM′ (x⊒xᵗ pᶜ x∋p)
const-narrowing-targetᵐᶜ () eqM′ (ƛ⊒ƛᵗ p↦qᶜ N⊒N′)
const-narrowing-targetᵐᶜ () eqM′ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
const-narrowing-targetᵐᶜ () eqM′ (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′)
const-narrowing-targetᵐᶜ eqM () (⊒Λᵗ typing genᶜ vV′ N⊒V′)
const-narrowing-targetᵐᶜ eqM ()
    (⊒⟨ν⟩ᵗ typing genS⊢ V′⊢ genᶜ i N⊒V′s)
const-narrowing-targetᵐᶜ () eqM′
    (α⊒αᵗ vL noL vL′ noL′ qᶜ pᶜ L⊒L′)
const-narrowing-targetᵐᶜ eqM () (⊒αᵗ vL′ noL′ pᶜ L⊒L′)
const-narrowing-targetᵐᶜ () eqM′
    (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
const-narrowing-targetᵐᶜ eqM ()
    (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
const-narrowing-targetᵐᶜ refl refl (κ⊒κᵗ (κℕ n) pᶜ) = refl
const-narrowing-targetᵐᶜ () eqM′ (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′)
const-narrowing-targetᵐᶜ eqM () (⊒cast+ᵗ pᶜ rᶜ t⊒ M⊒M′)
const-narrowing-targetᵐᶜ eqM () (⊒cast-ᵗ pᶜ rᶜ t⊒ M⊒M′)
const-narrowing-targetᵐᶜ () eqM′ (cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′)
const-narrowing-targetᵐᶜ () eqM′ (cast-⊒ᵗ qᶜ rᶜ s⊒ M⊒M′)

value-id-ℕ-narrowing-target-constᵐᶜ :
  ∀ {ΔL ΔR ρ W n} →
  Value W →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ $ (κℕ n)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  W ≡ $ (κℕ n)
value-id-ℕ-narrowing-target-constᵐᶜ {W = W} vW W⊒
    with canonical-ℕ vW (typed-term-narrowing-source-typingᵐᶜ W⊒)
value-id-ℕ-narrowing-target-constᵐᶜ {W = W} vW W⊒
    | nv-const {n = m} W≡
    rewrite W≡ | const-narrowing-targetᵐᶜ refl refl W⊒ =
  refl

value-normalized-id-ℕ-target-constᵐᶜ :
  ∀ {ΔL ΔR ρ W T p A B n} →
  Value W →
  T ≡ $ (κℕ n) →
  p ≡ id (‵ `ℕ) →
  A ≡ ‵ `ℕ →
  B ≡ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ T ∶ p ⦂ A ⊒ᵐ B →
  W ≡ $ (κℕ n)
value-normalized-id-ℕ-target-constᵐᶜ
    target-value T≡ p≡ A≡ B≡ W⊒ =
  value-id-ℕ-narrowing-target-constᵐᶜ target-value
    (subst
      (λ T → _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ T
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ)
      T≡
      (subst
        (λ p →
          _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ p ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ)
        p≡
        (subst
          (λ A →
            _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ _ ⦂ A ⊒ᵐ ‵ `ℕ)
          A≡
          (subst
            (λ B → _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ _ ⦂ _ ⊒ᵐ B)
            B≡
            W⊒))))

------------------------------------------------------------------------
-- Primitive addition simulation
------------------------------------------------------------------------

mediated-⊕-δ-left-first :
  ∀ {ΔL ΔR ρ M N m′ n′} →
  RuntimeOK M →
  No• N →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ ‵ `ℕ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ r ⦂ C ⊒ᵐ D
mediated-⊕-δ-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N = N} {m′ = m′} {n′ = n′}
    okM noN M⊒M′ N⊒N′ =
  let
    χsM , WM , ΔM ,
      vWM , noWM , M↠WM , ΔM≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaᵐ okM ($ (κℕ m′)) M⊒M′

    corrM :
      StoreCorr (applyTyCtxs χsM ΔL) ΔR (applyLeftChanges χsM ρ)
    corrM =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsM ρ))
        ΔM≡
        ρM-corr

    N⊒N′M :
      ΔM ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
        ⊢ applyTerms χsM N ⊒ $ (κℕ n′) ∶ id (‵ `ℕ)
          ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ
    N⊒N′M =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
            ⊢ applyTerms χsM N ⊒ $ (κℕ n′) ∶ id (‵ `ℕ)
              ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ)
        (sym ΔM≡)
        (left-changes-term-narrowingᵐ χsM corrM N⊒N′)

    χsN , WN , ΔN ,
      vWN , noWN , N↠WN , ΔN≡ , ρN-corr ,
      leftN≡ , rightN≡ , pNᶜ , WN⊒N′ =
      catchup-lemmaᵐ
        (applyTerms-preserves-RuntimeOK χsM (ok-no noN))
        ($ (κℕ n′))
        N⊒N′M

    left-steps :
      M ⊕[ addℕ ] N —↠[ χsM ] WM ⊕[ addℕ ] applyTerms χsM N
    left-steps = ⊕₁-↠ noN M↠WM

    right-steps :
      WM ⊕[ addℕ ] applyTerms χsM N
        —↠[ χsN ] applyTerms χsN WM ⊕[ addℕ ] WN
    right-steps = ⊕₂-↠ vWM noWM N↠WN

    operands-ready :
      M ⊕[ addℕ ] N
        —↠[ χsM ++ χsN ] applyTerms χsN WM ⊕[ addℕ ] WN
    operands-ready = ↠-trans left-steps right-steps

    WM≡target : WM ≡ $ (κℕ m′)
    WM≡target =
      value-normalized-id-ℕ-target-constᵐᶜ
        vWM
        refl
        refl
        (applyTys-ℕ χsM)
        refl
        WM⊒M′

    WN≡target : WN ≡ $ (κℕ n′)
    WN≡target =
      value-normalized-id-ℕ-target-constᵐᶜ
        vWN
        refl
        refl
        (applyTys-ℕ-applyTys χsM χsN)
        refl
        WN⊒N′

    source-δ :
      applyTerms χsN WM ⊕[ addℕ ] WN
        —↠[ keep ∷ [] ] $ (κℕ (m′ + n′))
    source-δ =
      constant-⊕-δ-step {χsL = χsN} {χsR = []}
        WM≡target
        WN≡target

    χs : StoreChanges
    χs = (χsM ++ χsN) ++ keep ∷ []

    source-steps :
      M ⊕[ addℕ ] N —↠[ χs ] $ (κℕ (m′ + n′))
    source-steps = ↠-trans operands-ready source-δ

    ΔN≡total :
      ΔN ≡ applyTyCtxs χs ΔL
    ΔN≡total =
      trans ΔN≡
        (trans
          (cong (applyTyCtxs χsN) ΔM≡)
          (sym
            (trans
              (applyTyCtxs-++ (χsM ++ χsN) (keep ∷ []) ΔL)
              (cong (applyTyCtxs (keep ∷ []))
                (applyTyCtxs-++ χsM χsN ΔL)))))

    ρN≡total :
      applyLeftChanges χsN (applyLeftChanges χsM ρ) ≡
        applyLeftChanges χs ρ
    ρN≡total =
      sym
        (trans
          (applyLeftChanges-++ (χsM ++ χsN) (keep ∷ []) ρ)
          (cong (applyLeftChanges (keep ∷ []))
            (applyLeftChanges-++ χsM χsN ρ)))

    result⊒ :
      ΔN ∣ ΔR ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ $ (κℕ (m′ + n′)) ⊒ $ (κℕ (m′ + n′))
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    result⊒ =
      κ⊒κᵗ (κℕ (m′ + n′)) (id-ℕ-narrowingᵐᶜ ρN-corr)
  in
  χs ,
  $ (κℕ (m′ + n′)) ,
  ΔN ,
  applyLeftChanges χsN (applyLeftChanges χsM ρ) ,
  ‵ `ℕ ,
  ‵ `ℕ ,
  id (‵ `ℕ) ,
  source-steps ,
  ΔN≡total ,
  ρN≡total ,
  sym (applyTys-ℕ χs) ,
  refl ,
  result⊒

mediated-⊕-δ-right-first :
  ∀ {ΔL ΔR ρ M N m′ n′} →
  Value M →
  No• M →
  RuntimeOK N →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ ‵ `ℕ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ r ⦂ C ⊒ᵐ D
mediated-⊕-δ-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N = N} {m′ = m′} {n′ = n′}
    vM noM okN M⊒M′ N⊒N′ =
  let
    χsN , WN , ΔN ,
      vWN , noWN , N↠WN , ΔN≡ , ρN-corr ,
      leftN≡ , rightN≡ , pNᶜ , WN⊒N′ =
      catchup-lemmaᵐ okN ($ (κℕ n′)) N⊒N′

    corrN :
      StoreCorr (applyTyCtxs χsN ΔL) ΔR (applyLeftChanges χsN ρ)
    corrN =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsN ρ))
        ΔN≡
        ρN-corr

    M⊒M′N :
      ΔN ∣ ΔR ∣ applyLeftChanges χsN ρ ∣ []
        ⊢ applyTerms χsN M ⊒ $ (κℕ m′) ∶ id (‵ `ℕ)
          ⦂ applyTys χsN (‵ `ℕ) ⊒ᵐ ‵ `ℕ
    M⊒M′N =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsN ρ ∣ []
            ⊢ applyTerms χsN M ⊒ $ (κℕ m′) ∶ id (‵ `ℕ)
              ⦂ applyTys χsN (‵ `ℕ) ⊒ᵐ ‵ `ℕ)
        (sym ΔN≡)
        (left-changes-term-narrowingᵐ χsN corrN M⊒M′)

    χsM , WM , ΔM ,
      vWM , noWM , M↠WM , ΔM≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaᵐ
        (ok-no (applyTerms-preserves-No• χsN noM))
        ($ (κℕ m′))
        M⊒M′N

    right-steps :
      M ⊕[ addℕ ] N —↠[ χsN ] applyTerms χsN M ⊕[ addℕ ] WN
    right-steps = ⊕₂-↠ vM noM N↠WN

    left-steps :
      applyTerms χsN M ⊕[ addℕ ] WN
        —↠[ χsM ] WM ⊕[ addℕ ] applyTerms χsM WN
    left-steps = ⊕₁-↠ noWN M↠WM

    operands-ready :
      M ⊕[ addℕ ] N
        —↠[ χsN ++ χsM ] WM ⊕[ addℕ ] applyTerms χsM WN
    operands-ready = ↠-trans right-steps left-steps

    WN≡target : WN ≡ $ (κℕ n′)
    WN≡target =
      value-normalized-id-ℕ-target-constᵐᶜ
        vWN
        refl
        refl
        (applyTys-ℕ χsN)
        refl
        WN⊒N′

    WM≡target : WM ≡ $ (κℕ m′)
    WM≡target =
      value-normalized-id-ℕ-target-constᵐᶜ
        vWM
        refl
        refl
        (applyTys-ℕ-applyTys χsN χsM)
        refl
        WM⊒M′

    source-δ :
      WM ⊕[ addℕ ] applyTerms χsM WN
        —↠[ keep ∷ [] ] $ (κℕ (m′ + n′))
    source-δ =
      constant-⊕-δ-step {χsL = []} {χsR = χsM}
        WM≡target
        WN≡target

    χs : StoreChanges
    χs = (χsN ++ χsM) ++ keep ∷ []

    source-steps :
      M ⊕[ addℕ ] N —↠[ χs ] $ (κℕ (m′ + n′))
    source-steps = ↠-trans operands-ready source-δ

    ΔM≡total :
      ΔM ≡ applyTyCtxs χs ΔL
    ΔM≡total =
      trans ΔM≡
        (trans
          (cong (applyTyCtxs χsM) ΔN≡)
          (sym
            (trans
              (applyTyCtxs-++ (χsN ++ χsM) (keep ∷ []) ΔL)
              (cong (applyTyCtxs (keep ∷ []))
                (applyTyCtxs-++ χsN χsM ΔL)))))

    ρM≡total :
      applyLeftChanges χsM (applyLeftChanges χsN ρ) ≡
        applyLeftChanges χs ρ
    ρM≡total =
      sym
        (trans
          (applyLeftChanges-++ (χsN ++ χsM) (keep ∷ []) ρ)
          (cong (applyLeftChanges (keep ∷ []))
            (applyLeftChanges-++ χsN χsM ρ)))

    result⊒ :
      ΔM ∣ ΔR ∣ applyLeftChanges χsM (applyLeftChanges χsN ρ) ∣ []
        ⊢ $ (κℕ (m′ + n′)) ⊒ $ (κℕ (m′ + n′))
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    result⊒ =
      κ⊒κᵗ (κℕ (m′ + n′)) (id-ℕ-narrowingᵐᶜ ρM-corr)
  in
  χs ,
  $ (κℕ (m′ + n′)) ,
  ΔM ,
  applyLeftChanges χsM (applyLeftChanges χsN ρ) ,
  ‵ `ℕ ,
  ‵ `ℕ ,
  id (‵ `ℕ) ,
  source-steps ,
  ΔM≡total ,
  ρM≡total ,
  sym (applyTys-ℕ χs) ,
  refl ,
  result⊒

mediated-⊕-δ :
  ∀ {ΔL ΔR ρ M N m′ n′} →
  RuntimeOK (M ⊕[ addℕ ] N) →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ ‵ `ℕ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ r ⦂ C ⊒ᵐ D
mediated-⊕-δ (ok-no (no•-⊕ noM noN)) M⊒M′ N⊒N′ =
  mediated-⊕-δ-left-first (ok-no noM) noN M⊒M′ N⊒N′
mediated-⊕-δ (ok-⊕₁ okM noN) M⊒M′ N⊒N′ =
  mediated-⊕-δ-left-first okM noN M⊒M′ N⊒N′
mediated-⊕-δ (ok-⊕₂ vM noM okN) M⊒M′ N⊒N′ =
  mediated-⊕-δ-right-first vM noM okN M⊒M′ N⊒N′

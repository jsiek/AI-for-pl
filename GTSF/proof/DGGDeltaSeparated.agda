{-# OPTIONS --allow-unsolved-metas #-}

module proof.DGGDeltaSeparated where

-- File Charter:
--   * Separated-store DGG helpers for primitive addition delta steps.
--   * Packages operand catchup and constant delta reduction.
--   * Exported by proof.DynamicGradualGuaranteeSeparated for the main DGG.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_+_)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; dualʷ
  ; id★
  ; id-＇
  ; id-‵
  ; _？︔_
  ; _︔seal_
  ; _∣_∣_⊢_∶_⊒_
  )
  renaming (_↦_ to _↦ⁿʷ_)
open import Primitives using (addℕ; κℕ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  ; applyRightChange
  ; catchup-lemmaˡ
  )
open import proof.NuPreservation using (runtime-⟨⟩)
open import proof.CoercionProperties using
  ( coercion-src-tgtᵐ
  ; dualActionOk-normal
  ; dualStoreAt-normal
  )
open import proof.NarrowWidenProperties using
  ( dualʷ-flips-typingᵐ
  )
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyCoercions
  ; applyCoercions-++
  ; applyCoercions-dual
  ; applyTys-++
  ; applyTys-ℕ
  ; applyTys-ℕ-applyTys
  ; applyTyCtxs-++
  ; ↠-trans
  ; cast-↠
  ; ·₁-↠
  ; ·₂-↠
  ; ⊕₁-↠
  ; ⊕₂-↠
  )
open import proof.SimBetaSeparated using
  ( applyTerms-preserves-RuntimeOK
  ; applyTys-⇒
  ; applyCoercions-↦
  ; applyCoercions-dual-applyCoercions
  ; no•-cast-inv
  ; ⟨⟩-term-injective
  ; ⟨⟩-coercion-injective
  ; left-change-coercion-narrowing
  ; left-change-source-coercion-narrowing
  ; advance-left-term-narrowing
  ; advance-left-function-term-narrowing
  ; advance-left-lambda-narrowing
  ; widen-fun-domainᵐ
  ; separated-fun-domain-dual
  ; separated-fun-codomain
  ; separated-left-coercionᵐ
  ; separated-right-coercionᵐ
  ; ↦-domain
  ; ↦-codomain
  ; ↦-left-injective
  ; ↦-right-injective
  ; dualʷ-raw-determined
  ; dualʷ-involutive-raw
  ; sim-beta
  )
open import proof.NuProgress using
  (FunView; fv-ƛ; fv-↦; canonical-⇒)
open import proof.DGGPrimitiveSeparated using
  ( id-ℕ-narrowingᶜ
  ; applyCoercions-id-ℕ
  ; applyCoercions-id-ℕ-applyCoercions
  ; source-nat-typingᶜ
  ; typed-term-narrowing-endpointsᶜ
  ; typed-term-narrowing-coercion-endpointsᶜ
  ; constant-⊕-δ-step
  ; const-narrowing-targetᶜ
  ; value-id-ℕ-narrowing-target-constᶜ
  ; value-normalized-id-ℕ-target-constᶜ
  )
------------------------------------------------------------------------
-- Primitive addition simulation
------------------------------------------------------------------------

separated-⊕-δ-left-first :
  ∀ {ΔL ΔR ρ M N m′ n′} →
  RuntimeOK M →
  No• N →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ r ⦂ C ⊒ D
separated-⊕-δ-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N = N} {m′ = m′} {n′ = n′}
    okM noN M⊒M′ N⊒N′ =
  let
    χsM , WM , ΔM ,
      vWM , noWM , M↠WM , ΔM≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaˡ
        okM
        ($ (κℕ m′))
        M⊒M′

    N⊒N′L :
      ΔM ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
        ⊢ applyTerms χsM N ⊒ $ (κℕ n′)
          ∶ applyCoercions χsM (id (‵ `ℕ))
            ⦂ applyTys χsM (‵ `ℕ) ⊒ ‵ `ℕ
    N⊒N′L =
      advance-left-term-narrowing χsM ΔM≡ ρM-corr N⊒N′

    χsN , WN , ΔN ,
      vWN , noWN , N↠WN , ΔN≡ , ρN-corr ,
      leftN≡ , rightN≡ , pNᶜ , WN⊒N′ =
      catchup-lemmaˡ
        (applyTerms-preserves-RuntimeOK χsM (ok-no noN))
        ($ (κℕ n′))
        N⊒N′L

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
      value-normalized-id-ℕ-target-constᶜ
        vWM
        refl
        (applyCoercions-id-ℕ χsM)
        (applyTys-ℕ χsM)
        refl
        WM⊒M′

    WN≡target : WN ≡ $ (κℕ n′)
    WN≡target =
      value-normalized-id-ℕ-target-constᶜ
        vWN
        refl
        (applyCoercions-id-ℕ-applyCoercions χsM χsN)
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
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    result⊒ =
      κ⊒κᵗ (κℕ (m′ + n′)) (id-ℕ-narrowingᶜ ρN-corr)
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
  result⊒

separated-⊕-δ-right-first :
  ∀ {ΔL ΔR ρ M N m′ n′} →
  Value M →
  No• M →
  RuntimeOK N →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ r ⦂ C ⊒ D
separated-⊕-δ-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N = N} {m′ = m′} {n′ = n′}
    vM noM okN M⊒M′ N⊒N′ =
  let
    χsN , WN , ΔN ,
      vWN , noWN , N↠WN , ΔN≡ , ρN-corr ,
      leftN≡ , rightN≡ , pNᶜ , WN⊒N′ =
      catchup-lemmaˡ
        okN
        ($ (κℕ n′))
        N⊒N′

    M⊒M′N :
      ΔN ∣ ΔR ∣ applyLeftChanges χsN ρ ∣ []
        ⊢ applyTerms χsN M ⊒ $ (κℕ m′)
          ∶ applyCoercions χsN (id (‵ `ℕ))
            ⦂ applyTys χsN (‵ `ℕ) ⊒ ‵ `ℕ
    M⊒M′N =
      advance-left-term-narrowing χsN ΔN≡ ρN-corr M⊒M′

    χsM , WM , ΔM ,
      vWM , noWM , M↠WM , ΔM≡ , ρM-corr ,
      leftM≡ , rightM≡ , pMᶜ , WM⊒M′ =
      catchup-lemmaˡ
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
      value-normalized-id-ℕ-target-constᶜ
        vWN
        refl
        (applyCoercions-id-ℕ χsN)
        (applyTys-ℕ χsN)
        refl
        WN⊒N′

    WM≡target : WM ≡ $ (κℕ m′)
    WM≡target =
      value-normalized-id-ℕ-target-constᶜ
        vWM
        refl
        (applyCoercions-id-ℕ-applyCoercions χsN χsM)
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
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    result⊒ =
      κ⊒κᵗ (κℕ (m′ + n′)) (id-ℕ-narrowingᶜ ρM-corr)
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
  result⊒

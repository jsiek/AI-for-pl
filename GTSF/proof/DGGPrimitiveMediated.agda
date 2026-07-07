module proof.DGGPrimitiveMediated where

-- File Charter:
--   * Mediated-store DGG helpers for primitive addition delta steps.
--   * Packages operand catchup and constant delta reduction.
--   * Exported by proof.DynamicGradualGuaranteeMediated for the main DGG.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
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
  ; applyRightChange
  ; applyLeftChanges-++
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.NarrowWidenProperties using (narrowing-determinedᵐ)
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

mediated-id-ℕ-index-determined :
  ∀ {μ ΔL ΔR ρ p} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  p ≡ id (‵ `ℕ)
mediated-id-ℕ-index-determined
    (stores , wfBase , wfBase , .(‵ `ℕ) , med-base , p⊒) =
  narrowing-determinedᵐ (rightStore-det stores)
    p⊒
    (cast-id wfBase refl , cross (id-‵ `ℕ))

typed-id-ℕ-index-determinedᵐ :
  ∀ {ΔL ΔR ρ γ M M′ p} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  p ≡ id (‵ `ℕ)
typed-id-ℕ-index-determinedᵐ M⊒M′ =
  mediated-id-ℕ-index-determined
    (proj₂ (typed-term-narrowing-coercionᵐ M⊒M′))

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

primitive-left-frame-keepᵐ :
  ∀ {ΔL ΔR ρ M N S′ N′} →
  No• N →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N ⊒ N′
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  (∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
   ∃[ C ] ∃[ D ] ∃[ r ]
    (M —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ᵐ D) →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ S′ ⊕[ addℕ ] N′ ∶ r ⦂ C ⊒ᵐ D
primitive-left-frame-keepᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {N = N} {S′ = S′} {N′ = N′}
    noN N⊒N′
    (χs , P , .(applyTyCtxs χs ΔL) , .(applyTyCtx keep ΔR) ,
     .(applyRightChange keep (applyLeftChanges χs ρ)) ,
     .(applyTys χs (‵ `ℕ)) , .(applyTy keep (‵ `ℕ)) , r ,
     M↠P , refl , refl , refl , refl , refl , P⊒S′) =
  let
    μP , rᶜ = typed-term-narrowing-coercionᵐ P⊒S′

    corr :
      StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corr = narrowing-store-corrᵐᶜ rᶜ

    pℕᶜ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
        ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    pℕᶜ = id-ℕ-narrowingᵐᶜ corr

    N⊒N′L :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ applyTerms χs N ⊒ N′ ∶ id (‵ `ℕ)
          ⦂ applyTys χs (‵ `ℕ) ⊒ᵐ ‵ `ℕ
    N⊒N′L = left-changes-term-narrowingᵐ χs corr N⊒N′

    N⊒N′ℕ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ applyTerms χs N ⊒ N′ ∶ id (‵ `ℕ)
          ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    N⊒N′ℕ =
      subst
        (λ A →
          applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ applyTerms χs N ⊒ N′ ∶ id (‵ `ℕ)
              ⦂ A ⊒ᵐ ‵ `ℕ)
        (applyTys-ℕ χs)
        N⊒N′L

    P⊒S′ℕ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ P ⊒ S′ ∶ r ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′ℕ =
      subst
        (λ A →
          applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ P ⊒ S′ ∶ r ⦂ A ⊒ᵐ ‵ `ℕ)
        (applyTys-ℕ χs)
        P⊒S′

    P⊒S′id :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ P ⊒ S′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′id =
      subst
        (λ q →
          applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ P ⊒ S′ ∶ q ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ)
        (typed-id-ℕ-index-determinedᵐ P⊒S′ℕ)
        P⊒S′ℕ

    framed⊒ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ P ⊕[ addℕ ] applyTerms χs N ⊒ S′ ⊕[ addℕ ] N′
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    framed⊒ = ⊕⊒⊕ᵗ pℕᶜ P⊒S′id N⊒N′ℕ
  in
  χs ,
  P ⊕[ addℕ ] applyTerms χs N ,
  applyTyCtxs χs ΔL ,
  ΔR ,
  applyLeftChanges χs ρ ,
  ‵ `ℕ ,
  ‵ `ℕ ,
  id (‵ `ℕ) ,
  ⊕₁-↠ noN M↠P ,
  refl ,
  refl ,
  refl ,
  sym (applyTys-ℕ χs) ,
  refl ,
  framed⊒

primitive-right-frame-keepᵐ :
  ∀ {ΔL ΔR ρ M M′ N S′} →
  Value M →
  No• M →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ →
  (∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
   ∃[ C ] ∃[ D ] ∃[ r ]
    (N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ᵐ D) →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ M′ ⊕[ addℕ ] S′ ∶ r ⦂ C ⊒ᵐ D
primitive-right-frame-keepᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {M′ = M′} {N = N} {S′ = S′}
    vM noM M⊒M′
    (χs , P , .(applyTyCtxs χs ΔL) , .(applyTyCtx keep ΔR) ,
     .(applyRightChange keep (applyLeftChanges χs ρ)) ,
     .(applyTys χs (‵ `ℕ)) , .(applyTy keep (‵ `ℕ)) , r ,
     N↠P , refl , refl , refl , refl , refl , P⊒S′) =
  let
    μP , rᶜ = typed-term-narrowing-coercionᵐ P⊒S′

    corr :
      StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corr = narrowing-store-corrᵐᶜ rᶜ

    pℕᶜ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
        ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    pℕᶜ = id-ℕ-narrowingᵐᶜ corr

    M⊒M′L :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ applyTerms χs M ⊒ M′ ∶ id (‵ `ℕ)
          ⦂ applyTys χs (‵ `ℕ) ⊒ᵐ ‵ `ℕ
    M⊒M′L = left-changes-term-narrowingᵐ χs corr M⊒M′

    M⊒M′ℕ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ applyTerms χs M ⊒ M′ ∶ id (‵ `ℕ)
          ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    M⊒M′ℕ =
      subst
        (λ A →
          applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ applyTerms χs M ⊒ M′ ∶ id (‵ `ℕ)
              ⦂ A ⊒ᵐ ‵ `ℕ)
        (applyTys-ℕ χs)
        M⊒M′L

    P⊒S′ℕ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ P ⊒ S′ ∶ r ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′ℕ =
      subst
        (λ A →
          applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ P ⊒ S′ ∶ r ⦂ A ⊒ᵐ ‵ `ℕ)
        (applyTys-ℕ χs)
        P⊒S′

    P⊒S′id :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ P ⊒ S′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′id =
      subst
        (λ q →
          applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
            ⊢ P ⊒ S′ ∶ q ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ)
        (typed-id-ℕ-index-determinedᵐ P⊒S′ℕ)
        P⊒S′ℕ

    framed⊒ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ applyTerms χs M ⊕[ addℕ ] P ⊒ M′ ⊕[ addℕ ] S′
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    framed⊒ = ⊕⊒⊕ᵗ pℕᶜ M⊒M′ℕ P⊒S′id
  in
  χs ,
  applyTerms χs M ⊕[ addℕ ] P ,
  applyTyCtxs χs ΔL ,
  ΔR ,
  applyLeftChanges χs ρ ,
  ‵ `ℕ ,
  ‵ `ℕ ,
  id (‵ `ℕ) ,
  ⊕₂-↠ vM noM N↠P ,
  refl ,
  refl ,
  refl ,
  sym (applyTys-ℕ χs) ,
  refl ,
  framed⊒

primitive-right-after-left-frame-keepᵐ :
  ∀ {ΔL ΔR ρ M N WM M′ S′ χsM ΔL₁} →
  No• N →
  Value WM →
  No• WM →
  M —↠[ χsM ] WM →
  ΔL₁ ≡ applyTyCtxs χsM ΔL →
  StoreCorr ΔL₁ ΔR (applyLeftChanges χsM ρ) →
  ΔL₁ ∣ ΔR ∣ applyLeftChanges χsM ρ ∣ []
    ⊢ WM ⊒ M′ ∶ id (‵ `ℕ)
      ⦂ applyTys χsM (‵ `ℕ) ⊒ᵐ ‵ `ℕ →
  (∃[ χsN ] ∃[ P ] ∃[ ΔL₂ ] ∃[ ΔR′ ] ∃[ ρ′ ]
   ∃[ C ] ∃[ D ] ∃[ r ]
    (applyTerms χsM N —↠[ χsN ] P) ×
    (ΔL₂ ≡ applyTyCtxs χsN ΔL₁) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep
      (applyLeftChanges χsN (applyLeftChanges χsM ρ))) ×
    (C ≡ applyTys χsN (applyTys χsM (‵ `ℕ))) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL₂ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ S′ ∶ r ⦂ C ⊒ᵐ D) →
  ∃[ χs ] ∃[ P ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C ≡ applyTys χs (‵ `ℕ)) ×
    (D ≡ applyTy keep (‵ `ℕ)) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ P ⊒ M′ ⊕[ addℕ ] S′ ∶ r ⦂ C ⊒ᵐ D
primitive-right-after-left-frame-keepᵐ
    {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {M = M} {N = N}
    {WM = WM} {M′ = M′} {S′ = S′} {χsM = χsM}
    {ΔL₁ = ΔL₁}
    noN vWM noWM M↠WM ΔL₁≡ corrM WM⊒M′
    (χsN , P , .(applyTyCtxs χsN ΔL₁) , .(applyTyCtx keep ΔR) ,
     .(applyRightChange keep
        (applyLeftChanges χsN (applyLeftChanges χsM ρ))) ,
     .(applyTys χsN (applyTys χsM (‵ `ℕ))) ,
     .(applyTy keep (‵ `ℕ)) , r ,
     N↠P , refl , refl , refl , refl , refl , P⊒S′) =
  let
    μP , rᶜ = typed-term-narrowing-coercionᵐ P⊒S′

    corrN :
      StoreCorr (applyTyCtxs χsN ΔL₁) ΔR
        (applyLeftChanges χsN (applyLeftChanges χsM ρ))
    corrN = narrowing-store-corrᵐᶜ rᶜ

    pℕᶜ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ)
        ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    pℕᶜ = id-ℕ-narrowingᵐᶜ corrN

    WM⊒M′N :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ applyTerms χsN WM ⊒ M′ ∶ id (‵ `ℕ)
          ⦂ applyTys χsN (applyTys χsM (‵ `ℕ)) ⊒ᵐ ‵ `ℕ
    WM⊒M′N = left-changes-term-narrowingᵐ χsN corrN WM⊒M′

    endpointℕ :
      applyTys χsN (applyTys χsM (‵ `ℕ)) ≡ ‵ `ℕ
    endpointℕ = applyTys-ℕ-applyTys χsM χsN

    WM⊒M′ℕ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ applyTerms χsN WM ⊒ M′ ∶ id (‵ `ℕ)
          ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    WM⊒M′ℕ =
      subst
        (λ A →
          applyTyCtxs χsN ΔL₁ ∣ ΔR
            ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
            ⊢ applyTerms χsN WM ⊒ M′ ∶ id (‵ `ℕ)
              ⦂ A ⊒ᵐ ‵ `ℕ)
        endpointℕ
        WM⊒M′N

    P⊒S′ℕ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ P ⊒ S′ ∶ r ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′ℕ =
      subst
        (λ A →
          applyTyCtxs χsN ΔL₁ ∣ ΔR
            ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
            ⊢ P ⊒ S′ ∶ r ⦂ A ⊒ᵐ ‵ `ℕ)
        endpointℕ
        P⊒S′

    P⊒S′id :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ P ⊒ S′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    P⊒S′id =
      subst
        (λ q →
          applyTyCtxs χsN ΔL₁ ∣ ΔR
            ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
            ⊢ P ⊒ S′ ∶ q ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ)
        (typed-id-ℕ-index-determinedᵐ P⊒S′ℕ)
        P⊒S′ℕ

    framed⊒ :
      applyTyCtxs χsN ΔL₁ ∣ ΔR
        ∣ applyLeftChanges χsN (applyLeftChanges χsM ρ) ∣ []
        ⊢ applyTerms χsN WM ⊕[ addℕ ] P
          ⊒ M′ ⊕[ addℕ ] S′
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    framed⊒ = ⊕⊒⊕ᵗ pℕᶜ WM⊒M′ℕ P⊒S′id

    χs : StoreChanges
    χs = χsM ++ χsN

    source-steps :
      M ⊕[ addℕ ] N —↠[ χs ] applyTerms χsN WM ⊕[ addℕ ] P
    source-steps =
      ↠-trans (⊕₁-↠ noN M↠WM) (⊕₂-↠ vWM noWM N↠P)

    ΔL₂≡total :
      applyTyCtxs χsN ΔL₁ ≡ applyTyCtxs χs ΔL
    ΔL₂≡total =
      trans (cong (applyTyCtxs χsN) ΔL₁≡)
        (sym (applyTyCtxs-++ χsM χsN ΔL))

    ρ≡total :
      applyLeftChanges χsN (applyLeftChanges χsM ρ) ≡
        applyLeftChanges χs ρ
    ρ≡total = sym (applyLeftChanges-++ χsM χsN ρ)
  in
  χs ,
  applyTerms χsN WM ⊕[ addℕ ] P ,
  applyTyCtxs χsN ΔL₁ ,
  ΔR ,
  applyLeftChanges χsN (applyLeftChanges χsM ρ) ,
  ‵ `ℕ ,
  ‵ `ℕ ,
  id (‵ `ℕ) ,
  source-steps ,
  ΔL₂≡total ,
  refl ,
  ρ≡total ,
  sym (applyTys-ℕ χs) ,
  refl ,
  framed⊒

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

module proof.DGGCastMediated where

-- File Charter:
--   * Mediated-store DGG helpers for target-side cast steps.
--   * Packages direct cast simulations whose proof should stay out of the
--     main DynamicGradualGuaranteeMediated case split.
--   * Currently exports direct target `blame` and `β-id` cases for
--     `⊒cast+ᵗ` and `⊒cast-ᵗ`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Store using (StoreIncl-drop)
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; renameⁿ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation using (medTy-mapʳ; mv-right-alloc)
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyRightChange
  ; leftStore-applyLeftChanges
  ; leftStore-applyRightChange
  ; rightStore-applyLeftChanges
  ; rightStore-applyRightChange
  )
open import proof.CoercionProperties using
  ( coercion-renameᵗᵐ
  ; coercion-weakenᵐ
  )
open import proof.MediationProperties using
  ( applyModeEnv
  ; applyModeEnvs
  ; left-change-narrowing¹
  ; left-changes-narrowingˡ
  ; left-changes-transportᵐ
  ; narrowing-dual¹-applyCoercions
  ; wfTy-⇑
  )
open import proof.NarrowWidenProperties using
  ( StoreDetWf
  ; modeRename-suc-tag-or-id
  )
open import proof.ReductionProperties using (applyCoercions; cast-↠)
open import proof.TypeProperties using (TyRenameWf-suc)

------------------------------------------------------------------------
-- Endpoint transport
------------------------------------------------------------------------

typed-term-narrowing-endpointsᵐᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B A′ B′} →
  A ≡ A′ →
  B ≡ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A′ ⊒ᵐ B′
typed-term-narrowing-endpointsᵐᶜ refl refl M⊒M′ = M⊒M′

------------------------------------------------------------------------
-- Store-change coercion transport for source casts
------------------------------------------------------------------------

right-alloc-transportᵐᶜ :
  ∀ {ΔL ΔR ρ r A B X} →
  StoreCorr ΔL (suc ΔR) (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ) →
  ΔL ∣ ΔR ∣ ρ ⊢ r ∶ᶜ A ⊒ᵐ B →
  ΔL ∣ suc ΔR ∣ right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ
    ⊢ ⇑ᶜ r ∶ᶜ A ⊒ᵐ ⇑ᵗ B
right-alloc-transportᵐᶜ {ρ = ρ} {r = r} {B = B} {X = X}
    corr′ (corr , wfA , wfB , Aʳ , med , (r⊢ , rⁿ)) =
  corr′ ,
  wfA ,
  wfTy-⇑ wfB ,
  ⇑ᵗ Aʳ ,
  medTy-mapʳ suc mv-right-alloc med ,
  subst
    (λ Σ →
      tag-or-idᵈ ∣ suc _ ∣ (zero , ⇑ᵗ X) ∷ Σ
        ⊢ ⇑ᶜ r ∶ ⇑ᵗ Aʳ ⊒ ⇑ᵗ B)
    (sym (rightStore-⇑ʳᶜorr ρ))
    ( coercion-weakenᵐ ≤-refl StoreIncl-drop
        (coercion-renameᵗᵐ
          {ρ = suc} {μ = tag-or-idᵈ} {ν = tag-or-idᵈ}
          TyRenameWf-suc
          modeRename-suc-tag-or-id
          r⊢)
    , renameⁿ suc rⁿ )

right-change-transportᵐᶜ :
  ∀ χ′ {ΔL ΔR ρ r A B} →
  StoreCorr ΔL (applyTyCtx χ′ ΔR) (applyRightChange χ′ ρ) →
  ΔL ∣ ΔR ∣ ρ ⊢ r ∶ᶜ A ⊒ᵐ B →
  ΔL ∣ applyTyCtx χ′ ΔR ∣ applyRightChange χ′ ρ
    ⊢ applyCoercion χ′ r ∶ᶜ A ⊒ᵐ applyTy χ′ B
right-change-transportᵐᶜ keep corr′ ev = ev
right-change-transportᵐᶜ (bind X) corr′ ev =
  right-alloc-transportᵐᶜ corr′ ev

intermediate-corrᵐ :
  ∀ χ′ χs {ΔL ΔR ρ} →
  StoreCorr (applyTyCtxs χs ΔL) (applyTyCtx χ′ ΔR)
    (applyRightChange χ′ (applyLeftChanges χs ρ)) →
  StoreCorr ΔL ΔR ρ →
  StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
intermediate-corrᵐ χ′ χs {ρ = ρ} finalCorr origCorr =
  store-corr
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (leftStore-applyRightChange χ′ (applyLeftChanges χs ρ))
      (leftStore-det finalCorr))
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (rightStore-applyLeftChanges χs ρ))
      (rightStore-det origCorr))

left-cast-evidence-finalᵐ :
  ∀ χ′ χs {η ΔL ρ s A C} →
  η ∣ ΔL ∣ leftStore ρ ⊢ s ∶ A ⊒ C →
  applyModeEnvs χs η ∣ applyTyCtxs χs ΔL
    ∣ leftStore (applyRightChange χ′ (applyLeftChanges χs ρ))
    ⊢ applyCoercions χs s ∶ applyTys χs A ⊒ applyTys χs C
left-cast-evidence-finalᵐ χ′ χs
    {η = η} {ΔL = ΔL} {ρ = ρ} {s = s} {A = A} {C = C}
    s⊒ =
  subst
    (λ Σ →
      applyModeEnvs χs η ∣ applyTyCtxs χs ΔL ∣ Σ
        ⊢ applyCoercions χs s ∶ applyTys χs A ⊒ applyTys χs C)
    (sym
      (trans
        (leftStore-applyRightChange χ′ (applyLeftChanges χs ρ))
        (leftStore-applyLeftChanges χs ρ)))
    (left-changes-narrowingˡ χs s⊒)

right-cast-evidence-finalᵐ :
  ∀ χ′ χs {η ΔR ρ t C B} →
  (t⊒ : η ∣ ΔR ∣ rightStore ρ ⊢ t ∶ C ⊒ B) →
  applyModeEnv χ′ η ∣ applyTyCtx χ′ ΔR
    ∣ rightStore (applyRightChange χ′ (applyLeftChanges χs ρ))
    ⊢ applyCoercion χ′ t ∶ applyTy χ′ C ⊒ applyTy χ′ B
right-cast-evidence-finalᵐ χ′ χs
    {η = η} {ΔR = ΔR} {ρ = ρ} {t = t} {C = C} {B = B}
    t⊒ =
  subst
    (λ Σ →
      applyModeEnv χ′ η ∣ applyTyCtx χ′ ΔR ∣ Σ
        ⊢ applyCoercion χ′ t ∶ applyTy χ′ C ⊒ applyTy χ′ B)
    (sym
      (trans
        (rightStore-applyRightChange χ′ (applyLeftChanges χs ρ))
        (cong (applyStore χ′) (rightStore-applyLeftChanges χs ρ))))
    (left-change-narrowing¹ χ′ t⊒)

------------------------------------------------------------------------
-- Direct target cast simulation
------------------------------------------------------------------------

target-blameᵐ :
  ∀ {ΔL ΔR ρ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ blame ∶ r′ ⦂ C′ ⊒ᵐ D′
target-blameᵐ M⊒M′ =
  [] ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  ⊒blameᵗ (typed-term-narrowing-source-typingᵐᶜ M⊒M′)
    (proj₂ (typed-term-narrowing-coercionᵐ M⊒M′))

target-cast-plus-β-idᵐ :
  ∀ {ΔL ΔR ρ M M′ r A B C T η} →
  η ∣ ΔR ∣ rightStore ρ ⊢ id T ∶ C ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ᵐ B →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep C) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ M′ ∶ r′ ⦂ C′ ⊒ᵐ D′
target-cast-plus-β-idᵐ (cast-id _ _ , _) M⊒M′ =
  [] ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  typed-term-narrowing-endpointsᵐᶜ refl refl M⊒M′

target-cast-minus-β-idᵐ :
  ∀ {ΔL ΔR ρ M M′ p A B C T η} →
  η ∣ ΔR ∣ rightStore ρ ⊢ id T ∶ C ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ C →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ M′ ∶ r′ ⦂ C′ ⊒ᵐ D′
target-cast-minus-β-idᵐ (cast-id _ _ , _) M⊒M′ =
  [] ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  typed-term-narrowing-endpointsᵐᶜ refl refl M⊒M′

target-cast-plus-inner-resultᵐ :
  ∀ {ΔL ΔR ρ M S′ p t A B C η χ′} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ C →
  (t⊒ : η ∣ ΔR ∣ rightStore ρ ⊢ t ∶ C ⊒ B) →
  (∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
   ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
    (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy χ′ B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ S′ ∶ r′ ⦂ C′ ⊒ᵐ D′) →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
    (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy χ′ C) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ S′ ⟨ applyCoercion χ′ (narrowing-dual¹ t⊒) ⟩
        ∶ r′ ⦂ C′ ⊒ᵐ D′
target-cast-plus-inner-resultᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {S′ = S′} {p = p} {t = t}
    {A = A} {B = B} {C = C} {η = η} {χ′ = χ′}
    pᶜ t⊒
    (χs , N , .(applyTyCtxs χs ΔL) , .(applyTyCtx χ′ ΔR) ,
     .(applyRightChange χ′ (applyLeftChanges χs ρ)) ,
     .(applyTys χs A) , .(applyTy χ′ B) , r′ ,
     source-steps , refl , refl , refl , refl , refl , N⊒S′) =
  let
    μ′ , rᶜ′ = typed-term-narrowing-coercionᵐ N⊒S′

    finalCorr :
      StoreCorr (applyTyCtxs χs ΔL) (applyTyCtx χ′ ΔR)
        (applyRightChange χ′ (applyLeftChanges χs ρ))
    finalCorr = narrowing-store-corrᵐᶜ rᶜ′

    corrL :
      StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corrL = intermediate-corrᵐ χ′ χs finalCorr
      (narrowing-store-corrᵐᶜ pᶜ)

    pLᶜ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
        ⊢ p ∶ᶜ applyTys χs A ⊒ᵐ C
    pLᶜ = left-changes-transportᵐ χs corrL pᶜ

    pᶜ′ :
      applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
        ∣ applyRightChange χ′ (applyLeftChanges χs ρ)
        ⊢ applyCoercion χ′ p ∶ᶜ applyTys χs A ⊒ᵐ applyTy χ′ C
    pᶜ′ = right-change-transportᵐᶜ χ′ finalCorr pLᶜ

    t⊒′ :
      applyModeEnv χ′ η ∣ applyTyCtx χ′ ΔR
        ∣ rightStore (applyRightChange χ′ (applyLeftChanges χs ρ))
        ⊢ applyCoercion χ′ t ∶ applyTy χ′ C ⊒ applyTy χ′ B
    t⊒′ = right-cast-evidence-finalᵐ χ′ χs t⊒

    dual≡ :
      narrowing-dual¹ t⊒′ ≡ applyCoercion χ′ (narrowing-dual¹ t⊒)
    dual≡ = narrowing-dual¹-applyCoercions (χ′ ∷ []) t⊒ t⊒′

    result :
      applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
        ∣ applyRightChange χ′ (applyLeftChanges χs ρ) ∣ []
        ⊢ N ⊒ S′ ⟨ applyCoercion χ′ (narrowing-dual¹ t⊒) ⟩
          ∶ applyCoercion χ′ p ⦂ applyTys χs A ⊒ᵐ applyTy χ′ C
    result =
      subst
        (λ d →
          applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
            ∣ applyRightChange χ′ (applyLeftChanges χs ρ) ∣ []
            ⊢ N ⊒ S′ ⟨ d ⟩
              ∶ applyCoercion χ′ p
              ⦂ applyTys χs A ⊒ᵐ applyTy χ′ C)
        dual≡
        (⊒cast+ᵗ pᶜ′ rᶜ′ t⊒′ N⊒S′)
  in
  χs ,
  N ,
  applyTyCtxs χs ΔL ,
  applyTyCtx χ′ ΔR ,
  applyRightChange χ′ (applyLeftChanges χs ρ) ,
  applyTys χs A ,
  applyTy χ′ C ,
  applyCoercion χ′ p ,
  source-steps ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  result

source-cast-minus-resultᵐ :
  ∀ {ΔL ΔR ρ M N′ q s A B C η χ′} →
  ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ C ⊒ᵐ B →
  η ∣ ΔL ∣ leftStore ρ ⊢ s ∶ A ⊒ C →
  (∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
   ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
    (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy χ′ B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ ∶ r′ ⦂ C′ ⊒ᵐ D′) →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M ⟨ s ⟩ —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx χ′ ΔR) ×
    (ρ′ ≡ applyRightChange χ′ (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs C) ×
    (D′ ≡ applyTy χ′ B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ ∶ r′ ⦂ C′ ⊒ᵐ D′
source-cast-minus-resultᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {M = M} {q = q} {s = s} {A = A} {B = B} {C = C}
    {η = η} {χ′ = χ′} qᶜ s⊒
    (χs , N , .(applyTyCtxs χs ΔL) , .(applyTyCtx χ′ ΔR) ,
     .(applyRightChange χ′ (applyLeftChanges χs ρ)) ,
     .(applyTys χs A) , .(applyTy χ′ B) , r′ ,
     source-steps , refl , refl , refl , refl , refl , N⊒N′) =
  let
    μ′ , rᶜ′ = typed-term-narrowing-coercionᵐ N⊒N′

    finalCorr :
      StoreCorr (applyTyCtxs χs ΔL) (applyTyCtx χ′ ΔR)
        (applyRightChange χ′ (applyLeftChanges χs ρ))
    finalCorr = narrowing-store-corrᵐᶜ rᶜ′

    corrL :
      StoreCorr (applyTyCtxs χs ΔL) ΔR (applyLeftChanges χs ρ)
    corrL = intermediate-corrᵐ χ′ χs finalCorr
      (narrowing-store-corrᵐᶜ qᶜ)

    qLᶜ :
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ
        ⊢ q ∶ᶜ applyTys χs C ⊒ᵐ B
    qLᶜ = left-changes-transportᵐ χs corrL qᶜ

    qᶜ′ :
      applyTyCtxs χs ΔL ∣ applyTyCtx χ′ ΔR
        ∣ applyRightChange χ′ (applyLeftChanges χs ρ)
        ⊢ applyCoercion χ′ q ∶ᶜ applyTys χs C ⊒ᵐ applyTy χ′ B
    qᶜ′ = right-change-transportᵐᶜ χ′ finalCorr qLᶜ

    s⊒′ :
      applyModeEnvs χs η ∣ applyTyCtxs χs ΔL
        ∣ leftStore (applyRightChange χ′ (applyLeftChanges χs ρ))
        ⊢ applyCoercions χs s ∶ applyTys χs A ⊒ applyTys χs C
    s⊒′ = left-cast-evidence-finalᵐ χ′ χs
      {η = η} {ΔL = ΔL} {ρ = ρ} {s = s} {A = A} {C = C}
      s⊒
  in
  χs ,
  N ⟨ applyCoercions χs s ⟩ ,
  applyTyCtxs χs ΔL ,
  applyTyCtx χ′ ΔR ,
  applyRightChange χ′ (applyLeftChanges χs ρ) ,
  applyTys χs C ,
  applyTy χ′ B ,
  applyCoercion χ′ q ,
  cast-↠ {c = s} source-steps ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  cast-⊒ᵗ qᶜ′ rᶜ′ s⊒′ N⊒N′

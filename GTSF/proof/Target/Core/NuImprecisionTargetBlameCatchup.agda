module proof.Target.Core.NuImprecisionTargetBlameCatchup where

-- File Charter:
--   * Owns source catch-up when a related target is already blame.
--   * Exposes the exact base lemma required by backward target-blame terminal
--     trace induction.
--   * The statement is frozen and checked; the structural proof is the active
--     boundary.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( keep
  ; _—↠[_]_
  ; ↠-refl
  ; ↠-step
  ; pure-step
  ; blame-ν
  ; blame-⟨⟩
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using (RuntimeOK; Value; Λ_; ν; _⟨_⟩; blame)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; blame⊑ᵀ
  ; Λ⊑ᵀ
  ; α⊑ᵀ
  ; allocation-prefixᵀ
  ; ν⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  )
open import proof.Core.Properties.NuRuntimeProperties
  using (runtime-ν; runtime-⟨⟩)
open import proof.Core.Properties.ReductionProperties using (↠-trans; cast-↠; ν-↠)


value-not-target-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ V A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V ⊑ blame ⦂ A ⊑ B ∶ p →
  ⊥
value-not-target-blameᵀ () (blame⊑ᵀ _)
value-not-target-blameᵀ (Λ vV) (Λ⊑ᵀ occ liftρ liftγ _ V⊑N′) =
  value-not-target-blameᵀ vV V⊑N′
value-not-target-blameᵀ vV
    (allocation-prefixᵀ prefix V⊑blame V⊢ blame⊢) =
  value-not-target-blameᵀ vV V⊑blame
value-not-target-blameᵀ (vV ⟨ c ⟩)
    (cast⊒⊑ᵀ mode seal★ c⊒ V⊑blame q c-shape comp) =
  value-not-target-blameᵀ vV V⊑blame
value-not-target-blameᵀ (vV ⟨ c ⟩)
    (cast⊑⊑ᵀ mode seal★ c⊑ V⊑blame q c-shape comp) =
  value-not-target-blameᵀ vV V⊑blame
value-not-target-blameᵀ (vV ⟨ c ⟩)
    (conv↑⊑ᵀ c↑ V⊑blame q replace) =
  value-not-target-blameᵀ vV V⊑blame
value-not-target-blameᵀ (vV ⟨ c ⟩)
    (conv↓⊑ᵀ c↓ V⊑blame q replace) =
  value-not-target-blameᵀ vV V⊑blame


ν-blame-tailᵀ :
  ∀ {N A c χs} →
  N —↠[ χs ] blame →
  ν A N c —↠[ χs ++ keep ∷ [] ] blame
ν-blame-tailᵀ N↠blame =
  ↠-trans (ν-↠ N↠blame) (↠-step blame-ν ↠-refl)


cast-blame-tailᵀ :
  ∀ {M c χs} →
  M —↠[ χs ] blame →
  M ⟨ c ⟩ —↠[ χs ++ keep ∷ [] ] blame
cast-blame-tailᵀ M↠blame =
  ↠-trans (cast-↠ M↠blame)
    (↠-step (pure-step blame-⟨⟩) ↠-refl)


left-catchup-target-blame-generalᵀ :
  ∀ {Φ Δᴸ Δᴿ M A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  RuntimeOK M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
  ∃[ χs ] (M —↠[ χs ] blame)
left-catchup-target-blame-generalᵀ okM (blame⊑ᵀ blame⊢) =
  [] , ↠-refl
left-catchup-target-blame-generalᵀ okM
    (Λ⊑ᵀ occ liftρ liftγ vV V⊑blame) =
  ⊥-elim (value-not-target-blameᵀ vV V⊑blame)
left-catchup-target-blame-generalᵀ okM
    (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑blame L•⊢ blame⊢) =
  ⊥-elim (value-not-target-blameᵀ vL L⊑blame)
left-catchup-target-blame-generalᵀ okM
    (allocation-prefixᵀ prefix M⊑blame M⊢ blame⊢) =
  left-catchup-target-blame-generalᵀ okM M⊑blame
left-catchup-target-blame-generalᵀ okM
    (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑blame replace) =
  χs ++ keep ∷ [] , ν-blame-tailᵀ N↠blame
  where
  χs,N↠blame =
    left-catchup-target-blame-generalᵀ (runtime-ν okM) N⊑blame
  χs = proj₁ χs,N↠blame
  N↠blame = proj₂ χs,N↠blame
left-catchup-target-blame-generalᵀ okM
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑blame q c-shape comp) =
  χs ++ keep ∷ [] , cast-blame-tailᵀ M↠blame
  where
  χs,M↠blame =
    left-catchup-target-blame-generalᵀ (runtime-⟨⟩ okM) M⊑blame
  χs = proj₁ χs,M↠blame
  M↠blame = proj₂ χs,M↠blame
left-catchup-target-blame-generalᵀ okM
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑blame q c-shape comp) =
  χs ++ keep ∷ [] , cast-blame-tailᵀ M↠blame
  where
  χs,M↠blame =
    left-catchup-target-blame-generalᵀ (runtime-⟨⟩ okM) M⊑blame
  χs = proj₁ χs,M↠blame
  M↠blame = proj₂ χs,M↠blame
left-catchup-target-blame-generalᵀ okM
    (conv↑⊑ᵀ c↑ M⊑blame q replace) =
  χs ++ keep ∷ [] , cast-blame-tailᵀ M↠blame
  where
  χs,M↠blame =
    left-catchup-target-blame-generalᵀ (runtime-⟨⟩ okM) M⊑blame
  χs = proj₁ χs,M↠blame
  M↠blame = proj₂ χs,M↠blame
left-catchup-target-blame-generalᵀ okM
    (conv↓⊑ᵀ c↓ M⊑blame q replace) =
  χs ++ keep ∷ [] , cast-blame-tailᵀ M↠blame
  where
  χs,M↠blame =
    left-catchup-target-blame-generalᵀ (runtime-⟨⟩ okM) M⊑blame
  χs = proj₁ χs,M↠blame
  M↠blame = proj₂ χs,M↠blame


left-catchup-target-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ M A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  RuntimeOK M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
  ∃[ χs ] (M —↠[ χs ] blame)
left-catchup-target-blameᵀ = left-catchup-target-blame-generalᵀ

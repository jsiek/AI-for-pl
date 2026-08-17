module proof.DGG.TargetBlameCatchupProof where

-- File Charter:
--   * Records the checked source-blame base case and wrapper replay pieces
--     for TargetBlameCatchupᵀ.
--   * Leaves the full CTI2 induction blocked on the proposed value-target
--     blame exclusion lemma in notes/t7-target-blame-catchup-proposal.red.
--   * Contains no postulates, holes, pragmas, or changes to the fixed
--     TargetBlameCatchupᵀ surface.

import Data.Nat as Nat
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; blame; _⟨_⟩; _↑_; _↓_; _⦂∀_[_])
import Reduction as R
open import Reduction using
  ( StoreChanges
  ; keep
  ; _∷_
  ; _—↠[_]_
  ; ↠-refl
  ; ↠-step
  ; pure-step
  ; blame-⟨⟩
  ; blame-reveal
  ; blame-conceal
  ; blame-•
  )
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedEvolveCompositionProof
  using (compose-parked-evolve)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedEvolve; ParkedWorld; evolve-keepᴸ; evolve-refl)
open import proof.Reduction
  using (_++χ_; cast-↠; composeReduction; conceal-↠; reveal-↠; typeApp-↠)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


target-blame-catchup-source-blame : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² blame ⊑ blame ∶ p
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
      (blame —↠[ χsᴸ ] blame) ×
      ParkedEvolve χsᴸ R.[] W W′
target-blame-catchup-source-blame parked rel =
  _ , R.[] , _ , _ , ↠-refl , evolve-refl


source-cast-blame-catchup : ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {μ : Env∼ Δᴸ} {A B : Ty Δᴸ} {c : μ ⊢ A ∼ B}
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ⟨ c ⟩ —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″
source-cast-blame-catchup {χsᴸ = χsᴸ} {c = c} M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction (cast-↠ c M↠blame)
    (↠-step (pure-step blame-⟨⟩) ↠-refl) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)


source-reveal-blame-catchup : ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {A B : Ty Δᴸ} {c : Conv↑ Δᴸ A B}
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ↑ c —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″
source-reveal-blame-catchup {χsᴸ = χsᴸ} {c = c} M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction (reveal-↠ c M↠blame)
    (↠-step (pure-step blame-reveal) ↠-refl) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)


source-conceal-blame-catchup : ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {A B : Ty Δᴸ} {c : Conv↓ Δᴸ A B}
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ↓ c —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″
source-conceal-blame-catchup {χsᴸ = χsᴸ} {c = c} M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction (conceal-↠ c M↠blame)
    (↠-step (pure-step blame-conceal) ↠-refl) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)


source-type-app-blame-catchup : ∀ {Δᴸ Δᴸ′ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ Δ′}
    {M : Term Δᴸ} {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
  → M —↠[ χsᴸ ] blame
  → ParkedEvolve χsᴸ R.[] W W′
  → Σ[ Δᴸ″ ∈ TyCtx ] Σ[ ψsᴸ ∈ StoreChanges Δᴸ Δᴸ″ ]
    Σ[ Δ″ ∈ TyCtx ] Σ[ W″ ∈ World Δᴸ″ Δᴿ Δ″ ]
      (M ⦂∀ C [ A ] —↠[ ψsᴸ ] blame) ×
      ParkedEvolve ψsᴸ R.[] W W″
source-type-app-blame-catchup {χsᴸ = χsᴸ} M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction (typeApp-↠ M↠blame)
    (↠-step (pure-step blame-•) ↠-refl) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)

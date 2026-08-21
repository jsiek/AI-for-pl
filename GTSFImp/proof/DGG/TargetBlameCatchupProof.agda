module proof.DGG.TargetBlameCatchupProof where

-- File Charter:
--   * Proves target-blame catch-up under an explicit source-boundary stack.
--   * Replays source wrappers after recursive catch-up and routes source-value
--     Λ branches through a supplied value/blame exclusion parameter.
--   * Exposes the fixed TargetBlameCatchupᵀ surface as a thin same-boundary
--     adapter once the exclusion parameter is supplied.

import Data.Nat as Nat
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms
  using (Term; Value; blame; _⟨_⟩; _↑_; _↓_; _⦂∀_[_])
import Reduction as R
open import Reduction using
  ( StoreChanges
  ; keep
  ; _∷_
  ; _—↠[_]_
  ; _—↠[_]⟨_⟩_
  ; _—→[_]⟨_⟩_
  ; _∎[]
  ; pure-step
  ; blame-⟨⟩
  ; blame-reveal
  ; blame-conceal
  ; blame-•
  )
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.CatchupToMorePreciseDef
  using (toTagRebaseAtᴸ)
open import proof.DGG.Parked.ParkedEvolveCompositionProof
  using (compose-parked-evolve)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedEvolve; ParkedWorld; evolve-keepᴸ; evolve-refl)
open import proof.DGG.TargetBlameCatchupDef
  using (TargetBlameCatchupᵀ)
open import proof.Reduction
  using
    ( _++χ_
    ; applyBodies
    ; applyConceals
    ; applyReveals
    ; cast-↠
    ; composeReduction
    ; conceal-↠
    ; reveal-↠
    ; typeApp-↠
    )
open CTX using
  (CtxImp;
   ImpEnvMono;
   TagRebaseAtᴸ;
   World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


data TargetBlameBoundary {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    World Δᴸ Δᴿ Δ → Set where

  target-blame-boundary-refl :
    TargetBlameBoundary W W

  target-blame-boundary-source-reveal : ∀ {W₀ W₁ Xᴸ? Xᴿ?}
    → TargetBlameBoundary W W₀
    → ImpEnvMono W₀ W₁
    → TagRebaseAtᴸ W₀ W₁ Xᴸ? Xᴿ?
    → TargetBlameBoundary W W₁

  target-blame-boundary-source-conceal : ∀ {W₀ W₁ Xᴸ? Xᴿ?}
    → TargetBlameBoundary W W₀
    → ImpEnvMono W₀ W₁
    → TagRebaseAtᴸ W₁ W₀ Xᴸ? Xᴿ?
    → TargetBlameBoundary W W₁


TargetValueBlameExclusionᵀ : Set
TargetValueBlameExclusionᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → Value V
  → W ∣ γ ⊢² V ⊑ blame ∶ p
  → ⊥


target-value-blame-exclusion : TargetValueBlameExclusionᵀ
target-value-blame-exclusion (CastTerms.ƛ N) ()
target-value-blame-exclusion (CastTerms.Λ vV)
    (CTI2.Λ⊑² Anv zero∈A liftγ vV′ target⊢ prem q) =
  target-value-blame-exclusion vV prem
target-value-blame-exclusion (CastTerms.Λ vV)
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV′
      target⊢ prem q) =
  target-value-blame-exclusion vV prem
target-value-blame-exclusion (CastTerms.$ k) ()
target-value-blame-exclusion (vV CastTerms.《 inert 》)
    (CTI2.cast⊑² c prem q) =
  target-value-blame-exclusion vV prem
target-value-blame-exclusion (vV CastTerms.↑ rv)
    (CTI2.reveal⊑² mono rb same c⊢ prem q) =
  target-value-blame-exclusion vV prem
target-value-blame-exclusion (vV CastTerms.↓ cv)
    (CTI2.conceal⊑² mono rb same c⊢ prem q) =
  target-value-blame-exclusion vV prem


TargetBlameCatchupUnderBoundaryᵀ : Set
TargetBlameCatchupUnderBoundaryᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → TargetBlameBoundary W Wᵖ
  → Wᵖ ∣ [] ⊢² M ⊑ blame ∶ p
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
      (M —↠[ χsᴸ ] blame) ×
      ParkedEvolve χsᴸ R.[] W W′


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
  _ , R.[] , _ , _ , (blame ∎[]) , evolve-refl


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
source-cast-blame-catchup {M = M} {χsᴸ = χsᴸ} {c = c}
    M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ⟨ c ⟩
      —↠[ χsᴸ ]⟨ cast-↠ c M↠blame ⟩
     blame ⟨ R.applyConsistencies χsᴸ c ⟩ ∎[])
    (blame ⟨ R.applyConsistencies χsᴸ c ⟩
      —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
     blame ∎[]) ,
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
source-reveal-blame-catchup {M = M} {χsᴸ = χsᴸ} {c = c}
    M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ↑ c
      —↠[ χsᴸ ]⟨ reveal-↠ c M↠blame ⟩
     blame ↑ applyReveals χsᴸ c ∎[])
    (blame ↑ applyReveals χsᴸ c
      —→[ keep ]⟨ pure-step blame-reveal ⟩
     blame ∎[]) ,
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
source-conceal-blame-catchup {M = M} {χsᴸ = χsᴸ} {c = c}
    M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ↓ c
      —↠[ χsᴸ ]⟨ conceal-↠ c M↠blame ⟩
     blame ↓ applyConceals χsᴸ c ∎[])
    (blame ↓ applyConceals χsᴸ c
      —→[ keep ]⟨ pure-step blame-conceal ⟩
     blame ∎[]) ,
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
source-type-app-blame-catchup {M = M} {χsᴸ = χsᴸ} {C = C}
    {A = A} M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ⦂∀ C [ A ]
      —↠[ χsᴸ ]⟨ typeApp-↠ M↠blame ⟩
     blame ⦂∀ applyBodies χsᴸ C [ R.applyTys χsᴸ A ] ∎[])
    (blame ⦂∀ applyBodies χsᴸ C [ R.applyTys χsᴸ A ]
      —→[ keep ]⟨ pure-step blame-• ⟩
     blame ∎[]) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)


target-blame-catchup-under-boundary :
    TargetValueBlameExclusionᵀ
  → TargetBlameCatchupUnderBoundaryᵀ
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary rel@(CTI2.blame⊑² target⊢ p) =
  _ , R.[] , _ , _ , (blame ∎[]) , evolve-refl
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary (CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ prem q) =
  ⊥-elim (target-value-blame-exclusion vV prem)
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV
      target⊢ prem q) =
  ⊥-elim (target-value-blame-exclusion vV prem)
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary (CTI2.•⊑² p∀ prem q r)
    with target-blame-catchup-under-boundary
      target-value-blame-exclusion parked boundary prem
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary (CTI2.•⊑² p∀ prem q r)
    | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
  source-type-app-blame-catchup M↠blame evol
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary (CTI2.cast⊑² c prem q)
    with target-blame-catchup-under-boundary
      target-value-blame-exclusion parked boundary prem
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary (CTI2.cast⊑² c prem q)
    | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
  source-cast-blame-catchup M↠blame evol
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary
    (CTI2.reveal⊑² mono rb CTX.same-[] c⊢ prem q)
    with target-blame-catchup-under-boundary
      target-value-blame-exclusion parked
      (target-blame-boundary-source-reveal boundary mono
        (toTagRebaseAtᴸ rb))
      prem
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary
    (CTI2.reveal⊑² mono rb CTX.same-[] c⊢ prem q)
    | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
  source-reveal-blame-catchup M↠blame evol
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary
    (CTI2.conceal⊑² mono rb CTX.same-[]
      c⊢ prem q)
    with target-blame-catchup-under-boundary
      target-value-blame-exclusion parked
      (target-blame-boundary-source-conceal boundary mono rb)
      prem
target-blame-catchup-under-boundary target-value-blame-exclusion
    parked boundary
    (CTI2.conceal⊑² mono rb CTX.same-[]
      c⊢ prem q)
    | Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol =
  source-conceal-blame-catchup M↠blame evol


target-blame-catchup : TargetBlameCatchupᵀ
target-blame-catchup parked rel =
  target-blame-catchup-under-boundary target-value-blame-exclusion
    parked target-blame-boundary-refl rel

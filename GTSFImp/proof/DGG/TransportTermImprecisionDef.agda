module proof.DGG.TransportTermImprecisionDef where

-- File Charter:
--   * States transport of term imprecision through parked evolution.
--   * Applies the source and target store-change traces to both terms and
--     reuses the canonical parked transport of the related result type.
--   * Exposes the source-only and paired single-bind transport surfaces needed
--     by the context-generalized parked driver.
--   * Contains no term-imprecision transport proof.

open import Data.List using ([])
import Data.Fin as Fin

open import Types using (Ty; ＇_)
open import Imprecision using (X⊑X; X⊑★)
open import CastTerms using (Term)
open import Reduction using (StoreChanges; bind; applyTerm; applyTerms)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision2 as CTIR
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedEvolve; evolve-refl; evolve-left-bind; evolve-both-bind)
open import proof.DGG.Parked.ParkedWorldLemma using (mapCtxᴾ; transport⊑ᴾ)
open CTI2 using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)


SourceBindTransport²ᵀ : Set
SourceBindTransport²ᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A₀ : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTI2.leftOnlyWorld X⊑★ W A₀
      ∣ mapCtxᴾ (evolve-left-bind {W = W} {A = A₀} evolve-refl) γ
      ⊢² applyTerm (bind A₀) M ⊑ M′
        ∶ transport⊑ᴾ
            (evolve-left-bind {W = W} {A = A₀} evolve-refl) p


BothBindTransport²ᵀ : Set
BothBindTransport²ᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A₀ : Ty Δᴸ} {B B₀ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (＇ Fin.zero) ⊑ᵂ⟨ CTI2.bothBindWorld X⊑X W A₀ B₀ ⟩
      (＇ Fin.zero)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTI2.bothBindWorld X⊑X W A₀ B₀
      ∣ mapCtxᴾ
          (evolve-both-bind {W = W} {A = A₀} {B = B₀} evolve-refl) γ
      ⊢² applyTerm (bind A₀) M ⊑ applyTerm (bind B₀) M′
      ∶ transport⊑ᴾ
            (evolve-both-bind {W = W} {A = A₀} {B = B₀} evolve-refl) p


TransportTermImprecisionCtxᴾᵀ : Set
TransportTermImprecisionCtxᴾᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W′ ∣ mapCtxᴾ evol γ
      ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
        ∶ transport⊑ᴾ evol p


TransportTermImprecisionᴾᵀ : Set
TransportTermImprecisionᴾᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → W′ ∣ [] ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
      ∶ transport⊑ᴾ evol p

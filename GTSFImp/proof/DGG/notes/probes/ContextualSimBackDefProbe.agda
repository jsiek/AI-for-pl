{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.ContextualSimBackDefProbe where

-- File Charter:
--   * Strict-pins the backward full-context support at the three first
--     migration paths: application left-to-right, primitive left-to-right,
--     and application-right beneath a source result cast.
--   * Uses only the canonical nineteen-edge zipper and the backward support
--     Def; it supplies no proof parameter or simulation implementation.

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyCtx; _⇒_)
open import Consistency using (Env∼; _⊢_∼_)
open import Imprecision using (_⊑_; ⇒⊑⇒)
open import Primitives using (Prim; primArgTy; primResultTy)
open import CastTerms using (Ctx; Δᵉ; Term; Value; _·_)
open import Reduction using (StoreChange; applyTerm)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( pack; _↘ᶜ*_; focus-here; focus-there
  ; focus-·₁; focus-·₂; focus-⊕₁; focus-⊕₂; focus-cast-source
  )
open import proof.DGG.SimBackContextDef using
  ( SourceEdgeEvolution; SourcePathEvolution
  ; evolve-source-here; evolve-source-there; RebuildTarget
  ; rebuild-target-here; rebuild-target-there; rebuild-target-edge
  )
open import proof.DGG.World


application-left-to-right-pin : ∀ {Cᴸ Cᴸ′ Cᴿ : Ctx}
    {γ : Cᴸ ⊑ᶜ Cᴿ} {γ′ : Cᴸ′ ⊑ᶜ Cᴿ}
    {L M : Term (Δᵉ Cᴸ)} {K N : Term (Δᵉ Cᴸ′)}
    {L′ M′ : Term (Δᵉ Cᴿ)}
    {A B : Ty (Δᵉ Cᴸ)} {A′ B′ : Ty (Δᵉ Cᴿ)}
    {C D : Ty (Δᵉ Cᴸ′)}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    {qA : C ⊑ᵀ⟨ γ′ ⟩ A′} {qB : D ⊑ᵀ⟨ γ′ ⟩ B′}
    (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
    (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    (function-rel′ : γ′ CTI.⊢² K ⊑ L′ ∶ ⇒⊑⇒ qA qB)
    (argument-rel′ : γ′ CTI.⊢² N ⊑ M′ ∶ qA)
  → SourceEdgeEvolution
      (focus-·₁ function-rel argument-rel)
      (focus-·₁ function-rel′ argument-rel′)
  → Value K
  → SourcePathEvolution
      (focus-there (focus-·₁ function-rel argument-rel) focus-here)
      (focus-there (focus-·₁ function-rel′ argument-rel′) focus-here)
    × (pack (CTI.·⊑·² function-rel′ argument-rel′)
        ↘ᶜ* pack argument-rel′)
application-left-to-right-pin function-rel argument-rel function-rel′
    argument-rel′ edge-evolution source-value =
  evolve-source-there edge-evolution evolve-source-here
  , focus-there
      (focus-·₂ function-rel′ argument-rel′ source-value) focus-here

primitive-left-to-right-pin : ∀ {Cᴸ Cᴸ′ Cᴿ : Ctx}
    {γ : Cᴸ ⊑ᶜ Cᴿ} {γ′ : Cᴸ′ ⊑ᶜ Cᴿ} {op : Prim}
    {L M : Term (Δᵉ Cᴸ)} {K N : Term (Δᵉ Cᴸ′)}
    {L′ M′ : Term (Δᵉ Cᴿ)}
    {p q : primArgTy op ⊑ᵀ⟨ γ ⟩ primArgTy op}
    {p′ q′ : primArgTy op ⊑ᵀ⟨ γ′ ⟩ primArgTy op}
    (left-rel : γ CTI.⊢² L ⊑ L′ ∶ p)
    (right-rel : γ CTI.⊢² M ⊑ M′ ∶ q)
    (result-rel : primResultTy op ⊑ᵀ⟨ γ ⟩ primResultTy op)
    (left-rel′ : γ′ CTI.⊢² K ⊑ L′ ∶ p′)
    (right-rel′ : γ′ CTI.⊢² N ⊑ M′ ∶ q′)
    (result-rel′ : primResultTy op ⊑ᵀ⟨ γ′ ⟩ primResultTy op)
  → SourceEdgeEvolution
      (focus-⊕₁ left-rel right-rel result-rel)
      (focus-⊕₁ left-rel′ right-rel′ result-rel′)
  → Value K
  → SourcePathEvolution
      (focus-there (focus-⊕₁ left-rel right-rel result-rel) focus-here)
      (focus-there
        (focus-⊕₁ left-rel′ right-rel′ result-rel′) focus-here)
    × (pack (CTI.⊕⊑⊕² op left-rel′ right-rel′ result-rel′)
        ↘ᶜ* pack right-rel′)
primitive-left-to-right-pin left-rel right-rel result-rel left-rel′
    right-rel′ result-rel′ edge-evolution source-value =
  evolve-source-there edge-evolution evolve-source-here
  , focus-there
      (focus-⊕₂ left-rel′ right-rel′ result-rel′ source-value) focus-here

result-cast-application-right-rebuild-pin : ∀ {Cᴸ Cᴿ : Ctx}
    {γ : Cᴸ ⊑ᶜ Cᴿ}
    {L M : Term (Δᵉ Cᴸ)} {L′ M′ : Term (Δᵉ Cᴿ)}
    {A B D : Ty (Δᵉ Cᴸ)} {A′ B′ : Ty (Δᵉ Cᴿ)}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    {μ : Env∼ (Δᵉ Cᴸ)}
    (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
    (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    (result-cast : μ ⊢ B ∼ D)
    (result-rel : D ⊑ᵀ⟨ γ ⟩ B′)
    (source-value : Value L)
    {Δᴿ′ : TyCtx} (χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′)
    (P′ : Term Δᴿ′)
  → RebuildTarget
      (focus-there
        (focus-cast-source result-cast
          (CTI.·⊑·² function-rel argument-rel) result-rel)
        (focus-there
          (focus-·₂ function-rel argument-rel source-value) focus-here))
      χᴿ P′ (applyTerm χᴿ L′ · P′)
result-cast-application-right-rebuild-pin function-rel argument-rel
    result-cast result-rel source-value χᴿ P′ =
  rebuild-target-there
    (rebuild-target-there
      (rebuild-target-here refl)
      (rebuild-target-edge refl))
    (rebuild-target-edge refl)

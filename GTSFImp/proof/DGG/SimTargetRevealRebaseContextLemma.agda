{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseContextLemma where

-- File Charter:
--   * Proves that a keep-store replacement of the focused CTI node replays
--     through every constructor of the canonical CTI zipper.
--   * Provides whole-root CTI reconstruction from `RebuildSource` evidence.
--   * Depends only on strict world-evolution and zipper infrastructure.

open import Reduction using (keep)
open import Relation.Binary.PropositionalEquality using
  (refl; subst; sym; trans)
open import CastTerms using (Term; ⟨_,_,_⟩)
open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)
open import proof.Reduction using
  (renamedConceal-term; renamedReveal-term)
open import proof.DGG.WorldEvolutionSequence using
  ( append-left-keep
  ; evolutions-refl
  ; multi-aligned
  ; multi-source-conceal
  ; multi-source-conceal-position
  ; multi-source-disaligned
  ; multi-source-mark
  ; multi-source-reveal
  ; multi-source-reveal-position
  ; multi-⊑ᵀ
  )


replay-edge-keep : ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {γᶠ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {L : Term Δᴸ} {L′ : Term Δᴿ}
    {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
  → (outer-related : γ CTI.⊢² M ⊑ M′ ∶ p)
  → (inner-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
  → (edge : pack outer-related ↘ᶜ pack inner-related)
  → ∀ {P N : Term Δᴸ}
  → γᶠ CTI.⊢² P ⊑ L′ ∶ s
  → RebuildSourceEdge edge keep P N
  → γ CTI.⊢² N ⊑ M′ ∶ p
replay-edge-keep
    (CTI.·⊑·² function-related argument-related)
    .function-related
    (focus-·₁ .function-related .argument-related)
    related′ (rebuild-edge refl) =
  CTI.·⊑·² related′ argument-related
replay-edge-keep
    (CTI.·⊑·² function-related argument-related)
    .argument-related
    (focus-·₂ .function-related .argument-related source-value)
    related′ (rebuild-edge refl) =
  CTI.·⊑·² function-related related′
replay-edge-keep
    (CTI.⊕⊑⊕² op left-related right-related r)
    .left-related
    (focus-⊕₁ .left-related .right-related .r)
    related′ (rebuild-edge refl) =
  CTI.⊕⊑⊕² op related′ right-related r
replay-edge-keep
    (CTI.⊕⊑⊕² op left-related right-related r)
    .right-related
    (focus-⊕₂ .left-related .right-related .r source-value)
    related′ (rebuild-edge refl) =
  CTI.⊕⊑⊕² op left-related related′ r
replay-edge-keep
    (CTI.•⊑•² p∀ related q r) .related
    (focus-•-paired .p∀ .related .q .r)
    related′ (rebuild-edge refl) =
  CTI.•⊑•² p∀ related′ q r
replay-edge-keep
    (CTI.•⊑² p∀ related q r) .related
    (focus-•-source .p∀ .related .q .r)
    related′ (rebuild-edge refl) =
  CTI.•⊑² p∀ related′ q r
replay-edge-keep
    (CTI.cast⊑cast² source-cast target-cast related q) .related
    (focus-cast-paired .source-cast .target-cast .related .q)
    related′ (rebuild-edge refl) =
  CTI.cast⊑cast² source-cast target-cast related′ q
replay-edge-keep
    (CTI.⊑cast² target-cast related q) .related
    (focus-cast-target .target-cast .related .q)
    related′ (rebuild-edge refl) =
  CTI.⊑cast² target-cast related′ q
replay-edge-keep
    (CTI.cast⊑² source-cast related q) .related
    (focus-cast-source .source-cast .related .q)
    related′ (rebuild-edge refl) =
  CTI.cast⊑² source-cast related′ q
replay-edge-keep
    (CTI.⊑reveal-identity target-reveal absent related q) .related
    (focus-target-reveal-identity .target-reveal .absent .related .q)
    related′ (rebuild-edge refl) =
  CTI.⊑reveal-identity target-reveal absent related′ q
replay-edge-keep
    (CTI.⊑conceal-identity target-conceal absent related q) .related
    (focus-target-conceal-identity .target-conceal .absent .related .q)
    related′ (rebuild-edge refl) =
  CTI.⊑conceal-identity target-conceal absent related′ q
replay-edge-keep {γ = γ} {M′ = M′}
    (CTI.reveal⊑-identity {c = c} source-reveal absent related q) .related
    (focus-source-reveal-identity .source-reveal .absent .related .q)
    related′ (rebuild-edge refl) =
  let evolution = append-left-keep {W = γ} evolutions-refl
      source-reveal′ = multi-source-reveal evolution source-reveal
  in
    subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
      (sym (renamedReveal-term _ c))
      (CTI.reveal⊑-identity {γ = γ} source-reveal′
        (trans (multi-source-reveal-position evolution source-reveal)
          absent)
        related′ (multi-⊑ᵀ evolution q))
replay-edge-keep {γ = γ} {M′ = M′}
    (CTI.conceal⊑-identity {c = c} source-conceal absent related q)
    .related
    (focus-source-conceal-identity .source-conceal .absent .related .q)
    related′ (rebuild-edge refl) =
  let evolution = append-left-keep {W = γ} evolutions-refl
      source-conceal′ = multi-source-conceal evolution source-conceal
  in
    subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
      (sym (renamedConceal-term _ c))
      (CTI.conceal⊑-identity {γ = γ} source-conceal′
        (trans (multi-source-conceal-position evolution source-conceal)
          absent)
        related′ (multi-⊑ᵀ evolution q))
replay-edge-keep {γ = γ} {M′ = M′}
    (CTI.reveal⊑-only² {c = c} source-reveal present mark free represented
      related q)
    .related
    (focus-source-reveal-only .source-reveal .present .mark .free
      .represented .related .q)
    related′ (rebuild-edge refl) =
  let evolution = append-left-keep {W = γ} evolutions-refl
      source-reveal′ = multi-source-reveal evolution source-reveal
      position = multi-source-reveal-position evolution source-reveal
  in
    subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
      (sym (renamedReveal-term _ c))
      (CTI.reveal⊑-only² {γ = γ} source-reveal′
        (λ absent → present (trans (sym position) absent))
        (multi-source-mark evolution mark)
        (multi-source-disaligned evolution free)
        (multi-⊑ᵀ evolution represented)
        related′ (multi-⊑ᵀ evolution q))
replay-edge-keep {γ = γ} {M′ = M′}
    (CTI.conceal⊑-only² {c = c} source-conceal present mark free
      represented related q)
    .related
    (focus-source-conceal-only .source-conceal .present .mark .free
      .represented .related .q)
    related′ (rebuild-edge refl) =
  let evolution = append-left-keep {W = γ} evolutions-refl
      source-conceal′ = multi-source-conceal evolution source-conceal
      position = multi-source-conceal-position evolution source-conceal
  in
    subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
      (sym (renamedConceal-term _ c))
      (CTI.conceal⊑-only² {γ = γ} source-conceal′
        (λ absent → present (trans (sym position) absent))
        (multi-source-mark evolution mark)
        (multi-source-disaligned evolution free)
        (multi-⊑ᵀ evolution represented)
        related′ (multi-⊑ᵀ evolution q))
replay-edge-keep {γ = γ} {M′ = M′}
    (CTI.reveal⊑reveal² {c = c} source-reveal target-reveal positions
      aligned represented related q)
    .related
    (focus-reveal-paired .source-reveal .target-reveal .positions .aligned
      .represented .related .q)
    related′ (rebuild-edge refl) =
  let evolution = append-left-keep {W = γ} evolutions-refl
      source-reveal′ = multi-source-reveal evolution source-reveal
  in
    subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
      (sym (renamedReveal-term _ c))
      (CTI.reveal⊑reveal² {γ = γ} source-reveal′ target-reveal
        (trans (multi-source-reveal-position evolution source-reveal)
          positions)
        (multi-aligned evolution aligned)
        (multi-⊑ᵀ evolution represented)
        related′ (multi-⊑ᵀ evolution q))
replay-edge-keep {γ = γ} {M′ = M′}
    (CTI.conceal⊑conceal² {c = c} source-conceal target-conceal
      positions aligned represented related q)
    .related
    (focus-conceal-paired .source-conceal .target-conceal .positions
      .aligned .represented .related .q)
    related′ (rebuild-edge refl) =
  let evolution = append-left-keep {W = γ} evolutions-refl
      source-conceal′ = multi-source-conceal evolution source-conceal
  in
    subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
      (sym (renamedConceal-term _ c))
      (CTI.conceal⊑conceal² {γ = γ} source-conceal′ target-conceal
        (trans (multi-source-conceal-position evolution source-conceal)
          positions)
        (multi-aligned evolution aligned)
        (multi-⊑ᵀ evolution represented)
        related′ (multi-⊑ᵀ evolution q))
replay-edge-keep
    (CTI.⊑reveal-rebase² target-reveal rebase related q) .related
    (focus-target-reveal-rebase .target-reveal .rebase .related .q)
    related′ (rebuild-edge refl) =
  CTI.⊑reveal-rebase² target-reveal rebase related′ q
replay-edge-keep
    (CTI.⊑conceal-rebase² target-conceal rebase related q) .related
    (focus-target-conceal-rebase .target-conceal .rebase .related .q)
    related′ (rebuild-edge refl) =
  CTI.⊑conceal-rebase² target-conceal rebase related′ q


replay-context-keep : ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {γᶠ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {L : Term Δᴸ} {L′ : Term Δᴿ}
    {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
  → (outer-related : γ CTI.⊢² M ⊑ M′ ∶ p)
  → (focus-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
  → (path : pack outer-related ↘ᶜ* pack focus-related)
  → ∀ {P N : Term Δᴸ}
  → γᶠ CTI.⊢² P ⊑ L′ ∶ s
  → RebuildSource path keep P N
  → γ CTI.⊢² N ⊑ M′ ∶ p
replay-context-keep related .related focus-here related′
    (rebuild-here refl) = related′
replay-context-keep outer-related focus-related
    (focus-there {middle = pack middle-related} edge tail) related′
    (rebuild-there tail-rebuild edge-rebuild) =
  replay-edge-keep outer-related middle-related edge
    (replay-context-keep middle-related focus-related tail related′
      tail-rebuild)
    edge-rebuild

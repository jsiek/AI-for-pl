{-# OPTIONS --safe #-}

module proof.DGG.SimBackContextDef where

-- File Charter:
--   * Adds the backward-facing operations to the canonical full-context CTI
--     zipper without duplicating its nineteen evaluation edges.
--   * Reconstructs target reducts through every target evaluation frame.
--   * Records source-side path evolution by preserved target frames and
--     source readiness, retaining constructor-form path evidence.

import Data.Nat as Nat
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using
  ( Conv↑; Conv↓; rename↑; rename↓ )
open import Primitives using (Prim)
open import CastTerms using
  ( Ctx; Δᵉ; Term; Value; _·_; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_; _⊕[_]_ )
open import Reduction using
  ( StoreChange; applyTy; applyTerm; applyBody; applyConsistency; applyVar )
open import proof.DGG.SimTargetRevealRebaseContextDef using
  ( RelatedConfiguration; pack; sourceTerm; targetTerm
  ; _↘ᶜ_; focus-·₁; focus-·₂; focus-⊕₁; focus-⊕₂
  ; focus-•-paired; focus-•-source
  ; focus-cast-paired; focus-cast-target; focus-cast-source
  ; focus-target-reveal-identity; focus-target-conceal-identity
  ; focus-source-reveal-identity; focus-source-conceal-identity
  ; focus-source-reveal-only; focus-source-conceal-only
  ; focus-reveal-paired; focus-conceal-paired
  ; focus-target-reveal-rebase; focus-target-conceal-rebase
  ; _↘ᶜ*_; focus-here; focus-there; extend-focus
  )
open import proof.DGG.World


world : ∀ {Cᴸ Cᴿ}
  → RelatedConfiguration Cᴸ Cᴿ → Cᴸ ⊑ᶜ Cᴿ
world (pack {γ = γ} related) = γ


------------------------------------------------------------------------
-- Target frames and reconstruction
------------------------------------------------------------------------

data TargetFrame (Δ : TyCtx) : Set where
  app-leftᵗᶠ : Term Δ → TargetFrame Δ
  app-rightᵗᶠ : Term Δ → TargetFrame Δ
  primitive-leftᵗᶠ : Prim → Term Δ → TargetFrame Δ
  primitive-rightᵗᶠ : Prim → Term Δ → TargetFrame Δ
  paired-type-applicationᵗᶠ :
    Ty (Nat.suc Δ) → Ty Δ → TargetFrame Δ
  source-type-applicationᵗᶠ : TargetFrame Δ
  paired-castᵗᶠ : ∀ {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → TargetFrame Δ
  target-castᵗᶠ : ∀ {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → TargetFrame Δ
  source-castᵗᶠ : TargetFrame Δ
  target-reveal-identityᵗᶠ :
    ∀ {A B : Ty Δ} → Conv↑ Δ A B → TargetFrame Δ
  target-conceal-identityᵗᶠ :
    ∀ {A B : Ty Δ} → Conv↓ Δ A B → TargetFrame Δ
  source-reveal-identityᵗᶠ : TargetFrame Δ
  source-conceal-identityᵗᶠ : TargetFrame Δ
  source-reveal-onlyᵗᶠ : TargetFrame Δ
  source-conceal-onlyᵗᶠ : TargetFrame Δ
  paired-revealᵗᶠ :
    ∀ {A B : Ty Δ} → Conv↑ Δ A B → TargetFrame Δ
  paired-concealᵗᶠ :
    ∀ {A B : Ty Δ} → Conv↓ Δ A B → TargetFrame Δ
  target-reveal-rebaseᵗᶠ :
    ∀ {A B : Ty Δ} → Conv↑ Δ A B → TargetFrame Δ
  target-conceal-rebaseᵗᶠ :
    ∀ {A B : Ty Δ} → Conv↓ Δ A B → TargetFrame Δ

targetFrame : ∀ {Cᴸ Cᴿ}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ inner → TargetFrame (Δᵉ Cᴿ)
targetFrame (focus-·₁ {M′ = M′} function-rel argument-rel) =
  app-leftᵗᶠ M′
targetFrame
    (focus-·₂ {L′ = L′} function-rel argument-rel source-value) =
  app-rightᵗᶠ L′
targetFrame (focus-⊕₁ {M′ = M′} {op = op} left-rel right-rel r) =
  primitive-leftᵗᶠ op M′
targetFrame
    (focus-⊕₂ {L′ = L′} {op = op} left-rel right-rel r
      source-value) =
  primitive-rightᵗᶠ op L′
targetFrame (focus-•-paired {C′ = C′} {A′ = A′} p∀ related q r) =
  paired-type-applicationᵗᶠ C′ A′
targetFrame (focus-•-source p∀ related q r) =
  source-type-applicationᵗᶠ
targetFrame (focus-cast-paired c c′ related q) = paired-castᵗᶠ c′
targetFrame (focus-cast-target c′ related q) = target-castᵗᶠ c′
targetFrame (focus-cast-source c related q) = source-castᵗᶠ
targetFrame (focus-target-reveal-identity {c′ = c′} c′⊢ absent related q) =
  target-reveal-identityᵗᶠ c′
targetFrame
    (focus-target-conceal-identity {c′ = c′} c′⊢ absent related q) =
  target-conceal-identityᵗᶠ c′
targetFrame (focus-source-reveal-identity c⊢ absent related q) =
  source-reveal-identityᵗᶠ
targetFrame (focus-source-conceal-identity c⊢ absent related q) =
  source-conceal-identityᵗᶠ
targetFrame
    (focus-source-reveal-only c⊢ present mark free represented related q) =
  source-reveal-onlyᵗᶠ
targetFrame
    (focus-source-conceal-only c⊢ present mark free represented related q) =
  source-conceal-onlyᵗᶠ
targetFrame
    (focus-reveal-paired {c′ = c′} c⊢ c′⊢ positions aligned represented
      related q) =
  paired-revealᵗᶠ c′
targetFrame
    (focus-conceal-paired {c′ = c′} c⊢ c′⊢ positions aligned represented
      related q) =
  paired-concealᵗᶠ c′
targetFrame (focus-target-reveal-rebase {c′ = c′} c′⊢ rebase related q) =
  target-reveal-rebaseᵗᶠ c′
targetFrame
    (focus-target-conceal-rebase {c′ = c′} c′⊢ rebase related q) =
  target-conceal-rebaseᵗᶠ c′

rebuildTargetFrame : ∀ {Δ Δ′}
  → TargetFrame Δ → StoreChange Δ Δ′ → Term Δ′ → Term Δ′
rebuildTargetFrame (app-leftᵗᶠ M) χ P = P · applyTerm χ M
rebuildTargetFrame (app-rightᵗᶠ L) χ P = applyTerm χ L · P
rebuildTargetFrame (primitive-leftᵗᶠ op M) χ P =
  P ⊕[ op ] applyTerm χ M
rebuildTargetFrame (primitive-rightᵗᶠ op L) χ P =
  applyTerm χ L ⊕[ op ] P
rebuildTargetFrame (paired-type-applicationᵗᶠ C A) χ P =
  P ⦂∀ applyBody χ C [ applyTy χ A ]
rebuildTargetFrame source-type-applicationᵗᶠ χ P = P
rebuildTargetFrame (paired-castᵗᶠ c) χ P =
  P ⟨ applyConsistency χ c ⟩
rebuildTargetFrame (target-castᵗᶠ c) χ P =
  P ⟨ applyConsistency χ c ⟩
rebuildTargetFrame source-castᵗᶠ χ P = P
rebuildTargetFrame (target-reveal-identityᵗᶠ c) χ P =
  P ↑ rename↑ (λ X → applyVar χ X) c
rebuildTargetFrame (target-conceal-identityᵗᶠ c) χ P =
  P ↓ rename↓ (λ X → applyVar χ X) c
rebuildTargetFrame source-reveal-identityᵗᶠ χ P = P
rebuildTargetFrame source-conceal-identityᵗᶠ χ P = P
rebuildTargetFrame source-reveal-onlyᵗᶠ χ P = P
rebuildTargetFrame source-conceal-onlyᵗᶠ χ P = P
rebuildTargetFrame (paired-revealᵗᶠ c) χ P =
  P ↑ rename↑ (λ X → applyVar χ X) c
rebuildTargetFrame (paired-concealᵗᶠ c) χ P =
  P ↓ rename↓ (λ X → applyVar χ X) c
rebuildTargetFrame (target-reveal-rebaseᵗᶠ c) χ P =
  P ↑ rename↑ (λ X → applyVar χ X) c
rebuildTargetFrame (target-conceal-rebaseᵗᶠ c) χ P =
  P ↓ rename↓ (λ X → applyVar χ X) c

rebuildTargetEdge : ∀ {Cᴸ Cᴿ Δᴿ′}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ inner
  → StoreChange (Δᵉ Cᴿ) Δᴿ′
  → Term Δᴿ′
  → Term Δᴿ′
rebuildTargetEdge edge χᴿ P = rebuildTargetFrame (targetFrame edge) χᴿ P

data RebuildTargetEdge {Cᴸ Cᴿ : Ctx} {Δᴿ′ : TyCtx}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
    (χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′)
    (inner-result : Term Δᴿ′) : Term Δᴿ′ → Set where

  rebuild-target-edge : ∀ {outer-result}
    → outer-result ≡ rebuildTargetEdge edge χᴿ inner-result
    → RebuildTargetEdge edge χᴿ inner-result outer-result

data RebuildTarget {Cᴸ Cᴿ : Ctx} {Δᴿ′ : TyCtx} :
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
  → (path : outer ↘ᶜ* focus)
  → (χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′)
  → (focus-result : Term Δᴿ′)
  → Term Δᴿ′ → Set₁ where

  rebuild-target-here : ∀ {related : RelatedConfiguration Cᴸ Cᴿ}
      {χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′}
      {focus-result result : Term Δᴿ′}
    → result ≡ focus-result
    → RebuildTarget {outer = related} {focus = related}
        focus-here χᴿ focus-result result

  rebuild-target-there : ∀
      {outer focus middle : RelatedConfiguration Cᴸ Cᴿ}
      {χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′}
      {focus-result middle-result outer-result : Term Δᴿ′}
      {edge : outer ↘ᶜ middle} {tail : middle ↘ᶜ* focus}
    → RebuildTarget tail χᴿ focus-result middle-result
    → RebuildTargetEdge edge χᴿ middle-result outer-result
    → RebuildTarget (focus-there edge tail) χᴿ focus-result
        outer-result

extend-target-rebuild : ∀ {Cᴸ Cᴿ Δᴿ′}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    {path : outer ↘ᶜ* middle} {edge : middle ↘ᶜ focus}
    {χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′}
    {focus-result middle-result outer-result : Term Δᴿ′}
  → RebuildTarget path χᴿ middle-result outer-result
  → RebuildTargetEdge edge χᴿ focus-result middle-result
  → RebuildTarget (extend-focus path edge) χᴿ focus-result
      outer-result
extend-target-rebuild (rebuild-target-here refl) edge-rebuild =
  rebuild-target-there (rebuild-target-here refl) edge-rebuild
extend-target-rebuild
    (rebuild-target-there tail-rebuild outer-rebuild) edge-rebuild =
  rebuild-target-there
    (extend-target-rebuild tail-rebuild edge-rebuild) outer-rebuild


------------------------------------------------------------------------
-- Source-side evolution of the same whole evaluation path
------------------------------------------------------------------------

SourceEdgeReady : ∀ {Cᴸ Cᴿ}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
  → outer ↘ᶜ inner → Set
SourceEdgeReady (focus-·₁ function-rel argument-rel) = ⊤
SourceEdgeReady
    (focus-·₂ {L = L} function-rel argument-rel source-value) =
  Value L
SourceEdgeReady (focus-⊕₁ left-rel right-rel r) = ⊤
SourceEdgeReady
    (focus-⊕₂ {L = L} left-rel right-rel r source-value) =
  Value L
SourceEdgeReady (focus-•-paired p∀ related q r) = ⊤
SourceEdgeReady (focus-•-source p∀ related q r) = ⊤
SourceEdgeReady (focus-cast-paired c c′ related q) = ⊤
SourceEdgeReady (focus-cast-target c′ related q) = ⊤
SourceEdgeReady (focus-cast-source c related q) = ⊤
SourceEdgeReady (focus-target-reveal-identity c′⊢ absent related q) = ⊤
SourceEdgeReady (focus-target-conceal-identity c′⊢ absent related q) = ⊤
SourceEdgeReady (focus-source-reveal-identity c⊢ absent related q) = ⊤
SourceEdgeReady (focus-source-conceal-identity c⊢ absent related q) = ⊤
SourceEdgeReady
    (focus-source-reveal-only c⊢ present mark free represented related q) =
  ⊤
SourceEdgeReady
    (focus-source-conceal-only c⊢ present mark free represented related q) =
  ⊤
SourceEdgeReady
    (focus-reveal-paired c⊢ c′⊢ positions aligned represented related q) =
  ⊤
SourceEdgeReady
    (focus-conceal-paired c⊢ c′⊢ positions aligned represented related q) =
  ⊤
SourceEdgeReady (focus-target-reveal-rebase c′⊢ rebase related q) = ⊤
SourceEdgeReady (focus-target-conceal-rebase c′⊢ rebase related q) = ⊤

record SourceEdgeEvolution {Cᴸ Cᴸ′ Cᴿ : Ctx}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ inner′ : RelatedConfiguration Cᴸ′ Cᴿ}
    (edge : outer ↘ᶜ inner) (edge′ : outer′ ↘ᶜ inner′) : Set₁ where
  constructor evolve-source-edge
  field
    same-target-frame : targetFrame edge ≡ targetFrame edge′
    source-edge-ready : SourceEdgeReady edge′

open SourceEdgeEvolution

source-edge-reflexive : ∀ {Cᴸ Cᴿ}
    {outer inner : RelatedConfiguration Cᴸ Cᴿ}
    (edge : outer ↘ᶜ inner)
  → SourceEdgeEvolution edge edge
source-edge-reflexive (focus-·₁ function-rel argument-rel) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-·₂ function-rel argument-rel source-value) =
  evolve-source-edge refl source-value
source-edge-reflexive (focus-⊕₁ left-rel right-rel r) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-⊕₂ left-rel right-rel r source-value) =
  evolve-source-edge refl source-value
source-edge-reflexive (focus-•-paired p∀ related q r) =
  evolve-source-edge refl tt
source-edge-reflexive (focus-•-source p∀ related q r) =
  evolve-source-edge refl tt
source-edge-reflexive (focus-cast-paired c c′ related q) =
  evolve-source-edge refl tt
source-edge-reflexive (focus-cast-target c′ related q) =
  evolve-source-edge refl tt
source-edge-reflexive (focus-cast-source c related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-target-reveal-identity c′⊢ absent related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-target-conceal-identity c′⊢ absent related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-source-reveal-identity c⊢ absent related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-source-conceal-identity c⊢ absent related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-source-reveal-only c⊢ present mark free represented related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-source-conceal-only c⊢ present mark free represented related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-reveal-paired c⊢ c′⊢ positions aligned represented related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-conceal-paired c⊢ c′⊢ positions aligned represented related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-target-reveal-rebase c′⊢ rebase related q) =
  evolve-source-edge refl tt
source-edge-reflexive
    (focus-target-conceal-rebase c′⊢ rebase related q) =
  evolve-source-edge refl tt

data SourcePathEvolution {Cᴸ Cᴸ′ Cᴿ : Ctx} :
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ focus′ : RelatedConfiguration Cᴸ′ Cᴿ}
  → (path : outer ↘ᶜ* focus) (path′ : outer′ ↘ᶜ* focus′)
  → Set₁ where

  evolve-source-here : ∀ {related related′}
    → SourcePathEvolution
        (focus-here {related = related}) (focus-here {related = related′})

  evolve-source-there : ∀
      {outer middle focus outer′ middle′ focus′}
      {edge : outer ↘ᶜ middle} {tail : middle ↘ᶜ* focus}
      {edge′ : outer′ ↘ᶜ middle′} {tail′ : middle′ ↘ᶜ* focus′}
    → SourceEdgeEvolution edge edge′
    → SourcePathEvolution tail tail′
    → SourcePathEvolution
        (focus-there edge tail) (focus-there edge′ tail′)

source-path-reflexive : ∀ {Cᴸ Cᴿ}
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    (path : outer ↘ᶜ* focus)
  → SourcePathEvolution path path
source-path-reflexive focus-here = evolve-source-here
source-path-reflexive (focus-there edge tail) =
  evolve-source-there (source-edge-reflexive edge)
    (source-path-reflexive tail)

data SourceExtendedPathEvolution {Cᴸ Cᴸ′ Cᴿ : Ctx}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    (path : outer ↘ᶜ* middle) (edge : middle ↘ᶜ focus)
    {outer′ focus′ : RelatedConfiguration Cᴸ′ Cᴿ}
    (path′ : outer′ ↘ᶜ* focus′) : Set₁ where

  evolved-source-extended-path : ∀
      {middle′ : RelatedConfiguration Cᴸ′ Cᴿ}
      (prefix′ : outer′ ↘ᶜ* middle′)
      (edge′ : middle′ ↘ᶜ focus′)
    → path′ ≡ extend-focus prefix′ edge′
    → SourcePathEvolution path prefix′
    → SourceEdgeEvolution edge edge′
    → SourceExtendedPathEvolution path edge path′

split-source-extended-path : ∀ {Cᴸ Cᴸ′ Cᴿ}
    {outer middle focus : RelatedConfiguration Cᴸ Cᴿ}
    {path : outer ↘ᶜ* middle} {edge : middle ↘ᶜ focus}
    {outer′ focus′ : RelatedConfiguration Cᴸ′ Cᴿ}
    {path′ : outer′ ↘ᶜ* focus′}
  → SourcePathEvolution (extend-focus path edge) path′
  → SourceExtendedPathEvolution path edge path′
split-source-extended-path {path = focus-here}
    (evolve-source-there edge-evolution evolve-source-here) =
  evolved-source-extended-path focus-here _ refl evolve-source-here
    edge-evolution
split-source-extended-path {path = focus-there outer-edge tail}
    (evolve-source-there outer-evolution tail-evolution)
    with split-source-extended-path tail-evolution
split-source-extended-path {path = focus-there outer-edge tail}
    (evolve-source-there outer-evolution tail-evolution)
  | evolved-source-extended-path prefix′ edge′ path-eq prefix-evolution
      edge-evolution =
    evolved-source-extended-path (focus-there _ prefix′) edge′
      (cong (focus-there _) path-eq)
      (evolve-source-there outer-evolution prefix-evolution)
      edge-evolution

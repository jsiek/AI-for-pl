{-# OPTIONS --safe #-}

module proof.DGG.SourceRebaseStackDef where

-- File Charter:
--   * Defines the balanced stack of open source-rebase scopes used by forward
--     simulation.
--   * A direct reveal pushes one frame; conceal pops that exact frame through
--     three protected CTI scopes and four chronological runtime scopes.
--   * Defines first-order stack evolution, its endpoint histories, and source
--     rebase transport without a classifier or result wrapper.

import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; subst; sym; trans)

import TermCtx as TC
open import TermCtx using (TermCtx)
open import Types using (Ty; TyVar; ★; ＇_; ⇑ᵗ)
open import TyStore using (TyStore; lookupStore)
open import Imprecision using (VarImp)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ)
import Reduction as R
open R using (StoreChanges)
open import proof.DGG.SourceRebase
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  ( evolution-bind-both
  ; evolution-bind-both-star
  ; evolution-bind-left
  ; evolution-bind-right
  ; evolution-keep
  )
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; composeMultiWorldEvolution
  ; evolutions-refl
  ; evolutions-step-both
  ; evolutions-step-left
  ; evolutions-step-right
  )
open import proof.Reduction using (_++χ_; applyVars; applyVars-++)


data SourceRebaseStack : ∀ {Γᴸ Γᴿ}
    → (root top : Γᴸ ⊑ᶜ Γᴿ)
    → Set where

  rebase-stack-root : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    → openFramesᶜ γ ≡ []
    → SourceRebaseStack γ γ

  rebase-stack-push : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
      {X : TyVar (Δᵉ Γᴸ)} {Y : TyVar (Δᵉ Γᴿ)}
    → SourceRebaseStack γ⁰ γ
    → (ok : PivotUpdateᵗ
        (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y))
    → (represented : (＇ X) ⊑ᵀ⟨ γ ⟩
        lookupStore (CastTerms.Σᵉ Γᴿ) Y)
    → SourceRebaseStack γ⁰
        (γ ▻ᶜ rebase-source-changeᶜ
          X Y ok open-frameᶜ represented)

  rebase-stack-term : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    → SourceRebaseStack γ⁰ γ
    → (represented⁰ : A ⊑ᵀ⟨ γ⁰ ⟩ B)
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → SourceRebaseStack
        (bind-termᶜ γ⁰ represented⁰) (bind-termᶜ γ represented)

  rebase-stack-both : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ} {v : VarImp}
    → SourceRebaseStack γ⁰ γ
    → SourceRebaseStack
        (liftBothᶜ v γ⁰) (liftBothᶜ v γ)

  rebase-stack-left : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
    → SourceRebaseStack γ⁰ γ
    → SourceRebaseStack (liftLeftᶜ γ⁰) (liftLeftᶜ γ)

  rebase-stack-bind-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → (A : Ty Δᴸ)
    → SourceRebaseStack γ⁰ γ
    → (eq⁰ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eq : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → SourceRebaseStack
        (γ⁰ ▻ᶜ bind-left-changeᶜ A eq⁰)
        (γ ▻ᶜ bind-left-changeᶜ A eq)

  rebase-stack-bind-right : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → SourceRebaseStack γ⁰ γ
    → (fresh⁰ : RightBindFreshᶜ γ⁰ B)
    → (fresh : RightBindFreshᶜ γ B)
    → (eq⁰ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eq : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseStack
        (γ⁰ ▻ᶜ bind-right-changeᶜ B fresh⁰ eq⁰)
        (γ ▻ᶜ bind-right-changeᶜ B fresh eq)

  rebase-stack-bind-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → SourceRebaseStack γ⁰ γ
    → (represented⁰ : A ⊑ᵀ⟨ γ⁰ ⟩ B)
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (eqᴸ⁰ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴿ⁰ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseStack
        (γ⁰ ▻ᶜ bind-both-changeᶜ represented⁰ eqᴸ⁰ eqᴿ⁰)
        (γ ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ)

  rebase-stack-bind-both-star : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → SourceRebaseStack γ⁰ γ
    → (represented⁰ : A ⊑ᵀ⟨ γ⁰ ⟩ B)
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (A≠★ : ⇑ᵗ A ≢ ★)
    → (eqᴸ⁰ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴿ⁰ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseStack
        (γ⁰ ▻ᶜ bind-both-star-changeᶜ
          represented⁰ A≠★ eqᴸ⁰ eqᴿ⁰)
        (γ ▻ᶜ bind-both-star-changeᶜ
          represented A≠★ eqᴸ eqᴿ)


source-rebase-stack : ∀ {Γᴸ Γᴿ : Ctx}
    {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ} {X Y}
  → openFramesᶜ γ⁰ ≡ []
  → SourceRebaseᶜ γ⁰ γ X Y
  → SourceRebaseStack γ⁰ γ
source-rebase-stack no-rebase (source-rebase-now ok represented) =
  rebase-stack-push (rebase-stack-root no-rebase) ok represented
source-rebase-stack no-rebase
    (source-rebase-bind-left A rebase eq⁰ eq) =
  rebase-stack-bind-left A
    (source-rebase-stack
      (renameOpenFrames-empty-invert no-rebase) rebase)
    eq⁰ eq
source-rebase-stack no-rebase
    (source-rebase-bind-right rebase fresh⁰ fresh eq⁰ eq) =
  rebase-stack-bind-right
    (source-rebase-stack
      (renameOpenFrames-empty-invert no-rebase) rebase)
    fresh⁰ fresh eq⁰ eq
source-rebase-stack no-rebase
    (source-rebase-bind-both rebase represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  rebase-stack-bind-both
    (source-rebase-stack
      (renameOpenFrames-empty-invert no-rebase) rebase)
    represented⁰ represented eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ
source-rebase-stack no-rebase
    (source-rebase-bind-both-star rebase represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  rebase-stack-bind-both-star
    (source-rebase-stack
      (renameOpenFrames-empty-invert no-rebase) rebase)
    represented⁰ represented A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ
source-rebase-stack no-rebase
    (source-rebase-bind-term rebase represented⁰ represented) =
  rebase-stack-term (source-rebase-stack no-rebase rebase)
    represented⁰ represented
source-rebase-stack no-rebase (source-rebase-lift-both rebase) =
  rebase-stack-both
    (source-rebase-stack
      (renameOpenFrames-empty-invert no-rebase) rebase)
source-rebase-stack no-rebase (source-rebase-lift-left rebase) =
  rebase-stack-left
    (source-rebase-stack
      (renameOpenFrames-empty-invert no-rebase) rebase)


source-rebase-stack-root-no-open-frames : ∀ {Γᴸ Γᴿ : Ctx}
    {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
  → SourceRebaseStack γ⁰ γ
  → openFramesᶜ γ⁰ ≡ []
source-rebase-stack-root-no-open-frames
    (rebase-stack-root no-open) = no-open
source-rebase-stack-root-no-open-frames
    (rebase-stack-push stack ok represented) =
  source-rebase-stack-root-no-open-frames stack
source-rebase-stack-root-no-open-frames
    (rebase-stack-term stack represented⁰ represented) =
  source-rebase-stack-root-no-open-frames stack
source-rebase-stack-root-no-open-frames (rebase-stack-both stack) =
  renameOpenFrames-empty
    (source-rebase-stack-root-no-open-frames stack)
source-rebase-stack-root-no-open-frames (rebase-stack-left stack) =
  renameOpenFrames-empty
    (source-rebase-stack-root-no-open-frames stack)
source-rebase-stack-root-no-open-frames
    (rebase-stack-bind-left A stack eq⁰ eq) =
  renameOpenFrames-empty
    (source-rebase-stack-root-no-open-frames stack)
source-rebase-stack-root-no-open-frames
    (rebase-stack-bind-right stack fresh⁰ fresh eq⁰ eq) =
  renameOpenFrames-empty
    (source-rebase-stack-root-no-open-frames stack)
source-rebase-stack-root-no-open-frames
    (rebase-stack-bind-both stack represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  renameOpenFrames-empty
    (source-rebase-stack-root-no-open-frames stack)
source-rebase-stack-root-no-open-frames
    (rebase-stack-bind-both-star stack represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  renameOpenFrames-empty
    (source-rebase-stack-root-no-open-frames stack)


pop-source-rebase-stack : ∀ {Γᴸ Γᴿ : Ctx}
    {γ⁰ γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {X Y}
  → SourceRebaseStack γ⁰ γ
  → SourceRebaseᶜ γᵖ γ X Y
  → SourceRebaseStack γ⁰ γᵖ
pop-source-rebase-stack (rebase-stack-root no-open) rebase
    with trans (sym no-open) (open-source-rebase-frames rebase)
pop-source-rebase-stack (rebase-stack-root no-open) rebase | ()
pop-source-rebase-stack
    (rebase-stack-push stack ok represented)
    (source-rebase-now .ok .represented) = stack
pop-source-rebase-stack
    (rebase-stack-term stack represented⁰ represented)
    (source-rebase-bind-term rebase representedᵖ .represented)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-term stack represented⁰ represented)
    (source-rebase-bind-term rebase representedᵖ .represented)
    | stack′ = rebase-stack-term stack′ represented⁰ representedᵖ
pop-source-rebase-stack
    (rebase-stack-both stack) (source-rebase-lift-both rebase)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-both stack) (source-rebase-lift-both rebase)
    | stack′ = rebase-stack-both stack′
pop-source-rebase-stack
    (rebase-stack-left stack) (source-rebase-lift-left rebase)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-left stack) (source-rebase-lift-left rebase)
    | stack′ = rebase-stack-left stack′
pop-source-rebase-stack
    (rebase-stack-bind-left A stack eq⁰ eq)
    (source-rebase-bind-left .A rebase eqᵖ .eq)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-bind-left A stack eq⁰ eq)
    (source-rebase-bind-left .A rebase eqᵖ .eq)
    | stack′ = rebase-stack-bind-left A stack′ eq⁰ eqᵖ
pop-source-rebase-stack
    (rebase-stack-bind-right stack fresh⁰ fresh eq⁰ eq)
    (source-rebase-bind-right rebase freshᵖ .fresh eqᵖ .eq)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-bind-right stack fresh⁰ fresh eq⁰ eq)
    (source-rebase-bind-right rebase freshᵖ .fresh eqᵖ .eq)
    | stack′ =
      rebase-stack-bind-right stack′ fresh⁰ freshᵖ eq⁰ eqᵖ
pop-source-rebase-stack
    (rebase-stack-bind-both stack represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ)
    (source-rebase-bind-both rebase representedᵖ .represented
      eqᴸᵖ .eqᴸ eqᴿᵖ .eqᴿ)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-bind-both stack represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ)
    (source-rebase-bind-both rebase representedᵖ .represented
      eqᴸᵖ .eqᴸ eqᴿᵖ .eqᴿ)
    | stack′ = rebase-stack-bind-both stack′
        represented⁰ representedᵖ eqᴸ⁰ eqᴸᵖ eqᴿ⁰ eqᴿᵖ
pop-source-rebase-stack
    (rebase-stack-bind-both-star stack represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ)
    (source-rebase-bind-both-star rebase representedᵖ .represented
      .A≠★ eqᴸᵖ .eqᴸ eqᴿᵖ .eqᴿ)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-bind-both-star stack represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ)
    (source-rebase-bind-both-star rebase representedᵖ .represented
      .A≠★ eqᴸᵖ .eqᴸ eqᴿᵖ .eqᴿ)
    | stack′ = rebase-stack-bind-both-star stack′
        represented⁰ representedᵖ A≠★ eqᴸ⁰ eqᴸᵖ eqᴿ⁰ eqᴿᵖ


data SourceRebaseStackEvolution : ∀
    {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {γ⁰′ γ′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
  → SourceRebaseStack γ⁰ γ
  → SourceRebaseStack γ⁰′ γ′
  → Set where

  stack-evolution-refl : ∀ {Cᴸ Cᴿ : Ctx}
      {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {stack : SourceRebaseStack γ⁰ γ}
    → SourceRebaseStackEvolution
        {χsᴸ = R.[]} {χsᴿ = R.[]} stack stack

  stack-evolution-keep-left : ∀ {Cᴸ Cᴿ : Ctx}
      {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {stack : SourceRebaseStack γ⁰ γ}
    → SourceRebaseStackEvolution
        {χsᴸ = R.keep R.∷ R.[]} {χsᴿ = R.[]} stack stack

  stack-evolution-keep-right : ∀ {Cᴸ Cᴿ : Ctx}
      {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {stack : SourceRebaseStack γ⁰ γ}
    → SourceRebaseStackEvolution
        {χsᴸ = R.[]} {χsᴿ = R.keep R.∷ R.[]} stack stack

  stack-evolution-keep-both : ∀ {Cᴸ Cᴿ : Ctx}
      {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {stack : SourceRebaseStack γ⁰ γ}
    → SourceRebaseStackEvolution
        {χsᴸ = R.keep R.∷ R.[]}
        {χsᴿ = R.keep R.∷ R.[]} stack stack

  stack-evolution-bind-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {stack : SourceRebaseStack γ⁰ γ}
    → (A : Ty Δᴸ)
    → (eq⁰ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eq : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → SourceRebaseStackEvolution
        {χsᴸ = R.bind A R.∷ R.[]} {χsᴿ = R.[]} stack
        (rebase-stack-bind-left A stack eq⁰ eq)

  stack-evolution-bind-right : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {stack : SourceRebaseStack γ⁰ γ}
    → (fresh⁰ : RightBindFreshᶜ γ⁰ B)
    → (fresh : RightBindFreshᶜ γ B)
    → (eq⁰ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eq : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseStackEvolution
        {χsᴸ = R.[]} {χsᴿ = R.bind B R.∷ R.[]} stack
        (rebase-stack-bind-right stack fresh⁰ fresh eq⁰ eq)

  stack-evolution-bind-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {stack : SourceRebaseStack γ⁰ γ}
    → (represented⁰ : A ⊑ᵀ⟨ γ⁰ ⟩ B)
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (eqᴸ⁰ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴿ⁰ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseStackEvolution
        {χsᴸ = R.bind A R.∷ R.[]}
        {χsᴿ = R.bind B R.∷ R.[]} stack
        (rebase-stack-bind-both stack represented⁰ represented
          eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ)

  stack-evolution-bind-both-star : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {stack : SourceRebaseStack γ⁰ γ}
    → (represented⁰ : A ⊑ᵀ⟨ γ⁰ ⟩ B)
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → (A≠★ : ⇑ᵗ A ≢ ★)
    → (eqᴸ⁰ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (eqᴿ⁰ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → SourceRebaseStackEvolution
        {χsᴸ = R.bind A R.∷ R.[]}
        {χsᴿ = R.bind B R.∷ R.[]} stack
        (rebase-stack-bind-both-star stack represented⁰ represented
          A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ)

  stack-evolution-compose : ∀
      {Cᴸ Cᴿ Cᴸ¹ Cᴿ¹ Cᴸ² Cᴿ² : Ctx}
      {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ}
      {γ⁰¹ γ¹ : Cᴸ¹ ⊑ᶜ Cᴿ¹}
      {γ⁰² γ² : Cᴸ² ⊑ᶜ Cᴿ²}
      {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
      {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
      {ψsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ²)}
      {ψsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ²)}
      {θsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ²)}
      {θsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ²)}
      {stack : SourceRebaseStack γ⁰ γ}
      {stack¹ : SourceRebaseStack γ⁰¹ γ¹}
      {stack² : SourceRebaseStack γ⁰² γ²}
    → SourceRebaseStackEvolution
        {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} stack stack¹
    → SourceRebaseStackEvolution
        {χsᴸ = ψsᴸ} {χsᴿ = ψsᴿ} stack¹ stack²
    → θsᴸ ≡ χsᴸ ++χ ψsᴸ
    → θsᴿ ≡ χsᴿ ++χ ψsᴿ
    → SourceRebaseStackEvolution
        {χsᴸ = θsᴸ} {χsᴿ = θsᴿ} stack stack²


composeSourceRebaseStackEvolution : ∀
    {Cᴸ Cᴿ Cᴸ¹ Cᴿ¹ Cᴸ² Cᴿ² : Ctx}
    {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ}
    {γ⁰¹ γ¹ : Cᴸ¹ ⊑ᶜ Cᴿ¹}
    {γ⁰² γ² : Cᴸ² ⊑ᶜ Cᴿ²}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ¹)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ¹)}
    {ψsᴸ : StoreChanges (Δᵉ Cᴸ¹) (Δᵉ Cᴸ²)}
    {ψsᴿ : StoreChanges (Δᵉ Cᴿ¹) (Δᵉ Cᴿ²)}
    {stack : SourceRebaseStack γ⁰ γ}
    {stack¹ : SourceRebaseStack γ⁰¹ γ¹}
    {stack² : SourceRebaseStack γ⁰² γ²}
  → SourceRebaseStackEvolution
      {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} stack stack¹
  → SourceRebaseStackEvolution
      {χsᴸ = ψsᴸ} {χsᴿ = ψsᴿ} stack¹ stack²
  → SourceRebaseStackEvolution
      {χsᴸ = χsᴸ ++χ ψsᴸ} {χsᴿ = χsᴿ ++χ ψsᴿ} stack stack²
composeSourceRebaseStackEvolution first second =
  stack-evolution-compose first second refl refl


stack-root-evolution : ∀
    {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {γ⁰′ γ′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {stack : SourceRebaseStack γ⁰ γ}
    {stack′ : SourceRebaseStack γ⁰′ γ′}
  → SourceRebaseStackEvolution
      {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} stack stack′
  → MultiWorldEvolution {W = γ⁰} {W′ = γ⁰′} χsᴸ χsᴿ
stack-root-evolution stack-evolution-refl = evolutions-refl
stack-root-evolution stack-evolution-keep-left =
  evolutions-step-left refl evolution-keep evolutions-refl
stack-root-evolution stack-evolution-keep-right =
  evolutions-step-right refl evolution-keep evolutions-refl
stack-root-evolution stack-evolution-keep-both =
  evolutions-step-both refl refl evolution-keep evolutions-refl
stack-root-evolution (stack-evolution-bind-left A eq⁰ eq) =
  evolutions-step-left refl (evolution-bind-left eq⁰) evolutions-refl
stack-root-evolution
    (stack-evolution-bind-right fresh⁰ fresh eq⁰ eq) =
  evolutions-step-right refl
    (evolution-bind-right fresh⁰ eq⁰) evolutions-refl
stack-root-evolution
    (stack-evolution-bind-both represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  evolutions-step-both refl refl
    (evolution-bind-both represented⁰ eqᴸ⁰ eqᴿ⁰) evolutions-refl
stack-root-evolution
    (stack-evolution-bind-both-star represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  evolutions-step-both refl refl
    (evolution-bind-both-star represented⁰ A≠★ eqᴸ⁰ eqᴿ⁰)
    evolutions-refl
stack-root-evolution
    (stack-evolution-compose first second refl refl) =
  composeMultiWorldEvolution
    (stack-root-evolution first) (stack-root-evolution second)


stack-top-evolution : ∀
    {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {γ⁰′ γ′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {stack : SourceRebaseStack γ⁰ γ}
    {stack′ : SourceRebaseStack γ⁰′ γ′}
  → SourceRebaseStackEvolution
      {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} stack stack′
  → MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ χsᴿ
stack-top-evolution stack-evolution-refl = evolutions-refl
stack-top-evolution stack-evolution-keep-left =
  evolutions-step-left refl evolution-keep evolutions-refl
stack-top-evolution stack-evolution-keep-right =
  evolutions-step-right refl evolution-keep evolutions-refl
stack-top-evolution stack-evolution-keep-both =
  evolutions-step-both refl refl evolution-keep evolutions-refl
stack-top-evolution (stack-evolution-bind-left A eq⁰ eq) =
  evolutions-step-left refl (evolution-bind-left eq) evolutions-refl
stack-top-evolution
    (stack-evolution-bind-right fresh⁰ fresh eq⁰ eq) =
  evolutions-step-right refl
    (evolution-bind-right fresh eq) evolutions-refl
stack-top-evolution
    (stack-evolution-bind-both represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  evolutions-step-both refl refl
    (evolution-bind-both represented eqᴸ eqᴿ) evolutions-refl
stack-top-evolution
    (stack-evolution-bind-both-star represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  evolutions-step-both refl refl
    (evolution-bind-both-star represented A≠★ eqᴸ eqᴿ)
    evolutions-refl
stack-top-evolution
    (stack-evolution-compose first second refl refl) =
  composeMultiWorldEvolution
    (stack-top-evolution first) (stack-top-evolution second)


transport-source-rebase-stack-evolution : ∀
    {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
    {γ⁰ γ : Cᴸ ⊑ᶜ Cᴿ} {γ⁰′ γ′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
    {χsᴿ : StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
    {stack : SourceRebaseStack γ⁰ γ}
    {stack′ : SourceRebaseStack γ⁰′ γ′}
    {X : TyVar (Δᵉ Cᴸ)} {Y : TyVar (Δᵉ Cᴿ)}
  → SourceRebaseᶜ γ⁰ γ X Y
  → SourceRebaseStackEvolution
      {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} stack stack′
  → SourceRebaseᶜ γ⁰′ γ′ (applyVars χsᴸ X) (applyVars χsᴿ Y)
transport-source-rebase-stack-evolution rebase stack-evolution-refl = rebase
transport-source-rebase-stack-evolution
    rebase stack-evolution-keep-left = rebase
transport-source-rebase-stack-evolution
    rebase stack-evolution-keep-right = rebase
transport-source-rebase-stack-evolution
    rebase stack-evolution-keep-both = rebase
transport-source-rebase-stack-evolution rebase
    (stack-evolution-bind-left A eq⁰ eq) =
  source-rebase-bind-left A rebase eq⁰ eq
transport-source-rebase-stack-evolution rebase
    (stack-evolution-bind-right fresh⁰ fresh eq⁰ eq) =
  source-rebase-bind-right rebase fresh⁰ fresh eq⁰ eq
transport-source-rebase-stack-evolution rebase
    (stack-evolution-bind-both represented⁰ represented
      eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  source-rebase-bind-both rebase represented⁰ represented
    eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ
transport-source-rebase-stack-evolution rebase
    (stack-evolution-bind-both-star represented⁰ represented
      A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) =
  source-rebase-bind-both-star rebase represented⁰ represented
    A≠★ eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ
transport-source-rebase-stack-evolution {X = X} {Y = Y} rebase
    (stack-evolution-compose {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {ψsᴸ = ψsᴸ} {ψsᴿ = ψsᴿ} first second refl refl) =
  subst (λ X′ → SourceRebaseᶜ _ _ X′ (applyVars (χsᴿ ++χ ψsᴿ) Y))
    (applyVars-++ χsᴸ ψsᴸ X)
    (subst (λ Y′ → SourceRebaseᶜ _ _
        (applyVars ψsᴸ (applyVars χsᴸ X)) Y′)
      (applyVars-++ χsᴿ ψsᴿ Y)
      (transport-source-rebase-stack-evolution
        (transport-source-rebase-stack-evolution rebase first) second))

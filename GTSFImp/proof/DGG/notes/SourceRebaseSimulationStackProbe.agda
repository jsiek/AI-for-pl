{-# OPTIONS --safe #-}

module proof.DGG.notes.SourceRebaseSimulationStackProbe where

-- File Charter:
--   * Probes the smallest first-order stack of source-rebase frames needed by
--     forward simulation.
--   * Makes synchronized evolution of every world in the stack explicit, so
--     a nested reveal can push a frame and return its transported predecessor.
--   * Preserves the chronological snoc order of runtime world changes around
--     an open rebase frame; evolution does not commute a bind below a rebase.
--   * Records the remaining obstruction: applying a zero-rebase closing
--     interface at a nonempty stack.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

import TermCtx as TC
open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx; TyVar; ★; ＇_; ⇑ᵗ)
open import TyStore using (TyStore; lookupStore)
open import Imprecision using (X⊑X)
open import CastTerms using (Ctx; Term; ⟨_,_,_⟩; Δᵉ; Σᵉ)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebase using
  ( SourceRebaseᶜ
  ; source-rebase-bind-term
  ; source-rebase-count≢zero
  ; source-rebase-bind-both
  ; source-rebase-bind-both-star
  ; source-rebase-bind-left
  ; source-rebase-bind-right
  ; source-rebase-lift-both
  ; source-rebase-lift-left
  ; source-rebase-now
  )
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  ( WorldEvolution
  ; bind-ctx
  ; evolution-bind-left
  ; keep-ctx
  )
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


data SourceRebaseStack : ∀ {Γᴸ Γᴿ}
    → (root top : Γᴸ ⊑ᶜ Γᴿ)
    → Set where

  rebase-stack-root : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    → sourceRebaseCountᶜ γ ≡ 0
    → SourceRebaseStack γ γ

  rebase-stack-push : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
      {X : TyVar (Δᵉ Γᴸ)} {Y : TyVar (Δᵉ Γᴿ)}
    → SourceRebaseStack γ⁰ γ
    → (ok : PivotUpdateᵗ
        (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y))
    → (represented : (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Y)
    → SourceRebaseStack γ⁰
        (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented)

  rebase-stack-term : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    → SourceRebaseStack γ⁰ γ
    → (represented⁰ : A ⊑ᵀ⟨ γ⁰ ⟩ B)
    → (represented : A ⊑ᵀ⟨ γ ⟩ B)
    → SourceRebaseStack
        (bind-termᶜ γ⁰ represented⁰) (bind-termᶜ γ represented)

  rebase-stack-both : ∀ {Γᴸ Γᴿ}
      {γ⁰ γ : Γᴸ ⊑ᶜ Γᴿ}
    → SourceRebaseStack γ⁰ γ
    → SourceRebaseStack
        (liftBothᶜ X⊑X γ⁰) (liftBothᶜ X⊑X γ)

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
        (γ⁰ ▻ᶜ
          bind-both-changeᶜ represented⁰ eqᴸ⁰ eqᴿ⁰)
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


-- Conceal can pop only the stored direct frame.  The three protected CTI
-- scopes are stripped synchronously before the direct case is reached.
pop-source-rebase-stack : ∀ {Γᴸ Γᴿ : Ctx}
    {γ⁰ γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {X Y}
  → SourceRebaseStack γ⁰ γ
  → SourceRebaseᶜ γᵖ γ X Y
  → SourceRebaseStack γ⁰ γᵖ
pop-source-rebase-stack (rebase-stack-root no-rebase) rebase =
  ⊥-elim (source-rebase-count≢zero rebase no-rebase)
pop-source-rebase-stack
    (rebase-stack-push stack ok represented)
    (source-rebase-now .ok .represented) = stack
pop-source-rebase-stack
    (rebase-stack-term stack represented⁰ represented)
    (source-rebase-bind-term rebase represented′ .represented)
    with pop-source-rebase-stack stack rebase
pop-source-rebase-stack
    (rebase-stack-term stack represented⁰ represented)
    (source-rebase-bind-term rebase represented′ .represented)
    | stack′ = rebase-stack-term stack′ represented⁰ represented′
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


-- A runtime bind is snoc'd after the open rebase.  A world rebuilt by first
-- binding the predecessor and then adding a fresh direct rebase is a distinct
-- history, and is not the endpoint of that one-step evolution.
chronological-bind-left-evolution : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ok : PivotUpdateᵗ (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y)}
    {represented : (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Y}
    (eq : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
  → WorldEvolution
      {W = γ ▻ᶜ rebase-source-changeᶜ X Y ok represented}
      {W′ = (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented)
        ▻ᶜ bind-left-changeᶜ A eq}
      (bind-ctx eq) keep-ctx
chronological-bind-left-evolution eq = evolution-bind-left eq


no-bind-left-evolution-to-rebuilt-rebase : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ok : PivotUpdateᵗ (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y)}
    {represented : (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Y}
    {eq : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ}
    {ok′ : PivotUpdateᵗ
      (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ A eq)) (Fin.suc X)
      (toRenameⁱ (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ A eq)) Y)}
    {represented′ : (＇ Fin.suc X)
      ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ A eq ⟩ lookupStore Σᴿ Y}
  → WorldEvolution
      {W = γ ▻ᶜ rebase-source-changeᶜ X Y ok represented}
      {W′ = (γ ▻ᶜ bind-left-changeᶜ A eq)
        ▻ᶜ rebase-source-changeᶜ
          (Fin.suc X) Y ok′ represented′}
      (bind-ctx eq) keep-ctx
  → ⊥
no-bind-left-evolution-to-rebuilt-rebase ()


data SourceRebaseStackEvolution : ∀
    {Δᴸ Δᴿ Δᴸ′ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Σᴸ′ : TyStore Δᴸ′} {Σᴿ′ : TyStore Δᴿ′}
    {γ⁰ γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {γ⁰′ γ′ : ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , [] ⟩}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
  → SourceRebaseStack γ⁰ γ
  → SourceRebaseStack γ⁰′ γ′
  → Set where

  rebase-stack-evolution-root : ∀
      {Δᴸ Δᴿ Δᴸ′ Δᴿ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Σᴸ′ : TyStore Δᴸ′} {Σᴿ′ : TyStore Δᴿ′}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {γ′ : ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩}
      {χsᴸ : StoreChanges Δᴸ Δᴸ′}
      {χsᴿ : StoreChanges Δᴿ Δᴿ′}
      {zero′ : sourceRebaseCountᶜ γ′ ≡ 0}
    → (zero : sourceRebaseCountᶜ γ ≡ 0)
    → MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ χsᴿ
    → SourceRebaseStackEvolution {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
        (rebase-stack-root {γ = γ} zero)
        (rebase-stack-root {γ = γ′} zero′)

  rebase-stack-evolution-push : ∀
      {Δᴸ Δᴿ Δᴸ′ Δᴿ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Σᴸ′ : TyStore Δᴸ′} {Σᴿ′ : TyStore Δᴿ′}
      {γ⁰ γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩}
      {γ⁰′ γ′ : ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩}
      {χsᴸ : StoreChanges Δᴸ Δᴸ′}
      {χsᴿ : StoreChanges Δᴿ Δᴿ′}
      {stack : SourceRebaseStack γ⁰ γ}
      {stack′ : SourceRebaseStack γ⁰′ γ′}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {X′ : TyVar Δᴸ′} {Y′ : TyVar Δᴿ′}
      {ok : PivotUpdateᵗ
        (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y)}
      {represented : (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Y}
      {ok′ : PivotUpdateᵗ
        (ηᴸᶜ γ′) X′ (toRenameⁱ (ηᴿᶜ γ′) Y′)}
      {represented′ : (＇ X′) ⊑ᵀ⟨ γ′ ⟩ lookupStore Σᴿ′ Y′}
    → SourceRebaseStackEvolution {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
        stack stack′
    → MultiWorldEvolution
        {W = γ ▻ᶜ rebase-source-changeᶜ X Y ok represented}
        {W′ = γ′ ▻ᶜ
          rebase-source-changeᶜ X′ Y′ ok′ represented′}
        χsᴸ χsᴿ
    → SourceRebaseStackEvolution {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
        (rebase-stack-push stack ok represented)
        (rebase-stack-push stack′ ok′ represented′)


-- This is the direct generalized worker statement suggested by the stack.
-- The stack evolution returns every synchronized history, rather than only
-- the root and top histories of the one-frame worker.
SimSourceRebaseStackᵀ : Set
SimSourceRebaseStackᵀ = ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ⁰ γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {stack : SourceRebaseStack γ⁰ γ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → M —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ⁰′ ∈
      (⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
       ⟨ Δᴿ′ , Σᴿ′ , [] ⟩) ]
    Σ[ γ′ ∈
      (⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
       ⟨ Δᴿ′ , Σᴿ′ , [] ⟩) ]
    Σ[ stack′ ∈ SourceRebaseStack γ⁰′ γ′ ]
    Σ[ q ∈ applyTy χᴸ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′)
      × SourceRebaseStackEvolution
          {χsᴸ = χᴸ ∷ˢ []ˢ} {χsᴿ = χsᴿ} stack stack′
      × (γ′ ⊢² N ⊑ N′ ∶ q)

{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePrecisePairedConversionValueLemma where

-- File Charter:
--   * Catches up the target side of paired reveal and conceal conversions
--     when the source wrapper is already a value.
--   * Active target conversions remain value wrappers; identity target
--     conversions take one keep step and expose the underlying value.
--   * Returns the reduction, value, evolution, type action, and CTI evidence
--     directly, without proof parameters or a named result wrapper.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using () renaming ([] to []ᵗ)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
import Conversion as Conv
import CastTerms as CT
open import CastTerms using
  (Term; Value; RevealValue; ConcealValue; ⟨_,_,_⟩; _↑_; _↓_)
open import Reduction using
  ( StoreChanges; []; _∷_; applyTys; keep; pure-step
  ; id-reveal; id-conceal
  ; _—↠[_]_; _—→[_]⟨_⟩_; _∎[]
  )
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.ConversionPivotAlignment using
  ( GeneratorPosition; generator-absent; generator-here
  ; generator-⇒-left; generator-⇒-right; generator-⇒-both
  ; generator-∀; joinGeneratorPositions; liftGeneratorPosition
  ; revealGeneratorPosition; concealGeneratorPosition
  )
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; ηᴸᶜ; ηᴿᶜ; toRenameⁱ)
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  (MultiWorldEvolution; evolutions-refl; evolutions-step-right)


join-position-not-here : ∀ {left right}
  → joinGeneratorPositions left right ≢ generator-here
join-position-not-here {generator-here} {generator-absent} ()
join-position-not-here {generator-absent} {generator-absent} ()
join-position-not-here {generator-absent} {generator-here} ()
join-position-not-here {generator-absent} {generator-⇒-left right} ()
join-position-not-here {generator-absent} {generator-⇒-right right} ()
join-position-not-here {generator-absent}
    {generator-⇒-both right₁ right₂} ()
join-position-not-here {generator-absent} {generator-∀ right} ()
join-position-not-here {generator-here} {generator-here} ()
join-position-not-here {generator-here} {generator-⇒-left right} ()
join-position-not-here {generator-here} {generator-⇒-right right} ()
join-position-not-here {generator-here}
    {generator-⇒-both right₁ right₂} ()
join-position-not-here {generator-here} {generator-∀ right} ()
join-position-not-here {generator-⇒-left left} {generator-absent} ()
join-position-not-here {generator-⇒-left left} {generator-here} ()
join-position-not-here {generator-⇒-left left}
    {generator-⇒-left right} ()
join-position-not-here {generator-⇒-left left}
    {generator-⇒-right right} ()
join-position-not-here {generator-⇒-left left}
    {generator-⇒-both right₁ right₂} ()
join-position-not-here {generator-⇒-left left} {generator-∀ right} ()
join-position-not-here {generator-⇒-right left} {generator-absent} ()
join-position-not-here {generator-⇒-right left} {generator-here} ()
join-position-not-here {generator-⇒-right left}
    {generator-⇒-left right} ()
join-position-not-here {generator-⇒-right left}
    {generator-⇒-right right} ()
join-position-not-here {generator-⇒-right left}
    {generator-⇒-both right₁ right₂} ()
join-position-not-here {generator-⇒-right left} {generator-∀ right} ()
join-position-not-here {generator-⇒-both left₁ left₂}
    {generator-absent} ()
join-position-not-here {generator-⇒-both left₁ left₂}
    {generator-here} ()
join-position-not-here {generator-⇒-both left₁ left₂}
    {generator-⇒-left right} ()
join-position-not-here {generator-⇒-both left₁ left₂}
    {generator-⇒-right right} ()
join-position-not-here {generator-⇒-both left₁ left₂}
    {generator-⇒-both right₁ right₂} ()
join-position-not-here {generator-⇒-both left₁ left₂}
    {generator-∀ right} ()
join-position-not-here {generator-∀ left} {generator-absent} ()
join-position-not-here {generator-∀ left} {generator-here} ()
join-position-not-here {generator-∀ left} {generator-⇒-left right} ()
join-position-not-here {generator-∀ left} {generator-⇒-right right} ()
join-position-not-here {generator-∀ left}
    {generator-⇒-both right₁ right₂} ()
join-position-not-here {generator-∀ left} {generator-∀ right} ()


lift-position-not-here : ∀ {position}
  → liftGeneratorPosition position ≢ generator-here
lift-position-not-here {generator-absent} ()
lift-position-not-here {generator-here} ()
lift-position-not-here {generator-⇒-left position} ()
lift-position-not-here {generator-⇒-right position} ()
lift-position-not-here {generator-⇒-both left right} ()
lift-position-not-here {generator-∀ position} ()


paired-reveal-value-catchup : ∀ {DeltaL DeltaR : TyCtx}
    {SigmaL : TyStore DeltaL} {SigmaR : TyStore DeltaR}
    {gamma : ⟨ DeltaL , SigmaL , []ᵗ ⟩ ⊑ᶜ ⟨ DeltaR , SigmaR , []ᵗ ⟩}
    {V : Term DeltaL} {V' : Term DeltaR}
    {A B : Ty DeltaL} {A' B' : Ty DeltaR}
    {XL : TyVar DeltaL} {XR : TyVar DeltaR}
    {RL : Ty DeltaL} {RR : Ty DeltaR}
    {c : Conv↑ DeltaL A B} {c' : Conv↑ DeltaR A' B'}
    {p : A ⊑ᵀ⟨ gamma ⟩ A'}
  → (ct : SigmaL ⊢↑[ XL ⦂ RL ] c)
  → (ct' : SigmaR ⊢↑[ XR ⦂ RR ] c')
  → revealGeneratorPosition ct ≡ revealGeneratorPosition ct'
  → toRenameⁱ (ηᴸᶜ gamma) XL ≡ toRenameⁱ (ηᴿᶜ gamma) XR
  → RL ⊑ᵀ⟨ gamma ⟩ RR
  → gamma ⊢² V ⊑ V' ∶ p
  → (q : B ⊑ᵀ⟨ gamma ⟩ B')
  → RevealValue c
  → Value V'
  → Σ[ psR ∈ StoreChanges DeltaR DeltaR ]
    Σ[ W' ∈ Term DeltaR ]
      (V' ↑ c' —↠[ psR ] W')
      × Value W'
      × MultiWorldEvolution {W = gamma} {W′ = gamma} [] psR
      × (∀ T → applyTys psR T ≡ T)
      × (gamma ⊢² V ↑ c ⊑ W' ∶ q)
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-⇒ left right)
    (Conv.⊢↑-unseal member) positions aligned represented related q
    CT.fun vV' = ⊥-elim (join-position-not-here positions)
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-⇒ left right)
    ct'@(Conv.⊢↑-⇒ left' right') positions aligned represented
    related q CT.fun vV' =
  [] , V' ↑ c' , (V' ↑ c' ∎[]) , (vV' CT.↑ CT.fun) ,
    evolutions-refl , (λ T → refl) ,
    CTI.reveal⊑reveal² ct ct' positions aligned represented related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-⇒ left right)
    ct'@(Conv.⊢↑-∀ eq body) positions aligned represented related q
    CT.fun vV' =
  [] , V' ↑ c' , (V' ↑ c' ∎[]) , (vV' CT.↑ CT.all) ,
    evolutions-refl , (λ T → refl) ,
    CTI.reveal⊑reveal² ct ct' positions aligned represented related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-⇒ left right)
    (Conv.⊢↑-id-var member XL≠Y) positions aligned represented related q
    CT.fun vV' =
  keep ∷ [] , V' ,
    (V' ↑ c'
   —→[ keep ]⟨ pure-step (id-reveal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.reveal⊑-identity ct positions related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-⇒ left right)
    (Conv.⊢↑-id-base member) positions aligned represented related q
    CT.fun vV' =
  keep ∷ [] , V' ,
    (V' ↑ c'
   —→[ keep ]⟨ pure-step (id-reveal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.reveal⊑-identity ct positions related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-⇒ left right)
    (Conv.⊢↑-id-star member) positions aligned represented related q
    CT.fun vV' =
  keep ∷ [] , V' ,
    (V' ↑ c'
   —→[ keep ]⟨ pure-step (id-reveal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.reveal⊑-identity ct positions related q

paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-∀ eq body)
    (Conv.⊢↑-unseal member) positions aligned represented related q
    CT.all vV' = ⊥-elim (lift-position-not-here positions)
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-∀ eq body)
    ct'@(Conv.⊢↑-⇒ left' right') positions aligned represented related q
    CT.all vV' =
  [] , V' ↑ c' , (V' ↑ c' ∎[]) , (vV' CT.↑ CT.fun) ,
    evolutions-refl , (λ T → refl) ,
    CTI.reveal⊑reveal² ct ct' positions aligned represented related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-∀ eq body)
    ct'@(Conv.⊢↑-∀ eq' body') positions aligned represented related q
    CT.all vV' =
  [] , V' ↑ c' , (V' ↑ c' ∎[]) , (vV' CT.↑ CT.all) ,
    evolutions-refl , (λ T → refl) ,
    CTI.reveal⊑reveal² ct ct' positions aligned represented related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-∀ eq body)
    (Conv.⊢↑-id-var member XL≠Y) positions aligned represented related q
    CT.all vV' =
  keep ∷ [] , V' ,
    (V' ↑ c'
   —→[ keep ]⟨ pure-step (id-reveal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.reveal⊑-identity ct positions related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-∀ eq body)
    (Conv.⊢↑-id-base member) positions aligned represented related q
    CT.all vV' =
  keep ∷ [] , V' ,
    (V' ↑ c'
   —→[ keep ]⟨ pure-step (id-reveal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.reveal⊑-identity ct positions related q
paired-reveal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↑-∀ eq body)
    (Conv.⊢↑-id-star member) positions aligned represented related q
    CT.all vV' =
  keep ∷ [] , V' ,
    (V' ↑ c'
   —→[ keep ]⟨ pure-step (id-reveal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.reveal⊑-identity ct positions related q


paired-conceal-value-catchup : ∀ {DeltaL DeltaR : TyCtx}
    {SigmaL : TyStore DeltaL} {SigmaR : TyStore DeltaR}
    {gamma : ⟨ DeltaL , SigmaL , []ᵗ ⟩ ⊑ᶜ ⟨ DeltaR , SigmaR , []ᵗ ⟩}
    {V : Term DeltaL} {V' : Term DeltaR}
    {A B : Ty DeltaL} {A' B' : Ty DeltaR}
    {XL : TyVar DeltaL} {XR : TyVar DeltaR}
    {RL : Ty DeltaL} {RR : Ty DeltaR}
    {c : Conv↓ DeltaL A B} {c' : Conv↓ DeltaR A' B'}
    {p : A ⊑ᵀ⟨ gamma ⟩ A'}
  → (ct : SigmaL ⊢↓[ XL ⦂ RL ] c)
  → (ct' : SigmaR ⊢↓[ XR ⦂ RR ] c')
  → concealGeneratorPosition ct ≡ concealGeneratorPosition ct'
  → toRenameⁱ (ηᴸᶜ gamma) XL ≡ toRenameⁱ (ηᴿᶜ gamma) XR
  → RL ⊑ᵀ⟨ gamma ⟩ RR
  → gamma ⊢² V ⊑ V' ∶ p
  → (q : B ⊑ᵀ⟨ gamma ⟩ B')
  → ConcealValue c
  → Value V'
  → Σ[ psR ∈ StoreChanges DeltaR DeltaR ]
    Σ[ W' ∈ Term DeltaR ]
      (V' ↓ c' —↠[ psR ] W')
      × Value W'
      × MultiWorldEvolution {W = gamma} {W′ = gamma} [] psR
      × (∀ T → applyTys psR T ≡ T)
      × (gamma ⊢² V ↓ c ⊑ W' ∶ q)
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-seal member)
    ct'@(Conv.⊢↓-seal member') positions aligned represented related q
    CT.seal vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.seal) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-seal member)
    ct'@(Conv.⊢↓-⇒ left' right') positions aligned represented related q
    CT.seal vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.fun) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-seal member)
    ct'@(Conv.⊢↓-∀ eq' body') positions aligned represented related q
    CT.seal vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.all) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    (Conv.⊢↓-seal member)
    (Conv.⊢↓-id-var member' XR≠Y) () aligned represented related q
    CT.seal vV'
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    (Conv.⊢↓-seal member)
    (Conv.⊢↓-id-base member') () aligned represented related q CT.seal vV'
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    (Conv.⊢↓-seal member)
    (Conv.⊢↓-id-star member') () aligned represented related q CT.seal vV'

paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-⇒ left right)
    ct'@(Conv.⊢↓-seal member') positions aligned represented related q
    CT.fun vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.seal) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-⇒ left right)
    ct'@(Conv.⊢↓-⇒ left' right') positions aligned represented related q
    CT.fun vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.fun) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-⇒ left right)
    ct'@(Conv.⊢↓-∀ eq' body') positions aligned represented related q
    CT.fun vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.all) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-⇒ left right)
    (Conv.⊢↓-id-var member' XR≠Y) positions aligned represented related q
    CT.fun vV' =
  keep ∷ [] , V' ,
    (V' ↓ c'
   —→[ keep ]⟨ pure-step (id-conceal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.conceal⊑-identity ct positions related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-⇒ left right)
    (Conv.⊢↓-id-base member') positions aligned represented related q
    CT.fun vV' =
  keep ∷ [] , V' ,
    (V' ↓ c'
   —→[ keep ]⟨ pure-step (id-conceal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.conceal⊑-identity ct positions related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-⇒ left right)
    (Conv.⊢↓-id-star member') positions aligned represented related q
    CT.fun vV' =
  keep ∷ [] , V' ,
    (V' ↓ c'
   —→[ keep ]⟨ pure-step (id-conceal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.conceal⊑-identity ct positions related q

paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-∀ eq body)
    ct'@(Conv.⊢↓-seal member') positions aligned represented related q
    CT.all vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.seal) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-∀ eq body)
    ct'@(Conv.⊢↓-⇒ left' right') positions aligned represented related q
    CT.all vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.fun) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-∀ eq body)
    ct'@(Conv.⊢↓-∀ eq' body') positions aligned represented related q
    CT.all vV' =
  [] , V' ↓ c' , (V' ↓ c' ∎[]) , (vV' CT.↓ CT.all) ,
    evolutions-refl , (λ T → refl) ,
    CTI.conceal⊑conceal² ct ct' positions aligned represented related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-∀ eq body)
    (Conv.⊢↓-id-var member' XR≠Y) positions aligned represented related q
    CT.all vV' =
  keep ∷ [] , V' ,
    (V' ↓ c'
   —→[ keep ]⟨ pure-step (id-conceal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.conceal⊑-identity ct positions related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-∀ eq body)
    (Conv.⊢↓-id-base member') positions aligned represented related q
    CT.all vV' =
  keep ∷ [] , V' ,
    (V' ↓ c'
   —→[ keep ]⟨ pure-step (id-conceal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.conceal⊑-identity ct positions related q
paired-conceal-value-catchup {V' = V'} {c = c} {c' = c'}
    ct@(Conv.⊢↓-∀ eq body)
    (Conv.⊢↓-id-star member') positions aligned represented related q
    CT.all vV' =
  keep ∷ [] , V' ,
    (V' ↓ c'
   —→[ keep ]⟨ pure-step (id-conceal vV') ⟩
     V' ∎[]) ,
    vV' , evolutions-step-right refl evolution-keep evolutions-refl ,
    (λ T → refl) , CTI.conceal⊑-identity ct positions related q

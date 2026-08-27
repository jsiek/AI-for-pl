{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceRebaseStackProof where

-- File Charter:
--   * Assembles canonical CTI transport through balanced source-rebase-stack
--     evolution.
--   * Recurses over the complete evolution split, using the open-stack source
--     bind induction and the existing target and paired bind inductions.
--   * Handles composed evolutions by explicit term and type transport.

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym)

open import Types using (Ty)
open import CastTerms using (Term; Δᵉ)
open import Reduction using
  (StoreChanges; applyTerm; applyTerms; applyTys)
open import proof.Reduction using (_++χ_; applyTys-++)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebaseStackDef using
  ( SourceRebaseStackEvolution
  ; stack-evolution-refl
  ; stack-evolution-keep-left
  ; stack-evolution-keep-right
  ; stack-evolution-keep-both
  ; stack-evolution-bind-left
  ; stack-evolution-bind-right
  ; stack-evolution-bind-both
  ; stack-evolution-bind-both-star
  ; stack-evolution-compose
  ; stack-top-evolution
  )
open import proof.DGG.TransportSourceRebaseStackBindDef using
  (TransportSourceRebaseStackBindᵀ)
open import proof.DGG.TransportSourceRebaseStackDef using
  (TransportSourceRebaseStackᵀ)
open import proof.DGG.TransportTermImprecisionStepDef using
  ( TransportTargetBindᵀ
  ; TransportPairedBindᵀ
  ; TransportPairedStarBindᵀ
  )
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-⊑ᵀ)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; evolutions-refl
  ; multi-⊑ᵀ
  )
import proof.Imprecision as PI


applyTerms-++ : ∀ {Δ⁰ Δ¹ Δ²}
    (χs : StoreChanges Δ⁰ Δ¹)
    (ψs : StoreChanges Δ¹ Δ²) (M : Term Δ⁰)
  → applyTerms ψs (applyTerms χs M) ≡
      applyTerms (χs ++χ ψs) M
applyTerms-++ Reduction.[] ψs M = refl
applyTerms-++ (Reduction.keep Reduction.∷ χs) ψs M =
  applyTerms-++ χs ψs M
applyTerms-++ (Reduction.bind A Reduction.∷ χs) ψs M =
  applyTerms-++ χs ψs (applyTerm (Reduction.bind A) M)


retarget-CTI : ∀ {Cᴸ Cᴿ : CastTerms.Ctx} {γ : Cᴸ ⊑ᶜ Cᴿ}
    {M M′ A B} {p q : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → γ ⊢² M ⊑ M′ ∶ q
retarget-CTI {p = p} {q = q} related =
  subst (λ r → _ ⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p q) related


transport-source-type : ∀ {Cᴸ Cᴿ : CastTerms.Ctx}
    {γ : Cᴸ ⊑ᶜ Cᴿ} {M M′ B}
    {A A′ : Ty (Δᵉ Cᴸ)} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (eq : A ≡ A′)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ ⊢² M ⊑ M′ ∶ subst (λ T → T ⊑ᵀ⟨ γ ⟩ B) eq p
transport-source-type refl related = related


transport-target-type : ∀ {Cᴸ Cᴿ : CastTerms.Ctx}
    {γ : Cᴸ ⊑ᶜ Cᴿ} {M M′ A}
    {B B′ : Ty (Δᵉ Cᴿ)} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (eq : B ≡ B′)
  → γ ⊢² M ⊑ M′ ∶ p
  → γ ⊢² M ⊑ M′ ∶ subst (A ⊑ᵀ⟨ γ ⟩_) eq p
transport-target-type refl related = related


module _
    (transport-source-bind : TransportSourceRebaseStackBindᵀ)
    (transport-target-bind : TransportTargetBindᵀ)
    (transport-paired-bind : TransportPairedBindᵀ)
    (transport-paired-star-bind : TransportPairedStarBindᵀ)
  where

  transport-source-rebase-stack : TransportSourceRebaseStackᵀ
  transport-source-rebase-stack stack-evolution-refl related = related
  transport-source-rebase-stack stack-evolution-keep-left related = related
  transport-source-rebase-stack stack-evolution-keep-right related = related
  transport-source-rebase-stack stack-evolution-keep-both related = related

  transport-source-rebase-stack {stack = stack}
      (stack-evolution-bind-left A eq⁰ eq) related =
    transport-source-bind {stack = stack} eq⁰ eq related

  transport-source-rebase-stack
      (stack-evolution-bind-right fresh⁰ fresh eq⁰ eq) related =
    transport-target-bind fresh eq related

  transport-source-rebase-stack
      (stack-evolution-bind-both represented⁰ represented
        eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) related =
    transport-paired-bind represented eqᴸ eqᴿ related

  transport-source-rebase-stack
      (stack-evolution-bind-both-star represented⁰ represented A≠★
        eqᴸ⁰ eqᴸ eqᴿ⁰ eqᴿ) related =
    transport-paired-star-bind represented A≠★ eqᴸ eqᴿ related

  transport-source-rebase-stack {M = M} {M′ = M′}
      (stack-evolution-compose
        {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
        {ψsᴸ = ψsᴸ} {ψsᴿ = ψsᴿ}
        first second refl refl) {p = p} related =
    subst
      (λ N′ → _ ⊢² applyTerms (χsᴸ ++χ ψsᴸ) M
        ⊑ N′ ∶ _)
      (applyTerms-++ χsᴿ ψsᴿ M′)
      (subst
        (λ N → _ ⊢² N ⊑
          applyTerms ψsᴿ (applyTerms χsᴿ M′) ∶ _)
        (applyTerms-++ χsᴸ ψsᴸ M)
        (retarget-CTI
          (transport-target-type
            (applyTys-++ χsᴿ ψsᴿ _)
            (transport-source-type
              (applyTys-++ χsᴸ ψsᴸ _)
              (transport-source-rebase-stack second
                (transport-source-rebase-stack first related))))))

module DGGSim where

-- File Charter:
--   * States the dynamic gradual guarantee for closed extrinsic-inst
--   * `PolyUpDown` terms using a simulation-shaped proof outline.
--   * Avoids the logical-relation fundamental theorem used by
--     `DynamicGradualGuarantee.agda`.
--   * Uses the corrected imprecision orientation: `M ⊑ M′` means `M` is
--     less imprecise/more precise and `M′` is more imprecise/less precise.
--   * Works top-down: the public theorem is proved from named simulation
--     obligations, which are postulated below as the remaining proof plan.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types
open import Store using (StoreWf)
open import Imprecision
open import Terms
  using
    ( Term
    ; blame
    ; substᵗᵐ
    ; `_
    ; _∣_∣_∣_⊢_⦂_
    )
open import TermProperties using (substˣ-term)
open import TermPrecision
open import ReductionFresh
  using
    ( Value
    ; _—→_
    ; β
    ; β-up-∀
    ; β-up-↦
    ; β-down-↦
    ; id-up
    ; id-down
    ; seal-unseal
    ; tag-untag-ok
    ; tag-untag-bad
    ; β-up-；
    ; β-down-；
    ; δ-⊕
    ; blame-·₁
    ; blame-·₂
    ; blame-·α
    ; blame-up
    ; blame-down
    ; blame-⊕₁
    ; blame-⊕₂
    ; _∣_—→_∣_
    ; id-step
    ; β-Λ
    ; β-down-∀
    ; β-down-ν
    ; β-up-ν
    ; ξ-·₁
    ; ξ-·₂
    ; ξ-·α
    ; ξ-up
    ; ξ-down
    ; ξ-⊕₁
    ; ξ-⊕₂
    ; _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; multi-trans
    )

------------------------------------------------------------------------
-- Closed instances and observable outcomes
------------------------------------------------------------------------

closedTySub : Substᵗ
closedTySub X = ‵ `ℕ

close : Term → Term
close M = substᵗᵐ closedTySub (substˣ-term (λ x → ` x) M)

closeˡ : Term → Term
closeˡ = close

closeʳ : Term → Term
closeʳ = close

steps :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  ℕ
steps (_ ∎) = zero
steps (_ —→⟨ _ ⟩ M↠N) = suc (steps M↠N)

Blame : Term → Set
Blame M = ∃[ ℓ ] (M ≡ blame ℓ)

Blames : Store → Term → Set
Blames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

Converges : Store → Term → Set
Converges Σ M =
  ∃[ Σ′ ] ∃[ W ] ((Σ ∣ M —↠ Σ′ ∣ W) × (Value W ⊎ Blame W))

Diverges : Store → Term → Set
Diverges Σ M = ¬ Converges Σ M

DivergeOrBlame : Store → Term → Set
DivergeOrBlame Σ M =
  ∀ Σ′ N →
  Σ ∣ M —↠ Σ′ ∣ N →
  Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σ′ ∣ N —→ Σ″ ∣ N″))

prefix-blames :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Blames Σ′ N →
  Blames Σ M
prefix-blames M↠N (Σᵇ , ℓ , N↠blame) =
  Σᵇ , ℓ , multi-trans M↠N N↠blame

------------------------------------------------------------------------
-- Simulation proof obligations
------------------------------------------------------------------------

LeftStepResult :
  ∀ {A B : Ty} →
  SealCtx → SealCtx → Store → Store → Term → Term → A ⊑ B → Set
LeftStepResult Ψˡ Ψʳ Σˡ′ Σʳ N M′ p =
  Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ , Σˡ′ , [] ⟫ ⊢ N ⊑ N′ ⦂ p))

postulate
  initial-simulation :
    ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
    (wfΣ : StoreWf 0 Ψ Σ) →
    ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ closeˡ M ⊑ closeʳ M′ ⦂ p

  left-step-preserves-store-wf :
    ∀ {Ψ Σ Σ′ M N} →
    StoreWf 0 Ψ Σ →
    Σ ∣ M —→ Σ′ ∣ N →
    StoreWf 0 Ψ Σ′

  -- Ports the context-rebuilding part of GTLC `sim`; the recursive
  -- result is deliberately an argument so the recursion remains explicit.
  sim-left-ξ-result :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : A ⊑ B}
      {Nᵣ Mᵣ′ : Term} {C D : Ty} {q : C ⊑ D} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Σˡ ∣ M —→ Σˡ′ ∣ N →
    LeftStepResult Ψˡ Ψʳ Σˡ′ Σʳ Nᵣ Mᵣ′ q →
    LeftStepResult Ψˡ Ψʳ Σˡ′ Σʳ N M′ p

  -- GTLC `sim-beta`.
  sim-left-beta :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC `sim-beta-cast`.
  sim-left-beta-cast :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC `⊑castL-id-inversion`.
  sim-left-castL-id-inversion :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC `⊑castR-id-inversion`.
  sim-left-castR-id-inversion :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC `cast-left-⨟-val`.
  sim-left-cast-left-seq-val :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC `sim-castL-result`.
  sim-left-castL-result :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC `cast-left-?-val`.
  sim-left-cast-left-tag-val :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

  -- GTLC blame-right cases use `⊑blameR` with left typing and type precision.
  sim-left-blame-result :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p

sim-left-raw :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  M —→ N →
  LeftStepResult Ψˡ Ψʳ Σˡ Σʳ N M′ p
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(β vV) =
  sim-left-beta M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(β-up-↦ vV vW) =
  sim-left-beta-cast M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(β-down-↦ vV vW) =
  sim-left-beta-cast M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(id-up vV) =
  sim-left-castL-id-inversion M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(id-down vV) =
  sim-left-castR-id-inversion M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(β-up-； vV) =
  sim-left-cast-left-seq-val M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(β-down-； vV) =
  sim-left-castL-result M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(tag-untag-ok vV) =
  sim-left-cast-left-tag-val M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ red@(tag-untag-bad vV G≢H) =
  sim-left-blame-result M⊑M′ wfΣˡ wfΣʳ red
sim-left-raw M⊑M′ wfΣˡ wfΣʳ (β-up-∀ vV) = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ (seal-unseal vV) = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ δ-⊕ = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ blame-·₁ = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ (blame-·₂ vV) = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ blame-·α = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ blame-up = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ blame-down = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ blame-⊕₁ = {!!}
sim-left-raw M⊑M′ wfΣˡ wfΣʳ (blame-⊕₂ vV) = {!!}

sim-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : A ⊑ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  LeftStepResult Ψˡ Ψʳ Σˡ′ Σʳ N M′ p
sim-left (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₁ redL)
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
... | rec = sim-left-ξ-result (⊑· L⊑L′ M⊑M′) red rec
sim-left (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₂ vV redM)
    with sim-left M⊑M′ wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑· L⊑L′ M⊑M′) red rec
sim-left (⊑⦂∀ rel wfA wfB hT) wfΣˡ wfΣʳ red@(ξ-·α redM)
    with sim-left rel wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑⦂∀ rel wfA wfB hT) red rec
sim-left (⊑⦂∀-ν A B p rel wfA hT) wfΣˡ wfΣʳ red@(ξ-·α redM)
    with sim-left rel wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑⦂∀-ν A B p rel wfA hT) red rec
sim-left (⊑up Φ lenΦ rel hu hu′) wfΣˡ wfΣʳ red@(ξ-up redM)
    with sim-left rel wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑up Φ lenΦ rel hu hu′) red rec
sim-left (⊑upL Φ lenΦ rel hu) wfΣˡ wfΣʳ red@(ξ-up redM)
    with sim-left rel wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑upL Φ lenΦ rel hu) red rec
sim-left (⊑down Φ lenΦ rel hd hd′) wfΣˡ wfΣʳ red@(ξ-down redM)
    with sim-left rel wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑down Φ lenΦ rel hd hd′) red rec
sim-left (⊑downL Φ lenΦ rel hd) wfΣˡ wfΣʳ red@(ξ-down redM)
    with sim-left rel wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑downL Φ lenΦ rel hd) red rec
sim-left (⊑⊕ L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-⊕₁ redL)
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
... | rec = sim-left-ξ-result (⊑⊕ L⊑L′ M⊑M′) red rec
sim-left (⊑⊕ L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-⊕₂ vV redM)
    with sim-left M⊑M′ wfΣˡ wfΣʳ redM
... | rec = sim-left-ξ-result (⊑⊕ L⊑L′ M⊑M′) red rec
sim-left M⊑M′ wfΣˡ wfΣʳ (id-step red) =
  sim-left-raw M⊑M′ wfΣˡ wfΣʳ red
sim-left M⊑M′ wfΣˡ wfΣʳ β-Λ = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (β-down-∀ vV) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (β-down-ν vV) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (β-up-ν vV) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-·α redM) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-up redM) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-down redM) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₁ redL) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₂ vV redM) = {!!}

sim-left* :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : A ⊑ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —↠ Σˡ′ ∣ N →
  Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ , Σˡ′ , [] ⟫ ⊢ N ⊑ N′ ⦂ p))
sim-left* {Σʳ = Σʳ} {M′ = M′} M⊑M′ wfΣˡ wfΣʳ (M ∎) =
  wfΣˡ , Σʳ , wfΣʳ , M′ , (M′ ∎) , M⊑M′
sim-left* M⊑M′ wfΣˡ wfΣʳ (M —→⟨ M→M₁ ⟩ M₁↠N)
    with left-step-preserves-store-wf wfΣˡ M→M₁
       | sim-left M⊑M′ wfΣˡ wfΣʳ M→M₁
sim-left* M⊑M′ wfΣˡ wfΣʳ (M —→⟨ M→M₁ ⟩ M₁↠N)
  | wfΣ₁ | Σʳ₁ , wfΣʳ₁ , M′₁ , M′↠M′₁ , M₁⊑M′₁
    with sim-left* M₁⊑M′₁ wfΣ₁ wfΣʳ₁ M₁↠N
sim-left* M⊑M′ wfΣˡ wfΣʳ (M —→⟨ M→M₁ ⟩ M₁↠N)
  | wfΣ₁ | Σʳ₁ , wfΣʳ₁ , M′₁ , M′↠M′₁ , M₁⊑M′₁
  | wfΣˡ′ , Σʳ′ , wfΣʳ′ , N′ , M′₁↠N′ , N⊑N′ =
  wfΣˡ′ , Σʳ′ , wfΣʳ′ , N′ ,
  multi-trans M′↠M′₁ M′₁↠N′ , N⊑N′

postulate
  right-value-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} {p : A ⊑ B} →
    Value V →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ V ⊑ N′ ⦂ p →
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ V′ ∈ Term ]
        (Value V′ ×
         (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ V ⊑ V′ ⦂ p))

  sim-right* :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Σʳ ∣ M′ —↠ Σʳ′ ∣ N′ →
    (Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ Σˡ′ ∈ Store ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
      Σ[ N ∈ Term ]
        ((Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
         (⟪ 0 , Ψˡ , Σˡ′ , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
    ⊎ Blames Σˡ M

  left-value-catchup-or-blame :
    ∀ {Ψˡ Σˡ N V′ A B} {p : A ⊑ B} →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ N ⊑ V′ ⦂ p →
    (Σ[ Σˡ′ ∈ Store ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
      Σ[ V ∈ Term ]
        (Value V ×
         (Σˡ ∣ N —↠ Σˡ′ ∣ V) ×
         (⟪ 0 , Ψˡ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
    ⊎ Blames Σˡ N

  right-converges-implies-left-converges :
    ∀ {Ψˡ Σˡ Σʳ M M′ A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Converges Σʳ M′ →
    Converges Σˡ M

  right-diverges-implies-left-blame-or-step :
    ∀ {Ψˡ Σˡ Σʳ Σˡ′ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Diverges Σʳ M′ →
    Σˡ ∣ M —↠ Σˡ′ ∣ N →
    Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σˡ′ ∣ N —→ Σ″ ∣ N″))

------------------------------------------------------------------------
-- Dynamic gradual guarantee, via simulation
------------------------------------------------------------------------

dynamic-gradual-guarantee-part1 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     Σ[ Σʳ′ ∈ Store ]
       Σ[ V′ ∈ Term ]
         (Value V′ ×
          (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
          (⟪ 0 , Ψ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
dynamic-gradual-guarantee-part1
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p}
  wfΣ rel {Σˡ′ = Σˡ′} vV M↠V
    with sim-left* {Ψˡ = Ψ} {Ψʳ = Ψ} {Σˡ = Σ} {Σʳ = Σ}
      {A = A} {B = B} {p = p} (initial-simulation wfΣ rel)
      wfΣ wfΣ M↠V
... | wfΣˡ′ , Σʳ₁ , wfΣʳ₁ , N′ , M′↠N′ , simVN′
    with right-value-catchup {Ψˡ = Ψ} {Ψʳ = Ψ} {Σˡ = Σˡ′}
      {Σʳ = Σʳ₁} {A = A} {B = B} {p = p} vV simVN′
... | Σʳ′ , wfΣʳ′ , V′ , vV′ , N′↠V′ , V⊑V′ =
  Σʳ′ , V′ ,
  vV′ , multi-trans M′↠N′ N′↠V′ , V⊑V′

dynamic-gradual-guarantee-part2 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  Diverges Σ (closeˡ M) →
  Diverges Σ (closeʳ M′)
dynamic-gradual-guarantee-part2
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p} wfΣ rel divˡ convʳ =
  divˡ
    (right-converges-implies-left-converges {Ψˡ = Ψ}
      {Σˡ = Σ} {Σʳ = Σ} {A = A} {B = B} {p = p}
      (initial-simulation wfΣ rel)
      convʳ)

dynamic-gradual-guarantee-part3 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     (Σ[ Σˡ′ ∈ Store ]
       Σ[ V ∈ Term ]
         (Value V ×
          (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
          (⟪ 0 , Ψ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
     ⊎ Blames Σ (closeˡ M))
dynamic-gradual-guarantee-part3
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p}
  wfΣ rel {Σʳ′ = Σʳ′} vV′ M′↠V′
    with sim-right* {Ψˡ = Ψ} {Ψʳ = Ψ} {Σˡ = Σ} {Σʳ = Σ}
      {A = A} {B = B} {p = p} (initial-simulation wfΣ rel) M′↠V′
... | inj₂ M↠blame = inj₂ M↠blame
... | inj₁ (wfΣʳ′ , Σˡ₁ , wfΣˡ₁ , N , M↠N , simNV′)
    with left-value-catchup-or-blame {Ψˡ = Ψ} {Σˡ = Σˡ₁}
      {A = A} {B = B} {p = p} vV′ simNV′
... | inj₁ (Σˡ′ , wfΣˡ′ , V , vV , N↠V , V⊑V′) =
  inj₁
    (Σˡ′ , V ,
     vV , multi-trans M↠N N↠V , V⊑V′)
... | inj₂ N↠blame =
  inj₂ (prefix-blames M↠N N↠blame)

dynamic-gradual-guarantee-part4 :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  Diverges Σ (closeʳ M′) →
  DivergeOrBlame Σ (closeˡ M)
dynamic-gradual-guarantee-part4
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p} wfΣ rel divʳ Σˡ′ N M↠N =
  right-diverges-implies-left-blame-or-step {Ψˡ = Ψ}
    {Σˡ = Σ} {Σʳ = Σ} {A = A} {B = B} {p = p}
    (initial-simulation wfΣ rel)
    divʳ
    M↠N

dynamic-gradual-guarantee :
  ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  -- Part 1: a less-imprecise value run is matched by a more-imprecise one.
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     Σ[ Σʳ′ ∈ Store ]
       Σ[ V′ ∈ Term ]
         (Value V′ ×
          (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
          (⟪ 0 , Ψ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
  ×
  -- Part 2: divergence of the less-imprecise term is preserved.
  (Diverges Σ (closeˡ M) → Diverges Σ (closeʳ M′))
  ×
  -- Part 3: a more-imprecise value run is caught up by the left,
  -- or left blames.
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     (Σ[ Σˡ′ ∈ Store ]
       Σ[ V ∈ Term ]
         (Value V ×
          (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
          (⟪ 0 , Ψ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
     ⊎ Blames Σ (closeˡ M))
  ×
  -- Part 4: if the right diverges, every left reduct can still step or blames.
  (Diverges Σ (closeʳ M′) → DivergeOrBlame Σ (closeˡ M))
dynamic-gradual-guarantee wfΣ rel =
  dynamic-gradual-guarantee-part1 wfΣ rel ,
  (dynamic-gradual-guarantee-part2 wfΣ rel ,
   (dynamic-gradual-guarantee-part3 wfΣ rel ,
    dynamic-gradual-guarantee-part4 wfΣ rel))

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Store using (StoreWf)
open import Imprecision
open import Terms
  using
    ( Term
    ; blame
    ; ƛ_⇒_
    ; _·_
    ; _up_
    ; _down_
    ; substᵗᵐ
    ; `_
    ; _∣_∣_∣_⊢_⦂_
    )
open import TermProperties using (substˣ-term; _[_])
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
open import PreservationFresh
  using
    ( preservation
    ; preservation-step
    ; StepCtxShape
    ; shape-id
    ; shape-suc
    ; step-ctx-shape
    ; step-preserves-store-wf
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

postulate
  initial-simulation :
    ∀ {Ψ Σ M M′ A B} {p : A ⊑ B} →
    (wfΣ : StoreWf 0 Ψ Σ) →
    ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ closeˡ M ⊑ closeʳ M′ ⦂ p

  -- GTLC blame-right cases use `⊑blameR` with left typing and type precision.
  sim-left-blame-result :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : A ⊑ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    (Σ[ Ψˡ′ ∈ SealCtx ]
      Σ[ Σʳ′ ∈ Store ]
      Σ[ N′ ∈ Term ]
        ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
         (⟪ 0 , Ψˡ′ , Σˡ , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))

  -- GTLC `[]ᶜ-⊑` analogue.
  []-⊑ :
    ∀ {E A A′ B B′ M M′ W W′}
      {pA : A ⊑ A′} {pB : B ⊑ B′} →
    extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ pB →
    E ⊢ W ⊑ W′ ⦂ pA →
    E ⊢ M [ W ] ⊑ M′ [ W′ ] ⦂ pB

-- GTLC `sim-beta`, adapted to left-imprecision orientation.
sim-left-beta :
  ∀ {Ψ Σ V W N′ W′ A A′ A′₂ B B′}
    {pA : A ⊑ A′} {pB : B ⊑ B′} →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ V ⊑ (ƛ A′₂ ⇒ N′) ⦂ (⊑-⇒ A A′ B B′ pA pB) →
  Value V →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ W ⊑ W′ ⦂ pA →
  Value W →
  Value W′ →
  Σ[ N ∈ Term ]
    ((Σ ∣ (V · W) —↠ Σ ∣ N) ×
     (⟪ 0 , Ψ , Σ , [] ⟫ ⊢ N ⊑ (N′ [ W′ ]) ⦂ pB))
sim-left-beta {W = W} (⊑ƛ hA hA′ rel) (ƛ _ ⇒ N) W⊑W′ vW vW′ =
  (N [ W ]) ,
  (_ —→⟨ id-step (β vW) ⟩
   ((N [ W ]) ∎)) ,
  []-⊑ rel W⊑W′
sim-left-beta rel@(⊑upL Φ lenΦ rel′ hu) vV W⊑W′ vW vW′ =
  {!!}
sim-left-beta rel@(⊑downL Φ lenΦ rel′ hd) vV W⊑W′ vW vW′ =
  {!!}


sim-left-blame-store :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M N A B ℓ} {p : A ⊑ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ blame ℓ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left-blame-store rel wfΣˡ wfΣʳ red
    with step-ctx-shape red | preservation-step wfΣˡ (⊑-left-typed rel) red
sim-left-blame-store rel wfΣˡ wfΣʳ red
  | shape-id | Ψˡ′ , eqΨ , N⊢
    rewrite eqΨ =
  _ , _ , _ ,
  (_ ∎) ,
  ⊑blameR N⊢
sim-left-blame-store rel wfΣˡ wfΣʳ red
  | shape-suc | Ψˡ′ , eqΨ , N⊢ =
  Ψˡ′ , _ , _ ,
  (_ ∎) ,
  ⊑blameR N⊢

sim-left-blame-raw :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ M N A B ℓ} {p : A ⊑ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  M —→ N →
  (Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ blame ℓ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ′ , Σˡ , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left-blame-raw rel wfΣˡ wfΣʳ red =
  _ , _ , _ ,
  (_ ∎) ,
  ⊑blameR (preservation wfΣˡ (⊑-left-typed rel) red)

appL-↠ :
  ∀ {Σ Σ′ : Store} {L L′ M : Term} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L · M) —↠ Σ′ ∣ (L′ · M)
appL-↠ {M = M} (L ∎) = (L · M) ∎
appL-↠ {M = M} (L —→⟨ L→L₁ ⟩ L₁↠L′) =
  (L · M) —→⟨ ξ-·₁ L→L₁ ⟩ appL-↠ {M = M} L₁↠L′

appR-↠ :
  ∀ {Σ Σ′ : Store} {V M M′ : Term} →
  Value V →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (V · M) —↠ Σ′ ∣ (V · M′)
appR-↠ {V = V} vV (M ∎) = (V · M) ∎
appR-↠ {V = V} vV (M —→⟨ M→M₁ ⟩ M₁↠M′) =
  (V · M) —→⟨ ξ-·₂ vV M→M₁ ⟩ appR-↠ vV M₁↠M′

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

sim-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : A ⊑ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left (⊑upR Φ lenΦ rel hu′) wfΣˡ wfΣʳ red
    with sim-left rel wfΣˡ wfΣʳ red
sim-left (⊑upR Φ lenΦ rel hu′) wfΣˡ wfΣʳ red
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑downR Φ lenΦ rel hd′) wfΣˡ wfΣʳ red
    with sim-left rel wfΣˡ wfΣʳ red
sim-left (⊑downR Φ lenΦ rel hd′) wfΣˡ wfΣʳ red
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left rel@(⊑blameR hM) wfΣˡ wfΣʳ red =
  sim-left-blame-store rel wfΣˡ wfΣʳ red
sim-left (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₁ redL)
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₁ redL)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Σʳᵣ , (M′ᵣ · _) , appL-↠ M′↠M′ᵣ , ⊑· Nᵣ⊑M′ᵣ {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₂ vV redM)
    with right-value-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} vV L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₂ vV redM)
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
    with sim-left M⊑M′ wfΣˡ wfΣʳᵥ redM
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  (⊑· L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-·₂ vV redM)
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Σʳᵣ , (V′ · M′ᵣ) ,
  multi-trans (appL-↠ {M = _} L′↠V′) (appR-↠ vV′ M′↠M′ᵣ) ,
  {!!}
sim-left (⊑⦂∀ rel wfA wfB hT) wfΣˡ wfΣʳ red@(ξ-·α redM)
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left (⊑⦂∀ rel wfA wfB hT) wfΣˡ wfΣʳ red@(ξ-·α redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑⦂∀-ν A B p rel wfA hT) wfΣˡ wfΣʳ red@(ξ-·α redM)
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left (⊑⦂∀-ν A B p rel wfA hT) wfΣˡ wfΣʳ red@(ξ-·α redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑up Φ lenΦ rel hu hu′) wfΣˡ wfΣʳ red@(ξ-up redM)
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left (⊑up Φ lenΦ rel hu hu′) wfΣˡ wfΣʳ red@(ξ-up redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑upL Φ lenΦ rel hu) wfΣˡ wfΣʳ red@(ξ-up redM)
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left (⊑upL Φ lenΦ rel hu) wfΣˡ wfΣʳ red@(ξ-up redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑down Φ lenΦ rel hd hd′) wfΣˡ wfΣʳ red@(ξ-down redM)
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left (⊑down Φ lenΦ rel hd hd′) wfΣˡ wfΣʳ red@(ξ-down redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑downL Φ lenΦ rel hd) wfΣˡ wfΣʳ red@(ξ-down redM)
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left (⊑downL Φ lenΦ rel hd) wfΣˡ wfΣʳ red@(ξ-down redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑⊕ L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-⊕₁ redL)
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left (⊑⊕ L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-⊕₁ redL)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left (⊑⊕ L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-⊕₂ vV redM)
    with sim-left M⊑M′ wfΣˡ wfΣʳ redM
sim-left (⊑⊕ L⊑L′ M⊑M′) wfΣˡ wfΣʳ red@(ξ-⊕₂ vV redM)
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (id-step red) =
  {!!}
-- PolyUpDown-specific store-allocation/poly-instantiation cases.
sim-left M⊑M′ wfΣˡ wfΣʳ β-Λ = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (β-down-∀ vV) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (β-down-ν vV) = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ (β-up-ν vV) = {!!}

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
    with step-preserves-store-wf wfΣˡ (⊑-left-typed M⊑M′) M→M₁
       | sim-left M⊑M′ wfΣˡ wfΣʳ M→M₁
sim-left* M⊑M′ wfΣˡ wfΣʳ (M —→⟨ M→M₁ ⟩ M₁↠N)
  | Ψwf , wfΣ₁ | Ψ₁ , Σʳ₁ , M′₁ , M′↠M′₁ , M₁⊑M′₁ =
  {!!}

postulate
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

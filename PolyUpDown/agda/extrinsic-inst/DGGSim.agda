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

open import Data.List using ([]; _++_; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n; n≤1+n)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans)
open import Relation.Nullary using (¬_)

open import Types
open import UpDown using (WfTy-weakenˢ; cast-tag)
open import Store using (StoreWf; _⊆ˢ_)
open import ImprecisionIndexed
open import Terms
  using
    ( Term
    ; blame
    ; ƛ_⇒_
    ; _·_
    ; _⦂∀_[_]
    ; _up_
    ; _down_
    ; substᵗᵐ
    ; `_
    ; inst-⟰ᵗ-⊆ˢ
    ; wk⊑
    ; wk⊒
    ; wkΣ-term
    ; _∣_∣_∣_⊢_⦂_
    )
open import TermProperties using (substˣ-term; _[_])
open import TermImprecisionIndexed
open import ReductionFresh
  using
    ( UpValue
    ; DownValue
    ; Value
    ; tag
    ; seal
    ; _↦_
    ; ∀ᵖ
    ; ν_
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
    ; length-append-tag
    ; StepCtxShape
    ; shape-id
    ; shape-suc
    ; step-ctx-shape
    ; step-preserves-store-wf
    ; wkΨ-term-suc
    ; wkΨ-cast-tag-⊑
    ; wkΨ-cast-tag-⊒
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
    ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    (wfΣ : StoreWf 0 Ψ Σ) →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ closeˡ M ⊑ closeʳ M′ ⦂ p

  -- GTLC blame-right cases use `⊑blameR` with left typing and type precision.
  sim-left-blame-result :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    M —→ N →
    (Σ[ Ψˡ′ ∈ SealCtx ]
      Σ[ Σʳ′ ∈ Store ]
         Σ[ N′ ∈ Term ]
        ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
         (⟪ 0 , Ψˡ′ , Σˡ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))

  -- GTLC `[]ᶜ-⊑` analogue.
  []-⊑ :
    ∀ {E A A′ B B′ M M′ W W′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
    extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ pB →
    E ⊢ W ⊑ W′ ⦂ pA →
    E ⊢ M [ W ] ⊑ M′ [ W′ ] ⦂ pB

wkΣ-⊑ :
  ∀ {E Σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , TPEnv.Ψ E , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΣ-⊑ w (⊑` h) = ⊑` h
wkΣ-⊑ w (⊑ƛ hA hA′ rel) = ⊑ƛ hA hA′ (wkΣ-⊑ w rel)
wkΣ-⊑ w (⊑· relL relM) = ⊑· (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ vM vM′ wfA wfB (wkΣ-⊑ (inst-⟰ᵗ-⊆ˢ w) rel)
wkΣ-⊑ w (⊑⦂∀ rel wfA wfB hT) = ⊑⦂∀ (wkΣ-⊑ w rel) wfA wfB hT
wkΣ-⊑ w (⊑⦂∀-ν A B p rel wfA hT inst) =
  ⊑⦂∀-ν A B p (wkΣ-⊑ w rel) wfA hT inst
wkΣ-⊑ w (⊑$ {n}) = ⊑$
wkΣ-⊑ w (⊑⊕ relL relM) = ⊑⊕ (wkΣ-⊑ w relL) (wkΣ-⊑ w relM)
wkΣ-⊑ w (⊑up Φ lenΦ rel hu hu′) =
  ⊑up Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu) (wk⊑ w hu′)
wkΣ-⊑ w (⊑upL Φ lenΦ rel hu) = ⊑upL Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu)
wkΣ-⊑ w (⊑upR Φ lenΦ rel hu′) = ⊑upR Φ lenΦ (wkΣ-⊑ w rel) (wk⊑ w hu′)
wkΣ-⊑ w (⊑down Φ lenΦ rel hd hd′) =
  ⊑down Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd) (wk⊒ w hd′)
wkΣ-⊑ w (⊑downL Φ lenΦ rel hd) =
  ⊑downL Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd)
wkΣ-⊑ w (⊑downR Φ lenΦ rel hd′) =
  ⊑downR Φ lenΦ (wkΣ-⊑ w rel) (wk⊒ w hd′)
wkΣ-⊑ w (⊑blameR hM) = ⊑blameR (wkΣ-term w hM)

wkΨ-⊑-suc :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , suc (TPEnv.Ψ E) , TPEnv.store E ,
    TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΨ-⊑-suc (⊑` h) = ⊑` h
wkΨ-⊑-suc (⊑ƛ hA hA′ rel) =
  ⊑ƛ (WfTy-weakenˢ hA (n≤1+n _))
      (WfTy-weakenˢ hA′ (n≤1+n _))
      (wkΨ-⊑-suc rel)
wkΨ-⊑-suc (⊑· relL relM) = ⊑· (wkΨ-⊑-suc relL) (wkΨ-⊑-suc relM)
wkΨ-⊑-suc (⊑Λ vM vM′ wfA wfB rel) =
  ⊑Λ vM vM′
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ wfB (n≤1+n _))
    (wkΨ-⊑-suc rel)
wkΨ-⊑-suc (⊑⦂∀ rel wfA wfB hT) =
  ⊑⦂∀ (wkΨ-⊑-suc rel)
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ wfB (n≤1+n _))
    (WfTy-weakenˢ hT (n≤1+n _))
wkΨ-⊑-suc {E = E} {M = M} {M′ = M′}
    (⊑⦂∀-ν A B {T = T} p rel wfA hT inst) =
  ⊑⦂∀-ν A B p
    (wkΨ-⊑-suc rel)
    (WfTy-weakenˢ wfA (n≤1+n _))
    (WfTy-weakenˢ hT (n≤1+n _))
    inst
wkΨ-⊑-suc (⊑$ {n}) = ⊑$
wkΨ-⊑-suc (⊑⊕ relL relM) = ⊑⊕ (wkΨ-⊑-suc relL) (wkΨ-⊑-suc relM)
wkΨ-⊑-suc (⊑up Φ lenΦ rel hu hu′) =
  ⊑up
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu)
    (wkΨ-cast-tag-⊑ hu′)
wkΨ-⊑-suc (⊑upL Φ lenΦ rel hu) =
  ⊑upL
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu)
wkΨ-⊑-suc (⊑upR Φ lenΦ rel hu′) =
  ⊑upR
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊑ hu′)
wkΨ-⊑-suc (⊑down Φ lenΦ rel hd hd′) =
  ⊑down
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd)
    (wkΨ-cast-tag-⊒ hd′)
wkΨ-⊑-suc (⊑downL Φ lenΦ rel hd) =
  ⊑downL
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd)
wkΨ-⊑-suc (⊑downR Φ lenΦ rel hd′) =
  ⊑downR
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-⊑-suc rel)
    (wkΨ-cast-tag-⊒ hd′)
wkΨ-⊑-suc (⊑blameR hM) = ⊑blameR (wkΨ-term-suc hM)

wkΨ-⊑-+ :
  ∀ {E M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  (k : ℕ) →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , (k + TPEnv.Ψ E) , TPEnv.store E ,
    TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢ M ⊑ M′ ⦂ p
wkΨ-⊑-+ zero rel = rel
wkΨ-⊑-+ (suc k) rel = wkΨ-⊑-suc (wkΨ-⊑-+ k rel)

wkΨ-⊑-≤ :
  ∀ {E Ψ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Ψ E ≤ Ψ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , Ψ′ , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΨ-⊑-≤ {E} {Ψ′} Ψ≤ rel =
  subst
    (λ q →
      (⟪ TPEnv.Δ E , q , TPEnv.store E , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
        _ ⊑ _ ⦂ _)
    (trans (+-comm (Ψ′ ∸ TPEnv.Ψ E) (TPEnv.Ψ E))
           (m+[n∸m]≡n Ψ≤))
    (wkΨ-⊑-+ (Ψ′ ∸ TPEnv.Ψ E) rel)

wkΨΣ-⊑ :
  ∀ {E Ψ′ Σ′ M M′ A B} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  TPEnv.Ψ E ≤ Ψ′ →
  TPEnv.store E ⊆ˢ Σ′ →
  E ⊢ M ⊑ M′ ⦂ p →
  (⟪ TPEnv.Δ E , Ψ′ , Σ′ , TPEnv.Ξ E , TPEnv.Γ E ⟫) ⊢
    M ⊑ M′ ⦂ p
wkΨΣ-⊑ Ψ≤ w rel = wkΣ-⊑ w (wkΨ-⊑-≤ Ψ≤ rel)

-- GTLC `sim-beta`, adapted to left-imprecision orientation.
sim-left-beta :
  ∀ {Ψ Σ V W N′ W′ A A′ A′₂ B B′}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ B′} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ V ⊑ (ƛ A′₂ ⇒ N′) ⦂ (⊑ᵢ-⇒ A A′ B B′ pA pB) →
  Value V →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ W ⊑ W′ ⦂ pA →
  Value W →
  Value W′ →
  Σ[ N ∈ Term ]
    ((Σ ∣ (V · W) —↠ Σ ∣ N) ×
     (⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ N ⊑ (N′ [ W′ ]) ⦂ pB))

sim-left-beta
  {W = W}
  (⊑ƛ hA hA′ N⊑N′)
  (ƛ A ⇒ N) W⊑W′ vW vW′ =
  N [ W ] ,
  (((ƛ A ⇒ N) · W) —→⟨ id-step (β vW) ⟩ (N [ W ]) ∎) ,
  []-⊑ N⊑N′ W⊑W′
sim-left-beta
  (⊑upL Φ lenΦ rel hu)
  (_up_ vU vp) W⊑W′ vW vW′
  with vp | hu
sim-left-beta
  (⊑upL Φ lenΦ rel hu)
  (_up_ vU vp) W⊑W′ vW vW′
  | tag | ()
sim-left-beta
  (⊑upL Φ lenΦ rel hu)
  (_up_ vU vp) W⊑W′ vW vW′
  | ∀ᵖ | ()
sim-left-beta
  (⊑upL Φ lenΦ rel hu)
  (_up_ vU vp) W⊑W′ vW vW′
  | _↦_ {p = p} {q = q} | _ =
  {!!}
sim-left-beta
  (⊑downL Φ lenΦ rel hd)
  (_down_ vU vp) W⊑W′ vW vW′
  with vp | hd
sim-left-beta
  (⊑downL Φ lenΦ rel hd)
  (_down_ vU vp) W⊑W′ vW vW′
  | seal | ()
sim-left-beta
  (⊑downL Φ lenΦ rel hd)
  (_down_ vU vp) W⊑W′ vW vW′
  | ∀ᵖ | ()
sim-left-beta
  (⊑downL Φ lenΦ rel hd)
  (_down_ vU vp) W⊑W′ vW vW′
  | ν_ | ()
sim-left-beta
  (⊑downL Φ lenΦ rel hd)
  (_down_ vU vp) W⊑W′ vW vW′
  | _↦_ {p = p} {q = q} | _ =
  {!!}


sim-left-blame-store :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M N A B ℓ} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ blame ℓ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left-blame-store rel wfΣˡ wfΣʳ red
    with step-ctx-shape red | preservation-step wfΣˡ (⊑-left-typed rel) red
sim-left-blame-store rel wfΣˡ wfΣʳ red
  | shape-id | Ψˡ′ , eqΨ , N⊢
    rewrite eqΨ = {!!}
sim-left-blame-store rel wfΣˡ wfΣʳ red
  | shape-suc | Ψˡ′ , eqΨ , N⊢ =
  {!!}

sim-left-blame-raw :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ M N A B ℓ} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  M —→ N →
  (Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ blame ℓ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ′ , Σˡ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left-blame-raw rel wfΣˡ wfΣʳ red =
  {!!}

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
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    Value V →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ V ⊑ N′ ⦂ p →
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ V′ ∈ Term ]
        (Value V′ ×
         (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p))

sim-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left M⊑M′ wfΣˡ wfΣʳ red with red

-- Congruence: application operator.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑· L⊑L′ M⊑M′
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑· L⊑L′ M⊑M′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Σʳᵣ , (M′ᵣ · _) , appL-↠ M′↠M′ᵣ ,
  ⊑· Nᵣ⊑M′ᵣ {!!}

-- Congruence: application operand.
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ M⊑M′
    with right-value-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vV L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ M⊑M′
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
    with sim-left M⊑M′ wfΣˡ wfΣʳᵥ redM
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ M⊑M′
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Σʳᵣ , (V′ · M′ᵣ) ,
  multi-trans (appL-↠ {M = _} L′↠V′) (appR-↠ vV′ M′↠M′ᵣ) ,
  ⊑· {!!} Nᵣ⊑M′ᵣ

-- Congruence: type application.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·α redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·α redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀ rel wfA wfB hT
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀ rel wfA wfB hT
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀-ν A B p rel wfA hT inst =
  {!!}

-- Congruence: up casts.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-up redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-up redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑up Φ lenΦ rel hu hu′
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑up Φ lenΦ rel hu hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: down casts.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-down redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-down redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑down Φ lenΦ rel hd hd′
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑down Φ lenΦ rel hd hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downL Φ lenΦ rel hd
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downL Φ lenΦ rel hd
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: primitive operator left operand.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑⊕ L⊑L′ M⊑M′
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑⊕ L⊑L′ M⊑M′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: primitive operator right operand.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₂ vV redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₂ vV redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑⊕ L⊑L′ M⊑M′
    with sim-left M⊑M′ wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑⊕ L⊑L′ M⊑M′
  | Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Raw, non-store-allocating steps.
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step raw =
  {!!}

-- PolyUpDown-specific store-allocation/poly-instantiation cases.
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-Λ = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-down-∀ vV = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-down-ν vV = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-up-ν vV = {!!}

sim-left* :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —↠ Σˡ′ ∣ N →
  Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p))
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
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Σʳ ∣ M′ —↠ Σʳ′ ∣ N′ →
    (Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ Σˡ′ ∈ Store ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
      Σ[ N ∈ Term ]
        ((Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
         (⟪ 0 , Ψˡ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
    ⊎ Blames Σˡ M

  left-value-catchup-or-blame :
    ∀ {Ψˡ Σˡ N V′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ N ⊑ V′ ⦂ p →
    (Σ[ Σˡ′ ∈ Store ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
      Σ[ V ∈ Term ]
        (Value V ×
         (Σˡ ∣ N —↠ Σˡ′ ∣ V) ×
         (⟪ 0 , Ψˡ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
    ⊎ Blames Σˡ N

  right-converges-implies-left-converges :
    ∀ {Ψˡ Σˡ Σʳ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Converges Σʳ M′ →
    Converges Σˡ M

  right-diverges-implies-left-blame-or-step :
    ∀ {Ψˡ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Diverges Σʳ M′ →
    Σˡ ∣ M —↠ Σˡ′ ∣ N →
    Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σˡ′ ∣ N —→ Σ″ ∣ N″))

------------------------------------------------------------------------
-- Dynamic gradual guarantee, via simulation
------------------------------------------------------------------------

dynamic-gradual-guarantee-part1 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     Σ[ Σʳ′ ∈ Store ]
       Σ[ V′ ∈ Term ]
         (Value V′ ×
          (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
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
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
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
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     (Σ[ Σˡ′ ∈ Store ]
       Σ[ V ∈ Term ]
         (Value V ×
          (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
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
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
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
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  -- Part 1: a less-imprecise value run is matched by a more-imprecise one.
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     Σ[ Σʳ′ ∈ Store ]
       Σ[ V′ ∈ Term ]
         (Value V′ ×
          (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
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
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
     ⊎ Blames Σ (closeˡ M))
  ×
  -- Part 4: if the right diverges, every left reduct can still step or blames.
  (Diverges Σ (closeʳ M′) → DivergeOrBlame Σ (closeˡ M))
dynamic-gradual-guarantee wfΣ rel =
  dynamic-gradual-guarantee-part1 wfΣ rel ,
  (dynamic-gradual-guarantee-part2 wfΣ rel ,
   (dynamic-gradual-guarantee-part3 wfΣ rel ,
    dynamic-gradual-guarantee-part4 wfΣ rel))

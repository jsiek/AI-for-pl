module SimLeftLemmas where

-- File Charter:
--   * Local helper lemmas for the left-to-right simulation proof in
--   * `DGGSim.agda`.
--   * Provides the beta-family lemmas used by `sim-left`: ordinary beta,
--     left-up function casts, and left-down function casts.
--   * Keeps the catchup and substitution proof obligations owned by these
--     lemmas next to the lemmas that use them.

open import Data.List using ([]; _∷_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Types
open import UpDown using (Up; Down; wt-↦; WfTy-weakenˢ)
open import Store using (StoreWf)
open import ImprecisionIndexed
open import Terms using (Term; ƛ_⇒_; _·_; _⦂∀_[_]; _up_; _down_)
open import TermProperties using (_[_])
open import TermImprecisionIndexed
open import ReductionFresh

postulate
  -- GTLC `[]ᶜ-⊑` analogue.
  []-⊑ :
    ∀ {E A A′ B B′ M M′ W W′}
      {pA : TPEnv.Ξ E ⊢ A ⊑ᵢ A′} {pB : TPEnv.Ξ E ⊢ B ⊑ᵢ B′} →
    extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ pB →
    E ⊢ W ⊑ W′ ⦂ pA →
    E ⊢ M [ W ] ⊑ M′ [ W′ ] ⦂ pB

  left-value-right-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    Value V →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ V ⊑ N′ ⦂ p →
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ V′ ∈ Term ]
        (Value V′ ×
         (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p))

--------------------------------------------------------------------------------
-- GTLC `sim-beta`, adapted to imprecision orientation.

sim-left-beta :
  ∀ {Ψ Σˡ Σʳ V′ W W′ N A A′ A₂ B B′}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ B′} →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢
    (ƛ A₂ ⇒ N) ⊑ V′ ⦂ (⊑ᵢ-⇒ A A′ B B′ pA pB) →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ W ⊑ W′ ⦂ pA →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ N [ W ] ⊑ N′ ⦂ pB))
sim-left-beta
  {Σʳ = Σʳ} {W′ = W′}
  (⊑ƛ hA hA′ rel) (ƛ A′ ⇒ N′) W⊑W′ vW vW′ =
  Σʳ , N′ [ W′ ] ,
  (((ƛ A′ ⇒ N′) · W′) —→⟨ id-step (β vW′) ⟩
   (N′ [ W′ ]) ∎) ,
  []-⊑ rel W⊑W′
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑downR Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Σʳ = Σʳᵃ} rel vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR Φ lenΦ N[W]⊑N′ hq
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  (_down_ vV′ dv′)
  W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑upR Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  (_down_ vV′ dv′)
  W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Σʳ = Σʳᵃ} rel vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  (_down_ vV′ dv′)
  W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR Φ lenΦ N[W]⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `up` function casts.
sim-left-beta-up :
  ∀ {Ψ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ B′}
    {p : Down} {q : Up} →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢
    (V up (Up._↦_ p q)) ⊑ V′ ⦂ (⊑ᵢ-⇒ A A′ B B′ pA pB) →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ W ⊑ W′ ⦂ pA →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢
          ((V · (W down p)) up q) ⊑ N′ ⦂ pB))
sim-left-beta-up
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑upL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑upL Φ lenΦ (⊑· rel (⊑downL Φ lenΦ W⊑W′ hp)) hq
sim-left-beta-up
  {Σʳ = Σʳ} {W′ = W′}
  (⊑up {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-up-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑up Φ lenΦ (⊑· rel (⊑down Φ lenΦ W⊑W′ hp hp′)) hq hq′
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑downR Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR Φ lenΦ N⊑N′ hq
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑upR Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `down` function casts.
sim-left-beta-down :
  ∀ {Ψ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ B′}
    {p : Up} {q : Down} →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢
    (V down (Down._↦_ p q)) ⊑ V′ ⦂ (⊑ᵢ-⇒ A A′ B B′ pA pB) →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ W ⊑ W′ ⦂ pA →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢
          ((V · (W up p)) down q) ⊑ N′ ⦂ pB))
sim-left-beta-down
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑downL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑downL Φ lenΦ (⊑· rel (⊑upL Φ lenΦ W⊑W′ hp)) hq
sim-left-beta-down
  {Σʳ = Σʳ} {W′ = W′}
  (⊑down {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-down-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑down Φ lenΦ (⊑· rel (⊑up Φ lenΦ W⊑W′ hp hp′)) hq hq′
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑downR Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ
           vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR Φ lenΦ N⊑N′ hq
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑upR Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ
           vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-left` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-left-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `DGGSim.agda` hole lines it supports.

-- Worker W01 helper slot

-- Worker W02 helper slot

-- Worker W03 helper slot

-- Worker W04 helper slot

-- Worker W05 helper slot

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Supports DGGSim.agda H10, the `ξ-·α` / `⊑⦂∀-ν` branch.
sim-left-w10-tyappν-cong :
  ∀ {Ψ Ψ′ : SealCtx} {Σ : Store} {M M′ A B T}
    {p : (ν-bound ∷ []) ⊢ A ⊑ᵢ ⇑ᵗ B}
    {pT : [] ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  Ψ ≤ Ψ′ →
  ⟪ 0 , Ψ′ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ (⊑ᵢ-ν A B p) →
  WfTy 1 Ψ A →
  (hT : WfTy 0 Ψ T) →
  νClosedInstᵢ p pT →
  ⟪ 0 , Ψ′ , Σ , [] , [] ⟫ ⊢ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ pT
sim-left-w10-tyappν-cong Ψ≤ rel wfA hT inst =
  ⊑⦂∀-ν _ _ _ rel (WfTy-weakenˢ wfA Ψ≤)
    (WfTy-weakenˢ hT Ψ≤) inst

-- Worker W11 helper slot

-- Worker W12 helper slot

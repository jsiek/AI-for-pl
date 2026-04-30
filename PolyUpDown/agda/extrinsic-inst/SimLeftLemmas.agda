module SimLeftLemmas where

-- File Charter:
--   * Local helper lemmas for the left-to-right simulation proof in
--   * `DGGSim.agda`.
--   * Provides the beta-family lemmas used by `sim-left`: ordinary beta,
--     left-up function casts, and left-down function casts.
--   * Keeps the catchup and substitution proof obligations owned by these
--     lemmas next to the lemmas that use them.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; trans)

open import Types
open import UpDown
  using (Up; Down; CastPerm; cast-tag; wt-↦; _∣_∣_∣_⊢_⦂_⊑_)
open import Store using (StoreWf; _⊆ˢ_)
open import ImprecisionIndexed
open import Terms using (Term; ƛ_⇒_; _·_; _up_; _down_; wk⊑)
open import TermProperties using (_[_])
open import TermImprecisionIndexed
open import ReductionFresh
open import PreservationFresh using (length-append-tag; wkΨ-cast-tag-⊑)

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

-- Supports DGGSim.agda H13.
sim-left-w03-wk-up-casts-+ :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B A′ B′ : Ty}{u u′ : Up} →
  (k : ℕ) →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     ((Δ ∣ (k + Ψ) ∣ Σ ∣ Φ′ ⊢ u ⦂ A ⊑ B) ×
      (Δ ∣ (k + Ψ) ∣ Σ ∣ Φ′ ⊢ u′ ⦂ A′ ⊑ B′)))
sim-left-w03-wk-up-casts-+ zero lenΦ hu hu′ = _ , lenΦ , hu , hu′
sim-left-w03-wk-up-casts-+ (suc k) lenΦ hu hu′
    with sim-left-w03-wk-up-casts-+ k lenΦ hu hu′
sim-left-w03-wk-up-casts-+ (suc k) lenΦ hu hu′
  | Φ′ , lenΦ′ , huᵣ , hu′ᵣ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊑ huᵣ ,
  wkΨ-cast-tag-⊑ hu′ᵣ

sim-left-w03-wk-up-casts-≤ :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Φ : List CastPerm}
    {A B A′ B′ : Ty}{u u′ : Up} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     ((Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ u ⦂ A ⊑ B) ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ u′ ⦂ A′ ⊑ B′)))
sim-left-w03-wk-up-casts-≤ {Δ} {Ψ} {Ψ′} {Σ} {Σ′}
  {A = A} {B = B} {A′ = A′} {B′ = B′} {u = u} {u′ = u′}
  Ψ≤Ψ′ Σ≤Σ′ lenΦ hu hu′
    with sim-left-w03-wk-up-casts-+ (Ψ′ ∸ Ψ) lenΦ hu hu′
sim-left-w03-wk-up-casts-≤ {Δ} {Ψ} {Ψ′} {Σ} {Σ′} {Φ}
  {A = A} {B = B} {A′ = A′} {B′ = B′} {u = u} {u′ = u′}
  Ψ≤Ψ′ Σ≤Σ′ lenΦ hu hu′
  | Φ′ , lenΦ′ , huᵣ , hu′ᵣ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ u ⦂ A ⊑ B) eq (wk⊑ Σ≤Σ′ huᵣ) ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ u′ ⦂ A′ ⊑ B′) eq
    (wk⊑ Σ≤Σ′ hu′ᵣ)

-- Worker W04 helper slot

postulate
  -- Supports DGGSim.agda H33.
  sim-left-w04-seal-unseal :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B}
      {pᵢ : [] ⊢ A ⊑ᵢ B}
      {p : Down} {q : Up} {α : Seal} →
    Value V →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢
      ((V down (UpDown.seal p α)) up (UpDown.unseal α q)) ⊑
        M′ ⦂ pᵢ →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Σ[ Ψˡ″ ∈ SealCtx ]
      Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
      Σ[ Σʳ′ ∈ Store ]
      Σ[ N′ ∈ Term ]
        ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
         (⟪ 0 , Ψˡ″ , Σˡ , [] , [] ⟫ ⊢
            ((V down p) up q) ⊑ N′ ⦂ pᵢ))

-- Worker W05 helper slot

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot

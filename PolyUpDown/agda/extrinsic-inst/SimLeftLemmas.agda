module SimLeftLemmas where

-- File Charter:
--   * Local helper lemmas for the left-to-right simulation proof in
--   * `DGGSim.agda`.
--   * Provides the beta-family lemmas used by `sim-left`: ordinary beta,
--     left-up function casts, and left-down function casts.
--   * Keeps the catchup and substitution proof obligations owned by these
--     lemmas next to the lemmas that use them.

open import Data.List using ([]; List; length; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans)

open import Types
open import UpDown using
  ( Up
  ; Down
  ; CastPerm
  ; wt-↦
  ; cast-tag
  ; _∣_∣_∣_⊢_⦂_⊒_
  )
open import Store using (StoreWf; _⊆ˢ_)
open import ImprecisionIndexed
open import Terms using (Term; ƛ_⇒_; _·_; _⦂∀_[_]; _up_; _down_; wk⊒)
open import TermProperties using (_[_])
open import TermImprecisionIndexed
open import ReductionFresh
open import PreservationFresh using (length-append-tag; wkΨ-cast-tag-⊒)

postulate
  left-value-right-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} →
    Value V →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ N′ ⦂ A ⊑ B →
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ V′ ∈ Term ]
        (Value V′ ×
         (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ B))

--------------------------------------------------------------------------------
-- GTLC `sim-beta`, adapted to imprecision orientation.

sim-left-beta :
  ∀ {Ψ Σˡ Σʳ V′ W W′ N A A′ A₂ B B′} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (ƛ A₂ ⇒ N) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ N [ W ] ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta
  {Σʳ = Σʳ} {W′ = W′}
  (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel)
  (ƛ A′ ⇒ N′) W⊑W′ vW vW′ =
  Σʳ , N′ [ W′ ] ,
  (((ƛ A′ ⇒ N′) · W′) —→⟨ id-step (β vW′) ⟩
   (N′ [ W′ ]) ∎) ,
  []-⊑ {pA = pA} {pB = pB} rel W⊑W′
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Σʳ = Σʳᵃ} rel vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N[W]⊑N′} {pB = pCod′}
    Φ lenΦ N[W]⊑N′ hq
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  (_down_ vV′ dv′)
  W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  (_down_ vV′ dv′)
  W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Σʳ = Σʳᵃ} rel vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  (_down_ vV′ dv′)
  W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N[W]⊑N′} {pB = pCod′}
    Φ lenΦ N[W]⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `up` function casts.
sim-left-beta-up :
  ∀ {Ψ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {p : Down} {q : Up} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (V up (Up._↦_ p q)) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V · (W down p)) up q) ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta-up
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑upL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑upL {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑downL {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp))
    hq
sim-left-beta-up
  {Σʳ = Σʳ} {W′ = W′}
  (⊑up {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-up-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑up {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑down {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp hp′))
    hq hq′
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `down` function casts.
sim-left-beta-down :
  ∀ {Ψ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {p : Up} {q : Down} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (V down (Down._↦_ p q)) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V · (W up p)) down q) ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta-down
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑downL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑downL {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑upL {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp))
    hq
sim-left-beta-down
  {Σʳ = Σʳ} {W′ = W′}
  (⊑down {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-down-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑down {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑up {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp hp′))
    hq hq′
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ
           vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Σʳ = Σʳᵃ} rel vV vV′ W⊑W′ᵥ
           vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq

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

-- Supports DGGSim.agda H42 (line 528): eliminate a left identity-down cast,
-- commuting through right-only casts.
sim-left-w03-id-down :
  ∀ {Ψ Σˡ Σʳ V M′ C A B} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ (V down Down.id C) ⊑ M′ ⦂ A ⊑ B →
  Σ[ N′ ∈ Term ]
    ((Σʳ ∣ M′ —↠ Σʳ ∣ N′) ×
     (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ N′ ⦂ A ⊑ B))
sim-left-w03-id-down (⊑upR {pB = pB} Φ lenΦ rel hu′)
    with sim-left-w03-id-down rel
sim-left-w03-id-down (⊑upR {pB = pB} Φ lenΦ rel hu′)
  | N′ , M′↠N′ , V⊑N′ =
  N′ up _ , up-↠ M′↠N′ ,
  ⊑upR {pA = ⊑-type-imprecision V⊑N′} {pB = pB}
    Φ lenΦ V⊑N′ hu′
sim-left-w03-id-down (⊑down {pB = pB} Φ lenΦ rel (UpDown.wt-id wfA) hd′) =
  _ , (_ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd′
sim-left-w03-id-down (⊑downL Φ lenΦ rel (UpDown.wt-id wfA)) =
  _ , (_ ∎) , rel
sim-left-w03-id-down (⊑downR {pB = pB} Φ lenΦ rel hd′)
    with sim-left-w03-id-down rel
sim-left-w03-id-down (⊑downR {pB = pB} Φ lenΦ rel hd′)
  | N′ , M′↠N′ , V⊑N′ =
  N′ down _ , down-↠ M′↠N′ ,
  ⊑downR {pA = ⊑-type-imprecision V⊑N′} {pB = pB}
    Φ lenΦ V⊑N′ hd′

-- Worker W04 helper slot

-- Worker W05 helper slot

postulate
  -- Supports SimLeft.agda H28: eliminate a left seal/unseal redex,
  -- commuting through right-only casts.
  sim-left-w05-seal-unseal :
    ∀ {Ψ Σˡ Σʳ V M′ A B}
      {d : Down} {u : Up} {α : Seal} →
    Value V →
    ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
      ((V down (UpDown.seal d α)) up (UpDown.unseal α u)) ⊑ M′ ⦂ A ⊑ B →
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V down d) up u) ⊑ N′ ⦂ A ⊑ B))

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

postulate
  -- Supports SimLeft.agda H41: left `β-up-ν` allocation step.
  sim-left-w09-H41 :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ V M′ N A B} {u : Up} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
      (V up (UpDown.ν u)) ⊑ M′ ⦂ A ⊑ B →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Σˡ ∣ (V up (UpDown.ν u)) —→ Σˡ′ ∣ N →
    Value V →
    (Σ[ Ψˡ″ ∈ SealCtx ]
      Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
      Σ[ Σʳ′ ∈ Store ]
      Σ[ N′ ∈ Term ]
        ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
         (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] , plain-[] , refl ⟫ ⊢ N ⊑ N′ ⦂ A ⊑ B)))

-- Supports DGGSim.agda H09 (line 215): lift right multi-steps through
-- type application.
sim-left-w09-tyapp-↠ :
  ∀ {Σ Σ′ L L′ B T} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L ⦂∀ B [ T ]) —↠ Σ′ ∣ (L′ ⦂∀ B [ T ])
sim-left-w09-tyapp-↠ (L ∎) = (L ⦂∀ _ [ _ ]) ∎
sim-left-w09-tyapp-↠ (L —→⟨ L→M ⟩ M↠N) =
  (L ⦂∀ _ [ _ ]) —→⟨ ξ-·α L→M ⟩ sim-left-w09-tyapp-↠ M↠N

-- Supports DGGSim.agda H17 (line 275): weaken both down-cast typings
-- through the same seal-context extension and store growth.
sim-left-w09-down-casts-+ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}
    {d d′ : Down} →
  (k : ℕ) →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     ((Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) ×
      (Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)))
sim-left-w09-down-casts-+ zero w lenΦ hd hd′ =
  _ , lenΦ , wk⊒ w hd , wk⊒ w hd′
sim-left-w09-down-casts-+ (suc k) w lenΦ hd hd′
    with sim-left-w09-down-casts-+ k w lenΦ hd hd′
sim-left-w09-down-casts-+ (suc k) w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊒ hdᵣ ,
  wkΨ-cast-tag-⊒ hdᵣ′

sim-left-w09-down-casts-≤ :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}
    {d d′ : Down} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     ((Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)))
sim-left-w09-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
    with sim-left-w09-down-casts-+ (Ψ′ ∸ Ψ) w lenΦ hd hd′
sim-left-w09-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) eq hdᵣ ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′) eq hdᵣ′

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot

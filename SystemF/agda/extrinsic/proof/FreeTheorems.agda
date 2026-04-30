{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.proof.FreeTheorems where

-- File Charter:
--   * Ports the intrinsic free-theorem statements to the extrinsic setting.
--   * Reuses the extrinsic logical relation to state relation witnesses.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to substEq)
open import Data.List using ([])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import extrinsic.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

open import extrinsic.Types
open import extrinsic.Terms
open import extrinsic.TermSubst using (sub-id)
open import extrinsic.Reduction
open import extrinsic.Preservation using (closed-typing-wf)
open import extrinsic.TypeTermSubst using (substᵀ-id-emptyΔ)
open import extrinsic.LogicalRelation
open import extrinsic.Parametricity

--------------------------------------------------------------------------------
-- Free theorem (identity)
--------------------------------------------------------------------------------

-- R = {(V, V)}
idR : ∀ {A} → (V : Term) → Rel A A
idR V V′ W′ _ _ _ _ = V ≡ V′ × V ≡ W′

free-theorem-id : ∀ {A : Ty}
  → (M V : Term)
  → 0 ∣ [] ⊢ M ⦂ `∀ (` 0 ⇒ ` 0)
  → 0 ∣ [] ⊢ V ⦂ A
  → Value V
    ------------------------
  → ((M ·[ A ]) · V) —↠ V
free-theorem-id {A} M X ⊢M ⊢X vX
  with fundamental M ⊢M ∅ρ ∅γ 𝒢-∅
... | ⟨ _ , ⟨ _ , ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ _ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with (proj₂ (proj₂ ∀-rel)) A A (closed-typing-wf ⊢X) (closed-typing-wf ⊢X) (idR {A = A} X)
... | ⟨ _ , ⟨ _ , ⟨ .(ƛ[ _ ] L₁) , ⟨ .(ƛ[ _ ] L₂) , ⟨ vLam {N = L₁} , ⟨ vLam {N = L₂} , ⟨ N₁—↠ƛL₁ , ⟨ _ , arg-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with (proj₂ (proj₂ arg-rel)) vX vX ⟨ ⊢X , ⟨ ⊢X , ⟨ refl , refl ⟩ ⟩ ⟩
... | ⟨ _ , ⟨ _ , res ⟩ ⟩
  with res
... | ⟨ V′ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ L₁X—↠V′ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ X≡V′ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = red
  where
  M-sub : substᵀ (left ∅ρ) (subst id M) ≡ M
  M-sub =
    trans
      (cong (substᵀ (left ∅ρ)) (sub-id M))
      (substᵀ-id-emptyΔ ⊢M)

  M·[]—↠N₁[A] : (substᵀ (left ∅ρ) (subst id M) ·[ A ]) —↠ (N₁ [ A ]ᵀ)
  M·[]—↠N₁[A] =
      (substᵀ (left ∅ρ) (subst id M) ·[ A ])
    —↠⟨ ·[]-↠ M₁—↠ΛN₁ ⟩
      ((Λ N₁) ·[ A ])
    —↠⟨ β-Λ-↠ {A = A} ⟩
      N₁ [ A ]ᵀ
    ∎

  M·[]—↠ƛL₁ : (substᵀ (left ∅ρ) (subst id M) ·[ A ]) —↠ (ƛ[ _ ] L₁)
  M·[]—↠ƛL₁ =
      (substᵀ (left ∅ρ) (subst id M) ·[ A ])
    —↠⟨ M·[]—↠N₁[A] ⟩
      N₁ [ A ]ᵀ
    —↠⟨ N₁—↠ƛL₁ ⟩
      (ƛ[ _ ] L₁)
    ∎

  M·[]·X—↠L₁X : ((substᵀ (left ∅ρ) (subst id M) ·[ A ]) · X) —↠ (L₁ [ X ])
  M·[]·X—↠L₁X =
      ((substᵀ (left ∅ρ) (subst id M) ·[ A ]) · X)
    —↠⟨ app-↠ M·[]—↠ƛL₁ vLam (X ∎) ⟩
      ((ƛ[ _ ] L₁) · X)
    —↠⟨ β-ƛ-↠ vX ⟩
      (L₁ [ X ])
    ∎

  red′ : ((substᵀ (left ∅ρ) (subst id M) ·[ A ]) · X) —↠ X
  red′ = substEq (((substᵀ (left ∅ρ) (subst id M) ·[ A ]) · X) —↠_)
    (sym X≡V′)
    ( ((substᵀ (left ∅ρ) (subst id M) ·[ A ]) · X)
    —↠⟨ M·[]·X—↠L₁X ⟩
      (L₁ [ X ])
    —↠⟨ L₁X—↠V′ ⟩
      V′
    ∎ )

  red : ((M ·[ A ]) · X) —↠ X
  red = substEq (λ Tm → ((Tm ·[ A ]) · X) —↠ X) M-sub red′

--------------------------------------------------------------------------------
-- Free theorem (representation independence)
--------------------------------------------------------------------------------

neg : Term
neg = ƛ[ `Bool ] (`if_then_else (` 0) `false `true)

flip : Term
flip = ƛ[ `ℕ ] (case_[zero⇒_|suc⇒_] (` 0) (`suc `zero) `zero)

-- R = {(true, 1), (false, 0)}
R : Rel `Bool `ℕ
R `true (`suc `zero) vTrue (vSuc vZero) ⊢V ⊢W = ⊤
R `false `zero vFalse vZero ⊢V ⊢W = ⊤
R _ _ _ _ ⊢V ⊢W = ⊥

neg-flip-related : 𝒱 (` 0 ⇒ ` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) neg flip vLam vLam
neg-flip-related = ⟨ ⊢neg , ⟨ ⊢flip , body ⟩ ⟩
  where
  ⊢neg : 0 ∣ [] ⊢ neg ⦂ substᵗ (left (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩)) (` 0 ⇒ ` 0)
  ⊢neg = ⊢ƛ wf`Bool (⊢if (⊢` Z) ⊢false ⊢true)

  ⊢flip : 0 ∣ [] ⊢ flip ⦂ substᵗ (right (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩)) (` 0 ⇒ ` 0)
  ⊢flip = ⊢ƛ wf`ℕ (⊢case (⊢` Z) (⊢suc ⊢zero) ⊢zero)

  body : ∀ {V W} (v : Value V) (w : Value W)
    → 𝒱 (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) V W v w
    → ℰ (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩)
        ((`if_then_else (` 0) `false `true) [ V ])
        ((case_[zero⇒_|suc⇒_] (` 0) (`suc `zero) `zero) [ W ])
  body {V = `true} {W = `zero} vTrue vZero ()
  body {V = `true} {W = `suc `zero} vTrue (vSuc vZero) ⟨ _ , ⟨ _ , tt ⟩ ⟩ =
    ⟨ ⊢L
    , ⟨ ⊢R
      , ⟨ `false
        , ⟨ `zero
          , ⟨ vFalse
            , ⟨ vZero
              , ⟨ redL
                , ⟨ redR
                  , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    ⊢L : 0 ∣ [] ⊢ (`if_then_else `true `false `true) ⦂ `Bool
    ⊢L = ⊢if ⊢true ⊢false ⊢true

    ⊢R : 0 ∣ [] ⊢ (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) ⦂ `ℕ
    ⊢R = ⊢case (⊢suc ⊢zero) (⊢suc ⊢zero) ⊢zero

    redL : (`if_then_else `true `false `true) —↠ `false
    redL = (`if_then_else `true `false `true) —→⟨ β-true ⟩ (`false ∎)

    redR : (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) —↠ `zero
    redR = (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc vZero ⟩ (`zero ∎)

    rel : 𝒱 (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) `false `zero vFalse vZero
    rel = ⟨ ⊢false , ⟨ ⊢zero , tt ⟩ ⟩
  body {V = `true} {W = `suc (`suc W)} vTrue (vSuc (vSuc w)) ()
  body {V = `false} {W = `zero} vFalse vZero ⟨ _ , ⟨ _ , tt ⟩ ⟩ =
    ⟨ ⊢L
    , ⟨ ⊢R
      , ⟨ `true
        , ⟨ `suc `zero
          , ⟨ vTrue
            , ⟨ vSuc vZero
              , ⟨ redL
                , ⟨ redR
                  , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    ⊢L : 0 ∣ [] ⊢ (`if_then_else `false `false `true) ⦂ `Bool
    ⊢L = ⊢if ⊢false ⊢false ⊢true

    ⊢R : 0 ∣ [] ⊢ (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) ⦂ `ℕ
    ⊢R = ⊢case ⊢zero (⊢suc ⊢zero) ⊢zero

    redL : (`if_then_else `false `false `true) —↠ `true
    redL = (`if_then_else `false `false `true) —→⟨ β-false ⟩ (`true ∎)

    redR : (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) —↠ (`suc `zero)
    redR = (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎)

    rel : 𝒱 (` 0) (∅ρ ,⟨ `Bool , `ℕ , wf`Bool , wf`ℕ , R ⟩) `true (`suc `zero) vTrue (vSuc vZero)
    rel = ⟨ ⊢true , ⟨ ⊢suc ⊢zero , tt ⟩ ⟩
  body {V = `false} {W = `suc W} vFalse (vSuc w) ()

-- If 0 ⊢ [] ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
free-theorem-rep :
  ∀ (M : Term)
  → 0 ∣ [] ⊢ M ⦂ `∀ (` 0 ⇒ (` 0 ⇒ ` 0) ⇒ ` 0)
    ------------------------------------------------------
  → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
        (((M ·[ `Bool ]) · `true)        · neg  —↠ V)
      × (((M ·[ `ℕ ]) · (`suc `zero)) · flip —↠ W)
      × (∃[ ⊢V ] ∃[ ⊢W ] R V W v w ⊢V ⊢W)
free-theorem-rep M ⊢M
  with fundamental M ⊢M ∅ρ ∅γ 𝒢-∅
... | ⟨ _ , ⟨ _ , ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ M₂—↠ΛN₂ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with (proj₂ (proj₂ ∀-rel)) `Bool `ℕ wf`Bool wf`ℕ R
... | ⟨ _ , ⟨ _ , ⟨ .(ƛ[ _ ] L₁) , ⟨ .(ƛ[ _ ] L₂) , ⟨ vLam {N = L₁} , ⟨ vLam {N = L₂} , ⟨ N₁—↠ƛL₁ , ⟨ N₂—↠ƛL₂ , arg₁-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with (proj₂ (proj₂ arg₁-rel)) vTrue (vSuc vZero) ⟨ ⊢true , ⟨ ⊢suc ⊢zero , tt ⟩ ⟩
... | ⟨ _ , ⟨ _ , ⟨ .(ƛ[ _ ] K₁) , ⟨ .(ƛ[ _ ] K₂) , ⟨ vLam {N = K₁} , ⟨ vLam {N = K₂} , ⟨ L₁true—↠ƛK₁ , ⟨ L₂suc0—↠ƛK₂ , arg₂-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with (proj₂ (proj₂ arg₂-rel)) vLam vLam neg-flip-related
... | ⟨ _ , ⟨ _ , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ K₁neg—↠V , ⟨ K₂flip—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ left-red , ⟨ right-red , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  M-sub-left : substᵀ (left ∅ρ) (subst id M) ≡ M
  M-sub-left =
    trans
      (cong (substᵀ (left ∅ρ)) (sub-id M))
      (substᵀ-id-emptyΔ ⊢M)

  M-sub-right : substᵀ (right ∅ρ) (subst id M) ≡ M
  M-sub-right =
    trans
      (cong (substᵀ (right ∅ρ)) (sub-id M))
      (substᵀ-id-emptyΔ ⊢M)

  M·[]—↠N₁[Bool] : (substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) —↠ (N₁ [ `Bool ]ᵀ)
  M·[]—↠N₁[Bool] =
      (substᵀ (left ∅ρ) (subst id M) ·[ `Bool ])
    —↠⟨ ·[]-↠ M₁—↠ΛN₁ ⟩
      ((Λ N₁) ·[ `Bool ])
    —↠⟨ β-Λ-↠ {A = `Bool} ⟩
      N₁ [ `Bool ]ᵀ
    ∎

  M·[]—↠N₂[ℕ] : (substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) —↠ (N₂ [ `ℕ ]ᵀ)
  M·[]—↠N₂[ℕ] =
      (substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ])
    —↠⟨ ·[]-↠ M₂—↠ΛN₂ ⟩
      ((Λ N₂) ·[ `ℕ ])
    —↠⟨ β-Λ-↠ {A = `ℕ} ⟩
      N₂ [ `ℕ ]ᵀ
    ∎

  M·[]—↠ƛL₁ : (substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) —↠ (ƛ[ _ ] L₁)
  M·[]—↠ƛL₁ =
      (substᵀ (left ∅ρ) (subst id M) ·[ `Bool ])
    —↠⟨ M·[]—↠N₁[Bool] ⟩
      N₁ [ `Bool ]ᵀ
    —↠⟨ N₁—↠ƛL₁ ⟩
      (ƛ[ _ ] L₁)
    ∎

  M·[]—↠ƛL₂ : (substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) —↠ (ƛ[ _ ] L₂)
  M·[]—↠ƛL₂ =
      (substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ])
    —↠⟨ M·[]—↠N₂[ℕ] ⟩
      N₂ [ `ℕ ]ᵀ
    —↠⟨ N₂—↠ƛL₂ ⟩
      (ƛ[ _ ] L₂)
    ∎

  M·[]·true—↠L₁true : ((substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) · `true) —↠ (L₁ [ `true ])
  M·[]·true—↠L₁true =
      ((substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) · `true)
    —↠⟨ app-↠ M·[]—↠ƛL₁ vLam (`true ∎) ⟩
      ((ƛ[ _ ] L₁) · `true)
    —↠⟨ β-ƛ-↠ vTrue ⟩
      (L₁ [ `true ])
    ∎

  M·[]·suc0—↠L₂suc0 : ((substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) · (`suc `zero)) —↠ (L₂ [ (`suc `zero) ])
  M·[]·suc0—↠L₂suc0 =
      ((substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) · (`suc `zero))
    —↠⟨ app-↠ M·[]—↠ƛL₂ vLam ((`suc `zero) ∎) ⟩
      ((ƛ[ _ ] L₂) · (`suc `zero))
    —↠⟨ β-ƛ-↠ (vSuc vZero) ⟩
      (L₂ [ (`suc `zero) ])
    ∎

  M·[]·true—↠ƛK₁ : ((substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) · `true) —↠ (ƛ[ _ ] K₁)
  M·[]·true—↠ƛK₁ =
      ((substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) · `true)
    —↠⟨ M·[]·true—↠L₁true ⟩
      (L₁ [ `true ])
    —↠⟨ L₁true—↠ƛK₁ ⟩
      (ƛ[ _ ] K₁)
    ∎

  M·[]·suc0—↠ƛK₂ : ((substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) · (`suc `zero)) —↠ (ƛ[ _ ] K₂)
  M·[]·suc0—↠ƛK₂ =
      ((substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) · (`suc `zero))
    —↠⟨ M·[]·suc0—↠L₂suc0 ⟩
      (L₂ [ (`suc `zero) ])
    —↠⟨ L₂suc0—↠ƛK₂ ⟩
      (ƛ[ _ ] K₂)
    ∎

  left-red′ : (((substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) · `true) · neg) —↠ V
  left-red′ =
      (((substᵀ (left ∅ρ) (subst id M) ·[ `Bool ]) · `true) · neg)
    —↠⟨ app-↠ M·[]·true—↠ƛK₁ vLam (neg ∎) ⟩
      ((ƛ[ _ ] K₁) · neg)
    —↠⟨ β-ƛ-↠ vLam ⟩
      (K₁ [ neg ])
    —↠⟨ K₁neg—↠V ⟩
      V
    ∎

  right-red′ : (((substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) · (`suc `zero)) · flip) —↠ W
  right-red′ =
      (((substᵀ (right ∅ρ) (subst id M) ·[ `ℕ ]) · (`suc `zero)) · flip)
    —↠⟨ app-↠ M·[]·suc0—↠ƛK₂ vLam (flip ∎) ⟩
      ((ƛ[ _ ] K₂) · flip)
    —↠⟨ β-ƛ-↠ vLam ⟩
      (K₂ [ flip ])
    —↠⟨ K₂flip—↠W ⟩
      W
    ∎

  left-red : (((M ·[ `Bool ]) · `true) · neg) —↠ V
  left-red = substEq (λ Tm → (((Tm ·[ `Bool ]) · `true) · neg) —↠ V) M-sub-left left-red′

  right-red : (((M ·[ `ℕ ]) · (`suc `zero)) · flip) —↠ W
  right-red = substEq (λ Tm → (((Tm ·[ `ℕ ]) · (`suc `zero)) · flip) —↠ W) M-sub-right right-red′

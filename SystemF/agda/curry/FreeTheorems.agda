{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.FreeTheorems where

-- File Charter:
--   * Ports the intrinsic free-theorem statements to the curry setting.
--   * Reuses the curry logical relation to state relation witnesses.

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; sym)
            renaming (subst to substEq)
open import Data.List using ([])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import curry.ProductOmega using (Σ-syntax; ∃-syntax; _×_)
  renaming (_,_ to ⟨_,_⟩)

open import curry.Types
open import curry.Terms
open import curry.Reduction
open import curry.LogicalRelation
open import curry.Parametricity

--------------------------------------------------------------------------------
-- Free theorem (identity)
--------------------------------------------------------------------------------

-- R = {(V, V)}
idR : ∀ {A} → (V : Term) → Rel A A
idR V V′ W′ _ _ = V ≡ V′ × V ≡ W′

free-theorem-id : ∀ {A : Ty}
  → (M V : Term)
  → 0 ⊢ [] ⊢ M ⦂ `∀ (` 0 ⇒ ` 0)
  → 0 ⊢ [] ⊢ V ⦂ A
  → Value V
    ------------------------
  → ((M ·[]) · V) —↠ V
free-theorem-id {A} M X ⊢M ⊢X vX
  with fundamental M ⊢M ∅ρ ∅γ 𝒢-∅
... | ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ M₂—↠ΛN₂ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with ∀-rel A A (idR {A = A} X)
... | ⟨ .(ƛ L₁) , ⟨ .(ƛ L₂) , ⟨ vLam {N = L₁} , ⟨ vLam {N = L₂} , ⟨ N₁—↠ƛL₁ , ⟨ N₂—↠ƛL₂ , arg-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with arg-rel vX vX ⟨ refl , refl ⟩
... | ⟨ V′ , ⟨ W′ , ⟨ v′ , ⟨ w′ , ⟨ L₁X—↠V′ , ⟨ L₂X—↠W′ , ⟨ X≡V′ , X≡W′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  red
  where
  M·[]—↠N₁ : (subst id M ·[]) —↠ N₁
  M·[]—↠N₁ =
      (subst id M ·[])
    —↠⟨ ·[]-↠ M₁—↠ΛN₁ ⟩
      ((Λ N₁) ·[])
    —↠⟨ β-Λ-↠ {A = A} ⟩
      N₁
    ∎

  M·[]—↠ƛL₁ : (subst id M ·[]) —↠ (ƛ L₁)
  M·[]—↠ƛL₁ =
      (subst id M ·[])
    —↠⟨ M·[]—↠N₁ ⟩
      N₁
    —↠⟨ N₁—↠ƛL₁ ⟩
      (ƛ L₁)
    ∎

  M·[]·X—↠L₁X : ((subst id M ·[]) · X) —↠ (L₁ [ X ])
  M·[]·X—↠L₁X =
      ((subst id M ·[]) · X)
    —↠⟨ app-↠ M·[]—↠ƛL₁ vLam (X ∎) ⟩
      ((ƛ L₁) · X)
    —↠⟨ β-ƛ-↠ vX ⟩
      (L₁ [ X ])
    ∎

  red′ : ((subst id M ·[]) · X) —↠ X
  red′ = substEq (((subst id M ·[]) · X) —↠_) (sym X≡V′)
    ( ((subst id M ·[]) · X)
    —↠⟨ M·[]·X—↠L₁X ⟩
      (L₁ [ X ])
    —↠⟨ L₁X—↠V′ ⟩
      V′
    ∎ )

  red : ((M ·[]) · X) —↠ X
  red rewrite sym (sub-id M) = red′

--------------------------------------------------------------------------------
-- Free theorem (representation independence)
--------------------------------------------------------------------------------

neg : Term
neg = ƛ (`if_then_else (` 0) `false `true)

flip : Term
flip = ƛ (case_[zero⇒_|suc⇒_] (` 0) (`suc `zero) `zero)

-- R = {(true, 1), (false, 0)}
R : Rel `Bool `ℕ
R `true (`suc `zero) vTrue (vSuc vZero) = ⊤
R `false `zero vFalse vZero = ⊤
R _ _ _ _ = ⊥

neg-flip-related : 𝒱 (` 0 ⇒ ` 0) (∅ρ ,⟨ `Bool , `ℕ , R ⟩) neg flip vLam vLam
neg-flip-related {V = `true} {W = `zero} vTrue vZero ()
neg-flip-related {V = `true} {W = `suc `zero} vTrue (vSuc vZero) tt =
  ⟨ `false , ⟨ `zero , ⟨ vFalse , ⟨ vZero ,
    ⟨ (`if_then_else `true `false `true) —→⟨ β-true ⟩ (`false ∎) ,
      ⟨ (case_[zero⇒_|suc⇒_] (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc vZero ⟩ (`zero ∎) ,
        tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `true} {W = `suc (`suc W)} vTrue (vSuc (vSuc w)) ()
neg-flip-related {V = `false} {W = `zero} vFalse vZero tt =
  ⟨ `true , ⟨ `suc `zero , ⟨ vTrue , ⟨ vSuc vZero ,
    ⟨ (`if_then_else `false `false `true) —→⟨ β-false ⟩ (`true ∎) ,
      ⟨ (case_[zero⇒_|suc⇒_] `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎) ,
        tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `false} {W = `suc W} vFalse (vSuc w) ()

-- If 0 ⊢ [] ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
free-theorem-rep :
  ∀ (M : Term)
  → 0 ⊢ [] ⊢ M ⦂ `∀ (` 0 ⇒ (` 0 ⇒ ` 0) ⇒ ` 0)
    ------------------------------------------------------
  → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
        (((M ·[]) · `true)        · neg  —↠ V)
      × (((M ·[]) · (`suc `zero)) · flip —↠ W)
      × R V W v w
free-theorem-rep M ⊢M
  with fundamental M ⊢M ∅ρ ∅γ 𝒢-∅
... | ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ M₂—↠ΛN₂ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with ∀-rel `Bool `ℕ R
... | ⟨ .(ƛ L₁) , ⟨ .(ƛ L₂) , ⟨ vLam {N = L₁} , ⟨ vLam {N = L₂} , ⟨ N₁—↠ƛL₁ , ⟨ N₂—↠ƛL₂ , arg₁-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with arg₁-rel vTrue (vSuc vZero) tt
... | ⟨ .(ƛ K₁) , ⟨ .(ƛ K₂) , ⟨ vLam {N = K₁} , ⟨ vLam {N = K₂} , ⟨ L₁true—↠ƛK₁ , ⟨ L₂suc0—↠ƛK₂ , arg₂-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with arg₂-rel vLam vLam neg-flip-related
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ K₁neg—↠V , ⟨ K₂flip—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ left-red , ⟨ right-red , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  M·[]—↠N₁ : (subst id M ·[]) —↠ N₁
  M·[]—↠N₁ =
      (subst id M ·[])
    —↠⟨ ·[]-↠ M₁—↠ΛN₁ ⟩
      ((Λ N₁) ·[])
    —↠⟨ β-Λ-↠ {A = `Bool} ⟩
      N₁
    ∎

  M·[]—↠N₂ : (subst id M ·[]) —↠ N₂
  M·[]—↠N₂ =
      (subst id M ·[])
    —↠⟨ ·[]-↠ M₂—↠ΛN₂ ⟩
      ((Λ N₂) ·[])
    —↠⟨ β-Λ-↠ {A = `ℕ} ⟩
      N₂
    ∎

  M·[]—↠ƛL₁ : (subst id M ·[]) —↠ (ƛ L₁)
  M·[]—↠ƛL₁ =
      (subst id M ·[])
    —↠⟨ M·[]—↠N₁ ⟩
      N₁
    —↠⟨ N₁—↠ƛL₁ ⟩
      (ƛ L₁)
    ∎

  M·[]—↠ƛL₂ : (subst id M ·[]) —↠ (ƛ L₂)
  M·[]—↠ƛL₂ =
      (subst id M ·[])
    —↠⟨ M·[]—↠N₂ ⟩
      N₂
    —↠⟨ N₂—↠ƛL₂ ⟩
      (ƛ L₂)
    ∎

  M·[]·true—↠L₁true : ((subst id M ·[]) · `true) —↠ (L₁ [ `true ])
  M·[]·true—↠L₁true =
      ((subst id M ·[]) · `true)
    —↠⟨ app-↠ M·[]—↠ƛL₁ vLam (`true ∎) ⟩
      ((ƛ L₁) · `true)
    —↠⟨ β-ƛ-↠ vTrue ⟩
      (L₁ [ `true ])
    ∎

  M·[]·suc0—↠L₂suc0 : ((subst id M ·[]) · (`suc `zero)) —↠ (L₂ [ (`suc `zero) ])
  M·[]·suc0—↠L₂suc0 =
      ((subst id M ·[]) · (`suc `zero))
    —↠⟨ app-↠ M·[]—↠ƛL₂ vLam ((`suc `zero) ∎) ⟩
      ((ƛ L₂) · (`suc `zero))
    —↠⟨ β-ƛ-↠ (vSuc vZero) ⟩
      (L₂ [ (`suc `zero) ])
    ∎

  M·[]·true—↠ƛK₁ : ((subst id M ·[]) · `true) —↠ (ƛ K₁)
  M·[]·true—↠ƛK₁ =
      ((subst id M ·[]) · `true)
    —↠⟨ M·[]·true—↠L₁true ⟩
      (L₁ [ `true ])
    —↠⟨ L₁true—↠ƛK₁ ⟩
      (ƛ K₁)
    ∎

  M·[]·suc0—↠ƛK₂ : ((subst id M ·[]) · (`suc `zero)) —↠ (ƛ K₂)
  M·[]·suc0—↠ƛK₂ =
      ((subst id M ·[]) · (`suc `zero))
    —↠⟨ M·[]·suc0—↠L₂suc0 ⟩
      (L₂ [ (`suc `zero) ])
    —↠⟨ L₂suc0—↠ƛK₂ ⟩
      (ƛ K₂)
    ∎

  left-red' : (((subst id M ·[]) · `true) · neg) —↠ V
  left-red' =
      (((subst id M ·[]) · `true) · neg)
    —↠⟨ app-↠ M·[]·true—↠ƛK₁ vLam (neg ∎) ⟩
      ((ƛ K₁) · neg)
    —↠⟨ β-ƛ-↠ vLam ⟩
      (K₁ [ neg ])
    —↠⟨ K₁neg—↠V ⟩
      V
    ∎

  right-red' : (((subst id M ·[]) · (`suc `zero)) · flip) —↠ W
  right-red' =
      (((subst id M ·[]) · (`suc `zero)) · flip)
    —↠⟨ app-↠ M·[]·suc0—↠ƛK₂ vLam (flip ∎) ⟩
      ((ƛ K₂) · flip)
    —↠⟨ β-ƛ-↠ vLam ⟩
      (K₂ [ flip ])
    —↠⟨ K₂flip—↠W ⟩
      W
    ∎

  left-red : (((M ·[]) · `true) · neg) —↠ V
  left-red rewrite sym (sub-id M) = left-red'

  right-red : (((M ·[]) · (`suc `zero)) · flip) —↠ W
  right-red rewrite sym (sub-id M) = right-red'

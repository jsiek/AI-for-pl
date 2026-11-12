module intrinsic-subst.proof.Parametricity where

-- File Charter:
--   * Private proofs about the logical relation of
--     intrinsic-subst/Parametricity.agda: anti-reduction, the renaming
--     lemma for `𝒱` and `ℰ` (`𝒱-ren⇒`, `𝒱-ren⇐`; weakening is the case
--     `agree-wk`), the compatibility lemmas for every typing rule except
--     type application, and, given that one as a hypothesis
--     (`CompatInst`), the fundamental theorem and termination.
--   * Terms whose types are only propositionally equal are compared with
--     heterogeneous equality `_≅_`.
--   * Uses the substitution laws of intrinsic-subst/proof/TermSubst.agda;
--     no function extensionality, and no assumption beyond `CompatInst`.

open import Level using (Level; Lift; lift; suc; zero)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym;
  trans; cong)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl;
  ≅-to-≡; ≡-to-≅)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction
open import intrinsic-subst.Parametricity
open import intrinsic-subst.proof.TypeSubst using (module TL; module TP;
  sub-idᵗ)
open import intrinsic-subst.proof.TermSubst using (fuseᵀ; idᵀ; exts-[];
  trav-travᵀ; ⇑ᵀ-[]ᵀ; sub-id; module PL; module TmLaws; module SubLaws)

open PL using (FuseHypᵀ; IdHypᵀ; conv∋-≅)
open TmLaws using (convᵀ-≅; ⇑s-⇑ᵛ)

--------------------------------------------------------------------------------
-- Values, casts, and heterogeneous equality
--------------------------------------------------------------------------------

Value-uniq : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} {M : Δ ∣ Γ ⊢ A}
  (v₁ v₂ : Value M)
  → v₁ ≡ v₂
Value-uniq V-zero V-zero = refl
Value-uniq (V-suc v₁) (V-suc v₂) = cong V-suc (Value-uniq v₁ v₂)
Value-uniq V-true V-true = refl
Value-uniq V-false V-false = refl
Value-uniq V-ƛ V-ƛ = refl
Value-uniq V-Λ V-Λ = refl

Value-conv : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ} (p : A ≡ B) {M : Δ ∣ Γ ⊢ A}
  → Value M
  → Value (convᵀ p M)
Value-conv refl v = v

conv-refl : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} (p : A ≡ A) (M : Δ ∣ Γ ⊢ A)
  → convᵀ p M ≡ M
conv-refl refl M = refl

-- a reduction sequence, moved to a heterogeneously equal start
↠-≅ : ∀ {Δ} {Γ : Ctx Δ} {T T' : Type Δ} (p : T ≡ T')
  {X U : Δ ∣ Γ ⊢ T} {X' : Δ ∣ Γ ⊢ T'}
  → X ≅ X'
  → X —↠ U
  → X' —↠ convᵀ p U
↠-≅ refl refl X↠U = X↠U

app-conv∋-≅ : ∀ {Δ} {Γ : Ctx Δ} {F : Type Δ → Set}
  (f : ∀ {C} → Γ ∋ C → F C) {C C' : Type Δ} (p : C ≡ C') (z : Γ ∋ C)
  → f (conv∋ p z) ≅ f z
app-conv∋-≅ f refl z = refl

∀-inj : ∀ {Δ} {A A' : Type (Δ ,α)} → `∀ A ≡ `∀ A' → A ≡ A'
∀-inj refl = refl

ƛ-inj-≅ : ∀ {Δ} {Γ : Ctx Δ} {A A' B B' : Type Δ}
  {N : Δ ∣ Γ , A ⊢ B} {N' : Δ ∣ Γ , A' ⊢ B'}
  → A ≡ A' → B ≡ B' → ƛ A ˙ N ≅ ƛ A' ˙ N'
  → N ≅ N'
ƛ-inj-≅ refl refl refl = refl

Λ-inj-≅ : ∀ {Δ} {Γ : Ctx Δ} {X X' : Type (Δ ,α)}
  {N : Δ ,α ∣ ⇑ᶜ Γ ⊢ X} {N' : Δ ,α ∣ ⇑ᶜ Γ ⊢ X'}
  → X ≡ X' → Λ N ≅ Λ N'
  → N ≅ N'
Λ-inj-≅ refl refl = refl

[]-≅ : ∀ {Δ} {Γ : Ctx Δ} {A A' B B' : Type Δ}
  {N : Δ ∣ Γ , A ⊢ B} {N' : Δ ∣ Γ , A' ⊢ B'}
  {V : Δ ∣ Γ ⊢ A} {V' : Δ ∣ Γ ⊢ A'}
  → A ≡ A' → B ≡ B' → N ≅ N' → V ≅ V'
  → N [ V ] ≅ N' [ V' ]
[]-≅ refl refl refl refl = refl

[]ᵀ-≅ : ∀ {Δ} {Γ : Ctx Δ} {X X' : Type (Δ ,α)}
  {N : Δ ,α ∣ ⇑ᶜ Γ ⊢ X} {N' : Δ ,α ∣ ⇑ᶜ Γ ⊢ X'} (B : Type Δ)
  → X ≡ X' → N ≅ N'
  → N [ B ]ᵀ ≅ N' [ B ]ᵀ
[]ᵀ-≅ B refl refl = refl

sub-arg-≅ : ∀ {Δ} {Γ Γ' : Ctx Δ} (σ : ∀ {C} → Γ ∋ C → Δ ∣ Γ' ⊢ C)
  {A A' : Type Δ} {M : Δ ∣ Γ ⊢ A} {M' : Δ ∣ Γ ⊢ A'}
  → A ≡ A' → M ≅ M'
  → sub σ M ≅ sub σ M'
sub-arg-≅ σ refl refl = refl

-- a relation holds of heterogeneously equal values
R-transport : ∀ {ℓ A₁ A₂} (R : Rel ℓ A₁ A₂)
  {V V' : ∅ ∣ ∅ ⊢ A₁} {W W' : ∅ ∣ ∅ ⊢ A₂}
  {v : Value V} {v' : Value V'} {w : Value W} {w' : Value W'}
  → V ≅ V' → W ≅ W'
  → R V W v w
  → R V' W' v' w'
R-transport R {v = v} {v'} {w} {w'} refl refl r
  with Value-uniq v v' | Value-uniq w w'
... | refl | refl = r

--------------------------------------------------------------------------------
-- Basic facts about the logical relation
--------------------------------------------------------------------------------

𝒱⇒ℰ : ∀ {ℓ Δ} (A : Type Δ) (ρ : RelSub ℓ Δ)
  {V : ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A} {W : ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A}
  (v : Value V) (w : Value W)
  → 𝒱 A ρ V W v w
  → ℰ A ρ V W
𝒱⇒ℰ A ρ {V = V} {W = W} v w rel =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ V ∎ , ⟨ W ∎ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℰ-anti-↠ˡ : ∀ {ℓ Δ} {A : Type Δ} {ρ : RelSub ℓ Δ}
  {M M′ : ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A} {N : ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → M —↠ M′
  → ℰ A ρ M′ N
  → ℰ A ρ M N
ℰ-anti-↠ˡ M↠M′ ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M′↠V , ⟨ N↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ ↠-trans M↠M′ M′↠V , ⟨ N↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℰ-anti-↠ʳ : ∀ {ℓ Δ} {A : Type Δ} {ρ : RelSub ℓ Δ}
  {M : ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A} {N N′ : ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → N —↠ N′
  → ℰ A ρ M N′
  → ℰ A ρ M N
ℰ-anti-↠ʳ N↠N′ ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M↠V , ⟨ N′↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M↠V , ⟨ ↠-trans N↠N′ N′↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℰ-cast : ∀ {ℓ Δ} {A : Type Δ} {ρ : RelSub ℓ Δ}
  {M M′ : ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A} {N N′ : ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → M ≡ M′
  → N ≡ N′
  → ℰ A ρ M′ N′
  → ℰ A ρ M N
ℰ-cast refl refl rel = rel

-- the relations at `Nat` and `Bool` do not depend on the substitution
𝒱-Nat-irrel : ∀ {ℓ Δ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  {V W : ∅ ∣ ∅ ⊢ `Nat} {v : Value V} {w : Value W}
  → 𝒱 `Nat ρ V W v w
  → 𝒱 `Nat ρ' V W v w
𝒱-Nat-irrel {v = V-zero} {w = V-zero} rel = rel
𝒱-Nat-irrel {v = V-zero} {w = V-suc w} (lift ())
𝒱-Nat-irrel {v = V-suc v} {w = V-zero} (lift ())
𝒱-Nat-irrel {ρ = ρ} {ρ' = ρ'} {v = V-suc v} {w = V-suc w} rel =
  𝒱-Nat-irrel {ρ = ρ} {ρ' = ρ'} {v = v} {w = w} rel

𝒱-Bool-irrel : ∀ {ℓ Δ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  {V W : ∅ ∣ ∅ ⊢ `Bool} {v : Value V} {w : Value W}
  → 𝒱 `Bool ρ V W v w
  → 𝒱 `Bool ρ' V W v w
𝒱-Bool-irrel {v = V-true} {w = V-true} rel = rel
𝒱-Bool-irrel {v = V-true} {w = V-false} (lift ())
𝒱-Bool-irrel {v = V-false} {w = V-true} (lift ())
𝒱-Bool-irrel {v = V-false} {w = V-false} rel = rel

𝒱-Nat-≅ : ∀ {ℓ Δ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  {V V' W W' : ∅ ∣ ∅ ⊢ `Nat}
  {v : Value V} {v' : Value V'} {w : Value W} {w' : Value W'}
  → V ≅ V' → W ≅ W'
  → 𝒱 `Nat ρ V W v w
  → 𝒱 `Nat ρ' V' W' v' w'
𝒱-Nat-≅ {ρ = ρ} {ρ' = ρ'} {v = v} {v'} {w} {w'} refl refl rel
  with Value-uniq v v' | Value-uniq w w'
... | refl | refl = 𝒱-Nat-irrel {ρ = ρ} {ρ' = ρ'} {v = v} {w = w} rel

𝒱-Bool-≅ : ∀ {ℓ Δ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  {V V' W W' : ∅ ∣ ∅ ⊢ `Bool}
  {v : Value V} {v' : Value V'} {w : Value W} {w' : Value W'}
  → V ≅ V' → W ≅ W'
  → 𝒱 `Bool ρ V W v w
  → 𝒱 `Bool ρ' V' W' v' w'
𝒱-Bool-≅ {ρ = ρ} {ρ' = ρ'} {v = v} {v'} {w} {w'} refl refl rel
  with Value-uniq v v' | Value-uniq w w'
... | refl | refl = 𝒱-Bool-irrel {ρ = ρ} {ρ' = ρ'} {v = v} {w = w} rel

--------------------------------------------------------------------------------
-- Renaming the types of the logical relation
--------------------------------------------------------------------------------

-- `ρ` agrees with `ρ'` along the renaming `ξ`
record Agree {ℓ Δ Δ'} (ξ : Δ ⇒ʳ Δ') (ρ : RelSub ℓ Δ) (ρ' : RelSub ℓ Δ')
  : Set ℓ where
  field
    e₁ : ∀ (α : TyVar Δ) → ρ₁ ρ α ≡ ρ₁ ρ' (ξ α)
    e₂ : ∀ (α : TyVar Δ) → ρ₂ ρ α ≡ ρ₂ ρ' (ξ α)
    R⇒ : ∀ (α : TyVar Δ) {V V' W W'}
      {v : Value V} {v' : Value V'} {w : Value W} {w' : Value W'}
      → V ≅ V' → W ≅ W'
      → ρR ρ α V W v w
      → ρR ρ' (ξ α) V' W' v' w'
    R⇐ : ∀ (α : TyVar Δ) {V V' W W'}
      {v : Value V} {v' : Value V'} {w : Value W} {w' : Value W'}
      → V ≅ V' → W ≅ W'
      → ρR ρ' (ξ α) V' W' v' w'
      → ρR ρ α V W v w

open Agree

agree-ext : ∀ {ℓ Δ Δ'} {ξ : Δ ⇒ʳ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  → Agree ξ ρ ρ'
  → (A₁ A₂ : Type ∅) (R : Rel ℓ A₁ A₂)
  → Agree (extᵗ ξ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)
agree-ext ag A₁ A₂ R = record
  { e₁ = λ { Z → refl ; (S α) → e₁ ag α }
  ; e₂ = λ { Z → refl ; (S α) → e₂ ag α }
  ; R⇒ = λ { Z eqV eqW r → R-transport R eqV eqW r
           ; (S α) eqV eqW r → R⇒ ag α eqV eqW r }
  ; R⇐ = λ { Z eqV eqW r → R-transport R (H.sym eqV) (H.sym eqW) r
           ; (S α) eqV eqW r → R⇐ ag α eqV eqW r }
  }

-- weakening: a relational substitution agrees with its extension
agree-wk : ∀ {ℓ Δ} {ρ : RelSub ℓ Δ}
  → (A₁ A₂ : Type ∅) (R : Rel ℓ A₁ A₂)
  → Agree (λ α → S α) ρ (extendRelSub ρ A₁ A₂ R)
agree-wk {ρ = ρ} A₁ A₂ R = record
  { e₁ = λ α → refl
  ; e₂ = λ α → refl
  ; R⇒ = λ α eqV eqW r → R-transport (ρR ρ α) eqV eqW r
  ; R⇐ = λ α eqV eqW r → R-transport (ρR ρ α) (H.sym eqV) (H.sym eqW) r
  }

module _ {ℓ Δ Δ'} {ξ : Δ ⇒ʳ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'} where

  ren-eq₁ : Agree ξ ρ ρ' → ∀ (A : Type Δ)
    → substᵗ (ρ₁ ρ) A ≡ substᵗ (ρ₁ ρ') (renameᵗ ξ A)
  ren-eq₁ ag A =
    trans (TL.sub-cong {σ = ρ₁ ρ} {τ = λ α → ρ₁ ρ' (ξ α)} (λ α → e₁ ag α) A)
      (sym (TL.ren-sub {r = ξ} {σ = ρ₁ ρ'} {τ = λ α → ρ₁ ρ' (ξ α)}
              (λ _ → refl) A))

  ren-eq₂ : Agree ξ ρ ρ' → ∀ (A : Type Δ)
    → substᵗ (ρ₂ ρ) A ≡ substᵗ (ρ₂ ρ') (renameᵗ ξ A)
  ren-eq₂ ag A =
    trans (TL.sub-cong {σ = ρ₂ ρ} {τ = λ α → ρ₂ ρ' (ξ α)} (λ α → e₂ ag α) A)
      (sym (TL.ren-sub {r = ξ} {σ = ρ₂ ρ'} {τ = λ α → ρ₂ ρ' (ξ α)}
              (λ _ → refl) A))

𝒱-ren⇒ : ∀ {ℓ Δ Δ'} {ξ : Δ ⇒ʳ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  → Agree ξ ρ ρ'
  → ∀ (A : Type Δ) {V W V' W'}
    {v : Value V} {w : Value W} {v' : Value V'} {w' : Value W'}
  → V ≅ V' → W ≅ W'
  → 𝒱 A ρ V W v w
  → 𝒱 (renameᵗ ξ A) ρ' V' W' v' w'

𝒱-ren⇐ : ∀ {ℓ Δ Δ'} {ξ : Δ ⇒ʳ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  → Agree ξ ρ ρ'
  → ∀ (A : Type Δ) {V W V' W'}
    {v : Value V} {w : Value W} {v' : Value V'} {w' : Value W'}
  → V ≅ V' → W ≅ W'
  → 𝒱 (renameᵗ ξ A) ρ' V' W' v' w'
  → 𝒱 A ρ V W v w

ℰ-ren⇒ : ∀ {ℓ Δ Δ'} {ξ : Δ ⇒ʳ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  → Agree ξ ρ ρ'
  → ∀ (A : Type Δ) {X Y X' Y'}
  → X ≅ X' → Y ≅ Y'
  → ℰ A ρ X Y
  → ℰ (renameᵗ ξ A) ρ' X' Y'

ℰ-ren⇐ : ∀ {ℓ Δ Δ'} {ξ : Δ ⇒ʳ Δ'} {ρ : RelSub ℓ Δ} {ρ' : RelSub ℓ Δ'}
  → Agree ξ ρ ρ'
  → ∀ (A : Type Δ) {X Y X' Y'}
  → X ≅ X' → Y ≅ Y'
  → ℰ (renameᵗ ξ A) ρ' X' Y'
  → ℰ A ρ X Y

𝒱-ren⇒ ag (` α) eqV eqW (lift r) = lift (R⇒ ag α eqV eqW r)
𝒱-ren⇒ {ρ = ρ} {ρ' = ρ'} ag `Nat {v = v} {w = w} {v' = v'} {w' = w'}
  eqV eqW rel =
  𝒱-Nat-≅ {ρ = ρ} {ρ' = ρ'} {v = v} {v'} {w} {w'} eqV eqW rel
𝒱-ren⇒ {ρ = ρ} {ρ' = ρ'} ag `Bool {v = v} {w = w} {v' = v'} {w' = w'}
  eqV eqW rel =
  𝒱-Bool-≅ {ρ = ρ} {ρ' = ρ'} {v = v} {v'} {w} {w'} eqV eqW rel
𝒱-ren⇒ ag (A ⇒ B) {v = V-ƛ {N = N}} {w = V-ƛ {N = M}}
  {v' = V-ƛ {N = N'}} {w' = V-ƛ {N = M'}} eqV eqW f {V₁'} {W₁'} v₁' w₁' rel' =
    ℰ-ren⇒ ag B
      ([]-≅ eA₁ eB₁ (ƛ-inj-≅ eA₁ eB₁ eqV) (convᵀ-≅ (sym eA₁) V₁'))
      ([]-≅ eA₂ eB₂ (ƛ-inj-≅ eA₂ eB₂ eqW) (convᵀ-≅ (sym eA₂) W₁'))
      (f (Value-conv (sym eA₁) v₁') (Value-conv (sym eA₂) w₁')
         (𝒱-ren⇐ ag A (convᵀ-≅ (sym eA₁) V₁') (convᵀ-≅ (sym eA₂) W₁') rel'))
  where
  eA₁ = ren-eq₁ ag A
  eB₁ = ren-eq₁ ag B
  eA₂ = ren-eq₂ ag A
  eB₂ = ren-eq₂ ag B
𝒱-ren⇒ {ξ = ξ} {ρ = ρ} {ρ' = ρ'} ag (`∀ A) {v = V-Λ {N = N}} {w = V-Λ {N = M}}
  {v' = V-Λ {N = N'}} {w' = V-Λ {N = M'}} eqV eqW f A₁ A₂ R =
    ℰ-ren⇒ (agree-ext ag A₁ A₂ R) A
      (H.trans (convᵀ-≅ (TL.exts-[] (ρ₁ ρ) A A₁) (N [ A₁ ]ᵀ))
        (H.trans ([]ᵀ-≅ A₁ eX₁ (Λ-inj-≅ eX₁ eqV))
          (H.sym (convᵀ-≅ (TL.exts-[] (ρ₁ ρ') (renameᵗ (extᵗ ξ) A) A₁)
                    (N' [ A₁ ]ᵀ)))))
      (H.trans (convᵀ-≅ (TL.exts-[] (ρ₂ ρ) A A₂) (M [ A₂ ]ᵀ))
        (H.trans ([]ᵀ-≅ A₂ eX₂ (Λ-inj-≅ eX₂ eqW))
          (H.sym (convᵀ-≅ (TL.exts-[] (ρ₂ ρ') (renameᵗ (extᵗ ξ) A) A₂)
                    (M' [ A₂ ]ᵀ)))))
      (f A₁ A₂ R)
  where
  eX₁ = ∀-inj (ren-eq₁ ag (`∀ A))
  eX₂ = ∀-inj (ren-eq₂ ag (`∀ A))

𝒱-ren⇐ ag (` α) eqV eqW (lift r) = lift (R⇐ ag α eqV eqW r)
𝒱-ren⇐ {ρ = ρ} {ρ' = ρ'} ag `Nat {v = v} {w = w} {v' = v'} {w' = w'}
  eqV eqW rel =
  𝒱-Nat-≅ {ρ = ρ'} {ρ' = ρ} {v = v'} {v} {w'} {w}
    (H.sym eqV) (H.sym eqW) rel
𝒱-ren⇐ {ρ = ρ} {ρ' = ρ'} ag `Bool {v = v} {w = w} {v' = v'} {w' = w'}
  eqV eqW rel =
  𝒱-Bool-≅ {ρ = ρ'} {ρ' = ρ} {v = v'} {v} {w'} {w}
    (H.sym eqV) (H.sym eqW) rel
𝒱-ren⇐ ag (A ⇒ B) {v = V-ƛ {N = N}} {w = V-ƛ {N = M}}
  {v' = V-ƛ {N = N'}} {w' = V-ƛ {N = M'}} eqV eqW f' {V₁} {W₁} v₁ w₁ rel =
    ℰ-ren⇐ ag B
      ([]-≅ eA₁ eB₁ (ƛ-inj-≅ eA₁ eB₁ eqV) (H.sym (convᵀ-≅ eA₁ V₁)))
      ([]-≅ eA₂ eB₂ (ƛ-inj-≅ eA₂ eB₂ eqW) (H.sym (convᵀ-≅ eA₂ W₁)))
      (f' (Value-conv eA₁ v₁) (Value-conv eA₂ w₁)
         (𝒱-ren⇒ ag A (H.sym (convᵀ-≅ eA₁ V₁)) (H.sym (convᵀ-≅ eA₂ W₁)) rel))
  where
  eA₁ = ren-eq₁ ag A
  eB₁ = ren-eq₁ ag B
  eA₂ = ren-eq₂ ag A
  eB₂ = ren-eq₂ ag B
𝒱-ren⇐ {ξ = ξ} {ρ = ρ} {ρ' = ρ'} ag (`∀ A) {v = V-Λ {N = N}} {w = V-Λ {N = M}}
  {v' = V-Λ {N = N'}} {w' = V-Λ {N = M'}} eqV eqW f' A₁ A₂ R =
    ℰ-ren⇐ (agree-ext ag A₁ A₂ R) A
      (H.trans (convᵀ-≅ (TL.exts-[] (ρ₁ ρ) A A₁) (N [ A₁ ]ᵀ))
        (H.trans ([]ᵀ-≅ A₁ eX₁ (Λ-inj-≅ eX₁ eqV))
          (H.sym (convᵀ-≅ (TL.exts-[] (ρ₁ ρ') (renameᵗ (extᵗ ξ) A) A₁)
                    (N' [ A₁ ]ᵀ)))))
      (H.trans (convᵀ-≅ (TL.exts-[] (ρ₂ ρ) A A₂) (M [ A₂ ]ᵀ))
        (H.trans ([]ᵀ-≅ A₂ eX₂ (Λ-inj-≅ eX₂ eqW))
          (H.sym (convᵀ-≅ (TL.exts-[] (ρ₂ ρ') (renameᵗ (extᵗ ξ) A) A₂)
                    (M' [ A₂ ]ᵀ)))))
      (f' A₁ A₂ R)
  where
  eX₁ = ∀-inj (ren-eq₁ ag (`∀ A))
  eX₂ = ∀-inj (ren-eq₂ ag (`∀ A))

ℰ-ren⇒ ag A eqX eqY
  ⟨ U , ⟨ U' , ⟨ u , ⟨ u' , ⟨ X↠U , ⟨ Y↠U' , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ convᵀ e₁A U , ⟨ convᵀ e₂A U'
  , ⟨ Value-conv e₁A u , ⟨ Value-conv e₂A u'
  , ⟨ ↠-≅ e₁A eqX X↠U , ⟨ ↠-≅ e₂A eqY Y↠U'
  , 𝒱-ren⇒ ag A (H.sym (convᵀ-≅ e₁A U)) (H.sym (convᵀ-≅ e₂A U')) rel
  ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  e₁A = ren-eq₁ ag A
  e₂A = ren-eq₂ ag A

ℰ-ren⇐ ag A eqX eqY
  ⟨ U' , ⟨ W' , ⟨ u' , ⟨ w' , ⟨ X'↠U' , ⟨ Y'↠W' , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ convᵀ (sym e₁A) U' , ⟨ convᵀ (sym e₂A) W'
  , ⟨ Value-conv (sym e₁A) u' , ⟨ Value-conv (sym e₂A) w'
  , ⟨ ↠-≅ (sym e₁A) (H.sym eqX) X'↠U' , ⟨ ↠-≅ (sym e₂A) (H.sym eqY) Y'↠W'
  , 𝒱-ren⇐ ag A (convᵀ-≅ (sym e₁A) U') (convᵀ-≅ (sym e₂A) W') rel
  ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  e₁A = ren-eq₁ ag A
  e₂A = ren-eq₂ ag A

--------------------------------------------------------------------------------
-- Extending environments under a term binder
--------------------------------------------------------------------------------

extEnv : ∀ {ℓ Δ} {Γ : Ctx Δ} {ρ : RelSub ℓ Δ} (A : Type Δ)
  → RelEnv Γ ρ
  → ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A
  → ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A
  → RelEnv (Γ , A) ρ
extEnv {ρ = ρ} A e V W = record
  { Γ₁ = Γ₁ e , substᵗ (ρ₁ ρ) A
  ; Γ₂ = Γ₂ e , substᵗ (ρ₂ ρ) A
  ; r₁ = extρ subKᵗ (ρ₁ ρ) (r₁ e)
  ; r₂ = extρ subKᵗ (ρ₂ ρ) (r₂ e)
  ; γ₁ = V • γ₁ e
  ; γ₂ = W • γ₂ e
  }

extEnv-𝒢 : ∀ {ℓ Δ} {Γ : Ctx Δ} {ρ : RelSub ℓ Δ} {A : Type Δ}
  {e : RelEnv Γ ρ}
  {V : ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A} {W : ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → 𝒢 ρ e
  → (v : Value V) (w : Value W)
  → 𝒱 A ρ V W v w
  → 𝒢 ρ (extEnv A e V W)
extEnv-𝒢 {ρ = ρ} {A = A} g v w rel Z = 𝒱⇒ℰ A ρ v w rel
extEnv-𝒢 g v w rel (S x) = g x

--------------------------------------------------------------------------------
-- Instantiating a type abstraction
--------------------------------------------------------------------------------

-- instantiate the type variable of closed terms in `∅ ,α` by `B`
instSub : (B : Type ∅) {Δ' : Ctx (∅ ,α)}
  → (∀ {C} → Δ' ∋ C → ∅ ,α ∣ ∅ ⊢ C)
  → ∀ {C} → mapᶜ subKᵗ (B •ᵗ idᵗ) Δ' ∋ C → ∅ ∣ ∅ ⊢ C
instSub B {Δ' , D} τ Z = τ Z [ B ]ᵀ
instSub B {Δ' , D} τ (S x) = instSub B (λ y → τ (S y)) x

instSub-mapᵛ : ∀ (B : Type ∅) {Δ' : Ctx (∅ ,α)}
  (τ : ∀ {C} → Δ' ∋ C → ∅ ,α ∣ ∅ ⊢ C) {C} (y : Δ' ∋ C)
  → instSub B τ (mapᵛ subKᵗ (B •ᵗ idᵗ) y) ≡ τ y [ B ]ᵀ
instSub-mapᵛ B τ Z = refl
instSub-mapᵛ B τ (S y) = instSub-mapᵛ B (λ z → τ (S z)) y

module _ {Δ} (σ : Δ ⇒ˢ ∅) (B : Type ∅) where

  -- instantiating after substituting under the binder
  inst-pt : ∀ (α : TyVar (Δ ,α))
    → substᵗ (B •ᵗ idᵗ) (extsᵗ σ α) ≡ (B •ᵗ σ) α
  inst-pt Z = refl
  inst-pt (S α) = TL.⇑-[] (σ α) B

  inst-eq : ∀ (C : Type (Δ ,α))
    → substᵗ (B •ᵗ idᵗ) (substᵗ (extsᵗ σ) C) ≡ substᵗ (B •ᵗ σ) C
  inst-eq C = TL.sub-sub (λ α → inst-pt α) C

  -- the term variables of the instantiated context
  inst-r : ∀ {Γ : Ctx Δ} {Γ₀ : Ctx ∅}
    → TyRen subKᵗ σ Γ Γ₀
    → TyRen subKᵗ (B •ᵗ σ) (⇑ᶜ Γ) (mapᶜ subKᵗ (B •ᵗ idᵗ) (⇑ᶜ Γ₀))
  inst-r r {C} x = conv∋ (inst-eq C) (mapᵛ subKᵗ (B •ᵗ idᵗ) (⇑ρ subKᵗ σ r x))

  -- closing the body of a type abstraction, then instantiating it, is
  -- closing it with the instantiated substitution and environment
  Λ-close : ∀ {Γ : Ctx Δ} {Γ₀ : Ctx ∅} (r : TyRen subKᵗ σ Γ Γ₀)
    (γ : ∀ {C} → Γ₀ ∋ C → ∅ ∣ ∅ ⊢ C) {A} (N : Δ ,α ∣ ⇑ᶜ Γ ⊢ A)
    → convᵀ (TL.exts-[] σ A B)
        (sub (⇑s tmK γ) (travᵀ subKᵗ (extsᵗ σ) (⇑ρ subKᵗ σ r) N) [ B ]ᵀ)
      ≡ sub (instSub B (⇑s tmK γ)) (travᵀ subKᵗ (B •ᵗ σ) (inst-r r) N)
  Λ-close r γ {A} N =
    ≅-to-≡
      (H.trans (convᵀ-≅ (TL.exts-[] σ A B) (sub τ Y [ B ]ᵀ))
        (H.trans
          (≡-to-≅ (sym (trav-travᵀ SubLaws.tmKL subKᵗ {θ = B •ᵗ idᵗ}
            {σ = τ} {ρ = mapᵛ subKᵗ (B •ᵗ idᵗ)} {ρ₁ = instᵛ B}
            {σ' = instSub B τ} (λ x → instSub-mapᵛ B τ x) Y)))
          (sub-arg-≅ (instSub B τ) (inst-eq A)
            (fuseᵀ {𝒯₁ = subKᵗ} {𝒯₂ = subKᵗ} {𝒯₃ = subKᵗ}
              {θ₁ = extsᵗ σ} {θ₂ = B •ᵗ idᵗ} {θ₃ = B •ᵗ σ}
              {ρ₁ = ⇑ρ subKᵗ σ r} {ρ₂ = mapᵛ subKᵗ (B •ᵗ idᵗ)}
              {ρ₃ = inst-r r}
              (record
                { ty-var = λ α → inst-pt α
                ; ctx = refl
                ; var = λ {C} x → H.sym (conv∋-≅ (inst-eq C)
                          (mapᵛ subKᵗ (B •ᵗ idᵗ) (⇑ρ subKᵗ σ r x)))
                })
              N))))
    where
    τ = ⇑s tmK γ
    Y = travᵀ subKᵗ (extsᵗ σ) (⇑ρ subKᵗ σ r) N

-- the environment for the body of a type abstraction
ΛEnv : ∀ {ℓ Δ} {Γ : Ctx Δ} {ρ : RelSub ℓ Δ}
  → RelEnv Γ ρ
  → (A₁ A₂ : Type ∅) (R : Rel ℓ A₁ A₂)
  → RelEnv (⇑ᶜ Γ) (extendRelSub ρ A₁ A₂ R)
ΛEnv {ρ = ρ} e A₁ A₂ R = record
  { Γ₁ = mapᶜ subKᵗ (A₁ •ᵗ idᵗ) (⇑ᶜ (Γ₁ e))
  ; Γ₂ = mapᶜ subKᵗ (A₂ •ᵗ idᵗ) (⇑ᶜ (Γ₂ e))
  ; r₁ = inst-r (ρ₁ ρ) A₁ (r₁ e)
  ; r₂ = inst-r (ρ₂ ρ) A₂ (r₂ e)
  ; γ₁ = instSub A₁ (⇑s tmK (γ₁ e))
  ; γ₂ = instSub A₂ (⇑s tmK (γ₂ e))
  }

private
  app-≅ : ∀ {Δ} {Γ : Ctx Δ} {F : Type Δ → Set}
    (f : ∀ {C} → Γ ∋ C → F C) {C C' : Type Δ} {z : Γ ∋ C} {z' : Γ ∋ C'}
    → C ≡ C' → z ≅ z'
    → f z ≅ f z'
  app-≅ f refl refl = refl

  -- the instantiated environment, at the variable bound last, is the
  -- original one
  inst-γ-≅ : ∀ {Δ} (σ : Δ ⇒ˢ ∅) (B : Type ∅) {Γ : Ctx Δ} {Γ₀ : Ctx ∅}
    {D : Type Δ} (r : TyRen subKᵗ σ (Γ , D) Γ₀)
    (γ : ∀ {C} → Γ₀ ∋ C → ∅ ∣ ∅ ⊢ C)
    → instSub B (⇑s tmK γ) (inst-r σ B r Z) ≅ γ (r Z)
  inst-γ-≅ σ B {D = D} r γ =
    H.trans (app-conv∋-≅ (instSub B (⇑s tmK γ)) (inst-eq σ B (⇑ᵗ D))
               (mapᵛ subKᵗ (B •ᵗ idᵗ) (⇑ρ subKᵗ σ r Z)))
      (H.trans (≡-to-≅ (instSub-mapᵛ B (⇑s tmK γ) (⇑ρ subKᵗ σ r Z)))
        (H.trans ([]ᵀ-≅ B E (app-≅ (⇑s tmK γ) E
                   (PL.⇑ρ-⇑ᵛ-≅ subKᵗ σ r Z)))
          (H.trans (≡-to-≅ (cong (λ M → M [ B ]ᵀ) (⇑s-⇑ᵛ tmK γ (r Z))))
            (⇑ᵀ-[]ᵀ (γ (r Z)) B))))
    where
    E = TP.Laws.exts-ren TL.tmL σ D

-- the instantiated environments are related
ΛEnv-𝒢 : ∀ {ℓ Δ} {Γ : Ctx Δ} {ρ : RelSub ℓ Δ}
  (e : RelEnv Γ ρ) (A₁ A₂ : Type ∅) (R : Rel ℓ A₁ A₂)
  → 𝒢 ρ e
  → 𝒢 (extendRelSub ρ A₁ A₂ R) (ΛEnv e A₁ A₂ R)
ΛEnv-𝒢 {Δ = Δ} {ρ = ρ} e A₁ A₂ R g = go (r₁ e) (r₂ e) g
  where
  go : ∀ {Γ' : Ctx Δ}
    (s₁ : TyRen subKᵗ (ρ₁ ρ) Γ' (Γ₁ e)) (s₂ : TyRen subKᵗ (ρ₂ ρ) Γ' (Γ₂ e))
    → (∀ {D} (y : Γ' ∋ D) → ℰ D ρ (γ₁ e (s₁ y)) (γ₂ e (s₂ y)))
    → ∀ {C} (x : ⇑ᶜ Γ' ∋ C)
    → ℰ C (extendRelSub ρ A₁ A₂ R)
        (instSub A₁ (⇑s tmK (γ₁ e)) (inst-r (ρ₁ ρ) A₁ s₁ x))
        (instSub A₂ (⇑s tmK (γ₂ e)) (inst-r (ρ₂ ρ) A₂ s₂ x))
  go {Γ' , D} s₁ s₂ h Z =
    ℰ-ren⇒ (agree-wk A₁ A₂ R) D
      (H.sym (inst-γ-≅ (ρ₁ ρ) A₁ s₁ (γ₁ e)))
      (H.sym (inst-γ-≅ (ρ₂ ρ) A₂ s₂ (γ₂ e)))
      (h Z)
  go {Γ' , D} s₁ s₂ h (S x) =
    go (λ y → s₁ (S y)) (λ y → s₂ (S y)) (λ y → h (S y)) x

--------------------------------------------------------------------------------
-- Compatibility lemmas
--------------------------------------------------------------------------------

compat-true : ∀ {ℓ Δ} {Γ : Ctx Δ} → LogicalRel ℓ (`true {Γ = Γ}) `true
compat-true ρ e g = 𝒱⇒ℰ `Bool ρ V-true V-true tt

compat-false : ∀ {ℓ Δ} {Γ : Ctx Δ} → LogicalRel ℓ (`false {Γ = Γ}) `false
compat-false ρ e g = 𝒱⇒ℰ `Bool ρ V-false V-false tt

compat-zero : ∀ {ℓ Δ} {Γ : Ctx Δ} → LogicalRel ℓ (`zero {Γ = Γ}) `zero
compat-zero ρ e g = 𝒱⇒ℰ `Nat ρ V-zero V-zero tt

compat-var : ∀ {ℓ Δ} {Γ : Ctx Δ} {A} (x : Γ ∋ A) → LogicalRel ℓ (` x) (` x)
compat-var x ρ e g = g x

compat-suc : ∀ {ℓ Δ} {Γ : Ctx Δ} {M : Δ ∣ Γ ⊢ `Nat}
  → LogicalRel ℓ M M
  → LogicalRel ℓ (`suc M) (`suc M)
compat-suc M-rel ρ e g with M-rel ρ e g
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M↠V , ⟨ M↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ `suc V , ⟨ `suc W , ⟨ V-suc v , ⟨ V-suc w
  , ⟨ suc-↠ M↠V , ⟨ suc-↠ M↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-if : ∀ {ℓ Δ} {Γ : Ctx Δ} {A} {L : Δ ∣ Γ ⊢ `Bool} {M N : Δ ∣ Γ ⊢ A}
  → LogicalRel ℓ L L
  → LogicalRel ℓ M M
  → LogicalRel ℓ N N
  → LogicalRel ℓ (`if_then_else L M N) (`if_then_else L M N)
compat-if {A = A} {L = L} {M = M} {N = N} L-rel M-rel N-rel ρ e g =
  go (L-rel ρ e g)
  where
  M₁ = close₁ e M
  M₂ = close₂ e M
  N₁ = close₁ e N
  N₂ = close₂ e N
  go : ℰ `Bool ρ (close₁ e L) (close₂ e L)
    → ℰ A ρ (`if_then_else (close₁ e L) M₁ N₁)
            (`if_then_else (close₂ e L) M₂ N₂)
  go ⟨ _ , ⟨ _ , ⟨ V-true , ⟨ V-true , ⟨ L↠ , ⟨ L↠′ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ℰ-anti-↠ʳ {A = A} {ρ = ρ}
      (↠-trans (if-↠ {M = M₂} {N = N₂} L↠′) (step-eq-↠ β-true refl))
      (ℰ-anti-↠ˡ {A = A} {ρ = ρ}
        (↠-trans (if-↠ {M = M₁} {N = N₁} L↠) (step-eq-↠ β-true refl))
        (M-rel ρ e g))
  go ⟨ _ , ⟨ _ , ⟨ V-false , ⟨ V-false , ⟨ L↠ , ⟨ L↠′ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ℰ-anti-↠ʳ {A = A} {ρ = ρ} (↠-trans (if-↠ {M = M₂} {N = N₂} L↠′)
                 (step-eq-↠ β-false refl))
      (ℰ-anti-↠ˡ {A = A} {ρ = ρ} (↠-trans (if-↠ {M = M₁} {N = N₁} L↠)
                    (step-eq-↠ β-false refl))
        (N-rel ρ e g))
  go ⟨ _ , ⟨ _ , ⟨ V-true , ⟨ V-false , ⟨ _ , ⟨ _ , lift () ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  go ⟨ _ , ⟨ _ , ⟨ V-false , ⟨ V-true , ⟨ _ , ⟨ _ , lift () ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-case-nat : ∀ {ℓ Δ} {Γ : Ctx Δ} {A}
  {L : Δ ∣ Γ ⊢ `Nat} {M : Δ ∣ Γ ⊢ A} {N : Δ ∣ Γ , `Nat ⊢ A}
  → LogicalRel ℓ L L
  → LogicalRel ℓ M M
  → LogicalRel ℓ N N
  → LogicalRel ℓ (`case-nat L M N) (`case-nat L M N)
compat-case-nat {A = A} {L = L} {M = M} {N = N} L-rel M-rel N-rel ρ e g =
  go (L-rel ρ e g)
  where
  M₁ = close₁ e M
  M₂ = close₂ e M
  N₁′ = travᵀ subKᵗ (ρ₁ ρ) (extρ subKᵗ (ρ₁ ρ) (r₁ e)) N
  N₂′ = travᵀ subKᵗ (ρ₂ ρ) (extρ subKᵗ (ρ₂ ρ) (r₂ e)) N
  N₁ = sub (exts tmK (γ₁ e)) N₁′
  N₂ = sub (exts tmK (γ₂ e)) N₂′
  go : ℰ `Nat ρ (close₁ e L) (close₂ e L)
    → ℰ A ρ (`case-nat (close₁ e L) M₁ N₁) (`case-nat (close₂ e L) M₂ N₂)
  go ⟨ _ , ⟨ _ , ⟨ V-zero , ⟨ V-zero , ⟨ L↠ , ⟨ L↠′ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ℰ-anti-↠ʳ {A = A} {ρ = ρ} (↠-trans (case-nat-↠ {M = M₂} {N = N₂} L↠′)
                 (step-eq-↠ β-zero refl))
      (ℰ-anti-↠ˡ {A = A} {ρ = ρ} (↠-trans (case-nat-↠ {M = M₁} {N = N₁} L↠)
                    (step-eq-↠ β-zero refl))
        (M-rel ρ e g))
  go ⟨ _ , ⟨ _ , ⟨ V-suc {V = V} v , ⟨ V-suc {V = W} w
     , ⟨ L↠ , ⟨ L↠′ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ℰ-anti-↠ʳ {A = A} {ρ = ρ} (↠-trans (case-nat-↠ {M = M₂} {N = N₂} L↠′)
                 (step-eq-↠ (β-suc w) refl))
      (ℰ-anti-↠ˡ {A = A} {ρ = ρ} (↠-trans (case-nat-↠ {M = M₁} {N = N₁} L↠)
                    (step-eq-↠ (β-suc v) refl))
        (ℰ-cast {A = A} {ρ = ρ} (exts-[] (γ₁ e) N₁′ V) (exts-[] (γ₂ e) N₂′ W)
          (N-rel ρ (extEnv `Nat e V W) (extEnv-𝒢 g v w rel))))
  go ⟨ _ , ⟨ _ , ⟨ V-zero , ⟨ V-suc w , ⟨ _ , ⟨ _ , lift () ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  go ⟨ _ , ⟨ _ , ⟨ V-suc v , ⟨ V-zero , ⟨ _ , ⟨ _ , lift () ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-ƛ : ∀ {ℓ Δ} {Γ : Ctx Δ} {A B} {N : Δ ∣ Γ , A ⊢ B}
  → LogicalRel ℓ N N
  → LogicalRel ℓ (ƛ A ˙ N) (ƛ A ˙ N)
compat-ƛ {A = A} {B = B} {N = N} N-rel ρ e g =
  𝒱⇒ℰ (A ⇒ B) ρ V-ƛ V-ƛ body
  where
  N₁ = travᵀ subKᵗ (ρ₁ ρ) (extρ subKᵗ (ρ₁ ρ) (r₁ e)) N
  N₂ = travᵀ subKᵗ (ρ₂ ρ) (extρ subKᵗ (ρ₂ ρ) (r₂ e)) N
  body : ∀ {V W} (v : Value V) (w : Value W)
    → 𝒱 A ρ V W v w
    → ℰ B ρ (sub (exts tmK (γ₁ e)) N₁ [ V ]) (sub (exts tmK (γ₂ e)) N₂ [ W ])
  body {V} {W} v w rel =
    ℰ-cast {A = B} {ρ = ρ} (exts-[] (γ₁ e) N₁ V) (exts-[] (γ₂ e) N₂ W)
      (N-rel ρ (extEnv A e V W) (extEnv-𝒢 g v w rel))

compat-· : ∀ {ℓ Δ} {Γ : Ctx Δ} {A B}
  {L : Δ ∣ Γ ⊢ A ⇒ B} {M : Δ ∣ Γ ⊢ A}
  → LogicalRel ℓ L L
  → LogicalRel ℓ M M
  → LogicalRel ℓ (L · M) (L · M)
compat-· {A = A} {B = B} {L = L} {M = M} L-rel M-rel ρ e g =
  go (L-rel ρ e g) (M-rel ρ e g)
  where
  go : ℰ (A ⇒ B) ρ (close₁ e L) (close₂ e L)
    → ℰ A ρ (close₁ e M) (close₂ e M)
    → ℰ B ρ (close₁ e L · close₁ e M) (close₂ e L · close₂ e M)
  go ⟨ _ , ⟨ _ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ L↠ , ⟨ L↠′ , f ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
     ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M↠ , ⟨ M↠′ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ℰ-anti-↠ʳ {A = B} {ρ = ρ}
      (↠-trans (·₁-↠ L↠′)
        (↠-trans (·₂-↠ V-ƛ M↠′) (step-eq-↠ (β-ƛ w) refl)))
      (ℰ-anti-↠ˡ {A = B} {ρ = ρ}
        (↠-trans (·₁-↠ L↠)
          (↠-trans (·₂-↠ V-ƛ M↠) (step-eq-↠ (β-ƛ v) refl)))
        (f v w rel))

compat-Λ : ∀ {ℓ Δ} {Γ : Ctx Δ} {A} {N : Δ ,α ∣ ⇑ᶜ Γ ⊢ A}
  → LogicalRel ℓ N N
  → LogicalRel ℓ (Λ N) (Λ N)
compat-Λ {A = A} {N = N} N-rel ρ e g =
  𝒱⇒ℰ (`∀ A) ρ V-Λ V-Λ λ A₁ A₂ R →
    ℰ-cast {A = A} {ρ = extendRelSub ρ A₁ A₂ R}
      (Λ-close (ρ₁ ρ) A₁ (r₁ e) (γ₁ e) N)
      (Λ-close (ρ₂ ρ) A₂ (r₂ e) (γ₂ e) N)
      (N-rel (extendRelSub ρ A₁ A₂ R) (ΛEnv e A₁ A₂ R)
        (ΛEnv-𝒢 e A₁ A₂ R g))

--------------------------------------------------------------------------------
-- Closed terms
--------------------------------------------------------------------------------

-- the relational substitution and environment for closed terms
ρ∅ : ∀ {ℓ} → RelSub ℓ ∅
ρ₁ ρ∅ = idᵗ
ρ₂ ρ∅ = idᵗ
ρR ρ∅ ()

private
  r∅ : TyRen subKᵗ (idᵗ {∅}) ∅ ∅
  r∅ ()

  γ∅ : ∀ {A} → ∅ ∋ A → ∅ ∣ ∅ ⊢ A
  γ∅ ()

-- (both sides use the same maps, so `close₂ e∅ M` is `close₁ e∅ M`)
e∅ : ∀ {ℓ} → RelEnv ∅ (ρ∅ {ℓ})
e∅ = record
  { Γ₁ = ∅ ; Γ₂ = ∅ ; r₁ = r∅ ; r₂ = r∅ ; γ₁ = γ∅ ; γ₂ = γ∅ }

g∅ : ∀ {ℓ} → 𝒢 (ρ∅ {ℓ}) e∅
g∅ ()

-- closing a closed term changes nothing
close∅-≅ : ∀ {ℓ A} (M : ∅ ∣ ∅ ⊢ A) → close₁ (e∅ {ℓ}) M ≅ M
close∅-≅ M =
  H.trans (≡-to-≅ (sub-id (λ ()) (travᵀ subKᵗ idᵗ r∅ M)))
    (idᵀ {𝒯 = subKᵗ} {θ = idᵗ} {ρ = r∅}
      (record { ty-var = λ { () } ; ctx = refl ; var = λ () }) M)

close∅-eq : ∀ (A : Type ∅) → substᵗ idᵗ A ≡ A
close∅-eq A = sub-idᵗ (λ _ → refl) A

--------------------------------------------------------------------------------
-- The fundamental theorem, given compatibility with type application
--------------------------------------------------------------------------------

module Fundamental (compat-∙ : CompatInst) where

  fundamental : (ℓ : Level) → ∀ {Δ} {Γ : Ctx Δ} {A} (M : Δ ∣ Γ ⊢ A)
    → LogicalRel ℓ M M
  fundamental ℓ `true = compat-true
  fundamental ℓ `false = compat-false
  fundamental ℓ `zero = compat-zero
  fundamental ℓ (`suc M) = compat-suc {M = M} (fundamental ℓ M)
  fundamental ℓ (`case-nat L M N) =
    compat-case-nat {L = L} {M = M} {N = N}
      (fundamental ℓ L) (fundamental ℓ M) (fundamental ℓ N)
  fundamental ℓ (`if_then_else L M N) =
    compat-if {L = L} {M = M} {N = N}
      (fundamental ℓ L) (fundamental ℓ M) (fundamental ℓ N)
  fundamental ℓ (` x) = compat-var x
  fundamental ℓ (ƛ A ˙ N) = compat-ƛ {N = N} (fundamental ℓ N)
  fundamental ℓ (L · M) =
    compat-· {L = L} {M = M} (fundamental ℓ L) (fundamental ℓ M)
  fundamental ℓ (Λ N) = compat-Λ {N = N} (fundamental ℓ N)
  fundamental ℓ (M ∙ B) = compat-∙ {M = M} B (fundamental ℓ M)

  terminate : ∀ {A} (M : ∅ ∣ ∅ ⊢ A) → ∃[ V ] (M —↠ V) × Value V
  terminate {A} M
    with fundamental zero M ρ∅ e∅ g∅
  ... | ⟨ V , ⟨ _ , ⟨ v , ⟨ _ , ⟨ M↠V , ⟨ _ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ convᵀ (close∅-eq A) V
    , ⟨ ↠-≅ (close∅-eq A) (close∅-≅ {ℓ = zero} M) M↠V
      , Value-conv (close∅-eq A) v ⟩ ⟩

module proof.Reduction.Determinism where

-- File Charter:
--   * Determinism of reduction: a term's pure step, and its
--     store-changing step with the step's store change, are unique.
--   * Counted runs (`LR.Steps`): two runs of the same length agree; a
--     run stops at the first value it reaches; two runs to values have
--     the same length, store changes and value (`det-value-run`), also
--     against an uncounted run (`det-value-↠`).
--   * Results over different store sizes are compared as dependent
--     pairs (`Out`, `Outs`), so no heterogeneous equality is needed.
--   * Used by the logical relation's replay worlds (notes/logrel-dgg.md,
--     Section 7, "Design (W)"): a right run replayed from the same store
--     allocates the same variables and ends at the same value.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import CastTerms
open import Primitives using (δ; δ-add; δ-and)
open import Reduction
open import LR.Steps using (_—→^_[_]_; none; more)
open import proof.Reduction.ValueIrreducibleProof using (value-no-step)

------------------------------------------------------------------------
-- Pure steps
------------------------------------------------------------------------

δ-det : ∀ {op κ κ′ κ₁ κ₂} → δ op κ κ′ κ₁ → δ op κ κ′ κ₂ → κ₁ ≡ κ₂
δ-det δ-add δ-add = refl
δ-det δ-and δ-and = refl

blame-no-pure : ∀ {Δ} {N : Term Δ} → blame —→ N → ⊥
blame-no-pure ()

notValue-blame : ∀ {Δ} → Value (blame {Δ}) → ⊥
notValue-blame ()

det-pure : ∀ {Δ} {M N₁ N₂ : Term Δ} → M —→ N₁ → M —→ N₂ → N₁ ≡ N₂
det-pure (δ-⊕ d₁) (δ-⊕ d₂) with δ-det d₁ d₂
det-pure (δ-⊕ d₁) (δ-⊕ d₂) | refl = refl
det-pure (β v₁) (β v₂) = refl
det-pure (β v₁) (blame-·₂ v₂) = ⊥-elim (notValue-blame v₁)
det-pure (β-id v₁) (β-id v₂) = refl
det-pure (β-id v₁) blame-⟨⟩ = ⊥-elim (notValue-blame v₁)
det-pure (β-⇒ v₁ w₁) (β-⇒ v₂ w₂) = refl
det-pure (β-⇒ v₁ w₁) (blame-·₂ v₂) = ⊥-elim (notValue-blame w₁)
det-pure (β-∀ v₁ refl) (β-∀ v₂ refl) = refl
det-pure (ground ⦃ Gns = n₁ ⦄ v₁ ne₁) (ground ⦃ Gns = n₂ ⦄ v₂ ne₂)
  rewrite nonStar-unique n₁ n₂ = refl
det-pure (ground v₁ ne₁) blame-⟨⟩ = ⊥-elim (notValue-blame v₁)
det-pure (expand ⦃ Gns = n₁ ⦄ v₁ ne₁) (expand ⦃ Gns = n₂ ⦄ v₂ ne₂)
  rewrite nonStar-unique n₁ n₂ = refl
det-pure (expand v₁ ne₁) (tag-untag v₂) = ⊥-elim (ne₁ refl)
det-pure (expand v₁ ne₁) (tag-untag-bad v₂ ne₂) = ⊥-elim (ne₁ refl)
det-pure (expand v₁ ne₁) blame-⟨⟩ = ⊥-elim (notValue-blame v₁)
det-pure (tag-untag v₁) (expand v₂ ne₂) = ⊥-elim (ne₂ refl)
det-pure (tag-untag v₁) (tag-untag v₂) = refl
det-pure (tag-untag v₁) (tag-untag-bad v₂ ne₂) = ⊥-elim (ne₂ refl)
det-pure (tag-untag-bad v₁ ne₁) (expand v₂ ne₂) = ⊥-elim (ne₂ refl)
det-pure (tag-untag-bad v₁ ne₁) (tag-untag v₂) = ⊥-elim (ne₁ refl)
det-pure (tag-untag-bad v₁ ne₁) (tag-untag-bad v₂ ne₂) = refl
det-pure (blame-bot-intro v₁) (blame-bot-intro v₂) = refl
det-pure (blame-bot-intro v₁) blame-⟨⟩ = refl
det-pure (β-reveal-⇒ v₁ w₁) (β-reveal-⇒ v₂ w₂) = refl
det-pure (β-reveal-⇒ v₁ w₁) (blame-·₂ v₂) = ⊥-elim (notValue-blame w₁)
det-pure (β-conceal-⇒ v₁ w₁) (β-conceal-⇒ v₂ w₂) = refl
det-pure (β-conceal-⇒ v₁ w₁) (blame-·₂ v₂) = ⊥-elim (notValue-blame w₁)
det-pure (id-reveal v₁) (id-reveal v₂) = refl
det-pure (id-reveal v₁) blame-reveal = refl
det-pure (id-conceal v₁) (id-conceal v₂) = refl
det-pure (id-conceal v₁) blame-conceal = refl
det-pure (conceal-reveal v₁) (conceal-reveal v₂) = refl
det-pure blame-·₁ blame-·₁ = refl
det-pure blame-·₁ (blame-·₂ v₂) = refl
det-pure (blame-·₂ v₁) (β v₂) = ⊥-elim (notValue-blame v₂)
det-pure (blame-·₂ v₁) (β-⇒ v₂ w₂) = ⊥-elim (notValue-blame w₂)
det-pure (blame-·₂ v₁) (β-reveal-⇒ v₂ w₂) = ⊥-elim (notValue-blame w₂)
det-pure (blame-·₂ v₁) (β-conceal-⇒ v₂ w₂) = ⊥-elim (notValue-blame w₂)
det-pure (blame-·₂ v₁) blame-·₁ = refl
det-pure (blame-·₂ v₁) (blame-·₂ v₂) = refl
det-pure blame-• blame-• = refl
det-pure blame-⟨⟩ (β-id v₂) = ⊥-elim (notValue-blame v₂)
det-pure blame-⟨⟩ (ground v₂ ne₂) = ⊥-elim (notValue-blame v₂)
det-pure blame-⟨⟩ (expand v₂ ne₂) = ⊥-elim (notValue-blame v₂)
det-pure blame-⟨⟩ (blame-bot-intro v₂) = refl
det-pure blame-⟨⟩ blame-⟨⟩ = refl
det-pure blame-reveal (id-reveal v₂) = refl
det-pure blame-reveal blame-reveal = refl
det-pure blame-conceal (id-conceal v₂) = refl
det-pure blame-conceal blame-conceal = refl
det-pure blame-⊕₁ blame-⊕₁ = refl
det-pure blame-⊕₁ (blame-⊕₂ v₂) = refl
det-pure (blame-⊕₂ v₁) blame-⊕₁ = refl
det-pure (blame-⊕₂ v₁) (blame-⊕₂ v₂) = refl

------------------------------------------------------------------------
-- Store-changing steps
------------------------------------------------------------------------

-- a step's outcome: the new store size, the change and the term
Out : TyCtx → Set
Out Δ = Σ[ Δ′ ∈ TyCtx ] (StoreChange Δ Δ′ × Term Δ′)

blame-no-step : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → blame —→[ χ ] N → ⊥
blame-no-step (pure-step ())

-- a pure step against any step
pure-det : ∀ {Δ Δ′} {M N₁ : Term Δ} {χ : StoreChange Δ Δ′}
    {N₂ : Term Δ′}
  → M —→ N₁ → M —→[ χ ] N₂
  → _≡_ {A = Out Δ} (Δ , keep , N₁) (Δ′ , χ , N₂)
pure-det p (pure-step q) with det-pure p q
pure-det p (pure-step q) | refl = refl
pure-det blame-⟨⟩ (β-inst v B≢★) = ⊥-elim (notValue-blame v)
pure-det (β v) (ξ-·₁ s eq) = ⊥-elim (value-no-step (ƛ _) s)
pure-det (β v) (ξ-·₂ v′ s eq) = ⊥-elim (value-no-step v s)
pure-det (β-⇒ v w) (ξ-·₁ s eq) = ⊥-elim (value-no-step (v 《 fun 》) s)
pure-det (β-⇒ v w) (ξ-·₂ v′ s eq) = ⊥-elim (value-no-step w s)
pure-det (β-reveal-⇒ v w) (ξ-·₁ s eq) =
  ⊥-elim (value-no-step (v ↑ fun) s)
pure-det (β-reveal-⇒ v w) (ξ-·₂ v′ s eq) = ⊥-elim (value-no-step w s)
pure-det (β-conceal-⇒ v w) (ξ-·₁ s eq) =
  ⊥-elim (value-no-step (v ↓ fun) s)
pure-det (β-conceal-⇒ v w) (ξ-·₂ v′ s eq) = ⊥-elim (value-no-step w s)
pure-det blame-·₁ (ξ-·₁ s eq) = ⊥-elim (blame-no-step s)
pure-det blame-·₁ (ξ-·₂ v′ s eq) = ⊥-elim (notValue-blame v′)
pure-det (blame-·₂ v) (ξ-·₁ s eq) = ⊥-elim (value-no-step v s)
pure-det (blame-·₂ v) (ξ-·₂ v′ s eq) = ⊥-elim (blame-no-step s)
pure-det (β-∀ v refl) (ξ-• s eqB eqA) =
  ⊥-elim (value-no-step (v 《 all 》) s)
pure-det blame-• (ξ-• s eqB eqA) = ⊥-elim (blame-no-step s)
pure-det (β-id v) (ξ-⟨⟩ s eq) = ⊥-elim (value-no-step v s)
pure-det (ground v ne) (ξ-⟨⟩ s eq) = ⊥-elim (value-no-step v s)
pure-det (expand v ne) (ξ-⟨⟩ s eq) = ⊥-elim (value-no-step v s)
pure-det (tag-untag v) (ξ-⟨⟩ s eq) =
  ⊥-elim (value-no-step (v 《 inj 》) s)
pure-det (tag-untag-bad v ne) (ξ-⟨⟩ s eq) =
  ⊥-elim (value-no-step (v 《 inj 》) s)
pure-det (blame-bot-intro v) (ξ-⟨⟩ s eq) = ⊥-elim (value-no-step v s)
pure-det blame-⟨⟩ (ξ-⟨⟩ s eq) = ⊥-elim (blame-no-step s)
pure-det (id-reveal v) (ξ-reveal s eq) = ⊥-elim (value-no-step v s)
pure-det (conceal-reveal v) (ξ-reveal s eq) =
  ⊥-elim (value-no-step (v ↓ seal) s)
pure-det blame-reveal (ξ-reveal s eq) = ⊥-elim (blame-no-step s)
pure-det (id-conceal v) (ξ-conceal s eq) = ⊥-elim (value-no-step v s)
pure-det blame-conceal (ξ-conceal s eq) = ⊥-elim (blame-no-step s)
pure-det (δ-⊕ d) (ξ-⊕₁ s eq) = ⊥-elim (value-no-step ($ _) s)
pure-det (δ-⊕ d) (ξ-⊕₂ v′ s eq) = ⊥-elim (value-no-step ($ _) s)
pure-det blame-⊕₁ (ξ-⊕₁ s eq) = ⊥-elim (blame-no-step s)
pure-det blame-⊕₁ (ξ-⊕₂ v′ s eq) = ⊥-elim (notValue-blame v′)
pure-det (blame-⊕₂ v) (ξ-⊕₁ s eq) = ⊥-elim (value-no-step v s)
pure-det (blame-⊕₂ v) (ξ-⊕₂ v′ s eq) = ⊥-elim (blame-no-step s)

sym-out : ∀ {Δ} {o₁ o₂ : Out Δ} → o₁ ≡ o₂ → o₂ ≡ o₁
sym-out refl = refl

-- determinism of a store-changing step
det : ∀ {Δ Δ₁ Δ₂} {M : Term Δ}
    {χ₁ : StoreChange Δ Δ₁} {N₁ : Term Δ₁}
    {χ₂ : StoreChange Δ Δ₂} {N₂ : Term Δ₂}
  → M —→[ χ₁ ] N₁ → M —→[ χ₂ ] N₂
  → _≡_ {A = Out Δ} (Δ₁ , χ₁ , N₁) (Δ₂ , χ₂ , N₂)
det (pure-step p) s = pure-det p s
det (β-Λ v) (pure-step p) = sym-out (pure-det p (β-Λ v))
det (β-Λ v) (β-Λ v′) = refl
det (β-Λ v) (ξ-• s eqB eqA) = ⊥-elim (value-no-step (Λ v) s)
det (β-inst v B≢★) (pure-step p) = sym-out (pure-det p (β-inst v B≢★))
det (β-inst v B≢★) (β-inst v′ B≢★′) = refl
det (β-inst v B≢★) (ξ-⟨⟩ s eq) = ⊥-elim (value-no-step v s)
det (β-gen v A≢★ g) (pure-step p) = sym-out (pure-det p (β-gen v A≢★ g))
det (β-gen v A≢★ g) (β-gen v′ A≢★′ g′) = refl
det (β-gen v A≢★ g) (ξ-• s eqB eqA) =
  ⊥-elim (value-no-step (v 《 genᵥ A≢★ g 》) s)
det (β-reveal-∀ v) (pure-step p) = sym-out (pure-det p (β-reveal-∀ v))
det (β-reveal-∀ v) (β-reveal-∀ v′) = refl
det (β-reveal-∀ v) (ξ-• s eqB eqA) = ⊥-elim (value-no-step (v ↑ all) s)
det (β-conceal-∀ v) (pure-step p) = sym-out (pure-det p (β-conceal-∀ v))
det (β-conceal-∀ v) (β-conceal-∀ v′) = refl
det (β-conceal-∀ v) (ξ-• s eqB eqA) =
  ⊥-elim (value-no-step (v ↓ all) s)
det (ξ-·₁ s eq) (pure-step p) = sym-out (pure-det p (ξ-·₁ s eq))
det (ξ-·₁ s refl) (ξ-·₁ s′ refl) with det s s′
det (ξ-·₁ s refl) (ξ-·₁ s′ refl) | refl = refl
det (ξ-·₁ s eq) (ξ-·₂ v′ s′ eq′) = ⊥-elim (value-no-step v′ s)
det (ξ-·₂ v s eq) (pure-step p) = sym-out (pure-det p (ξ-·₂ v s eq))
det (ξ-·₂ v s eq) (ξ-·₁ s′ eq′) = ⊥-elim (value-no-step v s′)
det (ξ-·₂ v s refl) (ξ-·₂ v′ s′ refl) with det s s′
det (ξ-·₂ v s refl) (ξ-·₂ v′ s′ refl) | refl = refl
det (ξ-• s eqB eqA) (pure-step p) = sym-out (pure-det p (ξ-• s eqB eqA))
det (ξ-• s eqB eqA) (β-Λ v) = ⊥-elim (value-no-step (Λ v) s)
det (ξ-• s eqB eqA) (β-gen v A≢★ g) =
  ⊥-elim (value-no-step (v 《 genᵥ A≢★ g 》) s)
det (ξ-• s eqB eqA) (β-reveal-∀ v) = ⊥-elim (value-no-step (v ↑ all) s)
det (ξ-• s eqB eqA) (β-conceal-∀ v) =
  ⊥-elim (value-no-step (v ↓ all) s)
det (ξ-• s refl refl) (ξ-• s′ refl refl) with det s s′
det (ξ-• s refl refl) (ξ-• s′ refl refl) | refl = refl
det (ξ-⟨⟩ s eq) (pure-step p) = sym-out (pure-det p (ξ-⟨⟩ s eq))
det (ξ-⟨⟩ s eq) (β-inst v B≢★) = ⊥-elim (value-no-step v s)
det (ξ-⟨⟩ s refl) (ξ-⟨⟩ s′ refl) with det s s′
det (ξ-⟨⟩ s refl) (ξ-⟨⟩ s′ refl) | refl = refl
det (ξ-reveal s eq) (pure-step p) = sym-out (pure-det p (ξ-reveal s eq))
det (ξ-reveal s refl) (ξ-reveal s′ refl) with det s s′
det (ξ-reveal s refl) (ξ-reveal s′ refl) | refl = refl
det (ξ-conceal s eq) (pure-step p) =
  sym-out (pure-det p (ξ-conceal s eq))
det (ξ-conceal s refl) (ξ-conceal s′ refl) with det s s′
det (ξ-conceal s refl) (ξ-conceal s′ refl) | refl = refl
det (ξ-⊕₁ s eq) (pure-step p) = sym-out (pure-det p (ξ-⊕₁ s eq))
det (ξ-⊕₁ s refl) (ξ-⊕₁ s′ refl) with det s s′
det (ξ-⊕₁ s refl) (ξ-⊕₁ s′ refl) | refl = refl
det (ξ-⊕₁ s eq) (ξ-⊕₂ v′ s′ eq′) = ⊥-elim (value-no-step v′ s)
det (ξ-⊕₂ v s eq) (pure-step p) = sym-out (pure-det p (ξ-⊕₂ v s eq))
det (ξ-⊕₂ v s eq) (ξ-⊕₁ s′ eq′) = ⊥-elim (value-no-step v s′)
det (ξ-⊕₂ v s refl) (ξ-⊕₂ v′ s′ refl) with det s s′
det (ξ-⊕₂ v s refl) (ξ-⊕₂ v′ s′ refl) | refl = refl

------------------------------------------------------------------------
-- Counted runs
------------------------------------------------------------------------

-- a run's outcome: the new store size, the changes and the term
Outs : TyCtx → Set
Outs Δ = Σ[ Δ′ ∈ TyCtx ] (StoreChanges Δ Δ′ × Term Δ′)

-- two runs of the same length agree
det-steps : ∀ {Δ Δ₁ Δ₂ k} {M : Term Δ}
    {χs₁ : StoreChanges Δ Δ₁} {N₁ : Term Δ₁}
    {χs₂ : StoreChanges Δ Δ₂} {N₂ : Term Δ₂}
  → M —→^ k [ χs₁ ] N₁ → M —→^ k [ χs₂ ] N₂
  → _≡_ {A = Outs Δ} (Δ₁ , χs₁ , N₁) (Δ₂ , χs₂ , N₂)
det-steps none none = refl
det-steps (more s ss) (more s′ ss′) with det s s′
det-steps (more s ss) (more s′ ss′) | refl with det-steps ss ss′
det-steps (more s ss) (more s′ ss′) | refl | refl = refl

-- a run cannot go past a value it reaches
value-run-stops : ∀ {Δ Δ₁ Δ₂ j k} {M : Term Δ}
    {χs₁ : StoreChanges Δ Δ₁} {V : Term Δ₁}
    {χs₂ : StoreChanges Δ Δ₂} {N : Term Δ₂}
  → M —→^ j [ χs₁ ] V → Value V → M —→^ k [ χs₂ ] N → k ≤ j
value-run-stops r v none = z≤n
value-run-stops none v (more s ss) = ⊥-elim (value-no-step v s)
value-run-stops (more s ss) v (more s′ ss′) with det s s′
value-run-stops (more s ss) v (more s′ ss′) | refl =
  s≤s (value-run-stops ss v ss′)

-- two runs to values agree, in their length too
det-value-run : ∀ {Δ Δ₁ Δ₂ j k} {M : Term Δ}
    {χs₁ : StoreChanges Δ Δ₁} {V₁ : Term Δ₁}
    {χs₂ : StoreChanges Δ Δ₂} {V₂ : Term Δ₂}
  → M —→^ j [ χs₁ ] V₁ → Value V₁ → M —→^ k [ χs₂ ] V₂ → Value V₂
  → j ≡ k × _≡_ {A = Outs Δ} (Δ₁ , χs₁ , V₁) (Δ₂ , χs₂ , V₂)
det-value-run none v₁ none v₂ = refl , refl
det-value-run none v₁ (more s′ ss′) v₂ = ⊥-elim (value-no-step v₁ s′)
det-value-run (more s ss) v₁ none v₂ = ⊥-elim (value-no-step v₂ s)
det-value-run (more s ss) v₁ (more s′ ss′) v₂ with det s s′
det-value-run (more s ss) v₁ (more s′ ss′) v₂ | refl
  with det-value-run ss v₁ ss′ v₂
det-value-run (more s ss) v₁ (more s′ ss′) v₂ | refl | refl , refl =
  refl , refl

-- a counted run and an uncounted one to values agree
det-value-↠ : ∀ {Δ Δ₁ Δ₂ j} {M : Term Δ}
    {χs₁ : StoreChanges Δ Δ₁} {V₁ : Term Δ₁}
    {χs₂ : StoreChanges Δ Δ₂} {V₂ : Term Δ₂}
  → M —→^ j [ χs₁ ] V₁ → Value V₁ → M —↠[ χs₂ ] V₂ → Value V₂
  → _≡_ {A = Outs Δ} (Δ₁ , χs₁ , V₁) (Δ₂ , χs₂ , V₂)
det-value-↠ none v₁ ↠-refl v₂ = refl
det-value-↠ none v₁ (↠-step s′ ss′) v₂ = ⊥-elim (value-no-step v₁ s′)
det-value-↠ (more s ss) v₁ ↠-refl v₂ = ⊥-elim (value-no-step v₂ s)
det-value-↠ (more s ss) v₁ (↠-step s′ ss′) v₂ with det s s′
det-value-↠ (more s ss) v₁ (↠-step s′ ss′) v₂ | refl
  with det-value-↠ ss v₁ ss′ v₂
det-value-↠ (more s ss) v₁ (↠-step s′ ss′) v₂ | refl | refl = refl

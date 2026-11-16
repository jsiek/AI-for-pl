module nu-cancel-id.Eval where

-- File Charter:
--   * A FUEL-BOUNDED EVALUATOR for closed, well-typed νF₁ᶜ terms.  Each
--     step is the one `progress` finds, and `preservation` types the
--     next state, so the evaluator needs no type checker of its own.
--   * It returns the run it took, the context the run ends at (with the
--     cells it allocated), and the value; or `nothing` when the fuel
--     runs out first.  Examples.agda checks it on the five examples,
--     with exactly the fuel each run needs.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)

open import nu-cancel-id.Types using (Ty)
open import nu-cancel-id.Ctx using (Ctx)
open import nu-cancel-id.Terms using (Term; _∣_⊢_⦂_)
open import nu-cancel-id.Reduction
  using (Value; _⊢_—↠_⊣_; _∎; _—→⟨_⟩_)
open import nu-cancel-id.Progress using (progress)
open import nu-cancel-id.Preservation using (preservation)

record Result (Γ : Ctx) (M : Term) : Set where
  constructor result
  field
    {ctx}  : Ctx
    {term} : Term
    run    : Γ ⊢ M —↠ term ⊣ ctx
    value  : Value term

open Result public

eval : ∀ {Γ : Ctx} {M : Term} {A : Ty}
  → ℕ → Γ ∣ [] ⊢ M ⦂ A → Maybe (Result Γ M)
eval {M = M} fuel ⊢M with progress ⊢M
eval {M = M} fuel    ⊢M | inj₁ v = just (result (M ∎) v)
eval         zero    ⊢M | inj₂ _ = nothing
eval {M = M} (suc n) ⊢M | inj₂ (N , a , M⟶N) =
  map (λ { (result rs v) → result (M —→⟨ M⟶N ⟩ rs) v })
      (eval n (preservation ⊢M M⟶N))

-- where a run ends: its context and its value, if fuel suffices
outcome : ∀ {Γ : Ctx} {M : Term} {A : Ty}
  → ℕ → Γ ∣ [] ⊢ M ⦂ A → Maybe (Ctx × Term)
outcome n ⊢M = map (λ r → ctx r , term r) (eval n ⊢M)

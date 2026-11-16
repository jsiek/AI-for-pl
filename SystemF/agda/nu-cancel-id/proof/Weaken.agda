module nu-cancel-id.proof.Weaken where

-- File Charter:
--   * TYPING SURVIVES TWO CHANGES OF THE STORE.
--     §1 inserting an UNNAMED cell at depth k (`insΓ`), which is what an
--     allocation does to the redex's siblings (k = 0) and to a ν's
--     conversion (k = 1), and what `crossΛ` does to a copy under `Λ`.
--     Cells at depth ≥ k shift (`extⁿ k suc`); names do not move, so
--     named types are unchanged.
--     §2 REFINING an abstract cell to a payload (`_⊑_`), which is what
--     TyBeta does to the `Λ`'s cell.
--   * Both are proved for payload lookup, conversions and terms.

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.proof.Types
open import nu-cancel-id.proof.Flags

private
  variable
    Γ : Ctx
    Σ Σ′ : Store
    Φ : Flags
    Γₜ : List Ty
    p q : Payload
    s : Sign
    α : ℕ
    A P Q R S : Ty
    c : Conv
    M : Term

∋-unique : Σ ∋ α := P → Σ ∋ α := Q → P ≡ Q
∋-unique p-here      p-here      = refl
∋-unique (p-there x) (p-there y) = cong ⇑ᵗ (∋-unique x y)

------------------------------------------------------------------------
-- 1. Inserting an unnamed cell at depth k
------------------------------------------------------------------------

renPay : ℕ → Payload → Payload
renPay k abs     = abs
renPay k (pay P) = pay (renameᵗ (extⁿ k suc) P)

-- a payload newer than the insertion point is renamed past it
insˢ : ℕ → Payload → Store → Store
insˢ zero    p Σ       = p ∷ Σ
insˢ (suc k) p []      = []
insˢ (suc k) p (q ∷ Σ) = renPay k q ∷ insˢ k p Σ

insΓ : ℕ → Payload → Ctx → Ctx
insΓ k p Γ = insˢ k p (store Γ) ∣ insᶠ k (flags Γ)

ins-∋ : ∀ k → Σ ∋ α := P
  → insˢ k p Σ ∋ extⁿ k suc α := renameᵗ (extⁿ k suc) P
ins-∋ zero p-here       = p-there p-here
ins-∋ zero (p-there x)  = p-there (p-there x)
ins-∋ {p = p} (suc k) (p-here {P = P} {Σ = Σ}) =
  subst (λ T → (pay (renameᵗ (extⁿ k suc) P) ∷ insˢ k p Σ) ∋ zero := T)
        (⇑-ren (extⁿ k suc) P) p-here
ins-∋ {α = suc α} {p = p} (suc k)
      (p-there {Σ = Σ} {α = α} {P = P} {p = q} x) =
  subst (λ T → (renPay k q ∷ insˢ k p Σ) ∋ suc (extⁿ k suc α) := T)
        (⇑-ren (extⁿ k suc) P) (p-there (ins-∋ k x))

ins-conv : ∀ k → Σ ∣ s , α ⊢ c ⦂ R ⟹ S
  → insˢ k p Σ ∣ s , extⁿ k suc α
      ⊢ c ⦂ renameᵗ (extⁿ k suc) R ⟹ renameᵗ (extⁿ k suc) S
ins-conv k c-id         = c-id
ins-conv k (c-fun c d)  = c-fun (ins-conv k c) (ins-conv k d)
ins-conv k (c-all c)    = c-all (ins-conv (suc k) c)
ins-conv k (c-seal x)   = c-seal (ins-∋ k x)
ins-conv k (c-unseal x) = c-unseal (ins-∋ k x)

ins-interior : ∀ k s α p Γ
  → insΓ k p (interior s α Γ) ≡ interior s (extⁿ k suc α) (insΓ k p Γ)
ins-interior k s α p Γ =
  cong (insˢ k p (store Γ) ∣_) (ins-setFlag k α (inside s) (flags Γ))

ins-⊢ : ∀ k → Γ ∣ Γₜ ⊢ M ⦂ A
  → insΓ k p Γ ∣ Γₜ ⊢ renameʳ (extⁿ k suc) M ⦂ A
ins-⊢ k (⊢` x)       = ⊢` x
ins-⊢ k ⊢nat         = ⊢nat
ins-⊢ k ⊢bool        = ⊢bool
ins-⊢ k (⊢ƛ sp ⊢N)   = ⊢ƛ (ins-⇝ k sp) (ins-⊢ k ⊢N)
ins-⊢ k (⊢· ⊢L ⊢M)   = ⊢· (ins-⊢ k ⊢L) (ins-⊢ k ⊢M)
ins-⊢ k (⊢Λ ⊢N)      = ⊢Λ (ins-⊢ (suc k) ⊢N)
ins-⊢ k (⊢ν sp ⊢L spC spB ⊢c) =
  ⊢ν (ins-⇝ k sp) (ins-⊢ k ⊢L) (ins-⇝ (suc k) spC) (ins-⇝ (suc k) spB)
     (ins-conv (suc k) ⊢c)
ins-⊢ {Γ = Γ} {p = p} k (⊢[] {α = α} {s = s} coh ⊢M spA spB ⊢c) =
  ⊢[] (ins-∋ᶠ k coh)
      (subst (λ Δ → Δ ∣ [] ⊢ _ ⦂ _) (ins-interior k s α p Γ) (ins-⊢ k ⊢M))
      (subst (λ Φ → Φ ⊢ _ ⇝ _) (ins-setFlag k α (inside s) (flags Γ))
             (ins-⇝ k spA))
      (ins-⇝ k spB)
      (ins-conv k ⊢c)

-- the sibling shift of a step that allocates
⊢↑ᵃ : ∀ a → Γ ∣ Γₜ ⊢ M ⦂ A → a ⨾ Γ ∣ Γₜ ⊢ ↑ᵃ a M ⦂ A
⊢↑ᵃ keep    ⊢M = ⊢M
⊢↑ᵃ (new P) ⊢M = ins-⊢ zero ⊢M

------------------------------------------------------------------------
-- 2. Refining an abstract cell to a payload
------------------------------------------------------------------------

infix 4 _⊑_
data _⊑_ : Store → Store → Set where
  ⊑-[]   : [] ⊑ []
  ⊑-abs  : Σ ⊑ Σ′ → (abs ∷ Σ) ⊑ (p ∷ Σ′)
  ⊑-same : Σ ⊑ Σ′ → (p ∷ Σ) ⊑ (p ∷ Σ′)

⊑-refl : ∀ Σ → Σ ⊑ Σ
⊑-refl []      = ⊑-[]
⊑-refl (p ∷ Σ) = ⊑-same (⊑-refl Σ)

⊑-∋ : Σ ⊑ Σ′ → Σ ∋ α := P → Σ′ ∋ α := P
⊑-∋ (⊑-same r) p-here      = p-here
⊑-∋ (⊑-abs r)  (p-there x) = p-there (⊑-∋ r x)
⊑-∋ (⊑-same r) (p-there x) = p-there (⊑-∋ r x)

⊑-conv : Σ ⊑ Σ′ → Σ ∣ s , α ⊢ c ⦂ R ⟹ S → Σ′ ∣ s , α ⊢ c ⦂ R ⟹ S
⊑-conv r c-id         = c-id
⊑-conv r (c-fun c d)  = c-fun (⊑-conv r c) (⊑-conv r d)
⊑-conv r (c-all c)    = c-all (⊑-conv (⊑-same r) c)
⊑-conv r (c-seal x)   = c-seal (⊑-∋ r x)
⊑-conv r (c-unseal x) = c-unseal (⊑-∋ r x)

⊑-⊢ : Σ ⊑ Σ′ → (Σ ∣ Φ) ∣ Γₜ ⊢ M ⦂ A → (Σ′ ∣ Φ) ∣ Γₜ ⊢ M ⦂ A
⊑-⊢ r (⊢` x)       = ⊢` x
⊑-⊢ r ⊢nat         = ⊢nat
⊑-⊢ r ⊢bool        = ⊢bool
⊑-⊢ r (⊢ƛ sp ⊢N)   = ⊢ƛ sp (⊑-⊢ r ⊢N)
⊑-⊢ r (⊢· ⊢L ⊢M)   = ⊢· (⊑-⊢ r ⊢L) (⊑-⊢ r ⊢M)
⊑-⊢ r (⊢Λ ⊢N)      = ⊢Λ (⊑-⊢ (⊑-same r) ⊢N)
⊑-⊢ r (⊢ν sp ⊢L spC spB ⊢c) =
  ⊢ν sp (⊑-⊢ r ⊢L) spC spB (⊑-conv (⊑-same r) ⊢c)
⊑-⊢ r (⊢[] coh ⊢M spA spB ⊢c) =
  ⊢[] coh (⊑-⊢ r ⊢M) spA spB (⊑-conv r ⊢c)

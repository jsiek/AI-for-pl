module nu-cancel-id.proof.Subst where

-- File Charter:
--   * BETA'S SUBSTITUTION PRESERVES TYPES.  A closed value `V : A`
--     replaces term variable `length Δ₁` in a term typed under
--     `Δ₁ ++ A ∷ Δ₂`.  Under a `Λ` the copy is `crossΛ V`, which hides the
--     `Λ`'s cell, so the copy is typed with every name it had: its
--     body by weakening with an unnamed cell, its exterior type `⇑ᵗ A`
--     read with the `Λ`'s name in front.
--   * §1 list lemmas; §2 extending a term context at the end; §3 the
--     variable case; §4 `crossΛ`; §5 the substitution lemma.

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.proof.Types
open import nu-cancel-id.proof.Flags
open import nu-cancel-id.proof.Weaken

private
  variable
    Γ : Ctx
    Γₜ Γₜ′ Δ₁ Δ₂ : List Ty
    x : ℕ
    A B R : Ty
    M N V : Term

------------------------------------------------------------------------
-- 1. Lists
------------------------------------------------------------------------

map-++ : ∀ (f : Ty → Ty) (xs ys : List Ty)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

length-map : ∀ (f : Ty → Ty) (xs : List Ty) → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

∋ˣ-++ : Γₜ ∋ˣ x ⦂ A → Γₜ ++ Γₜ′ ∋ˣ x ⦂ A
∋ˣ-++ x-here      = x-here
∋ˣ-++ (x-there l) = x-there (∋ˣ-++ l)

------------------------------------------------------------------------
-- 2. Extending a term context at the end
------------------------------------------------------------------------

⊢-extend : Γ ∣ Γₜ ⊢ M ⦂ A → Γ ∣ Γₜ ++ Γₜ′ ⊢ M ⦂ A
⊢-extend (⊢` l)         = ⊢` (∋ˣ-++ l)
⊢-extend ⊢nat           = ⊢nat
⊢-extend ⊢bool          = ⊢bool
⊢-extend (⊢ƛ sp ⊢N)     = ⊢ƛ sp (⊢-extend ⊢N)
⊢-extend (⊢· ⊢L ⊢M)     = ⊢· (⊢-extend ⊢L) (⊢-extend ⊢M)
⊢-extend {Γₜ′ = Γₜ′} (⊢Λ {Γₜ = Γₜ} ⊢N) =
  ⊢Λ (subst (λ Δ → _ ∣ Δ ⊢ _ ⦂ _) (sym (map-++ ⇑ᵗ Γₜ Γₜ′)) (⊢-extend ⊢N))
⊢-extend (⊢ν sp ⊢L spC spB ⊢c) = ⊢ν sp (⊢-extend ⊢L) spC spB ⊢c
⊢-extend (⊢[] coh ⊢M spA spB ⊢c) = ⊢[] coh ⊢M spA spB ⊢c

------------------------------------------------------------------------
-- 3. The variable case
------------------------------------------------------------------------

var-subst : ∀ Δ₁ {Δ₂ A B x}
  → Δ₁ ++ A ∷ Δ₂ ∋ˣ x ⦂ B
  → (hitVar x (length Δ₁) ≡ hit × B ≡ A)
    ⊎ ∃[ y ] (hitVar x (length Δ₁) ≡ miss y × Δ₁ ++ Δ₂ ∋ˣ y ⦂ B)
var-subst []       x-here      = inj₁ (refl , refl)
var-subst []       (x-there l) = inj₂ (_ , refl , l)
var-subst (C ∷ Δ₁) x-here      = inj₂ (_ , refl , x-here)
var-subst (C ∷ Δ₁) (x-there l) with var-subst Δ₁ l
var-subst (C ∷ Δ₁) (x-there {x = x} l) | inj₁ (eq , refl) =
  inj₁ (cong sucHit eq , refl)
var-subst (C ∷ Δ₁) (x-there {x = x} l) | inj₂ (y , eq , l′) =
  inj₂ (suc y , cong sucHit eq , x-there l′)

------------------------------------------------------------------------
-- 4. A copy under `Λ`
------------------------------------------------------------------------

⊢crossΛ : Γ ∣ [] ⊢ V ⦂ A
  → flags Γ ⊢ A ⇝ R
  → underΛ Γ ∣ [] ⊢ crossΛ V ⦂ ⇑ᵗ A
⊢crossΛ ⊢V sp = ⊢[] f-here (ins-⊢ zero ⊢V) (ins-⇝ zero sp) (⇑-⇝ zero sp) c-id

------------------------------------------------------------------------
-- 5. Substitution
------------------------------------------------------------------------

subst-pres : ∀ Δ₁ {Γ Δ₂ A B N V R}
  → Γ ∣ Δ₁ ++ A ∷ Δ₂ ⊢ N ⦂ B
  → Γ ∣ [] ⊢ V ⦂ A
  → flags Γ ⊢ A ⇝ R
  → Γ ∣ Δ₁ ++ Δ₂ ⊢ substᵐ (length Δ₁) V N ⦂ B
subst-pres Δ₁ (⊢` {x = x} l) ⊢V sp with var-subst Δ₁ l
subst-pres Δ₁ (⊢` {x = x} l) ⊢V sp | inj₁ (eq , refl) rewrite eq =
  ⊢-extend ⊢V
subst-pres Δ₁ (⊢` {x = x} l) ⊢V sp | inj₂ (y , eq , l′) rewrite eq = ⊢` l′
subst-pres Δ₁ ⊢nat         ⊢V sp = ⊢nat
subst-pres Δ₁ ⊢bool        ⊢V sp = ⊢bool
subst-pres Δ₁ (⊢ƛ {A = C} spC ⊢N) ⊢V sp =
  ⊢ƛ spC (subst-pres (C ∷ Δ₁) ⊢N ⊢V sp)
subst-pres Δ₁ (⊢· ⊢L ⊢M)   ⊢V sp =
  ⊢· (subst-pres Δ₁ ⊢L ⊢V sp) (subst-pres Δ₁ ⊢M ⊢V sp)
subst-pres Δ₁ {Δ₂ = Δ₂} {A = A} {V = V} (⊢Λ {N = N} ⊢N) ⊢V sp =
  ⊢Λ (cast (sym (map-++ ⇑ᵗ Δ₁ Δ₂))
           (cong (λ j → substᵐ j (crossΛ V) N) (length-map ⇑ᵗ Δ₁))
       (subst-pres (map ⇑ᵗ Δ₁)
          (subst (λ Δ → _ ∣ Δ ⊢ _ ⦂ _) (map-++ ⇑ᵗ Δ₁ (A ∷ Δ₂)) ⊢N)
          (⊢crossΛ ⊢V sp) (⇑-⇝ zero sp)))
  where
  cast : ∀ {Γ Δ Δ′ M M′ C}
    → Δ ≡ Δ′ → M ≡ M′ → Γ ∣ Δ ⊢ M ⦂ C → Γ ∣ Δ′ ⊢ M′ ⦂ C
  cast refl refl ⊢M = ⊢M
subst-pres Δ₁ (⊢ν spA ⊢L spC spB ⊢c) ⊢V sp =
  ⊢ν spA (subst-pres Δ₁ ⊢L ⊢V sp) spC spB ⊢c
subst-pres Δ₁ (⊢[] coh ⊢M spA spB ⊢c) ⊢V sp = ⊢[] coh ⊢M spA spB ⊢c

module proof.Denot.EagerCast where

-- File Charter:
--   * `eager c` is in eager normal form (`Denot.EagerCast`).
--   * Renaming preserves the normal form and the shape of the head, so
--     the swapped body of `genᴱ` stays normal; transport along an
--     equation of types preserves both as well.

open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

open import Types
open import Consistency
open import Denot.EagerCast
open import proof.Denot.SwapRename

------------------------------------------------------------------------
-- Transport
------------------------------------------------------------------------

eager-subst-left : ∀ {Δ} {μ : Env∼ Δ} {A A′ B : Ty Δ}
  → (e : A ≡ A′) {c : μ ⊢ A ∼ B}
  → Eager c → Eager (subst-left-∼ e c)
eager-subst-left refl Ec = Ec

eager-subst-right : ∀ {Δ} {μ : Env∼ Δ} {A B B′ : Ty Δ}
  → (e : B ≡ B′) {c : μ ⊢ A ∼ B}
  → Eager c → Eager (subst-right-∼ e c)
eager-subst-right refl Ec = Ec

notInst-subst-left : ∀ {Δ} {μ : Env∼ Δ} {A A′ B : Ty Δ}
  → (e : A ≡ A′) {c : μ ⊢ A ∼ B}
  → NotInst c → NotInst (subst-left-∼ e c)
notInst-subst-left refl n = n

notInst-subst-right : ∀ {Δ} {μ : Env∼ Δ} {A B B′ : Ty Δ}
  → (e : B ≡ B′) {c : μ ⊢ A ∼ B}
  → NotInst c → NotInst (subst-right-∼ e c)
notInst-subst-right refl n = n

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

rename-notInst : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ (ρ X) ≡ μ X)
  → (c : μ ⊢ A ∼ B)
  → NotInst c → NotInst (rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
rename-notInst ρ eq (id ★) n = tt
rename-notInst ρ eq (id (‵ ι)) n = tt
rename-notInst ρ eq (id (＇ X)) n = tt
rename-notInst ρ eq (c ↦ d) n = tt
rename-notInst ρ eq (∀ᶜ c) n = tt
rename-notInst ρ eq (c !) n = tt
rename-notInst ρ eq (？ c) n = tt
rename-notInst ρ eq ((inst c) B≢★) ()
rename-notInst ρ eq ((gen c) A≢★) n = tt
rename-notInst ρ eq bot-elim n = tt
rename-notInst ρ eq bot-intro n = tt

rename-eager : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ (ρ X) ≡ μ X)
  → {c : μ ⊢ A ∼ B}
  → Eager c → Eager (rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
rename-eager ρ eq (e-id {a = ★}) = e-id
rename-eager ρ eq (e-id {a = ‵ ι}) = e-id
rename-eager ρ eq (e-id {a = ＇ X}) = e-id
rename-eager {μ = μ} {μ′ = μ′} ρ eq (e-↦ Ec Ed) =
  e-↦ (rename-eager {μ = flipᵐ μ} {μ′ = flipᵐ μ′} ρ
         (flip-rename-env {μ = μ} {μ′ = μ′} ρ eq) Ec)
      (rename-eager {μ = μ} {μ′ = μ′} ρ eq Ed)
rename-eager {μ = μ} {μ′ = μ′} ρ eq (e-∀ Ec) =
  e-∀ (rename-eager {μ = extᵐ μ} {μ′ = extᵐ μ′} (extᵗ ρ)
    (extᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) Ec)
rename-eager {μ = μ} {μ′ = μ′} ρ eq (e-! Ec) =
  e-! ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ (rename-eager {μ = μ} {μ′ = μ′} ρ eq Ec)
rename-eager {μ = μ} {μ′ = μ′} ρ eq (e-？ Ec) =
  e-？ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ (rename-eager {μ = μ} {μ′ = μ′} ρ eq Ec)
rename-eager {μ = μ} {μ′ = μ′} ρ eq (e-inst {B = B} Ec) =
  e-inst ⦃ _ ⦄ ⦃ _ ⦄ (eager-subst-right (renameᵗ-shift ρ B)
    (rename-eager {μ = instᵐ μ} {μ′ = instᵐ μ′} (extᵗ ρ)
      (instᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) Ec))
rename-eager {μ = μ} {μ′ = μ′} ρ eq (e-gen {A = A} {c = c} Ec n) =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄
    (eager-subst-left (renameᵗ-shift ρ A)
      (rename-eager {μ = genᵐ μ} {μ′ = genᵐ μ′} (extᵗ ρ)
        (genᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) Ec))
    (notInst-subst-left (renameᵗ-shift ρ A)
      (rename-notInst {μ = genᵐ μ} {μ′ = genᵐ μ′} (extᵗ ρ)
        (genᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c n))
rename-eager ρ eq e-bot-elim = e-bot-elim
rename-eager ρ eq e-bot-intro = e-bot-intro

------------------------------------------------------------------------
-- genᴱ
------------------------------------------------------------------------

-- the plain case: a gen over the renamed body
plain : ∀ {Δ Δ′} {ν : Env∼ Δ} {μ : Env∼ Δ′} {C B : Ty Δ}
  → (ρ : Δ ⇒ʳ _) (eq : ∀ X → genᵐ μ (ρ X) ≡ ν X)
  → (c : ν ⊢ C ∼ B) (A : Ty Δ′) (eC : renameᵗ ρ C ≡ ⇑ᵗ A)
  → Eager c → NotInst c
  → Eager (subst-left-∼ eC (rename∼ {μ = ν} {μ′ = genᵐ μ} ρ eq c))
      × NotInst (subst-left-∼ eC (rename∼ {μ = ν} {μ′ = genᵐ μ} ρ eq c))
plain {ν = ν} {μ = μ} ρ eq c A eC Ec n =
  eager-subst-left eC (rename-eager {μ = ν} {μ′ = genᵐ μ} ρ eq Ec) ,
  notInst-subst-left eC (rename-notInst {μ = ν} {μ′ = genᵐ μ} ρ eq c n)

genᴱ-eager : ∀ {Δ Δ′} {ν : Env∼ Δ} {μ : Env∼ Δ′} {C B : Ty Δ}
  → (ρ : Δ ⇒ʳ _) (inj : ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → (eq : ∀ X → genᵐ μ (ρ X) ≡ ν X)
  → (c : ν ⊢ C ∼ B) (A : Ty Δ′) (eC : renameᵗ ρ C ≡ ⇑ᵗ A)
  → (A≢★ : A ≢ ★) (nv : NonVar (renameᵗ ρ B))
  → (z : _ ∈ᵗ renameᵗ ρ B)
  → Eager c
  → Eager (genᴱ {ν = ν} {μ = μ} ρ inj eq c A eC A≢★ nv z)
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@(id a) A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@(c₁ ↦ c₂) A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@(∀ᶜ c₁) A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@(c₁ !) A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@(？ c₁) A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@((gen c₁) C≢★) A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@bot-elim A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} ρ inj eq c@bot-intro A eC A≢★ nv z Ec =
  e-gen ⦃ _ ⦄ ⦃ _ ⦄ (proj₁ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
    (proj₂ (plain {ν = ν} {μ = μ} ρ eq c A eC Ec tt))
genᴱ-eager {ν = ν} {μ = μ} {B = B} ρ inj eq
    ((inst_ ⦃ C₁nv ⦄ ⦃ z∈C₁ ⦄ d) B≢★) (`∀ C₀) eC A≢★ nv z (e-inst Ed) =
  e-inst ⦃ _ ⦄ ⦃ _ ⦄ (eager-subst-right (cong `∀ (liftSwap-target ρ B))
    (genᴱ-eager {ν = instᵐ ν} {μ = instᵐ μ} (liftSwap ρ)
      (liftSwap-injective inj)
      (liftSwap-env {ν = ν} {μ = μ} ρ eq) d C₀
      (liftSwap-source ρ (ty-all-inj eC))
      (∈→≢★ (swap-occurs ρ inj (ty-all-inj eC) z∈C₁))
      (swap-target-nonvar ρ B nv)
      (swap-target-occurs ρ B z) Ed))
genᴱ-eager ρ inj eq ((inst d) B≢★) (＇ X) () A≢★ nv z Ec
genᴱ-eager ρ inj eq ((inst d) B≢★) (‵ ι) () A≢★ nv z Ec
genᴱ-eager ρ inj eq ((inst d) B≢★) ★ () A≢★ nv z Ec
genᴱ-eager ρ inj eq ((inst d) B≢★) (A₁ ⇒ A₂) () A≢★ nv z Ec

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

eager-eager : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B) → Eager (eager c)
eager-eager (id a) = e-id
eager-eager (c ↦ d) = e-↦ (eager-eager c) (eager-eager d)
eager-eager (∀ᶜ c) = e-∀ (eager-eager c)
eager-eager (c !) = e-! (eager-eager c)
eager-eager (？ c) = e-？ (eager-eager c)
eager-eager ((inst c) B≢★) = e-inst (eager-eager c)
eager-eager {μ = μ} ((gen_ {A = A} {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) A≢★) =
  eager-subst-right (cong `∀ (renameᵗ-id B))
    (genᴱ-eager {ν = genᵐ μ} {μ = μ} (λ X → X) (λ e → e) (λ X → refl)
      (eager c) A
      (renameᵗ-id (⇑ᵗ A)) A≢★ _ _ (eager-eager c))
eager-eager bot-elim = e-bot-elim
eager-eager bot-intro = e-bot-intro

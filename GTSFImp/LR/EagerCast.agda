module LR.EagerCast where

-- File Charter:
--   * The eager normal form of consistency casts
--     (notes/denotational-dgg.md, Section 7a): no `gen` has an `inst`
--     directly as its body.  `Eager c` is the predicate; as a grammar,
--       c ::= id | c ↦ c | ∀ᶜ c | c ! | ？ c | inst c | gen g | bot-elim
--           | bot-intro
--       g ::= c ↦ c | ∀ᶜ c | gen g        (with `GenSafe`, the rest
--                                          of a gen body's heads are
--                                          impossible by typing)
--   * `eager c` normalizes: it swaps `gen (inst d)` to `inst (gen d̃)`,
--     where `d̃` is `d` with the two innermost variables exchanged
--     (`proof.LR.SwapRename`).  It derives the same judgement.
--   * `genᴱ` builds the normal form of a `gen` over an already normal
--     body that is read through a renaming.  It is structural in the
--     body, which is why the renaming is a parameter: the swapped body
--     `d̃` is never constructed before it is normalized.
--   * The theorem that `eager c` is in normal form is in
--     `proof.LR.EagerCast`.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Nat using () renaming (suc to sucℕ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types
open import Consistency
open import proof.ImprecisionConsistency
  using (fin-suc-injective; ext-injective; rename-occurs;
         unrename-occurs)
open import proof.LR.SwapRename

------------------------------------------------------------------------
-- The normal form
------------------------------------------------------------------------

-- the head is not `inst`
NotInst : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
NotInst (id a) = ⊤
NotInst (c ↦ d) = ⊤
NotInst (∀ᶜ c) = ⊤
NotInst (c !) = ⊤
NotInst (？ c) = ⊤
NotInst ((inst c) B≢★) = ⊥
NotInst ((gen c) A≢★) = ⊤
NotInst bot-elim = ⊤
NotInst bot-intro = ⊤

data Eager : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set where
  e-id : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {a : Atom A}
    → Eager {μ = μ} (id a)

  e-↦ : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Eager c → Eager d
    → Eager (c ↦ d)

  e-∀ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (sucℕ Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
    → Eager c
    → Eager (∀ᶜ c)

  e-! : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄ {c : μ ⊢ A ∼ G}
      ⦃ Ans : NonStar A ⦄
    → Eager c
    → Eager (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)

  e-？ : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄ {c : μ ⊢ G ∼ B}
      ⦃ Bns : NonStar B ⦄
    → Eager c
    → Eager (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)

  e-inst : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (sucℕ Δ)} {B : Ty Δ}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B} {B≢★ : B ≢ ★}
    → Eager c
    → Eager ((inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) B≢★)

  e-gen : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {B : Ty (sucℕ Δ)}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B} {A≢★ : A ≢ ★}
    → Eager c
    → NotInst c
    → Eager ((gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) A≢★)

  e-bot-elim : ∀ {Δ} {μ : Env∼ Δ} → Eager {Δ} {μ} bot-elim

  e-bot-intro : ∀ {Δ} {μ : Env∼ Δ} → Eager {Δ} {μ} bot-intro

------------------------------------------------------------------------
-- A gen over a normal body, read through a renaming
------------------------------------------------------------------------

-- The pieces of the swap case, named so that proofs can refer to them.
-- `C₁` is the body of the `inst`'s source and `C₀` the instantiated
-- source after the swap.
ty-all-inj : ∀ {Δ} {X Y : Ty (sucℕ Δ)} → `∀ X ≡ `∀ Y → X ≡ Y
ty-all-inj refl = refl

swap-nonvar : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′)
    {C₁ : Ty (sucℕ Δ)} {C₀ : Ty (sucℕ Δ′)}
  → renameᵗ (extᵗ ρ) C₁ ≡ renameᵗ (extᵗ suc) C₀
  → NonVar C₁
  → NonVar C₀
swap-nonvar ρ e C₁nv =
  unrenameNonVar (extᵗ suc) (subst NonVar e (renameNonVar (extᵗ ρ) C₁nv))

swap-occurs : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′)
    {C₁ : Ty (sucℕ Δ)} {C₀ : Ty (sucℕ Δ′)}
  → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → renameᵗ (extᵗ ρ) C₁ ≡ renameᵗ (extᵗ suc) C₀
  → zero ∈ᵗ C₁
  → zero ∈ᵗ C₀
swap-occurs ρ inj e z∈C₁ = unshift-zero
  (subst (zero ∈ᵗ_) e (rename-occurs (extᵗ ρ) (ext-injective inj) z∈C₁))

swap-target-nonvar : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′) (B : Ty Δ)
  → NonVar (renameᵗ ρ B)
  → NonVar (renameᵗ (liftSwap ρ) (⇑ᵗ B))
swap-target-nonvar ρ B nv =
  subst NonVar (sym (liftSwap-target ρ B)) (renameNonVar (extᵗ suc) nv)

swap-target-occurs : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′) (B : Ty Δ)
  → zero ∈ᵗ renameᵗ ρ B
  → zero ∈ᵗ renameᵗ (liftSwap ρ) (⇑ᵗ B)
swap-target-occurs ρ B z =
  subst (zero ∈ᵗ_) (sym (liftSwap-target ρ B))
    (rename-occurs (extᵗ suc) (ext-injective fin-suc-injective) z)

-- `genᴱ ρ … c A …` is the normal form of `gen (rename ρ c)`.  The
-- variable that `gen` binds is `ρ`'s preimage of zero.
genᴱ : ∀ {Δ Δ′} {ν : Env∼ Δ} {μ : Env∼ Δ′} {C B : Ty Δ}
  → (ρ : Δ ⇒ʳ sucℕ Δ′)
  → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → (∀ X → genᵐ μ ‼ (ρ X) ≡ ν ‼ X)
  → ν ⊢ C ∼ B
  → (A : Ty Δ′)
  → renameᵗ ρ C ≡ ⇑ᵗ A
  → A ≢ ★
  → NonVar (renameᵗ ρ B)
  → zero ∈ᵗ renameᵗ ρ B
  → μ ⊢ A ∼ `∀ (renameᵗ ρ B)
genᴱ ρ inj eq c@(id a) A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@(c₁ ↦ c₂) A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@(∀ᶜ c₁) A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@(c₁ !) A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@(？ c₁) A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@((gen c₁) C≢★) A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@bot-elim A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ ρ inj eq c@bot-intro A eC A≢★ nv z =
  (gen_ ⦃ nv ⦄ ⦃ z ⦄ (subst-left-∼ eC (rename∼ ρ eq c))) A≢★
genᴱ {B = B} ρ inj eq ((inst_ ⦃ C₁nv ⦄ ⦃ z∈C₁ ⦄ d) B≢★)
    (`∀ C₀) eC A≢★ nv z =
  (inst_ ⦃ swap-nonvar ρ (ty-all-inj eC) C₁nv ⦄
    ⦃ swap-occurs ρ inj (ty-all-inj eC) z∈C₁ ⦄
    (subst-right-∼ (cong `∀ (liftSwap-target ρ B))
      (genᴱ (liftSwap ρ) (liftSwap-injective inj)
        (liftSwap-env ρ eq) d C₀
        (liftSwap-source ρ (ty-all-inj eC))
        (∈→≢★ (swap-occurs ρ inj (ty-all-inj eC) z∈C₁))
        (swap-target-nonvar ρ B nv)
        (swap-target-occurs ρ B z))))
    (λ ())
genᴱ ρ inj eq ((inst d) B≢★) (＇ X) () A≢★ nv z
genᴱ ρ inj eq ((inst d) B≢★) (‵ ι) () A≢★ nv z
genᴱ ρ inj eq ((inst d) B≢★) ★ () A≢★ nv z
genᴱ ρ inj eq ((inst d) B≢★) (A₁ ⇒ A₂) () A≢★ nv z

------------------------------------------------------------------------
-- Normalization
------------------------------------------------------------------------

eager : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → μ ⊢ A ∼ B
eager (id a) = id a
eager (c ↦ d) = eager c ↦ eager d
eager (∀ᶜ c) = ∀ᶜ (eager c)
eager (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (eager c) ⦃ Ans ⦄
eager (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (eager c) ⦃ Bns ⦄
eager ((inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) B≢★) =
  (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ (eager c)) B≢★
eager {μ = μ} ((gen_ {A = A} {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) A≢★) =
  subst-right-∼ (cong `∀ (renameᵗ-id B))
    (genᴱ (λ X → X) (λ e → e) (λ X → refl) (eager c) A
      (renameᵗ-id (⇑ᵗ A)) A≢★
      (subst NonVar (sym (renameᵗ-id B)) Bnv)
      (subst (zero ∈ᵗ_) (sym (renameᵗ-id B)) z∈B))
eager bot-elim = bot-elim
eager bot-intro = bot-intro

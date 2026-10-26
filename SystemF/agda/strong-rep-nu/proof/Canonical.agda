module strong-rep-nu.proof.Canonical where

-- File Charter:
--   * CANONICAL FORMS.  §1 `~` preserves the exterior type's head
--     constructor; §2 what an INERT tail can look like, read off its
--     TARGET type; §3 `simple-¬var`, `canon-simple-∀`, `canon-base`,
--     `canon-ℕ`, `canon-⇒`, `canon-∀`.
--   * ONE OBSERVATION DRIVES THE SUITE: for a wrapper value
--     `U ⟪ Θ , tail t ⟫`, `boundary` reads the EXTERIOR type as the
--     TARGET representation of `t` by `_⊢_~_`, and an INERT `t` determines that
--     target's head constructor outright (`id (` X)` and the seals ⇝ a
--     variable, `s ↦ u` ⇝ an arrow, `` `∀ s `` ⇝ a `∀`).  So no inert
--     tail has a BASE target, and — with ONE boundary per value — the
--     interior of a ∀-value's boundary is a `Λ`.
-- Commentary: Commentary.md § proof/Canonical.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; renameᵗ; extᵗ; ⇑ᵗ; Base; base-ℕ; base-𝔹)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary

private
  variable
    Δ Δ′ : Ctxᵗ
    η : TyCtx
    A B C R S : Ty
    X Y α : ℕ
    c : Conv

------------------------------------------------------------------------
-- §1  `≈` preserves the exterior type's head constructor
------------------------------------------------------------------------

-- Since the store design the exterior comparison relates the two
-- spellings at EQUAL representation depth, so these inversions are
-- direct.  Commentary.md § proof/Canonical.agda / §1

same-∀-target : η ⊢ A ~ `∀ R → Σ[ B ∈ Ty ] (A ≡ `∀ B)
same-∀-target (same-∀ p) = _ , refl

same-var-target : η ⊢ A ~ ` α → Σ[ X ∈ ℕ ] (A ≡ ` X)
same-var-target (same-var d) = _ , refl

-- A reading keeps the head constructor of the ordinary type
-- (`boundary` now relates the exterior type to the conversion's
-- REPRESENTATION target by `~` directly).
~-base : η ⊢ A ~ R → Base A → Base R
~-base same-ℕ base-ℕ = base-ℕ
~-base same-𝔹 base-𝔹 = base-𝔹

~-⇒ : η ⊢ (A ⇒ B) ~ R → Σ[ R₁ ∈ Ty ] Σ[ R₂ ∈ Ty ] (R ≡ R₁ ⇒ R₂)
~-⇒ (same-⇒ p q) = _ , _ , refl

~-∀ : η ⊢ `∀ A ~ R → Σ[ R₀ ∈ Ty ] (R ≡ `∀ R₀)
~-∀ (same-∀ p) = _ , refl

-- Retype a conversion along an equality of its target type.
conv-tgt≡ : ∀ {Θ p B′} → B ≡ B′
  → Δ ∣ Θ ⊢[ p ] c ∶ A ⇝ B → Δ ∣ Θ ⊢[ p ] c ∶ A ⇝ B′
conv-tgt≡ refl ⊢c = ⊢c

-- Retype a term along an equality of its type — used to move an
-- interior derivation along the conversion inversions, which name the
-- SOURCE type of an `id`/`unseal`.
⊢ty≡ : ∀ {Γ M}
  → A ≡ B → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ⊢ M ⦂ B
⊢ty≡ refl ⊢M = ⊢M

------------------------------------------------------------------------
-- §2  What an INERT tail can look like, read off its TARGET type
------------------------------------------------------------------------

-- A value boundary's conversion is a TAIL (its interior is simple, so
-- its source is not a variable).  No inert tail has a base target:
-- `id A` at a base type is ACTIVE (A-idb), so `V-⟪⟫` never builds a
-- value at a base type.
inert-¬base : ∀ {t Θ p} → InertTail t → Δ ∣ Θ ⊢[ p ] tail t ∶ A ⇝ B
  → ¬ Base B
inert-¬base I-idv (conv-tail (conv-mid (conv-id ())))
inert-¬base I-idv (conv-tail (conv-mid (conv-idv _))) ()
inert-¬base I-fun (conv-tail (conv-mid (conv-fun _ _))) ()
inert-¬base I-all (conv-tail (conv-mid (conv-all _))) ()
inert-¬base I-seal (conv-tail (conv-seal _ _)) ()
inert-¬base I-seal-seq (conv-tail (conv-seal-seq _ _ _ _)) ()

-- An ARROW target forces a function middle; a ∀ target a ∀ middle.
inert-fun-conv : ∀ {t Θ p} → InertTail t
  → Δ ∣ Θ ⊢[ p ] tail t ∶ A ⇝ (B ⇒ C)
  → Σ[ s ∈ Conv ] Σ[ u ∈ Conv ] (t ≡ mid (s ↦ u))
inert-fun-conv I-fun (conv-tail (conv-mid (conv-fun ⊢s ⊢t))) =
  _ , _ , refl

inert-all-conv : ∀ {t Θ p} → InertTail t
  → Δ ∣ Θ ⊢[ p ] tail t ∶ A ⇝ `∀ B
  → Σ[ s ∈ Conv ] (t ≡ mid (`∀ s))
inert-all-conv I-all (conv-tail (conv-mid (conv-all ⊢s))) = _ , refl

------------------------------------------------------------------------
-- §3  CANONICAL FORMS
------------------------------------------------------------------------

-- A SIMPLE value never has a variable type, and at a ∀ type it is a
-- `Λ` over a value.
simple-¬var : ∀ {U} → Simple U → Δ ∣ [] ⊢ U ⦂ ` X → ⊥
simple-¬var S-$ ()
simple-¬var S-true ()
simple-¬var S-false ()
simple-¬var S-ƛ ()
simple-¬var (S-Λ v) ()

canon-simple-∀ : ∀ {U} → Simple U → Δ ∣ [] ⊢ U ⦂ `∀ C
  → Σ[ N ∈ Term ] (Value N × (U ≡ Λ N))
canon-simple-∀ S-$ ()
canon-simple-∀ S-true ()
canon-simple-∀ S-false ()
canon-simple-∀ S-ƛ ()
canon-simple-∀ (S-Λ vN) (⊢Λ _ _) = _ , vN , refl

-- BASE.  A closed value at a base type is a numeral or Boolean literal,
-- outright — no wrapper survives (§2, inert-¬base).
canon-base : ∀ {V} → Value V → Base A → Δ ∣ [] ⊢ V ⦂ A
  → (Σ[ n ∈ ℕ ] (V ≡ $ n)) ⊎ (V ≡ `true) ⊎ (V ≡ `false)
canon-base (V-simple S-$)     b      ⊢$     = inj₁ (_ , refl)
canon-base (V-simple S-true)  base-𝔹 ⊢true  = inj₂ (inj₁ refl)
canon-base (V-simple S-false) base-𝔹 ⊢false = inj₂ (inj₂ refl)
canon-base (V-simple S-ƛ)     ()     (⊢ƛ _ _)
canon-base (V-simple (S-Λ _)) ()     (⊢Λ _ _)
canon-base {Δ = Δ} (V-⟪⟫ u it) b
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _) =
  ⊥-elim (inert-¬base it ⊢c (~-base sameₑ b))

canon-ℕ : ∀ {V}
  → Value V → Δ ∣ [] ⊢ V ⦂ `ℕ → Σ[ n ∈ ℕ ] (V ≡ $ n)
canon-ℕ v ⊢V with canon-base v base-ℕ ⊢V
canon-ℕ v ⊢V | inj₁ p = p
canon-ℕ v ()  | inj₂ (inj₁ refl)
canon-ℕ v ()  | inj₂ (inj₂ refl)

-- ARROW.  A closed value at an arrow type is a λ or a SIMPLE value
-- under a function middle — the two left-hand sides of Beta and Wrap.
canon-⇒ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → (Σ[ N ∈ Term ] (V ≡ ƛ A ∙ N))
  ⊎ (Σ[ U ∈ Term ] Σ[ Θ ∈ Boundary ] Σ[ s ∈ Conv ] Σ[ t ∈ Conv ]
       (Simple U × (V ≡ U ⟪ Θ , ⌞ s ↦ t ⌟ ⟫)))
canon-⇒ (V-simple S-$)     ()
canon-⇒ (V-simple S-true)  ()
canon-⇒ (V-simple S-false) ()
canon-⇒ (V-simple S-ƛ)     (⊢ƛ _ _) = inj₁ (_ , refl)
canon-⇒ (V-simple (S-Λ _)) ()
canon-⇒ {Δ = Δ} (V-⟪⟫ u it) (boundary _ _ ⊢c _ sameₑ _)
  with ~-⇒ sameₑ
canon-⇒ {Δ = Δ} (V-⟪⟫ u it) (boundary _ _ ⊢c _ sameₑ _)
  | R₁ , R₂ , eq with inert-fun-conv it (conv-tgt≡ eq ⊢c)
canon-⇒ {Δ = Δ} (V-⟪⟫ u it) (boundary _ _ ⊢c _ sameₑ _)
  | R₁ , R₂ , eq | s , t , refl = inj₂ (_ , _ , s , t , u , refl)

-- ∀.  A closed value at a ∀ type is a Λ over a VALUE (TyBeta's premise)
-- or a Λ under a ∀ middle (TyWrap's): the one-boundary invariant
-- leaves no third shape.
canon-∀ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → (Σ[ N ∈ Term ] (Value N × (V ≡ Λ N)))
  ⊎ (Σ[ N ∈ Term ] Σ[ Θ ∈ Boundary ] Σ[ s ∈ Conv ]
       (Value N × (V ≡ (Λ N) ⟪ Θ , ⌞ `∀ s ⌟ ⟫)))
canon-∀ (V-simple S-$)      ()
canon-∀ (V-simple S-true)   ()
canon-∀ (V-simple S-false)  ()
canon-∀ (V-simple S-ƛ)      ()
canon-∀ (V-simple (S-Λ vN)) (⊢Λ _ _) = inj₁ (_ , vN , refl)
canon-∀ {Δ = Δ} (V-⟪⟫ u it) (boundary _ ⊢U ⊢c sameᵢ sameₑ _)
  with ~-∀ sameₑ
canon-∀ {Δ = Δ} (V-⟪⟫ u it) (boundary _ ⊢U ⊢c sameᵢ sameₑ _)
  | R₀ , eq with inert-all-conv it (conv-tgt≡ eq ⊢c)
canon-∀ {Δ = Δ} (V-⟪⟫ u it) (boundary _ ⊢U ⊢c sameᵢ sameₑ _)
  | R₀ , eq | s , refl with conv-all-inv ⊢c
canon-∀ {Δ = Δ} (V-⟪⟫ u it) (boundary _ ⊢U ⊢c sameᵢ sameₑ _)
  | R₀ , eq | s , refl | A₀ , B₀ , refl , eqB , ⊢s
  with same-∀-target sameᵢ
canon-∀ {Δ = Δ} (V-⟪⟫ u it) (boundary _ ⊢U ⊢c sameᵢ sameₑ _)
  | R₀ , eq | s , refl | A₀ , B₀ , refl , eqB , ⊢s | D , refl
  with canon-simple-∀ u ⊢U
canon-∀ {Δ = Δ} (V-⟪⟫ u it) (boundary _ ⊢U ⊢c sameᵢ sameₑ _)
  | R₀ , eq | s , refl | A₀ , B₀ , refl , eqB , ⊢s | D , refl
  | N , vN , refl = inj₂ (_ , _ , s , vN , refl)

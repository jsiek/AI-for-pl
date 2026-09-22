module strong-rep-store.proof.Canonical where

-- CANONICAL FORMS for the conversion-boundary calculus.
--
-- A closed value is one of five shapes, and its EXTERIOR TYPE decides
-- which.  The whole suite is driven by ONE observation: for a wrapper
-- value `V ⟪ Θ , c ⟫` the `env` rule relates the EXTERIOR TYPE and the
-- TARGET TYPE of `c` through `SameTyExt`.  Its common representation type is
-- shifted past Θ's representation binders on the conversion side, and an
-- INERT `c` determines that target type's head constructor outright:
--
--   id (` X)  ⇝  ` X          I-idv
--   seal X    ⇝  ` X          I-seal
--   s ↦ t     ⇝  A′ ⇒ B′      I-fun
--   `∀ s      ⇝  `∀ B         I-all
--
-- Neither ACTIVE conversion can occur under `V-⟪⟫`, so no inert
-- conversion has a BASE target at all — which is why `canon-base` returns
-- a numeral OUTRIGHT (§3), with no wrapper escape hatch.  Dually, the two
-- conversions with a VARIABLE target are exactly `seal` and the
-- id-at-a-variable — the two left-hand sides of CancelR and IdPush (§3,
-- canon-var).  This is the v1 "canon-var nightmare", dissolved: it is a
-- two-way case split on a conversion constructor, with no rep comparison
-- anywhere.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary

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

-- The old `env` exposed `shiftBy (numBinds Θ) Bₑ` directly.  The relational
-- rule instead factors both spellings through a representation type and uses
-- `shiftRep` on the conversion side.  With the store design (experiment 2)
-- there is no bind prefix to cross, so `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` relates the two
-- spellings at equal representation depth — `shiftRep 0 R ≡ R` — and the
-- head-constructor inversions simplify accordingly.

same-base-target : η ⊢ A ~ R → Base R → Base A
same-base-target same-ℕ base-ℕ = base-ℕ
same-base-target same-𝔹 base-𝔹 = base-𝔹

same-⇒-target : η ⊢ A ~ (R ⇒ S)
  → Σ[ B ∈ Ty ] Σ[ C ∈ Ty ] (A ≡ B ⇒ C)
same-⇒-target (same-⇒ p q) = _ , _ , refl

same-∀-target : η ⊢ A ~ `∀ R → Σ[ B ∈ Ty ] (A ≡ `∀ B)
same-∀-target (same-∀ p) = _ , refl

same-var-target : η ⊢ A ~ ` α → Σ[ X ∈ ℕ ] (A ≡ ` X)
same-var-target (same-var d) = _ , refl

≈-base-target : ∀ {Δ Δ′ A B}
  → Base A → Δ ⊢ A ≈ B ⊣ Δ′
  → Base B
≈-base-target base-ℕ (`ℕ , same-ℕ , q) =
  same-base-target q base-ℕ
≈-base-target base-𝔹 (`𝔹 , same-𝔹 , q) =
  same-base-target q base-𝔹

≈-⇒-target : ∀ {Δ Δ′ A B C}
  → Δ ⊢ (A ⇒ B) ≈ C ⊣ Δ′
  → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ] (C ≡ A′ ⇒ B′)
≈-⇒-target (_ , same-⇒ p q , r) =
  same-⇒-target r

≈-∀-target : ∀ {Δ Δ′ A B}
  → Δ ⊢ `∀ A ≈ B ⊣ Δ′
  → Σ[ A′ ∈ Ty ] (B ≡ `∀ A′)
≈-∀-target (_ , same-∀ p , q) =
  same-∀-target q

≈-var-target : ∀ {Δ Δ′ X A}
  → Δ ⊢ ` X ≈ A ⊣ Δ′
  → Σ[ Y ∈ ℕ ] (A ≡ ` Y)
≈-var-target (_ , same-var {α = α} d , q) =
  same-var-target q

-- Retype a conversion along an equality of its target type.
conv-tgt≡ : ∀ {B′} → B ≡ B′
  → Δ ⊢ c ∶ A ⇝ B → Δ ⊢ c ∶ A ⇝ B′
conv-tgt≡ refl ⊢c = ⊢c

-- Retype a term along an equality of its type.  Used to move an interior
-- derivation along the conversion inversions of strong-rep-store.Conversion
-- (which
-- name the SOURCE type of an `id`/`unseal`), so that the canonical-forms
-- lemmas can be applied to it.
⊢ty≡ : ∀ {Γ M}
  → A ≡ B → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ⊢ M ⦂ B
⊢ty≡ refl ⊢M = ⊢M

------------------------------------------------------------------------
-- §2  What an INERT conversion can look like, read off its TARGET type
------------------------------------------------------------------------

-- No inert conversion has a base target.  `id A` at a base type is the
-- one conversion with a base target, and it is ACTIVE (A-idb), so `V-⟪⟫`
-- can never build a value at a base type.
inert-¬base : Inert c → Δ ⊢ c ∶ A ⇝ B → ¬ Base B
inert-¬base I-idv  (conv-id ())
inert-¬base I-idv  (conv-idv _)   ()
inert-¬base I-seal (conv-seal _)  ()
inert-¬base I-fun  (conv-fun _ _) ()
inert-¬base I-all  (conv-all _)   ()

-- An ARROW target forces a function conversion: `id`/`seal` have
-- variable targets and `` `∀ `` has a ∀ target.
inert-fun-conv : Inert c → Δ ⊢ c ∶ A ⇝ (B ⇒ C)
  → Σ[ s ∈ Conv ] Σ[ t ∈ Conv ] (c ≡ s ↦ t)
inert-fun-conv I-fun (conv-fun ⊢s ⊢t) = _ , _ , refl

-- A ∀ target forces a ∀ conversion.
inert-all-conv : Inert c → Δ ⊢ c ∶ A ⇝ `∀ B
  → Σ[ s ∈ Conv ] (c ≡ `∀ s)
inert-all-conv I-all (conv-all ⊢s) = _ , refl

-- A VARIABLE target admits exactly TWO conversions, and the variable is
-- literally the name they carry — there is no second spelling to compare.
-- These two are the left-hand sides of CancelR and IdPush.
inert-var-conv : Inert c → Δ ⊢ c ∶ A ⇝ ` X
  → (c ≡ seal X) ⊎ (c ≡ id (` X))
inert-var-conv I-idv  (conv-id ())
inert-var-conv I-idv  (conv-idv _)  = inj₂ refl
inert-var-conv I-seal (conv-seal _) = inj₁ refl

------------------------------------------------------------------------
-- §3  CANONICAL FORMS
------------------------------------------------------------------------

-- BASE.  A closed value at a base type is a numeral or Boolean literal,
-- outright — no wrapper survives (§2, inert-¬base).
canon-base : ∀ {V} → Value V → Base A → Δ ∣ [] ⊢ V ⦂ A
  → (Σ[ n ∈ ℕ ] (V ≡ $ n)) ⊎ (V ≡ `true) ⊎ (V ≡ `false)
canon-base V-$       b       ⊢$     = inj₁ (_ , refl)
canon-base V-true    base-𝔹 ⊢true  = inj₂ (inj₁ refl)
canon-base V-false   base-𝔹 ⊢false = inj₂ (inj₂ refl)
canon-base V-ƛ       ()      (⊢ƛ _ _)
canon-base (V-Λ _)   ()      (⊢Λ _ _)
canon-base {Δ = Δ} (V-⟪⟫ v ic) b
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _) =
  ⊥-elim
    (inert-¬base ic ⊢c
      (≈-base-target {Δ = Δ} {Δ′ = Δᶜ}
        b sameₑ))

canon-ℕ : ∀ {V}
  → Value V → Δ ∣ [] ⊢ V ⦂ `ℕ → Σ[ n ∈ ℕ ] (V ≡ $ n)
canon-ℕ V-$       ⊢$ = _ , refl
canon-ℕ V-true    ()
canon-ℕ V-false   ()
canon-ℕ V-ƛ       ()
canon-ℕ (V-Λ _)   ()
canon-ℕ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _) =
  ⊥-elim
    (inert-¬base ic ⊢c
      (≈-base-target {Δ = Δ} {Δ′ = Δᶜ}
        base-ℕ sameₑ))

-- ARROW.  A closed value at an arrow type is a λ or a wrapper with a
-- FUNCTION CONVERSION — the two left-hand sides of Beta and Peel.  The
-- wrapper's interior is itself a value, which is exactly Peel's first
-- premise.
canon-⇒ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → (Σ[ N ∈ Term ] (V ≡ ƛ A ∙ N))
  ⊎ (Σ[ W ∈ Term ] Σ[ Θ ∈ Boundary ] Σ[ s ∈ Conv ] Σ[ t ∈ Conv ]
       (Value W × (V ≡ W ⟪ Θ , s ↦ t ⟫)))
canon-⇒ V-$     ()
canon-⇒ V-true  ()
canon-⇒ V-false ()
canon-⇒ V-ƛ     (⊢ƛ _ _) = inj₁ (_ , refl)
canon-⇒ (V-Λ _) ()
canon-⇒ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  with ≈-⇒-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
canon-⇒ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | A′ , B′ , eq
  with inert-fun-conv ic (conv-tgt≡ eq ⊢c)
canon-⇒ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | A′ , B′ , eq | s , t , refl =
  inj₂ (_ , _ , s , t , v , refl)

-- ∀.  A closed value at a ∀ type is a Λ over a VALUE (V-Λ's premise, and
-- exactly TyBeta's premise) or a wrapper with a ∀ CONVERSION (TyPeelR's).
canon-∀ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → (Σ[ N ∈ Term ] (Value N × (V ≡ Λ N)))
  ⊎ (Σ[ W ∈ Term ] Σ[ Θ ∈ Boundary ] Σ[ s ∈ Conv ]
       (Value W × (V ≡ W ⟪ Θ , `∀ s ⟫)))
canon-∀ V-$      ()
canon-∀ V-true   ()
canon-∀ V-false  ()
canon-∀ V-ƛ      ()
canon-∀ (V-Λ vN) (⊢Λ _ _) = inj₁ (_ , vN , refl)
canon-∀ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  with ≈-∀-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
canon-∀ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | C′ , eq
  with inert-all-conv ic (conv-tgt≡ eq ⊢c)
canon-∀ {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | C′ , eq | s , refl =
  inj₂ (_ , _ , s , v , refl)

-- VARIABLE — the v2 canon-var.  A closed value at an abstract type is a
-- wrapper whose conversion is `seal Y` or `id (` Y)`, nothing else: the
-- two left-hand sides of CancelR and IdPush.  (`value-var-visible` is NOT
-- needed here — the conversion inversion already decides the shape;
-- visibility of the named slot is a separate, and independently available,
-- fact.)
canon-var : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ ` X
  → Σ[ W ∈ Term ] Σ[ Θ ∈ Boundary ] Σ[ Y ∈ ℕ ]
      (Value W
       × ((V ≡ W ⟪ Θ , seal Y ⟫) ⊎ (V ≡ W ⟪ Θ , id (` Y) ⟫)))
canon-var V-$     ()
canon-var V-true  ()
canon-var V-false ()
canon-var V-ƛ     ()
canon-var (V-Λ _) ()
canon-var {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  with ≈-var-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
canon-var {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | Y , eq
  with inert-var-conv ic (conv-tgt≡ eq ⊢c)
canon-var {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | Y , eq | inj₁ refl =
  _ , _ , _ , v , inj₁ refl
canon-var {Δ = Δ} (V-⟪⟫ v ic)
    (env {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
  | Y , eq | inj₂ refl =
  _ , _ , _ , v , inj₂ refl


module strong.proof.Canonical where

-- CANONICAL FORMS for the conversion-boundary calculus.
--
-- A closed value is one of five shapes, and its EXTERIOR TYPE decides
-- which.  The whole suite is driven by ONE observation: for a wrapper
-- value `V ⟪ Θ , c ⟫` the `env` rule pins the exterior face of `c` to
-- `liftN (nbind Θ) Bₑ`, and an INERT `c` determines that face's head
-- constructor outright:
--
--   id (` X)  ⇝  ` X          I-idv
--   seal X    ⇝  ` X          I-seal
--   s ↦ t     ⇝  A′ ⇒ B′      I-fun
--   `∀ s      ⇝  `∀ B         I-all
--
-- Neither ACTIVE face can occur under `V-⟪⟫`, so no inert face has a BASE
-- exterior at all — which is why `canon-base` returns a numeral OUTRIGHT
-- (§3), with no wrapper escape hatch.  Dually, the two faces with a
-- VARIABLE exterior are exactly `seal` and the id-at-a-variable — the two
-- left-hand sides of CancelR and IdPush (§3, canon-var).  This is the v1
-- "canon-var nightmare", dissolved: it is a two-way case split on a face
-- constructor, with no rep comparison anywhere.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

private
  variable
    Δ : Ctxᵗ
    A B C : Ty
    X Y : ℕ
    c : Conv
    p : Pol

------------------------------------------------------------------------
-- §1  The exterior face is the term's type, LIFTED past the owners
------------------------------------------------------------------------

-- `env` reads the exterior face at `liftN (nbind Θ) Bₑ`, so every face
-- inversion below has to see through `liftN`.  Lifting preserves the head
-- constructor; that is all we need.  (`liftN-base` and `liftN-var` are
-- already in strong.Ctx.)

liftN-⇒ : (n : ℕ) (A B : Ty) → liftN n (A ⇒ B) ≡ liftN n A ⇒ liftN n B
liftN-⇒ zero    A B = refl
liftN-⇒ (suc n) A B = cong ⇑ᵗ (liftN-⇒ n A B)

liftN-∀ : (n : ℕ) (C : Ty) → Σ[ C′ ∈ Ty ] (liftN n (`∀ C) ≡ `∀ C′)
liftN-∀ zero    C = C , refl
liftN-∀ (suc n) C with liftN-∀ n C
... | C′ , eq = renameᵗ (extᵗ suc) C′ , cong ⇑ᵗ eq

-- Retype a conversion along an equality of its exterior face.
conv-tgt≡ : ∀ {B′} → B ≡ B′
  → Δ ⊢ c ∶ A ⇝ B ∙ p → Δ ⊢ c ∶ A ⇝ B′ ∙ p
conv-tgt≡ refl ⊢c = ⊢c

-- Retype a term along an equality of its type.  Used to move an interior
-- derivation along the face inversions of strong.Conversion (which name
-- the INTERIOR face of an `id`/`unseal`), so that the canonical-forms
-- lemmas can be applied to it.
⊢ty≡ : ∀ {Γ M} → A ≡ B → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ⊢ M ⦂ B
⊢ty≡ refl ⊢M = ⊢M

------------------------------------------------------------------------
-- §2  What an INERT face can look like, read off its EXTERIOR type
------------------------------------------------------------------------

-- No inert face has a base exterior.  `id A` at a base type is the one
-- conversion with a base exterior, and it is ACTIVE (A-idb), so `V-⟪⟫`
-- can never build a value at a base type.
inert-¬base : Inert c → Δ ⊢ c ∶ A ⇝ B ∙ p → ¬ Base B
inert-¬base I-idv  (conv-id ())
inert-¬base I-idv  (conv-idv _)   ()
inert-¬base I-seal (conv-seal _)  ()
inert-¬base I-fun  (conv-fun _ _) ()
inert-¬base I-all  (conv-all _)   ()

-- An ARROW exterior forces the ↦ face: `id`/`seal` have variable
-- exteriors and `` `∀ `` has a ∀ exterior.
inert-fun-face : Inert c → Δ ⊢ c ∶ A ⇝ (B ⇒ C) ∙ p
  → Σ[ s ∈ Conv ] Σ[ t ∈ Conv ] (c ≡ s ↦ t)
inert-fun-face I-fun (conv-fun ⊢s ⊢t) = _ , _ , refl

-- A ∀ exterior forces the ∀ face.
inert-all-face : Inert c → Δ ⊢ c ∶ A ⇝ `∀ B ∙ p
  → Σ[ s ∈ Conv ] (c ≡ `∀ s)
inert-all-face I-all (conv-all ⊢s) = _ , refl

-- A VARIABLE exterior admits exactly TWO faces, and the variable is
-- literally the name they carry — there is no second spelling to compare.
-- These two are the left-hand sides of CancelR and IdPush.
inert-var-face : Inert c → Δ ⊢ c ∶ A ⇝ ` X ∙ p
  → (c ≡ seal X) ⊎ (c ≡ id (` X))
inert-var-face I-idv  (conv-id ())
inert-var-face I-idv  (conv-idv _)  = inj₂ refl
inert-var-face I-seal (conv-seal _) = inj₁ refl

------------------------------------------------------------------------
-- §3  CANONICAL FORMS
------------------------------------------------------------------------

-- BASE.  A closed value at a base type is a NUMERAL, outright — no
-- wrapper survives (§2, inert-¬base).  Note the `𝔹 instance is vacuous:
-- the calculus has no boolean literal, so there is simply no closed value
-- at `𝔹, and this statement absorbs that fact.
canon-base : ∀ {V} → Value V → Base A → Δ ∣ [] ⊢ V ⦂ A
  → Σ[ n ∈ ℕ ] (V ≡ $ n)
canon-base V-$        b  ⊢$            = _ , refl
canon-base V-ƛ        () (⊢ƛ _ _)
canon-base (V-Λ _)    () (⊢Λ _)
canon-base (V-⟪⟫ v ic) b (env {Θ = Θ} _ _ ⊢c _) =
  ⊥-elim (inert-¬base ic (conv-tgt≡ (liftN-base (nbind Θ) b) ⊢c) b)

canon-ℕ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ `ℕ → Σ[ n ∈ ℕ ] (V ≡ $ n)
canon-ℕ v ⊢V = canon-base v base-ℕ ⊢V

-- ARROW.  A closed value at an arrow type is a λ or a ↦-FACED WRAPPER —
-- the two left-hand sides of Beta and Peel.  The wrapper's interior is
-- itself a value, which is exactly Peel's first premise.
canon-⇒ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → (Σ[ N ∈ Term ] (V ≡ ƛ A ∙ N))
  ⊎ (Σ[ W ∈ Term ] Σ[ Θ ∈ CtxMorph ] Σ[ s ∈ Conv ] Σ[ t ∈ Conv ]
       (Value W × (V ≡ W ⟪ Θ , s ↦ t ⟫)))
canon-⇒ V-$     ()
canon-⇒ V-ƛ     (⊢ƛ _ _) = inj₁ (_ , refl)
canon-⇒ (V-Λ _) ()
canon-⇒ {A = A} {B = B} (V-⟪⟫ v ic) (env {Θ = Θ} _ _ ⊢c _)
  with inert-fun-face ic
         (conv-tgt≡ (liftN-⇒ (nbind Θ) A B) ⊢c)
canon-⇒ (V-⟪⟫ v ic) (env _ _ ⊢c _) | s , t , refl =
  inj₂ (_ , _ , s , t , v , refl)

-- ∀.  A closed value at a ∀ type is a Λ over a VALUE (V-Λ's premise, and
-- exactly TyBeta's premise) or a ∀-FACED WRAPPER (TyPeelR's).
canon-∀ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → (Σ[ N ∈ Term ] (Value N × (V ≡ Λ N)))
  ⊎ (Σ[ W ∈ Term ] Σ[ Θ ∈ CtxMorph ] Σ[ s ∈ Conv ]
       (Value W × (V ≡ W ⟪ Θ , `∀ s ⟫)))
canon-∀ V-$      ()
canon-∀ V-ƛ      ()
canon-∀ (V-Λ vN) (⊢Λ _) = inj₁ (_ , vN , refl)
canon-∀ {C = C} (V-⟪⟫ v ic) (env {Θ = Θ} _ _ ⊢c _)
  with liftN-∀ (nbind Θ) C
canon-∀ (V-⟪⟫ v ic) (env _ _ ⊢c _) | C′ , eq
  with inert-all-face ic (conv-tgt≡ eq ⊢c)
canon-∀ (V-⟪⟫ v ic) (env _ _ ⊢c _) | C′ , eq | s , refl =
  inj₂ (_ , _ , s , v , refl)

-- VARIABLE — the v2 canon-var.  A closed value at an abstract type is a
-- wrapper whose face is `seal Y` or `id (` Y)`, nothing else: the two
-- left-hand sides of CancelR and IdPush.  (`value-var-visible` is NOT
-- needed here — the face inversion already decides the shape; visibility
-- of the named slot is a separate, and independently available, fact.)
canon-var : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ ` X
  → Σ[ W ∈ Term ] Σ[ Θ ∈ CtxMorph ] Σ[ Y ∈ ℕ ]
      (Value W
       × ((V ≡ W ⟪ Θ , seal Y ⟫) ⊎ (V ≡ W ⟪ Θ , id (` Y) ⟫)))
canon-var V-$     ()
canon-var V-ƛ     ()
canon-var (V-Λ _) ()
canon-var {X = X} (V-⟪⟫ v ic) (env {Θ = Θ} _ _ ⊢c _)
  with inert-var-face ic
         (conv-tgt≡ (liftN-var (nbind Θ) X) ⊢c)
canon-var (V-⟪⟫ v ic) (env _ _ ⊢c _) | inj₁ refl =
  _ , _ , _ , v , inj₁ refl
canon-var (V-⟪⟫ v ic) (env _ _ ⊢c _) | inj₂ refl =
  _ , _ , _ , v , inj₂ refl

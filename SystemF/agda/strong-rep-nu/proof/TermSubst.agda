module strong-rep-nu.proof.TermSubst where

-- File Charter:
--   * THE PROOF HALF OF strong-rep-nu.TermSubst: every
--     renaming/substitution definition and lemma that NO top-level
--     module mentions.  The section numbers are the ones this material
--     had in the public file, because other modules cite them.
--     §1 `id²`/`renᶠ`; §2 values under a type renaming, the
--     ordinary-identity agreement `renᴹ²-ord-id`, and the derived
--     `renᴹ`/`wkN`/`wkᴹ`/`⇑ᴹ`; §3 TERM-VARIABLE renaming; §4 the `⤊`
--     transports and `⊢renⁿ`/`renⁿ-id`/`⊢weakenⁿ`; §5 `value-substᵐ`;
--     §6 the typed images `_∣_⊢ⁱ_⦂_`.
--   * NOTHING HERE MAY BE CITED FROM A TOP-LEVEL FILE: the top level
--     plus the theorem statements must be readable alone.
--   * TWO LAWS.  (1) Boundaries are TERM-CLOSED, so `renⁿ` does NOT
--     descend into `_⟪_,_⟫`.  (2) An ordinary-identity `renᴹ²` IS
--     `renᴹᴿ` (`renᴹ²-ord-id`).
-- Commentary: Commentary.md § proof/TermSubst.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst

------------------------------------------------------------------------
-- 1. Paired type-level renaming — the derived maps
------------------------------------------------------------------------

id² : TyRename
id² = ren² idᵗ idᵗ

renᶠ : Renameᵗ → Change → Change
renᶠ ρ = renᶠ² ρ ρ

------------------------------------------------------------------------
-- 2. Renaming terms — values, agreement, derived renamings
------------------------------------------------------------------------

-- VALUES SURVIVE EVERY RENAMING AND SUBSTITUTION, because `⊢Λ` carries
-- `Value N` and every typing-transport lemma must rebuild it.
inert-renᶜ : ∀ {c} (ρ : Renameᵗ) → Inert c → Inert (renᶜ ρ c)
inert-renᶜ ρ I-idv  = I-idv
inert-renᶜ ρ I-seal = I-seal
inert-renᶜ ρ I-fun  = I-fun
inert-renᶜ ρ I-all  = I-all

value-renᴹ² : ∀ {M} (ρ : TyRename) → Value M → Value (renᴹ² ρ M)
value-renᴹ² ρ V-$         = V-$
value-renᴹ² ρ V-true      = V-true
value-renᴹ² ρ V-false     = V-false
value-renᴹ² ρ V-ƛ         = V-ƛ
value-renᴹ² ρ (V-Λ v)     = V-Λ (value-renᴹ² (underΛ-ren ρ) v)
value-renᴹ² ρ (V-⟪⟫ v ic) = V-⟪⟫ (value-renᴹ² _ v) (inert-renᶜ _ ic)

value-renᴹᴿ : ∀ {M} (ρ : Renameᵗ) → Value M → Value (renᴹᴿ ρ M)
value-renᴹᴿ ρ V-$         = V-$
value-renᴹᴿ ρ V-true      = V-true
value-renᴹᴿ ρ V-false     = V-false
value-renᴹᴿ ρ V-ƛ         = V-ƛ
value-renᴹᴿ ρ (V-Λ v)     = V-Λ (value-renᴹᴿ (extᵗ ρ) v)
value-renᴹᴿ ρ (V-⟪⟫ v ic) = V-⟪⟫ (value-renᴹᴿ _ v) ic

extᵗ-pointwise-id : ∀ {ρ} → (∀ X → ρ X ≡ X)
  → ∀ X → extᵗ ρ X ≡ X
extᵗ-pointwise-id h zero    = refl
extᵗ-pointwise-id h (suc X) = cong suc (h X)

renameᵗ-pointwise-id : ∀ {ρ} → (∀ X → ρ X ≡ X)
  → ∀ A → renameᵗ ρ A ≡ A
renameᵗ-pointwise-id h (` X) = cong `_ (h X)
renameᵗ-pointwise-id h `ℕ = refl
renameᵗ-pointwise-id h `𝔹 = refl
renameᵗ-pointwise-id h (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-pointwise-id h A) (renameᵗ-pointwise-id h B)
renameᵗ-pointwise-id h (`∀ A) =
  cong `∀ (renameᵗ-pointwise-id (extᵗ-pointwise-id h) A)

renᶜ-pointwise-id : ∀ {ρ} → (∀ X → ρ X ≡ X)
  → ∀ c → renᶜ ρ c ≡ c
renᶜ-pointwise-id h (id A) = cong id (renameᵗ-pointwise-id h A)
renᶜ-pointwise-id h (seal X) = cong seal (h X)
renᶜ-pointwise-id h (unseal X) = cong unseal (h X)
renᶜ-pointwise-id h (s ↦ t) =
  cong₂ _↦_ (renᶜ-pointwise-id h s) (renᶜ-pointwise-id h t)
renᶜ-pointwise-id h (`∀ s) =
  cong `∀ (renᶜ-pointwise-id (extᵗ-pointwise-id h) s)

renᶠ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X)
  → ∀ δ → renᶠ² ρᵗ ρʳ δ ≡ renᶠᴿ ρʳ δ
renᶠ²-ord-id {ρʳ = ρʳ} h (unbind X α) =
  cong (λ X′ → unbind X′ (ρʳ α)) (h X)
renᶠ²-ord-id {ρʳ = ρʳ} h (bind X α) =
  cong (λ X′ → bind X′ (ρʳ α)) (h X)

renᴮ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X)
  → ∀ Θ → renᴮ² (ren² ρᵗ ρʳ) Θ ≡ renᴮᴿ ρʳ Θ
renᴮ²-ord-id {ρᵗ} {ρʳ} h χ = changes-id χ
  where
  changes-id : ∀ χ → map (renᶠ² ρᵗ ρʳ) χ ≡ map (renᶠᴿ ρʳ) χ
  changes-id [] = refl
  changes-id (δ ∷ χ) =
    cong₂ _∷_ (renᶠ²-ord-id h δ) (changes-id χ)

renᴹ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X) → ∀ M
  → renᴹ² (ren² ρᵗ ρʳ) M ≡ renᴹᴿ ρʳ M
renᴹ²-ord-id h (` x) = refl
renᴹ²-ord-id h ($ n) = refl
renᴹ²-ord-id h `true = refl
renᴹ²-ord-id h `false = refl
renᴹ²-ord-id h (ƛ A ∙ N) =
  cong₂ ƛ_∙_ (renameᵗ-pointwise-id h A) (renᴹ²-ord-id h N)
renᴹ²-ord-id h (L · M) =
  cong₂ _·_ (renᴹ²-ord-id h L) (renᴹ²-ord-id h M)
renᴹ²-ord-id h (Λ N) =
  cong Λ_ (renᴹ²-ord-id (extᵗ-pointwise-id h) N)
renᴹ²-ord-id {ρᵗ} {ρʳ} h (ν A · L ⟨ c ⟩) =
  trans
    (cong₂ (λ L′ c′ → ν renameᵗ ρᵗ A · L′ ⟨ c′ ⟩)
           (renᴹ²-ord-id h L)
           (renᶜ-pointwise-id (extᵗ-pointwise-id h) c))
    (cong (λ A′ → ν A′ · renᴹᴿ ρʳ L ⟨ c ⟩)
          (renameᵗ-pointwise-id h A))
renᴹ²-ord-id {ρᵗ} {ρʳ} h (M ⟪ Θ , c ⟫) =
  trans
    (cong (λ M′ →
             M′ ⟪ renᴮ² (ren² ρᵗ ρʳ) Θ , renᶜ ρᵗ c ⟫)
          (renᴹ²-ord-id h M))
    (trans
      (cong (λ Θ′ → renᴹᴿ ρʳ M
                         ⟪ Θ′ , renᶜ ρᵗ c ⟫)
            (renᴮ²-ord-id h Θ))
      (cong (λ c′ → renᴹᴿ ρʳ M
                         ⟪ renᴮᴿ ρʳ Θ , c′ ⟫)
            (renᶜ-pointwise-id h c)))

renᴹ : Renameᵗ → Term → Term
renᴹ ρ = renᴹ² (ren² ρ ρ)

wkN : ℕ → Renameᵗ
wkN zero    X = X
wkN (suc n) X = suc (wkN n X)

wkᴹ : ℕ → Term → Term
wkᴹ n = renᴹ (wkN n)

-- Crossing a term-level type binder weakens both free universes. The newly
-- bound ordinary variable names the newly bound abstract representation.
⇑ᴹ : Term → Term
⇑ᴹ = renᴹ² (ren² suc suc)

------------------------------------------------------------------------
-- 3. Term-variable renaming
------------------------------------------------------------------------

extⁿ : (Var → Var) → Var → Var
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (Var → Var) → Term → Term
renⁿ ρ (` x)          = ` (ρ x)
renⁿ ρ ($ n)          = $ n
renⁿ ρ `true           = `true
renⁿ ρ `false          = `false
renⁿ ρ (ƛ A ∙ N)      = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)        = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)          = Λ (renⁿ ρ N)
renⁿ ρ (ν A · L ⟨ c ⟩) = ν A · renⁿ ρ L ⟨ c ⟩
renⁿ ρ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

shiftᵐ : Term → Term
shiftᵐ = renⁿ suc

-- Ordinary-variable renaming never enters a boundary and a variable is
-- never a value, so values are preserved on the nose.
value-renⁿ : ∀ {M} {ρ : Var → Var} → Value M → Value (renⁿ ρ M)
value-renⁿ V-$         = V-$
value-renⁿ V-true      = V-true
value-renⁿ V-false     = V-false
value-renⁿ V-ƛ         = V-ƛ
value-renⁿ (V-Λ v)     = V-Λ (value-renⁿ v)
value-renⁿ (V-⟪⟫ v ic) = V-⟪⟫ v ic

∋-extⁿ : ∀ {Γ Γ′ A x B} {ρ : Var → Var}
  → (∀ {y C} → Γ ∋ y ⦂ C → Γ′ ∋ ρ y ⦂ C)
  → (A ∷ Γ) ∋ x ⦂ B
  → (A ∷ Γ′) ∋ extⁿ ρ x ⦂ B
∋-extⁿ h here      = here
∋-extⁿ h (there d) = there (h d)

------------------------------------------------------------------------
-- 4. Type-binder transport of term contexts
------------------------------------------------------------------------

∋-map⁻ : ∀ {f : Ty → Ty} {Γ x A′}
  → map f Γ ∋ x ⦂ A′
  → ∃[ A ] ((A′ ≡ f A) × (Γ ∋ x ⦂ A))
∋-map⁻ {Γ = []} ()
∋-map⁻ {Γ = A ∷ Γ} here = A , refl , here
∋-map⁻ {Γ = A ∷ Γ} (there d) with ∋-map⁻ d
∋-map⁻ {Γ = A ∷ Γ} (there d) | B , eq , q = B , eq , there q

∋-⤊ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⤊ Γ ∋ x ⦂ ⇑ᵗ A
∋-⤊ here      = here
∋-⤊ (there d) = there (∋-⤊ d)

⤊-∋ⁿ : ∀ {ρ : Var → Var} {Γ Γ′}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → (∀ {x A} → ⤊ Γ ∋ x ⦂ A → ⤊ Γ′ ∋ ρ x ⦂ A)
⤊-∋ⁿ h d with ∋-map⁻ d
⤊-∋ⁿ h d | A , refl , q = ∋-⤊ (h q)

⊢renⁿ : ∀ {Δ Γ Γ′ M A} {ρ : Var → Var}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ∣ Γ′ ⊢ renⁿ ρ M ⦂ A
⊢renⁿ h (⊢` d) = ⊢` (h d)
⊢renⁿ h ⊢$ = ⊢$
⊢renⁿ h ⊢true = ⊢true
⊢renⁿ h ⊢false = ⊢false
⊢renⁿ h (⊢ƛ w ⊢N) = ⊢ƛ w (⊢renⁿ (∋-extⁿ h) ⊢N)
⊢renⁿ h (⊢· ⊢L ⊢M) = ⊢· (⊢renⁿ h ⊢L) (⊢renⁿ h ⊢M)
⊢renⁿ h (⊢Λ vN ⊢N) = ⊢Λ (value-renⁿ vN) (⊢renⁿ (⤊-∋ⁿ h) ⊢N)
⊢renⁿ h (⊢ν wA rA ⊢L mw ⊢c same wB) =
  ⊢ν wA rA (⊢renⁿ h ⊢L) mw ⊢c same wB
⊢renⁿ h (env mwᵥ ⊢M ⊢c sameᵢ sameₑ wE) =
  env mwᵥ ⊢M ⊢c sameᵢ sameₑ wE

renⁿ-id : (ρ : Var → Var) → (∀ x → ρ x ≡ x)
  → (M : Term) → renⁿ ρ M ≡ M
renⁿ-id ρ h (` x) = cong `_ (h x)
renⁿ-id ρ h ($ n) = refl
renⁿ-id ρ h `true = refl
renⁿ-id ρ h `false = refl
renⁿ-id ρ h (ƛ A ∙ N) = cong (ƛ A ∙_) (renⁿ-id (extⁿ ρ) ext-id N)
  where
  ext-id : ∀ x → extⁿ ρ x ≡ x
  ext-id zero    = refl
  ext-id (suc x) = cong suc (h x)
renⁿ-id ρ h (L · M) = cong₂ _·_ (renⁿ-id ρ h L) (renⁿ-id ρ h M)
renⁿ-id ρ h (Λ N) = cong Λ_ (renⁿ-id ρ h N)
renⁿ-id ρ h (ν A · L ⟨ c ⟩) =
  cong (λ L′ → ν A · L′ ⟨ c ⟩) (renⁿ-id ρ h L)
renⁿ-id ρ h (M ⟪ Θ , c ⟫) = refl

⊢weakenⁿ : ∀ {Δ Γ M A}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ∣ Γ ⊢ M ⦂ A
⊢weakenⁿ {Γ = Γ} {M = M} {A = A} ⊢M =
  subst (λ N → _ ∣ Γ ⊢ N ⦂ A)
        (renⁿ-id idᵗ (λ x → refl) M)
        (⊢renⁿ (λ ()) ⊢M)

------------------------------------------------------------------------
-- 5. Term substitution
------------------------------------------------------------------------

-- Likewise for substitution: a value contains no free ordinary variable
-- at a value position, and boundaries are left alone.
value-substᵐ : ∀ {M} {σ : Var → Img} → Value M → Value (substᵐ σ M)
value-substᵐ V-$         = V-$
value-substᵐ V-true      = V-true
value-substᵐ V-false     = V-false
value-substᵐ V-ƛ         = V-ƛ
value-substᵐ (V-Λ v)     = V-Λ (value-substᵐ v)
value-substᵐ (V-⟪⟫ v ic) = V-⟪⟫ v ic

------------------------------------------------------------------------
-- 6. Typed images away from type-context transport
------------------------------------------------------------------------

infix 3 _∣_⊢ⁱ_⦂_
data _∣_⊢ⁱ_⦂_ : Ctxᵗ → Ctx → Img → Ty → Set where
  ⊢ivar : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ⁱ ivar x ⦂ A
  ⊢ival : ∀ {Δ Γ W A} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A
    → Δ ∣ Γ ⊢ⁱ ival W A ⦂ A

⊢imgTm : ∀ {Δ Γ i A}
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
  → Δ ∣ Γ ⊢ imgTm i ⦂ A
⊢imgTm (⊢ivar d) = ⊢` d
⊢imgTm (⊢ival w ⊢W) = ⊢weakenⁿ ⊢W

shiftᴵ-⊢ : ∀ {Δ Γ i A B}
  → Δ ∣ Γ ⊢ⁱ i ⦂ B
  → Δ ∣ A ∷ Γ ⊢ⁱ shiftᴵ i ⦂ B
shiftᴵ-⊢ (⊢ivar d) = ⊢ivar (there d)
shiftᴵ-⊢ (⊢ival w ⊢W) = ⊢ival w ⊢W

extᴵ-⊢ : ∀ {σ : Var → Img} {Δ Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B
        → Δ ∣ (A ∷ Γ′) ⊢ⁱ extᴵ σ x ⦂ B)
extᴵ-⊢ h here      = ⊢ivar here
extᴵ-⊢ h (there d) = shiftᴵ-⊢ (h d)

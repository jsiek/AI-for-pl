module strong-rep-nu.proof.Progress where

-- File Charter:
--   * PROGRESS for the two-universe conversion-boundary calculus.
--     §1 local inversions and representation readings; §2 the
--     `Merge` redex and its carried spellings (`merge-redex`); §3 base
--     identities; §4 the boundary cases; §5 the induction.
--   * The ordinary cases are the standard induction over
--     strong-rep-nu.proof.Canonical; the boundary cases additionally
--     CONSTRUCT the relational readings and weakenings the rules
--     carry, from `merged-conversion-exists`, `readable` and
--     `weaken`.  Nothing is a parameter.
--   * ONE BOUNDARY PER VALUE: a boundary over a boundary value is
--     ALWAYS a `Merge` redex, whatever its conversion.
--   * PROGRESS RETURNS THE STORE CHANGE TOO: every clause names the
--     `δ` its rule makes.
-- Commentary: Commentary.md § proof/Progress.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; extᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
open import strong-rep-nu.proof.Canonical
open import strong-rep-nu.proof.MoveScope using (merged-keeps₂)

private
  variable
    Δ Δ′ : Ctxᵗ
    A B R : Ty
    X α : ℕ

------------------------------------------------------------------------
-- 1. Local inversions and representation readings
------------------------------------------------------------------------

sameTy-base-src : Base A → Δ ⊢ B ≈ A ⊣ Δ′ → B ≡ A
sameTy-base-src base-ℕ (`ℕ , same-ℕ , same-ℕ) = refl
sameTy-base-src base-𝔹 (`𝔹 , same-𝔹 , same-𝔹) = refl

------------------------------------------------------------------------
-- 2. The merged frame's readings and the carried spellings
------------------------------------------------------------------------

-- `Merge`'s premises exist whenever a boundary sits over a value's
-- boundary: the merged conversion reading (`merged-conversion-exists`)
-- retains both old conversion contexts' names, so `weaken` moves each
-- conversion there.
-- Commentary.md § proof/Progress.agda / §2
merge-redex : ∀ {Δ Δᵢ Δ₂ᶜ U Θ₁ Θ₂ t₁ c₂ B C D}
  → Simple U → InertTail t₁
  → BoundaryWf Δ Θ₂ Δᵢ Δ₂ᶜ
  → Δᵢ ∣ [] ⊢ U ⟪ Θ₁ , tail t₁ ⟫ ⦂ B
  → Δ₂ᶜ ⊢ c₂ ∶ C ⇝ D
  → Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
      (Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ -→ M′ ∣ δ)
merge-redex u it mw₂ (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
  with merged-conversion-exists mw₂ mw₁
merge-redex u it mw₂ (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
  | Δ⋉ᶜ , r⋉ , keep₁ with readableᵀ ⊢t₁ | readable ⊢c₂
merge-redex u it mw₂ (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
  | Δ⋉ᶜ , r⋉ , keep₁ | r₁ , rd₁ | r₂ , rd₂
  with weakenᵀ keep₁ rd₁
     | weaken (merged-keeps₂ (bw-conversion mw₂) r⋉) rd₂
merge-redex u it mw₂ (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
  | Δ⋉ᶜ , r⋉ , keep₁ | r₁ , rd₁ | r₂ , rd₂ | t₁′ , rd₁′ | c₂′ , rd₂′ =
  _ , none
  , Merge u it (bw-interior mw₂) (bw-conversion mw₁) (bw-conversion mw₂)
          r⋉ (tail r₁ , sameᶜ-tail rd₁′ , sameᶜ-tail rd₁)
          (r₂ , rd₂′ , rd₂)

------------------------------------------------------------------------
-- 3. Base identities
------------------------------------------------------------------------

progress-id-base : ∀ {Δ Δᵢ Θ M A}
  → Value M
  → Base A
  → Δᵢ ∣ [] ⊢ M ⦂ A
  → Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
      (Δ ⊢ M ⟪ Θ , ⌞ id A ⌟ ⟫ -→ M′ ∣ δ)
progress-id-base v b ⊢M with canon-base v b ⊢M
progress-id-base v b ⊢M | inj₁ (n , refl) = $ n , none , Drop$ b
progress-id-base v base-ℕ ⊢M | inj₂ (inj₁ refl) with ⊢M
progress-id-base v base-ℕ ⊢M | inj₂ (inj₁ refl) | ()
progress-id-base v base-𝔹 ⊢M | inj₂ (inj₁ refl) =
  `true , none , Drop-true
progress-id-base v base-ℕ ⊢M | inj₂ (inj₂ refl) with ⊢M
progress-id-base v base-ℕ ⊢M | inj₂ (inj₂ refl) | ()
progress-id-base v base-𝔹 ⊢M | inj₂ (inj₂ refl) =
  `false , none , Drop-false

------------------------------------------------------------------------
-- 4. Progress
------------------------------------------------------------------------

module Impl where

  -- Once the interior is a value: a boundary over a boundary value is a
  -- `Merge` redex; over a simple value the conversion classification
  -- decides — inert is a value, `id` at a base type drops, and an
  -- unseal cannot occur (a simple value has no variable type).
  progress-boundary : ∀ {Δ Δᵢ Δᶜ Θ c M Bᵢ Cᵢ Cₑ}
    → Value M
    → BoundaryWf Δ Θ Δᵢ Δᶜ
    → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
    → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
    → Value (M ⟪ Θ , c ⟫)
      ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
           (Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ∣ δ))
  progress-boundary (V-⟪⟫ u it) mwΘ ⊢M ⊢c sameᵢ =
    inj₂ (merge-redex u it mwΘ ⊢M ⊢c)
  progress-boundary (V-simple u) mwΘ ⊢M ⊢c sameᵢ with act-or-inert ⊢c
  progress-boundary (V-simple u) mwΘ ⊢M ⊢c sameᵢ | inj₂ (I-tail it) =
    inj₁ (V-⟪⟫ u it)
  progress-boundary (V-simple u) mwΘ ⊢M ⊢c sameᵢ | inj₁ (A-idb b)
    with conv-id-base-src b ⊢c
  progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mwΘ ⊢M ⊢c sameᵢ
    | inj₁ (A-idb b) | refl =
    inj₂ (progress-id-base (V-simple u) b
      (⊢ty≡ (sameTy-base-src {Δ = Δᵢ} {Δ′ = Δᶜ} b sameᵢ) ⊢M))
  progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mwΘ ⊢M
    (conv-unseal d) sameᵢ | inj₁ A-unseal
    with ≈-var-source {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
  progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mwΘ ⊢M
    (conv-unseal d) sameᵢ | inj₁ A-unseal | Y , refl =
    ⊥-elim (simple-¬var u ⊢M)
  progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mwΘ ⊢M
    (conv-unseal-seq d ⊢c n m) sameᵢ | inj₁ A-unseal-seq
    with ≈-var-source {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
  progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mwΘ ⊢M
    (conv-unseal-seq d ⊢c n m) sameᵢ | inj₁ A-unseal-seq | Y , refl =
    ⊥-elim (simple-¬var u ⊢M)

  -- A function-conversion wrapper carries its own BoundaryWf and the domain
  -- conversion typing needed by the core `peel-premises-boundary` theorem.
  progress-peel : ∀ {Δ U M Θ s t A B}
    → Simple U
    → Value M
    → Δ ∣ [] ⊢ U ⟪ Θ , ⌞ s ↦ t ⌟ ⟫ ⦂ (A ⇒ B)
    → Σ[ N ∈ Term ] Σ[ δ ∈ Alloc ]
        (Δ ⊢ (U ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · M -→ N ∣ δ)
  progress-peel u vM
    (boundary mwΘ ⊢U (conv-tail (conv-mid (conv-fun ⊢s ⊢t))) sameᵢ sameₑ wE)
    with peel-premises-boundary mwΘ ⊢s
  progress-peel u vM
    (boundary mwΘ ⊢U (conv-tail (conv-mid (conv-fun ⊢s ⊢t))) sameᵢ sameₑ wE)
    | Δᵈ , s′ , rd , sc =
    _ , _ , Peel u vM (bw-conversion mwΘ) (bw-interior mwΘ) rd sc

  -- `ν` over a Λ under a ∀ middle: the middle's body typing is the
  -- rule's premise.
  progress-ν-∀conv : ∀ {Δ N Θ s c A C}
    → Value N
    → Δ ∣ [] ⊢ ν A · ((Λ N) ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩ ⦂ C
    → Σ[ M ∈ Term ] Σ[ δ ∈ Alloc ]
        (Δ ⊢ ν A · ((Λ N) ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩ -→ M ∣ δ)
  progress-ν-∀conv vN
    (⊢ν wA rA (boundary mwΘ ⊢V ⊢c sameᵢ sameₑ wE) mwν ⊢cν sameν wB)
    with conv-all-inv ⊢c
  progress-ν-∀conv vN
    (⊢ν wA rA (boundary mwΘ ⊢V ⊢c sameᵢ sameₑ wE) mwν ⊢cν sameν wB)
    | A₀ , B₀ , refl , eqₑ , ⊢s =
    _ , _ , Nu-⟪Λ⟫ vN (bw-conversion mwΘ) ⊢s rA

  ----------------------------------------------------------------------
  -- 5. The induction
  ----------------------------------------------------------------------

  progress : ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
    → Value M ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M -→ M′ ∣ δ))
  progress (⊢` ())
  progress ⊢$ = inj₁ (V-simple S-$)
  progress ⊢true = inj₁ (V-simple S-true)
  progress ⊢false = inj₁ (V-simple S-false)
  progress (⊢ƛ _ _) = inj₁ (V-simple S-ƛ)
  -- the value restriction: `⊢Λ` hands us the body's value proof
  progress (⊢Λ vN ⊢N) = inj₁ (V-simple (S-Λ vN))
  progress (⊢· ⊢L ⊢M) with progress ⊢L
  progress (⊢· ⊢L ⊢M) | inj₂ (L′ , δ , st) =
    inj₂ (L′ · ↑ᴹ[ δ ] _ , δ , ξ-·-l st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL with progress ⊢M
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₂ (M′ , δ , st) =
    inj₂ (↑ᴹ[ δ ] _ · M′ , δ , ξ-·-r vL st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM with canon-⇒ vL ⊢L
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM | inj₁ (N , refl) =
    inj₂ (_ , none , Beta vM)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM
    | inj₂ (U , Θ , s , t , u , refl) =
    inj₂ (progress-peel u vM ⊢L)
  progress (⊢ν wA rA ⊢L mw ⊢c same wB) with progress ⊢L
  progress (⊢ν wA rA ⊢L mw ⊢c same wB) | inj₂ (L′ , δ , st) =
    inj₂ (ν _ · L′ ⟨ _ ⟩ , δ , ξ-ν st)
  progress (⊢ν wA rA ⊢L mw ⊢c same wB) | inj₁ vL with canon-∀ vL ⊢L
  progress (⊢ν wA rA ⊢L mw ⊢c same wB) | inj₁ vL
    | inj₁ (N , vN , refl) = inj₂ (_ , _ , Nu-Λ vN rA)
  progress (⊢ν wA rA ⊢L mw ⊢c same wB) | inj₁ vL
    | inj₂ (N , Θ , s , vN , refl) =
    inj₂ (progress-ν-∀conv vN (⊢ν wA rA ⊢L mw ⊢c same wB))
  progress (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) with progress ⊢M
  progress (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₂ (M′ , δ , st) =
    inj₂ (M′ ⟪ ↑ᴮ[ δ ] _ , _ ⟫ , δ , ξ-⟪⟫ (bw-interior mwΘ) st)
  progress (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₁ vM =
    progress-boundary vM mwΘ ⊢M ⊢c sameᵢ

module strong-rep-nu.proof.ErasureRen where

-- File Charter:
--   * ERASURE UNDER A CHANGE OF STORE.  §1 the computed interior over
--     `map ρ`, `++`, `liftᴮ` and the sibling shift; §2 THE ONE LEMMA,
--     `erase-ren`: renaming the representation universe by ρ while the
--     store changes so that each renamed cell denotes τ of what the old
--     one did, erases to the source type substitution τ.  §3 its three
--     instances: the sibling shift (`erase-↑`), the crossing wrapper of
--     frame-exact substitution (`erase-cross`), and the cell `ν`
--     allocates (`erase-inst`).
--   * TYPED, BECAUSE OF THE JUNK LAW (proof/ErasureTypes): an unnamed
--     ordinary variable erases to itself, so the lemma holds on read
--     types only, and every type in a typed term is read.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (map-id)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx using (same-ren; names-underΛ-ren)
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Source using (STerm)
import strong-rep-nu.Source as S
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.Types using (substᵗ-renᵗ; extsᵗ-renᵗ)
open import strong-rep-nu.proof.TypeSubst
  using (subst-cong; subst-id; sub-sub; rename-subst-commute)
open import strong-rep-nu.proof.TermSubst
  using (extᵗ-pointwise-id; renᴹ²-ord-id)
open import strong-rep-nu.proof.Preserve using (wf-same)
open import strong-rep-nu.proof.ErasureTypes

------------------------------------------------------------------------
-- 1. The computed interior
------------------------------------------------------------------------

deleteAt-map : ∀ (ρ : Renameᵗ) X η
  → deleteAt X (map ρ η) ≡ map ρ (deleteAt X η)
deleteAt-map ρ X       []      = refl
deleteAt-map ρ zero    (α ∷ η) = refl
deleteAt-map ρ (suc X) (α ∷ η) = cong (ρ α ∷_) (deleteAt-map ρ X η)

insertAt-map : ∀ (ρ : Renameᵗ) X β η
  → insertAt X (ρ β) (map ρ η) ≡ map ρ (insertAt X β η)
insertAt-map ρ zero    β η       = refl
insertAt-map ρ (suc X) β []      = refl
insertAt-map ρ (suc X) β (α ∷ η) = cong (ρ α ∷_) (insertAt-map ρ X β η)

interiorⁿ-ren : ∀ (ρ : Renameᵗ) Θ η
  → interiorⁿ (renᴮᴿ ρ Θ) (map ρ η) ≡ map ρ (interiorⁿ Θ η)
interiorⁿ-ren ρ [] η = refl
interiorⁿ-ren ρ (unbind X α ∷ Θ) η =
  trans (cong (deleteAt X) (interiorⁿ-ren ρ Θ η))
        (deleteAt-map ρ X (interiorⁿ Θ η))
interiorⁿ-ren ρ (bind X α ∷ Θ) η =
  trans (cong (insertAt X (ρ α)) (interiorⁿ-ren ρ Θ η))
        (insertAt-map ρ X α (interiorⁿ Θ η))

interiorⁿ-++ : ∀ Θ₁ Θ₂ η
  → interiorⁿ (Θ₁ ++ Θ₂) η ≡ interiorⁿ Θ₁ (interiorⁿ Θ₂ η)
interiorⁿ-++ []       Θ₂ η = refl
interiorⁿ-++ (δ ∷ Θ₁) Θ₂ η = cong (act δ) (interiorⁿ-++ Θ₁ Θ₂ η)

interiorⁿ-lift : ∀ Θ η
  → interiorⁿ (liftᴮ Θ) (zero ∷ shiftReps η)
    ≡ zero ∷ shiftReps (interiorⁿ Θ η)
interiorⁿ-lift [] η = refl
interiorⁿ-lift (unbind X α ∷ Θ) η =
  trans (cong (deleteAt (suc X)) (interiorⁿ-lift Θ η))
        (cong (zero ∷_) (deleteAt-map suc X (interiorⁿ Θ η)))
interiorⁿ-lift (bind X α ∷ Θ) η =
  trans (cong (insertAt (suc X) (suc α)) (interiorⁿ-lift Θ η))
        (cong (zero ∷_) (insertAt-map suc X α (interiorⁿ Θ η)))

-- the sibling shift commutes with reading a boundary's interior
inside-apply : ∀ δ Δ Θ → inside (apply δ Δ) (↑ᴮ[ δ ] Θ) ≡ apply δ (inside Δ Θ)
inside-apply none    Δ Θ = refl
inside-apply (new R) (Ξ ∣ η) Θ =
  cong ((bindR R ∷ Ξ) ∣_) (interiorⁿ-ren suc Θ η)

eraseTy-apply : ∀ δ Δ A → eraseTy (apply δ Δ) A ≡ eraseTy Δ A
eraseTy-apply none    Δ A = refl
eraseTy-apply (new R) Δ A = subst-cong (nameσ-alloc R Δ) A

------------------------------------------------------------------------
-- 2. The lemma
------------------------------------------------------------------------

record EnvRel (ρ : Renameᵗ) (τ : Substᵗ) (Ξ₁ Ξ₂ : RepCtx) : Set where
  constructor envrel
  field
    env-rel : ∀ α → env Ξ₂ (ρ α) ≡ substᵗ τ (env Ξ₁ α)
open EnvRel public

EnvRel-cast : ∀ {ρ τ Ξ₁ Ξ₁′ Ξ₂} → Ξ₁′ ≡ Ξ₁ → EnvRel ρ τ Ξ₁ Ξ₂
  → EnvRel ρ τ Ξ₁′ Ξ₂
EnvRel-cast refl h = h

EnvRel-ext : ∀ {ρ τ Ξ₁ Ξ₂} → EnvRel ρ τ Ξ₁ Ξ₂
  → EnvRel (extᵗ ρ) (extsᵗ τ) (abstR ∷ Ξ₁) (abstR ∷ Ξ₂)
EnvRel-ext {ρ} {τ} {Ξ₁} {Ξ₂} h = envrel h′
  where
  h′ : ∀ α → env (abstR ∷ Ξ₂) (extᵗ ρ α)
             ≡ substᵗ (extsᵗ τ) (env (abstR ∷ Ξ₁) α)
  h′ zero    = refl
  h′ (suc α) = trans (cong ⇑ᵗ (env-rel h α)) (sym (exts-⇑ τ (env Ξ₁ α)))

-- a read type moves with the store
erase-ren-ty : ∀ {Δ₁ Ξ₂ η₂ A} (ρ : Renameᵗ) (τ : Substᵗ)
  → η₂ ≡ map ρ (names Δ₁)
  → EnvRel ρ τ (reps Δ₁) Ξ₂
  → Δ₁ ⊢ᵗ A
  → eraseTy (Ξ₂ ∣ η₂) A ≡ substᵗ τ (eraseTy Δ₁ A)
erase-ren-ty {Δ₁} {Ξ₂} {A = A} ρ τ refl h wA with wf-same wA
erase-ren-ty {Δ₁} {Ξ₂} {A = A} ρ τ refl h wA | R , p =
  trans (erase-~ {Δ = Ξ₂ ∣ map ρ (names Δ₁)} (same-ren ρ p))
    (trans (rename-subst-commute ρ (env Ξ₂) R)
      (trans (subst-∘ (env (reps Δ₁)) τ (λ α → env Ξ₂ (ρ α)) (env-rel h) R)
             (cong (substᵗ τ) (sym (erase-~ {Δ = Δ₁} p)))))

erase-ren : ∀ {Δ₁ Ξ₂ η₂ Γ M A} (ρ : Renameᵗ) (τ : Substᵗ)
  → η₂ ≡ map ρ (names Δ₁)
  → EnvRel ρ τ (reps Δ₁) Ξ₂
  → Δ₁ ∣ Γ ⊢ M ⦂ A
  → erase (Ξ₂ ∣ η₂) (renᴹᴿ ρ M) ≡ substˢᵗ τ (erase Δ₁ M)
erase-ren ρ τ eq h (⊢` d) = refl
erase-ren ρ τ eq h ⊢$ = refl
erase-ren ρ τ eq h ⊢true = refl
erase-ren ρ τ eq h ⊢false = refl
erase-ren ρ τ eq h (⊢ƛ wA ⊢N) =
  cong₂ S.ƛ_∙_ (erase-ren-ty ρ τ eq h wA) (erase-ren ρ τ eq h ⊢N)
erase-ren ρ τ eq h (⊢· ⊢L ⊢M) =
  cong₂ S._·_ (erase-ren ρ τ eq h ⊢L) (erase-ren ρ τ eq h ⊢M)
erase-ren {Δ₁} ρ τ refl h (⊢Λ vN ⊢N) =
  cong S.Λ_ (erase-ren (extᵗ ρ) (extsᵗ τ)
             (sym (names-underΛ-ren ρ (names Δ₁))) (EnvRel-ext h) ⊢N)
erase-ren ρ τ eq h (⊢ν wA rA ⊢L mw ⊢c same wB) =
  cong₂ S._[_] (erase-ren ρ τ eq h ⊢L) (erase-ren-ty ρ τ eq h wA)
erase-ren {Δ₁} {Ξ₂} ρ τ refl h
          (boundary {Δᵢ = Δᵢ} {Θ = Θ} {M = M} mw ⊢M ⊢c sᵢ sₑ wE) =
  trans (erase-ren ρ τ names-eq
           (EnvRel-cast (interior-reps (bw-interior mw)) h) ⊢M)
        (cong (λ D → substˢᵗ τ (erase D M))
              (sym (inside-sound (bw-interior mw))))
  where
  names-eq : interiorⁿ (renᴮᴿ ρ Θ) (map ρ (names Δ₁)) ≡ map ρ (names Δᵢ)
  names-eq = trans (interiorⁿ-ren ρ Θ (names Δ₁))
                   (cong (λ D → map ρ (names D))
                         (inside-sound (bw-interior mw)))

------------------------------------------------------------------------
-- 3. Instances
------------------------------------------------------------------------

private
  renᶠᴿ-id : ∀ {ρ : Renameᵗ} → (∀ X → ρ X ≡ X) → ∀ δ → renᶠᴿ ρ δ ≡ δ
  renᶠᴿ-id h (unbind X α) = cong (unbind X) (h α)
  renᶠᴿ-id h (bind X α)   = cong (bind X) (h α)

  renᴮᴿ-id : ∀ {ρ : Renameᵗ} → (∀ X → ρ X ≡ X) → ∀ Θ → renᴮᴿ ρ Θ ≡ Θ
  renᴮᴿ-id h []      = refl
  renᴮᴿ-id h (δ ∷ Θ) = cong₂ _∷_ (renᶠᴿ-id h δ) (renᴮᴿ-id h Θ)

renᴹᴿ-id : ∀ {ρ : Renameᵗ} → (∀ X → ρ X ≡ X) → ∀ M → renᴹᴿ ρ M ≡ M
renᴹᴿ-id h (` x) = refl
renᴹᴿ-id h ($ n) = refl
renᴹᴿ-id h `true = refl
renᴹᴿ-id h `false = refl
renᴹᴿ-id h (ƛ A ∙ N) = cong (ƛ A ∙_) (renᴹᴿ-id h N)
renᴹᴿ-id h (L · M) = cong₂ _·_ (renᴹᴿ-id h L) (renᴹᴿ-id h M)
renᴹᴿ-id h (Λ N) = cong Λ_ (renᴹᴿ-id (extᵗ-pointwise-id h) N)
renᴹᴿ-id h (ν A · L ⟨ c ⟩) = cong (λ L′ → ν A · L′ ⟨ c ⟩) (renᴹᴿ-id h L)
renᴹᴿ-id h (M ⟪ Θ , c ⟫) =
  cong₂ (λ M′ Θ′ → M′ ⟪ Θ′ , c ⟫) (renᴹᴿ-id h M) (renᴮᴿ-id h Θ)

-- THE SIBLING SHIFT is invisible
erase-↑ : ∀ {Δ Γ M A} δ → Δ ∣ Γ ⊢ M ⦂ A
  → erase (apply δ Δ) (↑ᴹ[ δ ] M) ≡ erase Δ M
erase-↑ none ⊢M = refl
erase-↑ {Δ = Ξ ∣ η} {M = M} (new R) ⊢M =
  trans (erase-ren suc `_ refl (envrel (λ α → sym (subst-id (env Ξ α)))) ⊢M)
        (substˢᵗ-id (λ X → refl) (erase (Ξ ∣ η) M))

-- THE CROSSING WRAPPER of frame-exact substitution erases to the
-- type-shifted image
erase-cross : ∀ {Δ W A} → Δ ∣ [] ⊢ W ⦂ A
  → erase (underΛ Δ) (crossΛᴹ W A) ≡ renameˢᵗ suc (erase Δ W)
erase-cross {Δ = Ξ ∣ η} {W = W} ⊢W =
  trans (cong (erase ((abstR ∷ Ξ) ∣ shiftReps η))
              (renᴹ²-ord-id (λ X → refl) W))
    (trans (erase-ren suc (renᵗ suc) refl
              (envrel (λ α → sym (substᵗ-renᵗ suc (env Ξ α)))) ⊢W)
           (substˢᵗ-renᵗ suc (erase (Ξ ∣ η) W)))

-- THE CELL `ν` ALLOCATES: a body read under the abstract cell, re-read
-- with the cell holding R, is the source instantiation at ⌊R⌋
erase-inst : ∀ {Ξ η Γ N C} R
  → ((abstR ∷ Ξ) ∣ (zero ∷ shiftReps η)) ∣ Γ ⊢ N ⦂ C
  → erase ((bindR R ∷ Ξ) ∣ (zero ∷ shiftReps η)) N
    ≡ (erase ((abstR ∷ Ξ) ∣ (zero ∷ shiftReps η)) N) [ substᵗ (env Ξ) R ]ᵀ
erase-inst {Ξ} {η} {N = N} R ⊢N =
  trans (cong (erase ((bindR R ∷ Ξ) ∣ (zero ∷ shiftReps η)))
              (sym (renᴹᴿ-id (λ X → refl) N)))
        (erase-ren (λ X → X) (singleTyEnv (substᵗ (env Ξ) R))
           (sym (map-id (zero ∷ shiftReps η))) (envrel h) ⊢N)
  where
  h : ∀ α → env (bindR R ∷ Ξ) α
        ≡ substᵗ (singleTyEnv (substᵗ (env Ξ) R)) (env (abstR ∷ Ξ) α)
  h zero    = refl
  h (suc α) = sym (single-⇑ (substᵗ (env Ξ) R) (env Ξ α))

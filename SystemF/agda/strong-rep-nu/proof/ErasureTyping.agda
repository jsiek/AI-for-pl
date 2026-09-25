module strong-rep-nu.proof.ErasureTyping where

-- File Charter:
--   * ERASURE PRESERVES TYPING: `erasure-typing` (stated as
--     `ErasureTyping` in strong-rep-nu.ErasureTheorems).
--   * The two non-System-F rules are the content.  `boundary`: the body
--     is erased at its interior, and the conversion is an
--     erasure-identity (`conv-erase`), so the interior and exterior types
--     erase alike.  `⊢ν`: the conversion context of `[bind X α]` over
--     the allocation differs from `under(X,α,Δ)` only in cell α
--     (`nu-type`), so the result type is the source instantiation.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst; subst₂)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Source
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.TypeSubst using (sub-sub; subst-cong)
open import strong-rep-nu.proof.Preserve
  using (wf-underΛ; empty-conversion)
open import strong-rep-nu.proof.ErasureTypes

------------------------------------------------------------------------
-- The ν result type
------------------------------------------------------------------------

-- the cell `ν` allocates, read abstractly, is what `under` reads
env-bind-abs : ∀ Ξ R (α : ℕ)
  → env (bindR R ∷ Ξ) α
    ≡ substᵗ (singleTyEnv (substᵗ (env Ξ) R)) (env (abstR ∷ Ξ) α)
env-bind-abs Ξ R zero    = refl
env-bind-abs Ξ R (suc α) = sym (single-⇑ (substᵗ (env Ξ) R) (env Ξ α))

-- A type read at the conversion context `(Ξ, α := R) ∣ (Γ, X ↦ α)`
-- erases to its erasure under `under(X,α,Δ)` instantiated at ⌊A⌋.
nu-read : ∀ Ξ η R C Rc
  → (zero ∷ shiftReps η) ⊢ C ~ Rc
  → eraseTy ((bindR R ∷ Ξ) ∣ (zero ∷ shiftReps η)) C
    ≡ (substᵗ (extsᵗ (nameσ (Ξ ∣ η))) C) [ substᵗ (env Ξ) R ]ᵗ
nu-read Ξ η R C Rc p =
  trans (erase-~ {Δ = (bindR R ∷ Ξ) ∣ (zero ∷ shiftReps η)} p)
    (trans (subst-∘ (env (abstR ∷ Ξ)) (singleTyEnv a) (env (bindR R ∷ Ξ))
                    (env-bind-abs Ξ R) Rc)
      (cong (substᵗ (singleTyEnv a))
        (trans (sym (erase-~ {Δ = underΛ (Ξ ∣ η)} p))
               (erase-underΛ (Ξ ∣ η) C))))
  where
  a = substᵗ (env Ξ) R

nu-type : ∀ {Δ Δᵢ Δᶜ A R C Cₑ B c}
  → Δ ⊢ᶜ A ~ R
  → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
  → Δᶜ ⊢ c ∶ C ⇝ Cₑ
  → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
  → (substᵗ (extsᵗ (nameσ Δ)) C) [ eraseTy Δ A ]ᵗ ≡ eraseTy Δ B
nu-type {Δ = Ξ ∣ η} {A = A} {R = R} {C = C} {Cₑ = Cₑ} {B = B}
        rA mw ⊢c same
  with conversion-functional (bw-conversion mw)
         (inst-conversion {R = R} {Θ = []} (empty-conversion {Δ = Ξ ∣ η}))
nu-type {Δ = Ξ ∣ η} {A = A} {R = R} {C = C} {Cₑ = Cₑ} {B = B}
        rA mw ⊢c same | refl =
  trans (cong (λ a → (substᵗ (extsᵗ (nameσ (Ξ ∣ η))) C) [ a ]ᵗ)
              (erase-~ {Δ = Ξ ∣ η} rA))
    (trans (sym (nu-read Ξ η R C (proj₁ (proj₁ (conv-scoped ⊢c)))
                         (proj₂ (proj₁ (conv-scoped ⊢c)))))
      (trans (conv-erase ⊢c)
        (trans (sym (erase-≈ refl same))
               (subst-cong (nameσ-alloc R (Ξ ∣ η)) B))))

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

erasure-typing : ∀ {Δ Γ M A}
  → WfCtx Δ
  → Δ ∣ Γ ⊢ M ⦂ A
  → srcScope (reps Δ) ∣ eraseCtx Δ Γ ⊢ˢ erase Δ M ⦂ eraseTy Δ A
erasure-typing w (⊢` d) = ⊢ˢ` (∋-map d)
erasure-typing w ⊢$ = ⊢ˢ$
erasure-typing w ⊢true = ⊢ˢtrue
erasure-typing w ⊢false = ⊢ˢfalse
erasure-typing w (⊢ƛ wA ⊢N) = ⊢ˢƛ (erase-wf w wA) (erasure-typing w ⊢N)
erasure-typing w (⊢· ⊢L ⊢M) =
  ⊢ˢ· (erasure-typing w ⊢L) (erasure-typing w ⊢M)
erasure-typing {Δ} {Γ} w (⊢Λ {C = C} {N = N} vN ⊢N) =
  ⊢ˢΛ (value-erase vN)
    (subst₂ (λ Γ′ C′ → suc (srcScope (reps Δ)) ∣ Γ′
                         ⊢ˢ erase (underΛ Δ) N ⦂ C′)
            (eraseCtx-⤊ Δ Γ) (erase-underΛ Δ C)
            (erasure-typing (wf-underΛ w) ⊢N))
erasure-typing {Δ} {Γ} w (⊢ν {A = A} {L = L} wA rA ⊢L mw ⊢c same wB) =
  subst (λ B′ → srcScope (reps Δ) ∣ eraseCtx Δ Γ
                  ⊢ˢ erase Δ L [ eraseTy Δ A ] ⦂ B′)
        (nu-type rA mw ⊢c same)
        (⊢ˢ[] (erasure-typing w ⊢L) (erase-wf w wA))
erasure-typing {Δ} {Γ} w
    (boundary {Δᵢ = Δᵢ} {Θ = Θ} {M = M} {Bᵢ = Bᵢ} {Bₑ = Bₑ}
              mw ⊢M ⊢c sameᵢ sameₑ wE) =
  subst₂ (λ n T → n ∣ eraseCtx Δ Γ ⊢ˢ T ⦂ eraseTy Δ Bₑ)
    (cong srcScope (interior-reps (bw-interior mw)))
    (cong (λ Δ′ → erase Δ′ M) (sym (inside-sound (bw-interior mw))))
    (⊢ˢ-weaken
      (subst (λ T → srcScope (reps Δᵢ) ∣ [] ⊢ˢ erase Δᵢ M ⦂ T) ty-eq
        (erasure-typing (bw-interior-wf mw) ⊢M)))
  where
  ty-eq : eraseTy Δᵢ Bᵢ ≡ eraseTy Δ Bₑ
  ty-eq =
    trans (erase-≈ (trans (interior-reps (bw-interior mw))
                          (sym (conversion-reps (bw-conversion mw))))
                   sameᵢ)
      (trans (conv-erase ⊢c)
        (sym (erase-≈ (sym (conversion-reps (bw-conversion mw))) sameₑ)))

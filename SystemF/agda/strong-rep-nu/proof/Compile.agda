module strong-rep-nu.proof.Compile where

-- File Charter:
--   * THE PROOF THAT `compile` PRESERVES TYPING (stated at the top level
--     in strong-rep-nu.CompileTyping).  §1 source formation is run-time
--     formation on any context with as many live names; §2 the theorem.
--     The `ν` case is the old `preserve-TyBeta`'s construction: the
--     compiled conversion `reveal 0 C` is typed at the conversion context
--     of `inst []` over the allocation, exactly where `Nu-Λ` puts it.

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Properties using (length-map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.Source
open import strong-rep-nu.Compile
open import strong-rep-nu.proof.Preserve

------------------------------------------------------------------------
-- 1.  Source formation
------------------------------------------------------------------------

lookup-< : ∀ {xs : List RVar} {X : ℕ} → X < length xs
  → ∃[ α ] (xs ∋ˡ X := α)
lookup-< {xs = x ∷ xs} {X = zero}  (s≤s z≤n) = x , here
lookup-< {xs = x ∷ xs} {X = suc X} (s≤s p) with lookup-< p
lookup-< {xs = x ∷ xs} {X = suc X} (s≤s p) | α , d = α , there d

names-underΛ-length : ∀ {Δ : Ctxᵗ} {n : ℕ} → length (names Δ) ≡ n
  → length (names (underΛ Δ)) ≡ suc n
names-underΛ-length {Δ = Δ} eq =
  cong suc (trans (length-map suc (names Δ)) eq)

swf→wf : ∀ {Δ : Ctxᵗ} {n : ℕ} {A : Ty} → length (names Δ) ≡ n
  → n ⊢ˢ A → Δ ⊢ᵗ A
swf→wf refl (swf-var p) = wf-var (lookup-< p)
swf→wf eq swf-ℕ = wf-ℕ
swf→wf eq swf-𝔹 = wf-𝔹
swf→wf eq (swf-⇒ wA wB) = wf-⇒ (swf→wf eq wA) (swf→wf eq wB)
swf→wf {Δ = Δ} eq (swf-∀ wA) =
  wf-∀ (swf→wf (names-underΛ-length {Δ = Δ} eq) wA)

------------------------------------------------------------------------
-- 2.  compile preserves typing
------------------------------------------------------------------------

-- the `ν` case: every premise of `⊢ν` for `ν A · L ⟨ reveal 0 C ⟩`
compile-ν : ∀ {Δ Γ A C L}
  → WfCtx Δ → CtxWf Δ Γ → Δ ⊢ᵗ A
  → Δ ∣ Γ ⊢ L ⦂ `∀ C
  → Δ ∣ Γ ⊢ ν A · L ⟨ reveal 0 C ⟩ ⦂ C [ A ]ᵗ
compile-ν {Δ = Δ} {A = A} {C = C} wfΔ h wA ⊢L
  with wf-same wA | ⊢ᵗ-of h ⊢L
compile-ν {Δ = Δ} {A = A} {C = C} wfΔ h wA ⊢L
  | R , p | wf-∀ wC =
  ⊢ν wA p ⊢L mwβ conv sameₑ wE₀
  where
  ΔR : Ctxᵗ
  ΔR = (bindR R ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ))

  refine : RepRefines (reps (underΛ Δ)) (reps ΔR)
  refine = rr-represent rr-refl

  conv : ΔR ⊢ reveal 0 C ∶ C ⇝ ⇑ᵗ (C [ A ]ᵗ)
  conv rewrite sym (subst-at-0 A C) =
    ⊢reveal (represented-lookup p) (wf-refine refine wC)

  wE₀ : Δ ⊢ᵗ C [ A ]ᵗ
  wE₀ = wf-[]ᵗ wC wA

  sameₑ : allocate R Δ ⊢ C [ A ]ᵗ ≈ ⇑ᵗ (C [ A ]ᵗ) ⊣ ΔR
  sameₑ with wf-same wE₀
  sameₑ | S , q = ⇑ᵗ S , same-shift-free q , same-weaken q

  mwβ : BoundaryWf (allocate R Δ) TyBetaBoundary ΔR ΔR
  mwβ =
    bw (alloc-wf wfΔ (same-wfᴿ wfΔ p))
       (inst-interior {R = R} empty-interior)
       (inst-conversion {R = R} empty-conversion)

compile-⊢ : ∀ {n Δ Γ M A}
  → WfCtx Δ → CtxWf Δ Γ → length (names Δ) ≡ n
  → (d : n ∣ Γ ⊢ˢ M ⦂ A) → Δ ∣ Γ ⊢ compile d ⦂ A
compile-⊢ wfΔ h eq (⊢ˢ` x) = ⊢` x
compile-⊢ wfΔ h eq ⊢ˢ$ = ⊢$
compile-⊢ wfΔ h eq ⊢ˢtrue = ⊢true
compile-⊢ wfΔ h eq ⊢ˢfalse = ⊢false
compile-⊢ wfΔ h eq (⊢ˢƛ w d) =
  ⊢ƛ wA (compile-⊢ wfΔ (CtxWf-∷ wA h) eq d)
  where wA = swf→wf eq w
compile-⊢ wfΔ h eq (⊢ˢ· d e) =
  ⊢· (compile-⊢ wfΔ h eq d) (compile-⊢ wfΔ h eq e)
compile-⊢ {Δ = Δ} wfΔ h eq (⊢ˢΛ v d) =
  ⊢Λ (compile-value d v)
     (compile-⊢ (wf-underΛ wfΔ) (CtxWf-⤊ h)
                (names-underΛ-length {Δ = Δ} eq) d)
compile-⊢ wfΔ h eq (⊢ˢ[] d w) =
  compile-ν wfΔ h (swf→wf eq w) (compile-⊢ wfΔ h eq d)

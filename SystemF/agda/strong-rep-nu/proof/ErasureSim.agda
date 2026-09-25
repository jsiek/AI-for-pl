module strong-rep-nu.proof.ErasureSim where

-- File Charter:
--   * THE SIMULATION.  `erasure-stutter` (a `Wrap`, `Merge` or `Id`
--     step, under congruences, leaves the erasure unchanged) and
--     `erasure-step` (every other step is exactly one source step), then
--     `erasure-sim` (their disjunction), `erasure-run` (along a run, with
--     preservation) and `compiled-run-erases`.
--   * Per rule: `TyBeta`/`TyWrap` are `β-Λ` by `erase-inst`; `Beta` is
--     `β-ƛ` by `erase-beta`; `Wrap` stutters because the dual restores
--     the name map; `Merge` because `interiorⁿ` of a merged scope is the
--     composite; `Id` because typing makes the body a literal.  The
--     congruences use `erase-↑` (siblings), `eraseTy-apply` (`ν`'s
--     argument) and `inside-apply` (a boundary's interior).

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst; subst₂)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx using (wf-empty)
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
import strong-rep-nu.Source as S
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Compile using (compile)
open import strong-rep-nu.CompileTyping using (compile-closed)
open import strong-rep-nu.Preservation using (preservation; preservation-wf)
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.ErasureTypes
open import strong-rep-nu.proof.ErasureRen
open import strong-rep-nu.proof.ErasureSubst using (erase-beta)
open import strong-rep-nu.proof.ErasureCompile using (erase-compile)

------------------------------------------------------------------------
-- 1. Base-typed simple values are literals
------------------------------------------------------------------------

private
  read-base : ∀ {η A R} → η ⊢ A ~ R → Base A → Base R
  read-base same-ℕ base-ℕ = base-ℕ
  read-base same-𝔹 base-𝔹 = base-𝔹
  read-base (same-var d) ()
  read-base (same-⇒ p q) ()
  read-base (same-∀ p) ()

  base-read : ∀ {η A R} → η ⊢ A ~ R → Base R → Base A
  base-read same-ℕ base-ℕ = base-ℕ
  base-read same-𝔹 base-𝔹 = base-𝔹
  base-read (same-var d) ()
  base-read (same-⇒ p q) ()
  base-read (same-∀ p) ()

  literal-erase : ∀ {Δ U B} Δ₁ Δ₂ → Simple U → Δ ∣ [] ⊢ U ⦂ B → Base B
    → erase Δ₁ U ≡ erase Δ₂ U
  literal-erase Δ₁ Δ₂ S-$ ⊢$ b = refl
  literal-erase Δ₁ Δ₂ S-true ⊢true b = refl
  literal-erase Δ₁ Δ₂ S-false ⊢false b = refl
  literal-erase Δ₁ Δ₂ S-ƛ (⊢ƛ w ⊢N) ()
  literal-erase Δ₁ Δ₂ (S-Λ v) (⊢Λ vN ⊢N) ()

------------------------------------------------------------------------
-- 2. Stutters
------------------------------------------------------------------------

erasure-stutter : ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→ M′ ∣ δ)
  → Stutter r
  → erase Δ M ≡ erase (apply δ Δ) M′
erasure-stutter w ⊢M (TyBeta v p) ()
erasure-stutter w ⊢M (Beta v) ()
erasure-stutter w ⊢M (TyWrap v rc ⊢s p) ()
erasure-stutter {Δ} w ⊢M
    (Wrap {V = V} {W = W} {Θ = Θ} v wv rc ri rd sc) s =
  cong (S._·_ (erase (inside Δ Θ) V))
       (cong (λ D → erase D W) (sym back))
  where
  back : inside (inside Δ Θ) (dual Θ) ≡ Δ
  back = trans (cong (λ D → inside D (dual Θ)) (inside-sound ri))
               (inside-sound (dual-interior ri))
erasure-stutter {Ξ ∣ η} w ⊢M
    (Merge {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} u it ri r₁ r₂ r⋉ sc₁ sc₂) s =
  cong (λ η′ → erase (Ξ ∣ η′) U) (sym (interiorⁿ-++ Θ₁ Θ₂ η))
erasure-stutter {Δ} w
    (boundary mw ⊢U (conv-tail (conv-mid (conv-id b′)))
              (Rᵢ , pᵢ , qᵢ) sₑ wE)
    (Id {Θ = Θ} u b) s =
  literal-erase _ Δ u ⊢U (base-read pᵢ (read-base qᵢ b′))
erasure-stutter w
    (boundary mw ⊢U (conv-tail (conv-mid (conv-idv tv))) sᵢ sₑ wE)
    (Id u ()) s
erasure-stutter {Δ} w (⊢· ⊢L ⊢M) (ξ-·₁ {δ = δ} st) s =
  cong₂ S._·_ (erasure-stutter w ⊢L st s) (sym (erase-↑ δ ⊢M))
erasure-stutter {Δ} w (⊢· ⊢V ⊢M) (ξ-·₂ {δ = δ} v st) s =
  cong₂ S._·_ (sym (erase-↑ δ ⊢V)) (erasure-stutter w ⊢M st s)
erasure-stutter {Δ} w (⊢ν {A = A} wA rA ⊢L mw ⊢c same wB)
    (ξ-ν {δ = δ} st) s =
  cong₂ S._[_] (erasure-stutter w ⊢L st s) (sym (eraseTy-apply δ Δ A))
erasure-stutter {Δ} w (boundary mw ⊢M ⊢c sᵢ sₑ wE)
    (ξ-⟪⟫ {Δᵢ = Δᵢ} {M = M} {M′ = M′} {Θ = Θ} {δ = δ} ri st) s
  with interior-functional ri (bw-interior mw)
erasure-stutter {Δ} w (boundary mw ⊢M ⊢c sᵢ sₑ wE)
    (ξ-⟪⟫ {Δᵢ = Δᵢ} {M = M} {M′ = M′} {Θ = Θ} {δ = δ} ri st) s
  | refl =
  trans (cong (λ D → erase D M) (inside-sound ri))
    (trans (erasure-stutter (bw-interior-wf mw) ⊢M st s)
      (cong (λ D → erase D M′)
        (sym (trans (inside-apply δ Δ Θ)
                    (cong (apply δ) (inside-sound ri))))))

------------------------------------------------------------------------
-- 3. Source steps
------------------------------------------------------------------------

erasure-step : ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→ M′ ∣ δ)
  → ¬ Stutter r
  → erase Δ M ⟶ˢ erase (apply δ Δ) M′
erasure-step {Ξ ∣ η} w (⊢ν {A = A} wA rA (⊢Λ vN ⊢N) mw ⊢c same wB)
    (TyBeta {R = R} {N = N} {c = c} v p) ns =
  subst (λ T → erase (Ξ ∣ η) (ν A · Λ N ⟨ c ⟩) ⟶ˢ T)
    (sym (trans (erase-inst R ⊢N)
                (cong (erase (underΛ (Ξ ∣ η)) N [_]ᵀ)
                      (sym (erase-~ {Δ = Ξ ∣ η} p)))))
    (β-Λ (value-erase v))
erasure-step {Δ} w (⊢· (⊢ƛ {A = A} {N = N} wA ⊢N) ⊢W) (Beta {W = W} v) ns =
  subst (λ T → (S.ƛ eraseTy Δ A ∙ erase Δ N) S.· erase Δ W ⟶ˢ T)
    (sym (erase-beta w wA ⊢N ⊢W)) (β-ƛ (value-erase v))
erasure-step {Ξ ∣ η} w
    (⊢ν {A = A} wA rA (boundary mw (⊢Λ vN ⊢N) ⊢c′ sᵢ sₑ wE) mw′ ⊢c same wB)
    (TyWrap {N = N} {Θ = Θ} {R = R} v rc ⊢s p) ns =
  subst (λ T → _ ⟶ˢ T)
    (sym (trans (cong (λ η′ → erase ((bindR R ∷ Ξ) ∣ η′) N)
                      (interiorⁿ-lift Θ η))
           (trans (erase-inst R ⊢N′)
                  (cong (erase (underΛ (inside (Ξ ∣ η) Θ)) N [_]ᵀ)
                        (sym (erase-~ {Δ = Ξ ∣ η} p))))))
    (β-Λ (value-erase v))
  where
  ⊢N′ : underΛ (inside (Ξ ∣ η) Θ) ∣ [] ⊢ N ⦂ _
  ⊢N′ = subst (λ D → underΛ D ∣ [] ⊢ N ⦂ _)
              (sym (inside-sound (bw-interior mw))) ⊢N
erasure-step w ⊢M (Wrap v wv rc ri rd sc) ns = ⊥-elim (ns tt)
erasure-step w ⊢M (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) ns = ⊥-elim (ns tt)
erasure-step w ⊢M (Id u b) ns = ⊥-elim (ns tt)
erasure-step {Δ} w (⊢· ⊢L ⊢M) (ξ-·₁ {L′ = L′} {δ = δ} st) ns =
  subst (λ T → _ ⟶ˢ S._·_ (erase (apply δ Δ) L′) T)
    (sym (erase-↑ δ ⊢M))
    (ξˢ-·₁ (erasure-step w ⊢L st ns))
erasure-step {Δ} w (⊢· ⊢V ⊢M) (ξ-·₂ {M′ = M′} {δ = δ} v st) ns =
  subst (λ T → _ ⟶ˢ S._·_ T (erase (apply δ Δ) M′))
    (sym (erase-↑ δ ⊢V))
    (ξˢ-·₂ (value-erase v) (erasure-step w ⊢M st ns))
erasure-step {Δ} w (⊢ν {A = A} wA rA ⊢L mw ⊢c same wB)
    (ξ-ν {L′ = L′} {δ = δ} st) ns =
  subst (λ T → _ ⟶ˢ S._[_] (erase (apply δ Δ) L′) T)
    (sym (eraseTy-apply δ Δ A))
    (ξˢ-[] (erasure-step w ⊢L st ns))
erasure-step {Δ} w (boundary mw ⊢M ⊢c sᵢ sₑ wE)
    (ξ-⟪⟫ {Δᵢ = Δᵢ} {M = M} {M′ = M′} {Θ = Θ} {δ = δ} ri st) ns
  with interior-functional ri (bw-interior mw)
erasure-step {Δ} w (boundary mw ⊢M ⊢c sᵢ sₑ wE)
    (ξ-⟪⟫ {Δᵢ = Δᵢ} {M = M} {M′ = M′} {Θ = Θ} {δ = δ} ri st) ns
  | refl =
  subst₂ _⟶ˢ_
    (cong (λ D → erase D M) (sym (inside-sound ri)))
    (cong (λ D → erase D M′)
          (sym (trans (inside-apply δ Δ Θ)
                      (cong (apply δ) (inside-sound ri)))))
    (erasure-step (bw-interior-wf mw) ⊢M st ns)

------------------------------------------------------------------------
-- 4. Consequences
------------------------------------------------------------------------

stutter? : ∀ {Δ M M′ δ} (r : Δ ⊢ M -→ M′ ∣ δ)
  → T (isStutter r) ⊎ ¬ T (isStutter r)
stutter? r with isStutter r
stutter? r | true  = inj₁ tt
stutter? r | false = inj₂ (λ ())

erasure-sim : ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
  → (erase Δ M ≡ erase (apply δ Δ) M′)
    ⊎ (erase Δ M ⟶ˢ erase (apply δ Δ) M′)
erasure-sim w ⊢M r with stutter? r
erasure-sim w ⊢M r | inj₁ s  = inj₁ (erasure-stutter w ⊢M r s)
erasure-sim w ⊢M r | inj₂ ns = inj₂ (erasure-step w ⊢M r ns)

erasure-run : ∀ {Δ M N A}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* N)
  → erase Δ M ⟶ˢ* erase (runCtx r) N
erasure-run w ⊢M done = doneˢ
erasure-run w ⊢M (st then sts) with erasure-sim w ⊢M st
erasure-run w ⊢M (st then sts) | inj₁ eq =
  subst (_⟶ˢ* _) (sym eq)
    (erasure-run (preservation-wf w ⊢M st) (preservation w ⊢M st) sts)
erasure-run w ⊢M (st then sts) | inj₂ s =
  s thenˢ
    erasure-run (preservation-wf w ⊢M st) (preservation w ⊢M st) sts

compiled-run-erases : ∀ {M A N}
  → (d : 0 S.∣ [] ⊢ˢ M ⦂ A)
  → (r : empty ⊢ compile d -→* N)
  → M ⟶ˢ* erase (runCtx r) N
compiled-run-erases {N = N} d r =
  subst (_⟶ˢ* erase (runCtx r) N) (erase-compile d) (erasure-run wf-empty (compile-closed d) r)

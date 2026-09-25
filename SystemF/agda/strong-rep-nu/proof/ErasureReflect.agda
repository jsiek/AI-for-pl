module strong-rep-nu.proof.ErasureReflect where

-- File Charter:
--   * REFLECTION: every source step of a typed term's erasure is matched
--     by a run — finitely many stutters, then one step that is not a
--     stutter.  `erasure-reflection`, via the split:
--     (a) STUTTERS TERMINATE: `weight` strictly decreases along every
--         stutter (`stutter-weight`), on any term, typed or not;
--     (b) a source step is DETERMINISTIC (`detˢ`) and a source value
--         does not step (`svalue-¬step`), so by progress the typed term
--         steps, and a non-stutter step lands exactly on the source
--         step's target (`erasure-step`).
--   * THE MEASURE.  A boundary weighs one; an application weighs three
--     times its operator, plus its operand, plus one.  `Wrap` moves one
--     boundary from the operator to the operand (weight 3 → 1) and wraps
--     the application in a boundary (+1): a net decrease of one.
--     `Merge` and `Id` remove a boundary.  Nothing reads a type or a
--     representation, so the sibling shift keeps the weight.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-monoˡ-<; +-monoʳ-<; *-monoʳ-<; ≤-trans; <-trans; n<1+n; ≤-refl)
open import Data.List using ([])
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
import strong-rep-nu.Source as S
open import strong-rep-nu.Source using (SValue; SV-$; SV-true; SV-false;
  SV-ƛ; SV-Λ)
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Progress using (progress)
open import strong-rep-nu.Preservation using (preservation; preservation-wf)
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.ErasureTypes using (value-erase)
open import strong-rep-nu.proof.ErasureSim
  using (erasure-stutter; erasure-step; stutter?)

------------------------------------------------------------------------
-- (a) Stutters terminate
------------------------------------------------------------------------

weight : Term → ℕ
weight (` x)           = zero
weight ($ n)           = zero
weight `true           = zero
weight `false          = zero
weight (ƛ A ∙ N)       = weight N
weight (L · M)         = suc (3 * weight L + weight M)
weight (Λ N)           = weight N
weight (ν A · L ⟨ c ⟩) = suc (weight L)
weight (M ⟪ Θ , c ⟫)   = suc (weight M)

weight-ren : ∀ (ρ : Renameᵗ) M → weight (renᴹᴿ ρ M) ≡ weight M
weight-ren ρ (` x) = refl
weight-ren ρ ($ n) = refl
weight-ren ρ `true = refl
weight-ren ρ `false = refl
weight-ren ρ (ƛ A ∙ N) = weight-ren ρ N
weight-ren ρ (L · M) =
  cong suc (cong₂ (λ a b → 3 * a + b) (weight-ren ρ L) (weight-ren ρ M))
weight-ren ρ (Λ N) = weight-ren (extᵗ ρ) N
weight-ren ρ (ν A · L ⟨ c ⟩) = cong suc (weight-ren ρ L)
weight-ren ρ (M ⟪ Θ , c ⟫) = cong suc (weight-ren ρ M)

weight-↑ : ∀ δ M → weight (↑ᴹ[ δ ] M) ≡ weight M
weight-↑ none    M = refl
weight-↑ (new R) M = weight-ren suc M

private
  -- 3 (v + 1) + w = (3 v + (w + 1)) + 1 + 1, so Wrap loses one
  wrap-arith : ∀ v w
    → suc (suc (3 * v + suc w)) < suc (3 * suc v + w)
  wrap-arith v w = subst (suc (suc (3 * v + suc w)) <_) (sym e) (n<1+n _)
    where
    open +-*-Solver
    e : suc (3 * suc v + w) ≡ suc (suc (suc (3 * v + suc w)))
    e = solve 2 (λ v w → con 1 :+ (con 3 :* (con 1 :+ v) :+ w)
                         := con 3 :+ (con 3 :* v :+ (con 1 :+ w)))
              refl v w

  app-l : ∀ {a a′} b → a′ < a → suc (3 * a′ + b) < suc (3 * a + b)
  app-l {a} {a′} b lt = s≤s (+-monoˡ-< b (*-monoʳ-< 3 lt))

  app-r : ∀ a {b b′} → b′ < b → suc (3 * a + b′) < suc (3 * a + b)
  app-r a lt = s≤s (+-monoʳ-< (3 * a) lt)

stutter-weight : ∀ {Δ M M′ δ} (r : Δ ⊢ M -→ M′ ∣ δ)
  → Stutter r → weight M′ < weight M
stutter-weight (TyBeta v p) ()
stutter-weight (Beta v) ()
stutter-weight (TyWrap v rc ⊢s p) ()
stutter-weight (Wrap {V = V} {W = W} v w rc ri rd sc) s =
  wrap-arith (weight V) (weight W)
stutter-weight (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) s = s≤s ≤-refl
stutter-weight (Id u b) s = s≤s ≤-refl
stutter-weight (ξ-·₁ {L = L} {L′ = L′} {M = M} {δ = δ} st) s =
  subst (λ z → suc (3 * weight L′ + z) < suc (3 * weight L + weight M))
        (sym (weight-↑ δ M))
        (app-l (weight M) (stutter-weight st s))
stutter-weight (ξ-·₂ {V = V} {M = M} {M′ = M′} {δ = δ} v st) s =
  subst (λ z → suc (3 * z + weight M′) < suc (3 * weight V + weight M))
        (sym (weight-↑ δ V))
        (app-r (weight V) (stutter-weight st s))
stutter-weight (ξ-ν st) s = s≤s (stutter-weight st s)
stutter-weight (ξ-⟪⟫ ri st) s = s≤s (stutter-weight st s)

------------------------------------------------------------------------
-- (b) The source side is deterministic and its values are final
------------------------------------------------------------------------

svalue-¬step : ∀ {V N} → SValue V → V ⟶ˢ N → ⊥
svalue-¬step SV-$ ()
svalue-¬step SV-true ()
svalue-¬step SV-false ()
svalue-¬step SV-ƛ ()
svalue-¬step (SV-Λ v) ()

detˢ : ∀ {M N₁ N₂} → M ⟶ˢ N₁ → M ⟶ˢ N₂ → N₁ ≡ N₂
detˢ (β-ƛ w) (β-ƛ w′) = refl
detˢ (β-ƛ w) (ξˢ-·₁ ())
detˢ (β-ƛ w) (ξˢ-·₂ v s) = ⊥-elim (svalue-¬step w s)
detˢ (β-Λ v) (β-Λ v′) = refl
detˢ (β-Λ v) (ξˢ-[] ())
detˢ (ξˢ-·₁ ()) (β-ƛ w)
detˢ (ξˢ-·₁ s) (ξˢ-·₁ s′) = cong (S._· _) (detˢ s s′)
detˢ (ξˢ-·₁ s) (ξˢ-·₂ v s′) = ⊥-elim (svalue-¬step v s)
detˢ (ξˢ-·₂ v s) (β-ƛ w) = ⊥-elim (svalue-¬step w s)
detˢ (ξˢ-·₂ v s) (ξˢ-·₁ s′) = ⊥-elim (svalue-¬step v s′)
detˢ (ξˢ-·₂ v s) (ξˢ-·₂ v′ s′) = cong (S._·_ _) (detˢ s s′)
detˢ (ξˢ-[] ()) (β-Λ v)
detˢ (ξˢ-[] s) (ξˢ-[] s′) = cong (S._[ _ ]) (detˢ s s′)

------------------------------------------------------------------------
-- Reflection
------------------------------------------------------------------------

private
  reflect : ∀ k {Δ M A N}
    → weight M < k
    → WfCtx Δ
    → Δ ∣ [] ⊢ M ⦂ A
    → erase Δ M ⟶ˢ N
    → ∃[ M′ ] Σ[ r ∈ Δ ⊢ M -→* M′ ] (erase (runCtx r) M′ ≡ N)
  reflect zero () w ⊢M s
  reflect (suc k) lt w ⊢M s with progress ⊢M
  reflect (suc k) lt w ⊢M s | inj₁ v =
    ⊥-elim (svalue-¬step (value-erase v) s)
  reflect (suc k) lt w ⊢M s | inj₂ (M′ , δ , r) with stutter? r
  reflect (suc k) lt w ⊢M s | inj₂ (M′ , δ , r) | inj₁ st
    with reflect k (≤-trans (stutter-weight r st) (lower lt))
                   (preservation-wf w ⊢M r) (preservation w ⊢M r)
                   (subst (_⟶ˢ _) (erasure-stutter w ⊢M r st) s)
    where
    lower : ∀ {m k} → m < suc k → m ≤ k
    lower (s≤s p) = p
  reflect (suc k) lt w ⊢M s | inj₂ (M′ , δ , r) | inj₁ st
    | M″ , rs , e = M″ , (r then rs) , e
  reflect (suc k) lt w ⊢M s | inj₂ (M′ , δ , r) | inj₂ ns =
    M′ , (r then done) , detˢ (erasure-step w ⊢M r ns) s

erasure-reflection : ∀ {Δ M A N}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → erase Δ M ⟶ˢ N
  → ∃[ M′ ] Σ[ r ∈ Δ ⊢ M -→* M′ ] (erase (runCtx r) M′ ≡ N)
erasure-reflection {M = M} w ⊢M s =
  reflect (suc (weight M)) (s≤s ≤-refl) w ⊢M s

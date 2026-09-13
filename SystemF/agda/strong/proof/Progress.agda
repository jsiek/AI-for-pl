module strong.proof.Progress where

-- Strong System F v7 — progress for well-formed type contexts.

open import Data.List using ([])
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.Reduction
open import strong.proof.Canonical
open import strong.proof.ConversionCanonical
open import strong.proof.CtxProperties using
  (ok-Λ; ok-boundary; quote-rep)

progress : ∀ {Δ M A}
  → Δ ok
  → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))
progress ctx-ok (⊢` ())
progress ctx-ok ⊢$ = inj₁ (Vs S$)
progress ctx-ok ⊢# = inj₁ (Vs S#)
progress ctx-ok (⊢⊕ left right) with progress ctx-ok left
progress ctx-ok (⊢⊕ left right) | inj₂ (L′ , step) =
  inj₂ (_ , ξ-⊕-l step)
progress ctx-ok (⊢⊕ left right) | inj₁ vL with progress ctx-ok right
progress ctx-ok (⊢⊕ left right) | inj₁ vL | inj₂ (R′ , step) =
  inj₂ (_ , ξ-⊕-r vL step)
progress ctx-ok (⊢⊕ left right) | inj₁ vL | inj₁ vR
  with canonical-ℕ vL left | canonical-ℕ vR right
progress ctx-ok (⊢⊕ left right) | inj₁ vL | inj₁ vR
  | m , refl | n , refl = inj₂ (_ , PrimBeta)
progress ctx-ok (⊢ƛ wf body) = inj₁ (Vs Sƛ)
progress ctx-ok (⊢· left right) with progress ctx-ok left
progress ctx-ok (⊢· left right) | inj₂ (L′ , step) =
  inj₂ (_ , ξ-·-l step)
progress ctx-ok (⊢· left right) | inj₁ vL with progress ctx-ok right
progress ctx-ok (⊢· left right) | inj₁ vL | inj₂ (R′ , step) =
  inj₂ (_ , ξ-·-r vL step)
progress ctx-ok (⊢· left right) | inj₁ vL | inj₁ vR
  with canonical-⇒ vL left
progress ctx-ok (⊢· left right) | inj₁ vL | inj₁ vR
  | inj₁ (N , refl) = inj₂ (_ , Beta vR)
progress ctx-ok (⊢· left right) | inj₁ vL | inj₁ vR
  | inj₂ (Θ , χ , W , c , c₁ , c₂ , refl , arr-eq) =
  inj₂ (_ , Wrap vL vR arr-eq)
progress ctx-ok (⊢Λ body) with progress (ok-Λ ctx-ok) body
progress ctx-ok (⊢Λ body) | inj₁ v = inj₁ (Vs (SΛ v))
progress ctx-ok (⊢Λ body) | inj₂ (N′ , step) = inj₂ (_ , ξ-Λ step)
progress ctx-ok (⊢•[] {A = A} left wfA) with progress ctx-ok left
progress ctx-ok (⊢•[] {A = A} left wfA) | inj₂ (L′ , step) =
  inj₂ (_ , ξ-•[] step)
progress ctx-ok (⊢•[] {A = A} left wfA) | inj₁ vL
  with canonical-∀ vL left | quote-rep wfA
progress ctx-ok (⊢•[] {A = A} left wfA) | inj₁ vL
  | inj₁ (N , vN , refl) | R , q =
  inj₂ (_ , TyBeta vN q)
progress ctx-ok (⊢•[] {A = A} left wfA) | inj₁ vL
  | inj₂ (Θ , χ , W , c , N , d , refl , vN , refl , all-eq)
  | R , q = inj₂ (_ , TyWrap vN all-eq q)
progress ctx-ok (⊢ν store scope nf body conv)
  with progress (ok-boundary ctx-ok store scope) body
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₂ (M′ , step) = inj₂ (_ , ξ-ν store scope step)
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vν simple inner-nf app) = inj₂ (_ , Merge (Vν simple inner-nf app))
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S$) with body
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S$) | ⊢$ with canonical-ℕ-conv conv nf
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S$) | ⊢$ | ready-applicable app = inj₁ (Vν S$ nf app)
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S$) | ⊢$ | ready-ℕ refl = inj₂ (_ , Const literal-$ base-ℕ)
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S$) | ⊢$ | ready-𝔹 refl with conv
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S$) | ⊢$ | ready-𝔹 refl | conv-id ()
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S#) with body
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S#) | ⊢# with canonical-𝔹-conv conv nf
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S#) | ⊢# | ready-applicable app = inj₁ (Vν S# nf app)
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S#) | ⊢# | ready-𝔹 refl = inj₂ (_ , Const literal-# base-𝔹)
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S#) | ⊢# | ready-ℕ refl with conv
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs S#) | ⊢# | ready-ℕ refl | conv-id ()
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs Sƛ) with body
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs Sƛ) | ⊢ƛ wf body′ =
  inj₁ (Vν Sƛ nf (canonical-⇒-conv conv nf))
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs (SΛ v)) with body
progress ctx-ok (⊢ν store scope nf body conv)
  | inj₁ (Vs (SΛ v)) | ⊢Λ body′ =
  inj₁ (Vν (SΛ v) nf (canonical-∀-conv conv nf))

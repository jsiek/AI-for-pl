module strong.proof.Canonical where

-- Strong System F v7 — canonical forms used by progress.

open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph using (Store; Scope)
open import strong.Terms
open import strong.proof.ConversionProperties
  using (conv-target; AllShape; all-shape; same-all-left)

allView-target : ∀ {c d}
  → allView c ≡ just d
  → Σ[ A ∈ Ty ] (target c ≡ `∀ A)
allView-target {c = id (`∀ A)} refl = A , refl
allView-target {c = all c ∷ᶜ id (`∀ A)} refl = A , refl

arr-target : ∀ {c c₁ c₂}
  → arr c ≡ just (c₁ , c₂)
  → Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] (target c ≡ A ⇒ B)
arr-target {c = id (A ⇒ B)} refl = A , B , refl
arr-target {c = (c₁ ↦ c₂) ∷ᶜ id (A ⇒ B)} refl = A , B , refl

applicable-arr : ∀ {c A B}
  → Applicable c
  → target c ≡ A ⇒ B
  → Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ] (arr c ≡ just (c₁ , c₂))
applicable-arr (applies-arr eq) target-eq = _ , _ , eq
applicable-arr (applies-all eq) target-eq with allView-target eq
applicable-arr (applies-all eq) target-eq | C , all-eq
  with trans (sym target-eq) all-eq
applicable-arr (applies-all eq) target-eq | C , all-eq | ()
applicable-arr (applies-var var-eq) target-eq
  with trans (sym target-eq) var-eq
applicable-arr (applies-var var-eq) target-eq | ()

applicable-all : ∀ {c A}
  → Applicable c
  → target c ≡ `∀ A
  → Σ[ d ∈ Conv ] (allView c ≡ just d)
applicable-all (applies-arr eq) target-eq with arr-target eq
applicable-all (applies-arr eq) target-eq | A , B , arr-eq
  with trans (sym target-eq) arr-eq
applicable-all (applies-arr eq) target-eq | A , B , arr-eq | ()
applicable-all (applies-all eq) target-eq = _ , eq
applicable-all (applies-var var-eq) target-eq
  with trans (sym target-eq) var-eq
applicable-all (applies-var var-eq) target-eq | ()

applicable-ℕ-impossible : ∀ {c}
  → Applicable c
  → target c ≡ `ℕ
  → ⊥
applicable-ℕ-impossible (applies-arr eq) target-eq with arr-target eq
applicable-ℕ-impossible (applies-arr eq) target-eq | A , B , arr-eq
  with trans (sym target-eq) arr-eq
applicable-ℕ-impossible (applies-arr eq) target-eq | A , B , arr-eq | ()
applicable-ℕ-impossible (applies-all eq) target-eq with allView-target eq
applicable-ℕ-impossible (applies-all eq) target-eq | A , all-eq
  with trans (sym target-eq) all-eq
applicable-ℕ-impossible (applies-all eq) target-eq | A , all-eq | ()
applicable-ℕ-impossible (applies-var var-eq) target-eq
  with trans (sym target-eq) var-eq
applicable-ℕ-impossible (applies-var var-eq) target-eq | ()

conversion-all-source : ∀ {Δ₁ Δ₂ c A B d}
  → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂
  → allView c ≡ just d
  → AllShape A
conversion-all-source (conv-id {B = `∀ B} same) refl =
  same-all-left same
conversion-all-source
  (conv-cons (conv-all s) (conv-id {B = `∀ B} same)) refl = all-shape _

simple-all : ∀ {Δ V A}
  → Simple V
  → Δ ∣ [] ⊢ V ⦂ A
  → AllShape A
  → Σ[ N ∈ Term ] (Value N × (V ≡ Λ N))
simple-all S$ ⊢$ ()
simple-all S# ⊢# ()
simple-all Sƛ (⊢ƛ wf body) ()
simple-all (SΛ v) (⊢Λ body) (all-shape A) = _ , v , refl

canonical-ℕ : ∀ {Δ V}
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `ℕ
  → Σ[ n ∈ ℕ ] (V ≡ $ n)
canonical-ℕ (Vs S$) ⊢$ = _ , refl
canonical-ℕ (Vs S#) ()
canonical-ℕ (Vs Sƛ) ()
canonical-ℕ (Vs (SΛ v)) ()
canonical-ℕ (Vν simple nf app) (⊢ν store scope nfc body conv)
  with applicable-ℕ-impossible app (conv-target conv)
canonical-ℕ (Vν simple nf app) (⊢ν store scope nfc body conv) | ()

canonical-⇒ : ∀ {Δ V A B}
  → Value V
  → Δ ∣ [] ⊢ V ⦂ A ⇒ B
  → (Σ[ N ∈ Term ] (V ≡ ƛ A ∙ N))
    ⊎ (Σ[ Θ ∈ Store ] Σ[ χ ∈ Scope ] Σ[ W ∈ Term ] Σ[ c ∈ Conv ]
       Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ]
       (V ≡ ν Θ , χ [ W ∣ c ]) ×
       (arr c ≡ just (c₁ , c₂)))
canonical-⇒ (Vs S$) ()
canonical-⇒ (Vs S#) ()
canonical-⇒ (Vs Sƛ) (⊢ƛ wf body) = inj₁ (_ , refl)
canonical-⇒ (Vs (SΛ v)) ()
canonical-⇒ (Vν simple nf app) (⊢ν store scope nfc body conv)
  with applicable-arr app (conv-target conv)
canonical-⇒ (Vν simple nf app) (⊢ν store scope nfc body conv)
  | c₁ , c₂ , arr-eq =
  inj₂ (_ , _ , _ , _ , c₁ , c₂ , refl , arr-eq)

canonical-∀ : ∀ {Δ V A}
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `∀ A
  → (Σ[ N ∈ Term ] (Value N × (V ≡ Λ N)))
    ⊎ (Σ[ Θ ∈ Store ] Σ[ χ ∈ Scope ] Σ[ W ∈ Term ] Σ[ c ∈ Conv ]
       Σ[ N ∈ Term ] Σ[ d ∈ Conv ]
       (W ≡ Λ N) × Value N ×
       (V ≡ ν Θ , χ [ W ∣ c ]) ×
       (allView c ≡ just d))
canonical-∀ (Vs S$) ()
canonical-∀ (Vs S#) ()
canonical-∀ (Vs Sƛ) ()
canonical-∀ (Vs (SΛ v)) (⊢Λ body) = inj₁ (_ , v , refl)
canonical-∀ (Vν simple nf app) (⊢ν store scope nfc body conv)
  with applicable-all app (conv-target conv)
canonical-∀ (Vν simple nf app) (⊢ν store scope nfc body conv)
  | d , all-eq
  with simple-all simple body (conversion-all-source conv all-eq)
canonical-∀ (Vν simple nf app) (⊢ν store scope nfc body conv)
  | d , all-eq | N , v , refl =
  inj₂ (_ , _ , _ , _ , _ , d , refl , v , refl , all-eq)

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
open import strong.proof.ConversionProperties using
  (conv-target; AllShape; all-shape; same-all-left;
   FunShape; fun-shape; same-fun-left)

allView-target : ∀ {c d}
  → allView c ≡ just d
  → Σ[ A ∈ Ty ] (target c ≡ `∀ A)
allView-target {c = id (`∀ A)} refl = A , refl
allView-target {c = all c ∷ᶜ id (`∀ A)} refl = A , refl

arr-target : ∀ {A₀ c c₁ c₂}
  → arr A₀ c ≡ just (c₁ , c₂)
  → Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] (target c ≡ A ⇒ B)
arr-target {c = id (A ⇒ B)} refl = A , B , refl
arr-target {c = (c₁ ↦ c₂) ∷ᶜ id (A ⇒ B)} refl = A , B , refl

-- `arr` succeeds or fails on the SHAPE alone; the domain argument only
-- lands in the output.  So success at one domain is success at any.
arr-any : ∀ {A′ c p} (A₀ : Ty) → arr A′ c ≡ just p
  → Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ] (arr A₀ c ≡ just (c₁ , c₂))
arr-any {c = id (A ⇒ B)} A₀ refl = _ , _ , refl
arr-any {c = (s ↦ t) ∷ᶜ id (A ⇒ B)} A₀ refl = _ , _ , refl

applicable-arr : ∀ {c A B}
  → Applicable c
  → target c ≡ A ⇒ B
  → ∀ A₀ → Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ] (arr A₀ c ≡ just (c₁ , c₂))
applicable-arr (applies-arr A′ eq) target-eq A₀ = arr-any A₀ eq
applicable-arr (applies-all eq) target-eq A₀ with allView-target eq
applicable-arr (applies-all eq) target-eq A₀ | C , all-eq
  with trans (sym target-eq) all-eq
applicable-arr (applies-all eq) target-eq A₀ | C , all-eq | ()
applicable-arr (applies-var var-eq) target-eq A₀
  with trans (sym target-eq) var-eq
applicable-arr (applies-var var-eq) target-eq A₀ | ()

applicable-all : ∀ {c A}
  → Applicable c
  → target c ≡ `∀ A
  → Σ[ d ∈ Conv ] (allView c ≡ just d)
applicable-all (applies-arr A′ eq) target-eq with arr-target eq
applicable-all (applies-arr A′ eq) target-eq | A , B , arr-eq
  with trans (sym target-eq) arr-eq
applicable-all (applies-arr A′ eq) target-eq | A , B , arr-eq | ()
applicable-all (applies-all eq) target-eq = _ , eq
applicable-all (applies-var var-eq) target-eq
  with trans (sym target-eq) var-eq
applicable-all (applies-var var-eq) target-eq | ()

applicable-ℕ-impossible : ∀ {c}
  → Applicable c
  → target c ≡ `ℕ
  → ⊥
applicable-ℕ-impossible (applies-arr A′ eq) target-eq with arr-target eq
applicable-ℕ-impossible (applies-arr A′ eq) target-eq | A , B , arr-eq
  with trans (sym target-eq) arr-eq
applicable-ℕ-impossible (applies-arr A′ eq) target-eq | A , B , arr-eq | ()
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
conversion-all-source (conv-id {B = `∀ B} same _) refl =
  same-all-left same
conversion-all-source
  (conv-cons (conv-all s) (tail-id {A = `∀ B} wf)) refl = all-shape _

-- A conversion `arr` can split has an ARROW source: the head rule states
-- it for a `↦` head, and a bare `id`'s two endpoints have the same shape.
conversion-fun-source : ∀ {Δ₁ Δ₂ c A B A₀ c₁ c₂}
  → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂
  → arr A₀ c ≡ just (c₁ , c₂)
  → FunShape A
conversion-fun-source (conv-id {B = A′ ⇒ B′} same _) refl =
  same-fun-left same
conversion-fun-source
  (conv-cons (conv-fun s t) (tail-id {A = A′ ⇒ B′} wf)) refl =
  fun-shape _ _

simple-fun : ∀ {Δ V A}
  → Simple V
  → Δ ∣ [] ⊢ V ⦂ A
  → FunShape A
  → Σ[ A₁ ∈ Ty ] Σ[ N ∈ Term ] (V ≡ ƛ A₁ ∙ N)
simple-fun S$ ⊢$ ()
simple-fun S# ⊢# ()
simple-fun Sƛ (⊢ƛ wf body) (fun-shape A B) = _ , _ , refl
simple-fun (SΛ v) (⊢Λ body) ()

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

-- An arrow-typed boundary VALUE carries a λ, exactly as a ∀-typed one
-- carries a Λ — and the λ's annotation is the interior domain `arr` needs.
canonical-⇒ : ∀ {Δ V A B}
  → Value V
  → Δ ∣ [] ⊢ V ⦂ A ⇒ B
  → (Σ[ N ∈ Term ] (V ≡ ƛ A ∙ N))
    ⊎ (Σ[ Θ ∈ Store ] Σ[ χ ∈ Scope ] Σ[ A₁ ∈ Ty ] Σ[ N ∈ Term ]
       Σ[ c ∈ Conv ] Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ]
       (V ≡ ν Θ , χ [ ƛ A₁ ∙ N ∣ c ]) ×
       (arr A₁ c ≡ just (c₁ , c₂)))
canonical-⇒ (Vs S$) ()
canonical-⇒ (Vs S#) ()
canonical-⇒ (Vs Sƛ) (⊢ƛ wf body) = inj₁ (_ , refl)
canonical-⇒ (Vs (SΛ v)) ()
canonical-⇒ (Vν simple nf app) (⊢ν store scope nfc body conv)
  with applicable-arr app (conv-target conv) `ℕ
canonical-⇒ (Vν simple nf app) (⊢ν store scope nfc body conv)
  | d₁ , d₂ , probe-eq
  with simple-fun simple body (conversion-fun-source conv probe-eq)
canonical-⇒ (Vν simple nf app) (⊢ν store scope nfc body conv)
  | d₁ , d₂ , probe-eq | A₁ , N , refl
  with arr-any A₁ probe-eq
canonical-⇒ (Vν simple nf app) (⊢ν store scope nfc body conv)
  | d₁ , d₂ , probe-eq | A₁ , N , refl | c₁ , c₂ , arr-eq =
  inj₂ (_ , _ , A₁ , N , _ , c₁ , c₂ , refl , arr-eq)

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

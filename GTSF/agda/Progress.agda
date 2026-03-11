module Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (zero)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)

open import PolyCoercions
open import PolyCastCalculus

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress (Σ : Store) (M : Term) : Set where
  done  : Value M → Progress Σ M
  step  : ∀ {Σ′ N} → (Σ ⊲ M) —→ (Σ′ ⊲ N) → Progress Σ M
  crash : ∀ {p} → M ≡ blame p → Progress Σ M

------------------------------------------------------------------------
-- Decidable equality on types
------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
(` x) ≟Ty (` y) with x ≟ y
... | yes refl = yes refl
... | no x≢y = no (λ { refl → x≢y refl })
(` x) ≟Ty `ℕ = no (λ ())
(` x) ≟Ty `Bool = no (λ ())
(` x) ≟Ty `Str = no (λ ())
(` x) ≟Ty `★ = no (λ ())
(` x) ≟Ty (`U u) = no (λ ())
(` x) ≟Ty (A ⇒ B) = no (λ ())
(` x) ≟Ty (`∀ A) = no (λ ())
`ℕ ≟Ty (` y) = no (λ ())
`ℕ ≟Ty `ℕ = yes refl
`ℕ ≟Ty `Bool = no (λ ())
`ℕ ≟Ty `Str = no (λ ())
`ℕ ≟Ty `★ = no (λ ())
`ℕ ≟Ty (`U u) = no (λ ())
`ℕ ≟Ty (A ⇒ B) = no (λ ())
`ℕ ≟Ty (`∀ A) = no (λ ())
`Bool ≟Ty (` y) = no (λ ())
`Bool ≟Ty `ℕ = no (λ ())
`Bool ≟Ty `Bool = yes refl
`Bool ≟Ty `Str = no (λ ())
`Bool ≟Ty `★ = no (λ ())
`Bool ≟Ty (`U u) = no (λ ())
`Bool ≟Ty (A ⇒ B) = no (λ ())
`Bool ≟Ty (`∀ A) = no (λ ())
`Str ≟Ty (` y) = no (λ ())
`Str ≟Ty `ℕ = no (λ ())
`Str ≟Ty `Bool = no (λ ())
`Str ≟Ty `Str = yes refl
`Str ≟Ty `★ = no (λ ())
`Str ≟Ty (`U u) = no (λ ())
`Str ≟Ty (A ⇒ B) = no (λ ())
`Str ≟Ty (`∀ A) = no (λ ())
`★ ≟Ty (` y) = no (λ ())
`★ ≟Ty `ℕ = no (λ ())
`★ ≟Ty `Bool = no (λ ())
`★ ≟Ty `Str = no (λ ())
`★ ≟Ty `★ = yes refl
`★ ≟Ty (`U u) = no (λ ())
`★ ≟Ty (A ⇒ B) = no (λ ())
`★ ≟Ty (`∀ A) = no (λ ())
(`U u) ≟Ty (` y) = no (λ ())
(`U u) ≟Ty `ℕ = no (λ ())
(`U u) ≟Ty `Bool = no (λ ())
(`U u) ≟Ty `Str = no (λ ())
(`U u) ≟Ty `★ = no (λ ())
(`U u) ≟Ty (`U v) with u ≟ v
... | yes refl = yes refl
... | no u≢v = no (λ { refl → u≢v refl })
(`U u) ≟Ty (A ⇒ B) = no (λ ())
(`U u) ≟Ty (`∀ A) = no (λ ())
(A ⇒ B) ≟Ty (` y) = no (λ ())
(A ⇒ B) ≟Ty `ℕ = no (λ ())
(A ⇒ B) ≟Ty `Bool = no (λ ())
(A ⇒ B) ≟Ty `Str = no (λ ())
(A ⇒ B) ≟Ty `★ = no (λ ())
(A ⇒ B) ≟Ty (`U u) = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no (λ { refl → A≢C refl })
... | _ | no B≢D = no (λ { refl → B≢D refl })
(A ⇒ B) ≟Ty (`∀ C) = no (λ ())
(`∀ A) ≟Ty (` y) = no (λ ())
(`∀ A) ≟Ty `ℕ = no (λ ())
(`∀ A) ≟Ty `Bool = no (λ ())
(`∀ A) ≟Ty `Str = no (λ ())
(`∀ A) ≟Ty `★ = no (λ ())
(`∀ A) ≟Ty (`U u) = no (λ ())
(`∀ A) ≟Ty (C ⇒ D) = no (λ ())
(`∀ A) ≟Ty (`∀ B) with A ≟Ty B
... | yes refl = yes refl
... | no A≢B = no (λ { refl → A≢B refl })

------------------------------------------------------------------------
-- Canonical forms for closed values
------------------------------------------------------------------------

canonical-★-inj : ∀ {S V}
  → Value V
  → S ∣ zero ⊢ [] ⊢ V ⦂ `★
  → Σ Ty (λ G → Σ Term (λ W → Value W × (V ≡ (W ⟨ G ! ⟩))))
canonical-★-inj (vU (v-const {k = nat n})) ()
canonical-★-inj (vU (v-const {k = bool b})) ()
canonical-★-inj (vU v-ƛ) ()
canonical-★-inj (vU v-Λ) ()
canonical-★-inj (v-⁻ vV) (⊢⟨⟩ _ ())
canonical-★-inj (v-! {V = W} {G = G} vW) (⊢⟨⟩ hW (⊢! _ _ _)) =
  G , (W , (vW , refl))
canonical-★-inj (v-↦ vV) (⊢⟨⟩ _ ())
canonical-★-inj (v-∀ᶜ vV) (⊢⟨⟩ _ ())

canonical-⇒ : ∀ {S V A B}
  → Value V
  → S ∣ zero ⊢ [] ⊢ V ⦂ (A ⇒ B)
  → (Σ Ty (λ C → Σ Term (λ N → V ≡ (ƛ C ⇒ N))))
    ⊎ (Σ Term (λ W → Σ Coercion (λ c → Σ Coercion (λ d → Value W × (V ≡ (W ⟨ c ↦ d ⟩))))))
canonical-⇒ (vU (v-const {k = nat n})) ()
canonical-⇒ (vU (v-const {k = bool b})) ()
canonical-⇒ (vU (v-ƛ {A = C} {M = N})) (⊢ƛ _ _) = inj₁ (C , (N , refl))
canonical-⇒ (vU v-Λ) ()
canonical-⇒ (v-⁻ vV) (⊢⟨⟩ _ ())
canonical-⇒ (v-! vV) (⊢⟨⟩ _ ())
canonical-⇒ (v-↦ {V = W} {c = c} {d = d} vW) (⊢⟨⟩ hW (⊢↦ _ _)) =
  inj₂ (W , (c , (d , (vW , refl))))
canonical-⇒ (v-∀ᶜ vV) (⊢⟨⟩ _ ())

canonical-∀ : ∀ {S V A}
  → Value V
  → S ∣ zero ⊢ [] ⊢ V ⦂ `∀ A
  → (Σ Term (λ N → Σ Ty (λ A₀ → V ≡ (Λ N ⦂ A₀))))
    ⊎ (Σ Term (λ W → Σ Coercion (λ c → Value W × (V ≡ (W ⟨ ∀ᶜ c ⟩)))))
canonical-∀ (vU (v-const {k = nat n})) ()
canonical-∀ (vU (v-const {k = bool b})) ()
canonical-∀ (vU v-ƛ) ()
canonical-∀ (vU (v-Λ {M = N} {A = A₀})) (⊢Λ _) = inj₁ (N , (A₀ , refl))
canonical-∀ (v-⁻ vV) (⊢⟨⟩ _ ())
canonical-∀ (v-! vV) (⊢⟨⟩ _ ())
canonical-∀ (v-↦ vV) (⊢⟨⟩ _ ())
canonical-∀ (v-∀ᶜ {V = W} {c = c} vW) (⊢⟨⟩ hW (⊢∀ᶜ _)) =
  inj₂ (W , (c , (vW , refl)))

canonical-U : ∀ {S V U}
  → Value V
  → S ∣ zero ⊢ [] ⊢ V ⦂ `U U
  → Σ Term (λ W → Value W × (V ≡ (W ⟨ U ⁻ ⟩)))
canonical-U (vU (v-const {k = nat n})) ()
canonical-U (vU (v-const {k = bool b})) ()
canonical-U (vU v-ƛ) ()
canonical-U (vU v-Λ) ()
canonical-U (v-⁻ {V = W} {U = U} vW) (⊢⟨⟩ hW (⊢conceal _ _)) =
  W , (vW , refl)
canonical-U (v-! vV) (⊢⟨⟩ _ ())
canonical-U (v-↦ vV) (⊢⟨⟩ _ ())
canonical-U (v-∀ᶜ vV) (⊢⟨⟩ _ ())

proj-progress : ∀ {S M G p}
  → Value M
  → S ∣ zero ⊢ [] ⊢ M ⦂ `★
  → Progress S (M ⟨ G `? p ⟩)
proj-progress {G = G} {p = p} vM M⦂
  with canonical-★-inj vM M⦂
... | H , (W , (vW , eq)) with H ≟Ty G
... | yes refl rewrite eq = step (β-proj-inj-ok vW)
... | no H≢G rewrite eq = step (β-proj-inj-bad vW H≢G)

reveal-progress : ∀ {S M U}
  → Value M
  → S ∣ zero ⊢ [] ⊢ M ⦂ `U U
  → Progress S (M ⟨ U ⁺ ⟩)
reveal-progress {U = U} vM M⦂ with canonical-U vM M⦂
... | W , (vW , eq) rewrite eq = step (β-remove vW)

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress : ∀ {S M A}
  → WfStore zero S
  → S ∣ zero ⊢ [] ⊢ M ⦂ A
  → Progress S M
progress wfΣ (⊢const _ _) = done (vU v-const)
progress wfΣ (⊢# ())
progress wfΣ (⊢ƛ _ _) = done (vU v-ƛ)
progress wfΣ (⊢· {L = L} {M = M} L⦂ M⦂) with progress wfΣ L⦂
... | step L→L′ = step (ξ (□· M) L→L′)
... | crash refl = step (ξ-blame (□· M))
... | done vL with progress wfΣ M⦂
...   | step M→M′ = step (ξ (L ·□ vL) M→M′)
...   | crash refl = step (ξ-blame (L ·□ vL))
...   | done vM with canonical-⇒ vL L⦂
...     | inj₁ (_ , (_ , refl)) = step (β-ƛ vM)
...     | inj₂ (W , (c , (d , (vW , refl)))) = step (β-↦ vW vM)
progress wfΣ (⊢Λ _) = done (vU v-Λ)
progress wfΣ (⊢·[] {M = M} {B = B} M⦂ hB) with progress wfΣ M⦂
... | step M→M′ = step (ξ (□·[ B ]) M→M′)
... | crash refl = step (ξ-blame (□·[ B ]))
... | done vM with canonical-∀ vM M⦂
...   | inj₁ (N , (A₀ , refl)) = {!!}
...   | inj₂ (W , (c , (vW , refl))) = {!!}
progress wfΣ (⊢⟨⟩ {M = M} {c = c} M⦂ c⦂) with progress wfΣ M⦂
... | step M→M′ = step (ξ (□⟨ c ⟩) M→M′)
... | crash refl = step (ξ-blame (□⟨ c ⟩))
... | done vM with c⦂
...   | ⊢idᶜ _ _ = step (β-id vM)
...   | ⊢! _ _ _ = done (v-! vM)
...   | ⊢? {G = G} {p = p} _ _ _ = proj-progress vM M⦂
...   | ⊢↦ _ _ = done (v-↦ vM)
...   | ⊢⨟ _ _ = step (β-seq vM)
...   | ⊢conceal _ _ = done (v-⁻ vM)
...   | ⊢reveal {U = U} _ _ = reveal-progress vM M⦂
...   | ⊢∀ᶜ _ = done (v-∀ᶜ vM)
...   | ⊢⊥ _ _ _ = step (β-fail vM)
progress wfΣ (⊢blame _) = crash refl

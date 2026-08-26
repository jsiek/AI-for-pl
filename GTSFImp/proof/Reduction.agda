module proof.Reduction where

-- File Charter:
--   * Proof lemmas for the store-changing reduction relation.
--   * Supplies arrow, universal-type, and dynamic-type preservation under
--     store-change transport, application, primitive-operation, and
--     type-application and conversion-frame congruence over multi-step
--     reduction, and inert and value preservation under transport.
--   * Also supplies store-change append algebra, multi-step trace
--     composition, readable concatenated multi-step chain notation (including
--     the common multi-step-then-single-step case), cast congruence over
--     multi-step reduction, conversion typing and value transport, and
--     cast-size preservation under store changes.
--   * Depends on Reduction for the base relations and proof.Consistency for
--     generated-cast safety.

import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore)
open import Consistency hiding (keep)
import Consistency as C
open import Conversion using
  (Conv↑; Conv↓; rename↑; rename↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Primitives using
  (Prim; addℕ; and𝔹; primArgTy; primResultTy)
import CastTerms as CT
open import CastTerms using
  ( Term; Value; RevealValue; ConcealValue; blame; _·_; _⦂∀_[_]
  ; _⊕[_]_; _⟨_⟩; Inert; inj; fun; all; seal; genᵥ
  )
open import CastTerms using (_↑_; _↓_)
open import Reduction
open import proof.Consistency using
  (castSize; castSize-renameEnvᶜ; gen-safe)
open import proof.ImprecisionConsistency using (fin-suc-injective)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using
  ( StoreRename-suc-bind
  ; conceal-renameᵗ
  ; rename-star-injective
  ; rename-occurs
  ; renameᵗ-pointwise-id
  ; renameᵗᵐ-preserves-Value
  ; rename-openᵗ
  ; reveal-renameᵗ
  ; reveal-rename-id
  ; conceal-rename-id
  )

applyVars : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → TyVar Δ
  → TyVar Δ′
applyVars [] X = X
applyVars (keep ∷ χs) X = applyVars χs X
applyVars (bind A ∷ χs) X = applyVars χs (Fin.suc X)

applyBodies : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → Ty (Nat.suc Δ)
  → Ty (Nat.suc Δ′)
applyBodies [] B = B
applyBodies (χ ∷ χs) B = applyBodies χs (applyBody χ B)

applyTy-⇒ : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′) (A B : Ty Δ)
  → applyTy χ (A ⇒ B) ≡ applyTy χ A ⇒ applyTy χ B
applyTy-⇒ keep A B = refl
applyTy-⇒ (bind C) A B = refl

applyTy-∀ : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′)
    (B : Ty (Nat.suc Δ))
  → applyTy χ (`∀ B) ≡ `∀ (applyBody χ B)
applyTy-∀ keep B = refl
applyTy-∀ (bind C) B = refl

applyTys-⇒ : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (A B : Ty Δ)
  → applyTys χs (A ⇒ B) ≡ applyTys χs A ⇒ applyTys χs B
applyTys-⇒ [] A B = refl
applyTys-⇒ (keep ∷ χs) A B = applyTys-⇒ χs A B
applyTys-⇒ ((bind C) ∷ χs) A B =
  applyTys-⇒ χs (⇑ᵗ A) (⇑ᵗ B)

applyTys-∀ : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
    (B : Ty (Nat.suc Δ))
  → applyTys χs (`∀ B) ≡ `∀ (applyBodies χs B)
applyTys-∀ [] B = refl
applyTys-∀ (keep ∷ χs) B = applyTys-∀ χs B
applyTys-∀ ((bind C) ∷ χs) B =
  applyTys-∀ χs (applyBody (bind C) B)

applyTys-★ : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
  → applyTys χs ★ ≡ ★
applyTys-★ [] = refl
applyTys-★ (keep ∷ χs) = applyTys-★ χs
applyTys-★ ((bind C) ∷ χs) = applyTys-★ χs

applyTys-primArgTy : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (op : Prim)
  → applyTys χs (primArgTy op) ≡ primArgTy op
applyTys-primArgTy [] op = refl
applyTys-primArgTy (keep ∷ χs) op = applyTys-primArgTy χs op
applyTys-primArgTy ((bind C) ∷ χs) addℕ =
  applyTys-primArgTy χs addℕ
applyTys-primArgTy ((bind C) ∷ χs) and𝔹 =
  applyTys-primArgTy χs and𝔹

applyTys-primResultTy : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (op : Prim)
  → applyTys χs (primResultTy op) ≡ primResultTy op
applyTys-primResultTy [] op = refl
applyTys-primResultTy (keep ∷ χs) op = applyTys-primResultTy χs op
applyTys-primResultTy ((bind C) ∷ χs) addℕ =
  applyTys-primResultTy χs addℕ
applyTys-primResultTy ((bind C) ∷ χs) and𝔹 =
  applyTys-primResultTy χs and𝔹

applyTys-open : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
    (B : Ty (Nat.suc Δ)) (A : Ty Δ)
  → applyTys χs (B [ A ]ᵗ) ≡
    applyBodies χs B [ applyTys χs A ]ᵗ
applyTys-open [] B A = refl
applyTys-open (keep ∷ χs) B A = applyTys-open χs B A
applyTys-open ((bind C) ∷ χs) B A =
  trans (cong (applyTys χs) (rename-openᵗ Fin.suc B A))
    (applyTys-open χs (applyBody (bind C) B) (applyTy (bind C) A))

applyTerms-preserves-Value : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
    {V : Term Δ}
  → Value V
  → Value (applyTerms χs V)
applyTerms-preserves-Value [] vV = vV
applyTerms-preserves-Value (keep ∷ χs) vV =
  applyTerms-preserves-Value χs vV
applyTerms-preserves-Value ((bind A) ∷ χs) vV =
  applyTerms-preserves-Value χs
    (renameᵗᵐ-preserves-Value wk↪ᵗ vV)

normalizeReveal : ∀ {Δ} {A B : Ty Δ}
  → Conv↑ Δ A B
  → Conv↑ Δ A B
normalizeReveal {A = A} {B = B} c =
  subst≡ (Conv↑ _ A) (renameᵗ-pointwise-id _ B (λ X → refl))
    (subst≡ (λ A′ → Conv↑ _ A′ _)
      (renameᵗ-pointwise-id _ A (λ X → refl))
      (rename↑ (λ X → X) c))

normalizeConceal : ∀ {Δ} {A B : Ty Δ}
  → Conv↓ Δ A B
  → Conv↓ Δ A B
normalizeConceal {A = A} {B = B} c =
  subst≡ (Conv↓ _ A) (renameᵗ-pointwise-id _ B (λ X → refl))
    (subst≡ (λ A′ → Conv↓ _ A′ _)
      (renameᵗ-pointwise-id _ A (λ X → refl))
      (rename↓ (λ X → X) c))

normalizeReveal-⊢↑ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty Δ}
    {c : Conv↑ Δ A B}
  → Σ ⊢↑[ X ⦂ R ] c
  → Σ ⊢↑[ X ⦂ R ] normalizeReveal c
normalizeReveal-⊢↑ {A = A} {B = B} c⊢ =
  reveal-subst (renameᵗ-pointwise-id _ A (λ X → refl))
    (renameᵗ-pointwise-id _ B (λ X → refl)) (reveal-rename-id c⊢)
  where
  reveal-subst : ∀ {Σ : TyStore _} {X : TyVar _}
      {R A₀ A₁ B₀ B₁ : Ty _}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → ∀ {d : Conv↑ _ A₀ B₀}
    → Σ ⊢↑[ X ⦂ R ] d
    → Σ ⊢↑[ X ⦂ R ] subst≡ (Conv↑ _ A₁) eqB
        (subst≡ (λ A′ → Conv↑ _ A′ B₀) eqA d)
  reveal-subst refl refl d⊢ = d⊢

normalizeConceal-⊢↓ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R A B : Ty Δ}
    {c : Conv↓ Δ A B}
  → Σ ⊢↓[ X ⦂ R ] c
  → Σ ⊢↓[ X ⦂ R ] normalizeConceal c
normalizeConceal-⊢↓ {A = A} {B = B} c⊢ =
  conceal-subst (renameᵗ-pointwise-id _ A (λ X → refl))
    (renameᵗ-pointwise-id _ B (λ X → refl)) (conceal-rename-id c⊢)
  where
  conceal-subst : ∀ {Σ : TyStore _} {X : TyVar _}
      {R A₀ A₁ B₀ B₁ : Ty _}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → ∀ {d : Conv↓ _ A₀ B₀}
    → Σ ⊢↓[ X ⦂ R ] d
    → Σ ⊢↓[ X ⦂ R ] subst≡ (Conv↓ _ A₁) eqB
        (subst≡ (λ A′ → Conv↓ _ A′ B₀) eqA d)
  conceal-subst refl refl d⊢ = d⊢


applyReveals : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) {A B : Ty Δ}
  → Conv↑ Δ A B
  → Conv↑ Δ′ (applyTys χs A) (applyTys χs B)
applyReveals [] c = c
applyReveals (keep ∷ χs) c =
  applyReveals χs (normalizeReveal c)
applyReveals (bind A ∷ χs) c =
  applyReveals χs (rename↑ Fin.suc c)

applyConceals : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) {A B : Ty Δ}
  → Conv↓ Δ A B
  → Conv↓ Δ′ (applyTys χs A) (applyTys χs B)
applyConceals [] c = c
applyConceals (keep ∷ χs) c =
  applyConceals χs (normalizeConceal c)
applyConceals (bind A ∷ χs) c =
  applyConceals χs (rename↓ Fin.suc c)

applyReveals-⊢↑ : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {χs : StoreChanges Δ Δ′} {X : TyVar Δ} {R A B : Ty Δ}
    {c : Conv↑ Δ A B}
  → Σ ⊢↑[ X ⦂ R ] c
  → applyStores χs Σ ⊢↑[ applyVars χs X ⦂ applyTys χs R ]
      applyReveals χs c
applyReveals-⊢↑ {χs = []} c⊢ = c⊢
applyReveals-⊢↑ {χs = keep ∷ χs} c⊢ =
  applyReveals-⊢↑ {χs = χs} (normalizeReveal-⊢↑ c⊢)
applyReveals-⊢↑ {χs = bind A ∷ χs} c⊢ =
  applyReveals-⊢↑ {χs = χs}
    (reveal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢)

applyConceals-⊢↓ : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {χs : StoreChanges Δ Δ′} {X : TyVar Δ} {R A B : Ty Δ}
    {c : Conv↓ Δ A B}
  → Σ ⊢↓[ X ⦂ R ] c
  → applyStores χs Σ ⊢↓[ applyVars χs X ⦂ applyTys χs R ]
      applyConceals χs c
applyConceals-⊢↓ {χs = []} c⊢ = c⊢
applyConceals-⊢↓ {χs = keep ∷ χs} c⊢ =
  applyConceals-⊢↓ {χs = χs} (normalizeConceal-⊢↓ c⊢)
applyConceals-⊢↓ {χs = bind A ∷ χs} c⊢ =
  applyConceals-⊢↓ {χs = χs}
    (conceal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢)

renamedReveal-term : ∀ {Δ} {A B : Ty Δ}
    (M : Term Δ) (c : Conv↑ Δ A B)
  → M ↑ rename↑ (λ X → X) c ≡ M ↑ normalizeReveal c
renamedReveal-term {A = A} {B = B} M c =
  reveal-subst (renameᵗ-pointwise-id _ A (λ X → refl))
    (renameᵗ-pointwise-id _ B (λ X → refl)) M
    (rename↑ (λ X → X) c)
  where
  reveal-subst : ∀ {A₀ A₁ B₀ B₁ : Ty _}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → (M : Term _)
    → (d : Conv↑ _ A₀ B₀)
    → M ↑ d ≡ M ↑ subst≡ (Conv↑ _ A₁) eqB
        (subst≡ (λ A′ → Conv↑ _ A′ B₀) eqA d)
  reveal-subst refl refl M d = refl

renamedConceal-term : ∀ {Δ} {A B : Ty Δ}
    (M : Term Δ) (c : Conv↓ Δ A B)
  → M ↓ rename↓ (λ X → X) c ≡ M ↓ normalizeConceal c
renamedConceal-term {A = A} {B = B} M c =
  conceal-subst (renameᵗ-pointwise-id _ A (λ X → refl))
    (renameᵗ-pointwise-id _ B (λ X → refl)) M
    (rename↓ (λ X → X) c)
  where
  conceal-subst : ∀ {A₀ A₁ B₀ B₁ : Ty _}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → (M : Term _)
    → (d : Conv↓ _ A₀ B₀)
    → M ↓ d ≡ M ↓ subst≡ (Conv↓ _ A₁) eqB
        (subst≡ (λ A′ → Conv↓ _ A′ B₀) eqA d)
  conceal-subst refl refl M d = refl


reveal-value-rename : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    {A B : Ty Δ} {c : Conv↑ Δ A B}
  → RevealValue c
  → RevealValue (rename↑ ρ c)
reveal-value-rename ρ fun = fun
reveal-value-rename ρ all = all


conceal-value-rename : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    {A B : Ty Δ} {c : Conv↓ Δ A B}
  → ConcealValue c
  → ConcealValue (rename↓ ρ c)
conceal-value-rename ρ seal = seal
conceal-value-rename ρ fun = fun
conceal-value-rename ρ all = all


normalizeReveal-preserves-RevealValue : ∀ {Δ} {A B : Ty Δ}
    {c : Conv↑ Δ A B}
  → RevealValue c
  → RevealValue (normalizeReveal c)
normalizeReveal-preserves-RevealValue {c = c} reveal
    with subst≡ Value (renamedReveal-term (CT.ƛ CT.blame) c)
      ((CT.ƛ CT.blame) CT.↑ reveal-value-rename (λ X → X) reveal)
normalizeReveal-preserves-RevealValue {c = c} reveal
    | value CT.↑ normalized = normalized


normalizeConceal-preserves-ConcealValue : ∀ {Δ} {A B : Ty Δ}
    {c : Conv↓ Δ A B}
  → ConcealValue c
  → ConcealValue (normalizeConceal c)
normalizeConceal-preserves-ConcealValue {c = c} conceal
    with subst≡ Value (renamedConceal-term (CT.ƛ CT.blame) c)
      ((CT.ƛ CT.blame) CT.↓ conceal-value-rename (λ X → X) conceal)
normalizeConceal-preserves-ConcealValue {c = c} conceal
    | value CT.↓ normalized = normalized


applyReveals-preserves-RevealValue : ∀ {Δ Δ′}
    (χs : StoreChanges Δ Δ′) {A B : Ty Δ} {c : Conv↑ Δ A B}
  → RevealValue c
  → RevealValue (applyReveals χs c)
applyReveals-preserves-RevealValue [] reveal = reveal
applyReveals-preserves-RevealValue (keep ∷ χs) reveal =
  applyReveals-preserves-RevealValue χs
    (normalizeReveal-preserves-RevealValue reveal)
applyReveals-preserves-RevealValue (bind A ∷ χs) reveal =
  applyReveals-preserves-RevealValue χs
    (reveal-value-rename Fin.suc reveal)


applyConceals-preserves-ConcealValue : ∀ {Δ Δ′}
    (χs : StoreChanges Δ Δ′) {A B : Ty Δ} {c : Conv↓ Δ A B}
  → ConcealValue c
  → ConcealValue (applyConceals χs c)
applyConceals-preserves-ConcealValue [] conceal = conceal
applyConceals-preserves-ConcealValue (keep ∷ χs) conceal =
  applyConceals-preserves-ConcealValue χs
    (normalizeConceal-preserves-ConcealValue conceal)
applyConceals-preserves-ConcealValue (bind A ∷ χs) conceal =
  applyConceals-preserves-ConcealValue χs
    (conceal-value-rename Fin.suc conceal)

reveal-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′} {A B : Ty Δ}
  → (c : Conv↑ Δ A B)
  → M —↠[ χs ] N
  → M ↑ c —↠[ χs ] N ↑ applyReveals χs c
reveal-↠ {M = M} c (_ ∎[]) = (M ↑ c) ∎[]
reveal-↠ {M = M} {N = P} {χs = keep ∷ χs} c
    (_ —→[ keep ]⟨ M→N ⟩ N↠P) =
  M ↑ c
    —→[ keep ]⟨
      subst≡ (λ P′ → M ↑ c —→[ keep ] P′)
        (renamedReveal-term _ c) (ξ-reveal M→N refl) ⟩
  _
    —↠[ χs ]⟨
      reveal-↠ (normalizeReveal c) N↠P ⟩
  P ↑ applyReveals χs (normalizeReveal c) ∎[]
reveal-↠ {M = M} {N = P} {χs = bind A ∷ χs} c
    (_ —→[ bind A ]⟨ M→N ⟩ N↠P) =
  M ↑ c
    —→[ bind A ]⟨ ξ-reveal M→N refl ⟩
  _
    —↠[ χs ]⟨ reveal-↠ (rename↑ Fin.suc c) N↠P ⟩
  P ↑ applyReveals χs (rename↑ Fin.suc c) ∎[]

conceal-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′} {A B : Ty Δ}
  → (c : Conv↓ Δ A B)
  → M —↠[ χs ] N
  → M ↓ c —↠[ χs ] N ↓ applyConceals χs c
conceal-↠ {M = M} c (_ ∎[]) = (M ↓ c) ∎[]
conceal-↠ {M = M} {N = P} {χs = keep ∷ χs} c
    (_ —→[ keep ]⟨ M→N ⟩ N↠P) =
  M ↓ c
    —→[ keep ]⟨
      subst≡ (λ P′ → M ↓ c —→[ keep ] P′)
        (renamedConceal-term _ c) (ξ-conceal M→N refl) ⟩
  _
    —↠[ χs ]⟨
      conceal-↠ (normalizeConceal c) N↠P ⟩
  P ↓ applyConceals χs (normalizeConceal c) ∎[]
conceal-↠ {M = M} {N = P} {χs = bind A ∷ χs} c
    (_ —→[ bind A ]⟨ M→N ⟩ N↠P) =
  M ↓ c
    —→[ bind A ]⟨ ξ-conceal M→N refl ⟩
  _
    —↠[ χs ]⟨ conceal-↠ (rename↓ Fin.suc c) N↠P ⟩
  P ↓ applyConceals χs (rename↓ Fin.suc c) ∎[]

appL-↠ : ∀ {Δ Δ′} {L M : Term Δ} {L′ : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → L —↠[ χs ] L′
  → L · M —↠[ χs ] L′ · applyTerms χs M
appL-↠ {L = L} {M = M} (_ ∎[]) = (L · M) ∎[]
appL-↠ {L = L} {M = M} {L′ = P} {χs = χ ∷ χs}
    (_ —→[ χ ]⟨ L→N ⟩ N↠P) =
  L · M
    —→[ χ ]⟨ ξ-·₁ L→N refl ⟩
  _
    —↠[ χs ]⟨ appL-↠ N↠P ⟩
  P · applyTerms χs (χ ▷ᵀ M) ∎[]

appR-↠ : ∀ {Δ Δ′} {V M : Term Δ} {M′ : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → Value V
  → M —↠[ χs ] M′
  → V · M —↠[ χs ] applyTerms χs V · M′
appR-↠ {V = V} {M = M} vV (_ ∎[]) = (V · M) ∎[]
appR-↠ {V = V} {M = M} {M′ = P} {χs = keep ∷ χs} vV
    (_ —→[ keep ]⟨ M→N ⟩ N↠P) =
  V · M
    —→[ keep ]⟨ ξ-·₂ vV M→N refl ⟩
  _
    —↠[ χs ]⟨ appR-↠ vV N↠P ⟩
  applyTerms χs V · P ∎[]
appR-↠ {V = V} {M = M} {M′ = P} {χs = bind A ∷ χs} vV
    (_ —→[ bind A ]⟨ M→N ⟩ N↠P) =
  V · M
    —→[ bind A ]⟨ ξ-·₂ vV M→N refl ⟩
  _
    —↠[ χs ]⟨
      appR-↠ (renameᵗᵐ-preserves-Value wk↪ᵗ vV) N↠P ⟩
  applyTerms χs (bind A ▷ᵀ V) · P ∎[]

primL-↠ : ∀ {Δ Δ′} {L M : Term Δ} {L′ : Term Δ′} {op : Prim}
    {χs : StoreChanges Δ Δ′}
  → L —↠[ χs ] L′
  → L ⊕[ op ] M —↠[ χs ] L′ ⊕[ op ] applyTerms χs M
primL-↠ {L = L} {M = M} (_ ∎[]) = (L ⊕[ _ ] M) ∎[]
primL-↠ {L = L} {M = M} {L′ = P} {op = op} {χs = χ ∷ χs}
    (_ —→[ χ ]⟨ L→N ⟩ N↠P) =
  L ⊕[ op ] M
    —→[ χ ]⟨ ξ-⊕₁ L→N refl ⟩
  _
    —↠[ χs ]⟨ primL-↠ N↠P ⟩
  P ⊕[ op ] applyTerms χs (χ ▷ᵀ M) ∎[]

primR-↠ : ∀ {Δ Δ′} {V M : Term Δ} {M′ : Term Δ′} {op : Prim}
    {χs : StoreChanges Δ Δ′}
  → Value V
  → M —↠[ χs ] M′
  → V ⊕[ op ] M —↠[ χs ] applyTerms χs V ⊕[ op ] M′
primR-↠ {V = V} {M = M} vV (_ ∎[]) = (V ⊕[ _ ] M) ∎[]
primR-↠ {V = V} {M = M} {M′ = P} {op = op}
    {χs = keep ∷ χs} vV (_ —→[ keep ]⟨ M→N ⟩ N↠P) =
  V ⊕[ op ] M
    —→[ keep ]⟨ ξ-⊕₂ vV M→N refl ⟩
  _
    —↠[ χs ]⟨ primR-↠ vV N↠P ⟩
  applyTerms χs V ⊕[ op ] P ∎[]
primR-↠ {V = V} {M = M} {M′ = P} {op = op}
    {χs = bind A ∷ χs} vV (_ —→[ bind A ]⟨ M→N ⟩ N↠P) =
  V ⊕[ op ] M
    —→[ bind A ]⟨ ξ-⊕₂ vV M→N refl ⟩
  _
    —↠[ χs ]⟨
      primR-↠ (renameᵗᵐ-preserves-Value wk↪ᵗ vV) N↠P ⟩
  applyTerms χs (bind A ▷ᵀ V) ⊕[ op ] P ∎[]

typeApp-↠ : ∀ {Δ Δ′} {L : Term Δ} {L′ : Term Δ′}
    {C : Ty (Nat.suc Δ)} {A : Ty Δ}
    {χs : StoreChanges Δ Δ′}
  → L —↠[ χs ] L′
  → L ⦂∀ C [ A ] —↠[ χs ]
      L′ ⦂∀ applyBodies χs C [ applyTys χs A ]
typeApp-↠ {L = L} {C = C} {A = A} (_ ∎[]) =
  (L ⦂∀ C [ A ]) ∎[]
typeApp-↠ {L = L} {L′ = P} {C = C} {A = A}
    {χs = χ ∷ χs} (_ —→[ χ ]⟨ L→N ⟩ N↠P) =
  L ⦂∀ C [ A ]
    —→[ χ ]⟨ ξ-• L→N refl refl ⟩
  _
    —↠[ χs ]⟨ typeApp-↠ N↠P ⟩
  P ⦂∀ applyBodies χs (applyBody χ C)
    [ applyTys χs (applyTy χ A) ] ∎[]

------------------------------------------------------------------------
-- Store-change append algebra
------------------------------------------------------------------------

infixr 5 _++χ_

_++χ_ : ∀ {Δ Δ′ Δ″}
  → StoreChanges Δ Δ′
  → StoreChanges Δ′ Δ″
  → StoreChanges Δ Δ″
[] ++χ ψs = ψs
(χ ∷ χs) ++χ ψs = χ ∷ (χs ++χ ψs)

applyStores-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ Σ
  → applyStores ψs (applyStores χs Σ) ≡ applyStores (χs ++χ ψs) Σ
applyStores-++ [] ψs Σ = refl
applyStores-++ (χ ∷ χs) ψs Σ =
  applyStores-++ χs ψs (applyStore χ Σ)

applyTys-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ A
  → applyTys ψs (applyTys χs A) ≡ applyTys (χs ++χ ψs) A
applyTys-++ [] ψs A = refl
applyTys-++ (χ ∷ χs) ψs A = applyTys-++ χs ψs (applyTy χ A)

cast-applyConsistencies-++ : ∀ {Δ₀ Δ₁ Δ₂} {μ : Env∼ Δ₀}
    {A B : Ty Δ₀}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → (c : μ ⊢ A ∼ B)
  → (M : Term Δ₂)
  → M ⟨ applyConsistencies ψs (applyConsistencies χs c) ⟩
      ≡ M ⟨ applyConsistencies (χs ++χ ψs) c ⟩
cast-applyConsistencies-++ [] ψs c M = refl
cast-applyConsistencies-++ (χ ∷ χs) ψs c M =
  cast-applyConsistencies-++ χs ψs (applyConsistency χ c) M

reveal-applyReveals-++ : ∀ {Δ₀ Δ₁ Δ₂} {A B : Ty Δ₀}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → (c : Conv↑ Δ₀ A B)
  → (M : Term Δ₂)
  → M ↑ applyReveals ψs (applyReveals χs c)
      ≡ M ↑ applyReveals (χs ++χ ψs) c
reveal-applyReveals-++ [] ψs c M = refl
reveal-applyReveals-++ (keep ∷ χs) ψs c M =
  reveal-applyReveals-++ χs ψs (normalizeReveal c) M
reveal-applyReveals-++ (bind A ∷ χs) ψs c M =
  reveal-applyReveals-++ χs ψs (rename↑ Fin.suc c) M

conceal-applyConceals-++ : ∀ {Δ₀ Δ₁ Δ₂} {A B : Ty Δ₀}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → (c : Conv↓ Δ₀ A B)
  → (M : Term Δ₂)
  → M ↓ applyConceals ψs (applyConceals χs c)
      ≡ M ↓ applyConceals (χs ++χ ψs) c
conceal-applyConceals-++ [] ψs c M = refl
conceal-applyConceals-++ (keep ∷ χs) ψs c M =
  conceal-applyConceals-++ χs ψs (normalizeConceal c) M
conceal-applyConceals-++ (bind A ∷ χs) ψs c M =
  conceal-applyConceals-++ χs ψs (rename↓ Fin.suc c) M

------------------------------------------------------------------------
-- Store-changing trace composition
------------------------------------------------------------------------

composeReductionᵀ : Set
composeReductionᵀ = ∀ {Δ₀ Δ₁ Δ₂}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {M : Term Δ₀} {N : Term Δ₁} {P : Term Δ₂}
  → M —↠[ χs ] N
  → N —↠[ ψs ] P
  → M —↠[ χs ++χ ψs ] P

composeReduction : composeReductionᵀ
composeReduction ↠-refl N↠P = N↠P
composeReduction (↠-step M→N N↠P) P↠Q =
  ↠-step M→N (composeReduction N↠P P↠Q)

infixr 2 _—↠+[_]⟨_⟩_

_—↠+[_]⟨_⟩_ : ∀ {Δ₀ Δ₁ Δ₂}
    (M : Term Δ₀) {N : Term Δ₁} {P : Term Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → M —↠[ χs ] N
  → {ψs : StoreChanges Δ₁ Δ₂}
  → N —↠[ ψs ] P
  → M —↠[ χs ++χ ψs ] P
M —↠+[ χs ]⟨ M↠N ⟩ N↠P = composeReduction M↠N N↠P

appR-blame-↠ : ∀ {Δ Δ′} {V M : Term Δ}
    {χs : StoreChanges Δ Δ′}
  → Value V
  → M —↠[ χs ] blame
  → V · M —↠[ χs ++χ (keep ∷ []) ] blame
appR-blame-↠ {V = V} {M = M} {χs = χs} vV M↠blame =
  V · M
    —↠+[ χs ]⟨ appR-↠ vV M↠blame ⟩
  applyTerms χs V · blame
    —→[ keep ]⟨ pure-step
      (blame-·₂ (applyTerms-preserves-Value χs vV)) ⟩
  blame ∎[]

reveal-blame-↠ : ∀ {Δ Δ′} {M : Term Δ}
    {χs : StoreChanges Δ Δ′} {A B : Ty Δ}
  → (c : Conv↑ Δ A B)
  → M —↠[ χs ] blame
  → M ↑ c —↠[ χs ++χ (keep ∷ []) ] blame
reveal-blame-↠ {M = M} {χs = χs} c M↠blame =
  M ↑ c
    —↠+[ χs ]⟨ reveal-↠ c M↠blame ⟩
  blame ↑ applyReveals χs c
    —→[ keep ]⟨ pure-step blame-reveal ⟩
  blame ∎[]

conceal-blame-↠ : ∀ {Δ Δ′} {M : Term Δ}
    {χs : StoreChanges Δ Δ′} {A B : Ty Δ}
  → (c : Conv↓ Δ A B)
  → M —↠[ χs ] blame
  → M ↓ c —↠[ χs ++χ (keep ∷ []) ] blame
conceal-blame-↠ {M = M} {χs = χs} c M↠blame =
  M ↓ c
    —↠+[ χs ]⟨ conceal-↠ c M↠blame ⟩
  blame ↓ applyConceals χs c
    —→[ keep ]⟨ pure-step blame-conceal ⟩
  blame ∎[]

typeApp-blame-↠ : ∀ {Δ Δ′} {M : Term Δ}
    {χs : StoreChanges Δ Δ′}
    {C : Ty (Nat.suc Δ)} {A : Ty Δ}
  → M —↠[ χs ] blame
  → M ⦂∀ C [ A ] —↠[ χs ++χ (keep ∷ []) ] blame
typeApp-blame-↠ {M = M} {χs = χs} {C = C} {A = A} M↠blame =
  M ⦂∀ C [ A ]
    —↠+[ χs ]⟨ typeApp-↠ M↠blame ⟩
  blame ⦂∀ applyBodies χs C [ applyTys χs A ]
    —→[ keep ]⟨ pure-step blame-• ⟩
  blame ∎[]

------------------------------------------------------------------------
-- Cast-size preservation under store changes
------------------------------------------------------------------------

castSize-applyConsistency : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {A B : Ty Δ}
  → (χ : StoreChange Δ Δ′)
  → (c : μ ⊢ A ∼ B)
  → castSize (applyConsistency χ c) ≡ castSize c
castSize-applyConsistency keep c = refl
castSize-applyConsistency (bind A) c =
  castSize-renameEnvᶜ Fin.suc (λ X → refl) c

castSize-applyConsistencies : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → (c : μ ⊢ A ∼ B)
  → castSize (applyConsistencies χs c) ≡ castSize c
castSize-applyConsistencies [] c = refl
castSize-applyConsistencies (χ ∷ χs) c =
  trans (castSize-applyConsistencies χs (applyConsistency χ c))
    (castSize-applyConsistency χ c)

cast-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → M —↠[ χs ] N
  → M ⟨ c ⟩ —↠[ χs ] N ⟨ χs ▶ᶜ c ⟩
cast-↠ {M = M} c (_ ∎[]) = (M ⟨ c ⟩) ∎[]
cast-↠ {M = M} {N = P} {χs = χ ∷ χs} c
    (_ —→[ χ ]⟨ M→N ⟩ N↠P) =
  (M ⟨ c ⟩)
    —→[ χ ]⟨ ξ-⟨⟩ M→N refl ⟩
  _
    —↠[ χs ]⟨ cast-↠ (χ ▷ᶜ c) N↠P ⟩
  (P ⟨ χs ▶ᶜ (χ ▷ᶜ c) ⟩) ∎[]

cast-blame-↠ : ∀ {Δ Δ′} {M : Term Δ}
    {χs : StoreChanges Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → M —↠[ χs ] blame
  → M ⟨ c ⟩ —↠[ χs ++χ (keep ∷ []) ] blame
cast-blame-↠ {M = M} {χs = χs} c M↠blame =
  M ⟨ c ⟩
    —↠+[ χs ]⟨ cast-↠ c M↠blame ⟩
  blame ⟨ applyConsistencies χs c ⟩
    —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
  blame ∎[]

applyStoreChange-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χ : StoreChange Δ Δ′)
  → Inert c
  → Inert (χ ▷ᶜ c)
applyStoreChange-Inert keep inert = inert
applyStoreChange-Inert (bind A)
    (inj ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = C.⇒∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = C.⇒∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = C.ι∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = C.ι∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj {G = ＇ X} ⦃ Gᵍ = ＇ .X ⦄
      ⦃ G∼★ = C.X∼★ᵍ eq ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ＇ Fin.suc X ⦄ ⦃ G∼★ = C.X∼★ᵍ eq ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj {G = ＇ X} ⦃ Gᵍ = ＇ .X ⦄
      ⦃ G∼★ = C.X∼★ᶜ eq ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ＇ Fin.suc X ⦄ ⦃ G∼★ = C.X∼★ᶜ eq ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = C.∀∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = C.∀∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A) fun = fun
applyStoreChange-Inert (bind A) all = all
applyStoreChange-Inert (bind A)
    (genᵥ {A = A₀} {B = B} {c = c}
      ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ A≢★ safe) =
  subst≡
    (λ z → Inert (gen_ ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ z∈B = z ⦄ _ _))
    (PI.∈ᵗ-unique (rename-occurs (extᵗ Fin.suc) z∈B) _)
    (genᵥ ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ z∈B = rename-occurs (extᵗ Fin.suc) z∈B ⦄
      A′≢★
      (gen-safe _ A′≢★ (renameNonVar (extᵗ Fin.suc) Bnv)
        (rename-occurs (extᵗ Fin.suc) z∈B)))
  where
  A′≢★ = λ eq → A≢★ (rename-star-injective Fin.suc eq)

applyConsistencies-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χs : StoreChanges Δ Δ′)
  → Inert c
  → Inert (χs ▶ᶜ c)
applyConsistencies-Inert [] inert = inert
applyConsistencies-Inert (χ ∷ χs) inert =
  applyConsistencies-Inert χs (applyStoreChange-Inert χ inert)

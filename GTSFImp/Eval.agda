module Eval where

-- File Charter:
--   * Fuel-bounded executable evaluation for intrinsically scoped GTSFImp
--     terms.
--   * Decides values and one-step reduction directly from syntax and returns
--     reduction witnesses suitable for executable examples and traces.
--   * Intrinsic conversion endpoints determine polymorphic reveal/conceal
--     reduct annotations without consulting typing derivations.

import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import Reduction
import proof.TypeSafety.Progress as Progress

------------------------------------------------------------------------
-- Executable value classification
------------------------------------------------------------------------

inert? : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → Maybe (Inert c)
inert? (id a) = nothing
inert? (c ↦ d) = just fun
inert? (∀ᶜ c) = just all
inert? (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    with Progress.to-ground g match c
inert? {μ = μ}
    (_! ⦃ g-⇒ ⦄ c
      ⦃ Ans ⦄ ⦃ match-⇒ ⦄)
    | Progress.same =
  just
    (inj ⦃ Gns = Ans ⦄ ⦃ match = match-⇒ ⦄)
inert? {μ = μ}
    (_! ⦃ g-ι ⦄ c
      ⦃ Ans ⦄ ⦃ match-ι ⦄)
    | Progress.same =
  just
    (inj ⦃ Gns = Ans ⦄ ⦃ match = match-ι ⦄)
inert? {μ = μ}
    (_! ⦃ g-X eq ⦄ .(idᵍ {μ = μ} (g-X eq))
    ⦃ nonstar-X ⦄ ⦃ match-X ⦄)
    | Progress.same =
  just
    (inj ⦃ g = g-X eq ⦄ ⦃ Gns = nonstar-X ⦄
      ⦃ match = match-X ⦄)
inert? (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    | Progress.other A≠G =
  nothing
inert? (？ c) = nothing
inert? (inst c) = nothing
inert? (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    with A ≟Ty ★
inert? (gen_ {A = .★} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) | yes refl = nothing
inert? (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) | no A≠★ =
  just (genᵥ A≠★ (Progress.gen-safe c A≠★ Bnv z∈B))

revealValue? : ∀ {Δ A B} (c : Conv↑ Δ A B)
  → Maybe (RevealValue c)
revealValue? (unseal X R) = nothing
revealValue? (c ↦↑ d) = just fun
revealValue? (`∀↑ c) = just all
revealValue? (id↑ A) = nothing

concealValue? : ∀ {Δ A B} (c : Conv↓ Δ A B)
  → Maybe (ConcealValue c)
concealValue? (seal X R) = just seal
concealValue? (c ↦↓ d) = just fun
concealValue? (`∀↓ c) = just all
concealValue? (id↓ A) = nothing

value? : ∀ {Δ} (M : Term Δ) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ N) = just (ƛ N)
value? (L · M) = nothing
value? (Λ M) with value? M
value? (Λ M) | just vM = just (Λ vM)
value? (Λ M) | nothing = nothing
value? (M ⦂∀ B [ A ]) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op ] M) = nothing
value? (M ⟨ c ⟩) with value? M
value? (M ⟨ c ⟩) | nothing = nothing
value? (M ⟨ c ⟩) | just vM with inert? c
value? (M ⟨ c ⟩) | just vM | just ic = just (vM 《 ic 》)
value? (M ⟨ c ⟩) | just vM | nothing = nothing
value? (M ↑ c) with value? M
value? (M ↑ c) | nothing = nothing
value? (M ↑ c) | just vM with revealValue? c
value? (M ↑ c) | just vM | just cv = just (vM ↑ cv)
value? (M ↑ c) | just vM | nothing = nothing
value? (M ↓ c) with value? M
value? (M ↓ c) | nothing = nothing
value? (M ↓ c) | just vM with concealValue? c
value? (M ↓ c) | just vM | just cv = just (vM ↓ cv)
value? (M ↓ c) | just vM | nothing = nothing
value? blame = nothing

------------------------------------------------------------------------
-- Executable one-step reduction
------------------------------------------------------------------------

data Step {Δ : TyCtx} (M : Term Δ) : Set where
  step-result : ∀ {Δ′}
    → (χ : StoreChange Δ Δ′)
    → (N : Term Δ′)
    → M —→[ χ ] N
    → Step M

pure-result : ∀ {Δ} {M N : Term Δ}
  → M —→ N
  → Step M
pure-result red = step-result keep _ (pure-step red)

app-redex? : ∀ {Δ} {L M : Term Δ}
  → Value L
  → Value M
  → Maybe (Step (L · M))
app-redex? (ƛ N) vM = just (pure-result (β vM))
app-redex? (Λ vL) vM = nothing
app-redex? ($ κ) vM = nothing
app-redex? (vL 《 inj 》) vM = nothing
app-redex? (vL 《 fun 》) vM =
  just (pure-result (β-⇒ vL vM refl))
app-redex? (vL 《 all 》) vM = nothing
app-redex? (vL 《 genᵥ A≠★ safe 》) vM = nothing
app-redex? (vL ↑ fun) vM =
  just (pure-result (β-reveal-⇒ vL vM))
app-redex? (vL ↑ all) vM = nothing
app-redex? (vL ↓ seal) vM = nothing
app-redex? (vL ↓ fun) vM =
  just (pure-result (β-conceal-⇒ vL vM))
app-redex? (vL ↓ all) vM = nothing

app-value-final? : ∀ {Δ} {L : Term Δ}
  → Value L
  → (M : Term Δ)
  → Maybe (Step (L · M))
app-value-final? vL blame =
  just (pure-result (blame-·₂ vL))
app-value-final? vL M with value? M
app-value-final? vL M | just vM = app-redex? vL vM
app-value-final? vL M | nothing = nothing

app-final? : ∀ {Δ}
  → (L M : Term Δ)
  → Maybe (Step (L · M))
app-final? blame M = just (pure-result blame-·₁)
app-final? L M with value? L
app-final? L M | just vL = app-value-final? vL M
app-final? L M | nothing = nothing

type-app-redex? : ∀ {Δ} {L : Term Δ}
  → TyStore Δ
  → (B : Ty (suc Δ))
  → (A : Ty Δ)
  → Value L
  → Maybe (Step (L ⦂∀ B [ A ]))
type-app-redex? Σ B A (ƛ N) = nothing
type-app-redex? Σ B A (Λ vV) =
  just (step-result (bind A) _ (β-Λ vV))
type-app-redex? Σ B A ($ κ) = nothing
type-app-redex? Σ B A (vV 《 inj 》) = nothing
type-app-redex? Σ B A (vV 《 fun 》) = nothing
type-app-redex? Σ B A (vV 《 all {B = C} 》) with C ≟Ty B
type-app-redex? Σ .C A (vV 《 all {B = C} 》) | yes refl =
  just (pure-result (β-∀ vV refl))
type-app-redex? Σ B A (vV 《 all {B = C} 》) | no C≠B =
  nothing
type-app-redex? Σ B A
    (vV 《 genᵥ {B = C} A≠★ safe 》) with C ≟Ty B
type-app-redex? Σ .C A
    (vV 《 genᵥ {B = C} A≠★ safe 》) | yes refl =
  just (step-result (bind A) _ (β-gen vV A≠★ safe))
type-app-redex? Σ B A
    (vV 《 genᵥ {B = C} A≠★ safe 》) | no C≠B =
  nothing
type-app-redex? Σ B A (vV ↑ fun) = nothing
type-app-redex? Σ B A (vV ↑ (all {B = D})) with D ≟Ty B
type-app-redex? Σ .D A (vV ↑ (all {B = D})) | yes refl =
  just (step-result (bind A) _ (β-reveal-∀ vV))
type-app-redex? Σ B A (vV ↑ (all {B = D})) | no D≠B = nothing
type-app-redex? Σ B A (vV ↓ seal) = nothing
type-app-redex? Σ B A (vV ↓ fun) = nothing
type-app-redex? Σ B A (vV ↓ (all {B = D})) with D ≟Ty B
type-app-redex? Σ .D A (vV ↓ (all {B = D})) | yes refl =
  just (step-result (bind A) _ (β-conceal-∀ vV))
type-app-redex? Σ B A (vV ↓ (all {B = D})) | no D≠B = nothing

type-app-final? : ∀ {Δ}
  → TyStore Δ
  → (L : Term Δ)
  → (B : Ty (suc Δ))
  → (A : Ty Δ)
  → Maybe (Step (L ⦂∀ B [ A ]))
type-app-final? Σ blame B A = just (pure-result blame-•)
type-app-final? Σ L B A with value? L
type-app-final? Σ L B A | just vL = type-app-redex? Σ B A vL
type-app-final? Σ L B A | nothing = nothing

cast-redex? : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (M : Term Δ)
  → (c : μ ⊢ A ∼ B)
  → Maybe (Step (M ⟨ c ⟩))
cast-redex? blame c = just (pure-result blame-⟨⟩)
cast-redex? M (id a) with value? M
cast-redex? M (id a) | just vM = just (pure-result (β-id vM))
cast-redex? M (id a) | nothing = nothing
cast-redex? M (c ↦ d) = nothing
cast-redex? M (∀ᶜ c) = nothing
cast-redex? M
    (_! ⦃ g-X eq ⦄ c ⦃ nonstar-X ⦄ ⦃ match-X ⦄)
    with value? M
cast-redex? M
    (_! ⦃ g-X eq ⦄ c ⦃ nonstar-X ⦄ ⦃ match-X ⦄)
    | nothing = nothing
cast-redex? M
    (_! ⦃ g-X eq ⦄ c ⦃ nonstar-X ⦄ ⦃ match-X ⦄)
    | just vM with Progress.to-ground (g-X eq) match-X c
cast-redex? M
    (_! ⦃ g-X eq ⦄ .(idᵍ (g-X eq))
      ⦃ nonstar-X ⦄ ⦃ match-X ⦄)
    | just vM | Progress.same = nothing
cast-redex? M
    (_! ⦃ g-X eq ⦄ c ⦃ nonstar-X ⦄ ⦃ match-X ⦄)
    | just vM | Progress.other A≠X =
  just
    (pure-result
      (ground ⦃ g-X eq ⦄ ⦃ nonstar-X ⦄ ⦃ match-X ⦄
        vM A≠X))
cast-redex? M (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    with value? M
cast-redex? M (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    | nothing = nothing
cast-redex? M (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    | just vM with Progress.to-ground g match c
cast-redex? M (_! ⦃ g ⦄ .(idᵍ g) ⦃ Ans ⦄ ⦃ match ⦄)
    | just vM | Progress.same = nothing
cast-redex? M (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    | just vM | Progress.other A≠G =
  just (pure-result (ground ⦃ Gns = ground-nonstar g ⦄
    ⦃ gmatch = ground-match g ⦄ vM A≠G))
cast-redex? M (？_ {G = G} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    with value? M
cast-redex? M (？_ {G = G} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    | nothing = nothing
cast-redex? M (？_ {G = G} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    | just vM with Progress.from-ground g match c
cast-redex? M (？_ {G = G} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    | just vM | Progress.other B≠G =
  just (pure-result (expand ⦃ Gns = ground-nonstar g ⦄
    ⦃ gmatch = ground-match g ⦄ vM (λ G≡B → B≠G (sym G≡B))))
cast-redex? ._ (？_ {G = G} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | just
      (vW 《 inj {G = H} ⦃ h ⦄ ⦃ Hns ⦄ ⦃ hmatch ⦄ 》)
    | Progress.same with H ≟Ty G
cast-redex? ._ (？_ {G = .H} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | just
      (vW 《 inj {G = H} ⦃ h ⦄ ⦃ Hns ⦄ ⦃ hmatch ⦄ 》)
    | Progress.same | yes refl rewrite nonStar-unique Bns Hns =
  just (pure-result (tag-untag
    ⦃ g = h ⦄ ⦃ h = g ⦄
    ⦃ Gns = Hns ⦄ ⦃ gmatch = hmatch ⦄
    ⦃ hmatch = match ⦄ vW))
cast-redex? ._ (？_ {G = G} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | just
      (vW 《 inj {G = H} ⦃ h ⦄ ⦃ Hns ⦄ ⦃ hmatch ⦄ 》)
    | Progress.same | no H≠G =
  just (pure-result (tag-untag-bad
    ⦃ g = h ⦄ ⦃ h = g ⦄
    ⦃ Gns = Hns ⦄ ⦃ gmatch = hmatch ⦄
    ⦃ Hns = Bns ⦄ ⦃ hmatch = match ⦄ vW H≠G))
cast-redex? M (？_ {G = G} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | just vM | Progress.same = nothing
cast-redex? M (inst_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    with value? M
cast-redex? M (inst_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | nothing = nothing
cast-redex? M (inst_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | just vM with B ≟Ty ★
cast-redex? M (inst_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | just vM | no B≠★ =
  just (step-result (bind ★) _ (β-inst vM B≠★))
cast-redex? M (inst_ {B = .★} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | just vM | yes refl with Progress.ground-inst-view c Anv z∈A
cast-redex? M (inst_ {B = .★} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | just vM | yes refl | Progress.factor f =
  just (pure-result (ground-∀ vM f))
cast-redex? M (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    with value? M
cast-redex? M (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | nothing = nothing
cast-redex? M (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | just vM with A ≟Ty ★
cast-redex? M (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | just vM | no A≠★ = nothing
cast-redex? M (gen_ {A = .★} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | just vM | yes refl with Progress.ground-gen-view c Bnv z∈B
cast-redex? M (gen_ {A = .★} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | just vM | yes refl | Progress.factor f =
  just (pure-result (expand-∀ vM f))

prim-value-final? : ∀ {Δ} {L : Term Δ}
  → (op : Prim)
  → Value L
  → (M : Term Δ)
  → Maybe (Step (L ⊕[ op ] M))
prim-value-final? op vL blame = just (pure-result (blame-⊕₂ vL))
prim-value-final? addℕ ($ (κℕ m)) ($ (κℕ n)) =
  just (pure-result (δ-⊕ δ-add))
prim-value-final? and𝔹 ($ (κ𝔹 b)) ($ (κ𝔹 c)) =
  just (pure-result (δ-⊕ δ-and))
prim-value-final? op vL M = nothing

prim-final? : ∀ {Δ}
  → (op : Prim)
  → (L M : Term Δ)
  → Maybe (Step (L ⊕[ op ] M))
prim-final? op blame M = just (pure-result blame-⊕₁)
prim-final? op L M with value? L
prim-final? op L M | just vL = prim-value-final? op vL M
prim-final? op L M | nothing = nothing

reveal-final? : ∀ {Δ}
  → (M : Term Δ)
  → ∀ {A B} (c : Conv↑ Δ A B)
  → Maybe (Step (M ↑ c))
reveal-final? blame c = just (pure-result blame-reveal)
reveal-final? M (unseal X R) with value? M
reveal-final? ._ (unseal X R)
    | just (vV ↓ seal {X = Y} {R = S}) with X ≟ Y
reveal-final? ._ (unseal .Y R)
    | just (vV ↓ seal {X = Y} {R = S}) | yes refl
    with R ≟Ty S
reveal-final? ._ (unseal .Y .S)
    | just (vV ↓ seal {X = Y} {R = S}) | yes refl | yes refl =
  just (pure-result (conceal-reveal vV))
reveal-final? ._ (unseal .Y R)
    | just (vV ↓ seal {X = Y} {R = S}) | yes refl | no R≠S =
  nothing
reveal-final? ._ (unseal X R)
    | just (vV ↓ seal {X = Y} {R = S}) | no X≠Y = nothing
reveal-final? M (unseal X R) | just vM = nothing
reveal-final? M (unseal X R) | nothing = nothing
reveal-final? M (c ↦↑ d) = nothing
reveal-final? M (`∀↑ c) = nothing
reveal-final? M (id↑ A) with value? M
reveal-final? M (id↑ A) | just vM = just (pure-result (id-reveal vM))
reveal-final? M (id↑ A) | nothing = nothing

conceal-final? : ∀ {Δ}
  → (M : Term Δ)
  → ∀ {A B} (c : Conv↓ Δ A B)
  → Maybe (Step (M ↓ c))
conceal-final? blame c = just (pure-result blame-conceal)
conceal-final? M (seal X R) = nothing
conceal-final? M (c ↦↓ d) = nothing
conceal-final? M (`∀↓ c) = nothing
conceal-final? M (id↓ A) with value? M
conceal-final? M (id↓ A) | just vM = just (pure-result (id-conceal vM))
conceal-final? M (id↓ A) | nothing = nothing

step? : ∀ {Δ} → TyStore Δ → (M : Term Δ) → Maybe (Step M)
step? Σ (` x) = nothing
step? Σ (ƛ N) = nothing
step? Σ (Λ N) = nothing
step? Σ ($ κ) = nothing
step? Σ blame = nothing
step? Σ (L · M) with step? Σ L
step? Σ (L · M) | just (step-result χ L′ L→L′) =
  just (step-result χ (L′ · χ ▷ᵀ M) (ξ-·₁ L→L′ refl))
step? Σ (L · M) | nothing with step? Σ M
step? Σ (L · M) | nothing | just (step-result χ M′ M→M′)
    with value? L
step? Σ (L · M) | nothing | just (step-result χ M′ M→M′)
    | just vL =
  just (step-result χ (χ ▷ᵀ L · M′) (ξ-·₂ vL M→M′ refl))
step? Σ (L · M) | nothing | just (step-result χ M′ M→M′)
    | nothing = app-final? L M
step? Σ (L · M) | nothing | nothing = app-final? L M
step? Σ (L ⦂∀ B [ A ]) with step? Σ L
step? Σ (L ⦂∀ B [ A ])
    | just (step-result χ L′ L→L′) =
  just
    (step-result χ
      (L′ ⦂∀ χ ▷ᵇ B [ χ ▷ᵗ A ])
      (ξ-• L→L′ refl refl))
step? Σ (L ⦂∀ B [ A ]) | nothing = type-app-final? Σ L B A
step? Σ (L ⊕[ op ] M) with step? Σ L
step? Σ (L ⊕[ op ] M) | just (step-result χ L′ L→L′) =
  just (step-result χ (L′ ⊕[ op ] χ ▷ᵀ M)
    (ξ-⊕₁ L→L′ refl))
step? Σ (L ⊕[ op ] M) | nothing with step? Σ M
step? Σ (L ⊕[ op ] M) | nothing
    | just (step-result χ M′ M→M′) with value? L
step? Σ (L ⊕[ op ] M) | nothing
    | just (step-result χ M′ M→M′) | just vL =
  just (step-result χ (χ ▷ᵀ L ⊕[ op ] M′)
    (ξ-⊕₂ vL M→M′ refl))
step? Σ (L ⊕[ op ] M) | nothing
    | just (step-result χ M′ M→M′) | nothing =
  prim-final? op L M
step? Σ (L ⊕[ op ] M) | nothing | nothing = prim-final? op L M
step? Σ (M ⟨ c ⟩) with step? Σ M
step? Σ (M ⟨ c ⟩) | just (step-result χ M′ M→M′) =
  just (step-result χ (M′ ⟨ χ ▷ᶜ c ⟩)
    (ξ-⟨⟩ M→M′ refl))
step? Σ (M ⟨ c ⟩) | nothing = cast-redex? M c
step? Σ (M ↑ c) with step? Σ M
step? Σ (M ↑ c) | just (step-result χ M′ M→M′) =
  just (step-result χ (M′ ↑ rename↑ (λ X → χ ▷ᵛ X) c)
    (ξ-reveal M→M′ refl))
step? Σ (M ↑ c) | nothing = reveal-final? M c
step? Σ (M ↓ c) with step? Σ M
step? Σ (M ↓ c) | just (step-result χ M′ M→M′) =
  just (step-result χ (M′ ↓ rename↓ (λ X → χ ▷ᵛ X) c)
    (ξ-conceal M→M′ refl))
step? Σ (M ↓ c) | nothing = conceal-final? M c

------------------------------------------------------------------------
-- Fuel-bounded traces
------------------------------------------------------------------------

record EvalResult {Δ : TyCtx} (M : Term Δ) : Set where
  constructor result
  field
    Δ′ : TyCtx
    changes : StoreChanges Δ Δ′
    term : Term Δ′
    trace : M —↠[ changes ] term
    value : Value term

open EvalResult public

data EvalOutcome {Δ : TyCtx} (M : Term Δ) : Set where
  returned : EvalResult M → EvalOutcome M
  blamed : ∀ {Δ′}
    → (changes : StoreChanges Δ Δ′)
    → M —↠[ changes ] blame
    → EvalOutcome M

outcomeCtx : ∀ {Δ} {M : Term Δ} → EvalOutcome M → TyCtx
outcomeCtx (returned r) = Δ′ r
outcomeCtx (blamed {Δ′} changes M↞blame) = Δ′

outcomeChanges : ∀ {Δ} {M : Term Δ} (r : EvalOutcome M)
  → StoreChanges Δ (outcomeCtx r)
outcomeChanges (returned r) = changes r
outcomeChanges (blamed changes M↞blame) = changes

finalTerm : ∀ {Δ} {M : Term Δ} (r : EvalOutcome M)
  → Term (outcomeCtx r)
finalTerm (returned r) = term r
finalTerm (blamed changes M↞blame) = blame

outcomeTrace : ∀ {Δ} {M : Term Δ} (r : EvalOutcome M)
  → M —↠[ outcomeChanges r ] finalTerm r
outcomeTrace (returned r) = trace r
outcomeTrace (blamed changes M↞blame) = M↞blame

evalFrom : ∀ {Δ}
  → TyStore Δ
  → (gas : ℕ)
  → (M : Term Δ)
  → Maybe (EvalOutcome M)
evalFrom Σ zero blame = just (blamed [] ↠-refl)
evalFrom Σ zero M with value? M
evalFrom Σ zero M | just vM =
  just (returned (result _ [] M ↠-refl vM))
evalFrom Σ zero M | nothing = nothing
evalFrom Σ (suc gas) blame = just (blamed [] ↠-refl)
evalFrom Σ (suc gas) M with value? M
evalFrom Σ (suc gas) M | just vM =
  just (returned (result _ [] M ↠-refl vM))
evalFrom Σ (suc gas) M | nothing with step? Σ M
evalFrom Σ (suc gas) M | nothing | nothing = nothing
evalFrom Σ (suc gas) M | nothing
    | just (step-result χ N M→N)
      with evalFrom (χ ▷ˢ Σ) gas N
evalFrom Σ (suc gas) M | nothing
    | just (step-result χ N M→N) | nothing = nothing
evalFrom Σ (suc gas) M | nothing
    | just (step-result χ N M→N)
    | just (returned (result Δ″ χs V N↠V vV)) =
  just (returned (result Δ″ (χ ∷ χs) V (↠-step M→N N↠V) vV))
evalFrom Σ (suc gas) M | nothing
    | just (step-result χ N M→N)
    | just (blamed χs N↠blame) =
  just (blamed (χ ∷ χs) (↠-step M→N N↠blame))

eval : (gas : ℕ)
  → (M : Term zero)
  → Maybe (EvalOutcome M)
eval = evalFrom store-empty

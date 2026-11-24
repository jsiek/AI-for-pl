module proof.LR.Case6Probe where

-- File Charter:
--   * A counterexample to the cast lemma's case 6 (left `∀ᶜ`, right
--     `inst`; notes/logrel-dgg.md, Section 7, "Case 6: a counterexample
--     in ≺") stated over the value relation alone.
--   * In `≺` at stage 1, the `∀⊑∀` clause holds for any right value,
--     because the left's instantiation takes its one counted step.  So
--     the polymorphic identity is related to the constant `$ 0`.
--   * The casts sit at related types and are in eager normal form, as
--     the two-sided cast rule asks: left `∀ᶜ (id ↦ id)` at
--     `∀X.X→★ ∼ ∀X.X→★`, right `inst (？X ↦ id)` at `∀X.X→★ ∼ ★→★`,
--     with `∀X.X→★ ⊑ ★→★` by `∀⊑`.
--   * The left cast gives a value at once; the right allocates and then
--     instantiates `$ 0`, which is stuck.  So the casts are not related
--     in `ℰ ≺ 1`: the cast lemma needs more about the right value than
--     the value relation says.
--   * Resolution (notes/logrel-dgg.md, Section 7, "Typing the right"):
--     the cast lemma's hypothesis is `𝒱ᵀ`, the value relation with the
--     right value typed in the world's right store.  `$ 0` is not typed
--     at `∀X.X→★` (`untyped`), so the pair is not in `𝒱ᵀ`
--     (`excluded`); a typed right value's instantiation reaches a value
--     (`proof.TypeSafety.InstValue`).

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Nat using (suc; s≤s; z≤n; _≤′_; ≤′-refl; ≤′-step)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using (store-empty)
open import Consistency
open import Conversion using (Conv↑)
open import CastTerms
open import Primitives using (κℕ)
open import Reduction
open import LR.Precision
open import LR.EagerCast
open import LR.World
open import LR.Steps
open import LR.Relation
open import proof.Reduction.ValueIrreducibleProof using (value-no-step)

------------------------------------------------------------------------
-- The data
------------------------------------------------------------------------

w₀ : World
w₀ = mkWorld 0 0 (λ ()) 0 pid store-empty

-- the bodies `X → ★` of the two `∀` types, X paired
p₀ : pair [] ⊢ ＇ zero ⇒ ★ ⊑ ＇ zero ⇒ ★
p₀ = ⇒⊑⇒ (X⊑Y ↔-here) ★⊑★

-- the cast's source types `∀X.X→★ ⊑ ∀X.X→★`
p : [] ⊢ `∀ (＇ zero ⇒ ★) ⊑ `∀ (＇ zero ⇒ ★)
p = ∀⊑∀ p₀

-- the cast's target types `∀X.X→★ ⊑ ★→★`
r : [] ⊢ `∀ (＇ zero ⇒ ★) ⊑ ★ ⇒ ★
r = ∀⊑ nonvar-fun (∈-fun-left var-∈) (⇒⊑⇒ (X⊑★ only-here) ★⊑★)

cl : []ᵛ ⊢ `∀ (＇ zero ⇒ ★) ∼ `∀ (＇ zero ⇒ ★)
cl = ∀ᶜ (id (＇ zero) ↦ id ★)

d₁ : flipᵐ (instᵐ []ᵛ) ⊢ ★ ∼ ＇ zero
d₁ = ？_ ⦃ ＇ zero ⦄ ⦃ ★∼Xᵍ refl ⦄ (id (＇ zero)) ⦃ nonstar-X ⦄

cr : []ᵛ ⊢ `∀ (＇ zero ⇒ ★) ∼ ★ ⇒ ★
cr = (inst_ ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄ (d₁ ↦ id ★)) (λ ())

cl-eager : Eager cl
cl-eager = e-∀ (e-↦ e-id e-id)

cr-eager : Eager cr
cr-eager = e-inst ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄ (e-↦ (e-？ e-id) e-id)

-- the casts' types are the derivations' types under the interpretation
cl-src : substᵗ (δl (closedI {0} {0})) (`∀ (＇ zero ⇒ ★))
  ≡ `∀ (＇ zero ⇒ ★)
cl-src = refl

Vl : Term 0
Vl = Λ (ƛ (` 0))

Vr : Term 0
Vr = $ (κℕ 0)

------------------------------------------------------------------------
-- The values are related at stage 1
------------------------------------------------------------------------

-- the left instantiation runs the one counted step
runs : ∀ {Δ} {B : Ty (suc Δ)} {T : Ty Δ} {n′} → n′ ≤′ 1
  → Runs ((Λ (ƛ (` 0))) ⦂∀ B [ T ]) n′
runs ≤′-refl = _ , _ , _ , more (β-Λ (ƛ (` 0))) none
runs (≤′-step ≤′-refl) = _ , [] , _ , none

related : 𝒱 ≺ 1 p w₀ closedI Vl Vr
related e le c wf T₀ eqT B₀ eqB = inj₁ (runs le)

------------------------------------------------------------------------
-- The typed relation excludes them
------------------------------------------------------------------------

-- `$ 0` is typed only at `ℕ`
untyped : ¬ Typedᴿ w₀ (`∀ (＇ zero ⇒ ★)) Vr
untyped (typedᴿ _ () (⊢$ _))

excluded : ¬ 𝒱ᵀ ≺ 1 p w₀ closedI Vl Vr
excluded (t , r) = untyped t

------------------------------------------------------------------------
-- The casts are not related at stage 1
------------------------------------------------------------------------

$-no-step : ∀ {Δ Δ′} {κ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → $ κ —→[ χ ] N → ⊥
$-no-step {κ = κ} s = value-no-step ($ κ) s

module _ {Δ} {κ} {B : Ty (suc Δ)} {T : Ty Δ} where

  M₀ : Term Δ
  M₀ = $ κ ⦂∀ B [ T ]

  app-stuck : ∀ {Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    → M₀ —→[ χ ] N → ⊥
  app-stuck (pure-step ())
  app-stuck (ξ-• s _ _) = $-no-step s

  module _ {A₁ A₂ : Ty Δ} {k : Conv↑ Δ A₁ A₂} where

    notVal : Value (M₀ ↑ k) → ⊥
    notVal (() ↑ _)

    reveal-stuck : ∀ {Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
      → M₀ ↑ k —→[ χ ] N → ⊥
    reveal-stuck (pure-step (id-reveal ()))
    reveal-stuck (ξ-reveal s _) = app-stuck s

    cast-stuck : ∀ {μ} {C₁ C₂ : Ty Δ} {c : μ ⊢ C₁ ∼ C₂}
        {Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
      → (M₀ ↑ k) ⟨ c ⟩ —→[ χ ] N → ⊥
    cast-stuck (pure-step (β-id v)) = notVal v
    cast-stuck (pure-step (ground v _)) = notVal v
    cast-stuck (pure-step (expand v _)) = notVal v
    cast-stuck (pure-step (blame-bot-intro v)) = notVal v
    cast-stuck (β-inst v _) = notVal v
    cast-stuck (ξ-⟨⟩ s _) = reveal-stuck s

    run-stuck : ∀ {μ} {C₁ C₂ : Ty Δ} {c : μ ⊢ C₁ ∼ C₂}
        {Δ′} {χs : StoreChanges Δ Δ′} {N : Term Δ′}
      → (M₀ ↑ k) ⟨ c ⟩ —↠[ χs ] N → Value N → ⊥
    run-stuck ↠-refl (v 《 _ 》) = notVal v
    run-stuck (↠-step s _) _ = cast-stuck s

-- the right cast allocates, then instantiates `$ 0`, and is stuck
right-stuck : ∀ {Δ′} {χs : StoreChanges 0 Δ′} {N : Term Δ′}
  → Vr ⟨ cr ⟩ —↠[ χs ] N → Value N → ⊥
right-stuck ↠-refl (_ 《 () 》)
right-stuck (↠-step (pure-step ()) _) _
right-stuck (↠-step (ξ-⟨⟩ s _) _) _ = $-no-step s
right-stuck (↠-step (β-inst _ _) rest) vN = run-stuck rest vN

left-value : Value (Vl ⟨ cl ⟩)
left-value = (Λ (ƛ (` 0))) 《 all 》

unrelated : ¬ ℰ ≺ 1 r w₀ closedI (Vl ⟨ cl ⟩) (Vr ⟨ cr ⟩)
unrelated (inj₁ (_ , _ , _ , more s _)) = value-no-step left-value s
unrelated (inj₂ (inj₁ (_ , _ , _ , s≤s z≤n , ())))
unrelated (inj₂ (inj₂ (_ , _ , _ , _ , _ , _ , _ , _ , _ ,
    _ , _ , runR , _ , vr , _))) = right-stuck runR vr

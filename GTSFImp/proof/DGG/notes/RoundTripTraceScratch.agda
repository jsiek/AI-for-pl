module RoundTripTraceScratch where

-- Root-only scratch for the ★ round-trip pair.
-- It records the literal gradual syntax, the source consistency obstruction,
-- executable cast-calculus probes for the expected runtime shape, and the
-- StarRepChainProbe mid-simulation relation instance.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using (store-empty)
open import Consistency using
  (Env∼; X∼★; ★∼X; idᶜ; instᵐ; genᵐ; _⊢_∼_; _∼_;
   id; _!; ？_; X∼★ᵍ; ★∼Xᵍ)
import GradualTerms as G
open import CastTerms
  using
    (Term; Value; `_ ; ƛ_; Λ_; $; _·_; _⦂∀_[_]; _⟨_⟩; _↓_;
     _《_》; inj; seal)
open import Reduction
open import Eval
open import Primitives using (κℕ)
import proof.Consistency2 as C2
open import proof.DGG.CastTermImprecision2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.ReachabilityScreen as RS
import proof.DGG.StarRepChainProbe as Probe

------------------------------------------------------------------------
-- Literal source syntax
------------------------------------------------------------------------

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

roundInnerᴳ : ∀ {Δ} → G.GTerm Δ
roundInnerᴳ =
  G.Λ
    (G.ƛ ＇ Fin.zero ⇒
      ((G.ƛ ＇ Fin.zero ⇒ G.` 0) G.·[ 80 ]
        (((G.ƛ ★ ⇒ G.` 0) G.·[ 81 ] G.` 0))))

Pᴳ : G.GTerm 0
Pᴳ =
  (((G.Λ
      (G.ƛ ＇ Fin.zero ⇒
        ((roundInnerᴳ {Δ = 1} G.`[ ＇ Fin.zero ])
          G.·[ 82 ] G.` 0)))
    G.`[ ★ ])
    G.·[ 83 ] G.$ (κℕ 0))

Qᴳ : G.GTerm 0
Qᴳ =
  (G.ƛ ★ ⇒
    ((roundInnerᴳ {Δ = 0} G.`[ ★ ]) G.·[ 82 ] G.` 0))
  G.·[ 83 ] G.$ (κℕ 0)

------------------------------------------------------------------------
-- Source consistency obstruction
------------------------------------------------------------------------

id-not-X∼★ : ∀ {Δ} {X : TyVar Δ} → idᶜ X ≢ X∼★
id-not-X∼★ ()

id-not-★∼X : ∀ {Δ} {X : TyVar Δ} → idᶜ X ≢ ★∼X
id-not-★∼X ()

Z : TyVar 1
Z = Fin.zero

Z₁ : Ty 1
Z₁ = ＇ Z

no-id-Z∼★ : idᶜ {Δ = 1} ⊢ Z₁ ∼ ★ → ⊥
no-id-Z∼★ c =
  C2.star-no-occurs
    (C2.source-occurs-target-safe {X = Z}
      (id-not-X∼★ {X = Z}) c (var-∈ {X = Z}))

no-id-★∼Z : idᶜ {Δ = 1} ⊢ ★ ∼ Z₁ → ⊥
no-id-★∼Z c =
  C2.star-no-occurs
    (C2.target-occurs-source-safe {X = Z}
      (id-not-★∼X {X = Z}) c (var-∈ {X = Z}))

-- These are the two source consistency obligations needed by the
-- round-trip body before compilation:
--
--   (λw : ★. w) x      needs ★ ∼ Z
--   (λy : Z. y) (...)  needs Z ∼ ★
--
-- Both are refuted above for the current closed source consistency relation.

------------------------------------------------------------------------
-- Cast-calculus probe for the expected runtime shape
------------------------------------------------------------------------

ℕ! : ∀ {Δ} → idᶜ {Δ = Δ} ⊢ ‵ `ℕ ∼ ★
ℕ! = id (‵ `ℕ) !

Z! : ∀ {Δ} → instᵐ (idᶜ {Δ = Δ}) ⊢ ＇ Fin.zero ∼ ★
Z! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

Z? : ∀ {Δ} → genᵐ (idᶜ {Δ = Δ}) ⊢ ★ ∼ ＇ Fin.zero
Z? =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

roundInnerᶜ : ∀ {Δ} → Term Δ
roundInnerᶜ =
  Λ
    (ƛ
      ((ƛ (` 0)) ·
        (((ƛ (` 0)) · ((` 0) ⟨ Z! ⟩)) ⟨ Z? ⟩)))

Pᶜ-probe : Term 0
Pᶜ-probe =
  ((Λ
      (ƛ
        ((roundInnerᶜ {Δ = 1} ⦂∀ X⇒X [ ＇ Fin.zero ])
          · (` 0))))
    ⦂∀ X⇒X [ ★ ])
  · (($ (κℕ 0)) ⟨ ℕ! ⟩)

Qᶜ-probe : Term 0
Qᶜ-probe =
  (ƛ ((roundInnerᶜ {Δ = 0} ⦂∀ X⇒X [ ★ ]) · (` 0)))
  · (($ (κℕ 0)) ⟨ ℕ! ⟩)

P-probe-status : RS.SideSummary.status (RS.runSummary 40 Pᶜ-probe)
  ≡ RS.returned-value
P-probe-status = refl

Q-probe-status : RS.SideSummary.status (RS.runSummary 40 Qᶜ-probe)
  ≡ RS.returned-value
Q-probe-status = refl

P-probe-allocations : RS.SideSummary.allocations (RS.runSummary 40 Pᶜ-probe)
  ≡ RS.alloc 0 0 RS.entry-star [] ∷
     RS.alloc 3 1 RS.entry-var (0 ∷ []) ∷ []
P-probe-allocations = refl

Q-probe-allocations : RS.SideSummary.allocations (RS.runSummary 40 Qᶜ-probe)
  ≡ RS.alloc 1 0 RS.entry-star [] ∷ []
Q-probe-allocations = refl

P-probe-tags-nonempty :
  RS.SideSummary.tags (RS.runSummary 40 Pᶜ-probe) ≢ []
P-probe-tags-nonempty ()

Q-probe-tags-nonempty :
  RS.SideSummary.tags (RS.runSummary 40 Qᶜ-probe) ≢ []
Q-probe-tags-nonempty ()

------------------------------------------------------------------------
-- Payoff relation instance, reused from StarRepChainProbe
------------------------------------------------------------------------

roundtrip-mid-output :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.target-sealed ∶ Probe.q
roundtrip-mid-output = Probe.output

roundtrip-mid-input :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.N ∶ Probe.input-type
roundtrip-mid-input = Probe.input

roundtrip-mid-q = Probe.q

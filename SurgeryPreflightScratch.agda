module SurgeryPreflightScratch where

-- Root-level scratch for the tag-discipline surgery pre-flight.
-- It checks the source-seal target-shape gates that decide whether the
-- remaining M3 source-strip clauses are still legal under the restricted
-- source-side seal rule.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Conversion using (Conv↓; seal)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; _⟨_⟩; _↓_; $)
open import Primitives using (κℕ)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Examples2 as Ex2
import proof.DGG.TerminusRebuildProbe as TRB
import proof.DGG.Inversion.TargetDescentDef as TDD
import proof.DGG.Inversion.TargetDescentProof as TDP
import TagDisciplineScratch as TD

open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Generic restricted source-seal frame
------------------------------------------------------------------------

record RestrictedSourceSealFrame {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W′ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
    {Xᴸ?} {Xᴿ?} {c : Conv↓ Δᴸ A A′} : Set where
  field
    target-ok : TD.SealTargetOK Xᴿ? M′
    rebaseᴸ : TD.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    premise² : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    live² : W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q

top-tag-not-plain : ∀ {Δ M A B} {μ : Env∼ Δ}
    {c : μ ⊢ A ∼ B}
  → TD.NotTopTag (M ⟨ c ⟩)
  → ⊥
top-tag-not-plain ()

name-tagged-target-not-none : ∀ {Δ Y S M A B} {μ : Env∼ Δ}
    {c : μ ⊢ A ∼ B}
  → TD.SealTargetOK nothing ((M ↓ seal Y S) ⟨ c ⟩)
  → ⊥
name-tagged-target-not-none (TD.plain-target ())

------------------------------------------------------------------------
-- Q1. M3 stuck input-shape gates
------------------------------------------------------------------------

-- The `cast⊑cast²` premise case is still legal: the outer source seal's
-- target partner is exactly `(U ↓ seal Y S) ⟨ Y! ⟩`.
m3-cast⊑cast²-input :
  RestrictedSourceSealFrame
    {W = TRB.InstanceB.W}
    {W′ = TRB.InstanceB.W}
    {γ = []}
    {γ′ = []}
    {M = TRB.InstanceB.source-payload}
    {M′ = TRB.InstanceB.target-tagged}
    {A = ★}
    {A′ = ＇ TRB.InstanceB.X}
    {B = ★}
    {p = ★⊑★}
    {q = TRB.InstanceB.X⊑★-W}
    {Xᴸ? = just TRB.InstanceB.X}
    {Xᴿ? = just TRB.InstanceB.Y}
    {c = seal TRB.InstanceB.X ★}
m3-cast⊑cast²-input = record
  { target-ok = TD.name-tagged-target
  ; rebaseᴸ = TD.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y
  ; premise² = TRB.InstanceB.premise-casts²
  ; live² = TRB.InstanceB.tagged-input
  }

-- The `cast⊑²` premise case is also still legal.  This is the same
-- name-tagged target, but with the source inert cast folded before the
-- outer source seal.
m3-cast⊑²-source-to-tag :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.V ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
m3-cast⊑²-source-to-tag =
  CTI2.⊑cast² TRB.InstanceB.Y! TRB.InstanceB.premise-chain²
    TRB.InstanceB.X⊑★-W

m3-cast⊑²-premise :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source-payload ⊑ TRB.InstanceB.target-tagged ∶
      ★⊑★
m3-cast⊑²-premise =
  CTI2.cast⊑² TRB.InstanceB.X! m3-cast⊑²-source-to-tag ★⊑★

m3-cast⊑²-live :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
m3-cast⊑²-live =
  CTI2.conceal⊑² (TRB.mono-refl {W = TRB.InstanceB.W})
    (CTI2.rebase-varᴸ TRB.InstanceB.rb-X-Y)
    CTI2.same-[] TRB.InstanceB.source-seal-⊢
    m3-cast⊑²-premise TRB.InstanceB.X⊑★-W

m3-cast⊑²-input :
  RestrictedSourceSealFrame
    {W = TRB.InstanceB.W}
    {W′ = TRB.InstanceB.W}
    {γ = []}
    {γ′ = []}
    {M = TRB.InstanceB.source-payload}
    {M′ = TRB.InstanceB.target-tagged}
    {A = ★}
    {A′ = ＇ TRB.InstanceB.X}
    {B = ★}
    {p = ★⊑★}
    {q = TRB.InstanceB.X⊑★-W}
    {Xᴸ? = just TRB.InstanceB.X}
    {Xᴿ? = just TRB.InstanceB.Y}
    {c = seal TRB.InstanceB.X ★}
m3-cast⊑²-input = record
  { target-ok = TD.name-tagged-target
  ; rebaseᴸ = TD.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y
  ; premise² = m3-cast⊑²-premise
  ; live² = m3-cast⊑²-live
  }

-- The nested source-conceal premise is not killed by the target-shape
-- restriction when its inner source-seal descent is also name-protected at
-- the same target name.  The full recursive worker still has to prove the
-- structural impossibility/recursive descent facts, but the new gate does
-- not make the shape empty.
m3-nested-conceal-target-ok :
  TD.SealTargetOK (just TRB.InstanceB.Y) TRB.InstanceB.target-tagged
m3-nested-conceal-target-ok = TD.name-tagged-target

-- The `rebase-onlyᴸ` premise has no target name available.  Since the M3
-- source-spine input target is a top-level tag, this branch is no longer
-- formable under the restricted rule.
m3-rebase-only-input-empty :
  TD.SealTargetOK nothing TRB.InstanceB.target-tagged
  → ⊥
m3-rebase-only-input-empty = name-tagged-target-not-none

------------------------------------------------------------------------
-- Q2. Proven re-emission construction gates
------------------------------------------------------------------------

terminus-instanceA-tagged-partner-ok :
  TD.SealTargetOK (just TRB.InstanceA.Y) TRB.InstanceA.target-tagged
terminus-instanceA-tagged-partner-ok = TD.name-tagged-target

terminus-instanceA-live-tagged-input :
  TRB.InstanceA.W ∣ [] ⊢²
    TRB.InstanceA.source ⊑ TRB.InstanceA.target-tagged ∶
      TRB.InstanceA.X⊑★-W
terminus-instanceA-live-tagged-input = TRB.InstanceA.tagged-input

terminus-instanceA-direct-dyn-id-empty :
  TD.SealTargetOK (just TRB.InstanceA.Y) TRB.InstanceA.U
  → ⊥
terminus-instanceA-direct-dyn-id-empty (TD.plain-target ())

terminus-instanceB-tagged-partner-ok :
  TD.SealTargetOK (just TRB.InstanceB.Y) TRB.InstanceB.target-tagged
terminus-instanceB-tagged-partner-ok = TD.name-tagged-target

terminus-instanceB-live-tagged-input :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
terminus-instanceB-live-tagged-input = TRB.InstanceB.tagged-input

terminus-instanceB-inner-dyn-id-empty :
  TD.SealTargetOK (just TRB.InstanceB.Y₂) TRB.InstanceB.U₀
  → ⊥
terminus-instanceB-inner-dyn-id-empty (TD.plain-target ())

seal-descent-at-var-＇-reemit-instance :
  TDD.TargetSealReemit TRB.InstanceB.W [] TRB.InstanceB.source-payload
    TRB.InstanceB.U TRB.InstanceB.X TRB.InstanceB.Y TRB.InstanceB.Y₂
    TRB.InstanceB.X⊑Y
seal-descent-at-var-＇-reemit-instance =
  TDP.target-seal＇-reemit TRB.InstanceB.mono-W-Wᵖ
    TRB.InstanceB.rb-chain CTI2.same-[] TRB.InstanceB.Y∈
    TRB.InstanceB.X⊑Y TRB.InstanceB.X⊑Y₂

------------------------------------------------------------------------
-- Q3. `left-path-argument₄`
------------------------------------------------------------------------

left-path-argument₄-old-wrapper-empty :
  TD.SealTargetOK nothing
    (($ (κℕ 7)) ⟨ Ex2.left-path-ℕ!₂ ⟩)
  → ⊥
left-path-argument₄-old-wrapper-empty (TD.plain-target ())

left-path-argument₄-payload-survives :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      Ex2.left-path-ℕ⊑★₄-YZ
left-path-argument₄-payload-survives =
  Ex2.left-path-argument₄-base

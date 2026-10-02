module TermImprecisionExamples where

-- File Charter:
--   * SANITY DERIVATIONS of `W ∣ γ ⊢ M ⊑ M′ ∶ p` (TermImprecision) on
--     the pairs of ImprecisionExamples (design.md §12.4):
--       p1-init   P1's initial pair L1 ⊑ R1: ·⊑·, ν⊑ν (ℕ ⊑ ★), Λ⊑Λ,
--                 ƛ⊑ƛ, x⊑x; ⊑cast, κ⊑κ for the argument
--       p1-tybeta P1 after both TyBetas: ·⊑·, ⟪⟫⊑⟪⟫ with X both-sided
--                 and ϱᵍ = {(αᴸ, αᴿ)}, αᴸ:=ℕ, αᴿ:=★
--       p2-tybeta P2 after the left's TyBeta: ·⊑·, ⟪⟫⊑ with X left-only
--                 (X⊑★), X→X ⊑ ★→★ inside, ℕ→ℕ ⊑ ★→★ outside
--       p3-inst   P3 after the right's Inst, TyBeta, Beta: ·⊑·, ν⊑,
--                 ⊑cast, ∀⊑⟪+⟫ (the left Λ's abstract rep. var paired
--                 lexically with αᴿ:=★; `inst-Λ`)
--     The later states are pinned to `evalTerms` by `refl`
--     (`*-state`), as Examples.ex7-env does, so they are the run's own
--     terms, not transcriptions.
--   * TYPING SIDE PREMISES come from `tc` derivations of the subterms,
--     read back into the rules' bundles by TermImprecision's inversions
--     (`ν-inv`, `⟪⟫-inv`).
--   * WELL-FORMEDNESS.  `Wᵢ₁-wf` checks `WfWorld` on p1-tybeta's
--     interior world (X both-sided names the paired αᴸ, αᴿ; ℕ ⊑ ★).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; head; drop)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TypeCheck using (tc; tf)
open import Eval using (evalTerms)
open import Imprecision
open import ImprecisionWorld
open import TermImprecision
open import ImprecisionExamples
  using (L1; R1; L1-⊢; R1-⊢; R2; L3-⊢; R3-⊢)
open import Reduction using (inst-Λ)

------------------------------------------------------------------------
-- Shared pieces
------------------------------------------------------------------------

idX : Term
idX = ƛ (` 0) ∙ ` 0

revX : Conv
revX = reveal 0 (` 0 ⇒ ` 0)

ℕ⊑★ : ∀ {μ} → μ ⊢ `ℕ ⊑ ★
ℕ⊑★ = ι⊑★ base-ℕ

5⟨ℕ!⟩ : Term
5⟨ℕ!⟩ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

-- the argument `5 ⊑ 5⟨ℕ!⟩` at ℕ ⊑ ★, in any world whose right side has
-- no names (the cast carries `[]`)
five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

∀X⇒X : Ty
∀X⇒X = `∀ (` 0 ⇒ ` 0)

------------------------------------------------------------------------
-- P1, initial pair
------------------------------------------------------------------------

νL νR : Term
νL = ν `ℕ · Λ idX ⟨ revX ⟩
νR = ν ★ · Λ idX ⟨ revX ⟩

νL-⊢ : empty ∣ [] ⊢ νL ⦂ `ℕ ⇒ `ℕ
νL-⊢ = tc

νR-⊢ : empty ∣ [] ⊢ νR ⦂ ★ ⇒ ★
νR-⊢ = tc

νL-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
νL-ty = proj₂ (proj₂ (ν-inv νL-⊢))

νR-ty : NuTy empty ★ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
νR-ty = proj₂ (proj₂ (ν-inv νR-⊢))

p1-init : ∅ʷ ∣ [] ⊢ L1 ⊑ R1 ∶ ℕ⊑★
p1-init =
  ·⊑· (ν⊑ν (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
              (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
           ℕ⊑★ νL-ty νR-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

------------------------------------------------------------------------
-- P1, after both TyBetas
------------------------------------------------------------------------

Θ₀ : Boundary
Θ₀ = bind 0 0 ∷ []

L1′ R1′ : Term
L1′ = (idX ⟪ Θ₀ , revX ⟫) · $ 5
R1′ = (idX ⟪ Θ₀ , revX ⟫) · 5⟨ℕ!⟩

L1′-state : head (drop 1 (evalTerms 10 L1-⊢)) ≡ just L1′
L1′-state = refl

R1′-state : head (drop 1 (evalTerms 11 R1-⊢)) ≡ just R1′
R1′-state = refl

ΔL ΔR ΔLᵢ ΔRᵢ : Ctxᵗ
ΔL = allocate `ℕ empty
ΔR = allocate ★ empty
ΔLᵢ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])
ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])

-- the exterior world: no names; the two store rep. vars paired (ϱᵍ)
W₁ : World ΔL ΔR
W₁ = world [] []↪ []↪ ((0 , 0) ∷ []) []

-- the interior world: X both-sided at X⊑X
Wᵢ₁ : World ΔLᵢ ΔRᵢ
Wᵢ₁ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

int₀ : ∀ {R} → allocate R empty ⊢ⁱ Θ₀ ⇒ ((bindR R ∷ []) ∣ (0 ∷ []))
int₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

Wᵢ₁-int : Interior W₁ Θ₀ Θ₀ Wᵢ₁
Wᵢ₁-int = record
  { int-left   = int₀
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

bL bR : Term
bL = idX ⟪ Θ₀ , revX ⟫
bR = bL

bL-⊢ : ΔL ∣ [] ⊢ bL ⦂ `ℕ ⇒ `ℕ
bL-⊢ = tc

bR-⊢ : ΔR ∣ [] ⊢ bR ⦂ ★ ⇒ ★
bR-⊢ = tc

bL-ty : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
bL-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv bL-⊢)))

bR-ty : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bR-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv bR-⊢)))

p1-tybeta : W₁ ∣ [] ⊢ L1′ ⊑ R1′ ∶ ℕ⊑★
p1-tybeta =
  ·⊑· (⟪⟫⊑⟪⟫ Wᵢ₁-int (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bL-ty bR-ty
              (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

Wᵢ₁-wf : WfWorld Wᵢ₁
Wᵢ₁-wf = wf-world (both (inj₁ here⇔) joint[]) agree uniq
  where
  agree : ∀ {α β} → Paired Wᵢ₁ α β → Agree Wᵢ₁ α β
  agree (inj₁ here⇔) =
    rep-rep r-here r-here same-ℕ same-★ ℕ⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())
  uniq : ∀ {α α′ β} → Paired Wᵢ₁ α β → Paired Wᵢ₁ α′ β → α ≡ α′
  uniq (inj₁ here⇔) (inj₁ here⇔) = refl
  uniq (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniq (inj₁ (there⇔ ())) _
  uniq (inj₂ ()) _
  uniq (inj₁ here⇔) (inj₂ ())

------------------------------------------------------------------------
-- P2, after the left's TyBeta (a left-only boundary)
------------------------------------------------------------------------

R2-state : R2 ≡ (ƛ ★ ∙ ` 0) · 5⟨ℕ!⟩
R2-state = refl

W₂ : World ΔL empty
W₂ = world [] []↪ []↪ [] []

-- X is left-only, so its mark is X⊑★
Wᵢ₂ : World ΔLᵢ empty
Wᵢ₂ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] []

Wᵢ₂-int : Interior W₂ Θ₀ [] Wᵢ₂
Wᵢ₂-int = record
  { int-left   = int₀
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { _ (_ , ()) _ _ }
  ; join-fresh = λ { _ () _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

p2-tybeta : W₂ ∣ [] ⊢ L1′ ⊑ R2 ∶ ℕ⊑★
p2-tybeta =
  ·⊑· (⟪⟫⊑ Wᵢ₂-int (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) bL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

------------------------------------------------------------------------
-- P3, after the right's Inst, TyBeta and Beta, before the left's
-- TyBeta: ∀⊑⟪+⟫ relates the left Λ to the right's Inst boundary
------------------------------------------------------------------------

R3′ : Term
R3′ = ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ ★ ⟩) · 5⟨ℕ!⟩

L3′-state : head (drop 1 (evalTerms 11 L3-⊢)) ≡ just L1
L3′-state = refl

R3′-state : head (drop 3 (evalTerms 16 R3-⊢)) ≡ just R3′
R3′-state = refl

W₃ : World empty ΔR
W₃ = world [] []↪ []↪ [] []

-- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★)
∀id⊑★ : ∀X⇒X ⊑ᵂ⟨ W₃ ⟩ (★ ⇒ ★)
∀id⊑★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

ΛidX-⊢ : empty ∣ [] ⊢ Λ idX ⦂ ∀X⇒X
ΛidX-⊢ = tc

p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
                         (inst-Λ (V-simple S-ƛ))
                         (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                         r-here bR-ty ∀id⊑★)
                 (cast-ty (⊢fun (⊢id wf-★) (⊢id wf-★)) refl) ∀id⊑★)
          ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

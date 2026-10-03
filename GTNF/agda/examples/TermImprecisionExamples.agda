module examples.TermImprecisionExamples where

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
--                 ⊑cast, ⊑⟪⟫ with one opening (design.md D26; the
--                 left Λ's abstract rep. var paired lexically with
--                 αᴿ:=★; `inst-Λ`)
--       p6-init-ν P6's initial ν pair, with `−X → id(ℕ)` related to
--                 `−X → id(★)` in the ν conversion world
--       p6-tybeta P6 right after both TyBetas: the same conversion
--                 comparison in the matched boundaries' conversion
--                 context
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
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms)
open import Imprecision
open import ImprecisionWorld
open import proof.ImprecisionWorld using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])
open import ConversionImprecision
open import TermImprecision
open import examples.ImprecisionExamples
  using (L1; R1; L1-⊢; R1-⊢; R2; L3-⊢; R3-⊢;
         L6; R6; L6-⊢; R6-⊢)
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

ConvCtx₀ : Ty → Ctxᵗ
ConvCtx₀ R = (bindR R ∷ []) ∣ (0 ∷ [])

conv₀ : ∀ {R} → allocate R empty ⊢ᶜ Θ₀ ⇒ ConvCtx₀ R
conv₀ = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

-- The ν-conversion world has one both-sided name and the ν-bound pair
-- in ϱˡ, not ϱᵍ.
Wν : ∀ {R R′} → World (ConvCtx₀ R) (ConvCtx₀ R′)
Wν = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ [])

Wν-conv : ∀ {R R′}
  → ConversionInterior (underν² R R′ ∅ʷ) Θ₀ Θ₀ Wν
Wν-conv = record
  { conv-left       = conv₀
  ; conv-right      = conv₀
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

revX⊑revX : ∀ {Δ Δ′} {W : World Δ Δ′}
  → Joins W 0 0 → ConvImp W revX revX
revX⊑revX j =
  conv-tail⊑tail
    (conv-mid⊑mid
      (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                 (conv-unseal⊑unseal j)))

νLR-conv : NuConversionImp ∅ʷ νL-ty νR-ty
νLR-conv = Wν , Wν-conv , revX⊑revX refl

p1-init : ∅ʷ ∣ [] ⊢ L1 ⊑ R1 ∶ ℕ⊑★
p1-init =
  ·⊑· (ν⊑ν (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
              (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
           ℕ⊑★ νL-ty νR-ty νLR-conv (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

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

Wᵢ₁-conv : ConversionInterior W₁ Θ₀ Θ₀ Wᵢ₁
Wᵢ₁-conv = record
  { conv-left       = conv₀
  ; conv-right      = conv₀
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
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

bLR-conv : BdyConversionImp W₁ bL-ty bR-ty
bLR-conv = Wᵢ₁ , Wᵢ₁-conv , revX⊑revX refl

Wᵢ₁-wf : WfWorld Wᵢ₁
Wᵢ₁-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 Wᵢ₁ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₁ ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wᵢ₁ α β → Agree Wᵢ₁ α β
  agree (inj₁ here⇔) =
    rep-rep r-here r-here (ι⊑★ base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

p1-tybeta : W₁ ∣ [] ⊢ L1′ ⊑ R1′ ∶ ℕ⊑★
p1-tybeta =
  ·⊑· (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
              (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bL-ty bR-ty bLR-conv
              (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

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

Wᵢ₂-wf : WfWorld Wᵢ₂
Wᵢ₂-wf = wf-world (left-only joint[]) agree
  (namedᴸ-≤1 Wᵢ₂ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₂ ≤1-[])
  where
  agree : ∀ {α β} → Paired Wᵢ₂ α β → Agree Wᵢ₂ α β
  agree (inj₁ ())
  agree (inj₂ ())

p2-tybeta : W₂ ∣ [] ⊢ L1′ ⊑ R2 ∶ ℕ⊑★
p2-tybeta =
  ·⊑· (⟪⟫⊑ Wᵢ₂-int Wᵢ₂-wf
              (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) bL-ty
              (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

------------------------------------------------------------------------
-- P3, after the right's Inst, TyBeta and Beta, before the left's
-- TyBeta: ⊑⟪⟫ with one opening (D26; before D26, ∀⊑⟪+⟫) relates the
-- left Λ to the right's Inst boundary
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

-- the Inst boundary `+X^α` (α:=★ at rep. var 0) alone: X is a
-- right-only name, with the mark m chosen here (D11)
int-ro₃ : ∀ {m} → Interior W₃ [] Θ₀ (W₃ ⊕ʳ m ^ 0)
int-ro₃ = record
  { int-left   = interior changes[]
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

-- the opened world: the left Λ's abstract rep. var paired lexically
-- with αᴿ:=★ (`abst-★`), the shared name at X⊑X
W₃⁺-wf : WfWorld (W₃ ⊕⁺ X⊑X ^ 0)
W₃⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree
  (namedᴸ-≤1 (W₃ ⊕⁺ X⊑X ^ 0) ≤1-∷[]) (namedᴿ-≤1 (W₃ ⊕⁺ X⊑X ^ 0) ≤1-∷[])
  where
  agree : ∀ {α β} → Paired (W₃ ⊕⁺ X⊑X ^ 0) α β
    → Agree (W₃ ⊕⁺ X⊑X ^ 0) α β
  agree (inj₁ ())
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

-- one opening of the left `ΛX. λx:X. x` at the boundary's name 0
-- (`inst-Λ`)
openΛidX : Opens Θ₀ (W₃ ⊕ʳ X⊑X ^ 0) (Λ idX) ∀X⇒X (W₃ ⊕⁺ X⊑X ^ 0) idX
  (` 0 ⇒ ` 0)
openΛidX =
  open-∀ nv-⇒ (∈-⇒ˡ ∈-var) (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
    (inst-Λ (V-simple S-ƛ)) refl (open-⊕ r-here) open-none

p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst =
  ·⊑· (ν⊑ (⊑cast (⊑⟪⟫ int-ro₃ openΛidX W₃⁺-wf
                         (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                         bR-ty ∀id⊑★)
                 (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl) ∀id⊑★)
          ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

------------------------------------------------------------------------
-- P6, the initial ν pair and the state after both TyBetas
------------------------------------------------------------------------

∀6L ∀6R : Ty
∀6L = `∀ (` 0 ⇒ `ℕ)
∀6R = `∀ (` 0 ⇒ ★)

∀6L⊑∀6R : ∀6L ⊑ᵂ⟨ ∅ʷ ⟩ ∀6R
∀6L⊑∀6R = ∀⊑∀ (⇒⊑⇒ X⊑X ℕ⊑★)

c6L c6R : Conv
c6L = reveal 0 (` 0 ⇒ `ℕ)
c6R = reveal 0 (` 0 ⇒ ★)

ν6L ν6R : Term
ν6L = ν `𝔹 · ` 0 ⟨ c6L ⟩
ν6R = ν `𝔹 · ` 0 ⟨ c6R ⟩

ν6L-⊢ : empty ∣ ∀6L ∷ [] ⊢ ν6L ⦂ `𝔹 ⇒ `ℕ
ν6L-⊢ = tc

ν6R-⊢ : empty ∣ ∀6R ∷ [] ⊢ ν6R ⦂ `𝔹 ⇒ ★
ν6R-⊢ = tc

ν6L-ty : NuTy empty `𝔹 (` 0 ⇒ `ℕ) c6L (`𝔹 ⇒ `ℕ)
ν6L-ty = proj₂ (proj₂ (ν-inv ν6L-⊢))

ν6R-ty : NuTy empty `𝔹 (` 0 ⇒ ★) c6R (`𝔹 ⇒ ★)
ν6R-ty = proj₂ (proj₂ (ν-inv ν6R-⊢))

c6⊑ : ∀ {Δ Δ′} {W : World Δ Δ′}
  → Joins W 0 0 → ConvImp W c6L c6R
c6⊑ j =
  conv-tail⊑tail
    (conv-mid⊑mid
      (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                 (conv-tail⊑tail
                   (conv-mid⊑mid (conv-id⊑id ℕ⊑★)))))

ν6-conv : NuConversionImp ∅ʷ ν6L-ty ν6R-ty
ν6-conv = Wν , Wν-conv , c6⊑ refl

p6-init-ν : ∅ʷ ∣ ctx-imp ∀6L ∀6R ∀6L⊑∀6R ∷ []
  ⊢ ν6L ⊑ ν6R ∶ ⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★
p6-init-ν =
  ν⊑ν (x⊑x Zʷ) (ι⊑ι base-𝔹) ν6L-ty ν6R-ty ν6-conv
       (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★)

Δ6 Δ6ᵢ : Ctxᵗ
Δ6 = allocate `𝔹 empty
Δ6ᵢ = ConvCtx₀ `𝔹

W₆ : World Δ6 Δ6
W₆ = world [] []↪ []↪ ((0 , 0) ∷ []) []

Wᵢ₆ : World Δ6ᵢ Δ6ᵢ
Wᵢ₆ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

int₆ : Δ6 ⊢ⁱ Θ₀ ⇒ Δ6ᵢ
int₆ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

Wᵢ₆-int : Interior W₆ Θ₀ Θ₀ Wᵢ₆
Wᵢ₆-int = record
  { int-left   = int₆
  ; int-right  = int₆
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Wᵢ₆-wf : WfWorld Wᵢ₆
Wᵢ₆-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 Wᵢ₆ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₆ ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wᵢ₆ α β → Agree Wᵢ₆ α β
  agree (inj₁ here⇔) =
    rep-rep r-here r-here (ι⊑ι base-𝔹)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wᵢ₆-conv : ConversionInterior W₆ Θ₀ Θ₀ Wᵢ₆
Wᵢ₆-conv = record
  { conv-left       = conv₀
  ; conv-right      = conv₀
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

body6L body6R : Term
body6L = ƛ (` 0) ∙ $ 7
body6R = body6L ⟨ X∼X ∷ [] ∣ idᵖ (` 0) ↦ᵖ (`ℕ !) ⟩

b6L b6R : Term
b6L = body6L ⟪ Θ₀ , c6L ⟫
b6R = body6R ⟪ Θ₀ , c6R ⟫

L6′ R6′ : Term
L6′ = b6L · `true
R6′ = b6R · `true

L6′-state : head (drop 2 (evalTerms 10 L6-⊢)) ≡ just L6′
L6′-state = refl

R6′-state : head (drop 2 (evalTerms 13 R6-⊢)) ≡ just R6′
R6′-state = refl

body6R-⊢ : Δ6ᵢ ∣ [] ⊢ body6R ⦂ ` 0 ⇒ ★
body6R-⊢ = tc

body6R-ty : CastTy Δ6ᵢ (X∼X ∷ []) (idᵖ (` 0) ↦ᵖ (`ℕ !))
                         (` 0 ⇒ `ℕ) (` 0 ⇒ ★)
body6R-ty = proj₂ (proj₂ (cast-inv body6R-⊢))

b6L-⊢ : Δ6 ∣ [] ⊢ b6L ⦂ `𝔹 ⇒ `ℕ
b6L-⊢ = tc

b6R-⊢ : Δ6 ∣ [] ⊢ b6R ⦂ `𝔹 ⇒ ★
b6R-⊢ = tc

b6L-ty : BdyTy Δ6 Θ₀ Δ6ᵢ (` 0 ⇒ `ℕ) c6L (`𝔹 ⇒ `ℕ)
b6L-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv b6L-⊢)))

b6R-ty : BdyTy Δ6 Θ₀ Δ6ᵢ (` 0 ⇒ ★) c6R (`𝔹 ⇒ ★)
b6R-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv b6R-⊢)))

b6-conv : BdyConversionImp W₆ b6L-ty b6R-ty
b6-conv = Wᵢ₆ , Wᵢ₆-conv , c6⊑ refl

p6-tybeta : W₆ ∣ [] ⊢ L6′ ⊑ R6′ ∶ ℕ⊑★
p6-tybeta =
  ·⊑·
    (⟪⟫⊑⟪⟫ Wᵢ₆-int Wᵢ₆-wf
      (⊑cast
        (ƛ⊑ƛ {pA = X⊑X} {pB = ι⊑ι base-ℕ}
          tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
        body6R-ty (⇒⊑⇒ X⊑X ℕ⊑★))
      b6L-ty b6R-ty b6-conv (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★))
    (κ⊑κ lit-true (ι⊑ι base-𝔹))

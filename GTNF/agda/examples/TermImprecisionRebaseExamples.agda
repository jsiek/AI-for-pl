module examples.TermImprecisionRebaseExamples where

-- File Charter:
--   * DERIVATIONS OF `W ∣ γ ⊢ M ⊑ M′ ∶ p` (TermImprecision) AT THE
--     PLACES WHERE papers/cambridge26.lagda.md REBASES ITS STORE
--     NARROWING with (split) or (extend), on the GTNF pairs of
--     CambridgeExamples, plus each pair's initial block.  Block names
--     and schedules are those of GTNF/notes/cambridge-imprecision-check
--     (-v2).md; the correspondence is GTNF/notes/rebasing-in-gtnf.md.
--       c12-b0, c12-x0, c12-b1   C12 (Ex 12): B0; the right-led (0,2)
--                                block (ν⊑ν around ∀⊑⟪+⟫); B1, where
--                                αᴸ has two right partners (D13)
--       c13-b1, c14-b1           C13/C14 B1 (Ex 13/14): two and three
--                                right partners (D13)
--       cg-b0, cg-x0             Cg (Ex 1/20): B0; the right-led block,
--                                ∀⊑⟪+⟫ at mark X⊑★ (D14)
--       c2-b0, c2-x0             C2 (Ex 2/21): B0; the right-led block,
--                                ∀⊑⟪+⟫ on a gen-cast ∀-value (D14)
--       c2-b6, c2-b7             C2 B6/B7: the multi-entry boundary
--                                (−X, +X) ∥ (−X, +X) with its conversion
--                                premise (D15, D17)
--       ch-b0, ch-x0, ch-b1      Ch (Ex 4/11): B0 (Λ⊑Λ, lexical pair);
--                                the right-led block (= p3-inst, lexical
--                                pair under ∀⊑⟪+⟫, D16); B1 (global pair)
--     Every state that is not a source program is pinned to its
--     `evalTerms` state by `refl` (`*-state`).
--   * TYPING SIDE PREMISES come from `tc` on the subterms, read back by
--     TermImprecision's inversions (`⟪⟫-inv`, `cast-inv`, `ν-inv`).
--   * WELL-FORMEDNESS (`WfWorld`) is proved for every world with a D13
--     non-injective pairing (C12 B1: W₁₂-wf, W₁₂²-wf, W₁₂ᴸ-wf, W₁₂ˣ-wf;
--     C14 B1: W₁₄-wf, W₁₄²-wf, W₁₄ᴸ-wf) and every world with a lexical
--     pair (ΛΛ-wf; Wg⁺-wf, Wg⁻-wf; W2⁺-wf, W2⁻-wf, which is also
--     ch-x0's premise world).  C2 B6/B7 and Ch B1 use
--     TermImprecisionExamples' Wᵢ₁ (Wᵢ₁-wf).
--   * NO RULE WAS CHANGED: every block derives with TermImprecision as
--     it stands.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; head; drop)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

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
open import ConversionImprecision
open import TermImprecision
open import examples.CambridgeExamples
open import TermSubst using (crossΛᴹ)
open import Reduction using (inst-Λ; inst-gen)
open import examples.TermImprecisionExamples
  using (idX; revX; ℕ⊑★; five⊑; Θ₀; L1′; ΔL; ΔR; ΔLᵢ; ΔRᵢ;
         W₁; Wᵢ₁; Wᵢ₁-int; Wᵢ₁-conv; Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv; revX⊑revX;
         νL-ty; Wν; Wν-conv; W₃; R3′; p3-inst)
open import examples.ImprecisionExamples using (L1)

------------------------------------------------------------------------
-- Pieces shared by the blocks
------------------------------------------------------------------------

-- `id(★) → id(★)` as a coercion and as a conversion
id★↦ : Coercion
id★↦ = idᵖ ★ ↦ᵖ idᵖ ★

id★→ : Conv
id★→ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

-- the gen wrapper's coercion `X! → X?ℓ0`
tagX↦ : Coercion
tagX↦ = (` 0) ! ↦ᵖ (` 0) ？ 0

X⇒X⊑★⇒★ : ∀ {Δ Δ′} {W : World Δ Δ′} → μʷ W ∋ˡ emb (ηᴸʷ W) 0 := X⊑★
  → (` 0 ⇒ ` 0) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
X⇒X⊑★⇒★ m = ⇒⊑⇒ (X⊑★ m) (X⊑★ m)

ℕ⇒ℕ : ∀ {Δ Δ′} (W : World Δ Δ′) → (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ `ℕ)
ℕ⇒ℕ W = ⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- D13 worlds: one left name c against a chain of right boundaries
------------------------------------------------------------------------

-- C12–C14 B1.  The left is `[+X^αᴸ] (λx:X. x) ⟨−X → +X⟩` at
-- ΔL = αᴸ:=ℕ.  The right nests `[+Y^β] ([−Y^β] … ⟨…⟩)⟨Y! → Y?ℓ0⟩` around
-- the Inst boundary `[+X^αᴿ] (λx:X. x)`.  Every right `+_^β` names a
-- right rep. var paired with αᴸ (D13), so c rejoins at each one; every
-- right `−_^β` leaves c left-only at c⊑★ (D15).  The store pairing ϱ is
-- global and the same in every world of the derivation.

module _ {Ξ′ : RepCtx} {ϱ : RepRel} where

  -- outside: no names
  Wc⁰ : World ΔL (Ξ′ ∣ [])
  Wc⁰ = world [] []↪ []↪ ϱ []

  -- c both-sided, its right name at rep. var β
  Wc² : (β : RVar) → World ΔLᵢ (Ξ′ ∣ (β ∷ []))
  Wc² β = world (X⊑★ ∷ []) (keep []↪) (keep []↪) ϱ []

  -- c left-only
  Wcᴸ : World ΔLᵢ (Ξ′ ∣ [])
  Wcᴸ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) ϱ []

  -- the matched TyBeta boundaries [+X^αᴸ] ∥ [+Y^0]
  Wc-bind² : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0 → Interior Wc⁰ Θ₀ Θ₀ (Wc² 0)
  Wc-bind² v p = record
    { int-left   = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; int-right  = interior (changes∷ changes[]
                     (step-bind v fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  Wc-bind²-conv : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0
    → ConversionInterior Wc⁰ Θ₀ Θ₀ (Wc² 0)
  Wc-bind²-conv v p = record
    { conv-left       =
        conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-right      = conversion (conv-bind v conv[] fresh[] ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  -- a right-only −Y^β: c goes left-only, keeping c⊑★
  Wc-unbindᴿ : ∀ {β} → Ξ′ ∋ʳ β → Interior (Wc² β) [] (unbind 0 β ∷ []) Wcᴸ
  Wc-unbindᴿ v = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind v del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  -- a right-only +X^β: c rejoins β's unique left partner αᴸ (D13)
  Wc-bindᴿ : ∀ {β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → Interior Wcᴸ [] (bind 0 β ∷ []) (Wc² β)
  Wc-bindᴿ v p = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[] (step-bind v fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

-- the types at these worlds
c⊑★ᴸ : ∀ Ξ′ ϱ → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wcᴸ {Ξ′} {ϱ} ⟩ (★ ⇒ ★)
c⊑★ᴸ Ξ′ ϱ = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

c⊑★² : ∀ Ξ′ ϱ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} β ⟩ (★ ⇒ ★)
c⊑★² Ξ′ ϱ β = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

c⊑c² : ∀ Ξ′ ϱ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} β ⟩ (` 0 ⇒ ` 0)
c⊑c² Ξ′ ϱ β = ⇒⊑⇒ (X⊑X {X = 0}) (X⊑X {X = 0})

-- the core `[+X^αᴿ] (λx:X. x) ⟨−X → +X⟩` against λx:X. x, and one
-- gen layer `[+Y^β] ([−Y^β] M ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩` around a
-- right term M, at the right context Ξ′ (the typing bundles are passed
-- in, read off `tc` at each instance)
core⊑ : ∀ {Ξ′ ϱ β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
  → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ idX ⟪ bind 0 β ∷ [] , revX ⟫
      ∶ c⊑★ᴸ Ξ′ ϱ
core⊑ {Ξ′} {ϱ} v p b =
  ⊑⟪⟫ (Wc-bindᴿ v p)
    (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
    b (c⊑★ᴸ Ξ′ ϱ)

-- the gen layer's right term, around M
genLayer : RVar → Term → Term
genLayer β M =
  (((M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩)
    ⟪ bind 0 β ∷ [] , revX ⟫

layer⊑ : ∀ {Ξ′ ϱ β M}
  → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
  → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ
  → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  → BdyTy (Ξ′ ∣ (β ∷ [])) (unbind 0 β ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
  → CastTy (Ξ′ ∣ (β ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ genLayer β M
      ∶ c⊑★ᴸ Ξ′ ϱ
layer⊑ {Ξ′} {ϱ} {β} v p M⊑ cᵢ bᵤ cₜ b =
  ⊑⟪⟫ (Wc-bindᴿ v p)
    (⊑cast {A = ` 0 ⇒ ` 0}
      (⊑⟪⟫ (Wc-unbindᴿ v) (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ)) bᵤ (c⊑★² Ξ′ ϱ β))
      cₜ (c⊑c² Ξ′ ϱ β))
    b (c⊑★ᴸ Ξ′ ϱ)

-- the outermost gen layer, matched with the left's TyBeta boundary
outer⊑ : ∀ {Ξ′ ϱ M B′}
  → (v : Ξ′ ∋ʳ 0) → (p : ϱ ∋ᵨ 0 ⇔ 0)
  → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ
  → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  → BdyTy (Ξ′ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
  → CastTy (Ξ′ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  → (b : BdyTy (Ξ′ ∣ []) Θ₀ (Ξ′ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX B′)
  → BdyConversionImp (Wc⁰ {Ξ′} {ϱ}) bL-ty b
  → (q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ Wc⁰ {Ξ′} {ϱ} ⟩ B′)
  → Wc⁰ {Ξ′} {ϱ} ∣ [] ⊢ idX ⟪ Θ₀ , revX ⟫ ⊑ genLayer 0 M ∶ q
outer⊑ {Ξ′} {ϱ} v p M⊑ cᵢ bᵤ cₜ b bc q =
  ⟪⟫⊑⟪⟫ (Wc-bind² v p)
    (⊑cast {A = ` 0 ⇒ ` 0}
      (⊑⟪⟫ (Wc-unbindᴿ v) (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ)) bᵤ (c⊑★² Ξ′ ϱ 0))
      cₜ (c⊑c² Ξ′ ϱ 0))
    bL-ty b bc q

------------------------------------------------------------------------
-- C12 B1: one left rep. var, two right partners (D13)
------------------------------------------------------------------------

-- C12's state 3: the right has run Inst, TyBeta (αᴿ:=★) and the source
-- TyBeta (βᴿ:=ℕ); βᴿ is rep. var 0, αᴿ is rep. var 1
Ξ₁₂ : RepCtx
Ξ₁₂ = bindR `ℕ ∷ bindR ★ ∷ []

-- αᴸ (0) is paired with both βᴿ (0) and αᴿ (1)
ϱ₁₂ : RepRel
ϱ₁₂ = (0 , 0) ∷ (0 , 1) ∷ []

B12x B12 : Term
B12x = idX ⟪ bind 0 1 ∷ [] , revX ⟫
B12  = genLayer 0 B12x

C12-R₃ : Term
C12-R₃ = B12 · $ 5

C12-L₁-state : head (drop 1 (evalTerms 10 C12-L-⊢)) ≡ just L1′
C12-L₁-state = refl

C12-R₃-state : head (drop 3 (evalTerms 24 C12-R-⊢)) ≡ just C12-R₃
C12-R₃-state = refl

-- the right contexts: outside, and with the one name at rep. var β
ΔR₁₂ : Ctxᵗ
ΔR₁₂ = Ξ₁₂ ∣ []

ΔR₁₂^ : RVar → Ctxᵗ
ΔR₁₂^ β = Ξ₁₂ ∣ (β ∷ [])

-- typing side premises, read off `tc`
B12-ty : BdyTy ΔR₁₂ Θ₀ (ΔR₁₂^ 0) (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
B12-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂} {M = B12}))))

B12x-ty : BdyTy ΔR₁₂ (bind 0 1 ∷ []) (ΔR₁₂^ 1) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
B12x-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂} {M = B12x}))))

id★↦-ty : ∀ {Ξ} → CastTy (Ξ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

-- one gen layer's two inner pieces
unbTerm tagTerm : RVar → Term → Term
unbTerm β M = (M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫
tagTerm β M = unbTerm β M ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

B12ᵤ-ty : BdyTy (ΔR₁₂^ 0) (unbind 0 0 ∷ []) ΔR₁₂ (★ ⇒ ★) id★→ (★ ⇒ ★)
B12ᵤ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂^ 0} {M = unbTerm 0 B12x}))))

B12ₜ-ty : CastTy (ΔR₁₂^ 0) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
B12ₜ-ty = proj₂ (proj₂
  (cast-inv {Γ = []} (tc {Δ = ΔR₁₂^ 0} {M = tagTerm 0 B12x})))

-- the worlds of the derivation
W₁₂ : World ΔL ΔR₁₂
W₁₂ = Wc⁰ {Ξ₁₂} {ϱ₁₂}

c12-b1 : W₁₂ ∣ [] ⊢ L1′ ⊑ C12-R₃ ∶ ι⊑ι base-ℕ
c12-b1 =
  ·⊑·
    (outer⊑ (_ , here) here⇔
      (core⊑ (_ , there here) (there⇔ here⇔) B12x-ty)
      id★↦-ty B12ᵤ-ty B12ₜ-ty B12-ty
      (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl) (ℕ⇒ℕ W₁₂))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- WfWorld for the four worlds of c12-b1: outside; c both-sided naming
-- (αᴸ, βᴿ); c left-only; c both-sided naming (αᴸ, αᴿ).  Each has
-- ϱᵍ = ϱ₁₂ and ϱˡ = ∅.
left0-ϱ₁₂ : ∀ {α β} → ϱ₁₂ ∋ᵨ α ⇔ β → α ≡ 0
left0-ϱ₁₂ here⇔ = refl
left0-ϱ₁₂ (there⇔ here⇔) = refl
left0-ϱ₁₂ (there⇔ (there⇔ ()))

module Wf₁₂ {nsL nsR : TyCtx} (μ : ImpEnv)
    (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

  W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₂ ∣ nsR)
  W = world μ η η′ ϱ₁₂ []

  -- both pairs agree: ℕ ⊑ ℕ and ℕ ⊑ ★
  agree : ∀ {α β} → Paired W α β → Agree W α β
  agree (inj₁ here⇔) = rep-rep r-here r-here same-ℕ same-ℕ (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ here⇔)) =
    rep-rep r-here (r-there r-here) same-ℕ same-★ ℕ⊑★
  agree (inj₁ (there⇔ (there⇔ ())))
  agree (inj₂ ())

  -- D13: many-to-one toward the left, so each right rep. var has one
  -- left partner
  uniq : ∀ {α α′ β} → Paired W α β → Paired W α′ β → α ≡ α′
  uniq (inj₁ p) (inj₁ p′) = trans (left0-ϱ₁₂ p) (sym (left0-ϱ₁₂ p′))
  uniq (inj₁ p) (inj₂ ())
  uniq (inj₂ ()) _

W₁₂-wf : WfWorld W₁₂
W₁₂-wf = wf-world joint[] agree uniq
  where open Wf₁₂ [] []↪ []↪

W₁₂²-wf : WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} 0)
W₁₂²-wf = wf-world (both (inj₁ here⇔) joint[]) agree uniq
  where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (keep []↪)

W₁₂ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₂} {ϱ₁₂})
W₁₂ᴸ-wf = wf-world (left-only joint[]) agree uniq
  where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (skip []↪)

W₁₂ˣ-wf : WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} 1)
W₁₂ˣ-wf = wf-world (both (inj₁ (there⇔ here⇔)) joint[]) agree uniq
  where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (keep []↪)

------------------------------------------------------------------------
-- Shared pieces for the right-led blocks
------------------------------------------------------------------------

-- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★), in any world
∀id⊑★ : ∀ {Δ Δ′} (W : World Δ Δ′) → `∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
∀id⊑★ W = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

∀id⊑∀id : ∀ {Δ Δ′} (W : World Δ Δ′)
  → `∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ W ⟩ `∀ (` 0 ⇒ ` 0)
∀id⊑∀id W = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → (★ ⇒ ★) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
★⇒★ W = ⇒⊑⇒ ★⊑★ ★⊑★

ℕ⇒ℕ⊑★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
ℕ⇒ℕ⊑★⇒★ W = ⇒⊑⇒ ℕ⊑★ ℕ⊑★

id★→⊑id★→ : ∀ {Δ Δ′} {W : World Δ Δ′} → ConvImp W id★→ id★→
id★→⊑id★→ =
  conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
  where
  i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★))

-- `[−X^α] (λx:★. x) ⟨id(★) → id(★)⟩`: the gen value's crossed body, and
-- the gen wrapper `(…)⟨X! → X?ℓ0⟩^[X:★∼X]` over it (on the left this is
-- `inst_X` of the gen value, `inst-gen`; on the right it is what the
-- right's TyBeta left inside its boundary)
I★⁻ I★gen : Term
I★⁻ = I★ ⟪ unbind 0 0 ∷ [] , id★→ ⟫
I★gen = I★⁻ ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

I★⁻-crossed : crossΛᴹ I★ (srcᵖ genI) ≡ I★⁻
I★⁻-crossed = refl

-- the right's state after Inst and TyBeta (αᴿ:=★), Cg-R = C2-R state 2
Bg Cg-R₂ : Term
Bg = I★gen ⟪ Θ₀ , revX ⟫
Cg-R₂ = (Bg ⟨ [] ∣ id★↦ ⟩) · dyn 5

Cg-R₂-state : head (drop 2 (evalTerms 21 Cg-R-⊢)) ≡ just Cg-R₂
Cg-R₂-state = refl

-- the right contexts: the exterior (αᴿ:=★ at rep. var 0), inside the
-- Inst boundary `+X^αᴿ`, inside the gen value's `−X^αᴿ`
ΔRₓ : Ctxᵗ
ΔRₓ = reps ΔR ∣ (0 ∷ [])

Bg-ty : BdyTy ΔR (bind 0 0 ∷ []) ΔRₓ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
Bg-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Bg}))))

I★⁻ᴿ-ty : BdyTy ΔRₓ (unbind 0 0 ∷ []) ΔR (★ ⇒ ★) id★→ (★ ⇒ ★)
I★⁻ᴿ-ty =
  proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★⁻}))))

tagᴿ-ty : CastTy ΔRₓ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagᴿ-ty =
  proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★gen})))

id★↦ᴿ-ty : CastTy ΔR [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦ᴿ-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

ΛidX-⊢ : empty ∣ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
ΛidX-⊢ = tc

------------------------------------------------------------------------
-- Cg's right-led block X0 (D14: ∀⊑⟪+⟫ at mark X⊑★)
------------------------------------------------------------------------

-- the premise world of ∀⊑⟪+⟫: the left Λ's abstract rep. var paired
-- LEXICALLY with αᴿ:=★; the shared name at X⊑★ (chosen here, D11)
Wg⁺ : World (underΛ empty) ΔRₓ
Wg⁺ = W₃ ⊕⁺ X⊑★ ^ 0

-- inside the right's −X^αᴿ: X is left-only, X⊑★
Wg⁻ : World (underΛ empty) ΔR
Wg⁻ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] ((0 , 0) ∷ [])

Wg⁻-int : Interior Wg⁺ [] (unbind 0 0 ∷ []) Wg⁻
Wg⁻-int = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-unbind (_ , here) del-here fresh[]))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { _ (_ , ()) _ _ }
  ; join-fresh = λ { _ () _ }
  ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
cg-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (∀⊑⟪+⟫ {m = X⊑★} (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
          (inst-Λ (V-simple S-ƛ))
          (⊑cast
            (⊑⟪⟫ Wg⁻-int (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
                 I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
            tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- WfWorld for the worlds of the lexical pair (aᴸ_ΛY, αᴿ:=★): the left
-- member abstract, the right member at ★ (`abst-★`)
module WfΛ★ {nsL nsR : TyCtx} (μ : ImpEnv)
    (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

  W : World ((abstR ∷ []) ∣ nsL) ((bindR ★ ∷ []) ∣ nsR)
  W = world μ η η′ [] ((0 , 0) ∷ [])

  agree : ∀ {α β} → Paired W α β → Agree W α β
  agree (inj₁ ())
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

  uniq : ∀ {α α′ β} → Paired W α β → Paired W α′ β → α ≡ α′
  uniq (inj₁ ()) _
  uniq (inj₂ here⇔) (inj₁ ())
  uniq (inj₂ here⇔) (inj₂ here⇔) = refl
  uniq (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniq (inj₂ (there⇔ ())) _

Wg⁺-wf : WfWorld Wg⁺
Wg⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree uniq
  where open WfΛ★ (X⊑★ ∷ []) (keep []↪) (keep []↪)

Wg⁻-wf : WfWorld Wg⁻
Wg⁻-wf = wf-world (left-only joint[]) agree uniq
  where open WfΛ★ (X⊑★ ∷ []) (keep []↪) (skip []↪)

------------------------------------------------------------------------
-- C2's right-led block X0 (D14: ∀⊑⟪+⟫ with a gen-cast left ∀-value)
------------------------------------------------------------------------

I★genI : Term
I★genI = I★ ⟨ [] ∣ genI ⟩

I★genI-⊢ : empty ∣ [] ⊢ I★genI ⦂ `∀ (` 0 ⇒ ` 0)
I★genI-⊢ = tc

C2-L-ν : Term
C2-L-ν = ν `ℕ · I★genI ⟨ revX ⟩

C2-L-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
C2-L-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C2-L-ν})))

C2-L₀-is : C2-L ≡ C2-L-ν · $ 5
C2-L₀-is = refl

-- the premise world, now at X⊑X (the gen wrappers are matched)
W2⁺ : World (underΛ empty) ΔRₓ
W2⁺ = W₃ ⊕⁺ X⊑X ^ 0

-- inside both −X^α: no names
W2⁻ : World (reps (underΛ empty) ∣ []) ΔR
W2⁻ = world [] []↪ []↪ [] ((0 , 0) ∷ [])

unbind₀-int : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ (unbind 0 0 ∷ [])
  ⇒ ((b ∷ Ξ) ∣ [])
unbind₀-int = interior (changes∷ changes[]
  (step-unbind (_ , here) del-here fresh[]))

unbind₀-conv : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ (unbind 0 0 ∷ [])
  ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
unbind₀-conv = conversion (conv-unbind (_ , here) conv[])

W2⁻-int : Interior W2⁺ (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W2⁻
W2⁻-int = record
  { int-left   = unbind₀-int
  ; int-right  = unbind₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

-- the conversion contexts skip the unbinds: they are the exterior
unbind₀-conv-self : ∀ {b b′ Ξ Ξ′}
    {W : World ((b ∷ Ξ) ∣ (0 ∷ [])) ((b′ ∷ Ξ′) ∣ (0 ∷ []))}
  → ConversionInterior W (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W
unbind₀-conv-self = record
  { conv-left       = unbind₀-conv
  ; conv-right      = unbind₀-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { here here here here → (λ j → j) , (λ j → j)
      ; here here here (there ())
      ; here here (there ()) _
      ; here (there ()) _ _
      ; (there ()) _ _ _
      }
  ; conv-join-fresh = λ
      { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  ; conv-mark-right = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  }

W2⁺-conv : ConversionInterior W2⁺ (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W2⁺
W2⁺-conv = unbind₀-conv-self

I★⁻ᴸ-ty : BdyTy (underΛ empty) (unbind 0 0 ∷ []) (reps (underΛ empty) ∣ [])
  (★ ⇒ ★) id★→ (★ ⇒ ★)
I★⁻ᴸ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = underΛ empty} {M = I★⁻}))))

tagᴸ-ty : CastTy (underΛ empty) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagᴸ-ty =
  proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ empty} {M = I★gen})))

c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
c2-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (∀⊑⟪+⟫ {m = X⊑X} (V-simple (S-cast (V-simple S-ƛ) I-gen)) I★genI-⊢
          (inst-gen (V-simple S-ƛ))
          (cast⊑cast
            (⟪⟫⊑⟪⟫ W2⁻-int (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
              I★⁻ᴸ-ty I★⁻ᴿ-ty (W2⁺ , W2⁺-conv , id★→⊑id★→) (★⇒★ W2⁺))
            tagᴸ-ty tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

W2⁺-wf : WfWorld W2⁺
W2⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree uniq
  where open WfΛ★ (X⊑X ∷ []) (keep []↪) (keep []↪)

W2⁻-wf : WfWorld W2⁻
W2⁻-wf = wf-world joint[] agree uniq
  where open WfΛ★ [] []↪ []↪

------------------------------------------------------------------------
-- C2 B6 and B7 (D15: a multi-entry boundary, with its conversion
-- premise)
------------------------------------------------------------------------

-- the multi-entry scope (−X, +X): head last, so `unbind` acts first
Θ⁻⁺ : Boundary
Θ⁻⁺ = bind 0 0 ∷ unbind 0 0 ∷ []

unb₀ : Boundary
unb₀ = unbind 0 0 ∷ []

-- `[−X^α] m ⟨−X⟩`, for the leaf m = 5 (left) or 5⟨ℕ!⟩ (right)
seal-leaf : Term → Term
seal-leaf m = m ⟪ unb₀ , tail (seal 0) ⟫

tagX untagX : Coercion
tagX   = (` 0) !
untagX = (` 0) ？ 0

C2-B6 C2-B7 : Term → Term
C2-B6 m =
  (((seal-leaf m ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , tail (mid (id ★)) ⟫)
    ⟨ ★∼X ∷ [] ∣ untagX ⟩) ⟪ Θ₀ , unseal 0 ⟫
C2-B7 m =
  (((seal-leaf m ⟪ Θ⁻⁺ , tail (mid (id (` 0))) ⟫) ⟨ X∼★ ∷ [] ∣ tagX ⟩)
    ⟨ ★∼X ∷ [] ∣ untagX ⟩) ⟪ Θ₀ , unseal 0 ⟫

C2-L₆-state : head (drop 6 (evalTerms 16 C2-L-⊢)) ≡ just (C2-B6 ($ 5))
C2-L₆-state = refl

C2-R₉-state : head (drop 9 (evalTerms 21 C2-R-⊢))
  ≡ just (C2-B6 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩)
C2-R₉-state = refl

C2-L₇-state : head (drop 7 (evalTerms 16 C2-L-⊢)) ≡ just (C2-B7 ($ 5))
C2-L₇-state = refl

C2-R₁₀-state : head (drop 10 (evalTerms 21 C2-R-⊢))
  ≡ just (C2-B7 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩)
C2-R₁₀-state = refl

-- the worlds: W₁ outside (ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}), Wᵢ₁ inside the outer
-- boundaries (X both-sided at X⊑X, chosen at B1); the final interior
-- world of (−X, +X) ∥ (−X, +X) is Wᵢ₁ again (X continues, keeps X⊑X);
-- inside the two −X, W₁ again (no names)
Wᵢ₁-unb : Interior Wᵢ₁ unb₀ unb₀ W₁
Wᵢ₁-unb = record
  { int-left   = unbind₀-int
  ; int-right  = unbind₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

Θ⁻⁺-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ Θ⁻⁺ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
Θ⁻⁺-int = interior (changes∷
  (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
  (step-bind (_ , here) fresh[] ins-here))

Θ⁻⁺-conv : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ Θ⁻⁺ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
Θ⁻⁺-conv = conversion (conv-bind-live (_ , here)
  (conv-unbind (_ , here) conv[]) here)

-- D15: X goes away and comes back within the entries; only the final
-- interior world is given, and X keeps its mark
Wᵢ₁-Θ⁻⁺ : Interior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
Wᵢ₁-Θ⁻⁺ = record
  { int-left   = Θ⁻⁺-int
  ; int-right  = Θ⁻⁺-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
      ; (_ , here) (_ , there ()) _ _
      ; (_ , there ()) _ _ _
      }
  ; join-fresh = λ
      { here here (inj₁ ()) ; here here (inj₂ ())
      ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
  }

Wᵢ₁-Θ⁻⁺-conv : ConversionInterior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
Wᵢ₁-Θ⁻⁺-conv = record
  { conv-left       = Θ⁻⁺-conv
  ; conv-right      = Θ⁻⁺-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { here here here here → (λ j → j) , (λ j → j)
      ; here here here (there ())
      ; here here (there ()) _
      ; here (there ()) _ _
      ; (there ()) _ _ _
      }
  ; conv-join-fresh = λ
      { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  ; conv-mark-right = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  }

-- typing side premises
leafᴸ-ty : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
leafᴸ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = seal-leaf ($ 5)}))))

leafᴿ-ty : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
leafᴿ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = seal-leaf (dyn 5)}))))

tag-ty : ∀ {R} → CastTy ((bindR R ∷ []) ∣ (0 ∷ [])) (X∼★ ∷ []) tagX (` 0) ★
tag-ty = cast-ty (⊢tag-var (_ , here) here tag-dyn) refl

untag-ty : ∀ {R} → CastTy ((bindR R ∷ []) ∣ (0 ∷ [])) (★∼X ∷ []) untagX ★ (` 0)
untag-ty = cast-ty (⊢check-var (_ , here) here check-dyn) refl

-- B6's middle boundary `[−X, +X] (…)⟨X!⟩ ⟨id(★)⟩`
mid6 : Term → Term
mid6 m = (seal-leaf m ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , tail (mid (id ★)) ⟫

mid6ᴸ-ty : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ ★ (tail (mid (id ★))) ★
mid6ᴸ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = mid6 ($ 5)}))))

mid6ᴿ-ty : BdyTy ΔRᵢ Θ⁻⁺ ΔRᵢ ★ (tail (mid (id ★))) ★
mid6ᴿ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = mid6 (dyn 5)}))))

-- B7's middle boundary `[−X, +X] (…) ⟨id(X)⟩`
mid7 : Term → Term
mid7 m = seal-leaf m ⟪ Θ⁻⁺ , tail (mid (id (` 0))) ⟫

mid7ᴸ-ty : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0) (tail (mid (id (` 0)))) (` 0)
mid7ᴸ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = mid7 ($ 5)}))))

mid7ᴿ-ty : BdyTy ΔRᵢ Θ⁻⁺ ΔRᵢ (` 0) (tail (mid (id (` 0)))) (` 0)
mid7ᴿ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = mid7 (dyn 5)}))))

-- the outer boundary `[+X] (…) ⟨+X⟩`
outᴸ-ty : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
outᴸ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C2-B6 ($ 5)}))))

outᴿ-ty : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
outᴿ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = C2-B6 (dyn 5)}))))

id★ᴿ-ty : CastTy ΔR [] (idᵖ ★) ★ ★
id★ᴿ-ty = cast-ty (⊢id atom-★ wf-★) refl

X⊑X₀ : ` 0 ⊑ᵂ⟨ Wᵢ₁ ⟩ ` 0
X⊑X₀ = X⊑X

-- the leaf `[−X] 5 ⟨−X⟩ ⊑ [−X] 5⟨ℕ!⟩ ⟨−X⟩`, with `−X ⊑ −X`
leaf⊑ : Wᵢ₁ ∣ [] ⊢ seal-leaf ($ 5) ⊑ seal-leaf (dyn 5) ∶ X⊑X₀
leaf⊑ =
  ⟪⟫⊑⟪⟫ Wᵢ₁-unb five⊑ leafᴸ-ty leafᴿ-ty
    (Wᵢ₁ , unbind₀-conv-self , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

c2-b6 : W₁ ∣ [] ⊢ C2-B6 ($ 5) ⊑ C2-B6 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩ ∶ ℕ⊑★
c2-b6 =
  ⊑cast
    (⟪⟫⊑⟪⟫ Wᵢ₁-int
      (cast⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-Θ⁻⁺
          (cast⊑cast leaf⊑ tag-ty tag-ty ★⊑★)
          mid6ᴸ-ty mid6ᴿ-ty
          (Wᵢ₁ , Wᵢ₁-Θ⁻⁺-conv , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★)))
          ★⊑★)
        untag-ty untag-ty X⊑X)
      outᴸ-ty outᴿ-ty
      (Wᵢ₁ , Wᵢ₁-conv , conv-unseal⊑unseal refl) ℕ⊑★)
    id★ᴿ-ty ℕ⊑★

c2-b7 : W₁ ∣ [] ⊢ C2-B7 ($ 5) ⊑ C2-B7 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩ ∶ ℕ⊑★
c2-b7 =
  ⊑cast
    (⟪⟫⊑⟪⟫ Wᵢ₁-int
      (cast⊑cast
        (cast⊑cast
          (⟪⟫⊑⟪⟫ Wᵢ₁-Θ⁻⁺ leaf⊑ mid7ᴸ-ty mid7ᴿ-ty
            (Wᵢ₁ , Wᵢ₁-Θ⁻⁺-conv ,
             conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id X⊑X)))
            X⊑X)
          tag-ty tag-ty ★⊑★)
        untag-ty untag-ty X⊑X)
      outᴸ-ty′ outᴿ-ty′
      (Wᵢ₁ , Wᵢ₁-conv , conv-unseal⊑unseal refl) ℕ⊑★)
    id★ᴿ-ty ℕ⊑★
  where
  outᴸ-ty′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  outᴸ-ty′ = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C2-B7 ($ 5)}))))
  outᴿ-ty′ : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
  outᴿ-ty′ = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = C2-B7 (dyn 5)}))))

------------------------------------------------------------------------
-- C13 B1 and C14 B1: two and three right partners (D13)
------------------------------------------------------------------------

-- C13's state 4: two Inst/TyBeta pairs on the right, βᴿ:=★ (0) and
-- αᴿ:=★ (1); the store pairing is ϱ₁₂ again, now ℕ ⊑ ★ twice
Ξ₁₃ : RepCtx
Ξ₁₃ = bindR ★ ∷ bindR ★ ∷ []

C13-R₄ : Term
C13-R₄ = (B12 ⟨ [] ∣ id★↦ ⟩) · dyn 5

C13-R₄-state : head (drop 4 (evalTerms 29 C13-R-⊢)) ≡ just C13-R₄
C13-R₄-state = refl

B13-ty : BdyTy (Ξ₁₃ ∣ []) Θ₀ (Ξ₁₃ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
B13-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ []} {M = B12}))))

B13x-ty : BdyTy (Ξ₁₃ ∣ []) (bind 0 1 ∷ []) (Ξ₁₃ ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX
  (★ ⇒ ★)
B13x-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ []} {M = B12x}))))

B13ᵤ-ty : BdyTy (Ξ₁₃ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ₁₃ ∣ []) (★ ⇒ ★) id★→
  (★ ⇒ ★)
B13ᵤ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ (0 ∷ [])} {M = unbTerm 0 B12x}))))

B13ₜ-ty : CastTy (Ξ₁₃ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
B13ₜ-ty = proj₂ (proj₂
  (cast-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ (0 ∷ [])} {M = tagTerm 0 B12x})))

W₁₃ : World ΔL (Ξ₁₃ ∣ [])
W₁₃ = Wc⁰ {Ξ₁₃} {ϱ₁₂}

c13-b1 : W₁₃ ∣ [] ⊢ L1′ ⊑ C13-R₄ ∶ ℕ⊑★
c13-b1 =
  ·⊑·
    (⊑cast
      (outer⊑ (_ , here) here⇔
        (core⊑ (_ , there here) (there⇔ here⇔) B13x-ty)
        id★↦-ty B13ᵤ-ty B13ₜ-ty B13-ty
        (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ⊑★⇒★ W₁₃))
      id★↦-ty (ℕ⇒ℕ⊑★⇒★ W₁₃))
    five⊑

-- C14's state 5: γᴿ:=ℕ (0) from the source ν, βᴿ:=★ (1) and αᴿ:=★ (2)
-- from the two Inst/TyBeta pairs; αᴸ has three right partners
Ξ₁₄ : RepCtx
Ξ₁₄ = bindR `ℕ ∷ bindR ★ ∷ bindR ★ ∷ []

ϱ₁₄ : RepRel
ϱ₁₄ = (0 , 0) ∷ (0 , 1) ∷ (0 , 2) ∷ []

B14x B14y B14 : Term
B14x = idX ⟪ bind 0 2 ∷ [] , revX ⟫
B14y = genLayer 1 B14x
B14  = genLayer 0 B14y

C14-R₅ : Term
C14-R₅ = B14 · $ 5

C14-R₅-state : head (drop 5 (evalTerms 38 C14-R-⊢)) ≡ just C14-R₅
C14-R₅-state = refl

B14-ty : BdyTy (Ξ₁₄ ∣ []) Θ₀ (Ξ₁₄ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
B14-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14}))))

B14ᵤ-ty : BdyTy (Ξ₁₄ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ₁₄ ∣ []) (★ ⇒ ★) id★→
  (★ ⇒ ★)
B14ᵤ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (0 ∷ [])} {M = unbTerm 0 B14y}))))

B14ₜ-ty : CastTy (Ξ₁₄ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
B14ₜ-ty = proj₂ (proj₂
  (cast-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (0 ∷ [])} {M = tagTerm 0 B14y})))

B14y-ty : BdyTy (Ξ₁₄ ∣ []) (bind 0 1 ∷ []) (Ξ₁₄ ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX
  (★ ⇒ ★)
B14y-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14y}))))

B14yᵤ-ty : BdyTy (Ξ₁₄ ∣ (1 ∷ [])) (unbind 0 1 ∷ []) (Ξ₁₄ ∣ []) (★ ⇒ ★) id★→
  (★ ⇒ ★)
B14yᵤ-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (1 ∷ [])} {M = unbTerm 1 B14x}))))

B14yₜ-ty : CastTy (Ξ₁₄ ∣ (1 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
B14yₜ-ty = proj₂ (proj₂
  (cast-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (1 ∷ [])} {M = tagTerm 1 B14x})))

B14x-ty : BdyTy (Ξ₁₄ ∣ []) (bind 0 2 ∷ []) (Ξ₁₄ ∣ (2 ∷ [])) (` 0 ⇒ ` 0) revX
  (★ ⇒ ★)
B14x-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14x}))))

W₁₄ : World ΔL (Ξ₁₄ ∣ [])
W₁₄ = Wc⁰ {Ξ₁₄} {ϱ₁₄}

c14-b1 : W₁₄ ∣ [] ⊢ L1′ ⊑ C14-R₅ ∶ ι⊑ι base-ℕ
c14-b1 =
  ·⊑·
    (outer⊑ (_ , here) here⇔
      (layer⊑ (_ , there here) (there⇔ here⇔)
        (core⊑ (_ , there (there here)) (there⇔ (there⇔ here⇔)) B14x-ty)
        id★↦-ty B14yᵤ-ty B14yₜ-ty B14y-ty)
      id★↦-ty B14ᵤ-ty B14ₜ-ty B14-ty
      (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl) (ℕ⇒ℕ W₁₄))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- WfWorld for the outer world and the three both-sided worlds of
-- c14-b1: αᴸ is paired with γᴿ:=ℕ, βᴿ:=★ and αᴿ:=★
left0-ϱ₁₄ : ∀ {α β} → ϱ₁₄ ∋ᵨ α ⇔ β → α ≡ 0
left0-ϱ₁₄ here⇔ = refl
left0-ϱ₁₄ (there⇔ here⇔) = refl
left0-ϱ₁₄ (there⇔ (there⇔ here⇔)) = refl
left0-ϱ₁₄ (there⇔ (there⇔ (there⇔ ())))

module Wf₁₄ {nsL nsR : TyCtx} (μ : ImpEnv)
    (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

  W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₄ ∣ nsR)
  W = world μ η η′ ϱ₁₄ []

  agree : ∀ {α β} → Paired W α β → Agree W α β
  agree (inj₁ here⇔) = rep-rep r-here r-here same-ℕ same-ℕ (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ here⇔)) =
    rep-rep r-here (r-there r-here) same-ℕ same-★ ℕ⊑★
  agree (inj₁ (there⇔ (there⇔ here⇔))) =
    rep-rep r-here (r-there (r-there r-here)) same-ℕ same-★ ℕ⊑★
  agree (inj₁ (there⇔ (there⇔ (there⇔ ()))))
  agree (inj₂ ())

  uniq : ∀ {α α′ β} → Paired W α β → Paired W α′ β → α ≡ α′
  uniq (inj₁ p) (inj₁ p′) = trans (left0-ϱ₁₄ p) (sym (left0-ϱ₁₄ p′))
  uniq (inj₁ p) (inj₂ ())
  uniq (inj₂ ()) _

W₁₄-wf : WfWorld W₁₄
W₁₄-wf = wf-world joint[] agree uniq
  where open Wf₁₄ [] []↪ []↪

W₁₄²-wf : ∀ {β} → ϱ₁₄ ∋ᵨ 0 ⇔ β → WfWorld (Wc² {Ξ₁₄} {ϱ₁₄} β)
W₁₄²-wf p = wf-world (both (inj₁ p) joint[]) agree uniq
  where open Wf₁₄ (X⊑★ ∷ []) (keep []↪) (keep []↪)

W₁₄ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₄} {ϱ₁₄})
W₁₄ᴸ-wf = wf-world (left-only joint[]) agree uniq
  where open Wf₁₄ (X⊑★ ∷ []) (keep []↪) (skip []↪)

------------------------------------------------------------------------
-- The initial blocks B0
------------------------------------------------------------------------

instI-ty : CastTy empty [] instI (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
instI-ty = proj₂ (proj₂
  (cast-inv {Γ = []} (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩})))

genI-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
genI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = I★genI})))

instI∘genI-ty : CastTy empty [] instI (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
instI∘genI-ty = proj₂ (proj₂
  (cast-inv {Γ = []} (tc {Δ = empty} {M = I★genI ⟨ [] ∣ instI ⟩})))

genI∘instI-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
genI∘instI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
  (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩})))

-- the left core Λ against the right core Λ: Λ⊑Λ pairs their abstract
-- rep. vars lexically
ΛI⊑ΛI : ∅ʷ ∣ [] ⊢ I ⊑ I ∶ (∀id⊑∀id ∅ʷ)
ΛI⊑ΛI = Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
  (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ)) (∀id⊑∀id ∅ʷ)

-- the premise world of Λ⊑Λ: (aᴸ_ΛY, aᴿ_ΛX) ∈ ϱˡ, both abstract
ΛΛ-wf : WfWorld (∅ʷ ⊕ X⊑X)
ΛΛ-wf = wf-world (both (inj₂ here⇔) joint[]) agree uniq
  where
  agree : ∀ {α β} → Paired (∅ʷ ⊕ X⊑X) α β → Agree (∅ʷ ⊕ X⊑X) α β
  agree (inj₁ ())
  agree (inj₂ here⇔) = abst-abst r-here r-here
  agree (inj₂ (there⇔ ()))
  uniq : ∀ {α α′ β} → Paired (∅ʷ ⊕ X⊑X) α β → Paired (∅ʷ ⊕ X⊑X) α′ β
    → α ≡ α′
  uniq (inj₁ ()) _
  uniq (inj₂ here⇔) (inj₁ ())
  uniq (inj₂ here⇔) (inj₂ here⇔) = refl
  uniq (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniq (inj₂ (there⇔ ())) _

-- Ch B0: Λ⊑Λ under the right's inst cast; the left ν is one-sided
ch-b0 : ∅ʷ ∣ [] ⊢ Ch-L ⊑ Ch-R ∶ ℕ⊑★
ch-b0 =
  ·⊑· (ν⊑ (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ)) five⊑

-- Cg B0: Λ⊑ (Y left-only at X⊑★) under the right's gen and inst casts
cg-b0 : ∅ʷ ∣ [] ⊢ Cg-L ⊑ Cg-R ∶ ℕ⊑★
cg-b0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (⊑cast
          (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
          genI-ty (∀id⊑∀id ∅ʷ))
        instI∘genI-ty (∀id⊑★ ∅ʷ))
      ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ))
    five⊑

-- C2 B0: the two gen casts matched by cast⊑cast; the right's inst
-- cast by ⊑cast; the left ν is one-sided
c2-b0 : ∅ʷ ∣ [] ⊢ C2-L ⊑ C2-R ∶ ℕ⊑★
c2-b0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (cast⊑cast (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ)) genI-ty genI-ty (∀id⊑∀id ∅ʷ))
        instI∘genI-ty (∀id⊑★ ∅ʷ))
      ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ))
    five⊑

-- C12 B0: ν⊑ν (its two rep. vars paired lexically in the conversion
-- world), the right's gen and inst casts by ⊑cast, Λ⊑Λ
C12-ν : Term
C12-ν = ν `ℕ · (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩

C12-R-is : C12-R ≡ C12-ν · $ 5
C12-R-is = refl

C12-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
C12-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C12-ν})))

c12-b0 : ∅ʷ ∣ [] ⊢ C12-L ⊑ C12-R ∶ ι⊑ι base-ℕ
c12-b0 =
  ·⊑·
    (ν⊑ν (⊑cast (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) genI∘instI-ty (∀id⊑∀id ∅ʷ))
      (ι⊑ι base-ℕ) νL-ty C12-ν-ty (Wν , Wν-conv , revX⊑revX refl) (ℕ⇒ℕ ∅ʷ))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

------------------------------------------------------------------------
-- Ch's right-led block X0 (= P3's ∀⊑⟪+⟫ block) and Ch B1
------------------------------------------------------------------------

Ch-R₂-state : head (drop 2 (evalTerms 15 Ch-R-⊢)) ≡ just R3′
Ch-R₂-state = refl

-- ∀⊑⟪+⟫ at X⊑X: (aᴸ_ΛY, αᴿ:=★) ∈ ϱˡ in its premise world W₃ ⊕⁺ X⊑X ^ 0
ch-x0 : W₃ ∣ [] ⊢ Ch-L ⊑ R3′ ∶ ℕ⊑★
ch-x0 = p3-inst

-- ch-x0's premise world is W2⁺ (the same world as C2's X0)
ch-x0-world : W₃ ⊕⁺ X⊑X ^ 0 ≡ W2⁺
ch-x0-world = refl

-- Ch B1: after the left's TyBeta the lexical pair is global,
-- ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}
Ch-L₁-state : head (drop 1 (evalTerms 10 Ch-L-⊢)) ≡ just L1′
Ch-L₁-state = refl

ch-b1 : W₁ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
ch-b1 =
  ·⊑·
    (⊑cast
      (⟪⟫⊑⟪⟫ Wᵢ₁-int
        (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
        bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
      id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
    five⊑

------------------------------------------------------------------------
-- C12's right-led block X0: ν⊑ν around ∀⊑⟪+⟫
------------------------------------------------------------------------

-- C12's state 2: the right's Inst and TyBeta (αᴿ:=★) have run inside
-- the source ν, which has not
C12-ν₂ C12-R₂ : Term
C12-ν₂ = ν `ℕ · ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩
C12-R₂ = C12-ν₂ · $ 5

C12-R₂-state : head (drop 2 (evalTerms 24 C12-R-⊢)) ≡ just C12-R₂
C12-R₂-state = refl

C12-ν₂-ty : NuTy ΔR `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
C12-ν₂-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔR} {M = C12-ν₂})))

genIᴿ-ty : CastTy ΔR [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
genIᴿ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
  (tc {Δ = ΔR} {M = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ⟨ [] ∣ genI ⟩})))

-- the ν conversion world: the two ν-bound rep. vars paired lexically
Wν₂ : World ((bindR `ℕ ∷ []) ∣ (0 ∷ [])) ((bindR `ℕ ∷ reps ΔR) ∣ (0 ∷ []))
Wν₂ = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ [])

Wν₂-conv : ConversionInterior (underν² `ℕ `ℕ W₃) Θ₀ Θ₀ Wν₂
Wν₂-conv = record
  { conv-left       = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
  ; conv-right      = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
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

c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
c12-x0 =
  ·⊑·
    (ν⊑ν
      (⊑cast
        (⊑cast
          (∀⊑⟪+⟫ {m = X⊑X} (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
            (inst-Λ (V-simple S-ƛ))
            (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
            r-here bR-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        genIᴿ-ty (∀id⊑∀id W₃))
      (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl) (ℕ⇒ℕ W₃))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

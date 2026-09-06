module strong.proof.IdPushReach where

-- IDPUSH — THE REACHABILITY VERDICT, and the soundness fix it points to.
--
-- RETIRED, AND KEPT AS A RECORD (2026-09-06).  The SCOPE MOVE
-- (strong.Reduction §2b) replaced the contractum this file is about:
-- IdPush now moves Θ₂'s scope into the inner frame, and its preservation
-- case needs NO scoping side-condition (proof/MoveScope.preserve-IdPush).
-- `idPush⁺` below is still a true lemma about the OLD contractum, and
-- `maskOnly` is still used by proof/WallReach; both are kept for that
-- record.  What follows describes the question as it stood.
--
--
-- proof/PreserveObstruct §4 refutes IdPush's preservation case with a
-- HAND-BUILT redex whose Θ₂ = `lock 1 ∷ []` blocks exactly the slot the
-- inner identity conversion's binder rep (` 1) names — the v1 c10/c11
-- chained-rep shape.  The mission: is that configuration REACHABLE by v2
-- reductions from a closed, plain System F source?
--
-- THE VERDICT (worked out in the report and recorded in Examples §10):
--
--   NOT reachable, once the SEPARATELY-DIAGNOSED Peel/`dual` bug is fixed.
--   The obstruction is `interior Θ₂ Δ ⊬ᵗ A`, where A is Y's rep.  For a lock in
--   Θ₂ to reach an ACTIVE outer conversion at all, Θ₂ must come from a
--   Peel's `dual Θ` (TyBeta only ever mints a lock-free `bind A ∷ []`).  A
--   repaired dual installs ONLY the binder locks `hideBinds (numBinds Θ)`,
--   which block Θ's own new binder slots — and by SIMULTANEITY
--   (Ctx.pushBinds lifts each rep past the binders INSIDE it, so a rep
--   is a type over the PLAIN exterior) no binder's rep ever names another
--   binder slot.  So the binder locks never block a conversion's rep, and the
--   `¬IdPushCase` witness — whose `Θ₂`'s lock lands on a NON-binder slot
--   the rep names — is producible only by the CURRENT `dual`'s
--   `unlock X ↦ lock (n+X)` defect (the §3 Peel refutation), not by
--   IdPush itself.
--
-- THE SOUNDNESS FIX (this file, machine-checked).  `idPush⁺` proves the
-- IdPush preservation case under ONE genuinely-added scoping side-condition
--
--     scoped : interior Θ₂ Δ ⊢ᵗ A                       (Q3(a)'s premise)
--
-- together with `binder : interior Θ₂ Δ ∋ Y := A`, which is NOT an assumption
-- about the world but a CONSEQUENCE of the redex being typed: `wE′` gives Y
-- visible in `interior Θ₂ Δ` and `d` gives Y a binder in `convCtx Θ₂ Δ`, and
-- `interior` differs from `convCtx` only by masking (never abst↔bind), so a
-- visible interior slot that is a binder outside is that same binder inside.
-- (That "mask-only" step is `MaskOnly` below; it is now PROVEN — `maskOnly`,
-- §2 — so this file assumes nothing.)
--
-- With both in hand the conversion-swapped contractum type-checks: the
-- reconstruction is the whole of §3.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction using ()
open import strong.proof.Preserve using (IdPushCase)

------------------------------------------------------------------------
-- §1  TWO LOOKUP TRANSPORTS  (they live in proof/MoveScope now)
------------------------------------------------------------------------

open import strong.proof.MoveScope using (unlockedScope-∋bind; pushBinds-∋)

------------------------------------------------------------------------
-- §2  THE MASK-ONLY FACT — PROVEN (2026-09-05)
------------------------------------------------------------------------

-- `interior Θ Δ` differs from `convCtx Θ Δ` ONLY by masking (`scope`
-- applies the `lock` masks, `unlockedScope` skips them; both do the same
-- binds and unmasks).  Masking never turns an `abst` into a `bind`, so a
-- slot that is NAMEABLE in `interior Θ Δ` and a BINDER in `convCtx Θ Δ`
-- is that same binder in `interior Θ Δ`.
MaskOnly : Set
MaskOnly = ∀ (Θ : CtxMorph) (Δ : Ctxᵗ) {Y A}
  → interior Θ Δ ∋tv Y → convCtx Θ Δ ∋ Y := A → interior Θ Δ ∋ Y := A

-- THE REFINEMENT THAT ONLY MASKS.  This is `Ctx._⊑ᵉ_` MINUS the one
-- clause that invents knowledge (`le-ao : abst ⊑ᵉ bind A`).  `scope` and
-- `unlockedScope` differ only by `lock`s, and a `lock` masks — it never turns a
-- Λ-bound slot into a binder — so the two type contexts are related by
-- THIS relation, not merely by `⊑`.  That is the whole content of the
-- lemma: `⊑` alone would permit `abst` outside to be `bind A` inside.
infix 4 _⊑ᵐᵉ_
data _⊑ᵐᵉ_ : Ent → Ent → Set where
  lm-aa : abst ⊑ᵐᵉ abst
  lm-oo : ∀ {A} → bind A ⊑ᵐᵉ bind A
  lm-bb : ∀ {E E′} → E ⊑ᵐᵉ E′ → masked E ⊑ᵐᵉ masked E′
  lm-bu : ∀ {E E′} → E ⊑ᵐᵉ E′ → Nameable E′ → masked E ⊑ᵐᵉ E′

infix 4 _⊑ᵐ_
data _⊑ᵐ_ : Ctxᵗ → Ctxᵗ → Set where
  lm[] : [] ⊑ᵐ []
  lm∷  : ∀ {E E′ Δ Δ′} → E ⊑ᵐᵉ E′ → Δ ⊑ᵐ Δ′ → (E ∷ Δ) ⊑ᵐ (E′ ∷ Δ′)

⊑ᵐᵉ-refl : (E : Ent) → E ⊑ᵐᵉ E
⊑ᵐᵉ-refl abst        = lm-aa
⊑ᵐᵉ-refl (bind A)    = lm-oo
⊑ᵐᵉ-refl (masked E)  = lm-bb (⊑ᵐᵉ-refl E)

⊑ᵐ-refl : (Δ : Ctxᵗ) → Δ ⊑ᵐ Δ
⊑ᵐ-refl []      = lm[]
⊑ᵐ-refl (E ∷ Δ) = lm∷ (⊑ᵐᵉ-refl E) (⊑ᵐ-refl Δ)

⊑ᵐᵉ-ren : ∀ {ρ E E′} → E ⊑ᵐᵉ E′ → renᵉ ρ E ⊑ᵐᵉ renᵉ ρ E′
⊑ᵐᵉ-ren lm-aa       = lm-aa
⊑ᵐᵉ-ren lm-oo       = lm-oo
⊑ᵐᵉ-ren (lm-bb l)   = lm-bb (⊑ᵐᵉ-ren l)
⊑ᵐᵉ-ren (lm-bu l v) = lm-bu (⊑ᵐᵉ-ren l) (renᵉ-Nameable v)

⊑ᵐ-∋e : ∀ {Δ Δ′ X E} → Δ ⊑ᵐ Δ′ → Δ ∋e X , E
      → ∃[ E′ ] ((Δ′ ∋e X , E′) × (E ⊑ᵐᵉ E′))
⊑ᵐ-∋e (lm∷ l ls) ez     = _ , ez , ⊑ᵐᵉ-ren l
⊑ᵐ-∋e (lm∷ l ls) (es d) with ⊑ᵐ-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵐᵉ-ren l′

-- THE POINT.  A masking refinement never invents a binder: an entry that
-- is VISIBLE and refines to `bind A` IS `bind A`.
⊑ᵐᵉ-bind : ∀ {E A} → E ⊑ᵐᵉ bind A → Nameable E → E ≡ bind A
⊑ᵐᵉ-bind lm-oo       v  = refl
⊑ᵐᵉ-bind (lm-bu l w) ()

-- masking loses nameability, so it refines the OTHER way
masked-⊑ᵐᵉ : ∀ {E E′} → E ⊑ᵐᵉ E′ → masked E ⊑ᵐᵉ E′
masked-⊑ᵐᵉ lm-aa       = lm-bu lm-aa nameable-a
masked-⊑ᵐᵉ lm-oo       = lm-bu lm-oo nameable-b
masked-⊑ᵐᵉ (lm-bb l)   = lm-bb (masked-⊑ᵐᵉ l)
masked-⊑ᵐᵉ (lm-bu l v) = lm-bu (lm-bu l v) v

mask-⊑ᵐ : ∀ {Δ Δ′} (Y : ℕ) → Δ ⊑ᵐ Δ′ → mask Y Δ ⊑ᵐ Δ′
mask-⊑ᵐ Y       lm[]       = lm[]
mask-⊑ᵐ zero    (lm∷ l ls) = lm∷ (masked-⊑ᵐᵉ l) ls
mask-⊑ᵐ (suc Y) (lm∷ l ls) = lm∷ l (mask-⊑ᵐ Y ls)

unmaskEnt-⊑ᵐᵉ-nameable : ∀ {E E′} → E ⊑ᵐᵉ E′ → Nameable E′ → E ⊑ᵐᵉ unmaskEnt E′
unmaskEnt-⊑ᵐᵉ-nameable l nameable-a = l
unmaskEnt-⊑ᵐᵉ-nameable l nameable-b = l

unmaskEnt-⊑ᵐᵉ : ∀ {E E′} → E ⊑ᵐᵉ E′ → unmaskEnt E ⊑ᵐᵉ unmaskEnt E′
unmaskEnt-⊑ᵐᵉ lm-aa       = lm-aa
unmaskEnt-⊑ᵐᵉ lm-oo       = lm-oo
unmaskEnt-⊑ᵐᵉ (lm-bb l)   = l
unmaskEnt-⊑ᵐᵉ (lm-bu l v) = unmaskEnt-⊑ᵐᵉ-nameable l v

unmask-⊑ᵐ : ∀ {Δ Δ′} (Y : ℕ) → Δ ⊑ᵐ Δ′ → unmask Y Δ ⊑ᵐ unmask Y Δ′
unmask-⊑ᵐ Y       lm[]       = lm[]
unmask-⊑ᵐ zero    (lm∷ l ls) = lm∷ (unmaskEnt-⊑ᵐᵉ l) ls
unmask-⊑ᵐ (suc Y) (lm∷ l ls) = lm∷ l (unmask-⊑ᵐ Y ls)

⊑ᵐ-pushBinds : ∀ {Δ Δ′} (As : List Ty) → Δ ⊑ᵐ Δ′
  → pushBinds As Δ ⊑ᵐ pushBinds As Δ′
⊑ᵐ-pushBinds []       ls = ls
⊑ᵐ-pushBinds (A ∷ As) ls = lm∷ lm-oo (⊑ᵐ-pushBinds As ls)

-- `scope` is `unlockedScope` with the locks applied — and nothing else.
scope⊑ᵐunlockedScope : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scope Θ Δ ⊑ᵐ unlockedScope Θ Δ
scope⊑ᵐunlockedScope []             Δ = ⊑ᵐ-refl Δ
scope⊑ᵐunlockedScope (bind A ∷ Θ)   Δ = scope⊑ᵐunlockedScope Θ Δ
scope⊑ᵐunlockedScope (unlock X ∷ Θ) Δ = unmask-⊑ᵐ X (scope⊑ᵐunlockedScope Θ Δ)
scope⊑ᵐunlockedScope (lock X ∷ Θ)   Δ = mask-⊑ᵐ X (scope⊑ᵐunlockedScope Θ Δ)

interior⊑ᵐconvCtx : (Θ : CtxMorph) (Δ : Ctxᵗ) → interior Θ Δ ⊑ᵐ convCtx Θ Δ
interior⊑ᵐconvCtx Θ Δ = ⊑ᵐ-pushBinds (repsOf Θ) (scope⊑ᵐunlockedScope Θ Δ)

-- THE LEMMA, no longer an interface.
maskOnly : MaskOnly
maskOnly Θ Δ (E , d , v) d′ with ⊑ᵐ-∋e (interior⊑ᵐconvCtx Θ Δ) d
... | E′ , d″ , l with ∋e-det d″ d′
...   | refl = subst (λ e → interior Θ Δ ∋e _ , e) (⊑ᵐᵉ-bind l v) d

------------------------------------------------------------------------
-- §3  THE SOUNDNESS OF IDPUSH UNDER THE SCOPING SIDE-CONDITION
------------------------------------------------------------------------

-- The preservation obligation of IdPush, EXACTLY as `IdPushCase`, but with
-- the added scoping premise `interior Θ₂ Δ ⊢ᵗ A` (Q3(a)) and the mask-only
-- binder fact fed in as a hypothesis.  This is a PROOF, not a parameter: the
-- conversion-swapped contractum types.
IdPushCase⁺ : Set
IdPushCase⁺ = ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → convCtx Θ₂ Δ ∋ Y := A
  → interior Θ₂ Δ ⊢ᵗ A
  → interior Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , mkId A ⟫ ⦂ C

idPush⁺ : IdPushCase⁺
idPush⁺ {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y} {A = A} {C = C}
        v d scoped binder
        (env mw₂ (env mw₁ ⊢V ⊢cᵢ wE′) ⊢cₒ wE)
  with ⊢cₒ
... | conv-unseal dₒ =
  env mw₂
      (env mw₁ ⊢V′ (conv-unseal dX) scoped)
      (subst (λ T → convCtx Θ₂ Δ ⊢ mkId A ∶ A ⇝ T) eqAC
             (mkId-⊢ (⊑-wf (interior⊑convCtx Θ₂ Δ) scoped)))
      wE
  where
  -- The outer `unseal Y`'s rep is `shiftBy (numBinds Θ₂) C`; it IS A.
  eqAC : A ≡ shiftBy (numBinds Θ₂) C
  eqAC = ∋:=-det d dₒ

  -- The inner `id (` X)` conversion: its source type is ` X, and its
  -- target `shiftBy (numBinds Θ₁) (` Y)` equals ` X, so
  -- X = numBinds Θ₁ + Y.
  srcX : _ ≡ ` X
  srcX = conv-idv-src ⊢cᵢ

  eqX : numBinds Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (shiftBy-var (numBinds Θ₁) Y)) (conv-idv-tgt ⊢cᵢ))

  -- V is a value of type ` X on the interior.
  ⊢V′ : interior Θ₁ (interior Θ₂ Δ) ∣ [] ⊢ V ⦂ ` X
  ⊢V′ = subst (λ T → interior Θ₁ (interior Θ₂ Δ) ∣ [] ⊢ V ⦂ T) srcX ⊢V

  -- The inner unseal's binder lookup: Y is a live binder inside
  -- (`binder`), so
  -- it is one in `unlockedScope Θ₁ (interior Θ₂ Δ)`, and the prefix lifts
  -- it to slot `numBinds Θ₁ + Y = X` at rep `shiftBy (numBinds Θ₁) A`.
  dX : convCtx Θ₁ (interior Θ₂ Δ) ∋ X := shiftBy (numBinds Θ₁) A
  dX = subst (λ Z → convCtx Θ₁ (interior Θ₂ Δ)
                      ∋ Z := shiftBy (numBinds Θ₁) A) eqX
             (pushBinds-∋ (repsOf Θ₁) (unlockedScope-∋bind Θ₁ binder))

-- With `maskOnly` PROVEN, `binder` is derived from the redex, so the SINGLE
-- genuinely-added premise is the scoping side-condition `interior Θ₂ Δ ⊢ᵗ A`.
idPushCase-scoped :
  ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → convCtx Θ₂ Δ ∋ Y := A
  → interior Θ₂ Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , mkId A ⟫ ⦂ C
idPushCase-scoped {Δ = Δ} {Θ₂ = Θ₂} v d scoped ⊢R
  with ⊢R
... | env mw₂ (env mw₁ ⊢V ⊢cᵢ wE′) (conv-unseal dₒ) wE =
  idPush⁺ v d scoped (maskOnly Θ₂ Δ (⊢ᵗ→∋tv wE′) d) ⊢R
  where
  -- With the outer conversion matched to `conv-unseal`,
  -- `wE′ : interior Θ₂ Δ ⊢ᵗ ` Y` reflects Y visible inside.
  ⊢ᵗ→∋tv : ∀ {Δ′ Z} → Δ′ ⊢ᵗ ` Z → Δ′ ∋tv Z
  ⊢ᵗ→∋tv (wf-var tv) = tv

------------------------------------------------------------------------
-- §4  THE SCOPING PREMISE IS EXACTLY WHAT THE COUNTEREXAMPLE VIOLATES
------------------------------------------------------------------------

-- proof/PreserveObstruct §4's witness has Δ = `bind (` 0) ∷ bind `ℕ ∷ []`,
-- Θ₂ = `lock 1 ∷ []`, so `interior Θ₂ Δ = bind (` 0) ∷ masked (bind `ℕ)
-- ∷ []` and A = ` 1.  The scoping premise `interior Θ₂ Δ ⊢ᵗ ` 1` is FALSE
-- (slot 1 is blocked) — that failure IS the obstruction, and `binder` still
-- HOLDS there
-- (slot 0 is a live binder with rep ` 1), so it is `scoped` alone that the
-- counterexample denies.
Ξi : Ctxᵗ
Ξi = bind (` 0) ∷ masked (bind `ℕ) ∷ []

-- `binder` holds at the witness …
binder-holds : Ξi ∋ 0 := ` 1
binder-holds = ez

-- … but `scoped` fails: the rep ` 1 is not well formed inside.
scoped-fails : ¬ (Ξi ⊢ᵗ ` 1)
scoped-fails (wf-var (_ , es ez , ()))

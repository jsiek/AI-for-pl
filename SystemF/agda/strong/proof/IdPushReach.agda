module strong.proof.IdPushReach where

-- IDPUSH — THE REACHABILITY VERDICT, and the soundness fix it points to.
--
-- proof/PreserveObstruct §4 refutes IdPush's preservation case with a
-- HAND-BUILT redex whose Θ₂ = `lock 1 ∷ []` blocks exactly the slot the
-- id-face's owner rep (` 1) names — the v1 c10/c11 chained-rep shape.  The
-- mission: is that configuration REACHABLE by v2 reductions from a closed,
-- plain System F source?
--
-- THE VERDICT (worked out in the report and recorded in Examples §10):
--
--   NOT reachable, once the SEPARATELY-DIAGNOSED Peel/`dual` bug is fixed.
--   The obstruction is `intC Θ₂ Δ ⊬ᵗ A`, where A is Y's rep.  For a lock in
--   Θ₂ to reach an ACTIVE outer face at all, Θ₂ must come from a Peel's
--   `dual Θ` (TyBeta only ever mints a lock-free `bind A ∷ []`).  A repaired
--   dual installs ONLY the owner locks `lockBinds (nbind Θ)`, which block
--   Θ's own new owner slots — and by SIMULTANEITY (Ctx.prep lifts each rep
--   past the owners bound INSIDE it, so a rep is a type over the PLAIN
--   exterior) no owner's rep ever names another owner slot.  So the owner
--   locks never block a face's rep, and the `¬IdPushCase` witness — whose
--   `Θ₂`'s lock lands on a NON-owner slot the rep names — is producible only
--   by the CURRENT `dual`'s `unlock X ↦ lock (n+X)` defect (the §3 Peel
--   refutation), not by IdPush itself.
--
-- THE SOUNDNESS FIX (this file, machine-checked).  `idPush⁺` proves the
-- IdPush preservation case under ONE genuinely-added scoping side-condition
--
--     scoped : intC Θ₂ Δ ⊢ᵗ A                       (Q3(a)'s premise)
--
-- together with `owner : intC Θ₂ Δ ∋ Y := A`, which is NOT an assumption
-- about the world but a CONSEQUENCE of the redex being typed: `wE′` gives Y
-- visible in `intC Θ₂ Δ` and `d` gives Y an owner in `fceC Θ₂ Δ`, and
-- `intC` differs from `fceC` only by masking (never abst↔bind), so a
-- visible interior slot that is an owner outside is that same owner inside.
-- (That "mask-only" step is `MaskOnly` below; it is now PROVEN — `maskOnly`,
-- §2 — so this file assumes nothing.)
--
-- With both in hand the swapped-face contractum type-checks: the reconstruction
-- is the whole of §3.

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
-- §1  TWO LOOKUP TRANSPORTS
------------------------------------------------------------------------

-- An owner survives `fscp`: it only unmasks (`unblk`, which fixes `bind`)
-- and skips locks, so a `bind` lookup is preserved unchanged.
fscp-∋bind : ∀ (Θ : CtxMorph) {D Y A}
  → D ∋ Y := A → fscp Θ D ∋ Y := A
fscp-∋bind []              d = d
fscp-∋bind (bind C ∷ Θ)    d = fscp-∋bind Θ d
fscp-∋bind (lock Z ∷ Θ)    d = fscp-∋bind Θ d
fscp-∋bind (unlock Z ∷ Θ) {Y = Y} d with Z ≟ℕ Y
... | yes refl = upd-hit  unblk unblk-comm    (fscp-∋bind Θ d)
... | no  ne   = upd-miss unblk unblk-comm ne (fscp-∋bind Θ d)

-- The owner prefix lifts an owner: slot Y in the tail becomes slot
-- `length As + Y` at the rep lifted past the `length As` prefix owners.
prep-∋ : ∀ (As : List Ty) {D Y A}
  → D ∋ Y := A → prep As D ∋ (length As + Y) := liftN (length As) A
prep-∋ []       d = d
prep-∋ (C ∷ As) d = es (prep-∋ As d)

------------------------------------------------------------------------
-- §2  THE MASK-ONLY FACT — PROVEN (2026-09-05)
------------------------------------------------------------------------

-- `intC Θ Δ` differs from `fceC Θ Δ` ONLY by masking (`scp` applies the
-- `lock` masks, `fscp` skips them; both do the same binds and unmasks).
-- Masking never turns an `abst` into a `bind`, so a slot that is VISIBLE in
-- `intC Θ Δ` and an OWNER in `fceC Θ Δ` is that same owner in `intC Θ Δ`.
MaskOnly : Set
MaskOnly = ∀ (Θ : CtxMorph) (Δ : Ctxᵗ) {Y A}
  → intC Θ Δ ∋tv Y → fceC Θ Δ ∋ Y := A → intC Θ Δ ∋ Y := A

-- THE REFINEMENT THAT ONLY MASKS.  This is `Ctx._⊑ᵉ_` MINUS the one
-- clause that invents knowledge (`le-ao : abst ⊑ᵉ bind A`).  `scp` and
-- `fscp` differ only by `lock`s, and a `lock` masks — it never turns a
-- Λ-bound slot into an owner — so the two type contexts are related by
-- THIS relation, not merely by `⊑`.  That is the whole content of the
-- lemma: `⊑` alone would permit `abst` outside to be `bind A` inside.
infix 4 _⊑ᵐᵉ_
data _⊑ᵐᵉ_ : Ent → Ent → Set where
  lm-aa : abst ⊑ᵐᵉ abst
  lm-oo : ∀ {A} → bind A ⊑ᵐᵉ bind A
  lm-bb : ∀ {E E′} → E ⊑ᵐᵉ E′ → blk E ⊑ᵐᵉ blk E′
  lm-bu : ∀ {E E′} → E ⊑ᵐᵉ E′ → Vis E′ → blk E ⊑ᵐᵉ E′

infix 4 _⊑ᵐ_
data _⊑ᵐ_ : Ctxᵗ → Ctxᵗ → Set where
  lm[] : [] ⊑ᵐ []
  lm∷  : ∀ {E E′ Δ Δ′} → E ⊑ᵐᵉ E′ → Δ ⊑ᵐ Δ′ → (E ∷ Δ) ⊑ᵐ (E′ ∷ Δ′)

⊑ᵐᵉ-refl : (E : Ent) → E ⊑ᵐᵉ E
⊑ᵐᵉ-refl abst     = lm-aa
⊑ᵐᵉ-refl (bind A) = lm-oo
⊑ᵐᵉ-refl (blk E)  = lm-bb (⊑ᵐᵉ-refl E)

⊑ᵐ-refl : (Δ : Ctxᵗ) → Δ ⊑ᵐ Δ
⊑ᵐ-refl []      = lm[]
⊑ᵐ-refl (E ∷ Δ) = lm∷ (⊑ᵐᵉ-refl E) (⊑ᵐ-refl Δ)

⊑ᵐᵉ-ren : ∀ {ρ E E′} → E ⊑ᵐᵉ E′ → renᵉ ρ E ⊑ᵐᵉ renᵉ ρ E′
⊑ᵐᵉ-ren lm-aa       = lm-aa
⊑ᵐᵉ-ren lm-oo       = lm-oo
⊑ᵐᵉ-ren (lm-bb l)   = lm-bb (⊑ᵐᵉ-ren l)
⊑ᵐᵉ-ren (lm-bu l v) = lm-bu (⊑ᵐᵉ-ren l) (renᵉ-Vis v)

⊑ᵐ-∋e : ∀ {Δ Δ′ X E} → Δ ⊑ᵐ Δ′ → Δ ∋e X , E
      → ∃[ E′ ] ((Δ′ ∋e X , E′) × (E ⊑ᵐᵉ E′))
⊑ᵐ-∋e (lm∷ l ls) ez     = _ , ez , ⊑ᵐᵉ-ren l
⊑ᵐ-∋e (lm∷ l ls) (es d) with ⊑ᵐ-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵐᵉ-ren l′

-- THE POINT.  A masking refinement never invents an owner: an entry that
-- is VISIBLE and refines to `bind A` IS `bind A`.
⊑ᵐᵉ-bind : ∀ {E A} → E ⊑ᵐᵉ bind A → Vis E → E ≡ bind A
⊑ᵐᵉ-bind lm-oo       v  = refl
⊑ᵐᵉ-bind (lm-bu l w) ()

-- masking loses nameability, so it refines the OTHER way
blk-⊑ᵐᵉ : ∀ {E E′} → E ⊑ᵐᵉ E′ → blk E ⊑ᵐᵉ E′
blk-⊑ᵐᵉ lm-aa       = lm-bu lm-aa vis-a
blk-⊑ᵐᵉ lm-oo       = lm-bu lm-oo vis-b
blk-⊑ᵐᵉ (lm-bb l)   = lm-bb (blk-⊑ᵐᵉ l)
blk-⊑ᵐᵉ (lm-bu l v) = lm-bu (lm-bu l v) v

mask-⊑ᵐ : ∀ {Δ Δ′} (Y : ℕ) → Δ ⊑ᵐ Δ′ → mask Y Δ ⊑ᵐ Δ′
mask-⊑ᵐ Y       lm[]       = lm[]
mask-⊑ᵐ zero    (lm∷ l ls) = lm∷ (blk-⊑ᵐᵉ l) ls
mask-⊑ᵐ (suc Y) (lm∷ l ls) = lm∷ l (mask-⊑ᵐ Y ls)

unblk-⊑ᵐᵉ-vis : ∀ {E E′} → E ⊑ᵐᵉ E′ → Vis E′ → E ⊑ᵐᵉ unblk E′
unblk-⊑ᵐᵉ-vis l vis-a = l
unblk-⊑ᵐᵉ-vis l vis-b = l

unblk-⊑ᵐᵉ : ∀ {E E′} → E ⊑ᵐᵉ E′ → unblk E ⊑ᵐᵉ unblk E′
unblk-⊑ᵐᵉ lm-aa       = lm-aa
unblk-⊑ᵐᵉ lm-oo       = lm-oo
unblk-⊑ᵐᵉ (lm-bb l)   = l
unblk-⊑ᵐᵉ (lm-bu l v) = unblk-⊑ᵐᵉ-vis l v

unmask-⊑ᵐ : ∀ {Δ Δ′} (Y : ℕ) → Δ ⊑ᵐ Δ′ → unmask Y Δ ⊑ᵐ unmask Y Δ′
unmask-⊑ᵐ Y       lm[]       = lm[]
unmask-⊑ᵐ zero    (lm∷ l ls) = lm∷ (unblk-⊑ᵐᵉ l) ls
unmask-⊑ᵐ (suc Y) (lm∷ l ls) = lm∷ l (unmask-⊑ᵐ Y ls)

⊑ᵐ-prep : ∀ {Δ Δ′} (As : List Ty) → Δ ⊑ᵐ Δ′ → prep As Δ ⊑ᵐ prep As Δ′
⊑ᵐ-prep []       ls = ls
⊑ᵐ-prep (A ∷ As) ls = lm∷ lm-oo (⊑ᵐ-prep As ls)

-- `scp` is `fscp` with the locks applied — and nothing else.
scp⊑ᵐfscp : (Θ : CtxMorph) (Δ : Ctxᵗ) → scp Θ Δ ⊑ᵐ fscp Θ Δ
scp⊑ᵐfscp []             Δ = ⊑ᵐ-refl Δ
scp⊑ᵐfscp (bind A ∷ Θ)   Δ = scp⊑ᵐfscp Θ Δ
scp⊑ᵐfscp (unlock X ∷ Θ) Δ = unmask-⊑ᵐ X (scp⊑ᵐfscp Θ Δ)
scp⊑ᵐfscp (lock X ∷ Θ)   Δ = mask-⊑ᵐ X (scp⊑ᵐfscp Θ Δ)

intC⊑ᵐfceC : (Θ : CtxMorph) (Δ : Ctxᵗ) → intC Θ Δ ⊑ᵐ fceC Θ Δ
intC⊑ᵐfceC Θ Δ = ⊑ᵐ-prep (reps Θ) (scp⊑ᵐfscp Θ Δ)

-- THE LEMMA, no longer an interface.
maskOnly : MaskOnly
maskOnly Θ Δ (E , d , v) d′ with ⊑ᵐ-∋e (intC⊑ᵐfceC Θ Δ) d
... | E′ , d″ , l with ∋e-det d″ d′
...   | refl = subst (λ e → intC Θ Δ ∋e _ , e) (⊑ᵐᵉ-bind l v) d

------------------------------------------------------------------------
-- §3  THE SOUNDNESS OF IDPUSH UNDER THE SCOPING SIDE-CONDITION
------------------------------------------------------------------------

-- The preservation obligation of IdPush, EXACTLY as `IdPushCase`, but with
-- the added scoping premise `intC Θ₂ Δ ⊢ᵗ A` (Q3(a)) and the mask-only
-- owner fact fed in as a hypothesis.  This is a PROOF, not a parameter: the
-- swapped-face contractum types.
IdPushCase⁺ : Set
IdPushCase⁺ = ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → fceC Θ₂ Δ ∋ Y := A
  → intC Θ₂ Δ ⊢ᵗ A
  → intC Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫ ⦂ C

idPush⁺ : IdPushCase⁺
idPush⁺ {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y} {A = A} {C = C}
        v d scoped owner
        (env bw₂ (env bw₁ ⊢V ⊢cᵢ wE′) ⊢cₒ wE)
  with ⊢cₒ
... | conv-unseal dₒ =
  env bw₂
      (env bw₁ ⊢V′ (conv-unseal dX) scoped)
      (subst (λ T → fceC Θ₂ Δ ⊢ idc A ∶ A ⇝ T ∙ ↑ˢ) eqAC
             (idc-⊢ (⊑-wf (intC⊑fceC Θ₂ Δ) scoped)))
      wE
  where
  -- The outer `unseal Y`'s rep is `liftN (nbind Θ₂) C`; it IS A.
  eqAC : A ≡ liftN (nbind Θ₂) C
  eqAC = ∋:=-det d dₒ

  -- The inner `id (` X)` face: its interior is ` X, and its exterior
  -- `liftN (nbind Θ₁) (` Y)` equals ` X, so X = nbind Θ₁ + Y.
  srcX : _ ≡ ` X
  srcX = conv-idv-src ⊢cᵢ

  eqX : nbind Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (liftN-var (nbind Θ₁) Y)) (conv-idv-tgt ⊢cᵢ))

  -- V is a value of type ` X on the interior.
  ⊢V′ : intC Θ₁ (intC Θ₂ Δ) ∣ [] ⊢ V ⦂ ` X
  ⊢V′ = subst (λ T → intC Θ₁ (intC Θ₂ Δ) ∣ [] ⊢ V ⦂ T) srcX ⊢V

  -- The inner unseal's owner lookup: Y is a live owner inside (owner), so
  -- it is one in `fscp Θ₁ (intC Θ₂ Δ)`, and the prefix lifts it to slot
  -- `nbind Θ₁ + Y = X` at rep `liftN (nbind Θ₁) A`.
  dX : fceC Θ₁ (intC Θ₂ Δ) ∋ X := liftN (nbind Θ₁) A
  dX = subst (λ Z → fceC Θ₁ (intC Θ₂ Δ) ∋ Z := liftN (nbind Θ₁) A) eqX
             (prep-∋ (reps Θ₁) (fscp-∋bind Θ₁ owner))

-- With `maskOnly` PROVEN, `owner` is derived from the redex, so the SINGLE
-- genuinely-added premise is the scoping side-condition `intC Θ₂ Δ ⊢ᵗ A`.
idPushCase-scoped :
  ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → fceC Θ₂ Δ ∋ Y := A
  → intC Θ₂ Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫ ⦂ C
idPushCase-scoped {Δ = Δ} {Θ₂ = Θ₂} v d scoped ⊢R
  with ⊢R
... | env bw₂ (env bw₁ ⊢V ⊢cᵢ wE′) (conv-unseal dₒ) wE =
  idPush⁺ v d scoped (maskOnly Θ₂ Δ (⊢ᵗ→∋tv wE′) d) ⊢R
  where
  -- With the outer face matched to `conv-unseal`, `wE′ : intC Θ₂ Δ ⊢ᵗ ` Y`
  -- reflects Y visible inside.
  ⊢ᵗ→∋tv : ∀ {Δ′ Z} → Δ′ ⊢ᵗ ` Z → Δ′ ∋tv Z
  ⊢ᵗ→∋tv (wf-var tv) = tv

------------------------------------------------------------------------
-- §4  THE SCOPING PREMISE IS EXACTLY WHAT THE COUNTEREXAMPLE VIOLATES
------------------------------------------------------------------------

-- proof/PreserveObstruct §4's witness has Δ = `bind (` 0) ∷ bind `ℕ ∷ []`,
-- Θ₂ = `lock 1 ∷ []`, so `intC Θ₂ Δ = bind (` 0) ∷ blk (bind `ℕ) ∷ []` and
-- A = ` 1.  The scoping premise `intC Θ₂ Δ ⊢ᵗ ` 1` is FALSE (slot 1 is
-- blocked) — that failure IS the obstruction, and `owner` still HOLDS there
-- (slot 0 is a live owner with rep ` 1), so it is `scoped` alone that the
-- counterexample denies.
Ξi : Ctxᵗ
Ξi = bind (` 0) ∷ blk (bind `ℕ) ∷ []

-- `owner` holds at the witness …
owner-holds : Ξi ∋ 0 := ` 1
owner-holds = ez

-- … but `scoped` fails: the rep ` 1 is not well formed inside.
scoped-fails : ¬ (Ξi ⊢ᵗ ` 1)
scoped-fails (wf-var (_ , es ez , ()))

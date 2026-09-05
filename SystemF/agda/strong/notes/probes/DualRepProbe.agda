module strong.notes.probes.DualRepProbe where

-- THE ⊢Δ QUESTION for strong.DualDef's DualRep≈ / BlkRepWf≈.
--
-- DualDef's own comment says the copied rep's well-formedness is "a fact
-- about ⊢ Δ, which the preservation statement does not carry".  This probe
-- settles the shape of the repair by REFUTING two statements:
--
--   §1  DualRep≈ AS STATED is FALSE.  Nothing in  Δ ∣ intOf Δ Θ ⊢ᵇ Θ
--       constrains Δ's OWN entries, so Δ may store a garbage rep.
--   §2  ⊢ Δ ALONE IS NOT ENOUGH.  BlkRepWf≈ quantifies over k and i with no
--       relation between them, while the only call site (rvlsᴳ, through
--       bwf-rvlsᴳ) uses  suc (i + k) ≡ cmax Θ .  At an UNRELATED (k , i) the
--       conclusion is false on a perfectly well-formed Δ.
--
--   §3  the REPAIRED statement (BlkRepWf, proved in strong.DualRepProof),
--       with the same two contexts now discharged.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_; _⊢_; entAt;
         wf-var; wf-ℕ; _∋tv_; here-abst; skip-abst; skip-rvld;
         ⊢_; ⊢∅; ⊢abst; ⊢rvld)
open import strong.Boundary
  using (BCtx; BEntry; rvl; rvl⋆; cnc; cnc⋆; revs; cmax; isConc; intOf;
         Bwf; bwf[]; bwf⋆↓; _∣_⊢ᵇ_; dfree)
open import strong.BReduction using (copyRep; unfEnt)
open import strong.DualDef using (BlkRepWf≈; DualRep≈)
open import strong.DualRepProof using (BlkRepWf; DualRepWf; dual-rep-wf)

------------------------------------------------------------------------
-- §1.  DualRep≈ IS FALSE AS STATED.
--
-- Δ₁ stores a rep that names index 3 at slot 0, whose own tail Δ₁ ↓ 0 is
-- EMPTY.  ⊢ Δ₁ is false; the boundary Θ₁ = [] is trivially well formed and
-- says nothing about Δ₁, so BlkRepWf≈'s hypotheses are all met at
-- (k , i) = (0 , 0) — and there  copyRep 0 0 (` 3) = ` 3 , which the
-- interior  intOf Δ₁ [] = Δ₁  (one slot) does not admit.
------------------------------------------------------------------------

Δ₁ : TCtx
Δ₁ = rvld (` 3) ∷ []

Θ₁ : BCtx
Θ₁ = []

-- the interior is Δ₁ itself: no reveals, no conceals
_ : intOf Δ₁ Θ₁ ≡ rvld (` 3) ∷ []
_ = refl

-- Δ₁'s entry at slot 0 is garbage: its tail has no slots at all
_ : Δ₁ ↓ 0 ≡ []
_ = refl

¬⊢Δ₁ : ¬ (⊢ Δ₁)
¬⊢Δ₁ (⊢rvld _ (wf-var ()))

-- the boundary premise DualRep≈ carries is satisfied
bwf₁ : Δ₁ ∣ intOf Δ₁ Θ₁ ⊢ᵇ Θ₁
bwf₁ = bwf[]

-- the copy the dual would emit …
_ : copyRep 0 (revs Θ₁) (` 3) ≡ ` 3
_ = refl

-- … is not a type of the dual's exterior
¬wf₁ : ¬ (intOf Δ₁ Θ₁ ⊢ ` 3)
¬wf₁ (wf-var (skip-rvld ()))

-- *** THE REFUTATION ***  the ∀-statement, applied to this instance
¬DualRep≈ : ¬ DualRep≈
¬DualRep≈ dr = ¬wf₁ (proj₁ (dr {Δ₁} {Θ₁} bwf₁ 0 0 (` 3) refl refl) refl)

------------------------------------------------------------------------
-- §2.  ⊢ Δ ALONE DOES NOT REPAIR IT.
--
-- Δ₂ is well formed: slot 0 knows ` 1, which IS a type of its tail
-- (two abstract slots).  Θ₂ = ↓Y:⋆ at index 1 conceals nothing AT A REP
-- (isConc 0 Θ₂ = false) but has cmax Θ₂ = 2, so the interior keeps only the
-- single slot below the drop.  At (k , i) = (0 , 0) — which the call site
-- never produces, since it always has suc (i + k) ≡ cmax Θ = 2 — the raw
-- copy is ` 1 again, and the interior has one slot.
------------------------------------------------------------------------

Δ₂ : TCtx
Δ₂ = rvld (` 1) ∷ abst ∷ abst ∷ []

Θ₂ : BCtx
Θ₂ = cnc⋆ 1 ∷ []

⊢Δ₂ : ⊢ Δ₂
⊢Δ₂ = ⊢rvld (⊢abst (⊢abst ⊢∅)) (wf-var (skip-abst here-abst))

bwf₂ : Δ₂ ∣ intOf Δ₂ Θ₂ ⊢ᵇ Θ₂
bwf₂ = bwf⋆↓ (skip-rvld here-abst) bwf[]

-- the drop is two slots wide, and slot 0 is NOT concealed at a rep
_ : cmax Θ₂ ≡ 2
_ = refl
_ : isConc 0 Θ₂ ≡ false
_ = refl
_ : intOf Δ₂ Θ₂ ≡ abst ∷ []
_ = refl

-- at k = 0 the raw guard is vacuously satisfied …
_ : dfree 0 0 (` 1) ≡ true
_ = refl
_ : copyRep 0 (revs Θ₂) (` 1) ≡ ` 1
_ = refl

-- … and the copy escapes the interior
¬wf₂ : ¬ (intOf Δ₂ Θ₂ ⊢ ` 1)
¬wf₂ (wf-var (skip-abst ()))

-- *** THE SECOND REFUTATION ***  the ⊢Δ-repaired statement, still without
-- the index relation, is false too
¬DualRep≈-wf : ¬ (∀ {Δ : TCtx} {Θ : BCtx} → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
                → BlkRepWf≈ Δ Θ)
¬DualRep≈-wf dr =
  ¬wf₂ (proj₁ (dr {Δ₂} {Θ₂} ⊢Δ₂ bwf₂ 0 0 (` 1) refl refl) refl)

-- the index relation the call site DOES have (rvlsᴳ (cmax Θ) 0 keeps
-- suc (s + k) ≡ cmax Θ) fails here: suc (0 + 0) = 1 ≢ 2 = cmax Θ₂
_ : ¬ (cmax Θ₂ ≤ suc (0 + 0))
_ = λ { (s≤s ()) }

------------------------------------------------------------------------
-- §3.  THE REPAIRED STATEMENT.  Both a context-well-formedness premise and
-- the call site's index relation, which together are exactly what the two
-- refutations ask for.  Proved in strong.DualRepProof as `DualRep-wf`.
------------------------------------------------------------------------

-- the repaired statement and its proof, imported so the two cannot drift
_ : DualRepWf
_ = dual-rep-wf

-- §1's instance is refused by the ⊢ Δ premise (¬⊢Δ₁) and §2's by the index
-- premise; at the index the CALL SITE uses, §2's Δ₂/Θ₂ goes through — slot
-- i = 1 with k = 0 is the dual's own second reveal, and there the copy is
-- the interior's slot 0.
_ : entAt Δ₂ 1 ≡ abst
_ = refl

-- and at a genuine knowledge slot of the same width the copy lands inside:
Δ₃ : TCtx
Δ₃ = abst ∷ rvld `ℕ ∷ abst ∷ []

⊢Δ₃ : ⊢ Δ₃
⊢Δ₃ = ⊢abst (⊢rvld (⊢abst ⊢∅) wf-ℕ)

_ : cmax Θ₂ ≤ suc (1 + 0)
_ = s≤s (s≤s z≤n)

_ : intOf Δ₃ Θ₂ ⊢ copyRep 0 (revs Θ₂) `ℕ
_ = wf-ℕ

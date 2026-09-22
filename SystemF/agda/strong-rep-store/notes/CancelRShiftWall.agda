module strong-rep-store.notes.CancelRShiftWall where

-- File Charter:
--   * THE WALL, and the record of the repair that answered it.  Found by
--     the stage-2 preservation port (2026-09-19): `CancelR`'s re-spelling
--     premise was read in the WRONG conversion context, and consequently
--     omitted the boundary scope's own representation-bind shift.
--   * REPAIRED THE SAME DAY, with Jeremy's approval — repair (a), the
--     premise read at Θ₁'s own conversion context.
--     `strong-rep-store.Reduction` carries the repaired rule and
--     `strong-rep-store.proof.MoveScope.preserve-CancelR` proves the
--     preservation case it generates.  See notes/DECISIONS.md,
--     2026-09-19.
--
-- WHAT THE STORE CHANGED (experiment 2, 2026-09-22,
-- notes/RepStoreSketch.md).  THE WALL IS DISSOLVED, and this file is its
-- record rather than its refutation.  A boundary carries no bind block,
-- so the inner layer's conversion context no longer lies `numBinds Θ₁`
-- representation binders inside its exterior — it lies ZERO binders
-- inside it, because a boundary changes NAMES only (`no-shift`, §4).
-- The `shiftBy (numBinds Θ₁)` the old premise dropped therefore does not
-- exist to be dropped, and the old premise and the repaired one now have
-- the SAME witness on the very configuration that raised the wall
-- (`old-premise`/`repaired-premise`, §3).
--
-- THE PREMISE STAYS ALL THE SAME, and it is still the repaired one: the
-- two layers are read at two different NAME MAPS — that is what §1's
-- configuration still exhibits, and what makes `A` and `Aᵢ` two
-- different spellings, `` ` 1 `` and `` ` 2 ``, of one representation.
-- They agree only because typing forces `X` and `Y` to name the same
-- cell (`cancel-name`, proof/IdLayer), which a REDUCTION rule may not
-- invert.  The reachable version of this configuration is
-- notes/CancelRReachabilityWitness.agda, nine steps from a closed plain
-- System F program.
--
-- WHAT SURVIVES HERE, all still machine-checked: the `Δ*` configuration
-- (§1), the well-typed redex (§2), the premises old and repaired (§3),
-- the retired shift arithmetic as a LOCAL statement and the one-line
-- reason it is gone (§4), the OLD stage-2 statement as a LOCAL copy,
-- because the rule it came from no longer exists (§5), and the repaired
-- step with its typeable contractum, on this very configuration (§6).
--
-- The local-copy device is the repo's usual one for a retired design:
-- `notes/ReUnlockWall.agda` states the pre-`conv-unlock-live` conversion
-- judgement locally in the same way.
--
-- WHAT THE RULE SAID, BEFORE (strong-rep-store.Reduction, until
-- 2026-09-19):
--
--   CancelR : … → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
--     → Δ⋉ᶜ ⊢ A′ ≈ A ⊣ Δᶜ                   -- ← read at the OUTER Δᶜ
--     → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A
--     → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
--         -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫
--
-- WHAT `env` DEMANDED OF THE CONTRACTUM, THEN.  Write n = numBinds Θ₁
-- and let R be the representation `A` denotes in `Δᶜ`.  The OUTER
-- layer's `mkId A` forces the inner boundary's exterior type to denote
-- R; the INNER layer's own `SameTyExt n` premise then forced
-- `mkId A′`'s type to denote `shiftBy n R`, because the inner boundary's
-- conversion context lay `n` representation binders inside its exterior.
-- The old rule, however, gave `A′` the UNSHIFTED reading.  A
-- representation reading is unique (`same-rep-unique`), so the two were
-- compatible only when `shiftBy n R ≡ R` — that is, only when `n ≡ 0` or
-- R had no free representation variable.  That was the whole defect.
-- `SameTyExt` and `n` are both gone with the bind block; §4 keeps the
-- arithmetic as a local statement and names its replacement.
--
-- THE TWO REPAIR PATHS, AND WHY (a) WON.  Path (b) was to prove and
-- carry the invariant `numBinds Θ₁ ≡ 0` — the hope being that a
-- REACHABLE `CancelR` redex always has it, since a bare `seal X` is
-- minted by `Peel` on the crossing argument, whose frame is
-- `dualBoundary Θ`.  That hope was wrong: `Peel` mints TWO boundaries
-- and only the ARGUMENT's carries the dual, so
-- `notes/CancelRReachabilityWitness.agda` reaches this configuration in
-- nine steps from a closed, plain source program.  Path (b) is closed;
-- path (a) — carry the premise at Θ₁'s own conversion context — is what
-- Jeremy approved and what §6 checks here.
--
-- THE REPAIR, AS INSTALLED.  `IdPush` already carried the analogous
-- premise against the INNER boundary's conversion context,
--
--   IdPush  … → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → …
--     → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ → …
--
-- and `Δ₁ᶜ` is where the cancelled seal's own source lives.  `CancelR`
-- now carries `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ`, `Δ₁ᶜ ∋ X := Aᵢ` and
-- `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ` — a premise block premise-isomorphic to
-- `IdPush`'s.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms
open import strong-rep-store.Reduction
open import strong-rep-store.TypeCheck using (tc; tr; int!; conv!; sq!; wf!)
open import strong-rep-store.proof.MoveScope using (preserve-CancelR)

------------------------------------------------------------------------
-- 1. The configuration
------------------------------------------------------------------------

-- Cell 0 is REPRESENTED BY cell 1 — the shape a type application at a
-- type VARIABLE produces (`f [Y]` under a later `Λ`).  That is what
-- makes R a representation variable rather than a closed type, and the
-- spelling difference therefore visible.  Cell 2 is what the inner
-- boundary scope unlocks.
Ξ* : RepCtx
Ξ* = bindR (` 0) ∷ bindR `ℕ ∷ bindR `𝔹 ∷ []

Δ* : Ctxᵗ
Δ* = Ξ* ∣ (0 ∷ 1 ∷ [])

wfΔ* : WfCtx Δ*
wfΔ* = wf! Δ*

-- The OUTER boundary scope is trivial, which keeps every context in the
-- example computable.
Θ₂* : Boundary
Θ₂* = boundary []

-- The INNER boundary scope UNLOCKS one name, and that is what the twelve
-- runs' `CancelR`s never do: it makes Θ₁'s conversion context a
-- different NAME MAP from Θ₂'s, so the cancelled binder has two
-- spellings.  (Before the store the same job was done by a one-wide bind
-- block, `boundary (`ℕ ∷ []) []`, and the two maps differed by a SHIFT.)
Θ₁* : Boundary
Θ₁* = boundary (unlock 0 2 ∷ [])

-- `Δ₁*` is at once the inner boundary's conversion context, its
-- interior, and — since Θ₂* is trivial — the merged scope's conversion
-- context.
Δ₁* : Ctxᵗ
Δ₁* = Ξ* ∣ (2 ∷ 0 ∷ 1 ∷ [])

Δ₁*-is-conversion : proj₁ (conv! Δ* Θ₁*) ≡ Δ₁*
Δ₁*-is-conversion = refl

------------------------------------------------------------------------
-- 2. The redex, well typed
------------------------------------------------------------------------

-- A closed value at the name `` ` 2 `` of Δ₁*, which denotes cell 1.
V* : Term
V* = ($ 7) ⟪ boundary [] , seal 2 ⟫

⊢V* : Δ₁* ∣ [] ⊢ V* ⦂ ` 2
⊢V* = tc

v* : Value V*
v* = V-⟪⟫ V-$ I-seal

-- `Δ₁* ∋ 1 := ` 2`: at the INNER conversion context the cancelled binder
-- is named 1 and its representation is spelled `` ` 2 ``.
d₁* : Δ₁* ∋ 1 := ` 2
d₁* = proj₂ (sq! Δ₁* 1)

-- `Δ* ∋ 0 := ` 1`: the SAME cell, at the OUTER conversion context, named
-- 0 and spelled `` ` 1 ``.
d₂* : Δ* ∋ 0 := ` 1
d₂* = proj₂ (sq! Δ* 0)

⊢redex* : Δ* ∣ [] ⊢
    (V* ⟪ Θ₁* , seal 1 ⟫) ⟪ Θ₂* , unseal 0 ⟫ ⦂ ` 1
⊢redex* = tc

------------------------------------------------------------------------
-- 3. The context readings, and the two spellings of the premise
------------------------------------------------------------------------

ri* : Δ* ⊢ⁱ Θ₂* ⇒ Δ*
ri* = proj₂ (int! Δ* Θ₂*)

r₁* : Δ* ⊢ᶜ Θ₁* ⇒ Δ₁*
r₁* = proj₂ (conv! Δ* Θ₁*)

r⋉* : Δ* ⊢ᶜ Θ₁* ⋉ Θ₂* ⇒ Δ₁*
r⋉* = proj₂ (conv! Δ* (Θ₁* ⋉ Θ₂*))

r₂* : Δ* ⊢ᶜ Θ₂* ⇒ Δ*
r₂* = proj₂ (conv! Δ* Θ₂*)

-- THE TWO NAME MAPS REALLY DIFFER — that half of the wall stands.
maps-differ : names Δ₁* ≢ names Δ*
maps-differ ()

-- THE PREMISE AT ISSUE, in the OLD spelling: `A′` re-spelled from `A`,
-- read at the OUTER conversion context.
old-premise : Δ₁* ⊢ ` 2 ≈ ` 1 ⊣ Δ*
old-premise = ` 1 , tr , tr

-- THE SAME PREMISE, REPAIRED: read from the cancelled seal's own source
-- `Aᵢ ≡ ` 2` at `Δ₁*`.
repaired-premise : Δ₁* ⊢ ` 2 ≈ ` 2 ⊣ Δ₁*
repaired-premise = ` 1 , tr , tr

-- AND THEY PICK THE SAME `A′` — read the two types above: both are
-- satisfied by `A′ ≡ ` 2`.  Before the store the old premise picked the
-- UNSHIFTED spelling and the inner `env` demanded the shifted one; with
-- the store there is no shift, both readings name cell 1, and the wall
-- is dissolved on its own configuration.  What the repaired premise
-- still buys is that the rule need not INVERT typing to learn that `X`
-- and `Y` name the same cell.

------------------------------------------------------------------------
-- 4. The retired shift arithmetic, and why it is gone
------------------------------------------------------------------------

-- `shiftRep` was `strong-rep-store.Ctx`'s lift of a representation past
-- a boundary scope's own bind block; `SameTyExt n` compared an exterior
-- reading against `shiftRep n` of it.  Both went with the bind block, so
-- the statement is kept LOCALLY: this is the arithmetic the old rule
-- dropped, and it was never trivial.
shiftRep° : ℕ → Ty → Ty
shiftRep° zero    R = R
shiftRep° (suc n) R = ⇑ᵗ (shiftRep° n R)

shift-moves-it : shiftRep° 1 (` 1) ≢ ` 1
shift-moves-it ()

-- AND WHY THERE IS NO SHIFT LEFT TO DROP.  A boundary changes NAMES
-- only, in both readings, so the inner layer's conversion context has
-- the very store its exterior has: zero representation binders in.  One
-- line, and it retires the whole `SameTyExt n` obligation.
no-shift : ∀ {Δ Δᵢ Δ₁ᶜ : Ctxᵗ} {Θ₂ Θ₁ : Boundary}
  → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → reps Δ₁ᶜ ≡ reps Δ
no-shift ri rc = trans (conversion-reps rc) (interior-reps ri)

------------------------------------------------------------------------
-- 5. The OLD stage-2 statement — a LOCAL copy
------------------------------------------------------------------------

-- What `strong-rep-store.Ctx` §9 held until the store landed: a bind
-- block pushed onto the representation context, with every name-map
-- entry moved up by the block's width.
pushRepBinds° : List Ty → RepCtx → RepCtx
pushRepBinds° []       Ξ = Ξ
pushRepBinds° (R ∷ Rs) Ξ =
  bindR (shiftRep° (length Rs) R) ∷ pushRepBinds° Rs Ξ

extendReps° : List Ty → Ctxᵗ → Ctxᵗ
extendReps° Rs (Ξ ∣ Δ) = pushRepBinds° Rs Ξ ∣ map (length Rs +_) Δ

-- `CancelRCase°` is `strong-rep-store.proof.Preserve.CancelRCase` AS IT
-- STOOD on 2026-09-19 before the repair — the rule's premises and the
-- redex's typing in, the contractum's typing out.  `Rs` is where
-- `binds Θ₂` stood.  It is written out here rather than imported because
-- neither the rule nor the bind block that generated it still exists.
-- The one line that mattered is `Δ⋉ᶜ ⊢ A′ ≈ A ⊣ Δᶜ`: read at the OUTER
-- conversion context.
--
-- IT IS NO LONGER REFUTABLE, and that is the point of this file now: at
-- `Rs ≡ []` — which is every boundary since experiment 2 — `extendReps°`
-- is the identity and the premise coincides with the repaired one (§3).
-- What replaced it is the live `CancelRCase`, proved outright by
-- `strong-rep-store.proof.MoveScope.preserve-CancelR` (§6).
CancelRCase° : Set
CancelRCase° = ∀ {Δ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′ C} (Rs : List Ty)
  → WfCtx Δ → Value V
  → extendReps° Rs Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
  → Δ⋉ᶜ ⊢ A′ ≈ A ⊣ Δᶜ
  → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
  → Δᶜ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢
      (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫)
        ⟪ rewind Θ₂ , mkId A ⟫ ⦂ C

-- At the width the store leaves, the retired prefix is the identity.
extendReps°-[] : ∀ {Δ} → extendReps° [] Δ ≡ Δ
extendReps°-[] {Δ = Ξ ∣ Δn} = cong (Ξ ∣_) (map-id Δn)
  where
  map-id : (Δn : TyCtx) → map (0 +_) Δn ≡ Δn
  map-id []        = refl
  map-id (α ∷ Δn′) = cong (α ∷_) (map-id Δn′)

------------------------------------------------------------------------
-- 6. THE REPAIRED RULE, ON THIS CONFIGURATION
------------------------------------------------------------------------

-- The repaired rule fires here — the wall was never about firing — and
-- mints `mkId (` 2)` on the inner layer and `mkId (` 1)` on the outer:
-- two spellings, one cell.
repaired-step : Δ* ⊢ (V* ⟪ Θ₁* , seal 1 ⟫) ⟪ Θ₂* , unseal 0 ⟫
  -→ (V* ⟪ Θ₁* ⋉ Θ₂* , mkId (` 2) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫
  ∣ none
repaired-step = CancelR v* ri* r₁* d₁* r⋉* repaired-premise r₂* d₂*

-- And its contractum IS well typed, by the preservation case the
-- repaired rule generates.  The wall is answered on the configuration
-- that raised it, by the theorem rather than by a hand-built derivation.
repaired-contractum-⊢ : Δ* ∣ [] ⊢
    (V* ⟪ Θ₁* ⋉ Θ₂* , mkId (` 2) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫ ⦂ ` 1
repaired-contractum-⊢ =
  preserve-CancelR wfΔ* v* ri* r₁* d₁* r⋉* repaired-premise r₂* d₂*
    ⊢redex*

module strong.notes.ForallPayloadWall where

-- File Charter:
--   * The record of a SECOND defect and its repair: a spelling — an
--     ordinary de Bruijn index — that is valid in a morphism's conversion
--     context is not valid in its interior, and `TyPeelR-⟪⟫` and `IdPush`
--     each carried one across without re-basing it.
--   * It holds the fact that CONSTRAINS the repair: the two name maps can
--     reorder relative to each other, so the crossing can only go through
--     the representation a name denotes, never through arithmetic on its
--     position.
--   * REPAIRED, unlike when this module was first written.  Both rules now
--     carry the interior spelling as a `_⊢_≈_⊣_` premise
--     (strong.Reduction; notes/DECISIONS.md, 2026-09-18), and the two
--     programs that found it run: they are §8 and §9 of
--     notes/RepresentationReductionExamples.agda.
--
-- HOW IT WAS FOUND.  By the first programs that instantiate at a
-- POLYMORPHIC type.  A morphism's `binds` hold the representation reading
-- of a type ARGUMENT, so a payload has a `∀` in it exactly when a type
-- application is impredicative; nothing else in the suite did that, and
-- `wfᴿ-∀` and `local-ref` fired nowhere.  Both programs were well typed,
-- both reached a redex at every step, and in both it was the CONTRACTUM
-- that failed to typecheck — `TyPeelR-⟪⟫` at the ninth step of one,
-- `IdPush` at the eleventh of the other.
--
-- WHY THE PAYLOAD MATTERED.  Not for itself.  A `∀` payload is simply the
-- first thing that made a lock and an unlock move a name far enough for
-- the two readings to disagree; the defect was never about payloads.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.CtxMorph
open import strong.TypeCheck

------------------------------------------------------------------------
-- 1. The two name maps can REORDER
------------------------------------------------------------------------

-- The interior's `unlock` inserts at a position in ITS list; the
-- conversion context, having skipped the matching `lock`, is looking at a
-- different one.  So the two are not even subsequences of one another.
Δ↔ : Ctxᵗ
Δ↔ = (bindR `ℕ ∷ bindR `𝔹 ∷ []) ∣ (0 ∷ 1 ∷ [])

-- lock representation variable 0 away, then bring it back at the END
Θ↔ : CtxMorph
Θ↔ = morph [] (unlock 1 0 ∷ lock 0 0 ∷ [])

reorder-interior : names (proj₁ (from-just (interior? Δ↔ Θ↔))) ≡ 1 ∷ 0 ∷ []
reorder-interior = refl

reorder-conversion :
  names (proj₁ (from-just (conversion? Δ↔ Θ↔))) ≡ 0 ∷ 1 ∷ []
reorder-conversion = refl

------------------------------------------------------------------------
-- 2. So a spelling MEANS different things in the two readings
------------------------------------------------------------------------

-- Ordinary index 0 names representation variable 0 in the conversion
-- context and representation variable 1 in the interior; the type `` ` 0 ``
-- written in one is the type `` ` 1 `` in the other.
crossing : rebase? (0 ∷ 1 ∷ []) (1 ∷ 0 ∷ []) (` 0)
  ≡ just (` 1 , ` 0 , same-var (there here) , same-var here)
crossing = refl

-- and it is PARTIAL: the conversion context holds names the interior's
-- locks removed, and those have no interior spelling at all
no-crossing : rebase? (0 ∷ 1 ∷ []) (1 ∷ []) (` 0) ≡ nothing
no-crossing = refl

------------------------------------------------------------------------
-- 3. The repair
------------------------------------------------------------------------

-- Because the crossing is a partial lookup rather than arithmetic, it
-- cannot be a defined function inside a contractum: the rule would have to
-- give a junk answer where there is none.  Both rules therefore NAME the
-- interior spelling and carry a `_⊢_≈_⊣_` relating it to the conversion
-- context's, which is the judgement `env` already uses for exactly this in
-- three positions.  Determinism is `sameTy-src-unique` (strong.Ctx), which
-- is why each rule also carries the interior name map's `Unique`.
--
--   TyPeelR-⟪⟫   …
--     → underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ
--     → …
--                   pushes `renameᵗ (extᵗ suc) Bᵢ′`
--   IdPush       … → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ → …
--                   mints `unseal X′`
--   CancelR      … → Δ⋉ᶜ ⊢ A′ ≈ A ⊣ Δᶜ → …
--                   mints `mkId A′` on the inner layer
--
-- The seven runs that predated the repair are unchanged by it, because
-- wherever the two contexts agree the re-based spelling is the old one.
--
-- `CancelR` was repaired PREVENTIVELY: it has the same crossing, but no
-- example distinguishes its two spellings, so it is the one of the three
-- that no failing program forced.  §1 is the argument for doing it
-- anyway.

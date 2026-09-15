module strong.proof.AddrWeaken where

-- Strong System F v8 — carrying a judgment under ONE new address
-- binder.
--
-- The color wrap needs this: substituting under a `Λ` sends the value
-- across a boundary, and the `Λ` binds an address, so the value's bound
-- addresses shift.  Crossing a `ν` is the same with a `nuBind` entry.
--
-- The weakening is indexed by the entry and by a DEPTH, and the depth
-- GROWS as it descends under a conversion's crossings: a boundary's
-- interior is the ambient context with the crossings above it, and the
-- new binder belongs BELOW those crossings — it is introduced outside
-- the boundary.  Pushing the entry on top instead would put it inside,
-- where the pops would have to pass it, which the pop judgment forbids.
--
-- Indexing by (entry, depth) makes the relation DETERMINISTIC, and the
-- renaming it performs is a FUNCTION of the index rather than an index
-- itself — the unifier cannot invert `extᵇ`.  (Both lessons are v7's,
-- from `proof/AnchorWeaken`; what is gone is the store-block
-- arithmetic, since this is one entry.)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

-- STATUS: this module is a STATEMENT of the obligation, not yet a
-- proof, because the shape it needs is in conflict with a decision
-- already taken.  See notes/DECISIONS.md (2026-09-15).
--
-- What is needed:
--
--   AddrWeaken = ∀ {Sg Δ Γ M A e} → AddrEnt e
--              → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A → Sg ∣ (e ∷ Δ) ∣ Γ ⊢ renAddrᴹ suc M ⦂ A
--
-- and it is `proof.TermSubstitution`'s one parameter.
--
-- THE CONFLICT.  Weakening a boundary asks its conversion to retype
-- from the weakened interior to the weakened exterior.  Take §6's
-- sealed literal, a value at `Δ = X:=α`:
--
--     7 ⟨ seal 0 α ∷ᶜ id (` 0) ⟩          seal: exterior Δ, interior []
--
-- Weakened by one address binder the exterior becomes `addr ∷ Δ`, and
-- the seal must now pop α from UNDER that binder:
--
--     (addr ∷ asgn α ∷ []) ▷ 0 := α ⇒ (addr ∷ [])
--
-- which the pop judgment forbids: address entries are NOT transparent,
-- deliberately, because that transparency is exactly what made
-- push/pop non-invertible and the interior walk a non-function
-- (2026-09-15, `proof/Interior`).
--
-- Depth-indexing the weakening (v7's `Wk P d` shape) does not help.
-- The address binder is introduced OUTSIDE the boundary, so it sits at
-- depth 0 in the boundary's exterior — precisely where the outermost
-- crossing needs to pop.
--
-- So the two requirements are in direct conflict:
--
--   * the interior walk wants NO address transparency, or `⟨c⟩` is not
--     a function and `ξ-⟨⟩` cannot compute the context it reduces in;
--   * address weakening wants address transparency, or a value
--     containing a sealed literal cannot cross a `Λ`.
--
-- A promising resolution: the two placements are OBSERVATIONALLY
-- EQUIVALENT.  `asgn α ∷ addr ∷ Δ` and `addr ∷ asgn α ∷ Δ` agree on
-- every lookup — `∋n` gives the same name and address in both, and so
-- do `∋a` and `∋r` — so restoring transparency and making `⟨c⟩` pick
-- the canonical (highest) placement should be sound up to that swap,
-- with `⌊A⌋` unaffected because it reads only `∋n`.  That needs a
-- context-swap lemma threaded through the judgments.

private
  variable
    Sg : Store
    Δ Δ′ Δ₂ Δ₂′ : Ctxᵗ
    e f : Ent
    d : ℕ
    A B : Ty
    R S : RepTy
    X : ℕ
    α : Addr


------------------------------------------------------------------------
-- What IS settled: the entries this weakening pushes, and the renaming
-- it performs as a function of the depth
------------------------------------------------------------------------

-- These entries bind an ADDRESS and no name, so names are untouched and
-- only bound addresses shift.
data AddrEnt : Ent → Set where
  is-addr : AddrEnt addr
  is-nu   : ∀ {R} → AddrEnt (nuBind R)

-- The renaming the weakening performs, as a function of the depth.
wkRen : ℕ → Renameᵇ
wkRen zero    = suc
wkRen (suc d) = extᵇ (wkRen d)

data AddrWk (e : Ent) : ℕ → Ctxᵗ → Ctxᵗ → Set where
  wk-base  : AddrEnt e → AddrWk e zero Δ (e ∷ Δ)
  wk-under : AddrWk e d Δ Δ′ → AddrWk e (suc d) (f ∷ Δ) (f ∷ Δ′)

wk-unique : AddrWk e d Δ Δ′ → AddrWk e d Δ Δ₂′ → Δ′ ≡ Δ₂′
wk-unique (wk-base _) (wk-base _) = refl
wk-unique (wk-under w) (wk-under v) rewrite wk-unique w v = refl


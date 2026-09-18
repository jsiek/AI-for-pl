module strong.notes.CrossingAudit where

-- File Charter:
--   * The audit of every rule that MINTS or MOVES a spelling, against the
--     question three repairs have already turned on: is the spelling read
--     in the same context it is used in?
--   * Each answer is machine-checked here, on a frame that both locks and
--     unlocks, since that is what makes the two contexts part.
--   * It records one hazard that is NOT repaired — `Peel` — and DISPROVES
--     the invariant that would have made it safe (§5).
--
-- THE QUESTION.  A morphism induces two name maps: the INTERIOR, which
-- performs every change, and the CONVERSION context, which skips `lock`s
-- so that a conversion can still name what the interior concealed.  An
-- ordinary de Bruijn index means different things in the two, and they
-- can even reorder relative to each other (§0).  So every spelling a rule
-- carries from one place to another has to be checked: read where, used
-- where.
--
-- THE SCORE.  Of the ten reduction rules, three mint or move a type or a
-- name and were each found to cross wrongly — `TyPeelR-⟪⟫`, `IdPush` and
-- `CancelR`, all repaired (notes/DECISIONS.md, 2026-09-18).  `TyBeta`,
-- `Beta` and `TyPeelR-Λ` are safe, and safe STRUCTURALLY, not by luck:
-- §§1–3 below.  `Peel` is the one that is neither — §4.

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
-- 0. The frame the audit runs on
------------------------------------------------------------------------

-- It must LOCK and UNLOCK, because a frame that only unlocks has the two
-- contexts equal and would audit clean whatever the rule did.  This one
-- locks representation variable 0 away and brings it back at the END, so
-- the interior moves it and the conversion context — which skipped the
-- lock, and whose re-unlock is therefore a no-op — does not.
Δ₀ : Ctxᵗ
Δ₀ = (bindR `ℕ ∷ bindR `𝔹 ∷ []) ∣ (0 ∷ 1 ∷ [])

Θ₀ : CtxMorph
Θ₀ = morph [] (unlock 1 0 ∷ lock 0 0 ∷ [])

nmConv : Ctxᵗ → CtxMorph → Maybe TyCtx
nmConv Γ Θ with conversion? Γ Θ
nmConv Γ Θ | just (Γᶜ , _) = just (names Γᶜ)
nmConv Γ Θ | nothing = nothing

nmDual : Ctxᵗ → CtxMorph → Maybe TyCtx
nmDual Γ Θ with interior? Γ Θ
nmDual Γ Θ | just (Γᵢ , _) = nmConv Γᵢ (dualMorph Θ)
nmDual Γ Θ | nothing = nothing

Δᵢ Δᶜ : Ctxᵗ
Δᵢ = proj₁ (from-just (interior? Δ₀ Θ₀))
Δᶜ = proj₁ (from-just (conversion? Δ₀ Θ₀))

interior-moved : names Δᵢ ≡ 1 ∷ 0 ∷ []
interior-moved = refl

conversion-did-not : names Δᶜ ≡ 0 ∷ 1 ∷ []
conversion-did-not = refl

------------------------------------------------------------------------
-- 1. TyBeta — safe
------------------------------------------------------------------------

-- `reveal 0 B` is minted from the redex's annotation `B`, read at
-- `underΛ Δ`, and lands on `instantiate R (morph [] [])`.  That frame has
-- ONE change and it is an `unlock`, so its conversion context and its
-- interior are the same map, and both are `underΛ Δ`.  A rule whose frame
-- never locks cannot cross wrongly.
tybeta-used :
  names (proj₁ (from-just (conversion? Δ₀ (instantiate `ℕ (morph [] [])))))
    ≡ names (underΛ Δ₀)
tybeta-used = refl

------------------------------------------------------------------------
-- 2. Beta — safe
------------------------------------------------------------------------

-- A value crossing a `Λ` is wrapped by `crossΛᴹ` in `mkId (⇑ᵗ A)` over
-- the frame `morph [] (lock 0 0 ∷ [])`.  `A` is read at Δ and `⇑ᵗ A` is
-- the right spelling at `underΛ Δ`; the frame's only change is the lock,
-- which the conversion context SKIPS, so the conversion context IS
-- `underΛ Δ`.  Nothing moves, so nothing can be misspelled.
beta-used :
  names (proj₁ (from-just
    (conversion? (underΛ Δ₀) (morph [] (lock 0 0 ∷ [])))))
    ≡ names (underΛ Δ₀)
beta-used = refl

------------------------------------------------------------------------
-- 3. TyPeelR-Λ — safe
------------------------------------------------------------------------

-- `instReveal 0 s` is minted from the crossed boundary's conversion `s`,
-- read at `underΛ Δᶜ`, and lands on `instantiate R Θ`.  `instantiate`
-- prepends one name and shifts every change of Θ by one in both
-- universes, so its conversion context is Θ's with that one name in
-- front — which is exactly `underΛ Δᶜ`.  Checked here on a frame that
-- locks, which is where it could have failed.
typeelrΛ-used :
  names (proj₁ (from-just (conversion? Δ₀ (instantiate `ℕ Θ₀))))
    ≡ names (underΛ Δᶜ)
typeelrΛ-used = refl

------------------------------------------------------------------------
-- 4. Peel — THE REMAINING HAZARD, not repaired
------------------------------------------------------------------------

-- `Peel` splits the redex's conversion `s ↦ t`.  `t` stays on Θ, so it is
-- still read where it was.  `s` moves onto `dualMorph Θ`, whose
-- conversion context is taken at the INTERIOR — and that is a different
-- map from Θ's own conversion context, where `s` was read:
peel-read : names Δᶜ ≡ 0 ∷ 1 ∷ []
peel-read = refl

peel-used : names (proj₁ (from-just (conversion? Δᵢ (dualMorph Θ₀))))
  ≡ 1 ∷ 0 ∷ []
peel-used = refl

-- Same names, opposite order: ordinary index 0 is representation variable
-- 0 where `s` was read and representation variable 1 where it is used.  A
-- conversion that mentions index 0 therefore means something else after
-- the move — the defect `TyPeelR-⟪⟫`, `IdPush` and `CancelR` each had.
--
-- WHY IT IS NOT REPAIRED HERE.  The repair the other three took does not
-- transfer: they each carried a TYPE or a NAME, and `SameTy` relates
-- those.  `s` is a CONVERSION, and there is no judgement yet that relates
-- two conversions naming the same representations.  Inventing one is a
-- larger step than the other three took, and it should be ruled rather
-- than assumed.
--
------------------------------------------------------------------------
-- 5. THE PROPERTY `Peel` NEEDS, AND WHEN IT HOLDS
------------------------------------------------------------------------

-- Write I⟦Θ⟧Δ for the interior name map and C⟦Θ⟧Δ for the conversion
-- one.  `Peel` reads `s` at C⟦Θ⟧Δ and uses it at C⟦dualMorph Θ⟧(I⟦Θ⟧Δ),
-- so what it needs, for the frame it fires on, is
--
--     (P)    C⟦dualMorph Θ⟧(I⟦Θ⟧Δ)  ≡  C⟦Θ⟧Δ
--
-- and that is `Ok` below.  §4 showed (P) failing on a hand-built frame.
-- The three facts that say when it holds are these.
Ok : Ctxᵗ → CtxMorph → Set
Ok Γ Θ = nmDual Γ Θ ≡ nmConv Γ Θ

reps₃ : RepCtx
reps₃ = bindR `ℕ ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []

Δ₃ : Ctxᵗ
Δ₃ = reps₃ ∣ (0 ∷ 1 ∷ [])

Lock Unlock : CtxMorph
Lock = morph [] (lock 0 0 ∷ [])
Unlock = morph [] (unlock 0 2 ∷ [])

-- FACT 1.  A change list with NO UNLOCKS has (P).  The conversion context
-- skips every lock, so C⟦Θ⟧Δ = Δ; the interior deletes the locked names;
-- the dual is all unlocks, at the positions the locks recorded, and each
-- is fresh at the interior, so running them restores Δ exactly.
locks-only-ok : Ok Δ₃ (morph [] (lock 0 1 ∷ lock 0 0 ∷ []))
locks-only-ok = refl

-- FACT 2.  A change list with NO LOCKS has (P).  Nothing is skipped, so
-- the two readings perform the same insertions and C⟦Θ⟧Δ = I⟦Θ⟧Δ; the
-- dual is all locks, which the conversion context skips, so it leaves
-- that map alone.
unlocks-only-ok : Ok Δ₃ Unlock
unlocks-only-ok = refl

-- FACT 3.  A MIXED list need not.  `lock 0 0` then `unlock 0 2`:
--
--   interior     (0 1)  --lock 0 0-->  (1)    --unlock 0 2 at 0-->  (2 1)
--   conversion   (0 1)  --skipped-->   (0 1)  --unlock 0 2 at 0-->  (2 0 1)
--
-- The same unlock inserts at position 0 of two lists that a skipped lock
-- has already made different, so 2 lands before 1 in one and before 0 in
-- the other.  The dual then restores 0 at the front of the interior's
-- result, and the two maps hold the same names in different orders.
mixed-dual : nmDual Δ₃ (morph [] (unlock 0 2 ∷ lock 0 0 ∷ []))
  ≡ just (0 ∷ 2 ∷ 1 ∷ [])
mixed-dual = refl

mixed-conv : nmConv Δ₃ (morph [] (unlock 0 2 ∷ lock 0 0 ∷ []))
  ≡ just (2 ∷ 0 ∷ 1 ∷ [])
mixed-conv = refl

-- SO THERE IS NO STRUCTURAL ARGUMENT FOR `Peel`.  (P) is not closed under
-- `_⋉_`, which is what mixes a locking list with an unlocking one:
push-shape-dual : nmDual Δ₃ (rewind Unlock ⋉ Lock) ≡ just (0 ∷ 2 ∷ 1 ∷ [])
push-shape-dual = refl

push-shape-conv : nmConv Δ₃ (rewind Unlock ⋉ Lock) ≡ just (2 ∷ 0 ∷ 1 ∷ [])
push-shape-conv = refl

-- and `_⋉_` is how `CancelR` and `IdPush` build every composite frame.
-- So (P) cannot be proved by induction over the grammar of frames, which
-- is what "every reachable frame is balanced" would have had to mean.
--
-- WHAT IS NOT CLAIMED.  That the frame above is REACHABLE.  It has the
-- form `Θ₁ ⋉ Θ₂` that `IdPush` builds, but no run is known to build one
-- from these ingredients, and no reachable frame violating (P) has been
-- exhibited.  What the disproof rules out is the PROOF STRATEGY, not
-- `Peel`.  Example 12 is the hardest case the suite puts to it — a
-- function flowing through §4's tower, so the identities the tower mints
-- are `_↦_`s and `Peel` fires on composites `CancelR` and `IdPush` built —
-- and it passes.  That is testing, not proof.

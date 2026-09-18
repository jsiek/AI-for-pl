module strong.notes.CrossingAudit where

-- File Charter:
--   * The audit of every rule that MINTS or MOVES a spelling, against the
--     question three repairs have already turned on: is the spelling read
--     in the same context it is used in?
--   * Each answer is machine-checked here, on a frame that both locks and
--     unlocks, since that is what makes the two contexts part.
--   * It records one hazard that is NOT repaired — `Peel` — together with
--     the reason no program reaches it, which is an invariant nobody has
--     proved.
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
open import Data.Maybe using (from-just)
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
-- WHY NO PROGRAM REACHES IT — AND WHY THAT IS NOT A PROOF.  Every frame
-- the rules actually build pairs each `lock` with the `unlock` of its own
-- DUAL, at the same recorded position: `dualMorph` inverts change by
-- change, `rewind` is `dual χ ++ χ`, `_⋉_` concatenates two such, and
-- `instantiate` shifts all of them uniformly.  Θ₀ above is not of that
-- shape, and no run in the suite produces one that is not.  That is an
-- INVARIANT — "every reachable frame is balanced" — which would make
-- `Peel` safe, and which nobody has stated or proved.  Until it is, the
-- eleven runs are the only evidence, and `Peel` fires on composite frames
-- in examples 10 and 11 without incident.

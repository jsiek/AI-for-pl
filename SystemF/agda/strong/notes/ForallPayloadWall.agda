module strong.notes.ForallPayloadWall where

-- File Charter:
--   * The machine-checked record of a SECOND defect: a representation
--     payload containing a `∀` breaks the calculus.  Two rules lose the
--     type — `TyPeelR-⟪⟫` and `IdPush` — and for the same reason.
--   * It holds two closed, well-typed programs that do not run, the step
--     at which each loses its type, and the premise that fails with the
--     value that would have worked.
--   * NOT REPAIRED.  Unlike notes/ReUnlockWall.agda, this one records a
--     defect that is still open.  These programs are therefore not in
--     notes/RepresentationReductionExamples.agda: they do not pass.
--
-- WHERE PAYLOADS WITH A `∀` COME FROM.  A morphism's `binds` hold the
-- representation reading of a type ARGUMENT, so one has a `∀` in it
-- exactly when a type application instantiates at a polymorphic type.
-- System F is impredicative, so that is ordinary; nothing in the rest of
-- the suite does it, and `wfᴿ-∀` and `local-ref` fire nowhere else.
--
-- THE SHARED CAUSE.  Both rules take a SPELLING — an ordinary de Bruijn
-- index — that is valid in one conversion context and reuse it in a
-- different one, without re-basing.  The two contexts agree whenever the
-- locks and unlocks between them leave the relevant name where it was,
-- which is why the rest of the suite never notices.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction
open import strong.TypeCheck
open import strong.Eval

------------------------------------------------------------------------
-- 0. Reading a term apart, for the dissections below
------------------------------------------------------------------------

funOf intr tyfun : Term → Term
funOf (L · M) = L
funOf t = t
intr (M ⟪ Θ , c ⟫) = M
intr t = t
tyfun (L ·[ B , A ]) = L
tyfun t = t

tyann : Term → Ty
tyann (L ·[ B , A ]) = B
tyann t = `ℕ

cnv : Term → Conv
cnv (M ⟪ Θ , c ⟫) = c
cnv t = id `ℕ

------------------------------------------------------------------------
-- 1. `TyPeelR-⟪⟫` pushes in an annotation read in the wrong context
------------------------------------------------------------------------

-- `ΛX. λx:X. ((ΛY. λy:Y. y) [∀Z. Z⇒X]) · (ΛZ. λz:Z. x)`, at `[ℕ] · 7`
-- and then `[𝔹] · true`.  The type argument `∀Z. Z⇒X` is a `∀` whose body
-- mentions a live type variable, so its payload has a payload-LOCAL
-- reference and a FREE representation variable under the same binder.
N₀ : Term
N₀ =
  ((Λ (ƛ ` 0 ∙
        (((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `∀ (` 0 ⇒ ` 1) ])
          · (Λ (ƛ ` 0 ∙ ` 1)))))
     ·[ ` 0 ⇒ `∀ (` 0 ⇒ ` 1) , `ℕ ] · $ 7)
    ·[ ` 0 ⇒ `ℕ , `𝔹 ] · `true

N₀-⊢ : empty ∣ [] ⊢ N₀ ⦂ `ℕ
N₀-⊢ = tc

-- It runs eight steps and then loses the type.  The ninth step is
-- `TyPeelR-⟪⟫`.
N-breaks : repKept (report (eval 9 N₀ N₀-⊢)) ≡ false
N-breaks = refl

N-at-step-9 : traceLen (eval 9 N₀ N₀-⊢) ≡ 9
N-at-step-9 = refl

N-state N-bad : Term
N-state = traceEnd (eval 8 N₀ N₀-⊢)
N-bad = from-just (stepTo empty N-state)

N-bad-untypeable : infer empty [] N-bad ≡ nothing
N-bad-untypeable = refl

-- THE FAILING PREMISE.  The contractum pushes the type application in one
-- layer, carrying `renameᵗ (extᵗ suc) Bᵢ` — where Bᵢ is the source of the
-- crossed boundary's conversion, read at `underΛ Δᶜ`.  `⊢·[]` reads that
-- annotation in the INTERIOR context instead, and the two disagree: Δᶜ
-- keeps the names the interior's locks removed, so the same
-- representation sits at a different ordinary index in each.
ΔN : Ctxᵗ
ΔN = (bindR (` 1) ∷ bindR (`∀ ((` 0) ⇒ (` 2))) ∷ bindR `𝔹 ∷ bindR `ℕ ∷ [])
       ∣ (0 ∷ 3 ∷ [])

N-app : Term
N-app = intr (intr (funOf N-bad))

-- the head really is a `∀`-value, at this type
N-head-ty : infer ΔN [] (tyfun N-app) ≡ just (`∀ ((` 0) ⇒ (` 2)) , tc)
N-head-ty = refl

-- but the annotation the rule pushed in names ` 4 where ` 2 was meant
N-annotation : tyann N-app ≡ (` 0) ⇒ (` 4)
N-annotation = refl

-- so `⊢·[]` cannot fire
N-app-untypeable : check⊢ ΔN [] (tyfun N-app) (`∀ (tyann N-app)) ≡ nothing
N-app-untypeable = refl

------------------------------------------------------------------------
-- 2. `IdPush` pushes a NAME read in the wrong context
------------------------------------------------------------------------

-- `(ΛX. λx:X. x) [∀Z. Z⇒Z] · (ΛZ. λz:Z. z)`, at `[𝔹] · true`: the
-- identity instantiated at its own type, so the payload is a closed `∀`.
H₀ : Term
H₀ = (((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `∀ (` 0 ⇒ ` 0) ])
        · (Λ (ƛ ` 0 ∙ ` 0)))
       ·[ ` 0 ⇒ ` 0 , `𝔹 ] · `true

H₀-⊢ : empty ∣ [] ⊢ H₀ ⦂ `𝔹
H₀-⊢ = tc

-- Ten steps, then the eleventh — `IdPush` — loses the type.
H-breaks : repKept (report (eval 11 H₀ H₀-⊢)) ≡ false
H-breaks = refl

H-at-step-11 : traceLen (eval 11 H₀ H₀-⊢) ≡ 11
H-at-step-11 = refl

H-state H-bad : Term
H-state = traceEnd (eval 10 H₀ H₀-⊢)
H-bad = from-just (stepTo empty H-state)

H-bad-untypeable : infer empty [] H-bad ≡ nothing
H-bad-untypeable = refl

-- THE FAILING PREMISE.  `IdPush` turns the inner `id (` X)` into
-- `unseal X` and merges the two frames.  `X` was read in the INNER
-- frame's conversion context; the merged frame has a different one, and
-- in it `X` names a different representation.
ΓH ΓHᶜ : Ctxᵗ
ΓH = (bindR (` 0) ∷ bindR `𝔹 ∷ bindR (`∀ ((` 0) ⇒ (` 0))) ∷ []) ∣ (1 ∷ [])
ΓHᶜ = (bindR (` 0) ∷ bindR `𝔹 ∷ bindR (`∀ ((` 0) ⇒ (` 0))) ∷ [])
        ∣ (0 ∷ 1 ∷ 2 ∷ [])

H-inner : Term
H-inner = intr (intr H-bad)

-- the value under the merged frame is fine, at ` 0
H-value-ty : ΓH ∣ [] ⊢ H-inner ⦂ ` 0
H-value-ty = tc

-- the conversion the rule minted
H-minted : cnv (intr H-bad) ≡ unseal 2
H-minted = refl

-- `unseal 2`'s source is ` 2, which is NOT the value's type ` 0 …
H-mismatch : sameTy? ΓH ΓHᶜ (` 0) (` 2) ≡ nothing
H-mismatch = refl

-- … whereas ` 1 is.  The rule should have pushed `unseal 1`.
H-would-work : SameTy ΓH (` 0) ΓHᶜ (` 1)
H-would-work = ` 1 , same-var here , same-var (there here)

------------------------------------------------------------------------
-- 3. Why the repair cannot be positional
------------------------------------------------------------------------

-- The obvious repair is to RE-BASE a spelling as it crosses: translate an
-- index from the conversion context's name map to the interior's.  That
-- translation cannot be positional arithmetic, because the two maps can
-- REORDER relative to each other — the interior's `unlock` inserts at a
-- position in ITS list, and the conversion context, having skipped the
-- matching `lock`, is looking at a different one.
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

-- So the two maps are not even a subsequence of one another, and the only
-- translation there is goes through the REPRESENTATION a name denotes:
-- look the rvar up in one map, find it in the other.  That is exactly what
-- `SameTy` asserts, and `same-target-unique` (strong.Ctx) already makes it
-- a function on a name map with `Unique` names — which both rules already
-- carry.  Stating it as a premise therefore costs one premise of a
-- judgement `env` already uses, and computing it instead would put a
-- PARTIAL, lookup-based function inside a contractum.

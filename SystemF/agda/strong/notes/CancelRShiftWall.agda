module strong.notes.CancelRShiftWall where

-- File Charter:
--   * The record of a THIRD crossing defect, found by the stage-2
--     preservation port (2026-09-19): `CancelR`'s re-spelling premise is
--     read in the WRONG conversion context, and consequently omits the
--     morphism's own representation-bind shift.
--   * It exhibits a CONCRETE well-typed redex, with every premise of the
--     rule satisfied, whose CONTRACTUM has no typing derivation.
--   * NOT repaired.  A rule change is Jeremy's call; this module records
--     the wall, and `strong.proof.MoveScope` keeps `CancelRCase` as the
--     open case it is.
--
-- WHAT THE RULE SAYS (strong.Reduction):
--
--   CancelR : … → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
--     → SameTy Δ⋉ᶜ A′ Δᶜ A
--     → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A
--     → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
--         -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫
--
-- WHAT `env` DEMANDS OF THE CONTRACTUM.  Write n = numBinds Θ₁ and let R
-- be the representation `A` denotes in `Δᶜ`.  The OUTER layer's `mkId A`
-- forces the inner boundary's exterior type to denote R; the INNER
-- layer's own `SameTyExt n` premise then forces `mkId A′`'s type to
-- denote `shiftBy n R`, because the inner boundary's conversion context
-- `Δ⋉ᶜ` lies `n` representation binders inside its exterior.  The rule,
-- however, gives `A′` the UNSHIFTED reading: `SameTy Δ⋉ᶜ A′ Δᶜ A` says
-- `A′` denotes R itself.  A representation reading is unique
-- (`same-rep-unique`), so the two are compatible only when
-- `shiftBy n R ≡ R` — that is, only when `n ≡ 0` or R has no free
-- representation variable.
--
-- WHY NO EXAMPLE SAW IT.  Every `CancelR` in the twelve runs cancels a
-- boundary minted by `Peel`, whose morphism is `dualMorph Θ` — and
-- `binds (dualMorph Θ) ≡ []`, so n is 0 there.  The identities the
-- unwinding tower mints are moreover at first-order types, where R is
-- closed and the shift is invisible a second time.
--
-- WHAT THE OLD DESIGN DID.  `proof/MoveScope.agda`'s retired
-- `preserve-CancelR` minted `mkId (shiftBy (numBinds Θ₁) A)` on the inner
-- layer, NOT `mkId A`: the shift was explicit there, because the old
-- masked-entry contexts let the contractum COMPUTE the inner spelling.
-- The two-universe design cannot compute it — the crossing is a partial
-- lookup (notes/ForallPayloadWall §1) — so the rule must CARRY it, and
-- the premise that carries it is the one stated against the wrong
-- context.
--
-- IS THE CONFIGURATION REACHABLE?  NOT SETTLED, and the question is the
-- second repair path.  The redex below is well typed and the rule fires
-- on it, which is all `CancelRCase` quantifies over; but no closed
-- program is exhibited that reduces TO it.  A bare `seal X` conversion is
-- minted by exactly one rule — `Peel`, on the crossing argument — whose
-- frame is `dualMorph Θ`, and `binds (dualMorph Θ) ≡ []`.  So a REACHABLE
-- `CancelR` redex may always have `numBinds Θ₁ ≡ 0`, in which case the
-- rule is sound where it fires and what is wrong is only the statement.
-- The two repairs are therefore: carry the shifted premise (below), or
-- prove and carry the invariant `numBinds Θ₁ ≡ 0`.  Both are rule-level
-- decisions.
--
-- THE SHAPE OF THE REPAIR (not installed).  `IdPush` already carries the
-- analogous premise against the INNER boundary's conversion context,
--
--   IdPush  … → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → … → SameTy Δ⋉ᶜ (` X′) Δ₁ᶜ (` X) → …
--
-- and `Δ₁ᶜ` is exactly where the shifted reading lives.  The uniform
-- premise for `CancelR` is therefore `SameTy Δ⋉ᶜ A′ Δ₁ᶜ Aᵢ` with `Aᵢ`
-- the source of the cancelled `seal X`, together with the reading
-- `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` the rule does not currently carry.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction
open import strong.proof.Preserve using (CancelRCase)

------------------------------------------------------------------------
-- 1. The configuration
------------------------------------------------------------------------

-- Representation 0 is REPRESENTED BY representation 1 — the shape a type
-- application at a type VARIABLE produces (`f [Y]` under a later `Λ`).
-- That is what makes R a variable rather than a closed type, and the
-- shift therefore visible.
Ξ* : RepCtx
Ξ* = bindR (` 0) ∷ bindR `ℕ ∷ []

Δ* : Ctxᵗ
Δ* = Ξ* ∣ (0 ∷ 1 ∷ [])

wfΔ* : WfCtx Δ*
wfΔ* = wf-ctx reps* names* unique*
  where
  reps* : WfRepCtx Ξ*
  reps* = wf-bindR (wfᴿ-var (free-ref here))
            (wf-bindR wfᴿ-ℕ wf-reps[])

  names* : ValidNames Ξ* (0 ∷ 1 ∷ [])
  names* here = bindR (` 0) , here
  names* (there here) = bindR `ℕ , there here

  unique* : Unique (0 ∷ 1 ∷ [])
  unique* = unique∷ (fresh∷ (λ ()) fresh[]) (unique∷ fresh[] unique[])

-- The OUTER morphism is trivial: it is the inner morphism's bind block
-- that the rule mis-crosses, and a trivial outer one keeps every context
-- in the example computable.
Θ₂* : CtxMorph
Θ₂* = morph [] []

-- The INNER morphism binds ONE representation variable.  This is the only
-- thing the twelve runs never do at a `CancelR`.
Θ₁* : CtxMorph
Θ₁* = morph (`ℕ ∷ []) []

-- `Δ₁*` is at once the inner boundary's conversion context, its interior,
-- and — since Θ₂* is trivial — the merged frame's conversion context.
Δ₁* : Ctxᵗ
Δ₁* = (bindR `ℕ ∷ Ξ*) ∣ (1 ∷ 2 ∷ [])

------------------------------------------------------------------------
-- 2. The redex, well typed
------------------------------------------------------------------------

-- A closed value at the abstract name `` ` 1 `` of Δ₁*: a numeral sealed
-- at the binder that name denotes.
V* : Term
V* = ($ 7) ⟪ morph [] [] , seal 1 ⟫

⊢V* : Δ₁* ∣ [] ⊢ V* ⦂ ` 1
⊢V* =
  env (mw wfΔ₁* binds[] (interior changes[]) (conversion conv[]))
      ⊢$
      (conv-seal (2 , `ℕ , there here , r-there (r-there r-here) , same-ℕ))
      (`ℕ , same-ℕ , same-ℕ)
      (` 2 , same-var (there here) , same-var (there here))
      (wf-var (2 , there here))
  where
  wfΔ₁* : WfCtx Δ₁*
  wfΔ₁* =
    wf-ctx (wf-bindR wfᴿ-ℕ (wf-reps wfΔ*))
           names₁ (unique∷ (fresh∷ (λ ()) fresh[]) (unique∷ fresh[] unique[]))
    where
    names₁ : ValidNames (bindR `ℕ ∷ Ξ*) (1 ∷ 2 ∷ [])
    names₁ here = bindR (` 0) , there here
    names₁ (there here) = bindR `ℕ , there (there here)

v* : Value V*
v* = V-⟪⟫ V-$ I-seal

mw₁* : MorphWf Δ* Θ₁* Δ₁* Δ₁*
mw₁* = mw wfΔ* (binds∷ wfᴿ-ℕ binds[])
          (interior changes[]) (conversion conv[])

mw₂* : MorphWf Δ* Θ₂* Δ* Δ*
mw₂* = mw wfΔ* binds[] (interior changes[]) (conversion conv[])

-- `Δ₁* ∋ 0 := ` 1`: ordinary 0 names representation 1, whose payload is
-- `` ` 2 ``, which is `` ` 1 `` read on Δ₁*'s name map.
d₁* : Δ₁* ∋ 0 := ` 1
d₁* = 1 , ` 2 , here , r-there r-here , same-var (there here)

-- `Δ* ∋ 0 := ` 1`: the SAME binder, one bind block out.
d₂* : Δ* ∋ 0 := ` 1
d₂* = 0 , ` 1 , here , r-here , same-var (there here)

⊢redex* : Δ* ∣ [] ⊢
    (V* ⟪ Θ₁* , seal 0 ⟫) ⟪ Θ₂* , unseal 0 ⟫ ⦂ ` 1
⊢redex* =
  env mw₂*
      (env mw₁* ⊢V* (conv-seal d₁*)
           (` 2 , same-var (there here) , same-var (there here))
           (` 0 , same-var here , same-var here)
           (wf-var (0 , here)))
      (conv-unseal d₂*)
      (` 0 , same-var here , same-var here)
      (` 1 , same-var (there here) , same-var (there here))
      (wf-var (1 , there here))

------------------------------------------------------------------------
-- 3. Every premise of the rule is satisfied
------------------------------------------------------------------------

r⋉* : extendReps (binds Θ₂*) Δ* ⊢ᶜ Θ₁* ⋉ Θ₂* ⇒ Δ₁*
r⋉* = conversion conv[]

r₂* : Δ* ⊢ᶜ Θ₂* ⇒ Δ*
r₂* = conversion conv[]

-- THE PREMISE AT ISSUE.  `A = ` 1` denotes representation 1 on Δ*; the
-- merged frame's conversion context spells that representation `` ` 0 ``.
-- So the premise HAS a witness, and the rule FIRES.
smA* : SameTy Δ₁* (` 0) Δ* (` 1)
smA* = ` 1 , same-var here , same-var (there here)

-- and the step itself
step* : Δ* ⊢ (V* ⟪ Θ₁* , seal 0 ⟫) ⟪ Θ₂* , unseal 0 ⟫
  -→ (V* ⟪ Θ₁* ⋉ Θ₂* , mkId (` 0) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫
step* = CancelR v* r⋉* smA* r₂* d₂*

------------------------------------------------------------------------
-- 4. The contractum has NO typing derivation
------------------------------------------------------------------------

-- The outer `mkId (` 1)` pins the inner boundary's exterior type to
-- representation 1.  The inner `env`'s `SameTyExt 1` then asks for
-- `shiftBy 1 (` 1) ≡ ` 2` where the inner `mkId (` 0)` delivers
-- representation 1.  `1 ≢ 2`, and that is the whole refutation.
no-cancel-contractum :
  ¬ (Δ* ∣ [] ⊢
       (V* ⟪ Θ₁* ⋉ Θ₂* , mkId (` 0) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫
       ⦂ ` 1)
no-cancel-contractum
  (env mwR (env mw⋉ ⊢V′ ⊢c′ sameᵢ′ sameₑ′ wE′) ⊢c sameᵢ sameₑ wE)
  with interior-functional (mw-interior mwR) (interior changes[])
     | conversion-functional (mw-conversion mwR) (conversion conv[])
no-cancel-contractum
  (env mwR (env mw⋉ ⊢V′ ⊢c′ sameᵢ′ sameₑ′ wE′) ⊢c sameᵢ sameₑ wE)
  | refl | refl
  with conversion-functional (mw-conversion mw⋉) r⋉* | ⊢c | ⊢c′
no-cancel-contractum
  (env mwR (env mw⋉ ⊢V′ ⊢c′ sameᵢ′ sameₑ′ wE′) ⊢c sameᵢ sameₑ wE)
  | refl | refl | refl | conv-idv _ | conv-idv _
  with sameᵢ | sameₑ′
no-cancel-contractum
  (env mwR (env mw⋉ ⊢V′ ⊢c′ sameᵢ′ sameₑ′ wE′) ⊢c sameᵢ sameₑ wE)
  | refl | refl | refl | conv-idv _ | conv-idv _
  | (R₁ , pB , same-var (there here)) | (R₂ , pB₂ , q₂)
  with same-rep-unique pB pB₂
no-cancel-contractum
  (env mwR (env mw⋉ ⊢V′ ⊢c′ sameᵢ′ sameₑ′ wE′) ⊢c sameᵢ sameₑ wE)
  | refl | refl | refl | conv-idv _ | conv-idv _
  | (R₁ , pB , same-var (there here)) | (R₂ , pB₂ , q₂)
  | refl with q₂
no-cancel-contractum
  (env mwR (env mw⋉ ⊢V′ ⊢c′ sameᵢ′ sameₑ′ wE′) ⊢c sameᵢ sameₑ wE)
  | refl | refl | refl | conv-idv _ | conv-idv _
  | (R₁ , pB , same-var (there here)) | (R₂ , pB₂ , q₂)
  | refl | same-var ()

------------------------------------------------------------------------
-- 5. Hence the stage-2 case, AS STATED, is refuted
------------------------------------------------------------------------

-- `CancelRCase` (strong.proof.Preserve §4) is the rule's premises and the
-- redex's typing in, the contractum's typing out.  §3 supplies the
-- premises and §2 the typing; §4 refutes the output.
cancelR-case-false : ¬ CancelRCase
cancelR-case-false cancel =
  no-cancel-contractum (cancel wfΔ* v* r⋉* smA* r₂* d₂* ⊢redex*)

module strong.notes.CancelRShiftWall where

-- File Charter:
--   * THE WALL, and the record of the repair that answered it.  Found by
--     the stage-2 preservation port (2026-09-19): `CancelR`'s re-spelling
--     premise was read in the WRONG conversion context, and consequently
--     omitted the morphism's own representation-bind shift.
--   * REPAIRED THE SAME DAY, with Jeremy's approval — repair (a), the
--     premise read at Θ₁'s own conversion context.  `strong.Reduction`
--     carries the repaired rule and
--     `strong.proof.MoveScope.preserve-CancelR` proves the preservation
--     case it generates.  See notes/DECISIONS.md, 2026-09-19.
--   * WHAT SURVIVES HERE, all still machine-checked: the `Δ*`
--     configuration (§1), the well-typed redex (§2), the premises (§3),
--     the shift incompatibility at the core of the defect (§4), the
--     refutation of the OLD stage-2 statement — stated against a LOCAL
--     copy of that statement, because the rule it came from no longer
--     exists (§5), and the repaired step with its now-typeable
--     contractum, on this very configuration (§6).
--
-- The local-copy device is the repo's usual one for a retired design:
-- `notes/ReUnlockWall.agda` states the pre-`conv-unlock-live` conversion
-- judgement locally in the same way, so that `no-old-rewind-conv` stays a
-- checked refutation rather than prose.
--
-- WHAT THE RULE SAID, BEFORE (strong.Reduction, until 2026-09-19):
--
--   CancelR : … → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
--     → SameTy Δ⋉ᶜ A′ Δᶜ A                   -- ← read at the OUTER Δᶜ
--     → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A
--     → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
--         -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫
--
-- WHAT `env` DEMANDS OF THE CONTRACTUM.  Write n = numBinds Θ₁ and let R
-- be the representation `A` denotes in `Δᶜ`.  The OUTER layer's `mkId A`
-- forces the inner boundary's exterior type to denote R; the INNER
-- layer's own `SameTyExt n` premise then forces `mkId A′`'s type to
-- denote `shiftBy n R`, because the inner boundary's conversion context
-- `Δ⋉ᶜ` lies `n` representation binders inside its exterior.  The old
-- rule, however, gave `A′` the UNSHIFTED reading: `SameTy Δ⋉ᶜ A′ Δᶜ A`
-- says `A′` denotes R itself.  A representation reading is unique
-- (`same-rep-unique`), so the two are compatible only when
-- `shiftBy n R ≡ R` — that is, only when `n ≡ 0` or R has no free
-- representation variable.  That is the whole defect, and §4 checks it on
-- `Δ*`.
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
-- the premise that carried it was stated against the wrong context.
--
-- THE TWO REPAIR PATHS, AND WHY (a) WON.  Path (b) was to prove and carry
-- the invariant `numBinds Θ₁ ≡ 0` — the hope being that a REACHABLE
-- `CancelR` redex always has it, since a bare `seal X` is minted by
-- `Peel` on the crossing argument, whose frame is `dualMorph Θ`.  That
-- hope was wrong: `Peel` mints TWO boundaries and only the ARGUMENT's
-- carries the dual, so `notes/CancelRReachabilityWitness.agda` reaches
-- this configuration in nine steps from a closed, plain source program.
-- Path (b) is closed; path (a) — carry the shifted premise, below — is
-- what Jeremy approved and what §6 checks here.
--
-- THE REPAIR, AS INSTALLED.  `IdPush` already carried the analogous
-- premise against the INNER boundary's conversion context,
--
--   IdPush  … → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → …
--     → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ → …
--
-- and `Δ₁ᶜ` is exactly where the shifted reading lives.  `CancelR` now
-- carries `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ`, `Δ₁ᶜ ∋ X := Aᵢ` and
-- `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ`, with `Aᵢ` the source of the
-- cancelled
-- `seal X` — a premise block premise-isomorphic to `IdPush`'s.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.proof.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction
open import strong.proof.MoveScope using (preserve-CancelR)

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
-- that the rule mis-crossed, and a trivial outer one keeps every context
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
-- 3. The context readings, shared by the old and the repaired premises
------------------------------------------------------------------------

ri* : Δ* ⊢ⁱ Θ₂* ⇒ Δ*
ri* = interior changes[]

r₁* : Δ* ⊢ᶜ Θ₁* ⇒ Δ₁*
r₁* = conversion conv[]

r⋉* : extendReps (binds Θ₂*) Δ* ⊢ᶜ Θ₁* ⋉ Θ₂* ⇒ Δ₁*
r⋉* = conversion conv[]

r₂* : Δ* ⊢ᶜ Θ₂* ⇒ Δ*
r₂* = conversion conv[]

-- THE PREMISE AT ISSUE, in the OLD spelling.  `A = ` 1` denotes
-- representation 1 on Δ*; the merged frame's conversion context spells
-- that representation `` ` 0 ``.  So the old premise HAD a witness, and
-- the old rule FIRED.
smA* : Δ₁* ⊢ ` 0 ≈ ` 1 ⊣ Δ*
smA* = ` 1 , same-var here , same-var (there here)

-- THE SAME PREMISE, REPAIRED.  Read from the cancelled seal's own source
-- at `Δ₁*` instead, and the witness is `` ` 1 ``, which denotes
-- representation 2 — the SHIFTED one.
smAᵢ* : Δ₁* ⊢ ` 1 ≈ ` 1 ⊣ Δ₁*
smAᵢ* = ` 2 , same-var (there here) , same-var (there here)

------------------------------------------------------------------------
-- 4. The shift incompatibility, at the core of the defect
------------------------------------------------------------------------

-- The inner boundary's `SameTyExt 1` compares the exterior reading
-- against `shiftRep 1` of it, and on `Δ*` the outer layer's reading is
-- the representation VARIABLE `` ` 1 ``.  So what the inner layer must
-- denote is `` ` 2 ``, not `` ` 1 ``.
shift-moves-it : shiftRep 1 (` 1) ≢ ` 1
shift-moves-it ()

-- The OLD spelling `` ` 0 `` denotes representation 1 at `Δ₁*` …
old-spelling-denotes : Δ₁* ⊢ᶜ ` 0 ~ ` 1
old-spelling-denotes = same-var here

-- … and nothing at `Δ₁*` spelled `` ` 0 `` can denote anything else
-- (`same-rep-unique` one witness down), so the inner layer's demand for
-- `` ` 2 `` is UNSATISFIABLE by the old premise's answer.
no-0-denotes-2 : ¬ (Δ₁* ⊢ᶜ ` 0 ~ ` 2)
no-0-denotes-2 (same-var ())

-- The REPAIRED spelling `` ` 1 `` denotes exactly `` ` 2 ``.
new-spelling-denotes : Δ₁* ⊢ᶜ ` 1 ~ shiftRep 1 (` 1)
new-spelling-denotes = same-var (there here)

-- The contractum the OLD rule built therefore has NO typing derivation.
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
-- 5. Hence the OLD stage-2 case is refuted — a LOCAL statement
------------------------------------------------------------------------

-- `CancelRCase°` is `strong.proof.Preserve.CancelRCase` AS IT STOOD on
-- 2026-09-19 before the repair — the rule's premises and the redex's
-- typing in, the contractum's typing out.  It is written out here rather
-- than imported because the rule that generated it no longer exists, and
-- a refutation that cannot be re-run is not evidence.  The one line that
-- matters is `SameTy Δ⋉ᶜ A′ Δᶜ A`: read at the OUTER conversion context.
CancelRCase° : Set
CancelRCase° = ∀ {Δ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′ C}
  → WfCtx Δ → Value V
  → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
  → Δ⋉ᶜ ⊢ A′ ≈ A ⊣ Δᶜ
  → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
  → Δᶜ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢
      (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫)
        ⟪ rewind Θ₂ , mkId A ⟫ ⦂ C

-- §3 supplies the premises and §2 the typing; §4 refutes the output.
cancelR-case°-false : ¬ CancelRCase°
cancelR-case°-false cancel =
  no-cancel-contractum (cancel wfΔ* v* r⋉* smA* r₂* d₂* ⊢redex*)

------------------------------------------------------------------------
-- 6. THE REPAIRED RULE, ON THIS CONFIGURATION
------------------------------------------------------------------------

-- The repaired rule fires here too — the wall was never about firing —
-- but it mints `mkId (` 1)` on the inner layer where the old rule minted
-- `mkId (` 0)`.
repaired-step : Δ* ⊢ (V* ⟪ Θ₁* , seal 0 ⟫) ⟪ Θ₂* , unseal 0 ⟫
  -→ (V* ⟪ Θ₁* ⋉ Θ₂* , mkId (` 1) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫
repaired-step = CancelR v* ri* r₁* d₁* r⋉* smAᵢ* r₂* d₂*

-- And its contractum IS well typed, by the preservation case the repaired
-- rule generates.  The wall is answered on the configuration that raised
-- it, by the theorem rather than by a hand-built derivation.
repaired-contractum-⊢ : Δ* ∣ [] ⊢
    (V* ⟪ Θ₁* ⋉ Θ₂* , mkId (` 1) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫ ⦂ ` 1
repaired-contractum-⊢ =
  preserve-CancelR wfΔ* v* ri* r₁* d₁* r⋉* smAᵢ* r₂* d₂* ⊢redex*

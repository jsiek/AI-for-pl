module strong.proof.MwUObstruct where

-- THE PROPOSED TIGHTNESS REPAIR, REFUTED — with witnesses.
--
-- proof/DualTightness.agda machine-checks the defect: `dualScope` DROPS
-- the crossed boundary's `unlock` entries, so `Peel` GAINS SCOPE.  The
-- repair on the table (Jeremy, 2026-09-06) is three coupled changes:
--
--   (1) `mw-u` requires the slot to be MASKED —
--       `mw-u : Δ ∋e X , masked E → Δ ⊢ᵐ Θ → Δ ⊢ᵐ (unlock X ∷ Θ)`
--       (no vacuous unlocks);
--   (2) `dualScope n (unlock X ∷ Θ) = lock (n + X) ∷ dualScope n Θ`
--       (restore what Θ unlocked);
--   (3) the outer boundary of CancelR/IdPush becomes BINDS-ONLY
--       (`bindsOnly Θ₂` in place of `dropLocks Θ₂`), so the moved scope
--       duplicates no unlock.
--
-- THIS MODULE ESTABLISHES:
--
--   §1  (2) FORCES (1).  With (2) alone, `Peel` OVER-masks at a vacuous
--       unlock and `preserve-Peel` is FALSE — witness: a WELL-TYPED redex
--       whose contractum is ill typed.
--   §2  (1) REFUTES `⊢ᵐ-⊑`, hence `⊢retag` (strong.TermSubst) — the
--       transport `Δ ⊑ Δ′` cannot carry an `unlock` across a refinement
--       that UNMASKS the slot it names.
--   §3  (1) REFUTES THE SCOPE MOVE, at `Θ₂` locking what `Θ₁` unlocks:
--       a WELL-TYPED IdPush redex whose contractum's merged frame
--       `Θ₁ ⋉ Θ₂ = unlock 1 ∷ lock 1 ∷ []` is read over a type context
--       where slot 1 is a PLAIN BINDER.  Both candidate outer frames
--       (`dropLocks Θ₂` and `bindsOnly Θ₂`) fail on it.
--   §4  … and the MIRROR, at `Θ₂` unlocking what `Θ₁` locks.
--   §5  IF `⊢ᵐ` were made SEQUENTIAL (the only reading of §3/§4 that
--       survives), THEN `dualScope` must also REVERSE its list: the
--       same-order dual is not an inverse.
--   §6  … and `bindsOnly`'s own `⊢ᵐ` then fails, because a `bind`'s rep is
--       read on the PLAIN exterior (simultaneity) while the move needs it
--       read past the frame's own unlocks.
--
-- THE SHAPE OF THE OBSTRUCTION, in one line: `⊢ᵐ` is SIMULTANEOUS (every
-- entry's premise is read on the PLAIN exterior Δ) while `scope` is
-- SEQUENTIAL (the list is applied head-last).  Under (1) `mw-l` and `mw-u`
-- become EXACT COMPLEMENTS — a lock names a NAMEABLE slot, an unlock a
-- MASKED one — so no simultaneous `⊢ᵐ` can hold of a list that both locks
-- and unlocks the same slot.  The scope move `_⋉_` builds exactly such
-- lists.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst using (wkᴹ)
open import strong.Reduction
open import strong.proof.DualTightness using (Δᵤ; Θᵤ)
open import strong.proof.MoveScope using (interior-⋉; convCtx-⋉; scope-scopeOf)

------------------------------------------------------------------------
-- §0  The three proposed definitions, LOCALLY
------------------------------------------------------------------------

-- (2): the dual RESTORES what Θ unlocked, keeping `lock ↦ unlock`.
dualScope′ : ℕ → CtxMorph → CtxMorph
dualScope′ n []             = []
dualScope′ n (bind A ∷ Θ)   = dualScope′ n Θ
dualScope′ n (unlock X ∷ Θ) = lock   (n + X) ∷ dualScope′ n Θ
dualScope′ n (lock X ∷ Θ)   = unlock (n + X) ∷ dualScope′ n Θ

dual′ : CtxMorph → CtxMorph
dual′ Θ = hideBinds (numBinds Θ) ++ dualScope′ (numBinds Θ) Θ

-- (3): the outer boundary keeps ONLY the binds.
bindsOnly : CtxMorph → CtxMorph
bindsOnly []             = []
bindsOnly (bind A ∷ Θ)   = bind A ∷ bindsOnly Θ
bindsOnly (unlock X ∷ Θ) = bindsOnly Θ
bindsOnly (lock X ∷ Θ)   = bindsOnly Θ

------------------------------------------------------------------------
-- §1  (2) FORCES (1):  the vacuous unlock, and preserve-Peel REFUTED
------------------------------------------------------------------------

-- ON JEREMY'S WITNESS (proof/DualTightness) THE REPAIR WORKS.  Θᵤ unlocks
-- a slot Δᵤ MASKS, so the restored lock lands where it should and the
-- crossing frame is Δᵤ EXACTLY — the contractum's argument is refused,
-- which is tightness.
_ : dual′ Θᵤ ≡ lock 0 ∷ []
_ = refl

_ : interior (dual′ Θᵤ) (interior Θᵤ Δᵤ) ≡ Δᵤ
_ = refl

-- BUT `mw-u` AS IT STANDS PERMITS A VACUOUS UNLOCK — a slot that is NOT
-- masked — and there the restored lock MASKS A SLOT THE EXTERIOR LEFT
-- NAMEABLE.  Δᵥ has one PLAIN binder; Θᵥ unlocks it for nothing.
Δᵥ : Ctxᵗ
Δᵥ = bind `ℕ ∷ []

Θᵥ : CtxMorph
Θᵥ = unlock 0 ∷ []

⊢ᵐΘᵥ : Δᵥ ⊢ᵐ Θᵥ                  -- legal today: an unlock claims nothing
⊢ᵐΘᵥ = mw-u ez mw[]

_ : interior Θᵥ Δᵥ ≡ Δᵥ          -- and does nothing
_ = refl

-- V₀ = λx:ℕ. 7,  crossed at  (ℕ⇒ℕ) inside  ⇝  (Z⇒ℕ) outside
V₀ : Term
V₀ = ƛ `ℕ ∙ ($ 7)

c₀ : Conv
c₀ = unseal 0 ↦ id `ℕ

-- W₀ = 3 sealed at Z's binder: a VALUE of type ` 0 at Δᵥ
W₀ : Term
W₀ = ($ 3) ⟪ [] , seal 0 ⟫

⊢W₀ : Δᵥ ∣ [] ⊢ W₀ ⦂ ` 0
⊢W₀ = env mw[] ⊢$ (conv-seal ez) (wf-var (bind `ℕ , ez , nameable-b))

Redexᵥ : Term
Redexᵥ = (V₀ ⟪ Θᵥ , c₀ ⟫) · W₀

-- THE REDEX IS WELL TYPED.
⊢Redexᵥ : Δᵥ ∣ [] ⊢ Redexᵥ ⦂ `ℕ
⊢Redexᵥ =
  ⊢· (env ⊢ᵐΘᵥ (⊢ƛ wf-ℕ ⊢$)
          (conv-fun (conv-unseal ez) (conv-id base-ℕ))
          (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b)) wf-ℕ))
     ⊢W₀

stepᵥ : Δᵥ ⊢ Redexᵥ -→ (V₀ · (wkᴹ 0 W₀ ⟪ dual Θᵥ , unseal 0 ⟫)) ⟪ Θᵥ , id `ℕ ⟫
stepᵥ = Peel V-ƛ (V-⟪⟫ V-$ I-seal)

-- UNDER (2) THE CROSSING FRAME MASKS Z, WHICH Δᵥ DID NOT.
_ : dual′ Θᵥ ≡ lock 0 ∷ []
_ = refl

_ : interior (dual′ Θᵥ) (interior Θᵥ Δᵥ) ≡ masked (bind `ℕ) ∷ []
_ = refl

-- … so the crossing argument does not retype, and the contractum is ILL
-- TYPED.  `preserve-Peel` is FALSE under (2) alone: hence (1).
¬⊢W₀-inside : ∀ {A} → ¬ (masked (bind `ℕ) ∷ [] ∣ [] ⊢ W₀ ⦂ A)
¬⊢W₀-inside (env _ _ _ (wf-var (_ , ez , ())))

------------------------------------------------------------------------
-- §2  (1) REFUTES `⊢ᵐ-⊑`, HENCE `⊢retag`
------------------------------------------------------------------------

-- `⊢retag : Δ ⊑ Δ′ → Δ ∣ Γ ⊢ M ⦂ A → Δ′ ∣ Γ ⊢ M ⦂ A` (strong.TermSubst)
-- runs `⊢ᵐ-⊑` on every boundary it crosses.  Under (1) an `unlock X`
-- CLAIMS that X is masked, and `le-mu` — the ⊑ᵉ clause that RE-EXPOSES a
-- concealed slot (Cancel's own refinement) — destroys the claim.
Δₘ Δₙ : Ctxᵗ
Δₘ = masked (bind `ℕ) ∷ []
Δₙ = bind `ℕ ∷ []

refine-mn : Δₘ ⊑ Δₙ
refine-mn = le∷ (le-mu le-bb nameable-b) le[]

M₂ : Term
M₂ = ($ 3) ⟪ unlock 0 ∷ [] , id `ℕ ⟫

⊢M₂ : Δₘ ∣ [] ⊢ M₂ ⦂ `ℕ
⊢M₂ = env (mw-u ez mw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

-- but slot 0 of Δₙ is a PLAIN binder, so `mw-u` under (1) has no premise
-- to offer, and `Δₙ ⊢ᵐ (unlock 0 ∷ [])` is not derivable.
no-masked-Δₙ : ∀ {E} → ¬ (Δₙ ∋e 0 , masked E)
no-masked-Δₙ ()

------------------------------------------------------------------------
-- §3  (1) REFUTES THE SCOPE MOVE — Θ₂ LOCKS WHAT Θ₁ UNLOCKS
------------------------------------------------------------------------

-- Δᵢ: slot 0 a binder at ℕ, slot 1 a binder at 𝔹.
Δᵢ : Ctxᵗ
Δᵢ = bind `ℕ ∷ bind `𝔹 ∷ []

Θ₂ᵢ : CtxMorph          -- the OUTER frame LOCKS slot 1
Θ₂ᵢ = lock 1 ∷ []

Θ₁ᵢ : CtxMorph          -- the INNER frame UNLOCKS it again
Θ₁ᵢ = unlock 1 ∷ []

_ : interior Θ₂ᵢ Δᵢ ≡ bind `ℕ ∷ masked (bind `𝔹) ∷ []
_ = refl

-- LEGAL UNDER (1): the inner unlock names a slot its OWN exterior masks.
⊢ᵐΘ₁ᵢ : interior Θ₂ᵢ Δᵢ ⊢ᵐ Θ₁ᵢ
⊢ᵐΘ₁ᵢ = mw-u (es ez) mw[]

_ : interior Θ₁ᵢ (interior Θ₂ᵢ Δᵢ) ≡ bind `ℕ ∷ bind `𝔹 ∷ []
_ = refl

-- a value of type ` 0: a numeral sealed at slot 0's binder
Vᵢ : Term
Vᵢ = ($ 5) ⟪ [] , seal 0 ⟫

Redexᵢ : Term
Redexᵢ = (Vᵢ ⟪ Θ₁ᵢ , id (` 0) ⟫) ⟪ Θ₂ᵢ , unseal 0 ⟫

-- THE REDEX IS WELL TYPED.
⊢Redexᵢ : Δᵢ ∣ [] ⊢ Redexᵢ ⦂ `ℕ
⊢Redexᵢ =
  env (mw-l (bind `𝔹 , es ez , nameable-b) mw[])
      (env ⊢ᵐΘ₁ᵢ
           (env mw[] ⊢$ (conv-seal ez) (wf-var (bind `ℕ , ez , nameable-b)))
           (conv-idv (bind `ℕ , ez , nameable-b))
           (wf-var (bind `ℕ , ez , nameable-b)))
      (conv-unseal ez)
      wf-ℕ

stepᵢ : Δᵢ ⊢ Redexᵢ -→ (Vᵢ ⟪ Θ₁ᵢ ⋉ Θ₂ᵢ , unseal 0 ⟫) ⟪ dropLocks Θ₂ᵢ , mkId `ℕ ⟫
stepᵢ = IdPush (V-⟪⟫ V-$ I-seal) ez

-- THE MERGED FRAME both unlocks and locks slot 1 …
_ : _≡_ {A = CtxMorph} (Θ₁ᵢ ⋉ Θ₂ᵢ) (unlock 1 ∷ lock 1 ∷ [])
_ = refl

-- … and BOTH candidate outer frames leave it read over Δᵢ, where slot 1
-- is a PLAIN binder.  (Θ₂ᵢ has neither binds nor unlocks, so `dropLocks`
-- and `bindsOnly` agree here.)
_ : _≡_ {A = CtxMorph} (dropLocks Θ₂ᵢ) []
_ = refl

_ : _≡_ {A = CtxMorph} (bindsOnly Θ₂ᵢ) []
_ = refl

_ : interior (dropLocks Θ₂ᵢ) Δᵢ ≡ Δᵢ
_ = refl

-- THE OBSTRUCTION: under (1) `Δᵢ ⊢ᵐ (unlock 1 ∷ lock 1 ∷ [])` has no
-- derivation, because `mw-u` would need slot 1 of Δᵢ to be MASKED.
no-masked-Δᵢ : ∀ {E} → ¬ (Δᵢ ∋e 1 , masked E)
no-masked-Δᵢ d with ∋e-det d (es ez)
... | ()

-- (The frame ITSELF is right: the merged frame's interior is the redex's
-- interior on the nose.  It is only `⊢ᵐ`, read simultaneously, that
-- refuses it.)
_ : interior (Θ₁ᵢ ⋉ Θ₂ᵢ) (interior (dropLocks Θ₂ᵢ) Δᵢ)
      ≡ interior Θ₁ᵢ (interior Θ₂ᵢ Δᵢ)
_ = refl

------------------------------------------------------------------------
-- §3b  WHAT (3) *DOES* BUY — the frame lemmas become EQUALITIES
------------------------------------------------------------------------

-- The positive half of the proposal, proven in general and independent of
-- `_⊢ᵐ_`: with a BINDS-ONLY outer frame the move is EXACT.  `frame-move`
-- (proof/MoveScope) is a ⊑ only because `dropLocks` retains Θ₂'s unlocks
-- and so applies them twice; drop them and the two frames coincide on the
-- nose, and the value crosses by `subst` with no `⊢retag` at all.
repsOf-bindsOnly : (Θ : CtxMorph) → repsOf (bindsOnly Θ) ≡ repsOf Θ
repsOf-bindsOnly []             = refl
repsOf-bindsOnly (bind A ∷ Θ)   = cong (A ∷_) (repsOf-bindsOnly Θ)
repsOf-bindsOnly (unlock X ∷ Θ) = repsOf-bindsOnly Θ
repsOf-bindsOnly (lock X ∷ Θ)   = repsOf-bindsOnly Θ

scope-bindsOnly : (Θ : CtxMorph) (Δ : Ctxᵗ) → scope (bindsOnly Θ) Δ ≡ Δ
scope-bindsOnly []             Δ = refl
scope-bindsOnly (bind A ∷ Θ)   Δ = scope-bindsOnly Θ Δ
scope-bindsOnly (unlock X ∷ Θ) Δ = scope-bindsOnly Θ Δ
scope-bindsOnly (lock X ∷ Θ)   Δ = scope-bindsOnly Θ Δ

interior-bindsOnly : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (bindsOnly Θ) Δ ≡ pushBinds (repsOf Θ) Δ
interior-bindsOnly Θ Δ
  rewrite repsOf-bindsOnly Θ | scope-bindsOnly Θ Δ = refl

-- (b), FIRST HALF: the value's frame is preserved EXACTLY.
interior-⋉-bindsOnly : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → interior (Θ₁ ⋉ Θ₂) (interior (bindsOnly Θ₂) Δ)
      ≡ interior Θ₁ (interior Θ₂ Δ)
interior-⋉-bindsOnly Θ₁ Θ₂ Δ
  rewrite interior-bindsOnly Θ₂ Δ =
  trans (interior-⋉ Θ₁ Θ₂ (pushBinds (repsOf Θ₂) Δ))
        (cong (λ Ξ → pushBinds (repsOf Θ₁) (scope Θ₁ Ξ))
              (scope-scopeOf (repsOf Θ₂) Θ₂ Δ))

-- (b), SECOND HALF: the conversion context of the moved frame is the
-- redex's own inner conversion context with Θ₂'s LOCKS lifted off — which
-- is the whole point of the move (the rep the swapped conversion presents
-- is read OUTSIDE those locks).
unlockedScope-scopeOf : (As : List Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → unlockedScope (scopeOf (length As) Θ) (pushBinds As Δ)
      ≡ pushBinds As (unlockedScope Θ Δ)
unlockedScope-scopeOf As []             Δ = refl
unlockedScope-scopeOf As (bind A ∷ Θ)   Δ = unlockedScope-scopeOf As Θ Δ
unlockedScope-scopeOf As (lock X ∷ Θ)   Δ = unlockedScope-scopeOf As Θ Δ
unlockedScope-scopeOf As (unlock X ∷ Θ) Δ =
  trans (cong (unmask (length As + X)) (unlockedScope-scopeOf As Θ Δ))
        (updateAt-pushBinds unmaskEnt As X (unlockedScope Θ Δ))

convCtx-⋉-bindsOnly : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → convCtx (Θ₁ ⋉ Θ₂) (interior (bindsOnly Θ₂) Δ)
      ≡ convCtx Θ₁ (convCtx Θ₂ Δ)
convCtx-⋉-bindsOnly Θ₁ Θ₂ Δ
  rewrite interior-bindsOnly Θ₂ Δ =
  trans (convCtx-⋉ Θ₁ Θ₂ (pushBinds (repsOf Θ₂) Δ))
        (cong (λ Ξ → pushBinds (repsOf Θ₁) (unlockedScope Θ₁ Ξ))
              (unlockedScope-scopeOf (repsOf Θ₂) Θ₂ Δ))

-- SO THE ONLY CASUALTY IS `⊢ᵐ-⋉`.  §3 and §4 are exactly that: the two
-- frames the move builds are semantically right and `_⊢ᵐ_`-illegal.

------------------------------------------------------------------------
-- §4  THE MIRROR — Θ₂ UNLOCKS WHAT Θ₁ LOCKS
------------------------------------------------------------------------

-- Δⱼ: slot 0 a MASKED binder at ℕ, slot 1 a plain binder at ℕ.
Δⱼ : Ctxᵗ
Δⱼ = masked (bind `ℕ) ∷ bind `ℕ ∷ []

Θ₂ⱼ : CtxMorph          -- the OUTER frame UNLOCKS slot 0 …
Θ₂ⱼ = unlock 0 ∷ []

Θ₁ⱼ : CtxMorph          -- … and the INNER frame LOCKS it again
Θ₁ⱼ = lock 0 ∷ []

_ : interior Θ₂ⱼ Δⱼ ≡ bind `ℕ ∷ bind `ℕ ∷ []
_ = refl

Vⱼ : Term
Vⱼ = ($ 5) ⟪ [] , seal 1 ⟫

Redexⱼ : Term
Redexⱼ = (Vⱼ ⟪ Θ₁ⱼ , id (` 1) ⟫) ⟪ Θ₂ⱼ , unseal 1 ⟫

⊢Redexⱼ : Δⱼ ∣ [] ⊢ Redexⱼ ⦂ `ℕ
⊢Redexⱼ =
  env (mw-u ez mw[])
      (env (mw-l (bind `ℕ , ez , nameable-b) mw[])
           (env mw[] ⊢$ (conv-seal (es ez))
                (wf-var (bind `ℕ , es ez , nameable-b)))
           (conv-idv (bind `ℕ , es ez , nameable-b))
           (wf-var (bind `ℕ , es ez , nameable-b)))
      (conv-unseal (es ez))
      wf-ℕ

stepⱼ : Δⱼ ⊢ Redexⱼ -→ (Vⱼ ⟪ Θ₁ⱼ ⋉ Θ₂ⱼ , unseal 1 ⟫) ⟪ dropLocks Θ₂ⱼ , mkId `ℕ ⟫
stepⱼ = IdPush (V-⟪⟫ V-$ I-seal) (es ez)

_ : _≡_ {A = CtxMorph} (Θ₁ⱼ ⋉ Θ₂ⱼ) (lock 0 ∷ unlock 0 ∷ [])
_ = refl

-- WITH `bindsOnly` the merged frame is read over Δⱼ, where slot 0 is
-- MASKED — so its `lock 0` has no `mw-l` premise …
_ : _≡_ {A = CtxMorph} (bindsOnly Θ₂ⱼ) []
_ = refl

¬∋tv-Δⱼ : ¬ (Δⱼ ∋tv 0)
¬∋tv-Δⱼ (_ , ez , ())

-- … and WITH `dropLocks` it is read over `convCtx Θ₂ⱼ Δⱼ`, where slot 0 is
-- a PLAIN binder — so its `unlock 0` has no `mw-u` premise under (1).
_ : interior (dropLocks Θ₂ⱼ) Δⱼ ≡ bind `ℕ ∷ bind `ℕ ∷ []
_ = refl

no-masked-cc : ∀ {E} → ¬ (interior (dropLocks Θ₂ⱼ) Δⱼ ∋e 0 , masked E)
no-masked-cc ()

------------------------------------------------------------------------
-- §5  IF `⊢ᵐ` WERE SEQUENTIAL, `dualScope` MUST ALSO REVERSE
------------------------------------------------------------------------

-- §3/§4 fail only because `⊢ᵐ` reads every entry on the PLAIN exterior.
-- The reading that survives them checks each entry against `scope Θ Δ` —
-- the type context the LATER entries have already produced, which is the
-- order `scope` applies them.  Under that reading a frame may toggle one
-- slot repeatedly, and then a SAME-ORDER dual is no longer an inverse:
-- `scope` applies its list HEAD-LAST, so undoing it must run the entries
-- BACK TO FRONT.
Θᵣ : CtxMorph
Θᵣ = unlock 0 ∷ lock 0 ∷ []

Δᵣ : Ctxᵗ
Δᵣ = bind `ℕ ∷ []

_ : scope Θᵣ Δᵣ ≡ Δᵣ                       -- lock then unlock: a no-op
_ = refl

-- the SAME-ORDER dual OVER-masks …
_ : scope (dualScope′ 0 Θᵣ) (scope Θᵣ Δᵣ) ≡ masked (bind `ℕ) ∷ []
_ = refl

¬inverse-same-order : ¬ (scope (dualScope′ 0 Θᵣ) (scope Θᵣ Δᵣ) ≡ Δᵣ)
¬inverse-same-order ()

-- … while the REVERSED one is exact.
_ : scope (unlock 0 ∷ lock 0 ∷ []) (scope Θᵣ Δᵣ) ≡ Δᵣ
_ = refl

------------------------------------------------------------------------
-- §6  … AND THEN `bindsOnly` LOSES ITS OWN `⊢ᵐ`
------------------------------------------------------------------------

-- A sequential `⊢ᵐ` must read `mw-b`'s rep sequentially too — otherwise
-- the moved frame `Θ₁ ⋉ Θ₂` has no `mw-b` premise for Θ₁'s own binders,
-- whose reps the redex only ever checked on `interior Θ₂ Δ`.  But then
-- `bindsOnly Θ₂` has no `⊢ᵐ` either: its binds are read on the PLAIN Δ,
-- where a rep naming a slot Θ₂ UNLOCKED is not well formed.
Δ₆ : Ctxᵗ
Δ₆ = masked (bind `ℕ) ∷ []

Θ₆ : CtxMorph
Θ₆ = bind (` 0) ∷ unlock 0 ∷ []

-- the rep IS well formed past the frame's own unlock …
_ : scope (unlock 0 ∷ []) Δ₆ ≡ bind `ℕ ∷ []
_ = refl

⊢ᵗ-rep-seq : scope (unlock 0 ∷ []) Δ₆ ⊢ᵗ ` 0
⊢ᵗ-rep-seq = wf-var (bind `ℕ , ez , nameable-b)

-- … and NOT on the plain exterior, which is where `bindsOnly Θ₆` reads it.
_ : _≡_ {A = CtxMorph} (bindsOnly Θ₆) (bind (` 0) ∷ [])
_ = refl

¬⊢ᵗ-rep-plain : ¬ (Δ₆ ⊢ᵗ ` 0)
¬⊢ᵗ-rep-plain (wf-var (_ , ez , ()))

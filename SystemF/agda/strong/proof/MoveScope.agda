module strong.proof.MoveScope where

-- THE SCOPE MOVE — its frame algebra, and the TWO preservation cases it
-- settles (CancelR and IdPush), UNCONDITIONALLY.
--
-- THE MOVE (strong.CtxMorph §4).  Both rules SWAP the two conversions
-- of a two-layer wrapper, so the INNER boundary stops presenting the
-- abstract name `` ` Y `` and starts presenting Y's REP.  A rep is a type
-- over the exterior; inside Θ₂'s LOCKS it need not be nameable at all,
-- and `env`'s last premise then fails — that was the wall (the old
-- proof/PreserveObstruct §4 refutation).
--
-- So the frames move with the conversions:
--
--   (V ⟪ Θ₁ , c ⟫) ⟪ Θ₂ , unseal Y ⟫
--     -→ (V ⟪ Θ₁ ⋉ Θ₂ , c′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫
--
-- `Θ₁ ⋉ Θ₂` appends Θ₂'s whole SCOPE (locks AND unlocks, in order,
-- lifted past Θ₂'s binders) at Θ₁'s TAIL, where `scope` applies it
-- FIRST; and `rewind Θ₂` is Θ₂ with its own scope UNDONE, so what is
-- left of the outer frame is the BIND PREFIX, in net effect:
--
--   scope    (rewind Θ₂) Δ ≡ Δ                          (given Δ ⊢ᵐ Θ₂)
--   interior (rewind Θ₂) Δ ≡ pushBinds (repsOf Θ₂) Δ
--
-- WHY `rewind` AND NOT `bindsOnly` / `dropLocks`.  All three have the
-- same net effect on the type context, and only `rewind` keeps its own
-- `⊢ᵐ`:
--   `dropLocks Θ₂` KEEPS Θ₂'s unlocks, so the moved copy of the same
--     unlock is then VACUOUS and `mw-u` refuses it;
--   `bindsOnly Θ₂` DELETES them, and then Θ₂'s own bind reps — read on
--     `unlockedScope Θ₂′ Δ` (`mw-b`) — lose the unlock they depend on;
--   `rewind Θ₂` keeps every entry and rewinds it, so every premise is
--     read exactly where the redex read it.
--
-- WHY IT WORKS, in one line: the moved scope re-creates Θ₂'s scope one
-- bind prefix in (`scope-scopeOf`), so the value's frame is preserved ON
-- THE NOSE — the two frame lemmas are EQUALITIES, and no `⊢retag`
-- appears in either case — while the rep the swapped conversion presents
-- is read OUTSIDE Θ₂'s locks, where `wf-shiftBy-pushBinds` supplies the
-- premise the wall used to deny.
--
--   §1  the lookup transports
--   §2  the list algebra of `scopeOf`/`rewind`/`_⋉_`
--   §3  the type-context identities
--   §4  the FRAME LEMMAS, as EQUALITIES
--   §4b why the unlocks travel too — the lock-only move, REFUTED
--   §5  `_⊢ᵐ_` for the two new frames
--   §6  the two cases

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.proof.Preserve using (CancelRCase; IdPushCase)
open import strong.proof.PeelDual
  using (⊢ᵐ-++; scope-++; unlockedScope-++; scope-dualScope; ⊢ᵐ-dualScope;
         repsOf-++; repsOf-dualScope)

------------------------------------------------------------------------
-- §1  Lookup transports
------------------------------------------------------------------------

-- A binder survives `unlockedScope`: it only unmasks (`unmaskEnt`, which fixes
-- `bind`) and skips locks, so a `bind` lookup is preserved unchanged.
unlockedScope-∋bind : ∀ (Θ : CtxMorph) {Δ Y A}
  → Δ ∋ Y := A → unlockedScope Θ Δ ∋ Y := A
unlockedScope-∋bind []              d = d
unlockedScope-∋bind (bind C ∷ Θ)    d = unlockedScope-∋bind Θ d
unlockedScope-∋bind (lock Z ∷ Θ)    d = unlockedScope-∋bind Θ d
unlockedScope-∋bind (unlock Z ∷ Θ) {Y = Y} d with Z ≟ℕ Y
... | yes refl =
  updateAt-hit  unmaskEnt unmaskEnt-comm    (unlockedScope-∋bind Θ d)
... | no  ne   =
  updateAt-miss unmaskEnt unmaskEnt-comm ne (unlockedScope-∋bind Θ d)

-- The bind prefix lifts a binder: slot Y in the tail becomes slot
-- `length As + Y` at the rep lifted past the `length As` prefix binders.
pushBinds-∋ : ∀ (As : List Ty) {Δ Y A}
  → Δ ∋ Y := A → pushBinds As Δ ∋ (length As + Y) := shiftBy (length As) A
pushBinds-∋ []       d = d
pushBinds-∋ (C ∷ As) d = es (pushBinds-∋ As d)

------------------------------------------------------------------------
-- §2  The list algebra of the move
------------------------------------------------------------------------

-- THE MOVE CARRIES NO BINDER: it moves scope entries only.
repsOf-scopeOf : (n : ℕ) (Θ : CtxMorph) → repsOf (scopeOf n Θ) ≡ []
repsOf-scopeOf n []             = refl
repsOf-scopeOf n (bind A ∷ Θ)   = repsOf-scopeOf n Θ
repsOf-scopeOf n (unlock X ∷ Θ) = repsOf-scopeOf n Θ
repsOf-scopeOf n (lock X ∷ Θ)   = repsOf-scopeOf n Θ

repsOf-⋉ : (Θ₁ Θ₂ : CtxMorph) → repsOf (Θ₁ ⋉ Θ₂) ≡ repsOf Θ₁
repsOf-⋉ []             Θ₂  = repsOf-scopeOf (numBinds Θ₂) Θ₂
repsOf-⋉ (bind A ∷ Θ₁)  Θ₂  = cong (A ∷_) (repsOf-⋉ Θ₁ Θ₂)
repsOf-⋉ (unlock X ∷ Θ₁) Θ₂ = repsOf-⋉ Θ₁ Θ₂
repsOf-⋉ (lock X ∷ Θ₁)  Θ₂  = repsOf-⋉ Θ₁ Θ₂

numBinds-⋉ : (Θ₁ Θ₂ : CtxMorph) → numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁
numBinds-⋉ Θ₁ Θ₂ = cong length (repsOf-⋉ Θ₁ Θ₂)

-- REWINDING KEEPS THE BINDERS: the inverse scope carries none.
repsOf-rewind : (Θ : CtxMorph) → repsOf (rewind Θ) ≡ repsOf Θ
repsOf-rewind Θ rewrite repsOf-++ (dualScope 0 Θ) Θ
                      | repsOf-dualScope 0 Θ = refl

numBinds-rewind : (Θ : CtxMorph) → numBinds (rewind Θ) ≡ numBinds Θ
numBinds-rewind Θ = cong length (repsOf-rewind Θ)

-- THE MOVED SCOPE, APPLIED PAST THE BIND PREFIX, IS THE ORIGINAL SCOPE
-- APPLIED UNDER IT.  This is the whole point of the index lift `n + X`,
-- and it is `updateAt-pushBinds` (strong.Ctx) once per entry.
scope-scopeOf : (As : List Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scope (scopeOf (length As) Θ) (pushBinds As Δ) ≡ pushBinds As (scope Θ Δ)
scope-scopeOf As []             Δ = refl
scope-scopeOf As (bind A ∷ Θ)   Δ = scope-scopeOf As Θ Δ
scope-scopeOf As (unlock X ∷ Θ) Δ =
  trans (cong (unmask (length As + X)) (scope-scopeOf As Θ Δ))
        (updateAt-pushBinds unmaskEnt As X (scope Θ Δ))
scope-scopeOf As (lock X ∷ Θ)   Δ =
  trans (cong (mask (length As + X)) (scope-scopeOf As Θ Δ))
        (updateAt-pushBinds masked As X (scope Θ Δ))

unlockedScope-scopeOf : (As : List Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → unlockedScope (scopeOf (length As) Θ) (pushBinds As Δ)
      ≡ pushBinds As (unlockedScope Θ Δ)
unlockedScope-scopeOf As []             Δ = refl
unlockedScope-scopeOf As (bind A ∷ Θ)   Δ = unlockedScope-scopeOf As Θ Δ
unlockedScope-scopeOf As (lock X ∷ Θ)   Δ = unlockedScope-scopeOf As Θ Δ
unlockedScope-scopeOf As (unlock X ∷ Θ) Δ =
  trans (cong (unmask (length As + X)) (unlockedScope-scopeOf As Θ Δ))
        (updateAt-pushBinds unmaskEnt As X (unlockedScope Θ Δ))

------------------------------------------------------------------------
-- §3  The type-context identities
------------------------------------------------------------------------

-- THE HEADLINE IDENTITY.  A rewound frame's SCOPE IS THE IDENTITY — this
-- is `scope-dualScope` (proof/PeelDual) at an empty bind prefix, and it
-- is where the whole design is paid for: the inverse is exact only
-- because `mw-u` refuses a vacuous unlock.
scope-rewind : (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ → scope (rewind Θ) Δ ≡ Δ
scope-rewind Θ {Δ = Δ} mw =
  trans (scope-++ (dualScope 0 Θ) Θ Δ) (scope-dualScope [] Θ mw)

interior-rewind : (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ
  → interior (rewind Θ) Δ ≡ pushBinds (repsOf Θ) Δ
interior-rewind Θ mw rewrite repsOf-rewind Θ | scope-rewind Θ mw = refl

-- The two frames of the contractum, unfolded.
interior-⋉ : (Θ₁ Θ₂ : CtxMorph) (Ξ : Ctxᵗ)
  → interior (Θ₁ ⋉ Θ₂) Ξ
      ≡ pushBinds (repsOf Θ₁) (scope Θ₁ (scope (scopeOf (numBinds Θ₂) Θ₂) Ξ))
interior-⋉ Θ₁ Θ₂ Ξ rewrite repsOf-⋉ Θ₁ Θ₂ =
  cong (pushBinds (repsOf Θ₁)) (scope-++ Θ₁ (scopeOf (numBinds Θ₂) Θ₂) Ξ)

convCtx-⋉ : (Θ₁ Θ₂ : CtxMorph) (Ξ : Ctxᵗ)
  → convCtx (Θ₁ ⋉ Θ₂) Ξ
      ≡ pushBinds (repsOf Θ₁)
          (unlockedScope Θ₁ (unlockedScope (scopeOf (numBinds Θ₂) Θ₂) Ξ))
convCtx-⋉ Θ₁ Θ₂ Ξ rewrite repsOf-⋉ Θ₁ Θ₂ =
  cong (pushBinds (repsOf Θ₁))
       (unlockedScope-++ Θ₁ (scopeOf (numBinds Θ₂) Θ₂) Ξ)

------------------------------------------------------------------------
-- §4  THE FRAME LEMMAS — EQUALITIES
------------------------------------------------------------------------

-- A rep survives `unlockedScope` and the bind prefix (`scope` would not
-- do — masking is what the wall was about).
wf-unlockedScope : ∀ {Δ A} (Θ : CtxMorph) → Δ ⊢ᵗ A → unlockedScope Θ Δ ⊢ᵗ A
wf-unlockedScope Θ w = ⊑-wf (Δ⊑unlockedScope Θ _) w

wf-convCtx : ∀ {Δ A} (Θ : CtxMorph)
  → Δ ⊢ᵗ A → convCtx Θ Δ ⊢ᵗ shiftBy (numBinds Θ) A
wf-convCtx Θ w = wf-shiftBy-pushBinds (repsOf Θ) (wf-unlockedScope Θ w)

-- … and the same at a REWOUND frame, whose bind count is Θ's own.
wf-convCtx-rewind : ∀ {Δ C} (Θ : CtxMorph) → Δ ⊢ᵗ C
  → convCtx (rewind Θ) Δ ⊢ᵗ shiftBy (numBinds Θ) C
wf-convCtx-rewind {Δ = Δ} {C = C} Θ w =
  subst (λ n → convCtx (rewind Θ) Δ ⊢ᵗ shiftBy n C)
        (numBinds-rewind Θ) (wf-convCtx (rewind Θ) w)

-- THE VALUE'S FRAME IS PRESERVED ON THE NOSE.  Everything Θ₂ masked the
-- moved scope masks again, at the same slots, in the same order, one
-- prefix further in (`scope-scopeOf`); and the outer frame contributes
-- nothing but its binders (`interior-rewind`).  So the value crosses by
-- `subst` — with `dropLocks` this was a ⊑ and needed `⊢retag` along a
-- `le-mu` step, which `mw-u` no longer tolerates.
interior-⋉-rewind : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ interior Θ₁ (interior Θ₂ Δ)
interior-⋉-rewind Θ₁ Θ₂ {Δ = Δ} mw
  rewrite interior-rewind Θ₂ mw =
  trans (interior-⋉ Θ₁ Θ₂ (pushBinds (repsOf Θ₂) Δ))
        (cong (λ Ξ → pushBinds (repsOf Θ₁) (scope Θ₁ Ξ))
              (scope-scopeOf (repsOf Θ₂) Θ₂ Δ))

-- … and the CONVERSION CONTEXT of the moved frame is the redex's inner
-- conversion context with Θ₂'s LOCKS lifted off — which is the whole
-- point of the move (the rep the swapped conversion presents is read
-- OUTSIDE those locks).
convCtx-⋉-rewind : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ convCtx Θ₁ (convCtx Θ₂ Δ)
convCtx-⋉-rewind Θ₁ Θ₂ {Δ = Δ} mw
  rewrite interior-rewind Θ₂ mw =
  trans (convCtx-⋉ Θ₁ Θ₂ (pushBinds (repsOf Θ₂) Δ))
        (cong (λ Ξ → pushBinds (repsOf Θ₁) (unlockedScope Θ₁ Ξ))
              (unlockedScope-scopeOf (repsOf Θ₂) Θ₂ Δ))

-- The one place a ⊑ survives, and it carries a TYPE, not a term: the
-- inner conversion is read where Θ₂'s locks are not applied at all.
convCtx-move : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → convCtx Θ₁ (interior Θ₂ Δ) ⊑ convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
convCtx-move Θ₁ Θ₂ {Δ = Δ} mw =
  subst (λ Ξ → convCtx Θ₁ (interior Θ₂ Δ) ⊑ Ξ)
        (sym (convCtx-⋉-rewind Θ₁ Θ₂ mw))
        (⊑-convCtx Θ₁ (interior⊑convCtx Θ₂ Δ))

-- THE BINDER, ON THE CONTRACTUM'S INNER CONVERSION CONTEXT.  The outer
-- reveal's own lookup — read on `convCtx Θ₂ Δ` — transported past the
-- moved scope, past Θ₁'s unmasks, and past Θ₁'s binders.
move-∋ : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {Y : ℕ} {A : Ty} → Δ ⊢ᵐ Θ₂
  → convCtx Θ₂ Δ ∋ Y := A
  → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
      ∋ (numBinds Θ₁ + Y) := shiftBy (numBinds Θ₁) A
move-∋ Θ₁ Θ₂ {Δ = Δ} {Y = Y} {A = A} mw d =
  subst (λ Ξ → Ξ ∋ (numBinds Θ₁ + Y) := shiftBy (numBinds Θ₁) A)
        (sym (convCtx-⋉-rewind Θ₁ Θ₂ mw))
        (pushBinds-∋ (repsOf Θ₁) (unlockedScope-∋bind Θ₁ d))

-- The conversion context of the moved inner frame carries every rep its
-- own exterior carries — it only ADDS unmasks and the bind prefix.
wf-convCtx-move : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {A : Ty} → Δ ⊢ᵐ Θ₂
  → convCtx Θ₂ Δ ⊢ᵗ A
  → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ⊢ᵗ shiftBy (numBinds Θ₁) A
wf-convCtx-move Θ₁ Θ₂ {Δ = Δ} {A = A} mw w =
  subst (λ Ξ → Ξ ⊢ᵗ shiftBy (numBinds Θ₁) A)
        (sym (convCtx-⋉-rewind Θ₁ Θ₂ mw))
        (wf-shiftBy-pushBinds (repsOf Θ₁) (wf-unlockedScope Θ₁ w))

------------------------------------------------------------------------
-- §4b  WHY THE UNLOCKS TRAVEL TOO — the lock-only move, REFUTED
------------------------------------------------------------------------

-- The obvious cheaper move appends only Θ₂'s LOCKS.  It reorders a
-- same-slot unlock/lock pair, because `scope` applies the list HEAD-LAST,
-- and then the value's frame is not REFINED but CORRUPTED: a slot the
-- value may name in the redex is MASKED in the contractum.
locksOnly : ℕ → CtxMorph → CtxMorph
locksOnly n []             = []
locksOnly n (bind A ∷ Θ)   = locksOnly n Θ
locksOnly n (unlock X ∷ Θ) = locksOnly n Θ
locksOnly n (lock X ∷ Θ)   = lock (n + X) ∷ locksOnly n Θ

-- THE WITNESS.  `Θ✗` masks slot 0 and then re-exposes it — and BOTH
-- entries are legal under the SEQUENTIAL judgement: the lock names a slot
-- visible at Δ✗, the unlock names the slot the lock itself just locked.
Θ✗ : CtxMorph
Θ✗ = unlock 0 ∷ lock 0 ∷ []

Δ✗ : Ctxᵗ
Δ✗ = bind `ℕ ∷ []

⊢ᵐ-Θ✗ : Δ✗ ⊢ᵐ Θ✗
⊢ᵐ-Θ✗ = mw-u (masked (bind `ℕ) , ez , locked nameable-b)
             (mw-l (bind `ℕ , ez , nameable-b) mw[])

_ : interior Θ✗ Δ✗ ≡ bind `ℕ ∷ []
_ = refl

_ : interior (rewind Θ✗) Δ✗ ≡ bind `ℕ ∷ []
_ = refl

-- … but the lock-only contractum's interior BLOCKS it.
_ : scope (locksOnly (numBinds Θ✗) Θ✗) (interior (rewind Θ✗) Δ✗)
      ≡ masked (bind `ℕ) ∷ []
_ = refl

¬frame-locksOnly :
  ¬ (interior [] (interior Θ✗ Δ✗)
       ≡ interior ([] ++ locksOnly (numBinds Θ✗) Θ✗)
                  (interior (rewind Θ✗) Δ✗))
¬frame-locksOnly ()

------------------------------------------------------------------------
-- §5  `_⊢ᵐ_` for the two new frames
------------------------------------------------------------------------

-- THE REWOUND FRAME.  Θ's own entries are read exactly where they were
-- (they sit at the TAIL of the append), and the inverse scope on top is
-- `⊢ᵐ-dualScope` at an empty bind prefix.
⊢ᵐ-rewind : ∀ (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ → Δ ⊢ᵐ rewind Θ
⊢ᵐ-rewind Θ mw = ⊢ᵐ-++ (dualScope 0 Θ) Θ (⊢ᵐ-dualScope [] Θ mw) mw

-- THE MOVED SCOPE IS WELL FORMED WHERE IT LANDS.  Θ₂'s entries are read
-- one bind prefix in, over `pushBinds As (scope Θ₂ᵢ Δ)` — which is where
-- Θ₂'s own premises live, lifted (`scope-scopeOf`).  No refinement step,
-- and no `le-mu`.
⊢ᵐ-scopeOf : ∀ (As : List Ty) (Θ : CtxMorph) {Δ : Ctxᵗ}
  → Δ ⊢ᵐ Θ → pushBinds As Δ ⊢ᵐ scopeOf (length As) Θ
⊢ᵐ-scopeOf As []             mw[]       = mw[]
⊢ᵐ-scopeOf As (bind A ∷ Θ)   (mw-b _ b) = ⊢ᵐ-scopeOf As Θ b
⊢ᵐ-scopeOf As (lock X ∷ Θ)   {Δ = Δ} (mw-l tv b) =
  mw-l (subst (λ Ξ → Ξ ∋tv (length As + X))
              (sym (scope-scopeOf As Θ Δ)) (pushBinds-∋tv As tv))
       (⊢ᵐ-scopeOf As Θ b)
⊢ᵐ-scopeOf As (unlock X ∷ Θ) {Δ = Δ} (mw-u lk b) =
  mw-u (subst (λ Ξ → Ξ ∋lk (length As + X))
              (sym (scope-scopeOf As Θ Δ)) (pushBinds-∋lk As lk))
       (⊢ᵐ-scopeOf As Θ b)

-- THE MERGED FRAME.  `⊢ᵐ-++` splits it at the move: Θ₂'s scope is read
-- over `pushBinds (repsOf Θ₂) Δ`, and Θ₁ is then read over exactly
-- `interior Θ₂ Δ` — its own exterior in the redex.  THIS is what the
-- sequential judgement buys: under a SIMULTANEOUS `mw-b`, Θ₁'s reps
-- would have to be well formed on the plain `pushBinds (repsOf Θ₂) Δ`,
-- and a rep naming a slot Θ₂ UNLOCKED is not.
⊢ᵐ-⋉ : ∀ (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ}
  → Δ ⊢ᵐ Θ₂ → interior Θ₂ Δ ⊢ᵐ Θ₁
  → interior (rewind Θ₂) Δ ⊢ᵐ (Θ₁ ⋉ Θ₂)
⊢ᵐ-⋉ Θ₁ Θ₂ {Δ = Δ} b₂ b₁ =
  subst (λ Ξ → Ξ ⊢ᵐ (Θ₁ ⋉ Θ₂)) (sym (interior-rewind Θ₂ b₂))
        (⊢ᵐ-++ Θ₁ (scopeOf (numBinds Θ₂) Θ₂)
                (subst (λ Ξ → Ξ ⊢ᵐ Θ₁)
                       (sym (scope-scopeOf (repsOf Θ₂) Θ₂ Δ)) b₁)
                (⊢ᵐ-scopeOf (repsOf Θ₂) Θ₂ b₂))

------------------------------------------------------------------------
-- §6  THE TWO CASES
------------------------------------------------------------------------

-- What both share: the outer boundary of the contractum.  Its frame is
-- `rewind Θ₂`, its conversion the identity at the rep, and its two
-- well-formedness obligations are the redex's own exterior type lifted.
module _ {Δ : Ctxᵗ} (Θ₂ : CtxMorph) {A C : Ty}
         (mw₂ : Δ ⊢ᵐ Θ₂) (wE : Δ ⊢ᵗ C)
         (eqAC : A ≡ shiftBy (numBinds Θ₂) C) where

  -- THE PREMISE THE WALL USED TO DENY.  `interior (rewind Θ₂) Δ` IS the
  -- bind prefix over the plain exterior (§3), and A is C lifted past
  -- Θ₂'s binders — so this is `wf-shiftBy-pushBinds`, and nothing else.
  moved-scoped : interior (rewind Θ₂) Δ ⊢ᵗ A
  moved-scoped rewrite eqAC | interior-rewind Θ₂ mw₂ =
    wf-shiftBy-pushBinds (repsOf Θ₂) wE

  moved-conv : convCtx (rewind Θ₂) Δ
                 ⊢ mkId A ∶ A ⇝ shiftBy (numBinds (rewind Θ₂)) C
  moved-conv rewrite numBinds-rewind Θ₂ | eqAC =
    mkId-⊢ (wf-convCtx-rewind Θ₂ wE)

-- ── IDPUSH ─────────────────────────────────────────────────────────────
-- The conversions swap and the scope moves.  Four moves, one per
-- premise of the contractum's inner `env`:
--
--   FRAME       `Θ₁ ⋉ Θ₂`, well formed by §5.
--   INTERIOR    `V`, transported by `subst` along the EQUALITY of §4.
--   CONVERSION  `unseal X` at the binder `move-∋` transports (§4); the
--               two names are forced equal by the inner identity
--               conversion's own TARGET type, `X ≡ numBinds Θ₁ + Y`
--               (proof/IdLayer, `idpush-name`).
--   EXTERIOR    `moved-scoped` — the premise that used to be the wall.
preserve-IdPush : IdPushCase
preserve-IdPush {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                {A = A} {C = C} v d
                (env mw₂ (env mw₁ ⊢V ⊢cᵢ wE′) (conv-unseal dₒ) wE) =
  env (⊢ᵐ-rewind Θ₂ mw₂)
      (env (⊢ᵐ-⋉ Θ₁ Θ₂ mw₂ mw₁) ⊢V′ convᵢ (moved-scoped Θ₂ mw₂ wE eqAC))
      (moved-conv Θ₂ mw₂ wE eqAC)
      wE
  where
  -- The outer `unseal Y`'s rep is `shiftBy (numBinds Θ₂) C`; it IS A.
  eqAC : A ≡ shiftBy (numBinds Θ₂) C
  eqAC = ∋:=-det d dₒ

  -- The inner `id (` X)` conversion: its source type is `` ` X ``, and
  -- its target `shiftBy (numBinds Θ₁) (` Y)` equals `` ` X ``.
  eqX : numBinds Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (shiftBy-var (numBinds Θ₁) Y)) (conv-idv-tgt ⊢cᵢ))

  ⊢V′ : interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ∣ [] ⊢ V ⦂ ` X
  ⊢V′ = subst (λ Ξ → Ξ ∣ [] ⊢ V ⦂ ` X)
              (sym (interior-⋉-rewind Θ₁ Θ₂ mw₂))
              (subst (λ T → interior Θ₁ (interior Θ₂ Δ) ∣ [] ⊢ V ⦂ T)
                     (conv-idv-src ⊢cᵢ) ⊢V)

  dX : convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
         ∋ X := shiftBy (numBinds Θ₁) A
  dX = subst (λ Z → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
                      ∋ Z := shiftBy (numBinds Θ₁) A)
             eqX (move-∋ Θ₁ Θ₂ mw₂ d)

  convᵢ : convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
            ⊢ unseal X ∶ ` X ⇝ shiftBy (numBinds (Θ₁ ⋉ Θ₂)) A
  convᵢ rewrite numBinds-⋉ Θ₁ Θ₂ = conv-unseal dX

-- ── CANCELR ────────────────────────────────────────────────────────────
-- The same four moves, with both conversions neutralised instead of
-- swapped.  THE TYPE EQUATION — `V`'s interior type IS the new inner
-- conversion's SOURCE — is the one piece of content: `seal X`'s source
-- is X's rep, and X's rep on the contractum's inner CONVERSION CONTEXT
-- is `shiftBy (numBinds Θ₁) A`, so `∋:=-det` closes it.
preserve-CancelR : CancelRCase
preserve-CancelR {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {C = C} v d
                 (env mw₂ (env mw₁ ⊢V ⊢c₁ wE′) (conv-unseal dₒ) wE) =
  env (⊢ᵐ-rewind Θ₂ mw₂)
      (env (⊢ᵐ-⋉ Θ₁ Θ₂ mw₂ mw₁) ⊢V′ convᵢ (moved-scoped Θ₂ mw₂ wE eqAC))
      (moved-conv Θ₂ mw₂ wE eqAC)
      wE
  where
  eqAC : A ≡ shiftBy (numBinds Θ₂) C
  eqAC = ∋:=-det d dₒ

  eqX : numBinds Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (shiftBy-var (numBinds Θ₁) Y)) (conv-seal-tgt ⊢c₁))

  dX : convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
         ∋ X := shiftBy (numBinds Θ₁) A
  dX = subst (λ Z → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
                      ∋ Z := shiftBy (numBinds Θ₁) A)
             eqX (move-∋ Θ₁ Θ₂ mw₂ d)

  -- `seal X`'s source, read where the move puts it.
  eqV : _ ≡ shiftBy (numBinds Θ₁) A
  eqV = ∋:=-det (⊑-kn (convCtx-move Θ₁ Θ₂ mw₂)
                      (seal-source-is-rep ⊢c₁))
                dX

  ⊢V′ : interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ∣ []
          ⊢ V ⦂ shiftBy (numBinds Θ₁) A
  ⊢V′ = subst (λ Ξ → Ξ ∣ [] ⊢ V ⦂ shiftBy (numBinds Θ₁) A)
              (sym (interior-⋉-rewind Θ₁ Θ₂ mw₂))
              (subst (λ T → interior Θ₁ (interior Θ₂ Δ) ∣ [] ⊢ V ⦂ T) eqV ⊢V)

  convᵢ : convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
            ⊢ mkId (shiftBy (numBinds Θ₁) A)
            ∶ shiftBy (numBinds Θ₁) A ⇝ shiftBy (numBinds (Θ₁ ⋉ Θ₂)) A
  convᵢ rewrite numBinds-⋉ Θ₁ Θ₂ =
    mkId-⊢ (wf-convCtx-move Θ₁ Θ₂ mw₂
              (subst (λ T → convCtx Θ₂ Δ ⊢ᵗ T) (sym eqAC) (wf-convCtx Θ₂ wE)))

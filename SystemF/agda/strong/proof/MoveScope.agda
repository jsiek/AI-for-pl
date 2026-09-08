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
-- `Θ₁ ⋉ Θ₂` appends Θ₂'s whole CHANGE LIST (locks AND unlocks, in order,
-- lifted past Θ₂'s binders) at Θ₁'s TAIL, where `applyChanges` applies it
-- FIRST — unless that copy is redundant, see below; and `rewind Θ₂` is Θ₂
-- with its own changes UNDONE, so what is left of the outer frame is the
-- BIND BLOCK, in net effect:
--
--   scope    (rewind Θ₂) Δ ≡ Δ                          (given Δ ⊢ᵐ Θ₂)
--   interior (rewind Θ₂) Δ ≡ pushBinds (binds Θ₂) Δ
--
-- WHY `rewind` AND NOT `morph (binds Θ₂) []` / `dropLocks`.  All three
-- have the same net effect on the type context, and only `rewind` keeps
-- its own `⊢ᵐ`:
--   `dropLocks Θ₂` KEEPS Θ₂'s unlocks, so the moved copy of the same
--     unlock is then VACUOUS and `sw-u` refuses it;
--   `morph (binds Θ₂) []` DELETES them, and then Θ₂'s own bind reps —
--     read on `unlockedScope Θ₂ Δ` — lose the unlock they depend on;
--   `rewind Θ₂` keeps every entry and rewinds it, so every premise is
--     read exactly where the redex read it.
--
-- WHY IT WORKS, in one line: the moved change list re-creates Θ₂'s
-- changes one bind prefix in (`applyChanges-shiftScope`), so the value's
-- frame is preserved ON THE NOSE — the two frame lemmas are EQUALITIES,
-- and no `⊢retag` appears in either case — while the rep the swapped
-- conversion presents is read OUTSIDE Θ₂'s locks, where
-- `wf-shiftBy-pushBinds` supplies the premise the wall used to deny.
--
-- AND NEITHER FRAME COPIES WHAT IS ALREADY THERE (2026-09-08).  Both
-- `rewind` and `_⋉_` carry a REDUNDANCY TEST (strong.CtxMorph §4): a
-- replay is not replayed again, and a moved copy whose unmasks the inner
-- list already performs — the outer changes being a replay, so the copy
-- is the identity on the interior — is DROPPED.  Every lemma below keeps
-- the statement it had, because both drops are EXACT; what changes is
-- that each has two branches, and on the redundant one the obligation is
-- the ORIGINAL frame's, on the nose.  Without the tests the change lists
-- double at every pass (Examples §16), and what no exact rewriting can
-- shrink is catalogued in proof/RewindNorm.
--
--   §1  the lookup transports
--   §2  the list algebra of `shiftScope`/`rewind`/`_⋉_`, and
--       `rewind-idem`
--   §3  the type-context identities, the unmask SET algebra
--       (`applyUnlocks-absorb`) and the two merge bridges
--   §4  the FRAME LEMMAS, as EQUALITIES
--   §4b why the unlocks travel too — the lock-only move, REFUTED
--   §5  `_⊢ᵐ_` for the two new frames
--   §6  the two cases

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Data.List.Properties using (length-++)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.proof.Preserve using (CancelRCase; IdPushCase)
open import strong.proof.PeelDual
  using (⊢ˢ-++; ⊢ˢ-suffix; applyChanges-++; applyUnlocks-++;
         applyChanges-dualScope; ⊢ˢ-dualScope)

------------------------------------------------------------------------
-- §1  Lookup transports
------------------------------------------------------------------------

-- A binder survives `applyUnlocks`: it only unmasks (`unmaskEnt`, which
-- fixes `bind`) and skips locks, so a `bind` lookup is preserved
-- unchanged.
applyUnlocks-∋bind : ∀ (S : List Change) {Δ Y A}
  → Δ ∋ Y := A → applyUnlocks S Δ ∋ Y := A
applyUnlocks-∋bind []              d = d
applyUnlocks-∋bind (lock Z ∷ S)    d = applyUnlocks-∋bind S d
applyUnlocks-∋bind (unlock Z ∷ S) {Y = Y} d with Z ≟ℕ Y
... | yes refl =
  updateAt-hit  unmaskEnt unmaskEnt-comm    (applyUnlocks-∋bind S d)
... | no  ne   =
  updateAt-miss unmaskEnt unmaskEnt-comm ne (applyUnlocks-∋bind S d)

unlockedScope-∋bind : ∀ (Θ : CtxMorph) {Δ Y A}
  → Δ ∋ Y := A → unlockedScope Θ Δ ∋ Y := A
unlockedScope-∋bind Θ d = applyUnlocks-∋bind (changes Θ) d

-- The bind prefix lifts a binder: slot Y in the tail becomes slot
-- `length As + Y` at the rep lifted past the `length As` prefix binders.
pushBinds-∋ : ∀ (As : List Ty) {Δ Y A}
  → Δ ∋ Y := A → pushBinds As Δ ∋ (length As + Y) := shiftBy (length As) A
pushBinds-∋ []       d = d
pushBinds-∋ (C ∷ As) d = es (pushBinds-∋ As d)

------------------------------------------------------------------------
-- §2  The list algebra of the move
------------------------------------------------------------------------

-- THE MOVE CARRIES NO BINDER, AND REWINDING KEEPS THE BINDERS.  With the
-- PAIR both are facts about the constructor — `refl` — and the five
-- filtering lemmas the interleaved list needed here (`repsOf-scopeOf`,
-- `repsOf-⋉`, `repsOf-rewind`, and the two `numBinds` corollaries, which
-- were `cong length` of them) collapse to these two `refl`s, used
-- nowhere.
numBinds-⋉ : (Θ₁ Θ₂ : CtxMorph) → numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁
numBinds-⋉ Θ₁ Θ₂ = refl

numBinds-rewind : (Θ : CtxMorph) → numBinds (rewind Θ) ≡ numBinds Θ
numBinds-rewind Θ = refl

-- REWINDING IS IDEMPOTENT (2026-09-08) — the fact that bounds the change
-- lists.  It is two list facts and one arithmetic fact:
--
--   the dual replay has the SAME LENGTH as what it replays;
--   `half (n + n) ≡ n`;
--   `drop (length A) (A ++ B) ≡ B`.
--
-- Together they say that `dualScope 0 S ++ S` IS a replay
-- (`Rewound-replay`), so `rewindChanges` returns it unchanged the next
-- time round.  Without this, the outer frame of a scope move is replayed
-- again on every pass and the lists DOUBLE — Examples §16.
length-dualScope : (n : ℕ) (S : List Change)
  → length (dualScope n S) ≡ length S
length-dualScope n []             = refl
length-dualScope n (lock X ∷ S)   =
  trans (length-++ (dualScope n S) {unlock (n + X) ∷ []})
        (trans (+-comm (length (dualScope n S)) 1)
               (cong suc (length-dualScope n S)))
length-dualScope n (unlock X ∷ S) =
  trans (length-++ (dualScope n S) {lock (n + X) ∷ []})
        (trans (+-comm (length (dualScope n S)) 1)
               (cong suc (length-dualScope n S)))

half-+ : (n : ℕ) → half (n + n) ≡ n
half-+ zero    = refl
half-+ (suc n) =
  trans (cong (λ m → half (suc m)) (+-suc n n)) (cong suc (half-+ n))

drop-length-++ : (S T : List Change) → drop (length S) (S ++ T) ≡ T
drop-length-++ []      T = refl
drop-length-++ (c ∷ S) T = drop-length-++ S T

secondHalf-replay : (S : List Change)
  → secondHalf (dualScope 0 S ++ S) ≡ S
secondHalf-replay S =
  trans (cong (λ n → drop (half n) (dualScope 0 S ++ S))
              (trans (length-++ (dualScope 0 S) {S})
                     (cong (_+ length S) (length-dualScope 0 S))))
        (trans (cong (λ n → drop n (dualScope 0 S ++ S))
                     (trans (half-+ (length S))
                            (sym (length-dualScope 0 S))))
               (drop-length-++ (dualScope 0 S) S))

Rewound-replay : (S : List Change) → Rewound (dualScope 0 S ++ S)
Rewound-replay S =
  cong (λ T → dualScope 0 T ++ T) (secondHalf-replay S)

-- A list that IS a replay is left alone, whichever way the test goes.
rewindChanges-fix : (S : List Change) (d : Dec (Rewound S))
  → Rewound S → rewindChanges S d ≡ S
rewindChanges-fix S (yes _) r = refl
rewindChanges-fix S (no ¬r) r = ⊥-elim (¬r r)

rewind-idem : (Θ : CtxMorph) → rewind (rewind Θ) ≡ rewind Θ
rewind-idem Θ with rewound? (changes Θ)
rewind-idem Θ | yes eq =
  cong (morph (binds Θ))
       (rewindChanges-fix (changes Θ) (rewound? (changes Θ)) eq)
rewind-idem Θ | no ¬eq =
  cong (morph (binds Θ))
       (rewindChanges-fix (dualScope 0 (changes Θ) ++ changes Θ)
                          (rewound? (dualScope 0 (changes Θ) ++ changes Θ))
                          (Rewound-replay (changes Θ)))

-- THE MOVED CHANGES, APPLIED PAST THE BIND PREFIX, ARE THE ORIGINAL
-- CHANGES APPLIED UNDER IT.  This is the whole point of the index lift
-- `n + X`, and it is `updateAt-pushBinds` (strong.Ctx) once per entry.
applyChanges-shiftScope : (As : List Ty) (S : List Change) (Δ : Ctxᵗ)
  → applyChanges (shiftScope (length As) S) (pushBinds As Δ)
      ≡ pushBinds As (applyChanges S Δ)
applyChanges-shiftScope As []             Δ = refl
applyChanges-shiftScope As (unlock X ∷ S) Δ =
  trans (cong (unmask (length As + X)) (applyChanges-shiftScope As S Δ))
        (updateAt-pushBinds unmaskEnt As X (applyChanges S Δ))
applyChanges-shiftScope As (lock X ∷ S)   Δ =
  trans (cong (mask (length As + X)) (applyChanges-shiftScope As S Δ))
        (updateAt-pushBinds maskEnt As X (applyChanges S Δ))

applyUnlocks-shiftScope : (As : List Ty) (S : List Change) (Δ : Ctxᵗ)
  → applyUnlocks (shiftScope (length As) S) (pushBinds As Δ)
      ≡ pushBinds As (applyUnlocks S Δ)
applyUnlocks-shiftScope As []             Δ = refl
applyUnlocks-shiftScope As (lock X ∷ S)   Δ = applyUnlocks-shiftScope As S Δ
applyUnlocks-shiftScope As (unlock X ∷ S) Δ =
  trans (cong (unmask (length As + X)) (applyUnlocks-shiftScope As S Δ))
        (updateAt-pushBinds unmaskEnt As X (applyUnlocks S Δ))

------------------------------------------------------------------------
-- §3  The type-context identities
------------------------------------------------------------------------

-- THE HEADLINE IDENTITY.  A rewound frame's CHANGES ARE THE IDENTITY —
-- this is `applyChanges-dualScope` (proof/PeelDual) at an empty bind
-- prefix, and it is where the whole design is paid for: the inverse is
-- exact only because `sw-u` refuses a vacuous unlock.
--
-- IT HOLDS OF A LIST THAT IS ALREADY A REPLAY, TOO, AND THAT IS WHY
-- `rewindChanges` MAY LEAVE ONE ALONE (strong.CtxMorph §4): `Rewound S`
-- says `S ≡ dualScope 0 Q ++ Q` for S's second half Q, `⊢ˢ-suffix` reads
-- Q's own sequential judgement out of S's, and then it is the SAME lemma
-- at Q.  So the identity is proved ONCE, of `rewindChanges` in both
-- branches.
applyChanges-rewindChanges : (S : List Change) (d : Dec (Rewound S))
  {Δ : Ctxᵗ} → Δ ⊢ˢ S → applyChanges (rewindChanges S d) Δ ≡ Δ
applyChanges-rewindChanges S (yes eq) {Δ = Δ} b =
  trans (cong (λ T → applyChanges T Δ) (sym eq))
        (trans (applyChanges-++ (dualScope 0 Q) Q Δ)
               (applyChanges-dualScope [] Q bQ))
  where
  Q : List Change
  Q = secondHalf S

  bQ : Δ ⊢ˢ Q
  bQ = ⊢ˢ-suffix (dualScope 0 Q) Q (subst (λ T → Δ ⊢ˢ T) (sym eq) b)
applyChanges-rewindChanges S (no _) {Δ = Δ} b =
  trans (applyChanges-++ (dualScope 0 S) S Δ)
        (applyChanges-dualScope [] S b)

scope-rewind : (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ → scope (rewind Θ) Δ ≡ Δ
scope-rewind Θ mwᵥ =
  applyChanges-rewindChanges (changes Θ) (rewound? (changes Θ))
                             (mw-changes mwᵥ)

interior-rewind : (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ
  → interior (rewind Θ) Δ ≡ pushBinds (binds Θ) Δ
interior-rewind Θ mwᵥ = cong (pushBinds (binds Θ)) (scope-rewind Θ mwᵥ)

-- ── THE MERGED LIST DOES WHAT THE FULL APPEND DOES ────────────────────
--
-- On `no` it IS the append.  On `yes` it is the inner list ALONE, and the
-- two halves of `Redundant` (strong.CtxMorph §4) are exactly the two
-- facts that make dropping the copy EXACT:
--
--   `applyChanges` — the dropped copy is the IDENTITY where it would have
--     acted, because the outer changes are a replay
--     (`applyChanges-rewindChanges` at its `yes`);
--   `applyUnlocks` — its unmasks are ALREADY ON, because the inner list
--     runs LAST and unlocks every slot the copy does
--     (`applyUnlocks-absorb`).
--
-- Neither is a refinement step: both are EQUALITIES, so every lemma below
-- keeps the shape it had.

-- Every operation `applyUnlocks` performs is an `unmask`, and unmasks
-- COMMUTE (strong.Ctx §6c) — at any two slots, the same one included.
applyUnlocks-unmask-comm : (S : List Change) (X : ℕ) (Δ : Ctxᵗ)
  → applyUnlocks S (unmask X Δ) ≡ unmask X (applyUnlocks S Δ)
applyUnlocks-unmask-comm []             X Δ = refl
applyUnlocks-unmask-comm (lock Y ∷ S)   X Δ =
  applyUnlocks-unmask-comm S X Δ
applyUnlocks-unmask-comm (unlock Y ∷ S) X Δ =
  trans (cong (unmask Y) (applyUnlocks-unmask-comm S X Δ))
        (unmask-comm Y X (applyUnlocks S Δ))

-- … so what a list has already unmasked cannot be unmasked again.
applyUnlocks-∈-idem : (S : List Change) (X : ℕ) (Δ : Ctxᵗ)
  → X ∈ᴺ unlockSlots S → unmask X (applyUnlocks S Δ) ≡ applyUnlocks S Δ
applyUnlocks-∈-idem (lock Y ∷ S)   X Δ i = applyUnlocks-∈-idem S X Δ i
applyUnlocks-∈-idem (unlock Y ∷ S) X Δ hereᴺ = unmask-idem X (applyUnlocks S Δ)
applyUnlocks-∈-idem (unlock Y ∷ S) X Δ (thereᴺ i) =
  trans (unmask-comm X Y (applyUnlocks S Δ))
        (cong (unmask Y) (applyUnlocks-∈-idem S X Δ i))

-- THE ABSORPTION.  `L` runs LAST, so if it unlocks every slot `M`
-- unlocks then `M`'s unmasks are invisible: `applyUnlocks` is a SET.
applyUnlocks-absorb : (L M : List Change) (Δ : Ctxᵗ)
  → unlockSlots M ⊆ᴺ unlockSlots L
  → applyUnlocks L (applyUnlocks M Δ) ≡ applyUnlocks L Δ
applyUnlocks-absorb L []             Δ s          = refl
applyUnlocks-absorb L (lock X ∷ M)   Δ s          =
  applyUnlocks-absorb L M Δ s
applyUnlocks-absorb L (unlock X ∷ M) Δ (sub∷ i s) =
  trans (applyUnlocks-unmask-comm L X (applyUnlocks M Δ))
        (trans (cong (unmask X) (applyUnlocks-absorb L M Δ s))
               (applyUnlocks-∈-idem L X Δ i))

merge-applyChanges : (Θ₁ Θ₂ : CtxMorph) (d : Dec (Redundant Θ₁ Θ₂))
  {Δ : Ctxᵗ} → Δ ⊢ˢ changes Θ₂
  → applyChanges (mergeChanges Θ₁ Θ₂ d) (pushBinds (binds Θ₂) Δ)
      ≡ applyChanges (changes Θ₁ ++ shiftScope (numBinds Θ₂) (changes Θ₂))
                     (pushBinds (binds Θ₂) Δ)
merge-applyChanges Θ₁ Θ₂ (no _)        b = refl
merge-applyChanges Θ₁ Θ₂ (yes (r , _)) {Δ = Δ} b =
  sym (trans (applyChanges-++ (changes Θ₁)
                              (shiftScope (numBinds Θ₂) (changes Θ₂))
                              (pushBinds (binds Θ₂) Δ))
             (cong (applyChanges (changes Θ₁)) copy-id))
  where
  copy-id : applyChanges (shiftScope (numBinds Θ₂) (changes Θ₂))
              (pushBinds (binds Θ₂) Δ) ≡ pushBinds (binds Θ₂) Δ
  copy-id =
    trans (applyChanges-shiftScope (binds Θ₂) (changes Θ₂) Δ)
          (cong (pushBinds (binds Θ₂))
                (applyChanges-rewindChanges (changes Θ₂) (yes r) b))

merge-applyUnlocks : (Θ₁ Θ₂ : CtxMorph) (d : Dec (Redundant Θ₁ Θ₂))
  (Ξ : Ctxᵗ)
  → applyUnlocks (mergeChanges Θ₁ Θ₂ d) Ξ
      ≡ applyUnlocks (changes Θ₁ ++ shiftScope (numBinds Θ₂) (changes Θ₂)) Ξ
merge-applyUnlocks Θ₁ Θ₂ (no _)        Ξ = refl
merge-applyUnlocks Θ₁ Θ₂ (yes (_ , s)) Ξ =
  sym (trans (applyUnlocks-++ (changes Θ₁)
                              (shiftScope (numBinds Θ₂) (changes Θ₂)) Ξ)
             (applyUnlocks-absorb (changes Θ₁)
               (shiftScope (numBinds Θ₂) (changes Θ₂)) Ξ s))

-- The two frames of the contractum, unfolded.  (The interior one is read
-- at the type context the move puts it over — the rewound frame's
-- interior — because that is where the dropped copy is the identity.)
interior-⋉ : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ˢ changes Θ₂
  → interior (Θ₁ ⋉ Θ₂) (pushBinds (binds Θ₂) Δ)
      ≡ pushBinds (binds Θ₁)
          (applyChanges (changes Θ₁)
            (applyChanges (shiftScope (numBinds Θ₂) (changes Θ₂))
                          (pushBinds (binds Θ₂) Δ)))
interior-⋉ Θ₁ Θ₂ {Δ = Δ} b =
  cong (pushBinds (binds Θ₁))
       (trans (merge-applyChanges Θ₁ Θ₂ (redundant? Θ₁ Θ₂) b)
              (applyChanges-++ (changes Θ₁)
                               (shiftScope (numBinds Θ₂) (changes Θ₂))
                               (pushBinds (binds Θ₂) Δ)))

convCtx-⋉ : (Θ₁ Θ₂ : CtxMorph) (Ξ : Ctxᵗ)
  → convCtx (Θ₁ ⋉ Θ₂) Ξ
      ≡ pushBinds (binds Θ₁)
          (applyUnlocks (changes Θ₁)
            (applyUnlocks (shiftScope (numBinds Θ₂) (changes Θ₂)) Ξ))
convCtx-⋉ Θ₁ Θ₂ Ξ =
  cong (pushBinds (binds Θ₁))
       (trans (merge-applyUnlocks Θ₁ Θ₂ (redundant? Θ₁ Θ₂) Ξ)
              (applyUnlocks-++ (changes Θ₁)
                               (shiftScope (numBinds Θ₂) (changes Θ₂)) Ξ))

------------------------------------------------------------------------
-- §4  THE FRAME LEMMAS — EQUALITIES
------------------------------------------------------------------------

-- A rep survives `unlockedScope` and the bind prefix (`scope` would not
-- do — masking is what the wall was about).
wf-unlockedScope : ∀ {Δ A} (Θ : CtxMorph) → Δ ⊢ᵗ A → unlockedScope Θ Δ ⊢ᵗ A
wf-unlockedScope Θ w = ⊑-wf (Δ⊑unlockedScope Θ _) w

wf-convCtx : ∀ {Δ A} (Θ : CtxMorph)
  → Δ ⊢ᵗ A → convCtx Θ Δ ⊢ᵗ shiftBy (numBinds Θ) A
wf-convCtx Θ w = wf-shiftBy-pushBinds (binds Θ) (wf-unlockedScope Θ w)

-- … and the same at a REWOUND frame, whose bind count IS Θ's own — now
-- definitionally, so the `subst` the interleaved list needed is gone.
wf-convCtx-rewind : ∀ {Δ C} (Θ : CtxMorph) → Δ ⊢ᵗ C
  → convCtx (rewind Θ) Δ ⊢ᵗ shiftBy (numBinds Θ) C
wf-convCtx-rewind Θ w = wf-convCtx (rewind Θ) w

-- THE VALUE'S FRAME IS PRESERVED ON THE NOSE.  Everything Θ₂ masked the
-- moved change list masks again, at the same slots, in the same order,
-- one prefix further in (`applyChanges-shiftScope`); and the outer frame
-- contributes nothing but its binders (`interior-rewind`).  So the value
-- crosses by `subst` — with `dropLocks` this was a ⊑ and needed `⊢retag`
-- along a `le-mu` step, which `sw-u` no longer tolerates.
interior-⋉-rewind : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ interior Θ₁ (interior Θ₂ Δ)
interior-⋉-rewind Θ₁ Θ₂ {Δ = Δ} mwᵥ
  rewrite interior-rewind Θ₂ mwᵥ =
  trans (interior-⋉ Θ₁ Θ₂ (mw-changes mwᵥ))
        (cong (λ Ξ → pushBinds (binds Θ₁) (applyChanges (changes Θ₁) Ξ))
              (applyChanges-shiftScope (binds Θ₂) (changes Θ₂) Δ))

-- … and the CONVERSION CONTEXT of the moved frame is the redex's inner
-- conversion context with Θ₂'s LOCKS lifted off — which is the whole
-- point of the move (the rep the swapped conversion presents is read
-- OUTSIDE those locks).
convCtx-⋉-rewind : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ convCtx Θ₁ (convCtx Θ₂ Δ)
convCtx-⋉-rewind Θ₁ Θ₂ {Δ = Δ} mwᵥ
  rewrite interior-rewind Θ₂ mwᵥ =
  trans (convCtx-⋉ Θ₁ Θ₂ (pushBinds (binds Θ₂) Δ))
        (cong (λ Ξ → pushBinds (binds Θ₁) (applyUnlocks (changes Θ₁) Ξ))
              (applyUnlocks-shiftScope (binds Θ₂) (changes Θ₂) Δ))

-- The one place a ⊑ survives, and it carries a TYPE, not a term: the
-- inner conversion is read where Θ₂'s locks are not applied at all.
convCtx-move : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → convCtx Θ₁ (interior Θ₂ Δ) ⊑ convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
convCtx-move Θ₁ Θ₂ {Δ = Δ} mwᵥ =
  subst (λ Ξ → convCtx Θ₁ (interior Θ₂ Δ) ⊑ Ξ)
        (sym (convCtx-⋉-rewind Θ₁ Θ₂ mwᵥ))
        (⊑-convCtx Θ₁ (interior⊑convCtx Θ₂ Δ))

-- THE BINDER, ON THE CONTRACTUM'S INNER CONVERSION CONTEXT.  The outer
-- reveal's own lookup — read on `convCtx Θ₂ Δ` — transported past the
-- moved changes, past Θ₁'s unmasks, and past Θ₁'s binders.
move-∋ : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {Y : ℕ} {A : Ty} → Δ ⊢ᵐ Θ₂
  → convCtx Θ₂ Δ ∋ Y := A
  → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
      ∋ (numBinds Θ₁ + Y) := shiftBy (numBinds Θ₁) A
move-∋ Θ₁ Θ₂ {Δ = Δ} {Y = Y} {A = A} mwᵥ d =
  subst (λ Ξ → Ξ ∋ (numBinds Θ₁ + Y) := shiftBy (numBinds Θ₁) A)
        (sym (convCtx-⋉-rewind Θ₁ Θ₂ mwᵥ))
        (pushBinds-∋ (binds Θ₁) (unlockedScope-∋bind Θ₁ d))

-- The conversion context of the moved inner frame carries every rep its
-- own exterior carries — it only ADDS unmasks and the bind prefix.
wf-convCtx-move : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {A : Ty} → Δ ⊢ᵐ Θ₂
  → convCtx Θ₂ Δ ⊢ᵗ A
  → convCtx (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ⊢ᵗ shiftBy (numBinds Θ₁) A
wf-convCtx-move Θ₁ Θ₂ {Δ = Δ} {A = A} mwᵥ w =
  subst (λ Ξ → Ξ ⊢ᵗ shiftBy (numBinds Θ₁) A)
        (sym (convCtx-⋉-rewind Θ₁ Θ₂ mwᵥ))
        (wf-shiftBy-pushBinds (binds Θ₁) (wf-unlockedScope Θ₁ w))

------------------------------------------------------------------------
-- §4b  WHY THE UNLOCKS TRAVEL TOO — the lock-only move, REFUTED
------------------------------------------------------------------------

-- The obvious cheaper move appends only Θ₂'s LOCKS.  It reorders a
-- same-slot unlock/lock pair, because `applyChanges` applies the list
-- HEAD-LAST, and then the value's frame is not REFINED but CORRUPTED: a
-- slot the value may name in the redex is MASKED in the contractum.
locksOnly : ℕ → List Change → List Change
locksOnly n []             = []
locksOnly n (unlock X ∷ S) = locksOnly n S
locksOnly n (lock X ∷ S)   = lock (n + X) ∷ locksOnly n S

-- THE WITNESS.  `Θ✗` masks slot 0 and then re-exposes it — and BOTH
-- entries are legal under the SEQUENTIAL change judgement: the lock names
-- a slot visible at Δ✗, the unlock names the slot the lock itself just
-- locked.
Θ✗ : CtxMorph
Θ✗ = morph [] (unlock 0 ∷ lock 0 ∷ [])

Δ✗ : Ctxᵗ
Δ✗ = unmasked (bind `ℕ) ∷ []

⊢ᵐ-Θ✗ : Δ✗ ⊢ᵐ Θ✗
⊢ᵐ-Θ✗ = mw rw[]
           (sw-u (masked (bind `ℕ) , ez , locked)
                 (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[]))

_ : interior Θ✗ Δ✗ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

_ : interior (rewind Θ✗) Δ✗ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

-- … but the lock-only contractum's interior BLOCKS it.
_ : applyChanges (locksOnly (numBinds Θ✗) (changes Θ✗))
                 (interior (rewind Θ✗) Δ✗)
      ≡ masked (bind `ℕ) ∷ []
_ = refl

¬frame-locksOnly :
  ¬ (interior (morph [] []) (interior Θ✗ Δ✗)
       ≡ interior (morph [] ([] ++ locksOnly (numBinds Θ✗) (changes Θ✗)))
                  (interior (rewind Θ✗) Δ✗))
¬frame-locksOnly ()

------------------------------------------------------------------------
-- §5  `_⊢ᵐ_` for the two new frames
------------------------------------------------------------------------

-- THE REWOUND FRAME.  Its CHANGES are Θ's own with the inverse list on
-- top (`⊢ˢ-dualScope` at an empty bind prefix); its REPS are Θ's own,
-- read past the extra unmasks the inverse list adds — MORE nameable, so
-- `⊢ʳ-⊑` carries them.  (Under the interleaved list the reps sat inside
-- the appended tail, where they were read unchanged.)
--
-- WHEN THE LIST IS ALREADY A REPLAY THERE IS NOTHING TO DO: the frame IS
-- Θ, so both halves are Θ's own judgement, ON THE NOSE — not even a
-- `⊢ʳ-⊑` step, because the reps are read on exactly the type context
-- they were read on.  That is what makes `rewind` IDEMPOTENT
-- (`rewind-idem` below) and the change lists BOUNDED (Examples §16).
⊢ᵐ-rewindChanges : ∀ (Θ : CtxMorph) (d : Dec (Rewound (changes Θ)))
  {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ
  → Δ ⊢ᵐ morph (binds Θ) (rewindChanges (changes Θ) d)
⊢ᵐ-rewindChanges Θ (yes eq) mwᵥ = mw (mw-reps mwᵥ) (mw-changes mwᵥ)
⊢ᵐ-rewindChanges Θ (no _) {Δ = Δ} mwᵥ =
  mw (subst (λ Ξ → Ξ ⊢ʳ binds Θ)
            (sym (applyUnlocks-++ (dualScope 0 (changes Θ)) (changes Θ) Δ))
            (⊢ʳ-⊑ (Δ⊑applyUnlocks (dualScope 0 (changes Θ))
                                  (applyUnlocks (changes Θ) Δ))
                  (mw-reps mwᵥ)))
     (⊢ˢ-++ (dualScope 0 (changes Θ)) (changes Θ)
            (⊢ˢ-dualScope [] (changes Θ) (mw-changes mwᵥ))
            (mw-changes mwᵥ))

⊢ᵐ-rewind : ∀ (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ → Δ ⊢ᵐ rewind Θ
⊢ᵐ-rewind Θ mwᵥ = ⊢ᵐ-rewindChanges Θ (rewound? (changes Θ)) mwᵥ

-- THE MOVED CHANGES ARE WELL FORMED WHERE THEY LAND.  Θ₂'s entries are
-- read one bind prefix in, over `pushBinds As (applyChanges S′ Δ)` —
-- which is where Θ₂'s own premises live, lifted
-- (`applyChanges-shiftScope`).  No refinement step, and no `le-mu`.
⊢ˢ-shiftScope : ∀ (As : List Ty) (S : List Change) {Δ : Ctxᵗ}
  → Δ ⊢ˢ S → pushBinds As Δ ⊢ˢ shiftScope (length As) S
⊢ˢ-shiftScope As []             sw[]       = sw[]
⊢ˢ-shiftScope As (lock X ∷ S)   {Δ = Δ} (sw-l tv b) =
  sw-l (subst (λ Ξ → Ξ ∋tv (length As + X))
              (sym (applyChanges-shiftScope As S Δ)) (pushBinds-∋tv As tv))
       (⊢ˢ-shiftScope As S b)
⊢ˢ-shiftScope As (unlock X ∷ S) {Δ = Δ} (sw-u lk b) =
  sw-u (subst (λ Ξ → Ξ ∋lk (length As + X))
              (sym (applyChanges-shiftScope As S Δ)) (pushBinds-∋lk As lk))
       (⊢ˢ-shiftScope As S b)

-- THE MERGED FRAME.  ITS TWO HALVES SPLIT CLEANLY, which is what the
-- pair buys: the CHANGES are `⊢ˢ-++` at the move (Θ₂'s changes read over
-- `pushBinds (binds Θ₂) Δ`, then Θ₁'s over exactly `interior Θ₂ Δ` — its
-- own exterior in the redex), and the REPS are Θ₁'s own, read past ALL of
-- the merged frame's unlocks, i.e. past Θ₁'s AND Θ₂'s.  That is MORE
-- nameable than where the redex read them, so `⊢ʳ-⊑` carries them and
-- nothing has to be re-derived — under a SIMULTANEOUS reading on the
-- PLAIN exterior neither half would survive.
-- WHEN THE MOVED COPY IS DROPPED, THE MERGED FRAME IS Θ₁ ITSELF, and its
-- `⊢ᵐ` is Θ₁'s own: the rewound frame's interior IS Θ₂'s interior,
-- because Θ₂'s changes are a replay.  Both halves travel by `subst`
-- along that ONE equality — no `⊢ˢ-++`, no `⊢ʳ-⊑`, nothing re-derived.
⊢ᵐ-⋉ᴰ : ∀ (Θ₁ Θ₂ : CtxMorph) (d : Dec (Redundant Θ₁ Θ₂)) {Δ : Ctxᵗ}
  → Δ ⊢ᵐ Θ₂ → interior Θ₂ Δ ⊢ᵐ Θ₁
  → interior (rewind Θ₂) Δ ⊢ᵐ morph (binds Θ₁) (mergeChanges Θ₁ Θ₂ d)
⊢ᵐ-⋉ᴰ Θ₁ Θ₂ (yes (r , _)) {Δ = Δ} b₂ b₁ =
  subst (λ Ξ → Ξ ⊢ᵐ Θ₁) (sym rewound-interior) b₁
  where
  rewound-interior : interior (rewind Θ₂) Δ ≡ interior Θ₂ Δ
  rewound-interior =
    trans (interior-rewind Θ₂ b₂)
          (cong (pushBinds (binds Θ₂))
                (sym (applyChanges-rewindChanges (changes Θ₂) (yes r)
                                                 (mw-changes b₂))))
⊢ᵐ-⋉ᴰ Θ₁ Θ₂ (no _) {Δ = Δ} b₂ b₁ =
  subst (λ Ξ → Ξ ⊢ᵐ morph (binds Θ₁) (changes Θ₁ ++ S₂))
        (sym (interior-rewind Θ₂ b₂))
        (mw reps chgs)
  where
  S₂ : List Change
  S₂ = shiftScope (numBinds Θ₂) (changes Θ₂)

  reps : applyUnlocks (changes Θ₁ ++ S₂) (pushBinds (binds Θ₂) Δ)
           ⊢ʳ binds Θ₁
  reps =
    subst (λ Ξ → Ξ ⊢ʳ binds Θ₁)
          (sym (trans (applyUnlocks-++ (changes Θ₁) S₂
                        (pushBinds (binds Θ₂) Δ))
                      (cong (applyUnlocks (changes Θ₁))
                            (applyUnlocks-shiftScope (binds Θ₂)
                                                     (changes Θ₂) Δ))))
          (⊢ʳ-⊑ (⊑-applyUnlocks (changes Θ₁)
                   (⊑-pushBinds (binds Θ₂)
                      (applyChanges⊑applyUnlocks (changes Θ₂) Δ)))
                (mw-reps b₁))

  chgs : pushBinds (binds Θ₂) Δ ⊢ˢ (changes Θ₁ ++ S₂)
  chgs =
    ⊢ˢ-++ (changes Θ₁) S₂
          (subst (λ Ξ → Ξ ⊢ˢ changes Θ₁)
                 (sym (applyChanges-shiftScope (binds Θ₂) (changes Θ₂) Δ))
                 (mw-changes b₁))
          (⊢ˢ-shiftScope (binds Θ₂) (changes Θ₂) (mw-changes b₂))

⊢ᵐ-⋉ : ∀ (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ}
  → Δ ⊢ᵐ Θ₂ → interior Θ₂ Δ ⊢ᵐ Θ₁
  → interior (rewind Θ₂) Δ ⊢ᵐ (Θ₁ ⋉ Θ₂)
⊢ᵐ-⋉ Θ₁ Θ₂ b₂ b₁ = ⊢ᵐ-⋉ᴰ Θ₁ Θ₂ (redundant? Θ₁ Θ₂) b₂ b₁

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
    wf-shiftBy-pushBinds (binds Θ₂) wE

  moved-conv : convCtx (rewind Θ₂) Δ
                 ⊢ mkId A ∶ A ⇝ shiftBy (numBinds (rewind Θ₂)) C
  moved-conv rewrite eqAC = mkId-⊢ (wf-convCtx-rewind Θ₂ wE)

-- ── IDPUSH ─────────────────────────────────────────────────────────────
-- The conversions swap and the changes move.  Four moves, one per
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
  convᵢ = conv-unseal dX

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
  convᵢ =
    mkId-⊢ (wf-convCtx-move Θ₁ Θ₂ mw₂
              (subst (λ T → convCtx Θ₂ Δ ⊢ᵗ T) (sym eqAC) (wf-convCtx Θ₂ wE)))

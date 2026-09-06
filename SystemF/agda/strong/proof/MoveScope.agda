module strong.proof.MoveScope where

-- THE SCOPE MOVE — its frame algebra, and the TWO preservation cases it
-- settles (CancelR and IdPush), UNCONDITIONALLY.
--
-- THE MOVE (strong.Reduction §2b, Jeremy 2026-09-06).  Both rules SWAP
-- the two faces of a two-layer wrapper, so the INNER boundary stops
-- presenting the abstract name `` ` Y `` and starts presenting Y's REP.
-- A rep is a type over the PLAIN exterior; inside Θ₂'s LOCKS it need not
-- be nameable at all, and `env`'s last premise then fails — that was the
-- wall (the old proof/PreserveObstruct §4 refutation, and the whole of
-- proof/WallReach, proof/WallGrounding, proof/ChainScoped).
--
-- So the frames move with the faces:
--
--   (V ⟪ Θ₁ , c ⟫) ⟪ Θ₂ , unseal Y ⟫
--     -→ (V ⟪ Θ₁ ⋉ Θ₂ , c′ ⟫) ⟪ dropLocks Θ₂ , mkId A ⟫
--
-- `dropLocks Θ₂` keeps Θ₂'s binds and unmasks; `Θ₁ ⋉ Θ₂` appends Θ₂'s
-- whole SCOPE (locks AND unlocks, in order, lifted past Θ₂'s owners) at
-- Θ₁'s TAIL, where `scope` applies it FIRST.
--
-- WHY IT WORKS, in one line: `interior (dropLocks Θ₂) Δ ≡ convCtx Θ₂ Δ`
-- (§3), and the rep the outer `unseal Y` hands back IS the redex's own exterior
-- type lifted, `A ≡ shiftBy (numBinds Θ₂) C` with `Δ ⊢ᵗ C` — so
-- `wf-shiftBy-pushBinds` gives the premise the wall used to deny (§6).
--
--   §1  the two lookup transports (`unlockedScope-∋bind`, `pushBinds-∋`,
--       and the two entry-level companions the moved scope's `MorphWf`
--       needs)
--   §2  the list algebra of `scopeOf`/`dropLocks`/`_⋉_`
--   §3  the two type-context identities
--   §4  the FRAME LEMMAS: the value's frame and its face type context are
--       REFINED by the move, unconditionally
--   §5  `MorphWf` for the two new frames
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
open import strong.TermSubst using (⊢retag)
open import strong.Reduction using (scopeOf; dropLocks; _⋉_)
open import strong.proof.Preserve using (CancelRCase; IdPushCase)

------------------------------------------------------------------------
-- §1  Lookup transports
------------------------------------------------------------------------

-- An owner survives `unlockedScope`: it only unmasks (`unmaskEnt`, which fixes
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

-- The owner prefix lifts an owner: slot Y in the tail becomes slot
-- `length As + Y` at the rep lifted past the `length As` prefix owners.
pushBinds-∋ : ∀ (As : List Ty) {Δ Y A}
  → Δ ∋ Y := A → pushBinds As Δ ∋ (length As + Y) := shiftBy (length As) A
pushBinds-∋ []       d = d
pushBinds-∋ (C ∷ As) d = es (pushBinds-∋ As d)

-- … and the two ENTRY-level companions, which is all a moved `lock` or
-- `unlock` needs: a lock names a VISIBLE slot, an unlock names a slot
-- that merely EXISTS.
pushBinds-∋tv : ∀ (As : List Ty) {Δ Y}
  → Δ ∋tv Y → pushBinds As Δ ∋tv (length As + Y)
pushBinds-∋tv []       tv           = tv
pushBinds-∋tv (C ∷ As) tv with pushBinds-∋tv As tv
... | E , d , v = _ , es d , renᵉ-Nameable v

pushBinds-∋e : ∀ (As : List Ty) {Δ Y E} → Δ ∋e Y , E
        → ∃[ E′ ] (pushBinds As Δ ∋e (length As + Y) , E′)
pushBinds-∋e []       d = _ , d
pushBinds-∋e (C ∷ As) d with pushBinds-∋e As d
... | E′ , d′ = _ , es d′

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


-- DROPPING THE LOCKS KEEPS THE OWNERS.
repsOf-dropLocks : (Θ : CtxMorph) → repsOf (dropLocks Θ) ≡ repsOf Θ
repsOf-dropLocks []             = refl
repsOf-dropLocks (bind A ∷ Θ)   = cong (A ∷_) (repsOf-dropLocks Θ)
repsOf-dropLocks (unlock X ∷ Θ) = repsOf-dropLocks Θ
repsOf-dropLocks (lock X ∷ Θ)   = repsOf-dropLocks Θ

numBinds-dropLocks : (Θ : CtxMorph) → numBinds (dropLocks Θ) ≡ numBinds Θ
numBinds-dropLocks Θ = cong length (repsOf-dropLocks Θ)

-- `scope`/`unlockedScope` of an append: the tail applies FIRST.
scope-++ : (Θ Ψ : CtxMorph) (Δ : Ctxᵗ) → scope (Θ ++ Ψ) Δ ≡ scope Θ (scope Ψ Δ)
scope-++ []             Ψ Δ = refl
scope-++ (bind A ∷ Θ)   Ψ Δ = scope-++ Θ Ψ Δ
scope-++ (unlock X ∷ Θ) Ψ Δ = cong (unmask X) (scope-++ Θ Ψ Δ)
scope-++ (lock X ∷ Θ)   Ψ Δ = cong (mask X) (scope-++ Θ Ψ Δ)

unlockedScope-++ : (Θ Ψ : CtxMorph) (Δ : Ctxᵗ)
  → unlockedScope (Θ ++ Ψ) Δ ≡ unlockedScope Θ (unlockedScope Ψ Δ)
unlockedScope-++ []             Ψ Δ = refl
unlockedScope-++ (bind A ∷ Θ)   Ψ Δ = unlockedScope-++ Θ Ψ Δ
unlockedScope-++ (unlock X ∷ Θ) Ψ Δ = cong (unmask X) (unlockedScope-++ Θ Ψ Δ)
unlockedScope-++ (lock X ∷ Θ)   Ψ Δ = unlockedScope-++ Θ Ψ Δ

-- THE MOVED SCOPE, APPLIED PAST THE OWNER PREFIX, IS THE ORIGINAL SCOPE
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

------------------------------------------------------------------------
-- §3  The two type-context identities
------------------------------------------------------------------------

scope-dropLocks : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scope (dropLocks Θ) Δ ≡ unlockedScope Θ Δ
scope-dropLocks []             Δ = refl
scope-dropLocks (bind A ∷ Θ)   Δ = scope-dropLocks Θ Δ
scope-dropLocks (unlock X ∷ Θ) Δ = cong (unmask X) (scope-dropLocks Θ Δ)
scope-dropLocks (lock X ∷ Θ)   Δ = scope-dropLocks Θ Δ

unlockedScope-dropLocks : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → unlockedScope (dropLocks Θ) Δ ≡ unlockedScope Θ Δ
unlockedScope-dropLocks []             Δ = refl
unlockedScope-dropLocks (bind A ∷ Θ)   Δ = unlockedScope-dropLocks Θ Δ
unlockedScope-dropLocks (unlock X ∷ Θ) Δ =
  cong (unmask X) (unlockedScope-dropLocks Θ Δ)
unlockedScope-dropLocks (lock X ∷ Θ)   Δ = unlockedScope-dropLocks Θ Δ

-- THE HEADLINE IDENTITY.  Once the locks are gone the frame's INTERIOR
-- IS ITS FACE TYPE CONTEXT — so a rep read on the face is nameable
-- inside, and nothing has to be assumed about the world.
interior-dropLocks : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (dropLocks Θ) Δ ≡ convCtx Θ Δ
interior-dropLocks Θ Δ
  rewrite repsOf-dropLocks Θ | scope-dropLocks Θ Δ = refl

convCtx-dropLocks : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → convCtx (dropLocks Θ) Δ ≡ convCtx Θ Δ
convCtx-dropLocks Θ Δ
  rewrite repsOf-dropLocks Θ | unlockedScope-dropLocks Θ Δ = refl

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
-- §4  THE FRAME LEMMAS
------------------------------------------------------------------------

-- A rep survives `unlockedScope` and the owner prefix (this is
-- `wf-unlockedScope`'s reason for existing: `scope` would not do —
-- masking is what the wall was about).
wf-unlockedScope : ∀ {Δ A} (Θ : CtxMorph) → Δ ⊢ᵗ A → unlockedScope Θ Δ ⊢ᵗ A
wf-unlockedScope Θ w = ⊑-wf (Δ⊑unlockedScope Θ _) w

wf-convCtx : ∀ {Δ A} (Θ : CtxMorph)
  → Δ ⊢ᵗ A → convCtx Θ Δ ⊢ᵗ shiftBy (numBinds Θ) A
wf-convCtx Θ w = wf-shiftBy-pushBinds (repsOf Θ) (wf-unlockedScope Θ w)

-- THE VALUE'S FRAME IS REFINED BY THE MOVE.  Everything Θ₂ masked, the
-- moved scope masks again — at the same slots, in the same order, one
-- prefix further in (`scope-scopeOf`) — and the RETAINED unmasks only add
-- nameability (`Δ⊑unlockedScope`).  So `⊢retag` carries the value across.
--
-- THIS IS THE LEMMA THAT DECIDES THE DESIGN.  Moving only the LOCKS
-- would need `scope (locks Θ₂) (unlockedScope Θ₂ Δ) ⊒ scope Θ₂ Δ`, which
-- is FALSE at a same-slot `unlock`/`lock` pair
-- (`Θ₂ = unlock 0 ∷ lock 0 ∷ []` over an already-blocked slot).  Moving
-- the WHOLE scope keeps the order, and then the refinement is
-- unconditional.
frame-move : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → interior Θ₁ (interior Θ₂ Δ) ⊑ interior (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
frame-move Θ₁ Θ₂ Δ =
  subst (λ Ξ → interior Θ₁ (interior Θ₂ Δ) ⊑ Ξ) (sym eq)
        (⊑-interior Θ₁ (⊑-pushBinds (repsOf Θ₂)
                          (⊑-scope Θ₂ (Δ⊑unlockedScope Θ₂ Δ))))
  where
  eq : interior (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
         ≡ interior Θ₁ (pushBinds (repsOf Θ₂) (scope Θ₂ (unlockedScope Θ₂ Δ)))
  eq = trans (interior-⋉ Θ₁ Θ₂ (interior (dropLocks Θ₂) Δ))
             (cong (λ Ξ → pushBinds (repsOf Θ₁) (scope Θ₁ Ξ))
                   (trans (cong (scope (scopeOf (numBinds Θ₂) Θ₂))
                                (interior-dropLocks Θ₂ Δ))
                          (scope-scopeOf (repsOf Θ₂) Θ₂ (unlockedScope Θ₂ Δ))))

-- … and so is its FACE type context, for the same reason plus the one
-- the move exists for: the inner face is now read where Θ₂'s locks are
-- not applied at all.
face-move : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → convCtx Θ₁ (interior Θ₂ Δ) ⊑ convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
face-move Θ₁ Θ₂ Δ =
  subst (λ Ξ → convCtx Θ₁ (interior Θ₂ Δ) ⊑ Ξ) (sym eq)
        (⊑-convCtx Θ₁ (⊑-trans (interior⊑convCtx Θ₂ Δ)
                          (Δ⊑unlockedScope (scopeOf (numBinds Θ₂) Θ₂)
                                           (convCtx Θ₂ Δ))))
  where
  eq : convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
         ≡ convCtx Θ₁ (unlockedScope (scopeOf (numBinds Θ₂) Θ₂)
                                     (convCtx Θ₂ Δ))
  eq = trans (convCtx-⋉ Θ₁ Θ₂ (interior (dropLocks Θ₂) Δ))
             (cong (λ Ξ → pushBinds (repsOf Θ₁)
                            (unlockedScope Θ₁
                              (unlockedScope (scopeOf (numBinds Θ₂) Θ₂) Ξ)))
                   (interior-dropLocks Θ₂ Δ))

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

-- THE WITNESS.  `Θ✗` masks slot 0 and then re-exposes it — both entries
-- are `MorphWf`-legal at `Δ✗` (a lock names a VISIBLE slot, an unlock a slot
-- that EXISTS) — so the redex's interior leaves slot 0 nameable.
Θ✗ : CtxMorph
Θ✗ = unlock 0 ∷ lock 0 ∷ []

Δ✗ : Ctxᵗ
Δ✗ = bind `ℕ ∷ []

MorphWf-Θ✗ : MorphWf Δ✗ Θ✗
MorphWf-Θ✗ = mw-u ez (mw-l (bind `ℕ , ez , nameable-b) mw[])

_ : interior Θ✗ Δ✗ ≡ bind `ℕ ∷ []
_ = refl

-- … but the lock-only contractum's interior BLOCKS it.
_ : scope (locksOnly (numBinds Θ✗) Θ✗) (interior (dropLocks Θ✗) Δ✗)
      ≡ masked (bind `ℕ) ∷ []
_ = refl

¬frame-locksOnly :
  ¬ (interior [] (interior Θ✗ Δ✗)
       ⊑ interior ([] ++ locksOnly (numBinds Θ✗) Θ✗)
                  (interior (dropLocks Θ✗) Δ✗))
¬frame-locksOnly (le∷ () ls)

-- THE OWNER, ON THE CONTRACTUM'S INNER FACE TYPE CONTEXT.  The outer
-- reveal's own lookup — read on `convCtx Θ₂ Δ`, which the move makes the
-- inner boundary's exterior — transported past the moved scope, past Θ₁'s
-- unmasks, and past Θ₁'s owners.  NO `maskOnly` step: the old proof had
-- to push the lookup INSIDE Θ₂'s locks, and this one never does.
move-∋ : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {Y : ℕ} {A : Ty}
  → convCtx Θ₂ Δ ∋ Y := A
  → convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
      ∋ (numBinds Θ₁ + Y) := shiftBy (numBinds Θ₁) A
move-∋ Θ₁ Θ₂ {Δ = Δ} {Y = Y} {A = A} d =
  subst (λ Ξ → Ξ ∋ (numBinds Θ₁ + Y) := shiftBy (numBinds Θ₁) A)
        (sym (convCtx-⋉ Θ₁ Θ₂ (interior (dropLocks Θ₂) Δ)))
        (pushBinds-∋ (repsOf Θ₁)
          (unlockedScope-∋bind Θ₁
            (unlockedScope-∋bind (scopeOf (numBinds Θ₂) Θ₂)
              (subst (λ Ξ → Ξ ∋ Y := A) (sym (interior-dropLocks Θ₂ Δ)) d))))

-- The face type context of the moved inner frame also carries every rep
-- its own exterior carries — it only ADDS unmasks and the owner prefix.
wf-face-move : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {A : Ty}
  → interior (dropLocks Θ₂) Δ ⊢ᵗ A
  → convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ) ⊢ᵗ shiftBy (numBinds Θ₁) A
wf-face-move Θ₁ Θ₂ {Δ = Δ} {A = A} w =
  subst (λ Ξ → Ξ ⊢ᵗ shiftBy (numBinds Θ₁) A)
        (sym (convCtx-⋉ Θ₁ Θ₂ (interior (dropLocks Θ₂) Δ)))
        (wf-shiftBy-pushBinds (repsOf Θ₁)
          (wf-unlockedScope Θ₁ (wf-unlockedScope (scopeOf (numBinds Θ₂) Θ₂) w)))

------------------------------------------------------------------------
-- §5  `MorphWf` for the two new frames
------------------------------------------------------------------------

-- Every `MorphWf` premise is read on the PLAIN exterior (simultaneity), so
-- an append is just a pair …
MorphWf-++ : ∀ {Δ} (Θ Ψ : CtxMorph) → MorphWf Δ Θ → MorphWf Δ Ψ
  → MorphWf Δ (Θ ++ Ψ)
MorphWf-++ []             Ψ mw[]        bΨ = bΨ
MorphWf-++ (bind A ∷ Θ)   Ψ (mw-b w b)  bΨ = mw-b w (MorphWf-++ Θ Ψ b bΨ)
MorphWf-++ (lock X ∷ Θ)   Ψ (mw-l tv b) bΨ = mw-l tv (MorphWf-++ Θ Ψ b bΨ)
MorphWf-++ (unlock X ∷ Θ) Ψ (mw-u d b)  bΨ = mw-u d (MorphWf-++ Θ Ψ b bΨ)

-- … and dropping entries is free.
MorphWf-dropLocks : ∀ {Δ} (Θ : CtxMorph) → MorphWf Δ Θ → MorphWf Δ (dropLocks Θ)
MorphWf-dropLocks []             mw[]        = mw[]
MorphWf-dropLocks (bind A ∷ Θ)   (mw-b w b)  = mw-b w (MorphWf-dropLocks Θ b)
MorphWf-dropLocks (lock X ∷ Θ)   (mw-l tv b) = MorphWf-dropLocks Θ b
MorphWf-dropLocks (unlock X ∷ Θ) (mw-u d b)  = mw-u d (MorphWf-dropLocks Θ b)

-- THE MOVED SCOPE IS WELL FORMED WHERE IT LANDS.  A `lock X` of Θ₂ named
-- a VISIBLE slot of Δ; the move reads it at `numBinds Θ₂ + X` on
-- `convCtx Θ₂ Δ`, where Θ₂'s own locks are NOT applied — so the slot is
-- still visible, which is precisely the nameability the move buys.
MorphWf-scopeOf : ∀ (As : List Ty) (Θ : CtxMorph) {Δ Ξ : Ctxᵗ}
  → Δ ⊑ Ξ → MorphWf Δ Θ → MorphWf (pushBinds As Ξ) (scopeOf (length As) Θ)
MorphWf-scopeOf As []             ls mw[]        = mw[]
MorphWf-scopeOf As (bind A ∷ Θ)   ls (mw-b w b)  = MorphWf-scopeOf As Θ ls b
MorphWf-scopeOf As (lock X ∷ Θ)   ls (mw-l tv b) =
  mw-l (pushBinds-∋tv As (⊑-tv ls tv)) (MorphWf-scopeOf As Θ ls b)
MorphWf-scopeOf As (unlock X ∷ Θ) ls (mw-u d b)  with ⊑-∋e ls d
... | E′ , d′ , _ with pushBinds-∋e As d′
...   | E″ , d″ = mw-u d″ (MorphWf-scopeOf As Θ ls b)

MorphWf-⋉ : ∀ (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ}
  → MorphWf (interior Θ₂ Δ) Θ₁ → MorphWf Δ Θ₂
  → MorphWf (interior (dropLocks Θ₂) Δ) (Θ₁ ⋉ Θ₂)
MorphWf-⋉ Θ₁ Θ₂ {Δ = Δ} b₁ b₂ =
  subst (λ Ξ → MorphWf Ξ (Θ₁ ⋉ Θ₂)) (sym (interior-dropLocks Θ₂ Δ))
        (MorphWf-++ Θ₁ (scopeOf (numBinds Θ₂) Θ₂)
                (MorphWf-⊑ (interior⊑convCtx Θ₂ Δ) b₁)
                (MorphWf-scopeOf (repsOf Θ₂) Θ₂ (Δ⊑unlockedScope Θ₂ Δ) b₂))

------------------------------------------------------------------------
-- §6  THE TWO CASES
------------------------------------------------------------------------

-- What both share: the outer boundary of the contractum.  Its frame is
-- `dropLocks Θ₂`, its face the identity at the rep, and its two
-- well-formedness obligations are the redex's own exterior type lifted.
module _ {Δ : Ctxᵗ} (Θ₂ : CtxMorph) {A C : Ty}
         (wE : Δ ⊢ᵗ C) (eqAC : A ≡ shiftBy (numBinds Θ₂) C) where

  -- THE PREMISE THE WALL USED TO DENY.  `interior (dropLocks Θ₂) Δ` IS
  -- `convCtx Θ₂ Δ` (§3), and A is C lifted past Θ₂'s owners — so this is
  -- `wf-shiftBy-pushBinds` at Θ₂'s reps, and nothing else.
  moved-scoped : interior (dropLocks Θ₂) Δ ⊢ᵗ A
  moved-scoped rewrite eqAC | interior-dropLocks Θ₂ Δ = wf-convCtx Θ₂ wE

  moved-face : convCtx (dropLocks Θ₂) Δ
                 ⊢ mkId A ∶ A ⇝ shiftBy (numBinds (dropLocks Θ₂)) C
  moved-face rewrite numBinds-dropLocks Θ₂ | convCtx-dropLocks Θ₂ Δ | eqAC =
    mkId-⊢ (wf-convCtx Θ₂ wE)

-- ── IDPUSH ─────────────────────────────────────────────────────────────
-- The faces are swapped and the scope moves.  Four moves, one per premise
-- of the contractum's inner `env`:
--
--   FRAME     `Θ₁ ⋉ Θ₂`, well formed by §5.
--   INTERIOR  `V`, retagged along `frame-move` (§4).
--   FACE      `unseal X` at the owner `move-∋` transports (§4); the two
--             names are forced equal by the id-face's own exterior,
--             `X ≡ numBinds Θ₁ + Y` (proof/IdLayer, `idpush-name`).
--   EXTERIOR  `moved-scoped` — the premise that used to be the wall.
preserve-IdPush : IdPushCase
preserve-IdPush {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                {A = A} {C = C} v d
                (env mw₂ (env mw₁ ⊢V ⊢cᵢ wE′) (conv-unseal dₒ) wE) =
  env (MorphWf-dropLocks Θ₂ mw₂)
      (env (MorphWf-⋉ Θ₁ Θ₂ mw₁ mw₂) ⊢V′ faceᵢ (moved-scoped Θ₂ wE eqAC))
      (moved-face Θ₂ wE eqAC)
      wE
  where
  -- The outer `unseal Y`'s rep is `shiftBy (numBinds Θ₂) C`; it IS A.
  eqAC : A ≡ shiftBy (numBinds Θ₂) C
  eqAC = ∋:=-det d dₒ

  -- The inner `id (` X)` face: its interior is `` ` X ``, and its
  -- exterior `shiftBy (numBinds Θ₁) (` Y)` equals `` ` X ``.
  eqX : numBinds Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (shiftBy-var (numBinds Θ₁) Y)) (conv-idv-tgt ⊢cᵢ))

  ⊢V′ : interior (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ) ∣ [] ⊢ V ⦂ ` X
  ⊢V′ = ⊢retag (frame-move Θ₁ Θ₂ Δ)
          (subst (λ T → interior Θ₁ (interior Θ₂ Δ) ∣ [] ⊢ V ⦂ T)
                 (conv-idv-src ⊢cᵢ) ⊢V)

  dX : convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
         ∋ X := shiftBy (numBinds Θ₁) A
  dX = subst (λ Z → convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
                      ∋ Z := shiftBy (numBinds Θ₁) A)
             eqX (move-∋ Θ₁ Θ₂ d)

  faceᵢ : convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
            ⊢ unseal X ∶ ` X ⇝ shiftBy (numBinds (Θ₁ ⋉ Θ₂)) A
  faceᵢ rewrite numBinds-⋉ Θ₁ Θ₂ = conv-unseal dX

-- ── CANCELR ────────────────────────────────────────────────────────────
-- The same four moves, with both faces neutralised instead of swapped.
-- THE FACE EQUATION — `V`'s interior type IS the new inner face — is the
-- one piece of content: `seal X`'s source is X's rep, and X's rep on the
-- contractum's inner face type context is `shiftBy (numBinds Θ₁) A`, so
-- `∋:=-det` closes it.  The old proof had to run that lookup INSIDE Θ₂'s
-- locks (whence `ScopedAtUnseal`); this one runs it on the face.
preserve-CancelR : CancelRCase
preserve-CancelR {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {C = C} v d
                 (env mw₂ (env mw₁ ⊢V ⊢c₁ wE′) (conv-unseal dₒ) wE) =
  env (MorphWf-dropLocks Θ₂ mw₂)
      (env (MorphWf-⋉ Θ₁ Θ₂ mw₁ mw₂) ⊢V′ faceᵢ (moved-scoped Θ₂ wE eqAC))
      (moved-face Θ₂ wE eqAC)
      wE
  where
  eqAC : A ≡ shiftBy (numBinds Θ₂) C
  eqAC = ∋:=-det d dₒ

  eqX : numBinds Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (shiftBy-var (numBinds Θ₁) Y)) (conv-seal-tgt ⊢c₁))

  dX : convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
         ∋ X := shiftBy (numBinds Θ₁) A
  dX = subst (λ Z → convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
                      ∋ Z := shiftBy (numBinds Θ₁) A)
             eqX (move-∋ Θ₁ Θ₂ d)

  -- `seal X`'s source, read where the move puts it.
  eqV : _ ≡ shiftBy (numBinds Θ₁) A
  eqV = ∋:=-det (⊑-kn (face-move Θ₁ Θ₂ Δ)
                      (seal-face-is-the-owners-rep ⊢c₁))
                dX

  ⊢V′ : interior (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ) ∣ []
          ⊢ V ⦂ shiftBy (numBinds Θ₁) A
  ⊢V′ = ⊢retag (frame-move Θ₁ Θ₂ Δ)
          (subst (λ T → interior Θ₁ (interior Θ₂ Δ) ∣ [] ⊢ V ⦂ T) eqV ⊢V)

  faceᵢ : convCtx (Θ₁ ⋉ Θ₂) (interior (dropLocks Θ₂) Δ)
            ⊢ mkId (shiftBy (numBinds Θ₁) A)
            ∶ shiftBy (numBinds Θ₁) A ⇝ shiftBy (numBinds (Θ₁ ⋉ Θ₂)) A
  faceᵢ rewrite numBinds-⋉ Θ₁ Θ₂ =
    mkId-⊢ (wf-face-move Θ₁ Θ₂ (moved-scoped Θ₂ wE eqAC))

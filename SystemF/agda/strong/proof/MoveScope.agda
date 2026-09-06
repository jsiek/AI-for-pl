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
--     -→ (V ⟪ Θ₁ ◃ Θ₂ , c′ ⟫) ⟪ unlocked Θ₂ , idc A ⟫
--
-- `unlocked Θ₂` keeps Θ₂'s binds and unmasks; `Θ₁ ◃ Θ₂` appends Θ₂'s
-- whole SCOPE (locks AND unlocks, in order, lifted past Θ₂'s owners) at
-- Θ₁'s TAIL, where `scp` applies it FIRST.
--
-- WHY IT WORKS, in one line: `intC (unlocked Θ₂) Δ ≡ fceC Θ₂ Δ` (§3), and
-- the rep the outer `unseal Y` hands back IS the redex's own exterior
-- type lifted, `A ≡ liftN (nbind Θ₂) C` with `Δ ⊢ᵗ C` — so
-- `wf-liftN-prep` gives the premise the wall used to deny (§6).
--
--   §1  the two lookup transports (`fscp-∋bind`, `prep-∋`, and the two
--       entry-level companions the moved scope's `Bwf` needs)
--   §2  the list algebra of `moveS`/`unlocked`/`_◃_`
--   §3  the two type-context identities
--   §4  the FRAME LEMMAS: the value's frame and its face type context are
--       REFINED by the move, unconditionally
--   §5  `Bwf` for the two new frames
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
open import strong.Reduction using (moveS; unlocked; _◃_)
open import strong.proof.Preserve using (CancelRCase; IdPushCase)

------------------------------------------------------------------------
-- §1  Lookup transports
------------------------------------------------------------------------

-- An owner survives `fscp`: it only unmasks (`unblk`, which fixes
-- `bind`) and skips locks, so a `bind` lookup is preserved unchanged.
fscp-∋bind : ∀ (Θ : CtxMorph) {Δ Y A}
  → Δ ∋ Y := A → fscp Θ Δ ∋ Y := A
fscp-∋bind []              d = d
fscp-∋bind (bind C ∷ Θ)    d = fscp-∋bind Θ d
fscp-∋bind (lock Z ∷ Θ)    d = fscp-∋bind Θ d
fscp-∋bind (unlock Z ∷ Θ) {Y = Y} d with Z ≟ℕ Y
... | yes refl = upd-hit  unblk unblk-comm    (fscp-∋bind Θ d)
... | no  ne   = upd-miss unblk unblk-comm ne (fscp-∋bind Θ d)

-- The owner prefix lifts an owner: slot Y in the tail becomes slot
-- `length As + Y` at the rep lifted past the `length As` prefix owners.
prep-∋ : ∀ (As : List Ty) {Δ Y A}
  → Δ ∋ Y := A → prep As Δ ∋ (length As + Y) := liftN (length As) A
prep-∋ []       d = d
prep-∋ (C ∷ As) d = es (prep-∋ As d)

-- … and the two ENTRY-level companions, which is all a moved `lock` or
-- `unlock` needs: a lock names a VISIBLE slot, an unlock names a slot
-- that merely EXISTS.
prep-∋tv : ∀ (As : List Ty) {Δ Y} → Δ ∋tv Y → prep As Δ ∋tv (length As + Y)
prep-∋tv []       tv           = tv
prep-∋tv (C ∷ As) tv with prep-∋tv As tv
... | E , d , v = _ , es d , renᵉ-Vis v

prep-∋e : ∀ (As : List Ty) {Δ Y E} → Δ ∋e Y , E
        → ∃[ E′ ] (prep As Δ ∋e (length As + Y) , E′)
prep-∋e []       d = _ , d
prep-∋e (C ∷ As) d with prep-∋e As d
... | E′ , d′ = _ , es d′

------------------------------------------------------------------------
-- §2  The list algebra of the move
------------------------------------------------------------------------

-- THE MOVE CARRIES NO BINDER: it moves scope entries only.
reps-moveS : (n : ℕ) (Θ : CtxMorph) → reps (moveS n Θ) ≡ []
reps-moveS n []             = refl
reps-moveS n (bind A ∷ Θ)   = reps-moveS n Θ
reps-moveS n (unlock X ∷ Θ) = reps-moveS n Θ
reps-moveS n (lock X ∷ Θ)   = reps-moveS n Θ

reps-◃ : (Θ₁ Θ₂ : CtxMorph) → reps (Θ₁ ◃ Θ₂) ≡ reps Θ₁
reps-◃ []             Θ₂ = reps-moveS (nbind Θ₂) Θ₂
reps-◃ (bind A ∷ Θ₁)  Θ₂ = cong (A ∷_) (reps-◃ Θ₁ Θ₂)
reps-◃ (unlock X ∷ Θ₁) Θ₂ = reps-◃ Θ₁ Θ₂
reps-◃ (lock X ∷ Θ₁)  Θ₂ = reps-◃ Θ₁ Θ₂

nbind-◃ : (Θ₁ Θ₂ : CtxMorph) → nbind (Θ₁ ◃ Θ₂) ≡ nbind Θ₁
nbind-◃ Θ₁ Θ₂ = cong length (reps-◃ Θ₁ Θ₂)


-- DROPPING THE LOCKS KEEPS THE OWNERS.
reps-unlocked : (Θ : CtxMorph) → reps (unlocked Θ) ≡ reps Θ
reps-unlocked []             = refl
reps-unlocked (bind A ∷ Θ)   = cong (A ∷_) (reps-unlocked Θ)
reps-unlocked (unlock X ∷ Θ) = reps-unlocked Θ
reps-unlocked (lock X ∷ Θ)   = reps-unlocked Θ

nbind-unlocked : (Θ : CtxMorph) → nbind (unlocked Θ) ≡ nbind Θ
nbind-unlocked Θ = cong length (reps-unlocked Θ)

-- `scp`/`fscp` of an append: the tail applies FIRST.
scp-++ : (Θ Ψ : CtxMorph) (Δ : Ctxᵗ) → scp (Θ ++ Ψ) Δ ≡ scp Θ (scp Ψ Δ)
scp-++ []             Ψ Δ = refl
scp-++ (bind A ∷ Θ)   Ψ Δ = scp-++ Θ Ψ Δ
scp-++ (unlock X ∷ Θ) Ψ Δ = cong (unmask X) (scp-++ Θ Ψ Δ)
scp-++ (lock X ∷ Θ)   Ψ Δ = cong (mask X) (scp-++ Θ Ψ Δ)

fscp-++ : (Θ Ψ : CtxMorph) (Δ : Ctxᵗ) → fscp (Θ ++ Ψ) Δ ≡ fscp Θ (fscp Ψ Δ)
fscp-++ []             Ψ Δ = refl
fscp-++ (bind A ∷ Θ)   Ψ Δ = fscp-++ Θ Ψ Δ
fscp-++ (unlock X ∷ Θ) Ψ Δ = cong (unmask X) (fscp-++ Θ Ψ Δ)
fscp-++ (lock X ∷ Θ)   Ψ Δ = fscp-++ Θ Ψ Δ

-- THE MOVED SCOPE, APPLIED PAST THE OWNER PREFIX, IS THE ORIGINAL SCOPE
-- APPLIED UNDER IT.  This is the whole point of the index lift `n + X`,
-- and it is `upd-prep` (strong.Ctx) once per entry.
scp-moveS : (As : List Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scp (moveS (length As) Θ) (prep As Δ) ≡ prep As (scp Θ Δ)
scp-moveS As []             Δ = refl
scp-moveS As (bind A ∷ Θ)   Δ = scp-moveS As Θ Δ
scp-moveS As (unlock X ∷ Θ) Δ =
  trans (cong (unmask (length As + X)) (scp-moveS As Θ Δ))
        (upd-prep unblk As X (scp Θ Δ))
scp-moveS As (lock X ∷ Θ)   Δ =
  trans (cong (mask (length As + X)) (scp-moveS As Θ Δ))
        (upd-prep blk As X (scp Θ Δ))

------------------------------------------------------------------------
-- §3  The two type-context identities
------------------------------------------------------------------------

scp-unlocked : (Θ : CtxMorph) (Δ : Ctxᵗ) → scp (unlocked Θ) Δ ≡ fscp Θ Δ
scp-unlocked []             Δ = refl
scp-unlocked (bind A ∷ Θ)   Δ = scp-unlocked Θ Δ
scp-unlocked (unlock X ∷ Θ) Δ = cong (unmask X) (scp-unlocked Θ Δ)
scp-unlocked (lock X ∷ Θ)   Δ = scp-unlocked Θ Δ

fscp-unlocked : (Θ : CtxMorph) (Δ : Ctxᵗ) → fscp (unlocked Θ) Δ ≡ fscp Θ Δ
fscp-unlocked []             Δ = refl
fscp-unlocked (bind A ∷ Θ)   Δ = fscp-unlocked Θ Δ
fscp-unlocked (unlock X ∷ Θ) Δ = cong (unmask X) (fscp-unlocked Θ Δ)
fscp-unlocked (lock X ∷ Θ)   Δ = fscp-unlocked Θ Δ

-- THE HEADLINE IDENTITY.  Once the locks are gone the frame's INTERIOR
-- IS ITS FACE TYPE CONTEXT — so a rep read on the face is nameable
-- inside, and nothing has to be assumed about the world.
intC-unlocked : (Θ : CtxMorph) (Δ : Ctxᵗ) → intC (unlocked Θ) Δ ≡ fceC Θ Δ
intC-unlocked Θ Δ
  rewrite reps-unlocked Θ | scp-unlocked Θ Δ = refl

fceC-unlocked : (Θ : CtxMorph) (Δ : Ctxᵗ) → fceC (unlocked Θ) Δ ≡ fceC Θ Δ
fceC-unlocked Θ Δ
  rewrite reps-unlocked Θ | fscp-unlocked Θ Δ = refl

-- The two frames of the contractum, unfolded.
intC-◃ : (Θ₁ Θ₂ : CtxMorph) (Ξ : Ctxᵗ)
  → intC (Θ₁ ◃ Θ₂) Ξ
      ≡ prep (reps Θ₁) (scp Θ₁ (scp (moveS (nbind Θ₂) Θ₂) Ξ))
intC-◃ Θ₁ Θ₂ Ξ rewrite reps-◃ Θ₁ Θ₂ =
  cong (prep (reps Θ₁)) (scp-++ Θ₁ (moveS (nbind Θ₂) Θ₂) Ξ)

fceC-◃ : (Θ₁ Θ₂ : CtxMorph) (Ξ : Ctxᵗ)
  → fceC (Θ₁ ◃ Θ₂) Ξ
      ≡ prep (reps Θ₁) (fscp Θ₁ (fscp (moveS (nbind Θ₂) Θ₂) Ξ))
fceC-◃ Θ₁ Θ₂ Ξ rewrite reps-◃ Θ₁ Θ₂ =
  cong (prep (reps Θ₁)) (fscp-++ Θ₁ (moveS (nbind Θ₂) Θ₂) Ξ)

------------------------------------------------------------------------
-- §4  THE FRAME LEMMAS
------------------------------------------------------------------------

-- A rep survives `fscp` and the owner prefix (this is `wf-fscp`'s reason
-- for existing: `scp` would not do — masking is what the wall was about).
wf-fscp : ∀ {Δ A} (Θ : CtxMorph) → Δ ⊢ᵗ A → fscp Θ Δ ⊢ᵗ A
wf-fscp Θ w = ⊑-wf (Δ⊑fscp Θ _) w

wf-fceC : ∀ {Δ A} (Θ : CtxMorph)
  → Δ ⊢ᵗ A → fceC Θ Δ ⊢ᵗ liftN (nbind Θ) A
wf-fceC Θ w = wf-liftN-prep (reps Θ) (wf-fscp Θ w)

-- THE VALUE'S FRAME IS REFINED BY THE MOVE.  Everything Θ₂ masked, the
-- moved scope masks again — at the same slots, in the same order, one
-- prefix further in (`scp-moveS`) — and the RETAINED unmasks only add
-- nameability (`Δ⊑fscp`).  So `⊢retag` carries the value across.
--
-- THIS IS THE LEMMA THAT DECIDES THE DESIGN.  Moving only the LOCKS
-- would need `scp (locks Θ₂) (fscp Θ₂ Δ) ⊒ scp Θ₂ Δ`, which is FALSE at
-- a same-slot `unlock`/`lock` pair (`Θ₂ = unlock 0 ∷ lock 0 ∷ []` over an
-- already-blocked slot).  Moving the WHOLE scope keeps the order, and
-- then the refinement is unconditional.
frame-move : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → intC Θ₁ (intC Θ₂ Δ) ⊑ intC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
frame-move Θ₁ Θ₂ Δ =
  subst (λ Ξ → intC Θ₁ (intC Θ₂ Δ) ⊑ Ξ) (sym eq)
        (⊑-intC Θ₁ (⊑-prep (reps Θ₂) (⊑-scp Θ₂ (Δ⊑fscp Θ₂ Δ))))
  where
  eq : intC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
         ≡ intC Θ₁ (prep (reps Θ₂) (scp Θ₂ (fscp Θ₂ Δ)))
  eq = trans (intC-◃ Θ₁ Θ₂ (intC (unlocked Θ₂) Δ))
             (cong (λ Ξ → prep (reps Θ₁) (scp Θ₁ Ξ))
                   (trans (cong (scp (moveS (nbind Θ₂) Θ₂))
                                (intC-unlocked Θ₂ Δ))
                          (scp-moveS (reps Θ₂) Θ₂ (fscp Θ₂ Δ))))

-- … and so is its FACE type context, for the same reason plus the one
-- the move exists for: the inner face is now read where Θ₂'s locks are
-- not applied at all.
face-move : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → fceC Θ₁ (intC Θ₂ Δ) ⊑ fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
face-move Θ₁ Θ₂ Δ =
  subst (λ Ξ → fceC Θ₁ (intC Θ₂ Δ) ⊑ Ξ) (sym eq)
        (⊑-fceC Θ₁ (⊑-trans (intC⊑fceC Θ₂ Δ)
                            (Δ⊑fscp (moveS (nbind Θ₂) Θ₂) (fceC Θ₂ Δ))))
  where
  eq : fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
         ≡ fceC Θ₁ (fscp (moveS (nbind Θ₂) Θ₂) (fceC Θ₂ Δ))
  eq = trans (fceC-◃ Θ₁ Θ₂ (intC (unlocked Θ₂) Δ))
             (cong (λ Ξ → prep (reps Θ₁)
                            (fscp Θ₁ (fscp (moveS (nbind Θ₂) Θ₂) Ξ)))
                   (intC-unlocked Θ₂ Δ))

------------------------------------------------------------------------
-- §4b  WHY THE UNLOCKS TRAVEL TOO — the lock-only move, REFUTED
------------------------------------------------------------------------

-- The obvious cheaper move appends only Θ₂'s LOCKS.  It reorders a
-- same-slot unlock/lock pair, because `scp` applies the list HEAD-LAST,
-- and then the value's frame is not REFINED but CORRUPTED: a slot the
-- value may name in the redex is MASKED in the contractum.
locksOnly : ℕ → CtxMorph → CtxMorph
locksOnly n []             = []
locksOnly n (bind A ∷ Θ)   = locksOnly n Θ
locksOnly n (unlock X ∷ Θ) = locksOnly n Θ
locksOnly n (lock X ∷ Θ)   = lock (n + X) ∷ locksOnly n Θ

-- THE WITNESS.  `Θ✗` masks slot 0 and then re-exposes it — both entries
-- are `Bwf`-legal at `Δ✗` (a lock names a VISIBLE slot, an unlock a slot
-- that EXISTS) — so the redex's interior leaves slot 0 nameable.
Θ✗ : CtxMorph
Θ✗ = unlock 0 ∷ lock 0 ∷ []

Δ✗ : Ctxᵗ
Δ✗ = bind `ℕ ∷ []

Bwf-Θ✗ : Bwf Δ✗ Θ✗
Bwf-Θ✗ = bw-u ez (bw-l (bind `ℕ , ez , vis-b) bw[])

_ : intC Θ✗ Δ✗ ≡ bind `ℕ ∷ []
_ = refl

-- … but the lock-only contractum's interior BLOCKS it.
_ : scp (locksOnly (nbind Θ✗) Θ✗) (intC (unlocked Θ✗) Δ✗)
      ≡ blk (bind `ℕ) ∷ []
_ = refl

¬frame-locksOnly :
  ¬ (intC [] (intC Θ✗ Δ✗)
       ⊑ intC ([] ++ locksOnly (nbind Θ✗) Θ✗) (intC (unlocked Θ✗) Δ✗))
¬frame-locksOnly (le∷ () ls)

-- THE OWNER, ON THE CONTRACTUM'S INNER FACE TYPE CONTEXT.  The outer
-- reveal's own lookup — read on `fceC Θ₂ Δ`, which the move makes the
-- inner boundary's exterior — transported past the moved scope, past Θ₁'s
-- unmasks, and past Θ₁'s owners.  NO `maskOnly` step: the old proof had
-- to push the lookup INSIDE Θ₂'s locks, and this one never does.
move-∋ : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {Y : ℕ} {A : Ty}
  → fceC Θ₂ Δ ∋ Y := A
  → fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
      ∋ (nbind Θ₁ + Y) := liftN (nbind Θ₁) A
move-∋ Θ₁ Θ₂ {Δ = Δ} {Y = Y} {A = A} d =
  subst (λ Ξ → Ξ ∋ (nbind Θ₁ + Y) := liftN (nbind Θ₁) A)
        (sym (fceC-◃ Θ₁ Θ₂ (intC (unlocked Θ₂) Δ)))
        (prep-∋ (reps Θ₁)
          (fscp-∋bind Θ₁
            (fscp-∋bind (moveS (nbind Θ₂) Θ₂)
              (subst (λ Ξ → Ξ ∋ Y := A) (sym (intC-unlocked Θ₂ Δ)) d))))

-- The face type context of the moved inner frame also carries every rep
-- its own exterior carries — it only ADDS unmasks and the owner prefix.
wf-face-move : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} {A : Ty}
  → intC (unlocked Θ₂) Δ ⊢ᵗ A
  → fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ) ⊢ᵗ liftN (nbind Θ₁) A
wf-face-move Θ₁ Θ₂ {Δ = Δ} {A = A} w =
  subst (λ Ξ → Ξ ⊢ᵗ liftN (nbind Θ₁) A)
        (sym (fceC-◃ Θ₁ Θ₂ (intC (unlocked Θ₂) Δ)))
        (wf-liftN-prep (reps Θ₁)
          (wf-fscp Θ₁ (wf-fscp (moveS (nbind Θ₂) Θ₂) w)))

------------------------------------------------------------------------
-- §5  `Bwf` for the two new frames
------------------------------------------------------------------------

-- Every `Bwf` premise is read on the PLAIN exterior (simultaneity), so
-- an append is just a pair …
Bwf-++ : ∀ {Δ} (Θ Ψ : CtxMorph) → Bwf Δ Θ → Bwf Δ Ψ → Bwf Δ (Θ ++ Ψ)
Bwf-++ []             Ψ bw[]        bΨ = bΨ
Bwf-++ (bind A ∷ Θ)   Ψ (bw-b w b)  bΨ = bw-b w (Bwf-++ Θ Ψ b bΨ)
Bwf-++ (lock X ∷ Θ)   Ψ (bw-l tv b) bΨ = bw-l tv (Bwf-++ Θ Ψ b bΨ)
Bwf-++ (unlock X ∷ Θ) Ψ (bw-u d b)  bΨ = bw-u d (Bwf-++ Θ Ψ b bΨ)

-- … and dropping entries is free.
Bwf-unlocked : ∀ {Δ} (Θ : CtxMorph) → Bwf Δ Θ → Bwf Δ (unlocked Θ)
Bwf-unlocked []             bw[]        = bw[]
Bwf-unlocked (bind A ∷ Θ)   (bw-b w b)  = bw-b w (Bwf-unlocked Θ b)
Bwf-unlocked (lock X ∷ Θ)   (bw-l tv b) = Bwf-unlocked Θ b
Bwf-unlocked (unlock X ∷ Θ) (bw-u d b)  = bw-u d (Bwf-unlocked Θ b)

-- THE MOVED SCOPE IS WELL FORMED WHERE IT LANDS.  A `lock X` of Θ₂ named
-- a VISIBLE slot of Δ; the move reads it at `nbind Θ₂ + X` on
-- `fceC Θ₂ Δ`, where Θ₂'s own locks are NOT applied — so the slot is
-- still visible, which is precisely the nameability the move buys.
Bwf-moveS : ∀ (As : List Ty) (Θ : CtxMorph) {Δ Ξ : Ctxᵗ}
  → Δ ⊑ Ξ → Bwf Δ Θ → Bwf (prep As Ξ) (moveS (length As) Θ)
Bwf-moveS As []             ls bw[]        = bw[]
Bwf-moveS As (bind A ∷ Θ)   ls (bw-b w b)  = Bwf-moveS As Θ ls b
Bwf-moveS As (lock X ∷ Θ)   ls (bw-l tv b) =
  bw-l (prep-∋tv As (⊑-tv ls tv)) (Bwf-moveS As Θ ls b)
Bwf-moveS As (unlock X ∷ Θ) ls (bw-u d b)  with ⊑-∋e ls d
... | E′ , d′ , _ with prep-∋e As d′
...   | E″ , d″ = bw-u d″ (Bwf-moveS As Θ ls b)

Bwf-◃ : ∀ (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ}
  → Bwf (intC Θ₂ Δ) Θ₁ → Bwf Δ Θ₂
  → Bwf (intC (unlocked Θ₂) Δ) (Θ₁ ◃ Θ₂)
Bwf-◃ Θ₁ Θ₂ {Δ = Δ} b₁ b₂ =
  subst (λ Ξ → Bwf Ξ (Θ₁ ◃ Θ₂)) (sym (intC-unlocked Θ₂ Δ))
        (Bwf-++ Θ₁ (moveS (nbind Θ₂) Θ₂)
                (Bwf-⊑ (intC⊑fceC Θ₂ Δ) b₁)
                (Bwf-moveS (reps Θ₂) Θ₂ (Δ⊑fscp Θ₂ Δ) b₂))

------------------------------------------------------------------------
-- §6  THE TWO CASES
------------------------------------------------------------------------

-- What both share: the outer boundary of the contractum.  Its frame is
-- `unlocked Θ₂`, its face the identity at the rep, and its two
-- well-formedness obligations are the redex's own exterior type lifted.
module _ {Δ : Ctxᵗ} (Θ₂ : CtxMorph) {A C : Ty}
         (wE : Δ ⊢ᵗ C) (eqAC : A ≡ liftN (nbind Θ₂) C) where

  -- THE PREMISE THE WALL USED TO DENY.  `intC (unlocked Θ₂) Δ` IS
  -- `fceC Θ₂ Δ` (§3), and A is C lifted past Θ₂'s owners — so this is
  -- `wf-liftN-prep` at Θ₂'s reps, and nothing else.
  moved-scoped : intC (unlocked Θ₂) Δ ⊢ᵗ A
  moved-scoped rewrite eqAC | intC-unlocked Θ₂ Δ = wf-fceC Θ₂ wE

  moved-face : fceC (unlocked Θ₂) Δ
                 ⊢ idc A ∶ A ⇝ liftN (nbind (unlocked Θ₂)) C
  moved-face rewrite nbind-unlocked Θ₂ | fceC-unlocked Θ₂ Δ | eqAC =
    idc-⊢ (wf-fceC Θ₂ wE)

-- ── IDPUSH ─────────────────────────────────────────────────────────────
-- The faces are swapped and the scope moves.  Four moves, one per premise
-- of the contractum's inner `env`:
--
--   FRAME     `Θ₁ ◃ Θ₂`, well formed by §5.
--   INTERIOR  `V`, retagged along `frame-move` (§4).
--   FACE      `unseal X` at the owner `move-∋` transports (§4); the two
--             names are forced equal by the id-face's own exterior,
--             `X ≡ nbind Θ₁ + Y` (proof/IdLayer, `idpush-name`).
--   EXTERIOR  `moved-scoped` — the premise that used to be the wall.
preserve-IdPush : IdPushCase
preserve-IdPush {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                {A = A} {C = C} v d
                (env bw₂ (env bw₁ ⊢V ⊢cᵢ wE′) (conv-unseal dₒ) wE) =
  env (Bwf-unlocked Θ₂ bw₂)
      (env (Bwf-◃ Θ₁ Θ₂ bw₁ bw₂) ⊢V′ faceᵢ (moved-scoped Θ₂ wE eqAC))
      (moved-face Θ₂ wE eqAC)
      wE
  where
  -- The outer `unseal Y`'s rep is `liftN (nbind Θ₂) C`; it IS A.
  eqAC : A ≡ liftN (nbind Θ₂) C
  eqAC = ∋:=-det d dₒ

  -- The inner `id (` X)` face: its interior is `` ` X ``, and its
  -- exterior `liftN (nbind Θ₁) (` Y)` equals `` ` X ``.
  eqX : nbind Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (liftN-var (nbind Θ₁) Y)) (conv-idv-tgt ⊢cᵢ))

  ⊢V′ : intC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ) ∣ [] ⊢ V ⦂ ` X
  ⊢V′ = ⊢retag (frame-move Θ₁ Θ₂ Δ)
          (subst (λ T → intC Θ₁ (intC Θ₂ Δ) ∣ [] ⊢ V ⦂ T)
                 (conv-idv-src ⊢cᵢ) ⊢V)

  dX : fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ) ∋ X := liftN (nbind Θ₁) A
  dX = subst (λ Z → fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
                      ∋ Z := liftN (nbind Θ₁) A)
             eqX (move-∋ Θ₁ Θ₂ d)

  faceᵢ : fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
            ⊢ unseal X ∶ ` X ⇝ liftN (nbind (Θ₁ ◃ Θ₂)) A
  faceᵢ rewrite nbind-◃ Θ₁ Θ₂ = conv-unseal dX

-- ── CANCELR ────────────────────────────────────────────────────────────
-- The same four moves, with both faces neutralised instead of swapped.
-- THE FACE EQUATION — `V`'s interior type IS the new inner face — is the
-- one piece of content: `seal X`'s source is X's rep, and X's rep on the
-- contractum's inner face type context is `liftN (nbind Θ₁) A`, so
-- `∋:=-det` closes it.  The old proof had to run that lookup INSIDE Θ₂'s
-- locks (whence `ScopedAtUnseal`); this one runs it on the face.
preserve-CancelR : CancelRCase
preserve-CancelR {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {C = C} v d
                 (env bw₂ (env bw₁ ⊢V ⊢c₁ wE′) (conv-unseal dₒ) wE) =
  env (Bwf-unlocked Θ₂ bw₂)
      (env (Bwf-◃ Θ₁ Θ₂ bw₁ bw₂) ⊢V′ faceᵢ (moved-scoped Θ₂ wE eqAC))
      (moved-face Θ₂ wE eqAC)
      wE
  where
  eqAC : A ≡ liftN (nbind Θ₂) C
  eqAC = ∋:=-det d dₒ

  eqX : nbind Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (liftN-var (nbind Θ₁) Y)) (conv-seal-tgt ⊢c₁))

  dX : fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ) ∋ X := liftN (nbind Θ₁) A
  dX = subst (λ Z → fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
                      ∋ Z := liftN (nbind Θ₁) A)
             eqX (move-∋ Θ₁ Θ₂ d)

  -- `seal X`'s source, read where the move puts it.
  eqV : _ ≡ liftN (nbind Θ₁) A
  eqV = ∋:=-det (⊑-kn (face-move Θ₁ Θ₂ Δ)
                      (seal-face-is-the-owners-rep ⊢c₁))
                dX

  ⊢V′ : intC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ) ∣ []
          ⊢ V ⦂ liftN (nbind Θ₁) A
  ⊢V′ = ⊢retag (frame-move Θ₁ Θ₂ Δ)
          (subst (λ T → intC Θ₁ (intC Θ₂ Δ) ∣ [] ⊢ V ⦂ T) eqV ⊢V)

  faceᵢ : fceC (Θ₁ ◃ Θ₂) (intC (unlocked Θ₂) Δ)
            ⊢ idc (liftN (nbind Θ₁) A)
            ∶ liftN (nbind Θ₁) A ⇝ liftN (nbind (Θ₁ ◃ Θ₂)) A
  faceᵢ rewrite nbind-◃ Θ₁ Θ₂ =
    idc-⊢ (wf-face-move Θ₁ Θ₂ (moved-scoped Θ₂ wE eqAC))

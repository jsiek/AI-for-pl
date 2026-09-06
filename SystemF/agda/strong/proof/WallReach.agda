module strong.proof.WallReach where

-- THE COMMON WALL, AND THE GROUNDED INVARIANT THAT CLEARS IT.
--
-- RETIRED, AND KEPT AS A RECORD (2026-09-06).  THE WALL IS GONE: the
-- SCOPE MOVE (strong.Reduction §2b) makes CancelR's and IdPush's
-- contracta present the rep on Θ₂'s FACE type context — `interior (dropLocks
-- Θ₂) Δ ≡ convCtx Θ₂ Δ` — where `wf-shiftBy-pushBinds` supplies it outright
-- (proof/MoveScope).  So no invariant has to be grounded at all.  What
-- follows is still TRUE, and is the machine-checked record of the
-- candidates that were tried; nothing in the main development uses it.
--
--
-- IdPush, CancelR and TyPeelR share ONE obstruction (notes/DECISIONS.md,
-- "Peel FIXED and PROVEN"): a contractum's inner wrapper must PRESENT the
-- owner's rep `A` inside `Θ₂`'s interior, and `env`'s last premise then
-- demands `interior Θ₂ Δ ⊢ᵗ A` — which fails exactly when `Θ₂` LOCKS a slot
-- that `A` names.  Jeremy's question, post-Peel-repair:
--
--   CAN A REACHABLE Θ₂ LOCK A SLOT THAT THE REP OF A VISIBLE OWNER NAMES?
--
-- THE ANSWER, in one invariant.  Say a type context is REP-WELL-FORMED
-- when every LIVE owner's rep is well formed WHERE IT LIVES:
--
--     RepWf Ξ  =  ∀ {Y A} → Ξ ∋ Y := A → Ξ ⊢ᵗ A
--
-- (a `masked`ed owner is exempt — `∋ Y := A` matches an UNBLOCKED `bind`
-- only, so `RepWf` says precisely "no lock blocks a slot that a NAMEABLE
-- owner's rep names").  Then:
--
--   §2  RepWf is closed under everything that BUILDS a type context in
--       this calculus: `abst ∷`, `bind A ∷` (TyBeta's mint), `masked ∷`,
--       and — the SIMULTANEITY step — the owner prefix `pushBinds`, whose
--       lifting of each rep past the owners bound inside it is exactly
--       what keeps the invariant.
--   §3  RepWf is NOT closed under `mask` — that IS the wall, as a
--       theorem, on the c10/c11 chained-rep shape.
--   §4  RepWf-dual: THE ANSWER.  A Peel's `dual Θ` installs only the
--       owner locks `hideBinds (numBinds Θ)`, and `interior-dual`
--       (proof/PeelDual) computes the resulting interior as
--       `map masked (pushBinds (repsOf Θ) []) ++ unlockedScope Θ Δ` — a
--       BLOCKED PREFIX over an unlocked tail.  Every live owner there
--       lives in the tail, so its rep is a lift past the whole blocked
--       prefix and names none of
--       it.  A crossing's locks CANNOT block a rep.
--   §5  The payoff: `unseal-scoped` derives `interior Θ Δ ⊢ᵗ A` for EVERY
--       unseal-faced wrapper from `RepWf (interior Θ Δ)` alone, which is
--       exactly the premise `idPush⁺` (proof/IdPushReach) needs and
--       exactly the fact CancelR's honest contractum demands.
--   §6  The term-level reading, and its LIMIT: the naive global invariant
--       ("RepWf at every wrapper's interior") is REFUTED BY A REACHABLE
--       TERM (Examples §12, `run-L₀`) — a `lock` may indeed block a rep,
--       but only in a `Θ₁` position, under an INERT face.  §7 discharges
--       the mint obligations for the narrowed, `Θ₂`-only reading.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ; renameᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Preserve using (⊢ᵗ-of; CtxWf-[])
open import strong.proof.PeelDual using (interior-dual)
open import strong.proof.IdPushReach using (maskOnly; idPush⁺)

private
  variable
    Δ Δ′ Ξ : Ctxᵗ
    Γ : Ctx
    A B C : Ty
    As : List Ty
    X Y : ℕ
    E : Ent
    M V : Term
    Θ Θ₁ Θ₂ : CtxMorph

------------------------------------------------------------------------
-- §1  THE INVARIANT
------------------------------------------------------------------------

-- What ONE entry owes the type context it sits on: a live owner owes its
-- rep's well-formedness THERE; a Λ-bound slot and a BLOCKED slot owe
-- nothing (a blocked entry can neither be named by a type nor supply an
-- owner lookup, so it is exempt by construction).
EntWf : Ctxᵗ → Ent → Set
EntWf Ξ abst        = ⊤
EntWf Ξ (bind A)    = Ξ ⊢ᵗ A
EntWf Ξ (masked E)  = ⊤

-- THE INVARIANT: every entry pays.  Its whole content is the `bind`
-- clause — no lock blocks a slot that a NAMEABLE owner's rep names.
RepWf : Ctxᵗ → Set
RepWf Ξ = ∀ {Y E} → Ξ ∋e Y , E → EntWf Ξ E

-- Reading it off at an owner is definitional: `Ξ ∋ Y := A` IS
-- `Ξ ∋e Y , bind A`, and `EntWf Ξ (bind A)` IS `Ξ ⊢ᵗ A`.
RepWf-owner : RepWf Ξ → Ξ ∋ Y := A → Ξ ⊢ᵗ A
RepWf-owner rw d = rw d

------------------------------------------------------------------------
-- §2  CLOSURE — everything that BUILDS a type context preserves it
------------------------------------------------------------------------

RepWf-[] : RepWf []
RepWf-[] ()

EntWf-ren : ∀ {ρ} (E : Ent) → Ren ρ Δ Δ′ → EntWf Δ E → EntWf Δ′ (renᵉ ρ E)
EntWf-ren abst     r w    = tt
EntWf-ren (bind A) r w    = wf-ren r w
EntWf-ren (masked E)  r w = tt

-- ONE cons step: the new head must pay for itself (read on the EXTENDED
-- context, i.e. at `⇑ᵉ`), and every old entry pays by weakening.
RepWf-∷ : (F : Ent) → EntWf (F ∷ Δ) (⇑ᵉ F) → RepWf Δ → RepWf (F ∷ Δ)
RepWf-∷ F wF rw ez     = wF
RepWf-∷ F wF rw (es d) = EntWf-ren _ Ren-wk (rw d)

-- A Λ-bound slot carries no rep, so it adds no obligation.
RepWf-abst : RepWf Δ → RepWf (abst ∷ Δ)
RepWf-abst = RepWf-∷ abst tt

-- TYBETA'S MINT.  `interior (bind A ∷ []) Δ` IS `bind A ∷ Δ`, and the one new
-- obligation is `Δ ⊢ᵗ A` — which is `⊢·[]`'s own premise.
RepWf-bind : Δ ⊢ᵗ A → RepWf Δ → RepWf (bind A ∷ Δ)
RepWf-bind {A = A} w = RepWf-∷ (bind A) (wf-ren Ren-wk w)

-- A blocked slot is INVISIBLE to the invariant.
RepWf-masked : RepWf Δ → RepWf (masked E ∷ Δ)
RepWf-masked {E = E} = RepWf-∷ (masked E) tt

RepWf-maskedAll : (Ps : Ctxᵗ) → RepWf Δ → RepWf (map masked Ps ++ Δ)
RepWf-maskedAll []       rw = rw
RepWf-maskedAll (P ∷ Ps) rw = RepWf-masked (RepWf-maskedAll Ps rw)

-- SIMULTANEITY, as the closure step for the owner prefix.  `pushBinds` stores
-- each rep LIFTED past the owners bound INSIDE it, so a rep never names
-- another owner of the same boundary — and that is exactly what makes
-- `RepWf` survive `pushBinds`.
-- (`wf-shiftBy-pushBinds` — a rep is a type over the plain exterior,
-- lifted past the owners bound inside it — is strong.Ctx's, §7.)

data AllWf (Δ : Ctxᵗ) : List Ty → Set where
  aw[] : AllWf Δ []
  aw∷  : Δ ⊢ᵗ A → AllWf Δ As → AllWf Δ (A ∷ As)

-- A well-formed boundary supplies exactly this: every rep it binds is a
-- well-formed type over the PLAIN exterior (`mw-b`).
MorphWf→AllWf : MorphWf Δ Θ → AllWf Δ (repsOf Θ)
MorphWf→AllWf mw[]        = aw[]
MorphWf→AllWf (mw-b w b)  = aw∷ w (MorphWf→AllWf b)
MorphWf→AllWf (mw-l tv b) = MorphWf→AllWf b
MorphWf→AllWf (mw-u d b)  = MorphWf→AllWf b

RepWf-pushBinds : (As : List Ty) → AllWf Δ As → RepWf Δ → RepWf (pushBinds As Δ)
RepWf-pushBinds []       aw[]        rw = rw
RepWf-pushBinds (A ∷ As) (aw∷ w aws) rw =
  RepWf-bind (wf-shiftBy-pushBinds As w) (RepWf-pushBinds As aws rw)

------------------------------------------------------------------------
-- §3  THE WALL — masking is the ONE operation that can break it
------------------------------------------------------------------------

-- The c10/c11 chained-rep shape, verbatim from proof/PreserveObstruct §4
-- (and REACHED from closed source by Examples §12, `run-L₀`).
WΔ WΞ : Ctxᵗ
WΔ = bind (` 0) ∷ bind `ℕ ∷ []
WΞ = bind (` 0) ∷ masked (bind `ℕ) ∷ []

_ : mask 1 WΔ ≡ WΞ
_ = refl

RepWf-WΔ : RepWf WΔ
RepWf-WΔ ez           = wf-var (_ , es ez , nameable-b)
RepWf-WΔ (es ez)      = wf-ℕ
RepWf-WΔ (es (es ()))

-- The lock at slot 1 blocks the slot that slot 0's rep NAMES.
¬RepWf-WΞ : ¬ RepWf WΞ
¬RepWf-WΞ rw with rw (ez {E = bind (` 0)})
... | wf-var (_ , es ez , ())

-- THE WALL, as a theorem: `mask` does not preserve the invariant.
mask-breaks-RepWf : ¬ (∀ (X : ℕ) (Ξ : Ctxᵗ) → RepWf Ξ → RepWf (mask X Ξ))
mask-breaks-RepWf h = ¬RepWf-WΞ (h 1 WΔ RepWf-WΔ)

------------------------------------------------------------------------
-- §4  THE ANSWER — a crossing's locks never block a rep
------------------------------------------------------------------------

-- With the repaired `dualScope` (no `unlock` case), the ONLY locks any rule
-- ever mints are `hideBinds (numBinds Θ)` at a Peel, and `interior-dual`
-- (proof/PeelDual) computes the crossing argument's interior as
--
--     map masked (pushBinds (repsOf Θ) [])  ++  unlockedScope Θ Δ
--
-- a BLOCKED PREFIX of exactly Θ's own owners over an UNLOCKED tail.  So
-- every slot a type may name there is in the tail, every live owner's rep
-- is that tail's rep lifted past the whole prefix, and the invariant is
-- preserved with NO side condition on Θ at all.
RepWf-dual : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → RepWf (unlockedScope Θ Δ)
    -------------------------------------
  → RepWf (interior (dual Θ) (interior Θ Δ))
RepWf-dual Θ Δ rw rewrite interior-dual Θ Δ =
  RepWf-maskedAll (pushBinds (repsOf Θ) []) rw

-- The premise is on `unlockedScope Θ Δ` (Θ's UNLOCKS applied), not on Δ: an
-- `unlock` re-exposes a slot whose rep may have been written before the
-- lock, so it is the one boundary entry the invariant must be checked
-- against.  When Θ has no `unlock` the premise is `RepWf Δ` on the nose.
data NoUnlock : CtxMorph → Set where
  nu[] : NoUnlock []
  nu-b : NoUnlock Θ → NoUnlock (bind A ∷ Θ)
  nu-l : NoUnlock Θ → NoUnlock (lock X ∷ Θ)

unlockedScope-NoUnlock : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → NoUnlock Θ → unlockedScope Θ Δ ≡ Δ
unlockedScope-NoUnlock []           Δ nu[]      = refl
unlockedScope-NoUnlock (bind A ∷ Θ) Δ (nu-b nu) = unlockedScope-NoUnlock Θ Δ nu
unlockedScope-NoUnlock (lock X ∷ Θ) Δ (nu-l nu) = unlockedScope-NoUnlock Θ Δ nu

RepWf-dual′ : (Θ : CtxMorph) (Δ : Ctxᵗ) → NoUnlock Θ
  → RepWf Δ → RepWf (interior (dual Θ) (interior Θ Δ))
RepWf-dual′ Θ Δ nu rw =
  RepWf-dual Θ Δ (subst RepWf (sym (unlockedScope-NoUnlock Θ Δ nu)) rw)

------------------------------------------------------------------------
-- §5  THE PAYOFF — the scoping fact the three rules need
------------------------------------------------------------------------

⊢ᵗ→∋tv : Δ ⊢ᵗ ` X → Δ ∋tv X
⊢ᵗ→∋tv (wf-var tv) = tv

-- The companion owner lookup, from the redex alone: an `unseal Y`-faced
-- wrapper types its body at `` ` Y ``, so Y is VISIBLE inside, and
-- `maskOnly` (interior differs from `convCtx` only by masking) turns the
-- `convCtx` owner fact into an interior one.  No assumption about the world.
unseal-owner : ∀ {Δ Γ M Θ Y A C}
  → convCtx Θ Δ ∋ Y := A
  → Δ ∣ Γ ⊢ M ⟪ Θ , unseal Y ⟫ ⦂ C
    ------------------------------
  → interior Θ Δ ∋ Y := A
unseal-owner {Δ = Δ} {Θ = Θ} d (env _ ⊢M (conv-unseal _) _) =
  maskOnly Θ Δ (⊢ᵗ→∋tv (⊢ᵗ-of CtxWf-[] ⊢M)) d

-- THE SCOPING FACT.  `interior Θ Δ ⊢ᵗ A` — the premise CancelR's honest
-- contractum demands and `idPush⁺` takes as `scoped` — is a CONSEQUENCE
-- of `RepWf (interior Θ Δ)`, for EVERY unseal-faced wrapper.
unseal-scoped : ∀ {Δ Γ M Θ Y A C} → RepWf (interior Θ Δ)
  → convCtx Θ Δ ∋ Y := A
  → Δ ∣ Γ ⊢ M ⟪ Θ , unseal Y ⟫ ⦂ C
    ------------------------------
  → interior Θ Δ ⊢ᵗ A
unseal-scoped rw d ⊢R = rw (unseal-owner d ⊢R)

-- JEREMY'S QUESTION, ANSWERED FOR THE ONLY LOCK-MINTING RULE.  A Peel
-- hands its crossing argument the frame `dual Θ`; if that frame is later
-- the Θ₂ of an IdPush/CancelR redex, the rep it hands back IS well formed
-- in its own interior.  No premise about Θ, no premise about Y, no
-- premise the rule would have to carry: `RepWf-dual` plus `unseal-scoped`.
peel-Θ₂-scoped : ∀ (Θ : CtxMorph) (Δ : Ctxᵗ) {Γ M Y A C}
  → RepWf (unlockedScope Θ Δ)
  → convCtx (dual Θ) (interior Θ Δ) ∋ Y := A
  → interior Θ Δ ∣ Γ ⊢ M ⟪ dual Θ , unseal Y ⟫ ⦂ C
    ---------------------------------------------
  → interior (dual Θ) (interior Θ Δ) ⊢ᵗ A
peel-Θ₂-scoped Θ Δ rw d ⊢R = unseal-scoped (RepWf-dual Θ Δ rw) d ⊢R

-- IDPUSH'S PRESERVATION CASE, over the invariant instead of over an
-- added rule premise: `RepWf (interior Θ₂ Δ)` is a fact about the type
-- context, not a side condition Progress would have to supply.
IdPushCase-RepWf : Set
IdPushCase-RepWf = ∀ {Δ V Θ₁ Θ₂ X Y A C}
  → RepWf (interior Θ₂ Δ) → Value V → convCtx Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    ---------------------------------------------------
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , mkId A ⟫ ⦂ C

idPush-RepWf : IdPushCase-RepWf
idPush-RepWf rw v d ⊢R =
  idPush⁺ v d (rw (unseal-owner d ⊢R)) (unseal-owner d ⊢R) ⊢R

-- THE SUPPLIER PHASE TWO WILL CONSUME.  CancelR's repair needs the rep
-- its own `unseal Y` hands back to be well formed INSIDE the frame that
-- hands it back — read off the redex, given only the invariant at the
-- ACTIVE boundary's interior.  (`RepWf (interior Θ₂ Δ)` cannot be grounded in
-- `MorphWf`: proof/WallGrounding refutes that, so it stays a hypothesis until
-- the condition is attached to the `unseal`-faced `env` node itself.)
scoped-at-unseal : ∀ {Δ V Θ₁ Θ₂ c₁ Y A C}
  → RepWf (interior Θ₂ Δ)
  → convCtx Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    ---------------------------------------------
  → interior Θ₂ Δ ⊢ᵗ A
scoped-at-unseal rw d ⊢R = unseal-scoped rw d ⊢R

-- CANCELR's honest contractum (keep both frames, neutralise both faces)
-- needs the SAME fact, at the SAME redex shape.
cancelR-scoped : ∀ {Δ V Θ₁ Θ₂ X Y A C}
  → RepWf (interior Θ₂ Δ)
  → convCtx Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    -------------------------------------------------
  → interior Θ₂ Δ ⊢ᵗ A
cancelR-scoped rw d ⊢R = unseal-scoped rw d ⊢R

------------------------------------------------------------------------
-- §6  THE TERM-LEVEL READING, AND ITS LIMIT
------------------------------------------------------------------------

-- The obvious term-level invariant: RepWf at EVERY wrapper's interior.
data WallFree : Ctxᵗ → Term → Set where
  w-var : ∀ {x} → WallFree Δ (` x)
  w-lit : ∀ {n} → WallFree Δ ($ n)
  w-ƛ   : ∀ {N} → WallFree Δ N → WallFree Δ (ƛ A ∙ N)
  w-·   : ∀ {L N} → WallFree Δ L → WallFree Δ N → WallFree Δ (L · N)
  w-Λ   : ∀ {N} → WallFree (abst ∷ Δ) N → WallFree Δ (Λ N)
  w-·[] : ∀ {L} → WallFree Δ L → WallFree Δ (L ·[ B , A ])
  w-⟪⟫  : ∀ {c} → RepWf (interior Θ Δ) → WallFree (interior Θ Δ) M
        → WallFree Δ (M ⟪ Θ , c ⟫)

WallStep : Set
WallStep = ∀ {Δ M M′} → WallFree Δ M → Δ ⊢ M -→ M′ → WallFree Δ M′

-- AND IT IS FALSE — on a REACHABLE term.  Examples §12 runs the closed
-- source `L = ((ΛY. λx:Y. ((ΛZ. x) [Y])) [ℕ]) · 7`; its step `lstep₄` is
-- an ordinary TyBeta that mints the CHAINED rep ` 0 around a wrapper
-- whose Peel-minted `lock 1` blocks exactly the slot that rep names.  So
-- "no lock ever blocks a rep" is NOT a term invariant of this calculus.
open import strong.Examples using (L₃; L₄; lstep₄)

wallfree-L₃ : WallFree [] L₃
wallfree-L₃ =
  w-⟪⟫ (RepWf-bind wf-ℕ RepWf-[])
       (w-·[] (w-Λ (w-⟪⟫ (RepWf-abst (RepWf-masked RepWf-[])) w-lit)))

¬wallfree-L₄ : ¬ WallFree [] L₄
¬wallfree-L₄ (w-⟪⟫ _ (w-⟪⟫ _ (w-⟪⟫ rw _))) = ¬RepWf-WΞ rw

¬wall-step : ¬ WallStep
¬wall-step ws = ¬wallfree-L₄ (ws wallfree-L₃ lstep₄)

-- THE READING, and it is the design answer.  The blocked context is
-- reached in a `Θ₁` POSITION — the interior of an INERT `seal`-faced
-- wrapper.  A rule only ever READS a rep out of a `Θ₂`: the frame of the
-- wrapper carrying the ACTIVE `unseal` face.  §4 says a Peel's locks sit
-- strictly BELOW everything a rep of that frame can name, and §5 turns
-- that into the three rules' missing premise.  So the invariant to carry
-- is not "no lock blocks a rep anywhere" (false, above) but "`RepWf` at
-- every Θ₂", whose mint obligations are §7.

------------------------------------------------------------------------
-- §7  THE MINT OBLIGATIONS, DISCHARGED
------------------------------------------------------------------------

-- What every boundary-minting rule owes the invariant, at the type
-- context it mints into.  TyBeta, Peel and CancelR pay; IdPush mints no
-- frame at all (both are carried over verbatim), so it owes nothing.

-- TYBETA.  `interior (bind A ∷ []) Δ ≡ bind A ∷ Δ` definitionally.
mint-TyBeta : Δ ⊢ᵗ A → RepWf Δ → RepWf (interior (bind A ∷ []) Δ)
mint-TyBeta = RepWf-bind

-- PEEL, on both sides: the outer frame is UNCHANGED, and the crossing
-- argument's frame is the dual — §4.
mint-Peel : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → RepWf (unlockedScope Θ Δ) → RepWf (interior (dual Θ) (interior Θ Δ))
mint-Peel = RepWf-dual

-- CANCELR MINTS NO FRAME AT ALL (the repaired rule, 2026-09-05): it
-- keeps both frames and neutralises both faces, so it owes the invariant
-- exactly what IdPush owes — nothing.  (The old residue
-- `repsOf→bind (repsOf Θ₂)` was BINDS-ONLY, so it was covered by the general
-- form below in any case.)

-- THE GENERAL FORM.  A frame that only BINDS (no lock, no unlock) touches
-- no existing entry, so `interior` is just `pushBinds` and §2's
-- simultaneity step carries it.  TyBeta's `bind A ∷ []` and TyPeelR's
-- `bind A ∷ Θ` (when Θ is binds-only) are both of this shape.
data BindsOnly : CtxMorph → Set where
  bo[] : BindsOnly []
  bo-b : BindsOnly Θ → BindsOnly (bind A ∷ Θ)

scope-BindsOnly : (Θ : CtxMorph) (Δ : Ctxᵗ) → BindsOnly Θ → scope Θ Δ ≡ Δ
scope-BindsOnly []           Δ bo[]      = refl
scope-BindsOnly (bind A ∷ Θ) Δ (bo-b bo) = scope-BindsOnly Θ Δ bo

mint-binds : (Θ : CtxMorph) → BindsOnly Θ → MorphWf Δ Θ → RepWf Δ
           → RepWf (interior Θ Δ)
mint-binds {Δ = Δ} Θ bo mw rw rewrite scope-BindsOnly Θ Δ bo =
  RepWf-pushBinds (repsOf Θ) (MorphWf→AllWf mw) rw

-- SUMMARY.  Every frame any rule mints is either BINDS-ONLY (TyBeta,
-- CancelR — `mint-binds`) or a DUAL (Peel — `RepWf-dual`); IdPush mints
-- none, carrying both frames over verbatim.  In each case the invariant
-- survives, WITHOUT any side condition the rule would have to carry and
-- Progress would have to supply.  What remains open is only the term-level
-- induction for the NARROWED (Θ₂-only) reading — its two content-carrying
-- cases are exactly the two lemmas above.
--
-- AND WHERE THAT INDUCTION CANNOT BE PUT.  Minting is not the only way a
-- type context changes: TyBeta REFINES a Λ-bound slot into an OWNER under
-- whatever locks the body already carries (`preserve-TyBeta`'s `refine`,
-- the `le-ao` clause), and `RepWf (interior Θ ·)` does not survive that.  So
-- the narrowed reading cannot be grounded in `MorphWf`, whose every premise
-- must be ⊑-stable for `MorphWf-⊑`/`⊢retag`.  proof/WallGrounding is the
-- machine-checked verdict, with the alternative home for the condition.

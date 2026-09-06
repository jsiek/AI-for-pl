module strong.proof.ChainScoped where

-- THE REP CHAIN AS THE INVARIANT — PROBE.
--
-- RETIRED, AND KEPT AS A RECORD (2026-09-06).  THE WALL IS GONE: the
-- SCOPE MOVE (strong.Reduction §2b) makes CancelR's and IdPush's
-- contracta present the rep on Θ₂'s FACE type context — `interior (dropLocks
-- Θ₂) Δ ≡ exterior Θ₂ Δ` — where `wf-shiftBy-pushBinds` supplies it outright
-- (proof/MoveScope).  So no invariant has to be grounded at all.  What
-- follows is still TRUE, and is the machine-checked record of the
-- candidates that were tried; nothing in the main development uses it.
--
--
-- Three premises have now been run at the `env` node and each has died:
--
--   * in `MorphWf` (a condition on Δ and Θ alone) — proof/WallGrounding: the
--     `¬IdPushCase` witness and a REACHABLE wrapper have the same Δ and
--     the same Θ and differ only in their FACE.
--   * the EXTERIOR TYPE at a reveal face — the FACE-CONDITIONED
--     candidate, which switched on the retired POLARITY index: IdPush
--     swaps the faces, so the obstruction moves to Θ₁, about which the
--     premise says nothing (its witness `R★` is rebuilt in §3 below).
--   * POINTWISE `RepWf` at every name-faced boundary — §1 below, killed
--     by a closed program.
--
-- This file defines and tests the fourth: follow the REP CHAIN of the
-- variable the face names, and nothing else.  §2 defines it, §3 runs it
-- on every witness in the development, §4 KILLS IT — with a hand-built
-- typed TyBeta redex — and §5 says what the counter-model demands.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Preserve using (preserve-TyBeta)
open import strong.proof.WallReach using (RepWf; EntWf)
open import strong.proof.PreserveObstruct using (Δi; Θi)
open import strong.Examples using (LΔ)

------------------------------------------------------------------------
-- §1  KILL TEST — POINTWISE `RepWf` AT NAME-FACED BOUNDARIES
------------------------------------------------------------------------

-- THE PROGRAM (closed, plain System F):
--
--   (ΛX′. λx′:X′. ((ΛZ. λx:X′. (ΛY. x) [Z]) [ℕ] · x′)) [ℕ] · 7
--
-- Two nested crossings put the argument `7` behind TWO wrappers, the
-- outer of which is ID-FACED at X′ and carries the Peel-minted lock of
-- the ΛZ boundary's owner.  The innermost TyBeta then instantiates Y at
-- Z — minting the owner `Y := Z` — INSIDE that wrapper's scope.  So the
-- id-faced wrapper's interior blocks the slot the fresh owner's rep
-- names, and pointwise `RepWf` there is false while the contractum types.

Pinner Pfun2 PZ Pbody Pfun1 P₀ : Term
Pinner = (Λ (` 0)) ·[ ` 2 , ` 0 ]              -- (ΛY. x) [Z]
Pfun2  = ƛ (` 1) ∙ Pinner                      -- λx:X′. …
PZ     = Λ Pfun2                               -- ΛZ. …
Pbody  = (PZ ·[ ` 1 ⇒ ` 1 , `ℕ ]) · (` 0)      -- (…[ℕ]) · x′
Pfun1  = ƛ (` 0) ∙ Pbody                       -- λx′:X′. …
P₀     = ((Λ Pfun1) ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Pinner : (abst ∷ abst ∷ []) ∣ (` 1 ∷ ` 1 ∷ []) ⊢ Pinner ⦂ ` 1
⊢Pinner = ⊢·[] (⊢Λ (⊢` here)) (wf-var (abst , ez , nameable-a))

⊢Pfun2 : (abst ∷ abst ∷ []) ∣ (` 1 ∷ []) ⊢ Pfun2 ⦂ (` 1 ⇒ ` 1)
⊢Pfun2 = ⊢ƛ (wf-var (abst , es ez , nameable-a)) ⊢Pinner

⊢Pbody : (abst ∷ []) ∣ (` 0 ∷ []) ⊢ Pbody ⦂ ` 0
⊢Pbody = ⊢· (⊢·[] (⊢Λ ⊢Pfun2) wf-ℕ) (⊢` here)

⊢P₀ : [] ∣ [] ⊢ P₀ ⦂ `ℕ
⊢P₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) ⊢Pbody)) wf-ℕ) ⊢$

-- ── THE RUN, every state rendered ─────────────────────────────────────

KS₇ : Term
KS₇ = ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫

-- the crossing argument the SECOND Peel builds: `7` behind a seal at X′
-- and then behind an ID FACE at X′, under the lock of Z's owner slot
xK ⇑xK : Term
xK  = (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ lock 0 ∷ [] , id (` 1) ⟫
⇑xK = (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫) ⟪ lock 1 ∷ [] , id (` 2) ⟫

_ : ⇑ᴹ xK ≡ ⇑xK
_ = refl

P₁ P₂ P₃ P₄ P₅ P₆ P₇ : Term
P₁ = (Pfun1 ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
P₂ = (Pfun1 · KS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
P₃ = ((PZ ·[ ` 1 ⇒ ` 1 , `ℕ ]) · KS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
P₄ = ((Pfun2 ⟪ bind `ℕ ∷ [] , id (` 1) ↦ id (` 1) ⟫) · KS₇)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
P₅ = ((Pfun2 · xK) ⟪ bind `ℕ ∷ [] , id (` 1) ⟫)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
P₆ = (((Λ ⇑xK) ·[ ` 2 , ` 0 ]) ⟪ bind `ℕ ∷ [] , id (` 1) ⟫)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
P₇ = ((⇑xK ⟪ bind (` 0) ∷ [] , id (` 2) ⟫) ⟪ bind `ℕ ∷ [] , id (` 1) ⟫)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

kstep₁ : [] ⊢ P₀ -→ P₁
kstep₁ = ξ-·-l (TyBeta V-ƛ)

kstep₂ : [] ⊢ P₁ -→ P₂
kstep₂ = Peel V-ƛ V-$

kstep₃ : [] ⊢ P₂ -→ P₃
kstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- the ΛZ instantiation: Z := ℕ, and the minted face is an ID LAYER
-- (the body type `X′` is an OUTER variable)
kstep₄ : [] ⊢ P₃ -→ P₄
kstep₄ = ξ-⟪⟫ (ξ-·-l (TyBeta V-ƛ))

-- the SECOND Peel: `dual (bind ℕ ∷ []) = lock 0 ∷ []`, so the crossing
-- argument acquires the lock of Z's own owner slot, under an ID face
kstep₅ : [] ⊢ P₄ -→ P₅
kstep₅ = ξ-⟪⟫ (Peel V-ƛ (V-⟪⟫ V-$ I-seal))

kstep₆ : [] ⊢ P₅ -→ P₆
kstep₆ = ξ-⟪⟫ (ξ-⟪⟫ (Beta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv)))

-- THE STEP THAT KILLS THE POINTWISE VARIANT: Y := Z is minted around a
-- wrapper whose `lock 1` blocks exactly Z.
kstep₇ : [] ⊢ P₆ -→ P₇
kstep₇ = ξ-⟪⟫ (ξ-⟪⟫ (TyBeta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv)))

run-P₀ : [] ⊢ P₀ -→* P₇
run-P₀ = kstep₁ then kstep₂ then kstep₃ then kstep₄ then kstep₅
    then kstep₆ then kstep₇ then done

-- ── THE TYPE CONTEXTS ─────────────────────────────────────────────────

KΔ₁ KΞ₂ Ξᴷ Ξᴷ′ Δᴷ Δᴷ′ : Ctxᵗ
KΔ₁ = bind `ℕ ∷ []                              -- X′ := ℕ
KΞ₂ = bind `ℕ ∷ bind `ℕ ∷ []                    -- Z := ℕ , X′ := ℕ
Ξᴷ  = abst ∷ KΞ₂                                -- under ΛY (redex)
Ξᴷ′ = abst ∷ masked (bind `ℕ) ∷ bind `ℕ ∷ []       -- … behind `lock 1`
Δᴷ  = bind (` 0) ∷ KΞ₂                          -- Y := Z (contractum)
Δᴷ′ = bind (` 0) ∷ masked (bind `ℕ) ∷ bind `ℕ ∷ [] -- … behind `lock 1`

_ : interior (lock 1 ∷ []) Ξᴷ ≡ Ξᴷ′
_ = refl

_ : interior (bind (` 0) ∷ []) KΞ₂ ≡ Δᴷ
_ = refl

_ : interior (lock 1 ∷ []) Δᴷ ≡ Δᴷ′
_ = refl

-- BEFORE the step the locked slot is named by nothing: slot 0 is Λ-bound.
RepWf-Ξᴷ′ : RepWf Ξᴷ′
RepWf-Ξᴷ′ ez               = tt
RepWf-Ξᴷ′ (es ez)          = tt
RepWf-Ξᴷ′ (es (es ez))     = wf-ℕ
RepWf-Ξᴷ′ (es (es (es ())))

-- AFTER it, the fresh owner `Y := Z` names the blocked slot.
¬RepWf-Δᴷ′ : ¬ RepWf Δᴷ′
¬RepWf-Δᴷ′ rw with rw (ez {E = bind (` 0)})
... | wf-var (_ , es ez , ())

-- ── BOTH STATES TYPE ──────────────────────────────────────────────────

⊢⇑xK-redex : Ξᴷ ∣ [] ⊢ ⇑xK ⦂ ` 2
⊢⇑xK-redex =
  env (mw-l (bind `ℕ , es ez , nameable-b) mw[])
      (env (mw-l (bind `ℕ , es (es ez) , nameable-b) mw[]) ⊢$
           (conv-seal (es (es ez)))
           (wf-var (bind `ℕ , es (es ez) , nameable-b)))
      (conv-idv (bind `ℕ , es (es ez) , nameable-b))
      (wf-var (bind `ℕ , es (es ez) , nameable-b))

⊢P₆-in : KΞ₂ ∣ [] ⊢ (Λ ⇑xK) ·[ ` 2 , ` 0 ] ⦂ ` 1
⊢P₆-in = ⊢·[] (⊢Λ ⊢⇑xK-redex) (wf-var (bind `ℕ , ez , nameable-b))

⊢P₆-mid : KΔ₁ ∣ [] ⊢ ((Λ ⇑xK) ·[ ` 2 , ` 0 ])
                       ⟪ bind `ℕ ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢P₆-mid = env (mw-b wf-ℕ mw[]) ⊢P₆-in
               (conv-idv (bind `ℕ , es ez , nameable-b))
               (wf-var (bind `ℕ , ez , nameable-b))

⊢P₆ : [] ∣ [] ⊢ P₆ ⦂ `ℕ
⊢P₆ = env (mw-b wf-ℕ mw[]) ⊢P₆-mid (conv-unseal ez) wf-ℕ

⊢⇑xK-contractum : Δᴷ ∣ [] ⊢ ⇑xK ⦂ ` 2
⊢⇑xK-contractum =
  env (mw-l (bind `ℕ , es ez , nameable-b) mw[])
      (env (mw-l (bind `ℕ , es (es ez) , nameable-b) mw[]) ⊢$
           (conv-seal (es (es ez)))
           (wf-var (bind `ℕ , es (es ez) , nameable-b)))
      (conv-idv (bind `ℕ , es (es ez) , nameable-b))
      (wf-var (bind `ℕ , es (es ez) , nameable-b))

⊢P₇-in : KΞ₂ ∣ [] ⊢ ⇑xK ⟪ bind (` 0) ∷ [] , id (` 2) ⟫ ⦂ ` 1
⊢P₇-in = env (mw-b (wf-var (bind `ℕ , ez , nameable-b)) mw[])
              ⊢⇑xK-contractum
              (conv-idv (bind `ℕ , es (es ez) , nameable-b))
              (wf-var (bind `ℕ , es ez , nameable-b))

⊢P₇-mid : KΔ₁ ∣ [] ⊢ (⇑xK ⟪ bind (` 0) ∷ [] , id (` 2) ⟫)
                       ⟪ bind `ℕ ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢P₇-mid = env (mw-b wf-ℕ mw[]) ⊢P₇-in
               (conv-idv (bind `ℕ , es ez , nameable-b))
               (wf-var (bind `ℕ , ez , nameable-b))

⊢P₇ : [] ∣ [] ⊢ P₇ ⦂ `ℕ
⊢P₇ = env (mw-b wf-ℕ mw[]) ⊢P₇-mid (conv-unseal ez) wf-ℕ

-- ── THE VERDICT ───────────────────────────────────────────────────────

-- The variant: pointwise `RepWf (interior Θ Δ)` at every boundary whose face
-- NAMES a slot (`id (` X)`, `unseal X`, `seal X`).  `P₇`'s middle-inner
-- wrapper is id-faced, so the variant applies to it.
NameFacedRepWf : Set
NameFacedRepWf = ∀ {Δ Γ M Θ X A} → Δ ∣ Γ ⊢ M ⟪ Θ , id (` X) ⟫ ⦂ A
               → RepWf (interior Θ Δ)

-- EVERY typing of `P₇` contains that wrapper, so the variant does not
-- merely refuse one derivation: it refuses the state.
P₇-lock : [] ∣ [] ⊢ P₇ ⦂ `ℕ → ∃[ B ] (Δᴷ ∣ [] ⊢ ⇑xK ⦂ B)
P₇-lock (env _ (env _ (env _ ⊢w _ _) _ _) _ _) = _ , ⊢w

-- KILLED: the variant contradicts a state REACHED from closed source.
¬NameFacedRepWf : ¬ NameFacedRepWf
¬NameFacedRepWf h with P₇-lock ⊢P₇
... | B , ⊢w = ¬RepWf-Δᴷ′ (h ⊢w)

------------------------------------------------------------------------
-- §2  THE CHAIN PREMISE
------------------------------------------------------------------------

-- The variables a type NAMES (de Bruijn, so a `∀ shifts the index).
infix 4 _∈ᵗ_
data _∈ᵗ_ : ℕ → Ty → Set where
  in-var : ∀ {X}     → X ∈ᵗ ` X
  in-⇒-l : ∀ {X A B} → X ∈ᵗ A → X ∈ᵗ (A ⇒ B)
  in-⇒-r : ∀ {X A B} → X ∈ᵗ B → X ∈ᵗ (A ⇒ B)
  in-∀   : ∀ {X A}   → suc X ∈ᵗ A → X ∈ᵗ (`∀ A)

-- THE REP CHAIN of a slot: its own rep, and — transitively — the rep of
-- every slot a reached rep NAMES.  This is the smallest set of types the
-- boundary must keep readable if the rules are ever to hand X's rep back
-- and then read on into it.
data Reach (Δ : Ctxᵗ) : ℕ → Ty → Set where
  rz : ∀ {X A}     → Δ ∋ X := A → Reach Δ X A
  rs : ∀ {X A Y B} → Reach Δ X A → Y ∈ᵗ A → Δ ∋ Y := B → Reach Δ X B

-- THE PREMISE, VERBATIM.  The face's name and the interior live in the
-- SAME index space (`interior Θ Δ` and `exterior Θ Δ` differ only by masking —
-- `maskOnly`), so there is no lifting to insert: the chain is read on the
-- FACE type context, and every member of it must be readable INSIDE.
ChainScoped : Ctxᵗ → CtxMorph → ℕ → Set
ChainScoped Δ Θ X = ∀ {A} → Reach (exterior Θ Δ) X A → interior Θ Δ ⊢ᵗ A

-- WHAT IT DELIVERS.  The `rz` member is exactly the premise `idPush⁺`
-- takes as `scoped` and `unseal-scoped` concludes — no lifting, on the
-- nose.
chain-rep : ∀ {Δ Θ X A}
  → ChainScoped Δ Θ X → exterior Θ Δ ∋ X := A → interior Θ Δ ⊢ᵗ A
chain-rep cs d = cs (rz d)

-- WHAT THE COMPOSITE FACES NEED.  A face is attached at its LEAVES: the
-- `id (` X)` / `seal X` / `unseal X` occurrences inside `↦` and `∀ .  For
-- `Preserve`'s cases that means:
--
--   IdPush   the redex's leaves are `X` (inner `id`) and `Y` (outer
--            `unseal`); the contractum's are the SAME two, swapped — so
--            the premise is preserved iff `ChainScoped Δ Θ₁ X` survives
--            the swap, which is what §4 tests.
--   CancelR  the residue's face is `mkId A` for the looked-up rep `A`, so
--            its leaves are exactly the variables of `A` — every one of
--            which is on Y's chain (`rs … in-… …`).  `ChainScoped` at Y
--            therefore covers the whole residue: that is the one place
--            where following the chain, rather than stopping at the rep,
--            is what makes the premise closed.
--
-- Base leaves (`id `ℕ`) name nothing and owe nothing.

------------------------------------------------------------------------
-- §3  THE DISCRIMINATION IT MAKES
------------------------------------------------------------------------

-- an `abst` slot has no rep, so a chain STOPS there
abst-not-owner : ∀ {Δ X B} → Δ ∋e X , abst → Δ ∋ X := B → ⊥
abst-not-owner d d′ with ∋e-det d d′
... | ()

-- ── REFUSES the `¬IdPushCase` witness (proof/PreserveObstruct §4) ─────

¬ChainScoped-Ri : ¬ ChainScoped Δi Θi 0
¬ChainScoped-Ri cs with cs (rz ez)
... | wf-var (_ , es ez , ())

-- ── REFUSES the Θ₁-lock witness ───────────────────────────────────────
--
-- `Ξ★` is the CHAINED-REP face type context (slot 1's rep is slot 2) and
-- `Θ★₁` locks slot 2 — the REP of the slot its own id-face names.  This
-- is the configuration that refuted the face-conditioned candidate: the
-- exterior type `` ` 1 `` is nameable inside, its rep `` ` 2 `` is not.

Ξ★ : Ctxᵗ
Ξ★ = bind `ℕ ∷ bind (` 0) ∷ bind `ℕ ∷ []

Θ★₁ : CtxMorph
Θ★₁ = lock 2 ∷ []

¬ChainScoped-R★ : ¬ ChainScoped Ξ★ Θ★₁ 1
¬ChainScoped-R★ cs with cs (rz (es ez))
... | wf-var (_ , es (es ez) , ())

-- ── ADMITS the REACHABLE wall wrapper of Examples §12 ─────────────────
--
-- `L₄`'s locked slot IS on no chain the face touches: the face names
-- slot 1, whose rep is `ℕ, and `ℕ names nothing.
chain-LΔ : ∀ {A} → Reach LΔ 1 A → A ≡ `ℕ
chain-LΔ (rz d) = ∋:=-det d (es ez)
chain-LΔ (rs r i d) with chain-LΔ r
chain-LΔ (rs r () d) | refl

ChainScoped-L₄ : ChainScoped LΔ (lock 1 ∷ []) 1
ChainScoped-L₄ r with chain-LΔ r
... | refl = wf-ℕ

-- ── ADMITS the §1 kill test, on both sides of its TyBeta ──────────────
--
-- The id-faced wrapper names X′ (slot 2), whose rep is `ℕ; the lock is on
-- Z (slot 1), which X′'s chain never reaches.  Pointwise `RepWf` fails
-- here (§1) precisely because it also looks at Y — a slot the face never
-- names.
chain-Δᴷ : ∀ {A} → Reach Δᴷ 2 A → A ≡ `ℕ
chain-Δᴷ (rz d) = ∋:=-det d (es (es ez))
chain-Δᴷ (rs r i d) with chain-Δᴷ r
chain-Δᴷ (rs r () d) | refl

ChainScoped-killtest : ChainScoped Δᴷ (lock 1 ∷ []) 2
ChainScoped-killtest r with chain-Δᴷ r
... | refl = wf-ℕ

chain-Ξᴷ : ∀ {A} → Reach Ξᴷ 2 A → A ≡ `ℕ
chain-Ξᴷ (rz d) = ∋:=-det d (es (es ez))
chain-Ξᴷ (rs r i d) with chain-Ξᴷ r
chain-Ξᴷ (rs r () d) | refl

ChainScoped-killtest-redex : ChainScoped Ξᴷ (lock 1 ∷ []) 2
ChainScoped-killtest-redex r with chain-Ξᴷ r
... | refl = wf-ℕ

------------------------------------------------------------------------
-- §4  THE COUNTER-MODEL — TYBETA BREAKS IT
------------------------------------------------------------------------

-- A chain STOPS at a Λ-bound slot, because an `abst` has no rep.  TyBeta
-- GIVES that slot a rep — and the chain then runs on, into whatever the
-- instantiating type names.  A lock that was harmless (the chain stopped
-- short of it) becomes fatal, and `⊢retag` cannot carry the premise
-- across.  This is `le-ao` again (proof/WallGrounding §3), one level down.
--
-- THE WITNESS.  `Λ` binds a slot; inside it a boundary binds an owner
-- whose rep NAMES that slot; inside THAT, a wrapper locks an older slot
-- and its id-face names the owner.  Instantiating the Λ at a type that
-- names the locked slot closes the circuit.

CΔ CΔ⁺ CΔ⁺′ CΔ′ CΔ′′ : Ctxᵗ
CΔ   = bind `ℕ ∷ []
CΔ⁺  = bind (` 0 ⇒ `ℕ) ∷ abst ∷ bind `ℕ ∷ []
CΔ⁺′ = bind (` 0 ⇒ `ℕ) ∷ abst ∷ masked (bind `ℕ) ∷ []
CΔ′  = bind (` 0 ⇒ `ℕ) ∷ bind (` 0) ∷ bind `ℕ ∷ []
CΔ′′ = bind (` 0 ⇒ `ℕ) ∷ bind (` 0) ∷ masked (bind `ℕ) ∷ []

CΘ : CtxMorph
CΘ = lock 2 ∷ []

_ : interior (bind (` 0 ⇒ `ℕ) ∷ []) (abst ∷ CΔ) ≡ CΔ⁺
_ = refl

_ : interior CΘ CΔ⁺ ≡ CΔ⁺′
_ = refl

_ : interior (bind (` 0 ⇒ `ℕ) ∷ []) (bind (` 0) ∷ CΔ) ≡ CΔ′
_ = refl

_ : interior CΘ CΔ′ ≡ CΔ′′
_ = refl

CV CW CM CN CR CC : Term
CV = (ƛ (` 1) ∙ ($ 3)) ⟪ [] , seal 0 ⟫
CW = CV ⟪ CΘ , id (` 0) ⟫
CM = CW ⟪ bind (` 0 ⇒ `ℕ) ∷ [] , unseal 0 ⟫
CN = ƛ `ℕ ∙ CM
CR = (Λ CN) ·[ `ℕ ⇒ (` 0 ⇒ `ℕ) , ` 0 ]
CC = CN ⟪ bind (` 0) ∷ [] , id `ℕ ↦ (seal 0 ↦ id `ℕ) ⟫

_ : reveal 0 (`ℕ ⇒ (` 0 ⇒ `ℕ)) ≡ id `ℕ ↦ (seal 0 ↦ id `ℕ)
_ = refl

⊢CV : CΔ⁺′ ∣ [] ⊢ CV ⦂ ` 0
⊢CV = env mw[]
           (⊢ƛ (wf-var (abst , es ez , nameable-a)) ⊢$)
           (conv-seal ez)
           (wf-var (bind (` 1 ⇒ `ℕ) , ez , nameable-b))

⊢CW : CΔ⁺ ∣ [] ⊢ CW ⦂ ` 0
⊢CW = env (mw-l (bind `ℕ , es (es ez) , nameable-b) mw[]) ⊢CV
           (conv-idv (bind (` 1 ⇒ `ℕ) , ez , nameable-b))
           (wf-var (bind (` 1 ⇒ `ℕ) , ez , nameable-b))

⊢CM : ∀ {Γ} → (abst ∷ CΔ) ∣ Γ ⊢ CM ⦂ (` 0 ⇒ `ℕ)
⊢CM = env (mw-b (wf-⇒ (wf-var (abst , ez , nameable-a)) wf-ℕ) mw[]) ⊢CW
           (conv-unseal ez)
           (wf-⇒ (wf-var (abst , ez , nameable-a)) wf-ℕ)

⊢CN : (abst ∷ CΔ) ∣ [] ⊢ CN ⦂ (`ℕ ⇒ (` 0 ⇒ `ℕ))
⊢CN = ⊢ƛ wf-ℕ ⊢CM

⊢CR : CΔ ∣ [] ⊢ CR ⦂ (`ℕ ⇒ (` 0 ⇒ `ℕ))
⊢CR = ⊢·[] (⊢Λ ⊢CN) (wf-var (bind `ℕ , ez , nameable-b))

cstep : CΔ ⊢ CR -→ CC
cstep = TyBeta V-ƛ

-- the contractum TYPES — this is a refutation of the PREMISE, not of the
-- calculus as it stands
⊢CC : CΔ ∣ [] ⊢ CC ⦂ (`ℕ ⇒ (` 0 ⇒ `ℕ))
⊢CC = preserve-TyBeta ⊢CR

-- ── BEFORE: the chain stops at the Λ-bound slot ───────────────────────

chain-CΔ⁺ : ∀ {A} → Reach CΔ⁺ 0 A → A ≡ (` 1 ⇒ `ℕ)
chain-CΔ⁺ (rz d) = ∋:=-det d ez
chain-CΔ⁺ (rs r i d) with chain-CΔ⁺ r
... | refl = ⊥-elim (stop i d)
  where
  stop : ∀ {Y B} → Y ∈ᵗ (` 1 ⇒ `ℕ) → CΔ⁺ ∋ Y := B → ⊥
  stop (in-⇒-l in-var) d′ = abst-not-owner (es ez) d′
  stop (in-⇒-r ())     d′

ChainScoped-CΔ⁺ : ChainScoped CΔ⁺ CΘ 0
ChainScoped-CΔ⁺ r with chain-CΔ⁺ r
... | refl = wf-⇒ (wf-var (abst , es ez , nameable-a)) wf-ℕ

-- the redex's other two wrappers owe nothing new: both frames are
-- lock-free, and the same chain stops at the same `abst`
ChainScoped-CV : ChainScoped CΔ⁺′ [] 0
ChainScoped-CV r with chain-CΔ⁺′ r
  where
  chain-CΔ⁺′ : ∀ {A} → Reach CΔ⁺′ 0 A → A ≡ (` 1 ⇒ `ℕ)
  chain-CΔ⁺′ (rz d) = ∋:=-det d ez
  chain-CΔ⁺′ (rs r′ i d) with chain-CΔ⁺′ r′
  ... | refl = ⊥-elim (stop i d)
    where
    stop : ∀ {Y B} → Y ∈ᵗ (` 1 ⇒ `ℕ) → CΔ⁺′ ∋ Y := B → ⊥
    stop (in-⇒-l in-var) d′ = abst-not-owner (es ez) d′
    stop (in-⇒-r ())     d′
... | refl = wf-⇒ (wf-var (abst , es ez , nameable-a)) wf-ℕ

-- ── AFTER: TyBeta gives the Λ-bound slot a rep, and the chain runs on ─

-- slot 1 is now `Y := Z`, and Z (slot 2) is what `CΘ` locks
_ : CΔ′ ∋ 1 := ` 2
_ = es ez

¬ChainScoped-CΔ′ : ¬ ChainScoped CΔ′ CΘ 0
¬ChainScoped-CΔ′ cs with cs (rs (rz ez) (in-⇒-l in-var) (es ez))
... | wf-var (_ , es (es ez) , ())

-- ── THE VERDICT ───────────────────────────────────────────────────────

-- the candidate rule, at the id-faced boundary
ChainFaced : Set
ChainFaced = ∀ {Δ Γ M Θ X A}
  → Δ ∣ Γ ⊢ M ⟪ Θ , id (` X) ⟫ ⦂ A → ChainScoped Δ Θ X

-- every typing of the contractum contains the offending wrapper
CC-W : ∀ {B} → CΔ ∣ [] ⊢ CC ⦂ B → ∃[ B′ ] (CΔ′ ∣ [] ⊢ CW ⦂ B′)
CC-W (env _ (⊢ƛ _ (env _ ⊢w _ _)) _ _) = _ , ⊢w

-- KILLED.  The redex satisfies the premise at every wrapper
-- (`ChainScoped-CΔ⁺`, `ChainScoped-CV`, and the `unseal`-faced one is
-- lock-free); the contractum does not.
¬ChainFaced : ¬ ChainFaced
¬ChainFaced h with CC-W ⊢CC
... | B′ , ⊢w = ¬ChainScoped-CΔ′ (h ⊢w)

------------------------------------------------------------------------
-- §5  WHAT THE COUNTER-MODEL DEMANDS
------------------------------------------------------------------------

-- The chain is not a fixed object: TYBETA EXTENDS IT, at every `abst`
-- slot it reaches, by a type chosen when the Λ is instantiated and read
-- on the Λ's OWN exterior.  A premise that quantifies over the chain AS
-- IT STANDS is therefore never stable; it must quantify over every chain
-- the slot could ever have.  Since the instantiating type may name any
-- slot older than the Λ, that is:
--
--   a `lock` at slot m is safe for a face naming X only if NO `abst`
--   slot reachable from X is YOUNGER than m
--
-- — a condition on the ORDER of slots, not on the reps.  In this
-- counter-model the chain from slot 0 reaches the `abst` at slot 1 and
-- the lock is at slot 2, which is older: refused, correctly.
--
-- That is the same shape as every previous verdict: the wall is about
-- what a lock can EVER hide, and `abst` slots are exactly the places
-- where "ever" is not yet decided.  The three candidates died because
-- each read the type context at one moment; the surviving formulations
-- must either (a) carry the order condition above, or (b) stop `⊢retag`
-- from refining under a lock at all — i.e. make TyBeta's contractum
-- unmask what it re-owns, or forbid `dual`'s locks from outliving the
-- crossing.

------------------------------------------------------------------------
-- §6  THE TWO REDUCTION CASES THE PREMISE DOES GET RIGHT
------------------------------------------------------------------------

-- Recorded because they survive the counter-model: whatever replaces
-- `ChainScoped` will want them, and they are the reason following the
-- chain is the right shape even though this particular reading of it is
-- not stable.

-- A chain reached THROUGH a type continues into that type's variables.
chain-mono : ∀ {F Y Z A B}
  → Reach F Y A → Z ∈ᵗ A → Reach F Z B → Reach F Y B
chain-mono r i (rz d)       = rs r i d
chain-mono r i (rs r′ i′ d) = rs (chain-mono r i r′) i′ d

-- CANCELR, DECIDED.  The residue's face is `mkId A` for the looked-up rep
-- `A`, so its leaves are exactly `A`'s variables — every one of them ON
-- Y's CHAIN.  The premise at Y therefore covers the whole residue, with
-- no lifting into Θ₁ and no extra hypothesis.  This is precisely what
-- following the chain buys over stopping at the rep.
cancelR-leaves : ∀ {Δ Θ Y Z A}
  → ChainScoped Δ Θ Y → Reach (exterior Θ Δ) Y A → Z ∈ᵗ A
    ----------------------------------------------------
  → ChainScoped Δ Θ Z
cancelR-leaves cs r i r′ = cs (chain-mono r i r′)

-- IDPUSH, DECIDED.  It keeps BOTH frames and BOTH names and swaps only
-- the faces: the inner `id (` X)` becomes `unseal X` at the SAME Θ₁, and
-- the outer `unseal Y` becomes `mkId A` at the SAME Θ₂ (whose leaves are
-- covered by `cancelR-leaves`).  So the premise transports on the nose —
-- the gap the face-conditioned candidate had (the exterior type says
-- nothing about Θ₁) does NOT recur, and its witness `R★` is refused
-- (`¬ChainScoped-R★`) rather than stepping to something untypeable.
idPush-inner : ∀ {Ξ Θ₁ X} → ChainScoped Ξ Θ₁ X → ChainScoped Ξ Θ₁ X
idPush-inner cs = cs

-- SO THE SCORE, on the premise as stated:
--
--   ⊑-stable                       NO   §4 (`¬ChainFaced`) — the kill
--   refuses `¬IdPushCase`'s Ri     yes  `¬ChainScoped-Ri`
--   refuses the Θ₁-lock witness R★ yes  `¬ChainScoped-R★`
--   admits Examples §12's L₄       yes  `ChainScoped-L₄`
--   admits the §1 kill test        yes  `ChainScoped-killtest`(`-redex`)
--   preserved by IdPush            yes  `idPush-inner`
--   preserved by CancelR's residue yes  `cancelR-leaves`
--   mintable at TyBeta             n/a  the mint is lock-free, but §4
--                                       shows TyBeta breaks the premise
--                                       at OTHER wrappers, by retagging
--   Peel crossing                  yes  the crossing face's SOURCE is a
--                                       `shiftBy`, so its target names no
--                                       owner of the crossed boundary
--   TyPeelR                        n/a  same retag defect as TyBeta
--
-- Every entry but the first is green.  The first is the whole game.

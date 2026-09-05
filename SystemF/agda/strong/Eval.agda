module strong.Eval where

-- Strong System F — A LIGHTWEIGHT EVALUATOR.
--
--   step : TCtx → Term → Maybe Term
--
-- a STEP FUNCTION for the reduction relation _⊢_-→_ (strong.BReduction),
-- INDEPENDENT OF THE TYPING JUDGEMENT: it inspects the term's shape, not
-- a derivation, and returns `nothing` on anything stuck or ill-formed.
-- It is canonical because the relation is DETERMINISTIC — `det`, proved
-- in strong.BReduction — so there is nothing to choose.
--
-- SOUNDNESS IS THE POINT (step-sound, below): whenever `step Δ M` answers
-- `just M′`, the relation really does step, and the WITNESS is built
-- alongside the contractum — `step` is the first projection of `stepΣ`,
-- which returns the pair (M′ , Δ ⊢ M -→ M′).  So no rule can be
-- mis-transcribed here without Agda noticing.  COMPLETENESS is progress,
-- and progress is FALSE in this calculus as it stands (gauntlet §9m,
-- notes/probes/DualIntProbe §5), so it is deliberately out of scope.
--
-- THE AMBIENT Δ.  The relation is knowledge-indexed: Peel builds the
-- AMBIENT DUAL `dualᴳ Δ Θ`, which copies Δ's own entry at every slot the
-- boundary drops without concealing, and TyWrap / TyPeel mint a reveal
-- on a boundary whose interior is read against Δ.  So `step` takes the
-- ambient type context, and the two frames that change it — ξ-Λ, at
-- (abst ∷ Δ), and ξ-⟪⟫, at (intOf Δ Θ) — pass the right one inward,
-- exactly as the rules say.
--
-- *** EVAL IS TYPE-BLIND, AND THAT IS A FEATURE. ***  Preservation is
-- FALSE for this calculus at a Peel whose dual demotes a slot the
-- crossing argument's own boundary conceals (strong/notes/probes/
-- DualIntProbe.agda §5: ⊢Redex is well typed at ℕ, `peel-step` fires,
-- and ¬⊢contractum shows the contractum has no typing at all).  Because
-- `step` never consults a typing derivation, it STEPS STRAIGHT THROUGH
-- that Peel and keeps running on the ill-typed contractum — which is
-- precisely what makes the evaluator usable as an INSTRUMENT on the
-- counterexample: strong/notes/probes/EvalProbe.agda §4 prints the run
-- and marks the state at which typability is lost.  A type-directed
-- evaluator could not show that trace at all.
--
-- The rule dispatch, in the order `step` tries it:
--
--   ` x , $ n , ƛ           no rule                      (stuck / value)
--   Λ N                     ξ-Λ            at (abst ∷ Δ)
--   L · M                   ξ-·-l ; then Beta / Peel at a value function
--                           and value argument ; then ξ-·-r
--   L ·[ B , A ]            ξ-·[] ; then TyBeta / TyWrap / TyPeel
--   M ⟪ Θ , B₀ ⟫            ξ-⟪⟫ at (intOf Δ Θ) ; then Drop$ / Merge
--
-- Trying the congruence FIRST is what implements the value premises for
-- free: a redex rule's own premises force its subterm to be a value, and
-- `step` returns `nothing` on values, so the congruence never pre-empts
-- a redex it should not.  The Value premises that are still needed —
-- Beta's argument, Peel's two, the ty-rules' bodies, Merge's — are
-- decided by strong.EvalDec's `value?` and consumed as the rule's own
-- premise.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String; _++_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context using (TCtx; TyEntry; abst; rvld; xrvld)
open import strong.Boundary
open import strong.BReduction
open import strong.EvalDec
open import strong.Show using (showTmIn)

------------------------------------------------------------------------
-- A step, WITH its derivation.  `step` is this function's first
-- projection, which is what makes step-sound a three-line theorem
-- instead of a second transcription of the whole rule table.
------------------------------------------------------------------------

Step : TCtx → Term → Set
Step Δ M = Σ Term λ M′ → Δ ⊢ M -→ M′

------------------------------------------------------------------------
-- Peel — the ⇒ face.  The argument crosses inward through the AMBIENT
-- DUAL dualᴳ Δ Θ, and B₁ is transported to the dual's frame by the block
-- permutation swapᵇ.  Every other face shape has no rule here.
------------------------------------------------------------------------

peelAt : (Δ : TCtx) (V : Term) (Θ : BCtx) (B₀ : Ty) (W : Term)
       → Value V → Value W → Maybe (Step Δ ((V ⟪ Θ , B₀ ⟫) · W))
peelAt Δ V Θ (` X)     W v w = nothing
peelAt Δ V Θ `ℕ        W v w = nothing
peelAt Δ V Θ `𝔹        W v w = nothing
peelAt Δ V Θ (`∀ B)    W v w = nothing
peelAt Δ V Θ (B₁ ⇒ B₂) W v w =
  just ( (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫
       , Peel v w )

------------------------------------------------------------------------
-- The two application redexes, at a VALUE function and a VALUE argument:
-- Beta on a bare ƛ, Peel on a wrapper.  Both premises are already in
-- hand, so no rule is fired without its own evidence.
------------------------------------------------------------------------

appRedex : (Δ : TCtx) (L W : Term) → Value L → Value W
         → Maybe (Step Δ (L · W))
appRedex Δ (` x)          W vL vW = nothing
appRedex Δ ($ n)          W vL vW = nothing
appRedex Δ (ƛ A ∙ N)      W vL vW = just (N [ W ]ᵐ , Beta vW)
appRedex Δ (L · M)        W vL vW = nothing
appRedex Δ (Λ N)          W vL vW = nothing
appRedex Δ (L ·[ B , A ]) W vL vW = nothing
appRedex Δ (V ⟪ Θ , B₀ ⟫) W vL vW =
  peelAt Δ V Θ B₀ W (V-⟪⟫⁻ᵥ vL) vW

------------------------------------------------------------------------
-- The type-application redexes at a WRAPPED function, i.e. at a ∀ face.
-- A Λ body is TyWrap's (the binder's slot IS the new reveal's, so
-- nothing moves); a WRAPPER body is TyPeel's (the elimination is pushed
-- inside, and the body is weakened by ⇑ᵀ for the new interior slot).
-- TyPeel's INERT premise is the value restriction — without it the body
-- could be an active wrapper, which steps by Merge under ξ-⟪⟫.
------------------------------------------------------------------------

tyPeelAt : (Δ : TCtx) (M : Term) (Θ : BCtx) (B₀ B A : Ty)
         → Maybe (Step Δ ((M ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]))
tyPeelAt Δ (` x)          Θ B₀ B A = nothing
tyPeelAt Δ ($ n)          Θ B₀ B A = nothing
tyPeelAt Δ (ƛ C ∙ N)      Θ B₀ B A = nothing
tyPeelAt Δ (L · M)        Θ B₀ B A = nothing
tyPeelAt Δ (L ·[ C , D ]) Θ B₀ B A = nothing
tyPeelAt Δ (Λ N)          Θ B₀ B A with value? N
tyPeelAt Δ (Λ N)          Θ B₀ B A | no  ¬v = nothing
tyPeelAt Δ (Λ N)          Θ B₀ B A | yes v  =
  just (N ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫ , TyWrap v)
tyPeelAt Δ (V ⟪ Θ₁ , B₁ ⟫) Θ B₀ B A with value? V
tyPeelAt Δ (V ⟪ Θ₁ , B₁ ⟫) Θ B₀ B A | no ¬v = nothing
tyPeelAt Δ (V ⟪ Θ₁ , B₁ ⟫) Θ B₀ B A | yes v with inert? Θ₁ B₁
tyPeelAt Δ (V ⟪ Θ₁ , B₁ ⟫) Θ B₀ B A | yes v | no ¬i = nothing
tyPeelAt Δ (V ⟪ Θ₁ , B₁ ⟫) Θ B₀ B A | yes v | yes i =
  just ( (⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ peelB Θ B₀ , ` 0 ])
           ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫
       , TyPeel v i )

tyWrapAt : (Δ : TCtx) (M : Term) (Θ : BCtx) (B₀ B A : Ty)
         → Maybe (Step Δ ((M ⟪ Θ , B₀ ⟫) ·[ B , A ]))
tyWrapAt Δ M Θ (` X)     B A = nothing
tyWrapAt Δ M Θ `ℕ        B A = nothing
tyWrapAt Δ M Θ `𝔹        B A = nothing
tyWrapAt Δ M Θ (C ⇒ D)   B A = nothing
tyWrapAt Δ M Θ (`∀ B₀)   B A = tyPeelAt Δ M Θ B₀ B A

-- TyBeta: a boundary is BORN, its single reveal recording the type
-- argument as stored, and the ∀-body annotation becoming the face.
tyRedex : (Δ : TCtx) (L : Term) (B A : Ty)
        → Maybe (Step Δ (L ·[ B , A ]))
tyRedex Δ (` x)          B A = nothing
tyRedex Δ ($ n)          B A = nothing
tyRedex Δ (ƛ C ∙ N)      B A = nothing
tyRedex Δ (L · M)        B A = nothing
tyRedex Δ (L ·[ C , D ]) B A = nothing
tyRedex Δ (Λ N)          B A with value? N
tyRedex Δ (Λ N)          B A | no  ¬v = nothing
tyRedex Δ (Λ N)          B A | yes v  =
  just (N ⟪ rvl A ∷ [] , B ⟫ , TyBeta v)
tyRedex Δ (M ⟪ Θ , B₀ ⟫) B A = tyWrapAt Δ M Θ B₀ B A

------------------------------------------------------------------------
-- The boundary redexes.  Drop$ is the whole base-face action set (the
-- body must be a NUMERAL — a face-only drop is unsound, CancelProbe's
-- lesson), and Merge is the collapse at an ACTIVE face over an INERT
-- one, guarded by strong.EvalDec's `mergeOK?`.
------------------------------------------------------------------------

dropAt : (Δ : TCtx) (n : ℕ) (Θ : BCtx) (B₀ : Ty)
       → Maybe (Step Δ (($ n) ⟪ Θ , B₀ ⟫))
dropAt Δ n Θ (` X)   = nothing
dropAt Δ n Θ `𝔹      = nothing
dropAt Δ n Θ (C ⇒ D) = nothing
dropAt Δ n Θ (`∀ C)  = nothing
dropAt Δ n Θ `ℕ      = just ($ n , Drop$)

mergeAt : (Δ : TCtx) (V : Term) (Θ₁ : BCtx) (B₁ : Ty)
          (Θ₂ : BCtx) (B₂ : Ty)
        → Maybe (Step Δ ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫))
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ with value? V
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | no  ¬v = nothing
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v  with inert? Θ₁ B₁
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v | no  ¬i = nothing
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v | yes i  with active? Θ₂ B₂
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v | yes i | no  ¬a = nothing
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v | yes i | yes a
  with mergeOK? Δ Θ₁ Θ₂ B₁ B₂
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v | yes i | yes a | no  ¬mok = nothing
mergeAt Δ V Θ₁ B₁ Θ₂ B₂ | yes v | yes i | yes a | yes mok =
  just (V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ B₁ ⟫ , Merge v i a mok)

wrapRedex : (Δ : TCtx) (M : Term) (Θ : BCtx) (B₀ : Ty)
          → Maybe (Step Δ (M ⟪ Θ , B₀ ⟫))
wrapRedex Δ (` x)          Θ B₀ = nothing
wrapRedex Δ (ƛ A ∙ N)      Θ B₀ = nothing
wrapRedex Δ (L · M)        Θ B₀ = nothing
wrapRedex Δ (Λ N)          Θ B₀ = nothing
wrapRedex Δ (L ·[ B , A ]) Θ B₀ = nothing
wrapRedex Δ ($ n)          Θ B₀ = dropAt Δ n Θ B₀
wrapRedex Δ (V ⟪ Θ₁ , B₁ ⟫) Θ B₀ = mergeAt Δ V Θ₁ B₁ Θ B₀

------------------------------------------------------------------------
-- THE STEP FUNCTION
------------------------------------------------------------------------

stepΣ : (Δ : TCtx) (M : Term) → Maybe (Step Δ M)
stepΣ Δ (` x)     = nothing
stepΣ Δ ($ n)     = nothing
stepΣ Δ (ƛ A ∙ N) = nothing

stepΣ Δ (Λ N) with stepΣ (abst ∷ Δ) N
stepΣ Δ (Λ N) | nothing        = nothing
stepΣ Δ (Λ N) | just (N′ , st) = just (Λ N′ , ξ-Λ st)

stepΣ Δ (L · M) with stepΣ Δ L
stepΣ Δ (L · M) | just (L′ , st) = just (L′ · M , ξ-·-l st)
stepΣ Δ (L · M) | nothing with value? L
stepΣ Δ (L · M) | nothing | no  ¬v = nothing
stepΣ Δ (L · M) | nothing | yes vL with value? M
stepΣ Δ (L · M) | nothing | yes vL | yes vM = appRedex Δ L M vL vM
stepΣ Δ (L · M) | nothing | yes vL | no ¬vM with stepΣ Δ M
stepΣ Δ (L · M) | nothing | yes vL | no ¬vM | nothing = nothing
stepΣ Δ (L · M) | nothing | yes vL | no ¬vM | just (M′ , st) =
  just (L · M′ , ξ-·-r vL st)

stepΣ Δ (L ·[ B , A ]) with stepΣ Δ L
stepΣ Δ (L ·[ B , A ]) | nothing        = tyRedex Δ L B A
stepΣ Δ (L ·[ B , A ]) | just (L′ , st) =
  just (L′ ·[ B , A ] , ξ-·[] st)

stepΣ Δ (M ⟪ Θ , B₀ ⟫) with stepΣ (intOf Δ Θ) M
stepΣ Δ (M ⟪ Θ , B₀ ⟫) | nothing        = wrapRedex Δ M Θ B₀
stepΣ Δ (M ⟪ Θ , B₀ ⟫) | just (M′ , st) =
  just (M′ ⟪ Θ , B₀ ⟫ , ξ-⟪⟫ st)

fstStep : ∀ {Δ M} → Maybe (Step Δ M) → Maybe Term
fstStep nothing         = nothing
fstStep (just (M′ , _)) = just M′

step : (Δ : TCtx) (M : Term) → Maybe Term
step Δ M = fstStep (stepΣ Δ M)

------------------------------------------------------------------------
-- *** SOUNDNESS ***  the answer is always a real step of the relation.
------------------------------------------------------------------------

fstStep-sound : ∀ {Δ M M′} (r : Maybe (Step Δ M))
              → fstStep r ≡ just M′ → Δ ⊢ M -→ M′
fstStep-sound (just (N , st)) refl = st
fstStep-sound nothing         ()

step-sound : ∀ {Δ M M′} → step Δ M ≡ just M′ → Δ ⊢ M -→ M′
step-sound {Δ} {M} e = fstStep-sound (stepΣ Δ M) e

------------------------------------------------------------------------
-- TRACES.  `trace k Δ M` is the sequence of states M, M₁, …, stopping
-- when `step` returns nothing (stuck, or a value) or when the fuel runs
-- out.  The list always contains M itself, so it is never empty.
------------------------------------------------------------------------

trace : ℕ → TCtx → Term → List Term
trace zero    Δ M = M ∷ []
trace (suc k) Δ M with step Δ M
trace (suc k) Δ M | nothing = M ∷ []
trace (suc k) Δ M | just M′ = M ∷ trace k Δ M′

------------------------------------------------------------------------
-- RENDERING A WHOLE TRACE in one call, so that scripts/render_term.sh
-- can print a run rather than a state (usage in strong/Show.agda's
-- header).  Each state goes through strong.Show's showTmIn at the
-- ambient's own length, and the states are joined by a step arrow.
--
--   scripts/render_term.sh 'showTrace 20 0 cxP₀' \
--     'open import strong.notes.InstallGauntlet'
--
-- The script reads the string out of an Agda type-error, so the newline
-- in the separator arrives ESCAPED; pipe through  sed 's/\\n/\n/g'  to
-- get one state per line.
------------------------------------------------------------------------

stepSep : String
stepSep = "
  —→  "

showStates : ℕ → List Term → String
showStates n []             = "·"
showStates n (M ∷ [])       = showTmIn n M
showStates n (M ∷ N ∷ Ms) =
  showTmIn n M ++ stepSep ++ showStates n (N ∷ Ms)

-- the general form: the REAL ambient context, whose entries Peel's dual
-- copies, with its own length used for the naming supply
showTraceIn : ℕ → TCtx → Term → String
showTraceIn k Δ M = showStates (length Δ) (trace k Δ M)

-- fuel + AMBIENT LENGTH.  The ambient is taken to be n Λ-bound
-- variables (prepAbst n []) — the right reading for a run under a
-- sequence of type abstractions, and exactly [] at n = 0.  Where the
-- ambient carries KNOWLEDGE (a `rvld` entry), Peel's dual copies it, so
-- use showTraceIn with the real context instead.
showTrace : ℕ → ℕ → Term → String
showTrace k n M = showStates n (trace k (prepAbst n []) M)

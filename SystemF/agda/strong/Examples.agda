module strong.Examples where

-- THE LIVING REGRESSION for the conversion-boundary design.
--
-- §1  T₆ — the transparent-layer (β2) family — RUNS TO 7 under IdPush.
-- §2  the cancel pair (Cancel + Drop$).
-- §3  T₈ — stacked id-layers — and its birth story (TyPeelR ⨟ TyBeta).
-- §4  Tᵣ and Tₘ — the two adversaries the retired `⊳` could NOT clear —
--     both run to 7 under IdPush.
-- §5  the three preservation BREAKS of the previous design (c10/c11, n1b,
--     n4) and the shape-IV survivor E★′: they type, they CROSS, and their
--     contracta are TYPED.
-- §6  the first end-to-end run from a CLOSED, PLAIN source program.
-- §7  three regressions on substᵐ (the Λ clause, the ƛ clause, and what
--     the Λ-crossing wrapper costs at a base type); §8 progress on §6;
--     §9 preservation on §6.
-- (§10 is GONE.  It held the reachability verdict for the old IdPush
--     contractum's scoping side-condition; the scope move (strong.Reduction
--     §2b) removed the side-condition, and the invariant hunt behind it is
--     recorded in notes/DECISIONS.md, 2026-09-06.  Later section numbers
--     are unchanged.)
-- §11 IDPUSH FROM CLOSED, PLAIN SOURCE — the run `Q` Jeremy asked for,
--     plus the three variants: (ii) a CHAINED conversion rep (`R`),
--     (iii) IdPush firing TWICE (`D`), and (i) a multi-bind Θ₁, which
--     turns out to be reachable only through TyPeelR — whose contractum
--     is here refuted from closed source for the first time (`G`).
-- §12 the WALL, probed for reachability post-Peel-repair (`L`): the
--     c10/c11 blocked type context IS reached from closed source, but in
--     a Θ₁ position, never as the Θ₂ a rule reads a rep out of.
-- §13 TYPEELR FROM CLOSED, PLAIN SOURCE, at a CONCEAL and a REVEAL
--     conversion: `J` (a CONCEAL ∀ conversion, the polymorphic
--     argument) runs to its answer 3 through the TyPeelR contractum the
--     retired polarity index used to refuse, `H` is the REVEAL mirror,
--     and §13c records the contracta weighed against the landed rule.
-- §14 THE PRE-BOUNDARY COUNTEREXAMPLE: `E`, the closed program that
--     refuted the per-variable design (v1's historical Example 8), run
--     in v2 to a VALUE — the step that used to produce an ill-typed
--     term is `estep₅`, `E-dual-int`/`E-dual-ext` are the frame
--     FRAME-EXACT BETA gives the crossed value, and `E-int`/`E-ext` the
--     two type contexts inside its own Peel-minted wrapper.
-- §15 TIGHTNESS, RULE BY RULE — Jeremy's test (proof/DualTightness)
--     applied to EVERY rule that moves a subterm into a new frame:
--     `TyBeta` (§15a), `TyPeelR` (§15b), `IdPush`/`CancelR` (§15c),
--     `Beta` (§15d, with the one expected exception — ERASURE; §15d₂ is
--     the UNDER-Λ case frame-exact Beta added), `Peel`'s `bind` half and
--     `hideBinds` (§15e; the `unlock` half is proof/DualTightness).
--     Every redex below is ILL TYPED and every contractum is REFUSED for
--     the same localized reason.  §15f collects the six frame identities
--     that make the section a theorem rather than six anecdotes.
-- §16 THE CHANGE LISTS, MEASURED — §14's `E₀` instantiated once more and
--     APPLIED (`F₀`, 36 steps to 42).  This is the run on which the
--     scope move's replayed and re-moved change lists used to DOUBLE at
--     every pass; the peak list length and the peak entry count are
--     pinned by `refl`, before (130 / 389) and after (50 / 101) the two
--     redundancy tests of strong.CtxMorph §4.
--
-- Every `_ : … ≡ …` in this file is a machine-checked frame computation.
--
-- AND EVERY PINNED RUN IS CHECKED AGAINST THE GENERATED ONE.  The chains
-- below are hand-composed, because they are readable; `strong.Eval`'s
-- `evalTerms` — progress iterated under preservation — regenerates them,
-- and the seven runs from closed or hand-built sources (§6 `P₀`,
-- §11 `Q₀`, §12 `L₀`, §12b `Ri`, §13a `J₀`, §13b `H₀`, §14 `E₀`) each
-- carry an `evalTerms n ⊢X₀ ≡ …` line that Agda checks by `refl`.
--
-- STEP COUNTS AFTER FRAME-EXACT BETA (2026-09-08).  A run changes length
-- exactly where a `Beta` substitutes under a `Λ`, and then only because
-- the minted transparent layer has to be walked through:
--
--   P₀  6 → 6    (the body is a bare variable: no Λ crossed)
--   Q₀  9 → 11   (+1 IdPush, +1 Drop$)
--   D₀  12 → 16  (two Λs crossed: +2 IdPush, +2 Drop$)
--   R₀  18 → 21  (+1 IdPush, +1 CancelR, +1 Drop$)
--   L₀  9 → 11   (+1 IdPush, +1 Drop$)
--   Ri  2 → 2    (hand-built; no Beta)
--   J₀  14 → 14  (the substituted variable sits under no Λ)
--   H₀  4 → 4    (the layer lands inside a ƛ body, unevaluated)
--   E₀  5 → 6    (+1 TyPeelR — §14's `estep₅`)
--   G   5 → 5    (`gstep₁ … gstep₅`; the layers land under the Λs,
--                 unevaluated)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- §1  T₆ — the transparent layer, and its run to 7
------------------------------------------------------------------------

-- T₆ = ((7 ⟪ [] , seal 1 ⟫) ⟪ bind ℕ , id (` 1) ⟫) ⟪ bind ℕ , unseal 0 ⟫
-- typed at ℕ, not a value, and — before IdPush — no rule fired: Cancel
-- wanted a seal-topped interior, Drop$ a base conversion, ξ-⟪⟫ a
-- stepping interior.  The middle wrapper is the "transparent layer".

Δ₆ S₆₁ S₆₂ : Ctxᵗ
Δ₆  = unmasked (bind `ℕ) ∷ []
S₆₁ = unmasked (bind `ℕ) ∷ Δ₆
S₆₂ = unmasked (bind `ℕ) ∷ S₆₁

W₆₀ W₆₁ T₆ : Term
W₆₀ = ($ 7) ⟪ morph [] [] , seal 1 ⟫
W₆₁ = W₆₀ ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫
T₆  = W₆₁ ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

⊢W₆₀ : S₆₂ ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀ = env (mw rw[] sw[]) ⊢$ (conv-seal (es ez))
           (wf-var (unmasked (bind `ℕ) , es ez , nameable))

⊢W₆₁ : S₆₁ ∣ [] ⊢ W₆₁ ⦂ ` 0
⊢W₆₁ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢W₆₀
           (conv-idv (unmasked (bind `ℕ) , es ez , nameable))
           (wf-var (unmasked (bind `ℕ) , ez , nameable))

⊢T₆ : Δ₆ ∣ [] ⊢ T₆ ⦂ `ℕ
⊢T₆ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢W₆₁ (conv-unseal ez) wf-ℕ

¬val-T₆ : ¬ Value T₆
¬val-T₆ (V-⟪⟫ _ ())

-- STEP 1 — IDPUSH.  The two CONVERSIONS swap; both frames are untouched.
-- The pushed name `1` is the identity conversion's bind variable
-- (proof/IdLayer.agda, `idpush-name`), and the residue conversion is the
-- identity at the LOOKED-UP rep — the lookup premise, exactly as ruled.
T₆-1 : Term
T₆-1 = (W₆₀ ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

push-T₆ : Δ₆ ⊢ T₆ -→ T₆-1
push-T₆ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢T₆-1-in : S₆₁ ∣ [] ⊢ W₆₀ ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫ ⦂ `ℕ
⊢T₆-1-in = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢W₆₀ (conv-unseal (es ez)) wf-ℕ

⊢T₆-1 : Δ₆ ∣ [] ⊢ T₆-1 ⦂ `ℕ
⊢T₆-1 = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢T₆-1-in (conv-id base-ℕ) wf-ℕ

-- STEP 2 — the seal/unseal pair is now ADJACENT: the ordinary cancel
-- fires.  BOTH FRAMES STAY (the repaired rule) and both conversions
-- become the identity at the looked-up rep, so the seal's own (here
-- empty) frame survives as one more transparent layer.
T₆-2 : Term
T₆-2 = ((($ 7) ⟪ morph [] [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
         ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

cancel-T₆ : Δ₆ ⊢ T₆-1 -→ T₆-2
cancel-T₆ = ξ-⟪⟫ (CancelR V-$ (es ez))

⊢T₆-2-in : S₆₁ ∣ []
         ⊢ ($ 7) ⟪ morph [] [] , id `ℕ ⟫ ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫ ⦂ `ℕ
⊢T₆-2-in = env (mw (rw-b wf-ℕ rw[]) sw[])
                (env (mw rw[] sw[]) ⊢$ (conv-id base-ℕ) wf-ℕ)
                (conv-id base-ℕ) wf-ℕ

⊢T₆-2 : Δ₆ ∣ [] ⊢ T₆-2 ⦂ `ℕ
⊢T₆-2 = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢T₆-2-in (conv-id base-ℕ) wf-ℕ

-- STEPS 3, 4, 5 — base conversions over a numeral, innermost first.
run-T₆ : Δ₆ ⊢ T₆ -→* $ 7
run-T₆ = push-T₆
    then cancel-T₆
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

------------------------------------------------------------------------
-- §2  The cancel pair
------------------------------------------------------------------------

-- (7 ⟪ ↓X , seal 0 ⟫) ⟪ ↑X:=ℕ , unseal 0 ⟫ — outer conversion ACTIVE,
-- inner INERT, read straight off the conversion constructors.

Θ↑ Θ↓ : CtxMorph
Θ↑ = morph (`ℕ ∷ []) []
Θ↓ = morph [] (lock 0 ∷ [])

cancelTm : Term
cancelTm = (($ 7) ⟪ Θ↓ , seal 0 ⟫) ⟪ Θ↑ , unseal 0 ⟫

⊢cancelTm : [] ∣ [] ⊢ cancelTm ⦂ `ℕ
⊢cancelTm =
  env (mw (rw-b wf-ℕ rw[]) sw[])
      (env (mw rw[] (sw-l (_ , ez , nameable) sw[])) ⊢$
           (conv-seal ez) (wf-var (_ , ez , nameable)))
      (conv-unseal ez)
      wf-ℕ

-- the pair is NOT a value (the outer conversion is active) and the
-- cancel fires.  BOTH FRAMES STAY and both conversions become the
-- identity at the looked-up rep (the repaired rule): nothing that `V`
-- might name is dropped, and the mini-core's extra `hideBinds` — which
-- masked an exterior slot that does not exist (proof/MaskFacts
-- `¬⊢ᵐ-cancel-residue`) — is gone for good.
cancel-step : [] ⊢ cancelTm
            -→ (($ 7) ⟪ Θ↓ , id `ℕ ⟫) ⟪ Θ↑ , id `ℕ ⟫
cancel-step = CancelR V-$ ez

drop-step-in : [] ⊢ (($ 7) ⟪ Θ↓ , id `ℕ ⟫) ⟪ Θ↑ , id `ℕ ⟫
             -→ ($ 7) ⟪ Θ↑ , id `ℕ ⟫
drop-step-in = ξ-⟪⟫ (Drop$ base-ℕ)

drop-step : [] ⊢ ($ 7) ⟪ Θ↑ , id `ℕ ⟫ -→ $ 7
drop-step = Drop$ base-ℕ

run-cancelTm : [] ⊢ cancelTm -→* $ 7
run-cancelTm = cancel-step then drop-step-in then drop-step then done

_ : mkId `ℕ ≡ id `ℕ
_ = refl

------------------------------------------------------------------------
-- §3  T₈ — stacked id-layers, and where they come from
------------------------------------------------------------------------

LA LB T₈ : Term
LA = (($ 7) ⟪ morph [] [] , seal 2 ⟫) ⟪ morph ((` 0) ∷ []) [] , id (` 2) ⟫
LB = LA ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫
T₈ = LB ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

SA : Ctxᵗ
SA = unmasked (bind (` 0)) ∷ S₆₂            -- the interior type context of LA

⊢LA-in : SA ∣ [] ⊢ ($ 7) ⟪ morph [] [] , seal 2 ⟫ ⦂ ` 2
⊢LA-in = env (mw rw[] sw[]) ⊢$ (conv-seal (es (es ez)))
             (wf-var (unmasked (bind `ℕ) , es (es ez) , nameable))

⊢LA : S₆₂ ∣ [] ⊢ LA ⦂ ` 1
⊢LA = env (mw (rw-b (wf-var (unmasked (bind `ℕ) , ez , nameable)) rw[]) sw[])
          ⊢LA-in
          (conv-idv (unmasked (bind `ℕ) , es (es ez) , nameable))
          (wf-var (unmasked (bind `ℕ) , es ez , nameable))

⊢LB : S₆₁ ∣ [] ⊢ LB ⦂ ` 0
⊢LB = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢LA
          (conv-idv (unmasked (bind `ℕ) , es ez , nameable))
          (wf-var (unmasked (bind `ℕ) , ez , nameable))

⊢T₈ : Δ₆ ∣ [] ⊢ T₈ ⦂ `ℕ
⊢T₈ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢LB (conv-unseal ez) wf-ℕ

-- The stack resolves ONE LAYER PER STEP, outermost first: each IdPush moves
-- the active conversion one layer inward toward the seal, so any depth
-- terminates.  (IdAbsorb needed `⊳` to merge the frames and could not do
-- this one — the inner layer's bind `` ` 0 `` names the next layer's
-- binder, IdLayerProbe §4c.  IdPush touches no frame.)
T₈-1 T₈-2 T₈-3 : Term
T₈-1 = (LA ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
T₈-2 = (((($ 7) ⟪ morph [] [] , seal 2 ⟫) ⟪ morph ((` 0) ∷ []) [] , unseal 2 ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
T₈-3 = (((($ 7) ⟪ morph [] [] , id `ℕ ⟫) ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

push-T₈  : Δ₆ ⊢ T₈ -→ T₈-1
push-T₈  = IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) ez

push-T₈′ : Δ₆ ⊢ T₈-1 -→ T₈-2
push-T₈′ = ξ-⟪⟫ (IdPush (V-⟪⟫ V-$ I-seal) (es ez))

cancel-T₈ : Δ₆ ⊢ T₈-2 -→ T₈-3
cancel-T₈ = ξ-⟪⟫ (ξ-⟪⟫ (CancelR V-$ (es (es ez))))

run-T₈ : Δ₆ ⊢ T₈ -→* $ 7
run-T₈ = push-T₈
    then push-T₈′
    then cancel-T₈
    then ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── the birth story ────────────────────────────────────────────────────
-- An id-layer is minted by an ordinary TyBeta whose body type is an OUTER
-- variable: `reveal 0 (` 1)` is the identity conversion, and the binder
-- it binds is never read.
_ : reveal 0 (` 1) ≡ id (` 1)
_ = refl

⊢W₆₀Λ : (unmasked abst ∷ S₆₁) ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀Λ = env (mw rw[] sw[]) ⊢$ (conv-seal (es ez))
            (wf-var (unmasked (bind `ℕ) , es ez , nameable))

Pkg : Term
Pkg = (Λ W₆₀) ⟪ morph [] [] , `∀ (id (` 1)) ⟫

⊢Pkg : S₆₁ ∣ [] ⊢ Pkg ⦂ `∀ (` 1)
⊢Pkg = env (mw rw[] sw[]) (⊢Λ ⊢W₆₀Λ)
           (conv-all (conv-idv (unmasked (bind `ℕ) , es ez , nameable)))
           (wf-∀ (wf-var (unmasked (bind `ℕ) , es ez , nameable)))

T₉ : Term
T₉ = (Pkg ·[ ` 1 , `ℕ ]) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

⊢T₉ : Δ₆ ∣ [] ⊢ T₉ ⦂ `ℕ
⊢T₉ = env (mw (rw-b wf-ℕ rw[]) sw[]) (⊢·[] ⊢Pkg wf-ℕ) (conv-unseal ez) wf-ℕ

-- TyPeelR mints the id-layer no matter what TyBeta does.  On an IDENTITY
-- ∀ conversion the mint is the conversion itself
-- (`instReveal 0 (id (` 1)) = id (` 1)`, since slot 1 is not the new
-- binder) and the pushed-in annotation is the interior ∀-body, SHIFTED
-- past the binder the rule introduces: `` ` 2 `` rather than `` ` 1 ``.
Pk-1 : Term
Pk-1 = ((Λ (($ 7) ⟪ morph [] [] , seal 2 ⟫)) ·[ ` 2 , ` 0 ])
         ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫

⊢Pk-conv : (unmasked abst ∷ convCtx (morph [] []) S₆₁) ⊢ id (` 1) ∶ ` 1 ⇝ ` 1
⊢Pk-conv = conv-idv (unmasked (bind `ℕ) , es ez , nameable)

typeel-T₉ : Δ₆ ⊢ T₉ -→ Pk-1 ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
typeel-T₉ = ξ-⟪⟫ (TyPeelR (V-Λ (V-⟪⟫ V-$ I-seal)) ⊢Pk-conv)

-- and TyBeta then mints exactly T₈'s inner layer.
reaches-T₈ : Δ₆ ⊢ T₉ -→* T₈
reaches-T₈ = typeel-T₉
        then ξ-⟪⟫ (ξ-⟪⟫ (TyBeta (V-⟪⟫ V-$ I-seal)))
        then done

-- ── why TyBeta needs its Value premise (repair 5) ──────────────────────
-- This calculus reduces UNDER Λ, so a Λ-body can be a redex and `Λ N` is
-- then not a value.  `TyBeta`'s LHS pattern `(Λ N) ·[ B , A ]` matches such
-- a term as well, and so does `ξ-·[] ⨟ ξ-Λ`, with DIFFERENT contracta — a
-- genuine overlap that repair (1) (V-Λ's Value premise) does not close.
-- With `Value N` on TyBeta the order is forced: the body reduces first, and
-- only the resulting VALUE package is instantiated.

Ωt : Term
Ωt = Λ ((ƛ `ℕ ∙ ($ 1)) · ($ 2))

⊢Ωt : [] ∣ [] ⊢ Ωt ·[ `ℕ , `ℕ ] ⦂ `ℕ
⊢Ωt = ⊢·[] (⊢Λ (⊢· (⊢ƛ wf-ℕ ⊢$) ⊢$)) wf-ℕ

¬val-Ωt : ¬ Value Ωt
¬val-Ωt (V-Λ ())

-- the body steps first …
body-first : [] ⊢ Ωt ·[ `ℕ , `ℕ ] -→ (Λ ($ 1)) ·[ `ℕ , `ℕ ]
body-first = ξ-·[] (ξ-Λ (Beta V-$))

-- … and only then is the (now valuable) package instantiated.
then-tybeta : [] ⊢ (Λ ($ 1)) ·[ `ℕ , `ℕ ]
                -→ ($ 1) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
then-tybeta = TyBeta V-$

run-Ωt : [] ⊢ Ωt ·[ `ℕ , `ℕ ] -→* $ 1
run-Ωt = body-first then then-tybeta then Drop$ base-ℕ then done

------------------------------------------------------------------------
-- §4  The two adversaries `⊳` could not clear
------------------------------------------------------------------------

-- ── Tᵣ (IdLayerProbe §4c): the id-layer's context morphism carries a rep that
-- NAMES the outer boundary's binder.  Merging the frames would have to
-- SUBSTITUTE reps into reps — rep arithmetic, i.e. the retired `⊕`.
-- IdPush touches no frame, so the instance is ordinary.

Θᵣ₁ Θᵣ₂ : CtxMorph
Θᵣ₁ = morph ((` 0) ∷ []) []
Θᵣ₂ = morph (`ℕ ∷ []) []

Sᵣ : Ctxᵗ
Sᵣ = unmasked (bind (` 0)) ∷ unmasked (bind `ℕ) ∷ []

Vᵣ Tᵣ : Term
Vᵣ = ($ 7) ⟪ morph [] [] , seal 1 ⟫
Tᵣ = (Vᵣ ⟪ Θᵣ₁ , id (` 1) ⟫) ⟪ Θᵣ₂ , unseal 0 ⟫

_ : interior Θᵣ₁ (interior Θᵣ₂ []) ≡ Sᵣ
_ = refl

⊢Vᵣ : Sᵣ ∣ [] ⊢ Vᵣ ⦂ ` 1
⊢Vᵣ = env (mw rw[] sw[]) ⊢$ (conv-seal (es ez))
          (wf-var (unmasked (bind `ℕ) , es ez , nameable))

⊢Tᵣ : [] ∣ [] ⊢ Tᵣ ⦂ `ℕ
⊢Tᵣ = env (mw (rw-b wf-ℕ rw[]) sw[])
          (env (mw (rw-b (wf-var (unmasked (bind `ℕ) , ez , nameable)) rw[])
                   sw[])
               ⊢Vᵣ
               (conv-idv (unmasked (bind `ℕ) , es ez , nameable))
               (wf-var (unmasked (bind `ℕ) , ez , nameable)))
          (conv-unseal ez) wf-ℕ

push-Tᵣ : [] ⊢ Tᵣ -→ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫
push-Tᵣ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢push-Tᵣ : [] ∣ [] ⊢ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tᵣ = env (mw (rw-b wf-ℕ rw[]) sw[])
               (env (mw (rw-b (wf-var (unmasked (bind `ℕ) , ez , nameable))
                              rw[]) sw[])
                    ⊢Vᵣ (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tᵣ : [] ⊢ Tᵣ -→* $ 7
run-Tᵣ = push-Tᵣ
    then ξ-⟪⟫ (CancelR V-$ (es ez))
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── Tₘ (IdLayerProbe §4b): Θ₂ re-exposes a masked slot (`unlock 0`) and the
-- id-layer masks it again (`lock 0`).  The merged morphism computed both
-- type contexts correctly and yet the FORMER, simultaneous `_⊢ᵐ_` refused
-- it, because it checked every entry against the plain exterior.  The
-- SEQUENTIAL judgement checks each entry on the frame it acts on, and
-- accepts it.  Again: IdPush merges nothing.

Δₘ Mₘ : Ctxᵗ
Δₘ = masked (bind `𝔹) ∷ unmasked (bind `ℕ) ∷ []
Mₘ = unmasked (bind `𝔹) ∷ unmasked (bind `ℕ) ∷ []

Θₘ₁ Θₘ₂ : CtxMorph
Θₘ₁ = morph [] (lock 0 ∷ [])
Θₘ₂ = morph [] (unlock 0 ∷ [])

Vₘ Tₘ : Term
Vₘ = ($ 7) ⟪ morph [] [] , seal 1 ⟫
Tₘ = (Vₘ ⟪ Θₘ₁ , id (` 1) ⟫) ⟪ Θₘ₂ , unseal 1 ⟫

_ : interior Θₘ₂ Δₘ ≡ Mₘ
_ = refl

⊢Vₘ : Δₘ ∣ [] ⊢ Vₘ ⦂ ` 1
⊢Vₘ = env (mw rw[] sw[]) ⊢$ (conv-seal (es ez))
          (wf-var (unmasked (bind `ℕ) , es ez , nameable))

⊢Tₘ : Δₘ ∣ [] ⊢ Tₘ ⦂ `ℕ
⊢Tₘ = env (mw rw[] (sw-u (_ , ez , locked) sw[]))
          (env (mw rw[] (sw-l (unmasked (bind `𝔹) , ez , nameable) sw[])) ⊢Vₘ
               (conv-idv (unmasked (bind `ℕ) , es ez , nameable))
               (wf-var (unmasked (bind `ℕ) , es ez , nameable)))
          (conv-unseal (es ez)) wf-ℕ

-- THE SCOPE MOVE IS VISIBLE HERE, and this is the one run on which it
-- is: `Θₘ₂` is not binds-only (it carries the re-exposing `unlock 0`), so
-- the contractum's inner frame gains it at the tail — where `scope`
-- applies it FIRST, exactly where `Θₘ₂` applied it.  The outer frame
-- REWINDS it (`rewind Θₘ₂ ≡ lock 0 ∷ unlock 0 ∷ []`), which on this run
-- is literally the same list as the merged inner frame.
Θₘ₁′ : CtxMorph
Θₘ₁′ = morph [] (lock 0 ∷ unlock 0 ∷ [])

_ : _≡_ {A = CtxMorph} (Θₘ₁ ⋉ Θₘ₂) Θₘ₁′
_ = refl

_ : _≡_ {A = CtxMorph} (rewind Θₘ₂) Θₘ₁′
_ = refl

_ : interior (rewind Θₘ₂) Δₘ ≡ Δₘ
_ = refl

-- … and the value's own frame is unchanged: the moved `unlock 0` is
-- undone by the `lock 0` that already stood in front of it.
_ : interior Θₘ₁′ (interior (rewind Θₘ₂) Δₘ) ≡ interior Θₘ₁ (interior Θₘ₂ Δₘ)
_ = refl

⊢ᵐΘₘ₁′ : Δₘ ⊢ᵐ Θₘ₁′
⊢ᵐΘₘ₁′ = mw rw[]
            (sw-l (unmasked (bind `𝔹) , ez , nameable)
                  (sw-u (_ , ez , locked) sw[]))

push-Tₘ : Δₘ ⊢ Tₘ -→ (Vₘ ⟪ Θₘ₁′ , unseal 1 ⟫) ⟪ rewind Θₘ₂ , id `ℕ ⟫
push-Tₘ = IdPush (V-⟪⟫ V-$ I-seal) (es ez)

⊢push-Tₘ : Δₘ ∣ [] ⊢ (Vₘ ⟪ Θₘ₁′ , unseal 1 ⟫) ⟪ Θₘ₁′ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tₘ = env ⊢ᵐΘₘ₁′
               (env ⊢ᵐΘₘ₁′ ⊢Vₘ (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tₘ : Δₘ ⊢ Tₘ -→* $ 7
run-Tₘ = push-Tₘ
    then ξ-⟪⟫ (CancelR V-$ (es ez))
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

------------------------------------------------------------------------
-- §5  The three preservation BREAKS, and the shape-IV survivor
------------------------------------------------------------------------

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

Ren-suc : ∀ {E Δ} → Ren suc Δ (E ∷ Δ)
Ren-suc = mkRen (λ d → es d)

-- ── c10 / c11 (the §9n break) ──────────────────────────────────────────
--   old:  Δd = rvld (` 0) ∷ abst ∷ rvld `ℕ ∷ []   W:=X , X , V:=ℕ
--   The reveal's rep NAMES the chained slot W, whose bind knowledge is the
--   Λ-bound X; the old dual DEMOTED W and the crossing value's licence died.

Δd : Ctxᵗ                       -- W:=X , X abstract , V:=ℕ
Δd = unmasked (bind (` 0)) ∷ unmasked abst ∷ unmasked (bind `ℕ) ∷ []

-- W's rep, read on Δd, is the Λ-bound X — the chained spelling that broke.
_ : Δd ∋ 0 := ` 1
_ = ez

Θ2 : CtxMorph                       -- bind(W) , conceal V
Θ2 = morph ((` 0) ∷ []) (lock 2 ∷ [])

-- ONE frame change: the binder is pushed on, V is MASKED IN PLACE (the entry
-- `unmasked (bind `ℕ)` survives as `masked (bind `ℕ)`), nothing is
-- dropped.
_ : interior Θ2 Δd
      ≡ unmasked (bind (` 0)) ∷ unmasked (bind (` 0))
      ∷ unmasked abst ∷ masked (bind `ℕ) ∷ []
_ = refl

-- the CONVERSION CONTEXT keeps every slot live, so a conceal's licence
-- resolves.
_ : convCtx Θ2 Δd
      ≡ unmasked (bind (` 0)) ∷ unmasked (bind (` 0))
      ∷ unmasked abst ∷ unmasked (bind `ℕ) ∷ []
_ = refl

cΘ2 : Conv                      -- (X⇒X)⇒ℕ  ⇝  (W⇒W)⇒ℕ
cΘ2 = (unseal 0 ↦ seal 0) ↦ id `ℕ

Vd Wd : Term
Vd = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
Wd = (ƛ (` 1) ∙ (` 0)) ⟪ morph [] (lock 0 ∷ []) , unseal 0 ↦ seal 0 ⟫

⊢cΘ2 : convCtx Θ2 Δd ⊢ cΘ2 ∶ ((` 0 ⇒ ` 0) ⇒ `ℕ) ⇝ ((` 1 ⇒ ` 1) ⇒ `ℕ)
⊢cΘ2 = conv-fun (conv-fun (conv-unseal ez) (conv-seal ez)) (conv-id base-ℕ)

⊢Fnd : Δd ∣ [] ⊢ Vd ⟪ Θ2 , cΘ2 ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fnd = env (mw (rw-b (wf-var (_ , ez , nameable)) rw[])
               (sw-l (_ , es (es ez) , nameable) sw[]))
           (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable))
                     (wf-var (_ , ez , nameable))) ⊢$)
           ⊢cΘ2
           (wf-⇒ (wf-⇒ (wf-var (_ , ez , nameable))
                       (wf-var (_ , ez , nameable))) wf-ℕ)

-- THE CROSSING VALUE.  Its bind boundary masks W and seals at it: the licence
-- `seal 0` cites the binder at slot 0 of Δd, whose rep is X = ` 1.
_ : interior (morph [] (lock 0 ∷ [])) Δd
      ≡ masked (bind (` 0)) ∷ unmasked abst ∷ unmasked (bind `ℕ) ∷ []
_ = refl

⊢Wd : Δd ∣ [] ⊢ Wd ⦂ (` 0 ⇒ ` 0)
⊢Wd = env (mw rw[] (sw-l (_ , ez , nameable) sw[]))
          (⊢ƛ (wf-var (_ , es ez , nameable)) (⊢` here))
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (_ , ez , nameable))
                (wf-var (_ , ez , nameable)))

Wd-value : Value Wd
Wd-value = V-⟪⟫ V-ƛ I-fun

⊢Redexd : Δd ∣ [] ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd ⦂ `ℕ
⊢Redexd = ⊢· ⊢Fnd ⊢Wd

peel-d : Δd ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd
           -→ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
                ⟪ Θ2 , id `ℕ ⟫
peel-d = Peel V-ƛ Wd-value

-- THE DUAL is two names and nothing else: mask the binder, re-expose V.
_ : dual Θ2 ≡ morph [] (lock 0 ∷ unlock 3 ∷ [])
_ = refl

-- THE REPOINTING.  The dual's interior is Δd with ONE masked slot in front:
-- every entry of Δd is still there, in the same order, with the same rep.
-- W's entry — the one the old design demoted to `abst` — is untouched.
_ : interior (dual Θ2) (interior Θ2 Δd) ≡ masked (bind (` 0)) ∷ Δd
_ = refl

-- and the dual's CONVERSION CONTEXT is IDENTICAL to the crossed
-- boundary's, so `s` transplants verbatim (no swapᵇ, no re-derivation).
_ : convCtx (dual Θ2) (interior Θ2 Δd) ≡ convCtx Θ2 Δd
_ = refl

-- THE CONTRACTUM IS TYPED.  (The previous design has `¬⊢contractum` here.)
⊢contractumd :
  Δd ∣ [] ⊢ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
              ⟪ Θ2 , id `ℕ ⟫ ⦂ `ℕ
⊢contractumd =
  env (mw (rw-b (wf-var (_ , ez , nameable)) rw[])
          (sw-l (_ , es (es ez) , nameable) sw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable))
                    (wf-var (_ , ez , nameable))) ⊢$)
          ⊢Wd-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  -- the crossing argument, re-typed INSIDE, by ⊢rename at the weakening.
  ⊢Wd-in : (masked (bind (` 0)) ∷ Δd) ∣ [] ⊢ wkᴹ 1 Wd ⦂ (` 1 ⇒ ` 1)
  ⊢Wd-in = ⊢rename Ren-suc suc-inj ⊢Wd
  ⊢Wd-crossed : interior Θ2 Δd ∣ []
                  ⊢ wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫
                  ⦂ (` 0 ⇒ ` 0)
  ⊢Wd-crossed =
    env (mw rw[]
            (sw-l (_ , ez , nameable)
                  (sw-u (_ , es (es (es ez)) , locked) sw[])))
        ⊢Wd-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , nameable))
              (wf-var (_ , ez , nameable)))

-- ── n1b (the break, minimized) ─────────────────────────────────────────
-- The chain X:=Y over a Λ-bound Y, with the ambient's third slot and the
-- rep-carrying conceal both removed.

Δ1b : Ctxᵗ
Δ1b = unmasked (bind (` 0)) ∷ unmasked abst ∷ []

Θ1b : CtxMorph
Θ1b = morph ((` 0) ∷ []) (lock 1 ∷ [])

_ : interior Θ1b Δ1b
      ≡ unmasked (bind (` 0)) ∷ unmasked (bind (` 0)) ∷ masked abst ∷ []
_ = refl

V1b W1b : Term
V1b = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
W1b = (ƛ (` 1) ∙ (` 0)) ⟪ morph [] (lock 0 ∷ []) , unseal 0 ↦ seal 0 ⟫

cΘ1b : Conv
cΘ1b = (unseal 0 ↦ seal 0) ↦ id `ℕ

⊢W1b : Δ1b ∣ [] ⊢ W1b ⦂ (` 0 ⇒ ` 0)
⊢W1b = env (mw rw[] (sw-l (_ , ez , nameable) sw[]))
           (⊢ƛ (wf-var (_ , es ez , nameable)) (⊢` here))
           (conv-fun (conv-unseal ez) (conv-seal ez))
           (wf-⇒ (wf-var (_ , ez , nameable))
                 (wf-var (_ , ez , nameable)))

⊢Fn1b : Δ1b ∣ [] ⊢ V1b ⟪ Θ1b , cΘ1b ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fn1b = env (mw (rw-b (wf-var (_ , ez , nameable)) rw[])
                (sw-l (_ , es ez , nameable) sw[]))
            (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable))
                      (wf-var (_ , ez , nameable))) ⊢$)
            (conv-fun (conv-fun (conv-unseal ez) (conv-seal ez))
                      (conv-id base-ℕ))
            (wf-⇒ (wf-⇒ (wf-var (_ , ez , nameable))
                        (wf-var (_ , ez , nameable))) wf-ℕ)

⊢Redex1b : Δ1b ∣ [] ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b ⦂ `ℕ
⊢Redex1b = ⊢· ⊢Fn1b ⊢W1b

_ : dual Θ1b ≡ morph [] (lock 0 ∷ unlock 2 ∷ [])
_ = refl

-- the repointing again: nothing dropped, nothing demoted …
_ : interior (dual Θ1b) (interior Θ1b Δ1b) ≡ masked (bind (` 0)) ∷ Δ1b
_ = refl

-- … and the crossing value's licence, re-based one slot out, is STILL A
-- LIVE BINDER.
_ : (masked (bind (` 0)) ∷ Δ1b) ∋ 1 := ` 2
_ = es ez

peel-1b : Δ1b ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b
            -→ (V1b · (wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫))
                 ⟪ Θ1b , id `ℕ ⟫
peel-1b = Peel V-ƛ (V-⟪⟫ V-ƛ I-fun)

⊢contractum1b :
  Δ1b ∣ [] ⊢ (V1b · (wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫))
               ⟪ Θ1b , id `ℕ ⟫ ⦂ `ℕ
⊢contractum1b =
  env (mw (rw-b (wf-var (_ , ez , nameable)) rw[])
          (sw-l (_ , es ez , nameable) sw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable))
                    (wf-var (_ , ez , nameable))) ⊢$)
          ⊢W1b-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  ⊢W1b-in : (masked (bind (` 0)) ∷ Δ1b) ∣ [] ⊢ wkᴹ 1 W1b ⦂ (` 1 ⇒ ` 1)
  ⊢W1b-in = ⊢rename Ren-suc suc-inj ⊢W1b
  ⊢W1b-crossed : interior Θ1b Δ1b ∣ []
                   ⊢ wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫
                   ⦂ (` 0 ⇒ ` 0)
  ⊢W1b-crossed =
    env (mw rw[]
            (sw-l (_ , ez , nameable)
                  (sw-u (_ , es (es ez) , locked) sw[])))
        ⊢W1b-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , nameable)) (wf-var (_ , ez , nameable)))

-- ── n4 (the x-alias break) ─────────────────────────────────────────────
-- There is no x-entry and no rep-less reveal to alias: a conceal cites a
-- binder, full stop.  The n4 configuration becomes an ordinary binder +
-- alias.

Δ4 : Ctxᵗ
Δ4 = masked (bind `ℕ) ∷ []          -- a slot masked by an enclosing boundary

Θ4 : CtxMorph                        -- re-expose it
Θ4 = morph [] (unlock 0 ∷ [])

_ : interior Θ4 Δ4 ≡ unmasked (bind `ℕ) ∷ []
_ = refl

-- the alias RESTORES NAMEABILITY, and with it the binder's knowledge — the
-- fact `demote-x-always` denied.  It invents nothing: the rep `ℕ` was
-- already sitting in the masked entry.
_ : interior Θ4 Δ4 ∋ 0 := `ℕ
_ = ez

-- ── E★′ (the shape-IV survivor) ────────────────────────────────────────

Γ★ : Ctxᵗ
Γ★ = unmasked abst ∷ unmasked (bind `ℕ) ∷ []

Θ★ : CtxMorph
Θ★ = morph ((` 0) ∷ []) (lock 1 ∷ [])

_ : interior Θ★ Γ★
      ≡ unmasked (bind (` 0)) ∷ unmasked abst ∷ masked (bind `ℕ) ∷ []
_ = refl

_ : dual Θ★ ≡ morph [] (lock 0 ∷ unlock 2 ∷ [])
_ = refl

_ : interior (dual Θ★) (interior Θ★ Γ★) ≡ masked (bind (` 0)) ∷ Γ★
_ = refl

------------------------------------------------------------------------
-- §6  THE FIRST END-TO-END RUN — a CLOSED, PLAIN source program
------------------------------------------------------------------------

-- Every earlier section starts from a term that already carries boundaries.
-- This one starts from ORDINARY SYSTEM F: no wrapper, no context morphism,
-- no conversion, typed at the EMPTY type context and the EMPTY term
-- context.  Every boundary below is MINTED BY REDUCTION, and the run ends
-- at a value.
--
--   P₀ = (ΛX. λx:X. x) [ℕ] · 7   ↦*   7
--
-- The five rules it exercises, in order:
--   TyBeta  — the boundary is BORN, at the binder X := ℕ
--   Peel    — the crossing: the argument 7 acquires the DUAL
--   Beta    — the ordinary β step, i.e. ⊢subst (strong.TermSubst)
--   CancelR — the seal/unseal pair, minted by TyBeta and Peel, annihilates
--   Drop$   — the surviving base conversion over a numeral is dropped

polyid : Term
polyid = Λ (ƛ (` 0) ∙ (` 0))

⊢polyid : [] ∣ [] ⊢ polyid ⦂ `∀ (` 0 ⇒ ` 0)
⊢polyid = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) (⊢` here))

P₀ : Term
P₀ = (polyid ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢P₀ : [] ∣ [] ⊢ P₀ ⦂ `ℕ
⊢P₀ = ⊢· (⊢·[] ⊢polyid wf-ℕ) ⊢$

-- ── STEP 1 — TYBETA.  The ∀-elimination mints THE BINDER of the event and
-- derives its conversion from the body type: `reveal 0 (X⇒X)` is the
-- ↦-pair that seals on the domain and unseals on the codomain.

_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

P₁ : Term
P₁ = ((ƛ (` 0) ∙ (` 0)) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)

step₁ : [] ⊢ P₀ -→ P₁
step₁ = ξ-·-l (TyBeta V-ƛ)

⊢fn₁ : [] ∣ [] ⊢ (ƛ (` 0) ∙ (` 0)) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫
         ⦂ (`ℕ ⇒ `ℕ)
⊢fn₁ = env (mw (rw-b wf-ℕ rw[]) sw[])
           (⊢ƛ (wf-var (unmasked (bind `ℕ) , ez , nameable)) (⊢` here))
           (conv-fun (conv-seal ez) (conv-unseal ez))
           (wf-⇒ wf-ℕ wf-ℕ)

⊢P₁ : [] ∣ [] ⊢ P₁ ⦂ `ℕ
⊢P₁ = ⊢· ⊢fn₁ ⊢$

-- ── STEP 2 — PEEL.  The application is pushed one layer in and the argument
-- acquires the DUAL: one `lock` per binder of the crossed boundary and
-- nothing else.  Its conversion is `s`, the ↦'s domain component,
-- transplanted VERBATIM — the dual's CONVERSION CONTEXT IS the crossed
-- boundary's.

_ : dual (morph (`ℕ ∷ []) []) ≡ morph [] (lock 0 ∷ [])
_ = refl

_ : convCtx (dual (morph (`ℕ ∷ []) [])) (interior (morph (`ℕ ∷ []) []) [])
      ≡ convCtx (morph (`ℕ ∷ []) []) []
_ = refl

P₂ : Term
P₂ = ((ƛ (` 0) ∙ (` 0)) · (($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫))
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

step₂ : [] ⊢ P₁ -→ P₂
step₂ = Peel V-ƛ V-$

-- the crossing argument, typed INSIDE: 7 is sealed at the new binder, so the
-- interior sees it at the abstract name X.
⊢arg₂ : (unmasked (bind `ℕ) ∷ []) ∣ []
          ⊢ ($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫ ⦂ ` 0
⊢arg₂ = env (mw rw[] (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[])) ⊢$
            (conv-seal ez) (wf-var (unmasked (bind `ℕ) , ez , nameable))

⊢P₂ : [] ∣ [] ⊢ P₂ ⦂ `ℕ
⊢P₂ = env (mw (rw-b wf-ℕ rw[]) sw[])
          (⊢· (⊢ƛ (wf-var (unmasked (bind `ℕ) , ez , nameable)) (⊢` here))
               ⊢arg₂)
          (conv-unseal ez) wf-ℕ

-- ── STEP 3 — BETA, under the boundary.  This is the step ⊢subst pays for:
-- the contractum's typing below is `preserve-Beta` (strong.TermSubst),
-- i.e. ⊢subst applied to the interior redex.

P₃ : Term
P₃ = (($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫)
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

-- NO Λ IS CROSSED HERE (the body is the bare variable), so frame-exact
-- Beta mints no wrapper and the contractum is the argument itself.
_ : (` 0) [ ($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫ ∶ ` 0 ]ᵐ
      ≡ ($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫
_ = refl

step₃ : [] ⊢ P₂ -→ P₃
step₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

⊢P₃-in : (unmasked (bind `ℕ) ∷ []) ∣ []
           ⊢ ($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫ ⦂ ` 0
⊢P₃-in = preserve-Beta
           (⊢· (⊢ƛ (wf-var (unmasked (bind `ℕ) , ez , nameable)) (⊢` here))
                ⊢arg₂)

⊢P₃ : [] ∣ [] ⊢ P₃ ⦂ `ℕ
⊢P₃ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢P₃-in (conv-unseal ez) wf-ℕ

-- ── STEP 4 — CANCEL.  The seal minted by Peel and the unseal minted by
-- TyBeta are now adjacent and cite THE SAME ENTRY, so the type match is
-- definitional; each conversion becomes the identity at the LOOKED-UP
-- rep, and BOTH FRAMES STAY (the repaired rule) — so the crossing's own
-- `lock 0` survives as a transparent layer, to be dropped in its own
-- right.

P₄ : Term
P₄ = (($ 7) ⟪ morph [] (lock 0 ∷ []) , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

step₄ : [] ⊢ P₃ -→ P₄
step₄ = CancelR V-$ ez

⊢P₄-in : (unmasked (bind `ℕ) ∷ []) ∣ []
           ⊢ ($ 7) ⟪ morph [] (lock 0 ∷ []) , id `ℕ ⟫ ⦂ `ℕ
⊢P₄-in = env (mw rw[] (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[]))
              ⊢$ (conv-id base-ℕ) wf-ℕ

⊢P₄ : [] ∣ [] ⊢ P₄ ⦂ `ℕ
⊢P₄ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢P₄-in (conv-id base-ℕ) wf-ℕ

-- ── STEPS 5, 6 — the two base conversions over the numeral, and the run.

P₅ : Term
P₅ = ($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

step₅ : [] ⊢ P₄ -→ P₅
step₅ = ξ-⟪⟫ (Drop$ base-ℕ)

⊢P₅ : [] ∣ [] ⊢ P₅ ⦂ `ℕ
⊢P₅ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

step₆ : [] ⊢ P₅ -→ $ 7
step₆ = Drop$ base-ℕ

run-P₀ : [] ⊢ P₀ -→* $ 7
run-P₀ = step₁ then step₂ then step₃ then step₄ then step₅ then step₆
    then done

val-P₀ : Value ($ 7)
val-P₀ = V-$

-- ── AND THE GENERATED RUN AGREES ───────────────────────────────────────
--
-- `eval` (strong.Eval) is PROGRESS iterated under PRESERVATION, so the
-- six steps above are not merely A run but THE run the machine takes.
-- The hand-composed chain stays (it is what a reader reads); this line
-- is what checks it.
--
-- RENDERED (scripts/render_term.sh 'showTrace 0 (eval 6 ⊢P₀)'):
--
--   ((ΛX. (λx:X. x)) [ℕ] · 7)
--     --[TyBeta]-->
--   (((λx:X. x) ⟪ ↑X:=ℕ , (seal X ↦ unseal X) ⟫) · 7)
--     --[Peel]-->
--   (((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
--     --[Beta]-->
--   ((7 ⟪ ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
--     --[CancelR]-->
--   ((7 ⟪ ↓X , id ℕ ⟫) ⟪ ↑X:=ℕ , id ℕ ⟫)
--     --[Drop$]-->
--   (7 ⟪ ↑X:=ℕ , id ℕ ⟫)
--     --[Drop$]-->
--   7
--     -- VALUE

open import strong.Eval using (evalTerms; eval-sound)

_ : evalTerms 6 ⊢P₀ ≡ P₀ ∷ P₁ ∷ P₂ ∷ P₃ ∷ P₄ ∷ P₅ ∷ ($ 7) ∷ []
_ = refl

------------------------------------------------------------------------
-- §7  Three regressions on substᵐ itself
------------------------------------------------------------------------

-- ── the Λ clause: an image crossing a Λ is SHIFTED AND WRAPPED ─────────
-- Under a Λ the term context is ⤊ Γ, so a term written over Δ must have its
-- boundary NAMES shifted before it is planted inside.  Here `seal 0` becomes
-- `seal 1` — and it must, since slot 0 inside the Λ is `abst`, where
-- `conv-seal` has no binder to cite.
--
-- FRAME-EXACT BETA ALSO WRAPS IT (2026-09-08).  Shifting alone leaves the
-- image's frame one entry LARGER than the frame it was born in — the Λ's
-- own slot — which is harmless via indices but not exact.  So the image
-- acquires THE CROSSED BINDER'S DUAL, `morph [] (lock 0 ∷ [])`, under an
-- identity conversion at its own (shifted) type, and its frame is then its
-- BIRTH frame with the Λ's slot masked.

Δₛ : Ctxᵗ
Δₛ = unmasked (bind `ℕ) ∷ []

Wₛ Nₛ : Term
Wₛ = ($ 7) ⟪ morph [] [] , seal 0 ⟫
Nₛ = Λ (` 0)

⊢Wₛ : Δₛ ∣ [] ⊢ Wₛ ⦂ ` 0
⊢Wₛ = env (mw rw[] sw[]) ⊢$ (conv-seal ez)
          (wf-var (unmasked (bind `ℕ) , ez , nameable))

⊢Nₛ : Δₛ ∣ (` 0 ∷ []) ⊢ Nₛ ⦂ `∀ (` 1)
⊢Nₛ = ⊢Λ (⊢` here)

-- BEFORE FRAME-EXACT BETA this was `Λ (($ 7) ⟪ morph [] [] , seal 1 ⟫)`:
-- the shift, and nothing recording that slot 0 is not the image's.
_ : Nₛ [ Wₛ ∶ ` 0 ]ᵐ
      ≡ Λ ((($ 7) ⟪ morph [] [] , seal 1 ⟫)
             ⟪ morph [] (lock 0 ∷ []) , id (` 1) ⟫)
_ = refl

-- THE FRAME IDENTITY THAT MAKES IT EXACT — definitional, at this Δ: the
-- image is read at Δₛ itself, with the crossed Λ's slot masked.  (The
-- shifted `seal 1` names Δₛ's binder, one slot further out, exactly as
-- before.)
_ : interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δₛ) ≡ masked abst ∷ Δₛ
_ = refl

⊢Nₛ[Wₛ] : Δₛ ∣ [] ⊢ Nₛ [ Wₛ ∶ ` 0 ]ᵐ ⦂ `∀ (` 1)
⊢Nₛ[Wₛ] = ⊢subst (wf-var (unmasked (bind `ℕ) , ez , nameable)) ⊢Nₛ ⊢Wₛ

-- ── the ƛ clause: the ƛ-bound slot is PROTECTED, the image is not ───────
-- `extᴵ` plants `ivar zero` at the ƛ-bound slot and weakens the rest by
-- one term variable; a VALUE image is term-closed (`⊢ival`), so the
-- weakening leaves it alone and the substituted identity keeps naming its
-- own argument.  NO Λ IS CROSSED, so no wrapper is minted.

_ : (ƛ `ℕ ∙ (` 1)) [ ƛ `ℕ ∙ (` 0) ∶ `ℕ ⇒ `ℕ ]ᵐ ≡ ƛ `ℕ ∙ (ƛ `ℕ ∙ (` 0))
_ = refl

_ : [] ∣ [] ⊢ (ƛ `ℕ ∙ (` 1)) [ ƛ `ℕ ∙ (` 0) ∶ `ℕ ⇒ `ℕ ]ᵐ
      ⦂ (`ℕ ⇒ (`ℕ ⇒ `ℕ))
_ = ⊢subst (wf-⇒ wf-ℕ wf-ℕ) (⊢ƛ wf-ℕ (⊢` (there here))) (⊢ƛ wf-ℕ (⊢` here))

-- ── WHAT THE WRAPPER COSTS AT A BASE TYPE ──────────────────────────────
-- `mkId` is INERT at a variable, a function type and a `` `∀ `` — there
-- the wrapper is a VALUE (`V-⟪⟫ … I-idv` / `I-fun` / `I-all`).  At a BASE
-- type it is `id ℕ`, which is ACTIVE, so the wrapper is NOT a value and
-- `Drop$` finishes it in one step.  That is the whole price of
-- frame-exactness at a base-typed argument, and progress is not disturbed
-- by it: a closed value at `ℕ` is a numeral (no inert conversion targets a
-- base type), so `Drop$` always applies.

Bᵍ Cᵍ : Term
Bᵍ = (ƛ `ℕ ∙ (Λ (` 0))) · ($ 7)
Cᵍ = (Λ (` 0)) [ $ 7 ∶ `ℕ ]ᵐ

_ : Cᵍ ≡ Λ (($ 7) ⟪ morph [] (lock 0 ∷ []) , id `ℕ ⟫)
_ = refl

⊢Bᵍ : [] ∣ [] ⊢ Bᵍ ⦂ `∀ `ℕ
⊢Bᵍ = ⊢· (⊢ƛ wf-ℕ (⊢Λ (⊢` here))) ⊢$

-- neither the redex's contractum nor `Λ ($ 7)` is reached by one step:
-- the run is Beta then Drop$, and `Λ ($ 7)` is the value.
_ : evalTerms 2 ⊢Bᵍ ≡ Bᵍ ∷ Cᵍ ∷ Λ ($ 7) ∷ []
_ = refl

val-Λ$ : Value (Λ ($ 7))
val-Λ$ = V-Λ V-$

-- the wrapper itself is NOT a value, and this is the step it takes
¬val-Cᵍ-in : ¬ Value (($ 7) ⟪ morph [] (lock 0 ∷ []) , id `ℕ ⟫)
¬val-Cᵍ-in (V-⟪⟫ _ ())

stepᵍ : [] ⊢ Cᵍ -→ Λ ($ 7)
stepᵍ = ξ-Λ (Drop$ base-ℕ)

------------------------------------------------------------------------
-- §8  PROGRESS, on the run of §6
------------------------------------------------------------------------

-- The five redex states of `run-P₀`, each handed to `progress`: at every
-- one of them the theorem answers "it steps", and `det` (strong.Reduction)
-- identifies the step it found with the step the run actually takes.  So
-- progress is not merely non-vacuous here — it recomputes §6's trace.
--
-- Read the imports as part of the section: §8 is the only part of this
-- file that depends on the theorem.

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import strong.Progress using (progress)

progress-P₀ : Σ[ M′ ∈ Term ] (([] ⊢ P₀ -→ M′) × (M′ ≡ P₁))
progress-P₀ with progress ⊢P₀
progress-P₀ | inj₁ ()
progress-P₀ | inj₂ (M′ , st) = M′ , st , det st step₁

progress-P₁ : Σ[ M′ ∈ Term ] (([] ⊢ P₁ -→ M′) × (M′ ≡ P₂))
progress-P₁ with progress ⊢P₁
progress-P₁ | inj₁ ()
progress-P₁ | inj₂ (M′ , st) = M′ , st , det st step₂

-- P₂ is a boundary over a REDEX, so progress recurses into the interior
-- and comes back out through ξ-⟪⟫.
progress-P₂ : Σ[ M′ ∈ Term ] (([] ⊢ P₂ -→ M′) × (M′ ≡ P₃))
progress-P₂ with progress ⊢P₂
progress-P₂ | inj₁ (V-⟪⟫ () _)
progress-P₂ | inj₂ (M′ , st) = M′ , st , det st step₃

-- P₃ is the CANCEL state: the interior is a value, the conversion is the
-- ACTIVE `unseal 0`, and canon-var picks out the concealing layer under
-- it.
progress-P₃ : Σ[ M′ ∈ Term ] (([] ⊢ P₃ -→ M′) × (M′ ≡ P₄))
progress-P₃ with progress ⊢P₃
progress-P₃ | inj₁ (V-⟪⟫ _ ())
progress-P₃ | inj₂ (M′ , st) = M′ , st , det st step₄

-- P₄ is a DROP$ state UNDER a boundary: the interior transparent layer
-- goes first, by ξ-⟪⟫.
progress-P₄ : Σ[ M′ ∈ Term ] (([] ⊢ P₄ -→ M′) × (M′ ≡ P₅))
progress-P₄ with progress ⊢P₄
progress-P₄ | inj₁ (V-⟪⟫ _ ())
progress-P₄ | inj₂ (M′ , st) = M′ , st , det st step₅

-- P₅ is the last DROP$ state: the conversion is the ACTIVE `id `ℕ` and
-- canon-base says the interior value is a numeral.
progress-P₅ : Σ[ M′ ∈ Term ] (([] ⊢ P₅ -→ M′) × (M′ ≡ $ 7))
progress-P₅ with progress ⊢P₅
progress-P₅ | inj₁ (V-⟪⟫ _ ())
progress-P₅ | inj₂ (M′ , st) = M′ , st , det st step₆

-- and the endpoint: at `$ 7` progress answers VALUE, not step.
progress-end : Value ($ 7)
progress-end with progress {Δ = []} {A = `ℕ} (⊢$ {Γ = []} {n = 7})
progress-end | inj₁ v        = v
progress-end | inj₂ (_ , st) = ⊥-elim (value-¬step V-$ st)

open import strong.Preservation
  using (preservation-TyBeta; preservation-Beta; preservation-Drop$;
         preservation; preservation*)

------------------------------------------------------------------------
-- §9  PRESERVATION ALONG run-P₀
------------------------------------------------------------------------

-- Each ⊢Pᵢ₊₁ from ⊢Pᵢ, by the preservation case of the rule that fired
-- — TyBeta, Beta and Drop$ below, one per step, as they were written
-- while Peel and CancelR were still open.
--
-- BOTH ARE NOW THEOREMS, so the whole run also goes in ONE LINE.
run-P₀-pres : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
run-P₀-pres = preservation* ⊢P₀ run-P₀

-- STEP 1 — TyBeta, under ξ-·-l.
⊢P₁-pres : [] ∣ [] ⊢ P₁ ⦂ `ℕ
⊢P₁-pres = ⊢· (preservation-TyBeta (⊢·[] ⊢polyid wf-ℕ)) ⊢$

-- STEP 3 — Beta, under ξ-⟪⟫: the ξ case rebuilds the same `env` around
-- the stepped interior, and that interior is `preservation-Beta`
-- (⊢P₃-in above).
⊢P₃-pres : [] ∣ [] ⊢ P₃ ⦂ `ℕ
⊢P₃-pres = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢P₃-in (conv-unseal ez) wf-ℕ

-- STEP 6 — Drop$ (step 5 is the same rule, under ξ-⟪⟫).
⊢P₆-pres : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
⊢P₆-pres = preservation-Drop$ base-ℕ ⊢P₅

------------------------------------------------------------------------
-- §11  IDPUSH FROM A CLOSED, PLAIN SOURCE
------------------------------------------------------------------------

-- Jeremy, 2026-09-05: "do we have any traces that land on the IdPush case
-- at all, regardless of what it's under?"  Until §11 the answer was NO:
-- T₆/T₈/Tᵣ/Tₘ (§§1–4) and the ¬IdPushCase witness (proof/PreserveObstruct
-- §4) are all HAND-BUILT terms that already carry boundaries.  This
-- section answers with runs that start from ORDINARY SYSTEM F — no
-- wrapper, no context morphism, no conversion, empty type context, empty
-- term context — and LAND ON IDPUSH.
--
-- THE SHAPE THAT MAKES AN ID-LAYER.  TyBeta's minted conversion is
-- `reveal 0 B`, and `reveal 0 (` k)` is `id (` k)` for every k ≠ 0.
-- So an id-layer is born exactly when a type abstraction is instantiated
-- at a body type that is an OUTER type variable — a VACUOUS `Λ`, whose
-- body mentions a variable bound further out.  The smallest source with
-- that shape is the supervisor's candidate:
--
--   Q = ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [ℕ]) · 7
--
-- de Bruijn: under Z the outer Y is slot 1, so `ΛZ. x` has type `∀ (` 1)
-- and the inner TyBeta mints `reveal 0 (` 1) = id (` 1)` — an identity
-- layer around x's value, sitting inside the OUTER package's revealing
-- wrapper.  That two-wrapper stack IS the IdPush redex.

open import strong.proof.PeelDual using (preserve-Peel)

-- ── the source ─────────────────────────────────────────────────────────

Qvac Qbody Qfun Q₀ : Term
Qvac  = Λ (` 0)                          -- ΛZ. x
Qbody = Qvac ·[ ` 1 , `ℕ ]               -- (ΛZ. x) [ℕ]
Qfun  = Λ (ƛ (` 0) ∙ Qbody)              -- ΛY. λx:Y. (ΛZ. x) [ℕ]
Q₀    = (Qfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Qbody : (unmasked abst ∷ []) ∣ (` 0 ∷ []) ⊢ Qbody ⦂ ` 0
⊢Qbody = ⊢·[] (⊢Λ (⊢` here)) wf-ℕ

⊢Qfun : [] ∣ [] ⊢ Qfun ⦂ `∀ (` 0 ⇒ ` 0)
⊢Qfun = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) ⊢Qbody)

⊢Q₀ : [] ∣ [] ⊢ Q₀ ⦂ `ℕ
⊢Q₀ = ⊢· (⊢·[] ⊢Qfun wf-ℕ) ⊢$

-- The two type contexts the run works in: the outer boundary's interior,
-- and the id-layer's interior.
QΔ₁ QΞ₂ : Ctxᵗ
QΔ₁ = unmasked (bind `ℕ) ∷ []
QΞ₂ = unmasked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ []

_ : interior (morph (`ℕ ∷ []) []) [] ≡ QΔ₁
_ = refl

_ : interior (morph (`ℕ ∷ []) []) QΔ₁ ≡ QΞ₂
_ = refl

-- ── STEP 1 — TYBETA (outer).  The binder Y := ℕ is minted.

_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

Q₁ : Term
Q₁ = ((ƛ (` 0) ∙ Qbody) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)

qstep₁ : [] ⊢ Q₀ -→ Q₁
qstep₁ = ξ-·-l (TyBeta V-ƛ)

⊢Qbody₁ : QΔ₁ ∣ (` 0 ∷ []) ⊢ Qbody ⦂ ` 0
⊢Qbody₁ = ⊢·[] (⊢Λ (⊢` here)) wf-ℕ

⊢Q₁ : [] ∣ [] ⊢ Q₁ ⦂ `ℕ
⊢Q₁ = ⊢· (preservation-TyBeta (⊢·[] ⊢Qfun wf-ℕ)) ⊢$

-- ── STEP 2 — PEEL.  7 crosses; `dual (bind ℕ ∷ []) = lock 0 ∷ []`, so
-- the argument acquires a concealing wrapper that hides the new binder.

_ : dual (morph (`ℕ ∷ []) []) ≡ morph [] (lock 0 ∷ [])
_ = refl

QS₇ : Term
QS₇ = ($ 7) ⟪ morph [] (lock 0 ∷ []) , seal 0 ⟫

Q₂ : Term
Q₂ = ((ƛ (` 0) ∙ Qbody) · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

qstep₂ : [] ⊢ Q₁ -→ Q₂
qstep₂ = Peel V-ƛ V-$

⊢QS₇ : QΔ₁ ∣ [] ⊢ QS₇ ⦂ ` 0
⊢QS₇ = env (mw rw[] (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[])) ⊢$
            (conv-seal ez) (wf-var (unmasked (bind `ℕ) , ez , nameable))

⊢Q₂ : [] ∣ [] ⊢ Q₂ ⦂ `ℕ
⊢Q₂ = preserve-Peel V-ƛ V-$ ⊢Q₁

-- ── STEP 3 — BETA, under ξ-⟪⟫, NOW FRAME-EXACT (2026-09-08).  `substᵐ`'s
-- Λ clause does two things to the sealed 7 as it crosses ΛZ: it SHIFTS it
-- (the seal NAME moves, seal 0 ↦ seal 1, and so does the lock) and it
-- WRAPS it in ΛZ'S DUAL `morph [] (lock 0 ∷ [])`, under the identity
-- conversion at the argument's own (shifted) type `` ` 1 ``.
--
-- BEFORE FRAME-EXACT BETA the contractum was `(Λ QS₇⇑) ·[ ` 1 , `ℕ ]` —
-- the shift alone — and the run below was TWO STEPS SHORTER (9, not 11):
-- the new transparent layer is pushed in by a SECOND IdPush (step 6) and
-- finished by a FOURTH Drop$.

QS₇⇑ QS₇↑ : Term
QS₇⇑ = ($ 7) ⟪ morph [] (lock 1 ∷ []) , seal 1 ⟫
QS₇↑ = QS₇⇑ ⟪ morph [] (lock 0 ∷ []) , id (` 1) ⟫

_ : ⇑ᴹ QS₇ ≡ QS₇⇑
_ = refl

_ : Qbody [ QS₇ ∶ ` 0 ]ᵐ ≡ (Λ QS₇↑) ·[ ` 1 , `ℕ ]
_ = refl

-- THE FRAME IDENTITY that makes it exact (strong.TermSubst §5b): inside
-- the new wrapper the argument is read at QΞ₂ with ΛZ's slot MASKED —
-- that is QΔ₁, its BIRTH frame, one binder in.  It gained nothing by
-- crossing.
QΞ₂ᵏ : Ctxᵗ
QΞ₂ᵏ = masked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ []

_ : interior (morph [] (lock 0 ∷ [])) QΞ₂ ≡ QΞ₂ᵏ
_ = refl

Q₃ : Term
Q₃ = ((Λ QS₇↑) ·[ ` 1 , `ℕ ]) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

qstep₃ : [] ⊢ Q₂ -→ Q₃
qstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

⊢Q₃-in : QΔ₁ ∣ [] ⊢ (Λ QS₇↑) ·[ ` 1 , `ℕ ] ⦂ ` 0
⊢Q₃-in = preservation-Beta
           (⊢· (⊢ƛ (wf-var (unmasked (bind `ℕ) , ez , nameable)) ⊢Qbody₁)
                ⊢QS₇)

⊢Q₃ : [] ∣ [] ⊢ Q₃ ⦂ `ℕ
⊢Q₃ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢Q₃-in (conv-unseal ez) wf-ℕ

-- THE NEW LAYER, TYPED BY HAND: this is `⊢crossΛ` (strong.TermSubst §6)
-- on the ground — the `lock 0` is legal because ΛZ's own slot is nameable
-- (`sw-l`), the interior is the argument at QΞ₂ᵏ, and the conversion is
-- `conv-idv` at the argument's type, read OUTSIDE the lock.

⊢QS₇⇑ : QΞ₂ᵏ ∣ [] ⊢ QS₇⇑ ⦂ ` 1
⊢QS₇⇑ = env (mw rw[] (sw-l (unmasked (bind `ℕ) , es ez , nameable) sw[])) ⊢$
             (conv-seal (es ez))
             (wf-var (unmasked (bind `ℕ) , es ez , nameable))

⊢QS₇↑ : QΞ₂ ∣ [] ⊢ QS₇↑ ⦂ ` 1
⊢QS₇↑ = env (mw rw[] (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[]))
             ⊢QS₇⇑ (conv-idv (unmasked (bind `ℕ) , es ez , nameable))
             (wf-var (unmasked (bind `ℕ) , es ez , nameable))

-- ── STEP 4 — TYBETA (inner), under ξ-⟪⟫.  THE ID-LAYER IS BORN: the body
-- type is the OUTER variable, so the minted conversion is an identity.
-- The value it fires on is now the WRAPPED argument, so its `Value`
-- witness gains one `V-⟪⟫` at the inert `id (` 1)`.

_ : reveal 0 (` 1) ≡ id (` 1)
_ = refl

Q₄ : Term
Q₄ = (QS₇↑ ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫)
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

qstep₄ : [] ⊢ Q₃ -→ Q₄
qstep₄ = ξ-⟪⟫ (TyBeta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv))

⊢Q₄-in : QΔ₁ ∣ [] ⊢ QS₇↑ ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫ ⦂ ` 0
⊢Q₄-in = preservation-TyBeta ⊢Q₃-in

⊢Q₄ : [] ∣ [] ⊢ Q₄ ⦂ `ℕ
⊢Q₄ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢Q₄-in (conv-unseal ez) wf-ℕ

-- ── STEP 5 — THE IDPUSH REDEX, AND IDPUSH.  Θ₁ = Θ₂ = `bind ℕ ∷ []`,
-- X = 1, Y = 0, A = ℕ (the looked-up rep).  Both frames are untouched;
-- only the two conversions swap.
--
-- FROM HERE ON the intermediate typings are taken from PRESERVATION
-- itself (`preservation ⊢Qᵢ qstepᵢ₊₁`) rather than rebuilt by hand: the
-- extra transparent layer makes the trees taller without making them say
-- anything new, and the hand-built `env` derivations that mattered are
-- the two above.

Q₅ : Term
Q₅ = (QS₇↑ ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫)
       ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

qstep₅ : [] ⊢ Q₄ -→ Q₅
qstep₅ = IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) ez

⊢Q₅ : [] ∣ [] ⊢ Q₅ ⦂ `ℕ
⊢Q₅ = preservation ⊢Q₄ qstep₅

-- ── STEP 6 — IDPUSH AGAIN, under ξ-⟪⟫: THE STEP FRAME-EXACT BETA ADDS.
-- The layer the substitution minted is itself an `id (` X)` sitting under
-- an ACTIVE `unseal`, so the same rule fires on it — Θ₁ is ΛZ's dual
-- `morph [] (lock 0 ∷ [])`, X = Y = 1, A = ℕ.

Q₆ : Term
Q₆ = ((QS₇⇑ ⟪ morph [] (lock 0 ∷ []) , unseal 1 ⟫)
        ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

qstep₆ : [] ⊢ Q₅ -→ Q₆
qstep₆ = ξ-⟪⟫ (IdPush (V-⟪⟫ V-$ I-seal) (es ez))

⊢Q₆ : [] ∣ [] ⊢ Q₆ ⦂ `ℕ
⊢Q₆ = preservation ⊢Q₅ qstep₆

-- ── STEP 7 — CANCEL, at depth 2.  The seal minted by Peel and the unseal
-- IdPush moved inwards are now adjacent.  BOTH FRAMES STAY, and the scope
-- move sends ΛZ's dual `lock 0` into the inner frame's TAIL while the
-- residue keeps it REWOUND (`unlock 0 ∷ lock 0`).

Q₇ Q₈ Q₉ Q₁₀ : Term
Q₇ = ((((($ 7) ⟪ morph [] (lock 1 ∷ lock 0 ∷ []) , id `ℕ ⟫)
           ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
         ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
Q₈ = ((($ 7) ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
        ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
Q₉ = (($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
Q₁₀ = ($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

qstep₇ : [] ⊢ Q₆ -→ Q₇
qstep₇ = ξ-⟪⟫ (ξ-⟪⟫ (CancelR V-$ (es ez)))

⊢Q₇ : [] ∣ [] ⊢ Q₇ ⦂ `ℕ
⊢Q₇ = preservation ⊢Q₆ qstep₇

-- ── STEPS 8–11 — the FOUR base conversions over the numeral (three,
-- before frame-exact Beta).

qstep₈ : [] ⊢ Q₇ -→ Q₈
qstep₈ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))

⊢Q₈ : [] ∣ [] ⊢ Q₈ ⦂ `ℕ
⊢Q₈ = preservation ⊢Q₇ qstep₈

qstep₉ : [] ⊢ Q₈ -→ Q₉
qstep₉ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

⊢Q₉ : [] ∣ [] ⊢ Q₉ ⦂ `ℕ
⊢Q₉ = preservation ⊢Q₈ qstep₉

qstep₁₀ : [] ⊢ Q₉ -→ Q₁₀
qstep₁₀ = ξ-⟪⟫ (Drop$ base-ℕ)

⊢Q₁₀ : [] ∣ [] ⊢ Q₁₀ ⦂ `ℕ
⊢Q₁₀ = preservation ⊢Q₉ qstep₁₀

qstep₁₁ : [] ⊢ Q₁₀ -→ $ 7
qstep₁₁ = Drop$ base-ℕ

⊢Q₁₁ : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
⊢Q₁₁ = preservation-Drop$ base-ℕ ⊢Q₁₀

run-Q₀ : [] ⊢ Q₀ -→* $ 7
run-Q₀ = qstep₁ then qstep₂ then qstep₃ then qstep₄ then qstep₅
    then qstep₆ then qstep₇ then qstep₈ then qstep₉ then qstep₁₀
    then qstep₁₁ then done

-- … and the generated run agrees, both IdPush states and all.
_ : evalTerms 11 ⊢Q₀
      ≡ Q₀ ∷ Q₁ ∷ Q₂ ∷ Q₃ ∷ Q₄ ∷ Q₅ ∷ Q₆ ∷ Q₇ ∷ Q₈ ∷ Q₉ ∷ Q₁₀ ∷ ($ 7) ∷ []
_ = refl

-- ── DETERMINISM PINS.  Each state has exactly ONE successor, so the run
-- above is THE run: nothing else can fire at Q₄, in particular.

qdet₁ : ∀ {M′} → [] ⊢ Q₀ -→ M′ → M′ ≡ Q₁
qdet₁ st = det st qstep₁

qdet₂ : ∀ {M′} → [] ⊢ Q₁ -→ M′ → M′ ≡ Q₂
qdet₂ st = det st qstep₂

qdet₃ : ∀ {M′} → [] ⊢ Q₂ -→ M′ → M′ ≡ Q₃
qdet₃ st = det st qstep₃

qdet₄ : ∀ {M′} → [] ⊢ Q₃ -→ M′ → M′ ≡ Q₄
qdet₄ st = det st qstep₄

qdet₅ : ∀ {M′} → [] ⊢ Q₄ -→ M′ → M′ ≡ Q₅
qdet₅ st = det st qstep₅

qdet₆ : ∀ {M′} → [] ⊢ Q₅ -→ M′ → M′ ≡ Q₆
qdet₆ st = det st qstep₆

qdet₇ : ∀ {M′} → [] ⊢ Q₆ -→ M′ → M′ ≡ Q₇
qdet₇ st = det st qstep₇

qdet₈ : ∀ {M′} → [] ⊢ Q₇ -→ M′ → M′ ≡ Q₈
qdet₈ st = det st qstep₈

qdet₉ : ∀ {M′} → [] ⊢ Q₈ -→ M′ → M′ ≡ Q₉
qdet₉ st = det st qstep₉

qdet₁₀ : ∀ {M′} → [] ⊢ Q₉ -→ M′ → M′ ≡ Q₁₀
qdet₁₀ st = det st qstep₁₀

qdet₁₁ : ∀ {M′} → [] ⊢ Q₁₀ -→ M′ → M′ ≡ $ 7
qdet₁₁ st = det st qstep₁₁

------------------------------------------------------------------------
-- §11a  VARIANT (iii) — IDPUSH FIRING TWICE IN ONE RUN
------------------------------------------------------------------------

-- Stacked id-layers, from stacked VACUOUS type abstractions:
--
--   D = ((ΛY. λx:Y. ((ΛZ. ((ΛW. x) [ℕ])) [ℕ])) [ℕ]) · 7
--
-- Each vacuous Λ contributes one TyBeta whose body type is an OUTER
-- variable, hence one `id (` k)` layer.  NOTE THE ORDER: the inner
-- TyBeta must fire FIRST (under ξ-Λ), because TyBeta's `Value N` premise
-- (repair (5)) refuses to fire on a `Λ` whose body is still a redex.

Dvac Dinner Dbody Dfun D₀ : Term
Dvac   = Λ (` 0)                            -- ΛW. x
Dinner = Λ (Dvac ·[ ` 2 , `ℕ ])             -- ΛZ. ((ΛW. x) [ℕ])
Dbody  = Dinner ·[ ` 1 , `ℕ ]               -- (ΛZ. …) [ℕ]
Dfun   = Λ (ƛ (` 0) ∙ Dbody)
D₀     = (Dfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Dbody : (unmasked abst ∷ []) ∣ (` 0 ∷ []) ⊢ Dbody ⦂ ` 0
⊢Dbody = ⊢·[] (⊢Λ (⊢·[] (⊢Λ (⊢` here)) wf-ℕ)) wf-ℕ

⊢Dfun : [] ∣ [] ⊢ Dfun ⦂ `∀ (` 0 ⇒ ` 0)
⊢Dfun = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) ⊢Dbody)

⊢D₀ : [] ∣ [] ⊢ D₀ ⦂ `ℕ
⊢D₀ = ⊢· (⊢·[] ⊢Dfun wf-ℕ) ⊢$

QΞ₃ : Ctxᵗ
QΞ₃ = unmasked (bind `ℕ) ∷ QΞ₂

-- FRAME-EXACT BETA (2026-09-08) plants the crossed 7 under TWO Λs, so it
-- acquires TWO dual wrappers — ΛY's `↓Y` and, outside it, ΛZ's `↓Z` —
-- each with an identity conversion at the argument's type at that depth.
-- BEFORE FRAME-EXACT BETA the planted value was the bare shifted
-- `($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫` and the run was 12 steps;
-- it is now 16 — the two extra layers are pushed in by two extra IdPush
-- steps and finished by two extra Drop$.
DS₇ : Term
DS₇ = ((($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
          ⟪ morph [] (lock 1 ∷ []) , id (` 2) ⟫)
        ⟪ morph [] (lock 0 ∷ []) , id (` 2) ⟫

val-DS₇ : Value DS₇
val-DS₇ = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) I-idv

D₁ D₂ D₃ D₄ D₅ D₆ D₇ D₈ : Term
D₁  = ((ƛ (` 0) ∙ Dbody) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
D₂  = ((ƛ (` 0) ∙ Dbody) · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
D₃  = ((Λ ((Λ DS₇) ·[ ` 2 , `ℕ ])) ·[ ` 1 , `ℕ ])
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
D₄  = ((Λ (DS₇ ⟪ morph (`ℕ ∷ []) [] , id (` 2) ⟫)) ·[ ` 1 , `ℕ ])
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
D₅  = ((DS₇ ⟪ morph (`ℕ ∷ []) [] , id (` 2) ⟫)
         ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
D₆  = ((DS₇ ⟪ morph (`ℕ ∷ []) [] , id (` 2) ⟫)
         ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫)
        ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₇  = ((DS₇ ⟪ morph (`ℕ ∷ []) [] , unseal 2 ⟫)
         ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
        ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₈  = (((((($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
              ⟪ morph [] (lock 1 ∷ []) , id (` 2) ⟫)
             ⟪ morph [] (lock 0 ∷ []) , unseal 2 ⟫)
            ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

D₉ D₁₀ D₁₁ D₁₂ D₁₃ D₁₄ D₁₅ : Term
D₉  = (((((($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
              ⟪ morph [] (lock 1 ∷ lock 0 ∷ []) , unseal 2 ⟫)
             ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
            ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₁₀ = (((((($ 7) ⟪ morph [] (lock 2 ∷ lock 1 ∷ lock 0 ∷ []) , id `ℕ ⟫)
              ⟪ morph [] (unlock 0 ∷ unlock 1 ∷ lock 1 ∷ lock 0 ∷ [])
                , id `ℕ ⟫)
             ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
            ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₁₁ = ((((($ 7) ⟪ morph [] (unlock 0 ∷ unlock 1 ∷ lock 1 ∷ lock 0 ∷ [])
                    , id `ℕ ⟫)
             ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
            ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₁₂ = (((($ 7) ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
            ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₁₃ = ((($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₁₄ = (($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
D₁₅ = ($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

dstep₁ : [] ⊢ D₀ -→ D₁
dstep₁ = ξ-·-l (TyBeta V-ƛ)

dstep₂ : [] ⊢ D₁ -→ D₂
dstep₂ = Peel V-ƛ V-$

dstep₃ : [] ⊢ D₂ -→ D₃
dstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- the INNER vacuous Λ fires first — under ξ-Λ, because `Λ N` is a value
-- only when N is (V-Λ's premise, repair (1)).
dstep₄ : [] ⊢ D₃ -→ D₄
dstep₄ = ξ-⟪⟫ (ξ-·[] (ξ-Λ (TyBeta val-DS₇)))

dstep₅ : [] ⊢ D₄ -→ D₅
dstep₅ = ξ-⟪⟫ (TyBeta (V-⟪⟫ val-DS₇ I-idv))

-- IDPUSH #1 — the outer id-layer.
dstep₆ : [] ⊢ D₅ -→ D₆
dstep₆ = IdPush (V-⟪⟫ val-DS₇ I-idv) ez

-- IDPUSH #2 — the unseal IdPush #1 pushed inwards meets the NEXT layer.
dstep₇ : [] ⊢ D₆ -→ D₇
dstep₇ = ξ-⟪⟫ (IdPush val-DS₇ (es ez))

-- IDPUSH #3, #4 — THE TWO STEPS FRAME-EXACT BETA ADDS: the two dual
-- wrappers are themselves `id (` X)` layers, so the same rule walks
-- through them.
dstep₈ : [] ⊢ D₇ -→ D₈
dstep₈ = ξ-⟪⟫ (ξ-⟪⟫ (IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) (es (es ez))))

dstep₉ : [] ⊢ D₈ -→ D₉
dstep₉ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (IdPush (V-⟪⟫ V-$ I-seal) (es (es ez)))))

dstep₁₀ : [] ⊢ D₉ -→ D₁₀
dstep₁₀ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (CancelR V-$ (es (es ez))))))

dstep₁₁ : [] ⊢ D₁₀ -→ D₁₁
dstep₁₁ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))))

dstep₁₂ : [] ⊢ D₁₁ -→ D₁₂
dstep₁₂ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))))

dstep₁₃ : [] ⊢ D₁₂ -→ D₁₃
dstep₁₃ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))

dstep₁₄ : [] ⊢ D₁₃ -→ D₁₄
dstep₁₄ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

dstep₁₅ : [] ⊢ D₁₄ -→ D₁₅
dstep₁₅ = ξ-⟪⟫ (Drop$ base-ℕ)

dstep₁₆ : [] ⊢ D₁₅ -→ $ 7
dstep₁₆ = Drop$ base-ℕ

run-D₀ : [] ⊢ D₀ -→* $ 7
run-D₀ = dstep₁ then dstep₂ then dstep₃ then dstep₄ then dstep₅
    then dstep₆ then dstep₇ then dstep₈ then dstep₉ then dstep₁₀
    then dstep₁₁ then dstep₁₂ then dstep₁₃ then dstep₁₄ then dstep₁₅
    then dstep₁₆ then done

-- ── EVERY CONTRACTUM TYPES ─────────────────────────────────────────────
--
-- With FOUR IdPush states the hand-built `env` towers say nothing §11's
-- pair does not, so the typings are taken from PRESERVATION itself.  The
-- one fact worth pinning by hand is the FRAME the two new wrappers give
-- the planted value: QΞ₃ with BOTH crossed Λ slots masked — i.e. QΔ₁,
-- its birth frame, two binders in.
DΞᵏ : Ctxᵗ
DΞᵏ = masked (bind `ℕ) ∷ masked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ []

_ : interior (morph [] (lock 1 ∷ [])) (interior (morph [] (lock 0 ∷ [])) QΞ₃)
      ≡ DΞᵏ
_ = refl

-- the sealed 7 at the FULL bind prefix — still used by §11c's K
⊢Dseal₇ : QΞ₃ ∣ [] ⊢ ($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫ ⦂ ` 2
⊢Dseal₇ = env (mw rw[]
                 (sw-l (unmasked (bind `ℕ) , es (es ez) , nameable) sw[]))
               ⊢$ (conv-seal (es (es ez)))
               (wf-var (unmasked (bind `ℕ) , es (es ez) , nameable))

⊢D₁ : [] ∣ [] ⊢ D₁ ⦂ `ℕ
⊢D₁ = preservation ⊢D₀ dstep₁

⊢D₂ : [] ∣ [] ⊢ D₂ ⦂ `ℕ
⊢D₂ = preservation ⊢D₁ dstep₂

⊢D₃ : [] ∣ [] ⊢ D₃ ⦂ `ℕ
⊢D₃ = preservation ⊢D₂ dstep₃

⊢D₄ : [] ∣ [] ⊢ D₄ ⦂ `ℕ
⊢D₄ = preservation ⊢D₃ dstep₄

⊢D₅ : [] ∣ [] ⊢ D₅ ⦂ `ℕ
⊢D₅ = preservation ⊢D₄ dstep₅

⊢D₆ : [] ∣ [] ⊢ D₆ ⦂ `ℕ
⊢D₆ = preservation ⊢D₅ dstep₆

⊢D₇ : [] ∣ [] ⊢ D₇ ⦂ `ℕ
⊢D₇ = preservation ⊢D₆ dstep₇

⊢D₈ : [] ∣ [] ⊢ D₈ ⦂ `ℕ
⊢D₈ = preservation ⊢D₇ dstep₈

⊢D₉ : [] ∣ [] ⊢ D₉ ⦂ `ℕ
⊢D₉ = preservation ⊢D₈ dstep₉

⊢D₁₀ : [] ∣ [] ⊢ D₁₀ ⦂ `ℕ
⊢D₁₀ = preservation ⊢D₉ dstep₁₀

------------------------------------------------------------------------
-- §11b  VARIANT (ii) — AN ID-LAYER WHOSE CONVERSION REP IS CHAINED
------------------------------------------------------------------------

-- The Θ₂ of §11's IdPush redex is `bind ℕ ∷ []`: the rep it hands back is
-- the BASE TYPE ℕ, which names nothing.  This variant makes the rep a
-- VARIABLE that names ANOTHER BINDER — the "chained rep" shape that is the
-- whole content of the c10/c11 obstruction (proof/PreserveObstruct §4).
-- It is obtained by running Q's own program INSIDE one more package, at
-- the OUTER package's type variable:
--
--   R = ((ΛX. λy:X. ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [X]) · y) [ℕ]) · 7
--
-- The inner instantiation `[X]` mints a binder whose rep is `X`, so at
-- the IdPush redex `convCtx Θ₂ Δ ∋ 0 := ` 1` — Y's rep NAMES the outer binder
-- X.  IDPUSH FIRES AND THE CONTRACTUM TYPES: nothing in Θ₂ is locked, so
-- the scoping fact `interior Θ₂ Δ ⊢ᵗ ` 1` holds.

Rbody Rfun R₀ : Term
Rbody = (Qfun ·[ ` 0 ⇒ ` 0 , ` 0 ]) · (` 0)
Rfun  = Λ (ƛ (` 0) ∙ Rbody)
R₀    = (Rfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Qfun-any : ∀ {Δ Γ} → Δ ∣ Γ ⊢ Qfun ⦂ `∀ (` 0 ⇒ ` 0)
⊢Qfun-any =
  ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable))
         (⊢·[] (⊢Λ (⊢` here)) wf-ℕ))

⊢Rbody : (unmasked abst ∷ []) ∣ (` 0 ∷ []) ⊢ Rbody ⦂ ` 0
⊢Rbody = ⊢· (⊢·[] ⊢Qfun-any (wf-var (unmasked abst , ez , nameable))) (⊢` here)

⊢R₀ : [] ∣ [] ⊢ R₀ ⦂ `ℕ
⊢R₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) ⊢Rbody))
               wf-ℕ) ⊢$

-- the three type contexts the chained run works in
RΞ RΞ′ RΞ″ : Ctxᵗ
RΞ  = unmasked (bind (` 0)) ∷ unmasked (bind `ℕ) ∷ []
RΞ′ = unmasked (bind `ℕ) ∷ RΞ
RΞ″ = unmasked (bind `ℕ) ∷ masked (bind (` 0)) ∷ unmasked (bind `ℕ) ∷ []

_ : interior (morph ((` 0) ∷ []) []) QΔ₁ ≡ RΞ
_ = refl

_ : interior (morph (`ℕ ∷ []) []) RΞ ≡ RΞ′
_ = refl

_ : interior (morph [] (lock 1 ∷ [])) RΞ′ ≡ RΞ″
_ = refl

-- THE CHAINED REP, as a lookup: Θ₂'s binder 0 has rep ` 1, which NAMES
-- the outer binder — and that slot is VISIBLE inside Θ₂ (nothing locks it).
Rchain : convCtx (morph ((` 0) ∷ []) []) QΔ₁ ∋ 0 := ` 1
Rchain = ez

Rchain-scoped : interior (morph ((` 0) ∷ []) []) QΔ₁ ⊢ᵗ ` 1
Rchain-scoped = wf-var (_ , es ez , nameable)

-- ── the states ─────────────────────────────────────────────────────────

RS RS↑ : Term
RS  = (($ 7) ⟪ morph [] (lock 1 ∷ []) , seal 1 ⟫) ⟪ morph [] (lock 0 ∷ []) ,
  seal 0 ⟫
RS↑ = (($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫) ⟪ morph [] (lock 1 ∷ []) ,
  seal 1 ⟫

_ : wkᴹ 1 QS₇ ≡ ($ 7) ⟪ morph [] (lock 1 ∷ []) , seal 1 ⟫
_ = refl

_ : ⇑ᴹ RS ≡ RS↑
_ = refl

-- FRAME-EXACT BETA (2026-09-08): the value planted under ΛZ acquires
-- ΛZ's dual, with an identity conversion at the argument's type at that
-- depth (the CHAINED variable ` 1, i.e. Y).
RS↑↑ : Term
RS↑↑ = RS↑ ⟪ morph [] (lock 0 ∷ []) , id (` 1) ⟫

R₁ R₂ R₃ R₄ R₅ R₆ : Term
R₁  = ((ƛ (` 0) ∙ Rbody) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
R₂  = ((ƛ (` 0) ∙ Rbody) · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
R₃  = ((Qfun ·[ ` 0 ⇒ ` 0 , ` 0 ]) · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
R₄  = (((ƛ (` 0) ∙ Qbody) ⟪ morph ((` 0) ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · QS₇)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
R₅  = (((ƛ (` 0) ∙ Qbody) · RS) ⟪ morph ((` 0) ∷ []) [] , unseal 0 ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
R₆  = (((Λ RS↑↑) ·[ ` 1 , `ℕ ]) ⟪ morph ((` 0) ∷ []) [] , unseal 0 ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

rstep₁ : [] ⊢ R₀ -→ R₁
rstep₁ = ξ-·-l (TyBeta V-ƛ)

rstep₂ : [] ⊢ R₁ -→ R₂
rstep₂ = Peel V-ƛ V-$

-- THIS Beta crosses NO Λ (the variable sits in an argument position), so
-- it mints no wrapper.
rstep₃ : [] ⊢ R₂ -→ R₃
rstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- the INNER package is instantiated at the OUTER binder: rep ` 0.
rstep₄ : [] ⊢ R₃ -→ R₄
rstep₄ = ξ-⟪⟫ (ξ-·-l (TyBeta V-ƛ))

rstep₅ : [] ⊢ R₄ -→ R₅
rstep₅ = ξ-⟪⟫ (Peel V-ƛ (V-⟪⟫ V-$ I-seal))

-- … and THIS one does: `RS` crosses ΛZ and is wrapped in `↓Z , id Y`.
rstep₆ : [] ⊢ R₅ -→ R₆
rstep₆ = ξ-⟪⟫ (ξ-⟪⟫ (Beta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal)))

_ : evalTerms 6 ⊢R₀ ≡ R₀ ∷ R₁ ∷ R₂ ∷ R₃ ∷ R₄ ∷ R₅ ∷ R₆ ∷ []
_ = refl

-- The tail is a cascade of IdPushes (each residue conversion is ITSELF an
-- id-layer), two Cancels and six transparent layers over the numeral —
-- 15 steps from R₆, for 21 in all, against 18 before frame-exact Beta
-- (the extra layer buys one more IdPush, one more CancelR and one more
-- Drop$).  RENDERED
-- (scripts/render_term.sh 'showTrace 0 (eval 21 ⊢R₀)'), the rule sequence
-- is
--
--   TyBeta Peel Beta TyBeta Peel Beta TyBeta
--   IdPush IdPush CancelR IdPush IdPush IdPush IdPush CancelR
--   Drop$ Drop$ Drop$ Drop$ Drop$ Drop$
--
-- and the chain is the machine's own (`eval-sound`, strong.Eval), which is
-- what the states after R₆ are worth: they are what the rules compute.
run-R₀ : [] ⊢ R₀ -→* $ 7
run-R₀ = eval-sound 21 ⊢R₀

-- ── THE CHAINED IDPUSH REDEX AND ITS CONTRACTUM BOTH TYPE ──────────────
--
-- Stated STANDALONE, on the shape the cascade reaches, at the frame it
-- reaches it in: what §11b is about is the CHAINED REP, not how many
-- transparent layers stand between it and the numeral.

⊢RV₂ : RΞ″ ∣ [] ⊢ ($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫ ⦂ ` 2
⊢RV₂ = env (mw rw[] (sw-l (_ , es (es ez) , nameable) sw[])) ⊢$
            (conv-seal (es (es ez))) (wf-var (_ , es (es ez) , nameable))

⊢RS↑ : RΞ′ ∣ [] ⊢ RS↑ ⦂ ` 1
⊢RS↑ = env (mw rw[] (sw-l (_ , es ez , nameable) sw[])) ⊢RV₂
            (conv-seal (es ez)) (wf-var (_ , es ez , nameable))

⊢Rlayer : RΞ ∣ [] ⊢ RS↑ ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫ ⦂ ` 0
⊢Rlayer = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢RS↑
               (conv-idv (_ , es ez , nameable))
               (wf-var (_ , ez , nameable))

Rchained Rchained′ : Term
Rchained  = (RS↑ ⟪ morph (`ℕ ∷ []) [] , id (` 1) ⟫)
              ⟪ morph ((` 0) ∷ []) [] , unseal 0 ⟫
Rchained′ = (RS↑ ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫)
              ⟪ morph ((` 0) ∷ []) [] , id (` 1) ⟫

⊢Rchained : QΔ₁ ∣ [] ⊢ Rchained ⦂ ` 0
⊢Rchained = env (mw (rw-b (wf-var (_ , ez , nameable)) rw[]) sw[]) ⊢Rlayer
                 (conv-unseal ez) (wf-var (_ , ez , nameable))

-- IDPUSH AT A CHAINED REP: `Rchain` is the lookup, `Rchain-scoped` the
-- premise `env` then asks for.
rstep-chained : QΔ₁ ⊢ Rchained -→ Rchained′
rstep-chained = IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal) Rchain

-- the contractum: the inner wrapper now EXPORTS the chained rep ` 1, and
-- `env`'s last premise `RΞ ⊢ᵗ ` 1` is exactly `Rchain-scoped`.
⊢R₈-mid : RΞ ∣ [] ⊢ RS↑ ⟪ morph (`ℕ ∷ []) [] , unseal 1 ⟫ ⦂ ` 1
⊢R₈-mid = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢RS↑
               (conv-unseal (es ez)) Rchain-scoped

⊢Rchained′ : QΔ₁ ∣ [] ⊢ Rchained′ ⦂ ` 0
⊢Rchained′ = env (mw (rw-b (wf-var (_ , ez , nameable)) rw[]) sw[]) ⊢R₈-mid
                  (conv-idv (_ , es ez , nameable))
                  (wf-var (_ , ez , nameable))

------------------------------------------------------------------------
-- §11c  VARIANT (i) — AN ID-LAYER WITH A NON-TRIVIAL Θ₁
------------------------------------------------------------------------

-- Variant (i) asks for an IdPush redex whose INNER frame Θ₁ binds more
-- than one binder.  WHICH RULE COULD EVER MINT ONE?  Exactly one:
--
--   TyBeta   mints `morph (A ∷ []) []`                       numBinds 1
--   Peel     mints `dual Θ`, which is ALL locks/unlocks numBinds 0
--   CancelR  mints NO frame (both are carried over)
--   IdPush   mints NO frame (both are carried over)
--   TyPeelR  prepends one bind          numBinds = 1 + numBinds Θ
--
-- so `numBinds Θ ≥ 2` is reachable ONLY through TyPeelR.  Those facts,
-- machine-checked:

numBinds-TyBeta : (A : Ty) → numBinds (morph (A ∷ []) []) ≡ 1
numBinds-TyBeta A = refl

numBinds-dual : (Θ : CtxMorph) → numBinds (dual Θ) ≡ 0
numBinds-dual Θ = refl

numBinds-TyPeelR : (A : Ty) (Θ : CtxMorph)
  → numBinds (morph (A ∷ binds Θ) (changes Θ)) ≡ suc (numBinds Θ)
numBinds-TyPeelR A Θ = refl

-- ── A CLOSED SOURCE THAT REACHES TYPEELR ───────────────────────────────
--
--   G = ((ΛX. λx:X. ((ΛY. ΛZ. x) [ℕ]) [ℕ]) [ℕ]) · 7
--
-- `ΛY. ΛZ. x` has type ∀Y.∀Z.X, so the FIRST inner instantiation mints
-- the conversion `reveal 0 (`∀ (` 2)) = `∀ (id (` 2))` — an INERT ∀
-- conversion on a one-binder frame — and the SECOND instantiation is a
-- TyPeelR redex.  Its contractum would be the wanted `numBinds 2`
-- id-layer …

Gpoly Gbody Gfun G₀ : Term
Gpoly = Λ (Λ (` 0))                         -- ΛY. ΛZ. x
Gbody = (Gpoly ·[ `∀ (` 2) , `ℕ ]) ·[ ` 1 , `ℕ ]
Gfun  = Λ (ƛ (` 0) ∙ Gbody)
G₀    = (Gfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Gbody : (unmasked abst ∷ []) ∣ (` 0 ∷ []) ⊢ Gbody ⦂ ` 0
⊢Gbody = ⊢·[] (⊢·[] (⊢Λ (⊢Λ (⊢` here))) wf-ℕ) wf-ℕ

⊢G₀ : [] ∣ [] ⊢ G₀ ⦂ `ℕ
⊢G₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) ⊢Gbody))
               wf-ℕ) ⊢$

_ : reveal 0 (`∀ (` 2)) ≡ `∀ (id (` 2))
_ = refl

-- FRAME-EXACT BETA (2026-09-08): the planted 7 crosses BOTH Λs of
-- `Gpoly`, so it acquires the SAME pair of dual wrappers as §11a's `DS₇`
-- — the two calculi differ only in where the `·[ ]` sit.
GV G₁ G₂ G₃ G₄ G₅ : Term
GV = Λ DS₇
G₁ = ((ƛ (` 0) ∙ Gbody) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
G₂ = ((ƛ (` 0) ∙ Gbody) · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
G₃ = (((Λ GV) ·[ `∀ (` 2) , `ℕ ]) ·[ ` 1 , `ℕ ])
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
G₄ = ((GV ⟪ morph (`ℕ ∷ []) [] , `∀ (id (` 2)) ⟫) ·[ ` 1 , `ℕ ])
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
G₅ = ((wkᴹ 1 GV) ·[ ` 3 , ` 0 ])
       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , id (` 2) ⟫
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

-- the moved value, spelled out: every NAME shifts, the innermost `lock 0`
-- stays put (it is the value's own crossed Λ, protected by `extᵗ`).
_ : wkᴹ 1 GV
      ≡ Λ (((($ 7) ⟪ morph [] (lock 3 ∷ []) , seal 3 ⟫)
                ⟪ morph [] (lock 2 ∷ []) , id (` 3) ⟫)
               ⟪ morph [] (lock 0 ∷ []) , id (` 3) ⟫)
_ = refl

gstep₁ : [] ⊢ G₀ -→ G₁
gstep₁ = ξ-·-l (TyBeta V-ƛ)

gstep₂ : [] ⊢ G₁ -→ G₂
gstep₂ = Peel V-ƛ V-$

gstep₃ : [] ⊢ G₂ -→ G₃
gstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

gstep₄ : [] ⊢ G₃ -→ G₄
gstep₄ = ξ-⟪⟫ (ξ-·[] (TyBeta (V-Λ val-DS₇)))

-- the TyPeelR step, whose contractum is the wanted `numBinds Θ₁ ≡ 2` layer.
-- Its conversion premise is the redex's own, one `` `∀ `` inside —
-- here the identity at the OUTER binder, read under the ∀-binder.
⊢Gconv : (unmasked abst ∷ convCtx (morph (`ℕ ∷ []) []) QΔ₁)
           ⊢ id (` 2) ∶ ` 2 ⇝ ` 2
⊢Gconv = conv-idv (unmasked (bind `ℕ) , es (es ez) , nameable)

gstep₅ : [] ⊢ G₄ -→ G₅
gstep₅ = ξ-⟪⟫ (TyPeelR (V-Λ val-DS₇) ⊢Gconv)

_ : numBinds (morph (`ℕ ∷ `ℕ ∷ []) []) ≡ 2
_ = refl

-- G₄ IS WELL TYPED, AND SO IS ITS TYPEELR CONTRACTUM, with the repaired
-- rule: the pushed-in annotation is the INTERIOR ∀-body shifted past the
-- new binder (`` ` 3 ``, matching `wkᴹ 1 GV : `∀ (` 3)`), and the frame is
-- plain `Θ` — the `renᴮ suc Θ` double-shift that made `¬⊢G₅` true is
-- gone.  So variant (i) HAS a well-typed closed-source instance.
--
-- The typings come from PRESERVATION: with the two dual wrappers the
-- hand-built `env` towers are three layers taller and say nothing more,
-- and the frame each wrapper gives the planted value is pinned in §11a
-- (`DΞᵏ`).
⊢G₁ : [] ∣ [] ⊢ G₁ ⦂ `ℕ
⊢G₁ = preservation ⊢G₀ gstep₁

⊢G₂ : [] ∣ [] ⊢ G₂ ⦂ `ℕ
⊢G₂ = preservation ⊢G₁ gstep₂

⊢G₃ : [] ∣ [] ⊢ G₃ ⦂ `ℕ
⊢G₃ = preservation ⊢G₂ gstep₃

⊢G₄ : [] ∣ [] ⊢ G₄ ⦂ `ℕ
⊢G₄ = preservation ⊢G₃ gstep₄

⊢G₅ : [] ∣ [] ⊢ G₅ ⦂ `ℕ
⊢G₅ = preservation ⊢G₄ gstep₅

-- ── AND THE MULTI-BIND ID-LAYER IT DELIVERS ────────────────────────────
-- The same shape, hand-built at the frame the repaired rule produces
-- (one bind prepended, no double shift): IdPush fires at
-- `numBinds Θ₁ ≡ 2` and the
-- contractum TYPES.  So the multi-bind case is not itself an obstruction
-- — the lifting `shiftBy 2` is exactly absorbed by `pushBinds`.

K₀ K₁ : Term
K₀ = ((($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
        ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , id (` 2) ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
K₁ = ((($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
        ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , unseal 2 ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

_ : interior (morph (`ℕ ∷ `ℕ ∷ []) []) QΔ₁ ≡ QΞ₃
_ = refl

⊢K₀-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
                       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , id (` 2) ⟫ ⦂ ` 0
⊢K₀-in = env (mw (rw-b wf-ℕ (rw-b wf-ℕ rw[])) sw[]) ⊢Dseal₇
              (conv-idv (_ , es (es ez) , nameable))
              (wf-var (_ , ez , nameable))

⊢K₀ : [] ∣ [] ⊢ K₀ ⦂ `ℕ
⊢K₀ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢K₀-in (conv-unseal ez) wf-ℕ

kstep : [] ⊢ K₀ -→ K₁
kstep = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢K₁-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
                       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , unseal 2 ⟫ ⦂ `ℕ
⊢K₁-in = env (mw (rw-b wf-ℕ (rw-b wf-ℕ rw[])) sw[]) ⊢Dseal₇
              (conv-unseal (es (es ez))) wf-ℕ

⊢K₁ : [] ∣ [] ⊢ K₁ ⦂ `ℕ
⊢K₁ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢K₁-in (conv-id base-ℕ) wf-ℕ

------------------------------------------------------------------------
-- §12  THE WALL, PROBED FOR REACHABILITY POST-REPAIR
------------------------------------------------------------------------

-- THE WALL (notes/DECISIONS.md, "Peel FIXED and PROVEN"): IdPush,
-- CancelR and TyPeelR all need a contractum's inner wrapper to PRESENT A
-- REP `A` inside `Θ₂`'s interior, which fails when `Θ₂` LOCKS a slot that
-- `A` names.  The `¬IdPushCase` witness (proof/PreserveObstruct §4) is
-- exactly that: `Δi = bind (` 0) ∷ bind ℕ ∷ []`, `Θ₂ = lock 1 ∷ []`, so
-- `interior Θ₂ Δi = unmasked (bind (` 0)) ∷ masked (bind ℕ) ∷ []` — the
-- binder at slot 0 has rep ` 1, and slot 1 is blocked.
--
-- The retired §10 recorded the verdict "NOT reachable" (the hunt itself is
-- in notes/DECISIONS.md, 2026-09-06).  THIS SECTION SHARPENS IT.
-- Change ONE character of §11's Q — instantiate the vacuous `ΛZ` at the
-- OUTER type variable `Y` instead of at `ℕ`:
--
--   L = ((ΛY. λx:Y. ((ΛZ. x) [Y])) [ℕ]) · 7
--
-- and the witness type context IS REACHED, from closed plain source:
-- after the inner TyBeta the binder's rep is the chained `` ` 0 ``, and the
-- Peel-minted `lock 1` inside blocks the very slot that rep names.
--
-- BUT NOT WHERE IT HURTS.  The blocked context appears as the interior of
-- the CONCEALING (inert) wrapper, i.e. in a `Θ₁` position; the `Θ₂` of
-- every IdPush/CancelR redex on this run is lock-free, and both
-- contracta type.  The run reaches a VALUE.  So: THE WALL CONTEXT IS
-- REACHABLE, THE WALL CONFIGURATION IS NOT — the observation the invariant
-- hunt tried, and failed, to turn into a theorem (notes/DECISIONS.md,
-- 2026-09-06).

Lbody Lfun L₀ : Term
Lbody = (Λ (` 0)) ·[ ` 1 , ` 0 ]         -- (ΛZ. x) [Y]
Lfun  = Λ (ƛ (` 0) ∙ Lbody)
L₀    = (Lfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Lbody : (unmasked abst ∷ []) ∣ (` 0 ∷ []) ⊢ Lbody ⦂ ` 0
⊢Lbody = ⊢·[] (⊢Λ (⊢` here)) (wf-var (unmasked abst , ez , nameable))

⊢L₀ : [] ∣ [] ⊢ L₀ ⦂ `ℕ
⊢L₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) ⊢Lbody))
               wf-ℕ) ⊢$

-- THE WITNESS CONTEXTS, verbatim from proof/PreserveObstruct §4.
LΔ LΞ : Ctxᵗ
LΔ = unmasked (bind (` 0)) ∷ unmasked (bind `ℕ) ∷ []
LΞ = unmasked (bind (` 0)) ∷ masked (bind `ℕ) ∷ []

_ : interior (morph ((` 0) ∷ []) []) QΔ₁ ≡ LΔ
_ = refl

_ : interior (morph [] (lock 1 ∷ [])) LΔ ≡ LΞ
_ = refl

-- FRAME-EXACT BETA (2026-09-08) plants `QS₇↑` (§11) — the crossed 7 with
-- ΛY's dual on it — where the shift alone used to plant `QS₇⇑`.  The wall
-- CONTEXT is unchanged: the Peel-minted `lock 1` is still what sits inside
-- the chained binder.  The run is 11 steps, against 9 before.
L₁ L₂ L₃ L₄ L₅ : Term
L₁ = ((ƛ (` 0) ∙ Lbody) ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
L₂ = ((ƛ (` 0) ∙ Lbody) · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
L₃ = ((Λ QS₇↑) ·[ ` 1 , ` 0 ]) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
L₄ = (QS₇↑ ⟪ morph ((` 0) ∷ []) [] , id (` 1) ⟫)
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
L₅ = (QS₇↑ ⟪ morph ((` 0) ∷ []) [] , unseal 1 ⟫)
       ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

L₆ L₇ L₈ L₉ L₁₀ : Term
L₆ = ((QS₇⇑ ⟪ morph [] (lock 0 ∷ []) , unseal 1 ⟫)
        ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
L₇ = ((((($ 7) ⟪ morph [] (lock 1 ∷ lock 0 ∷ []) , id `ℕ ⟫)
            ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
           ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
L₈ = ((($ 7) ⟪ morph [] (unlock 0 ∷ lock 0 ∷ []) , id `ℕ ⟫)
         ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
L₉ = (($ 7) ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
L₁₀ = ($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

lstep₁ : [] ⊢ L₀ -→ L₁
lstep₁ = ξ-·-l (TyBeta V-ƛ)

lstep₂ : [] ⊢ L₁ -→ L₂
lstep₂ = Peel V-ƛ V-$

lstep₃ : [] ⊢ L₂ -→ L₃
lstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- THE STEP THAT BUILDS THE WALL CONTEXT: the binder minted here has the
-- CHAINED rep ` 0, and the Peel-minted `lock 1` sits inside it.
lstep₄ : [] ⊢ L₃ -→ L₄
lstep₄ = ξ-⟪⟫ (TyBeta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv))

-- … and IdPush still fires, because its Θ₂ (`bind ℕ ∷ []`) is LOCK-FREE.
lstep₅ : [] ⊢ L₄ -→ L₅
lstep₅ = IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) ez

-- IdPush again, on the layer frame-exact Beta added.
lstep₆ : [] ⊢ L₅ -→ L₆
lstep₆ = ξ-⟪⟫ (IdPush (V-⟪⟫ V-$ I-seal) (es ez))

lstep₇ : [] ⊢ L₆ -→ L₇
lstep₇ = ξ-⟪⟫ (ξ-⟪⟫ (CancelR V-$ (es ez)))

lstep₈ : [] ⊢ L₇ -→ L₈
lstep₈ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))

lstep₉ : [] ⊢ L₈ -→ L₉
lstep₉ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

lstep₁₀ : [] ⊢ L₉ -→ L₁₀
lstep₁₀ = ξ-⟪⟫ (Drop$ base-ℕ)

lstep₁₁ : [] ⊢ L₁₀ -→ $ 7
lstep₁₁ = Drop$ base-ℕ

run-L₀ : [] ⊢ L₀ -→* $ 7
run-L₀ = lstep₁ then lstep₂ then lstep₃ then lstep₄ then lstep₅
    then lstep₆ then lstep₇ then lstep₈ then lstep₉ then lstep₁₀
    then lstep₁₁ then done

-- … and the generated run agrees, so the wall CONTEXT really is on the
-- machine's own trace and not only on a hand-written one.
_ : evalTerms 11 ⊢L₀
      ≡ L₀ ∷ L₁ ∷ L₂ ∷ L₃ ∷ L₄ ∷ L₅ ∷ L₆ ∷ L₇ ∷ L₈ ∷ L₉ ∷ L₁₀ ∷ ($ 7) ∷ []
_ = refl

-- ── every state on the run TYPES, including the two the wall touches ───
--
-- `⊢Lseal₇` is the wall's own subterm, read at the wall frame `LΔ`; the
-- run states come from PRESERVATION (the extra transparent layer makes
-- each `env` tower one deeper and says nothing new).

⊢Lseal₇ : LΔ ∣ [] ⊢ ($ 7) ⟪ morph [] (lock 1 ∷ []) , seal 1 ⟫ ⦂ ` 1
⊢Lseal₇ = env (mw rw[] (sw-l (_ , es ez , nameable) sw[])) ⊢$
               (conv-seal (es ez)) (wf-var (_ , es ez , nameable))

⊢L₄ : [] ∣ [] ⊢ L₄ ⦂ `ℕ
⊢L₄ = preservation (preservation (preservation (preservation ⊢L₀ lstep₁)
                                               lstep₂) lstep₃) lstep₄

⊢L₅ : [] ∣ [] ⊢ L₅ ⦂ `ℕ
⊢L₅ = preservation ⊢L₄ lstep₅

-- THE PRECISE READING.  On this run the blocked slot lives inside a
-- wrapper that is a `Θ₁` (an INERT `seal` conversion, the CancelR
-- pattern's inner layer); the `Θ₂` of `lstep₅`'s IdPush and of
-- `lstep₆`'s CancelR is `bind ℕ ∷ []`, which locks nothing.  "A Θ₂ never
-- locks a slot a visible binder's rep names" is the statement the invariant
-- hunt tried to prove about the only rule that mints locks at all (Peel's
-- `dual`); it was refuted (notes/DECISIONS.md, 2026-09-06), and the scope
-- move made it unnecessary.

------------------------------------------------------------------------
-- §12b  THE WALL WITNESS, AFTER THE SCOPE MOVE
------------------------------------------------------------------------

-- §12 asked whether the wall CONFIGURATION is reachable.  The scope move
-- (strong.CtxMorph §4, 2026-09-06) makes the question moot: the
-- configuration is fine.  Here is the hand-built witness itself
-- (proof/PreserveObstruct §4) — `Δi = X := Y , Y := ℕ`, where X's rep
-- NAMES Y, under an outer boundary that LOCKS Y — taking its step.
--
--   R₀  = ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ id X ⟫) ⟪ ↓Y , unseal X ⟫)
--   R₁′ = ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ ↓Y , unseal X ⟫) ⟪ id Y ⟫)
--
-- (rendered by scripts/render_term.sh at `Δi`; `↓Y` is `lock 1`, `↥Y` is
-- `unlock 1`.)  READ THE TWO LINES SIDE BY SIDE: `↓Y` has moved from the
-- OUTER boundary to the INNER one, and the reveal `unseal X` went with
-- it; what is left outside is the REWOUND frame `↥Y , ↓Y`, whose net
-- effect on the type context is nothing at all.  The rep `Y` the reveal
-- hands back is therefore presented on the
-- outer boundary's own type context — where Y is live — instead of
-- inside the lock, which is exactly what `env`'s last premise refused.
-- The value's frame is unchanged, so `V` retypes where it was.

open import strong.proof.PreserveObstruct
  using (Δi; Θi; Vi; Ri; ⊢Ri; step-i)

wallR₁ : Term
wallR₁ = (Vi ⟪ morph [] [] ⋉ Θi , unseal 0 ⟫) ⟪ rewind Θi , mkId (` 1) ⟫

_ : wallR₁ ≡ (Vi ⟪ morph [] (lock 1 ∷ []) , unseal 0 ⟫)
               ⟪ morph [] (unlock 1 ∷ lock 1 ∷ []) , id (` 1) ⟫
_ = refl

-- THE STEP THE OLD RULE COULD NOT TAKE SOUNDLY …
wallstep₁ : Δi ⊢ Ri -→ wallR₁
wallstep₁ = step-i

-- … AND THE CONTRACTUM TYPES, by the theorem.
⊢wallR₁ : Δi ∣ [] ⊢ wallR₁ ⦂ ` 1
⊢wallR₁ = preservation ⊢Ri wallstep₁

-- the value's own frame is untouched by the move
_ : interior (morph [] [] ⋉ Θi) (interior (rewind Θi) Δi)
      ≡ interior (morph [] []) (interior Θi Δi)
_ = refl

-- AND THE RUN FINISHES.  The move brought the `seal X` of `Vi`'s own
-- outer layer directly under the pushed `unseal X`, so CancelR fires and
-- the result is a VALUE (at the abstract type Y — `7` is still sealed):
--
--   R₂ = ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫) ⟪ id Y ⟫) ⟪ id Y ⟫)
--
-- the mask/unmask pair sitting inertly on the frame it was moved into.
wallR₂ : Term
wallR₂ = (((($ 7) ⟪ morph [] [] , seal 1 ⟫)
             ⟪ morph [] (unlock 1 ∷ lock 1 ∷ []) , id (` 1) ⟫)
             ⟪ morph [] (unlock 1 ∷ lock 1 ∷ []) , id (` 1) ⟫)
             ⟪ morph [] (unlock 1 ∷ lock 1 ∷ []) , id (` 1) ⟫

wallstep₂ : Δi ⊢ wallR₁ -→ wallR₂
wallstep₂ = ξ-⟪⟫ (CancelR (V-⟪⟫ V-$ I-seal) ez)

run-wall : Δi ⊢ Ri -→* wallR₂
run-wall = wallstep₁ then wallstep₂ then done

-- … and the generated run agrees: the machine takes the moved step, at a
-- NON-EMPTY ambient (Δi = X := Y , Y := ℕ).
_ : evalTerms 2 ⊢Ri ≡ Ri ∷ wallR₁ ∷ wallR₂ ∷ []
_ = refl

val-wallR₂ : Value wallR₂
val-wallR₂ = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) I-idv) I-idv

⊢wallR₂ : Δi ∣ [] ⊢ wallR₂ ⦂ ` 1
⊢wallR₂ = preservation* ⊢Ri run-wall

------------------------------------------------------------------------
-- §13  TYPEELR FROM CLOSED, PLAIN SOURCE — THE TWO CONVERSIONS
------------------------------------------------------------------------

-- §11c's G reaches TyPeelR at an IDENTITY ∀ conversion, where the
-- annotation repair cannot fire.  This section reaches it at the two
-- conversions that DO exercise the mint `instReveal 0 s`, from ordinary
-- System F:
--
--   §13a  a CONCEAL ∀ conversion — a POLYMORPHIC ARGUMENT that crossed
--         a Peel.  Two machine-checked facts: (i) keeping `s` is
--         untypeable, and (ii) the mint `instReveal 0 s` TYPES, by the
--         theorem — the case the retired polarity index used to refuse.
--         The run then continues to a value.
--   §13b  the REVEAL mirror image, likewise by the theorem.
--   §13c  the RECORD of the other contracta weighed for §13a's redex —
--         Jeremy's candidate and its neighbours — and why each was not
--         taken.
--
-- The two sources differ by ONE thing — whether the ∀ crosses the
-- boundary INWARD (as an argument, §13a) or OUTWARD (as a result, §13b).
-- Under the polarity index that difference decided TYPEABILITY; now it
-- decides only which binder each minted leaf cites.

open import strong.Preservation using (preservation-TyPeelR)
open import strong.proof.PreserveObstruct
  using (Δt; Wt; val-Wt; ⊢Wt; Θt; st; ⊢st; Wft; ⊢Wft; Rt; ⊢Rt; step-t;
         ⊢t-contractum)

open import strong.proof.PeelDual using (interior-dual)
open import strong.proof.MoveScope using (interior-⋉-rewind)

------------------------------------------------------------------------
-- §13a  A CONCEAL ∀ CONVERSION: the polymorphic argument
------------------------------------------------------------------------

--   J = ((ΛX. λx:X. λf:(∀Y. Y ⇒ X). (f [X]) · x) [ℕ]) · 7 · (ΛY. λy:Y. 3)
--
-- `f`'s type mentions X, so TyBeta's minted conversion CONCEALS X on
-- f's domain: `conceal 0 (∀Y. Y ⇒ X) = ∀ (id Y ↦ seal X)`, a CONCEAL ∀
-- conversion.  The Peel hands it to the crossing argument verbatim, and
-- the body's `f [X]` is then a TyPeelR redex at that conversion.

JT : Ty                                  -- ∀Y. Y ⇒ X, read under X
JT = `∀ (` 0 ⇒ ` 1)

JB : Ty                                  -- the ΛX body type
JB = ` 0 ⇒ (JT ⇒ ` 0)

Jbody Jfun J₀ : Term
Jbody = ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · (` 1))
Jfun  = Λ (ƛ (` 0) ∙ Jbody)
J₀    = ((Jfun ·[ JB , `ℕ ]) · ($ 7)) · Wt

⊢JT : ∀ {Δ} → (unmasked abst ∷ Δ) ⊢ᵗ JT
⊢JT = wf-∀ (wf-⇒ (wf-var (unmasked abst , ez , nameable))
                 (wf-var (unmasked abst , es ez , nameable)))

⊢Jfun : [] ∣ [] ⊢ Jfun ⦂ `∀ JB
⊢Jfun = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable))
               (⊢ƛ ⊢JT (⊢· (⊢·[] (⊢` here)
                                 (wf-var (unmasked abst , ez , nameable)))
                            (⊢` (there here)))))

⊢J₀ : [] ∣ [] ⊢ J₀ ⦂ `ℕ
⊢J₀ = ⊢· (⊢· (⊢·[] ⊢Jfun wf-ℕ) ⊢$) ⊢Wt

-- ── the run to the TyPeelR redex ───────────────────────────────────────

-- TyBeta's mint: the argument's ∀-type is CONCEALED (it is a domain).
_ : reveal 0 JB ≡ seal 0 ↦ ((`∀ (id (` 0) ↦ seal 1)) ↦ unseal 0)
_ = refl

_ : conceal 0 JT ≡ `∀ st
_ = refl

J₁ J₂ J₃ J₄ J₅ : Term
J₁ = (((ƛ (` 0) ∙ Jbody)
         ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ ((`∀ st) ↦ unseal 0) ⟫) · ($ 7)) · Wt
J₂ = (((ƛ (` 0) ∙ Jbody) · QS₇)
        ⟪ morph (`ℕ ∷ []) [] , (`∀ st) ↦ unseal 0 ⟫) · Wt
J₃ = ((ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · QS₇))
        ⟪ morph (`ℕ ∷ []) [] , (`∀ st) ↦ unseal 0 ⟫) · Wt
J₄ = ((ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · QS₇)) · Wft)
       ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
J₅ = (Rt · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

jstep₁ : [] ⊢ J₀ -→ J₁
jstep₁ = ξ-·-l (ξ-·-l (TyBeta V-ƛ))

jstep₂ : [] ⊢ J₁ -→ J₂
jstep₂ = ξ-·-l (Peel V-ƛ V-$)

jstep₃ : [] ⊢ J₂ -→ J₃
jstep₃ = ξ-·-l (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal)))

-- THE CROSSING: the polymorphic argument acquires the CONCEAL ∀
-- conversion.
jstep₄ : [] ⊢ J₃ -→ J₄
jstep₄ = Peel V-ƛ (V-Λ V-ƛ)

jstep₅ : [] ⊢ J₄ -→ J₅
jstep₅ = ξ-⟪⟫ (Beta (V-⟪⟫ (V-Λ V-ƛ) I-all))

run-J₀ : [] ⊢ J₀ -→* J₅
run-J₀ = jstep₁ then jstep₂ then jstep₃ then jstep₄ then jstep₅ then done

-- J₅'s head IS proof/PreserveObstruct §2's redex, and it is TYPED there.
_ : J₅ ≡ (((Wt ⟪ Θt , `∀ st ⟫) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · QS₇)
           ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
_ = refl

⊢J₅-head : Δt ∣ [] ⊢ Rt ⦂ (` 0 ⇒ ` 0)
⊢J₅-head = ⊢Rt

J₆head J₆ : Term
J₆head = (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 0 ])
           ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , instReveal 0 st ⟫
J₆     = (J₆head · QS₇) ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

-- … and TyPeelR fires on it, from this closed source.  (Fact (ii) below
-- types both `J₆head` and `J₆`.)
jstep₆ : [] ⊢ J₅ -→ J₆
jstep₆ = ξ-⟪⟫ (ξ-·-l step-t)

-- ── FACT (i): KEEPING `s` IS UNTYPEABLE ────────────────────────────────
-- The note's contractum keeps the conversion `s`, whose TARGET body
-- still mentions the ∀-bound `` ` 0 `` where `env` now demands the
-- INSTANTIATED body: the domain leaf `id (` 0)` would have to convert
-- `` ` 1 `` (the new binder's rep, read inside) to `` ` 0 ``, and an
-- identity converts a type to ITSELF (`conv-id-refl`).
¬⊢J-plain :
  ¬ (Δt ∣ [] ⊢ (wkᴹ 1 Wt ·[ ` 0 ⇒ `ℕ , ` 0 ])
                 ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , st ⟫ ⦂ (` 0 ⇒ ` 0))
¬⊢J-plain (env _ (⊢·[] _ _) (conv-fun ⊢s ⊢t) _) with conv-id-refl ⊢s
... | ()

-- ── FACT (ii): THE MINT TYPES ──────────────────────────────────────────
-- `instReveal 0 st` inserts the instantiation leaf at the ∀-bound slot:

_ : instReveal 0 st ≡ seal 0 ↦ seal 1
_ = refl

J-convCtx : Ctxᵗ
J-convCtx = convCtx (morph ((` 0) ∷ binds Θt) (changes Θt)) Δt

_ : J-convCtx ≡ unmasked (bind (` 0)) ∷ unmasked (bind `ℕ) ∷ []
_ = refl

-- EACH LEAF CONCEALS AT ITS OWN BINDER, and that is the whole content …
-- the INSERTED leaf: the new binder's rep ` 1, concealed at its own name
J-dom : J-convCtx ⊢ seal 0 ∶ ` 1 ⇝ ` 0
J-dom = conv-seal ez

-- the conversion's OWN leaf: ℕ concealed at the crossed boundary's binder
J-cod : J-convCtx ⊢ seal 1 ∶ `ℕ ⇝ ` 1
J-cod = conv-seal (es ez)

-- … and so does the TREE.  Under the retired polarity index this was the
-- REFUTATION: `seal 0` sits CONTRAVARIANTLY and `seal 1` COVARIANTLY, so
-- no single `p` typed both.  Per variable there is nothing to reconcile —
-- Y's name is on the interior side (the `bind` this rule just pushed),
-- X's on the exterior side (behind Θt's `lock`).
⊢J-conv : J-convCtx ⊢ seal 0 ↦ seal 1 ∶ (` 0 ⇒ `ℕ) ⇝ (` 1 ⇒ ` 1)
⊢J-conv = conv-fun J-dom J-cod

-- HENCE THE LANDED CONTRACTUM TYPES, by the theorem — the head of J₆.
⊢J₆head : Δt ∣ [] ⊢ J₆head ⦂ (` 0 ⇒ ` 0)
⊢J₆head = preservation-TyPeelR val-Wt ⊢st ⊢Rt

_ : ⊢J₆head ≡ ⊢t-contractum
_ = refl

-- … and so does the whole state, one `env` out.
⊢J₆ : [] ∣ [] ⊢ J₆ ⦂ `ℕ
⊢J₆ = env (mw (rw-b wf-ℕ rw[]) sw[]) (⊢· ⊢J₆head ⊢QS₇) (conv-unseal ez) wf-ℕ

-- ── THE RUN CONTINUES, TO A VALUE ──────────────────────────────────────
--
-- Eight more steps: the TyBeta the peel exposed (the interior ∀ is now
-- instantiated at the binder TyPeelR bound), TWO Peels — the argument `7`
-- crosses both of the boundaries the run has stacked — a Beta, and then
-- the four transparent layers unwinding, Drop$ ⨟ CancelR ⨟ Drop$ ⨟ Drop$.
-- The answer is 3: `ΛY. λy:Y. 3` ignores its argument.
--
-- RENDERED (scripts/render_term.sh, `showTmIn 0`):
--
--  J₆  ((((ΛZ. (λx:Z. 3)) [Y] ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫)
--         · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
--  J₇  (((((λx:Z. 3) ⟪ ↑Z:=Y , (seal Z ↦ id ℕ) ⟫)
--          ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫)
--         · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑X:=ℕ , unseal X ⟫)
--  J₈  (((((λx:Z. 3) ⟪ ↑Z:=Y , (seal Z ↦ id ℕ) ⟫)
--          · ((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , ↥X , seal Y ⟫))
--         ⟪ ↑Y:=X , ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
--  J₉  (((((λx:Z. 3)
--          · (((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , ↥X , seal Y ⟫) ⟪ ↓Z , seal Z ⟫))
--          ⟪ ↑Z:=Y , id ℕ ⟫) ⟪ ↑Y:=X , ↓X , seal X ⟫)
--         ⟪ ↑X:=ℕ , unseal X ⟫)
--  J₁₀ (((3 ⟪ ↑Z:=Y , id ℕ ⟫) ⟪ ↑Y:=X , ↓X , seal X ⟫)
--         ⟪ ↑X:=ℕ , unseal X ⟫)
--  J₁₁ ((3 ⟪ ↑Y:=X , ↓X , seal X ⟫) ⟪ ↑X:=ℕ , unseal X ⟫)
--  J₁₂ ((3 ⟪ ↑Y:=X , ↓X , id ℕ ⟫) ⟪ ↑X:=ℕ , id ℕ ⟫)
--  J₁₃ (3 ⟪ ↑X:=ℕ , id ℕ ⟫)
--   →  3

_ : wkᴹ 1 Wt ≡ Wt
_ = refl

-- TyBeta's mint at the new binder: a conceal on the domain, a transparent
-- base identity on the codomain.
_ : reveal 0 (` 0 ⇒ `ℕ) ≡ seal 0 ↦ id `ℕ
_ = refl

JV : Term                      -- λy. 3, behind the freshly born boundary
JV = (ƛ (` 0) ∙ ($ 3)) ⟪ morph ((` 0) ∷ []) [] , seal 0 ↦ id `ℕ ⟫

val-JV : Value JV
val-JV = V-⟪⟫ V-ƛ I-fun

-- the two duals the two Peels mint
_ : dual (morph ((` 0) ∷ binds Θt) (changes Θt)) ≡ morph [] (lock 0 ∷ unlock 1 ∷
  [])
_ = refl

_ : dual (morph ((` 0) ∷ []) []) ≡ morph [] (lock 0 ∷ [])
_ = refl

JW JW′ : Term                  -- `7` after the first / the second crossing
JW  = wkᴹ 1 QS₇ ⟪ dual (morph ((` 0) ∷ binds Θt) (changes Θt)) , seal 0 ⟫
JW′ = wkᴹ 1 JW ⟪ dual (morph ((` 0) ∷ []) []) , seal 0 ⟫

_ : JW ≡ (($ 7) ⟪ morph [] (lock 1 ∷ []) , seal 1 ⟫) ⟪ morph [] (lock 0 ∷ unlock
  1 ∷ []) , seal 0 ⟫
_ = refl

val-JW : Value JW
val-JW = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal

val-JW′ : Value JW′
val-JW′ = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal) I-seal

J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ J₁₃ : Term
J₇  = ((JV ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , seal 0 ↦ seal 1 ⟫) · QS₇)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
J₈  = ((JV · JW) ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , seal 1 ⟫) ⟪ morph (`ℕ
  ∷ []) [] , unseal 0 ⟫
J₉  = ((((ƛ (` 0) ∙ ($ 3)) · JW′) ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫)
         ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , seal 1 ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
J₁₀ = ((($ 3) ⟪ morph ((` 0) ∷ []) [] , id `ℕ ⟫) ⟪ morph ((` 0) ∷ binds Θt)
  (changes Θt) , seal 1 ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫
J₁₁ = (($ 3) ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , seal 1 ⟫) ⟪ morph (`ℕ ∷
  []) [] , unseal 0 ⟫
J₁₂ = (($ 3) ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , id `ℕ ⟫) ⟪ morph (`ℕ ∷
  []) [] , id `ℕ ⟫
J₁₃ = ($ 3) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫

jstep₇ : [] ⊢ J₆ -→ J₇
jstep₇ = ξ-⟪⟫ (ξ-·-l (ξ-⟪⟫ (TyBeta V-ƛ)))

jstep₈ : [] ⊢ J₇ -→ J₈
jstep₈ = ξ-⟪⟫ (Peel val-JV (V-⟪⟫ V-$ I-seal))

jstep₉ : [] ⊢ J₈ -→ J₉
jstep₉ = ξ-⟪⟫ (ξ-⟪⟫ (Peel V-ƛ val-JW))

jstep₁₀ : [] ⊢ J₉ -→ J₁₀
jstep₁₀ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Beta val-JW′)))

jstep₁₁ : [] ⊢ J₁₀ -→ J₁₁
jstep₁₁ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

-- the CANCEL: the inner conceal at the binder the TyPeelR-born frame
-- carries, directly under the reveal that owns it (X ≡ numBinds Θ₁ + Y).
jstep₁₂ : [] ⊢ J₁₁ -→ J₁₂
jstep₁₂ = CancelR V-$ ez

jstep₁₃ : [] ⊢ J₁₂ -→ J₁₃
jstep₁₃ = ξ-⟪⟫ (Drop$ base-ℕ)

jstep₁₄ : [] ⊢ J₁₃ -→ $ 3
jstep₁₄ = Drop$ base-ℕ

run-J₆ : [] ⊢ J₆ -→* $ 3
run-J₆ = jstep₇ then jstep₈ then jstep₉ then jstep₁₀ then jstep₁₁
    then jstep₁₂ then jstep₁₃ then jstep₁₄ then done

-- THE WHOLE RUN, from closed plain source to the answer.
run-J : [] ⊢ J₀ -→* $ 3
run-J = jstep₁ then jstep₂ then jstep₃ then jstep₄ then jstep₅
   then jstep₆ then run-J₆

-- … and the generated run agrees on all fourteen steps, TyPeelR (J₅ → J₆)
-- included: the rule the retired polarity index refused is the step the
-- machine takes.
_ : evalTerms 14 ⊢J₀
      ≡ J₀ ∷ J₁ ∷ J₂ ∷ J₃ ∷ J₄ ∷ J₅ ∷ J₆ ∷ J₇ ∷ J₈ ∷ J₉ ∷ J₁₀ ∷ J₁₁
      ∷ J₁₂ ∷ J₁₃ ∷ ($ 3) ∷ []
_ = refl

------------------------------------------------------------------------
-- §13b  THE REVEAL MIRROR IMAGE
------------------------------------------------------------------------

--   H = (((ΛX. λx:X. ΛY. λy:Y. x) [ℕ]) · 7) [ℕ]
--
-- Here the ∀ crosses OUTWARD, as the RESULT, so TyBeta's mint REVEALS X
-- on the codomain: `reveal 0 (X ⇒ ∀Y. Y ⇒ X)` is
-- `seal X ↦ ∀ (id Y ↦ unseal X)` — §13a's shape with reveal and conceal
-- exchanged.  The contractum types BY THE THEOREM, as §13a's now does.

HB : Ty
HB = ` 0 ⇒ `∀ (` 0 ⇒ ` 1)

Hfun H₀ : Term
Hfun = Λ (ƛ (` 0) ∙ (Λ (ƛ (` 0) ∙ (` 1))))
H₀   = ((Hfun ·[ HB , `ℕ ]) · ($ 7)) ·[ ` 0 ⇒ `ℕ , `ℕ ]

⊢Hfun : [] ∣ [] ⊢ Hfun ⦂ `∀ HB
⊢Hfun = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable))
               (⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable))
                       (⊢` (there here)))))

⊢H₀ : [] ∣ [] ⊢ H₀ ⦂ (`ℕ ⇒ `ℕ)
⊢H₀ = ⊢·[] (⊢· (⊢·[] ⊢Hfun wf-ℕ) ⊢$) wf-ℕ

-- the REVEAL ∀ conversion, minted by the same rule that minted §13a's
-- CONCEAL one
_ : reveal 0 HB ≡ seal 0 ↦ (`∀ (id (` 0) ↦ unseal 1))
_ = refl

-- FRAME-EXACT BETA (2026-09-08): the crossed 7 is planted under ΛY (and
-- then under a ƛ, which changes no frame), so it carries ΛY's dual.  The
-- RUN LENGTH IS UNCHANGED — the layer sits inside a ƛ body, where nothing
-- evaluates it — only the states' spelling changes.  `QS₇↑′` is the same
-- value again, moved past the binder TyPeelR introduces.
QS₇↑′ : Term
QS₇↑′ = (($ 7) ⟪ morph [] (lock 2 ∷ []) , seal 2 ⟫)
          ⟪ morph [] (lock 0 ∷ []) , id (` 2) ⟫

HV H₁ H₂ H₃ H₄ : Term
HV = Λ (ƛ (` 0) ∙ QS₇↑)
H₁ = (((ƛ (` 0) ∙ (Λ (ƛ (` 0) ∙ (` 1))))
         ⟪ morph (`ℕ ∷ []) [] , seal 0 ↦ (`∀ (id (` 0) ↦ unseal 1)) ⟫) · ($ 7))
       ·[ ` 0 ⇒ `ℕ , `ℕ ]
H₂ = (((ƛ (` 0) ∙ (Λ (ƛ (` 0) ∙ (` 1)))) · QS₇)
        ⟪ morph (`ℕ ∷ []) [] , `∀ (id (` 0) ↦ unseal 1) ⟫) ·[ ` 0 ⇒ `ℕ , `ℕ ]
H₃ = (HV ⟪ morph (`ℕ ∷ []) [] , `∀ (id (` 0) ↦ unseal 1) ⟫) ·[ ` 0 ⇒ `ℕ , `ℕ ]
H₄ = ((Λ (ƛ (` 0) ∙ QS₇↑′)) ·[ ` 0 ⇒ ` 2 , ` 0 ])
       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , seal 0 ↦ unseal 1 ⟫

_ : wkᴹ 1 HV ≡ Λ (ƛ (` 0) ∙ QS₇↑′)
_ = refl

hstep₁ : [] ⊢ H₀ -→ H₁
hstep₁ = ξ-·[] (ξ-·-l (TyBeta V-ƛ))

hstep₂ : [] ⊢ H₁ -→ H₂
hstep₂ = ξ-·[] (Peel V-ƛ V-$)

hstep₃ : [] ⊢ H₂ -→ H₃
hstep₃ = ξ-·[] (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal)))

-- THE CONVERSION PREMISE, read off the redex's own `env`, one
-- `` `∀ `` inside.
⊢Hconv : (unmasked abst ∷ convCtx (morph (`ℕ ∷ []) []) []) ⊢ id (` 0) ↦ unseal 1
           ∶ (` 0 ⇒ ` 1) ⇝ (` 0 ⇒ `ℕ)
⊢Hconv = conv-fun (conv-idv (unmasked abst , ez , nameable))
                  (conv-unseal (es ez))

-- the mint: the inserted `seal 0` conceals the binder this rule
-- introduces, under an `unseal 1` that reveals the crossed boundary's.
_ : instReveal 0 (id (` 0) ↦ unseal 1) ≡ seal 0 ↦ unseal 1
_ = refl

hstep₄ : [] ⊢ H₃ -→ H₄
hstep₄ = TyPeelR (V-Λ V-ƛ) ⊢Hconv

run-H₀ : [] ⊢ H₀ -→* H₄
run-H₀ = hstep₁ then hstep₂ then hstep₃ then hstep₄ then done

-- … and the generated run agrees.  Four steps is exactly `run-H₀`'s
-- length, so the trace stops OUT OF FUEL at H₄ — which is right: H₄ is
-- not a value, and `hstep₅` below is its next step.
_ : evalTerms 4 ⊢H₀ ≡ H₀ ∷ H₁ ∷ H₂ ∷ H₃ ∷ H₄ ∷ []
_ = refl

-- ── AND THE CONTRACTUM TYPES — by the theorem, not by hand ─────────────

-- the sealed 7 inside ΛY's dual, at ΛY's own frame: this is `⊢crossΛ`
-- (strong.TermSubst §6) once more, and the `lock 0` is legal because ΛY's
-- slot is nameable.
⊢HV : (unmasked (bind `ℕ) ∷ []) ∣ [] ⊢ HV ⦂ `∀ (` 0 ⇒ ` 1)
⊢HV = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable))
             (env (mw rw[] (sw-l (unmasked abst , ez , nameable) sw[]))
                  (env (mw rw[]
                          (sw-l (unmasked (bind `ℕ) , es ez , nameable) sw[]))
                       ⊢$ (conv-seal (es ez))
                       (wf-var (unmasked (bind `ℕ) , es ez , nameable)))
                  (conv-idv (unmasked (bind `ℕ) , es ez , nameable))
                  (wf-var (unmasked (bind `ℕ) , es ez , nameable))))

⊢H₃ : [] ∣ [] ⊢ H₃ ⦂ (`ℕ ⇒ `ℕ)
⊢H₃ = ⊢·[] (env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢HV
                (conv-all ⊢Hconv)
                (wf-∀ (wf-⇒ (wf-var (unmasked abst , ez , nameable)) wf-ℕ)))
           wf-ℕ

⊢H₄ : [] ∣ [] ⊢ H₄ ⦂ (`ℕ ⇒ `ℕ)
⊢H₄ = preservation-TyPeelR (V-Λ V-ƛ) ⊢Hconv ⊢H₃

-- and H₄ is ONE TyBeta from a value, so the repaired rule does not
-- strand the run either.
H₅ : Term
H₅ = ((ƛ (` 0) ∙ QS₇↑′) ⟪ morph ((` 0) ∷ []) [] , reveal 0 (` 0 ⇒ ` 2) ⟫)
       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , seal 0 ↦ unseal 1 ⟫

hstep₅ : [] ⊢ H₄ -→ H₅
hstep₅ = ξ-⟪⟫ (TyBeta V-ƛ)

val-H₅ : Value H₅
val-H₅ = V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun

------------------------------------------------------------------------
-- §13c  JEREMY'S CANDIDATE AND ITS NEIGHBOURS
------------------------------------------------------------------------

-- THE RECORD of the contracta weighed for §13a's TyPeelR redex while the
-- polarity index still stood (2026-09-06).  Each is the same redex
--
--     (ΛY. λy:Y. 3) ⟪ ↓X , `∀ (id Y ↦ seal X) ⟫  [X]
--
-- contracted a different way; the landed rule is the one §13a runs, and
-- these are kept because they say WHY the others were not taken.

-- (i) JEREMY'S CANDIDATE, first form: keep the conversion
--     `id X ↦ seal X` and instantiate the interior at the FRESH binder
--     Y.  The id leaf's source is then X while the interior's domain is
--     Y, and an identity converts a type to ITSELF.
Cj1 : Term
Cj1 = (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 0 ])
        ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , id (` 1) ↦ seal 1 ⟫

¬⊢Cj1 : ¬ (Δt ∣ [] ⊢ Cj1 ⦂ (` 0 ⇒ ` 0))
¬⊢Cj1 (env _ (⊢·[] _ _) (conv-fun ⊢s ⊢t) _) with conv-id-refl ⊢s
... | ()

-- (ii) … second form: instantiate the interior at X itself.  X is MASKED
--      inside the boundary (`↓X`), so the instantiation is not even a
--      well-formed type there.
Cj2 : Term
Cj2 = (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 1 ])
        ⟪ morph ((` 0) ∷ binds Θt) (changes Θt) , id (` 1) ↦ seal 1 ⟫

¬⊢Cj2 : ∀ {B} → ¬ (Δt ∣ [] ⊢ Cj2 ⦂ B)
¬⊢Cj2 (env _ (⊢·[] _ (wf-var (_ , es ez , ()))) _ _)

-- (iii) the same conversion with the lock LIFTED for the instantiation
--       (`scope` applies the head last, so an `unlock X` in front makes
--       X visible inside).  TYPES — but it un-masks what the crossing
--       masked.
Cu : Term
Cu = (Wt ·[ ` 0 ⇒ `ℕ , ` 0 ]) ⟪ morph (binds Θt) (unlock 0 ∷ changes Θt) , id (`
  0) ↦ seal 0 ⟫

⊢Cu : Δt ∣ [] ⊢ Cu ⦂ (` 0 ⇒ ` 0)
⊢Cu = env (mw rw[]
              (sw-u (_ , ez , locked)
                    (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[])))
          (⊢·[] ⊢Wt (wf-var (unmasked (bind `ℕ) , ez , nameable)))
          (conv-fun (conv-idv (unmasked (bind `ℕ) , ez , nameable))
            (conv-seal ez))
          (wf-⇒ (wf-var (unmasked (bind `ℕ) , ez , nameable))
                (wf-var (unmasked (bind `ℕ) , ez , nameable)))

-- (iv) or the lock simply REMOVED (a lock binds nothing, so dropping it
--      is shift-free).  TYPES — but it discards the crossing's mask.
Cr : Term
Cr = (Wt ·[ ` 0 ⇒ `ℕ , ` 0 ]) ⟪ morph [] [] , id (` 0) ↦ seal 0 ⟫

⊢Cr : Δt ∣ [] ⊢ Cr ⦂ (` 0 ⇒ ` 0)
⊢Cr = env (mw rw[] sw[])
          (⊢·[] ⊢Wt (wf-var (unmasked (bind `ℕ) , ez , nameable)))
          (conv-fun (conv-idv (unmasked (bind `ℕ) , ez , nameable))
            (conv-seal ez))
          (wf-⇒ (wf-var (unmasked (bind `ℕ) , ez , nameable))
                (wf-var (unmasked (bind `ℕ) , ez , nameable)))

-- (v) OPTION B: instantiate the interior at the RESOLVED argument (X's
--     own rep ℕ), keep Θ, and mint the conversion by `conceal` on the
--     type.  TYPES — but it RESOLVES the binder, which the interior may
--     not see.
Cb : Term
Cb = (Wt ·[ ` 0 ⇒ `ℕ , `ℕ ]) ⟪ Θt , unseal 0 ↦ seal 0 ⟫

_ : conceal 0 (` 0 ⇒ ` 0) ≡ unseal 0 ↦ seal 0
_ = refl

⊢Cb : Δt ∣ [] ⊢ Cb ⦂ (` 0 ⇒ ` 0)
⊢Cb = env (mw rw[] (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[]))
          (⊢·[] ⊢Wt wf-ℕ)
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (unmasked (bind `ℕ) , ez , nameable))
                (wf-var (unmasked (bind `ℕ) , ez , nameable)))

-- (vi) Option B's REVEAL mirror, on §13b's H: no lock is in the way, so
--      the resolve variant lands on the same shape the theorem gives.
CbH : Term
CbH = (HV ·[ ` 0 ⇒ ` 1 , `ℕ ]) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ↦ unseal 0 ⟫

⊢CbH : [] ∣ [] ⊢ CbH ⦂ (`ℕ ⇒ `ℕ)
⊢CbH = env (mw (rw-b wf-ℕ rw[]) sw[]) (⊢·[] ⊢HV wf-ℕ)
           (conv-fun (conv-id base-ℕ) (conv-unseal ez)) (wf-⇒ wf-ℕ wf-ℕ)

-- THE VERDICT.  (i) and (ii) are untypeable outright; (iii)–(vi) type,
-- but each pays with the boundary's own discipline — (iii)/(iv) weaken
-- the mask the crossing installed, (v)/(vi) resolve the binder inside.
-- The landed rule keeps the frame and the mask and mints
-- `instReveal 0 s`, which types by `preservation-TyPeelR` (§13a).

------------------------------------------------------------------------
-- §14  THE PRE-BOUNDARY COUNTEREXAMPLE, RUN IN v2
------------------------------------------------------------------------

-- THE PROGRAM THAT KILLED THE PER-VARIABLE DESIGN (notes/old/notes-v1.md,
-- "Example 8, historical").  With one wrapper per revealed/concealed
-- variable — `M ↑[X:=A]` / `M ↓[X:=A]` — the run
--
--   (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)              : ∀Y. Y→Y
--   → TyBeta      (λf:(∀Z.Z→Z). ΛY. f [Y]) ↑[X:=ℕ] · (ΛZ. λz:Z. z)
--   → WrapReveal  ((λf. ΛY. f [Y]) · (ΛZ. λz:Z. z)↓[X:=ℕ]) ↑[X:=ℕ]
--   → Beta        (ΛY. (ΛZ. λz:Z. z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]
--   → TyWrapCncl  (ΛY. ((ΛZ. λz:Z. z) [Y]) ↓[X:=ℕ]) ↑[X:=ℕ]        ← ILL-TYPED
--
-- left the calculus.  Two things went wrong at once, and v2's boundary
-- fixes both:
--
--  (1) MASK, DON'T DROP.  A conceal's interior was the exterior with X
--      and everything bound AFTER X removed, so at Γ = Y , X:=ℕ the
--      interior was Γ↓X = ∅ and Y — bound after the boundary was born —
--      was gone.  v2's `lock` MASKS in place: `interior (lock 1 ∷ []) Δ`
--      keeps every entry of Δ and only makes slot 1 un-nameable (E-int
--      below).  Y stays.
--
--  (2) A TYPE ARGUMENT IS NEVER PUSHED IN.  TyWrapCncl wrote the spelled
--      argument into the sealed body.  `TyPeelR` records it as a NEW
--      BIND on the boundary (one bind prepended) and instantiates the interior
--      at the fresh NAME `` ` 0 ``; that is why the boundary is a LIST —
--      a context morphism — and not a single reveal-or-conceal.
--
-- Below: the SAME closed program, in v2, run to a VALUE in SIX steps,
-- with every step pinned by `det`.  Step 5 is the one that used to die.
--
-- RENDERED (scripts/render_term.sh 'showTrace 0 (eval 6 ⊢E₀)'):
--
--  E₀  ((ΛX. (λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))) [ℕ] · (ΛZ. (λx:Z. x)))
--  E₁  (((λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))
--         ⟪ ↑X:=ℕ , ((∀Y. (id Y ↦ id Y)) ↦ (∀Y. (id Y ↦ id Y))) ⟫)
--        · (ΛZ. (λx:Z. x)))
--  E₂  (((λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))
--         · ((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Y. (id Y ↦ id Y)) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₃  ((ΛY. (((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Z. (id Z ↦ id Z)) ⟫)
--               ⟪ ↓Y , (∀Z. (id Z ↦ id Z)) ⟫) [Y])
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₄  ((ΛY. (((ΛX′. (λx:X′. x)) ⟪ ↓X , (∀X′. (id X′ ↦ id X′)) ⟫) [Z]
--               ⟪ ↑Z:=Y , ↓Y , (seal Z ↦ unseal Z) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₅  ((ΛY. (((ΛY′. (λx:Y′. x)) [X′]
--                 ⟪ ↑X′:=Z , ↓X , (seal X′ ↦ unseal X′) ⟫)
--               ⟪ ↑Z:=Y , ↓Y , (seal Z ↦ unseal Z) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₆  ((ΛY. ((((λx:Y′. x) ⟪ ↑Y′:=X′ , (seal Y′ ↦ unseal Y′) ⟫)
--                 ⟪ ↑X′:=Z , ↓X , (seal X′ ↦ unseal X′) ⟫)
--               ⟪ ↑Z:=Y , ↓Y , (seal Z ↦ unseal Z) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)                      -- a VALUE
--
-- THE `↓Y` IS FRAME-EXACT BETA'S (2026-09-08).  Before it, E₃ and E₄ read
--
--  E₃  ((ΛY. ((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Z. (id Z ↦ id Z)) ⟫) [Y])
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₄  ((ΛY. ((ΛX′. (λx:X′. x)) [Z] ⟪ ↑Z:=Y , ↓X , (seal Z ↦ unseal Z) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--
-- — the crossed value planted under ΛY with NOTHING saying that ΛY's slot
-- is not in its frame.  Now it carries ΛY's dual `↓Y`, the run peels the
-- two wrappers in turn (steps 4 and 5), and it is six steps rather than
-- five.
--
-- E₃ is the old design's fourth line, and E₄/E₅ are where the two designs
-- part: `↑Z:=Y , ↓Y` and `↑X′:=Z , ↓X` are boundaries that MASK the outer
-- name and BIND a fresh one at the rep the exterior offers — no type is
-- pushed into the sealed body, and the rep is read at the boundary's
-- exterior (there are no unlocks, so that is `unlockedScope Θ Δ`), where
-- it is in scope.

-- ── the source ─────────────────────────────────────────────────────────

EID EBod : Ty
EID  = `∀ (` 0 ⇒ ` 0)                    -- ∀Z. Z ⇒ Z   (= ∀Y. Y ⇒ Y)
EBod = EID ⇒ EID                         -- the ΛX body type

Earg Ebody Efun E₀ : Term
Earg  = Λ (ƛ (` 0) ∙ (` 0))              -- ΛZ. λz:Z. z
Ebody = Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ])   -- ΛY. f [Y]
Efun  = Λ (ƛ EID ∙ Ebody)                -- ΛX. λf:(∀Z.Z⇒Z). ΛY. f [Y]
E₀    = (Efun ·[ EBod , `ℕ ]) · Earg

⊢EID : ∀ {Δ} → (unmasked abst ∷ Δ) ⊢ᵗ EID
⊢EID = wf-∀ (wf-⇒ (wf-var (unmasked abst , ez , nameable))
                  (wf-var (unmasked abst , ez , nameable)))

⊢Earg : ∀ {Δ Γ} → Δ ∣ Γ ⊢ Earg ⦂ EID
⊢Earg = ⊢Λ (⊢ƛ (wf-var (unmasked abst , ez , nameable)) (⊢` here))

⊢Efun : [] ∣ [] ⊢ Efun ⦂ `∀ EBod
⊢Efun = ⊢Λ (⊢ƛ ⊢EID
               (⊢Λ (⊢·[] (⊢` here) (wf-var (unmasked abst , ez , nameable)))))

⊢E₀ : [] ∣ [] ⊢ E₀ ⦂ EID
⊢E₀ = ⊢· (⊢·[] ⊢Efun wf-ℕ) ⊢Earg

-- ── the two conversions the run uses ───────────────────────────────

-- X does not occur in EBod, so TyBeta's mint is TRANSPARENT on both
-- halves: the crossing hands the argument an all-identity ∀ conversion.
Eid∀ : Conv
Eid∀ = `∀ (id (` 0) ↦ id (` 0))

_ : reveal 0 EBod ≡ Eid∀ ↦ Eid∀
_ = refl

-- ── STEP 1 — TYBETA.  The binder X := ℕ is minted.

E₁ : Term
E₁ = ((ƛ EID ∙ Ebody) ⟪ morph (`ℕ ∷ []) [] , Eid∀ ↦ Eid∀ ⟫) · Earg

estep₁ : [] ⊢ E₀ -→ E₁
estep₁ = ξ-·-l (TyBeta V-ƛ)

-- ── STEP 2 — PEEL.  `ΛZ. λz:Z. z` crosses; the dual masks the new binder.

_ : dual (morph (`ℕ ∷ []) []) ≡ morph [] (lock 0 ∷ [])
_ = refl

_ : wkᴹ 1 Earg ≡ Earg
_ = refl

EW : Term                        -- the argument, behind the crossing
EW = Earg ⟪ morph [] (lock 0 ∷ []) , Eid∀ ⟫

val-EW : Value EW
val-EW = V-⟪⟫ (V-Λ V-ƛ) I-all

E₂ : Term
E₂ = ((ƛ EID ∙ Ebody) · EW) ⟪ morph (`ℕ ∷ []) [] , Eid∀ ⟫

estep₂ : [] ⊢ E₁ -→ E₂
estep₂ = Peel V-ƛ (V-Λ V-ƛ)

-- ── STEP 3 — BETA, under ξ-⟪⟫, FRAME-EXACT (2026-09-08).  `substᵐ`'s Λ
-- clause does two things to the crossed value as it passes ΛY: it SHIFTS
-- it — the LOCK's name moves, lock 0 ↦ lock 1, and nothing else does, a
-- name and not a spelling — and it WRAPS it in ΛY's DUAL `↓Y`, under the
-- identity conversion at the argument's own type.
--
-- BEFORE FRAME-EXACT BETA the contractum was `Λ (EW↑ ·[ … ])`: the
-- shifted value with NOTHING recording that ΛY's slot is not its.  Its
-- frame at that position was `Y Λ-bound , ⌷[X := ℕ]` (`E-int` below) — one
-- entry MORE than the frame it was born in.  Harmless via indices (its
-- shifted names cannot reach slot 0) but not EXACT; every other rule in
-- the table is exact, and this is the one Jeremy asked to close.  The run
-- is 6 steps now, against 5 before: the extra layer is consumed by a
-- second TyPeelR.

EW↑ : Term
EW↑ = Earg ⟪ morph [] (lock 1 ∷ []) , Eid∀ ⟫

_ : ⇑ᴹ EW ≡ EW↑
_ = refl

EW↑↑ : Term                      -- … and the wrapper ΛY's dual adds
EW↑↑ = EW↑ ⟪ morph [] (lock 0 ∷ []) , Eid∀ ⟫

-- `EID` is a CLOSED type, so `⇑ᵗ EID ≡ EID` and the minted identity
-- conversion is the one the run already uses: `mkId EID ≡ Eid∀`.
_ : mkId EID ≡ Eid∀
_ = refl

_ : Ebody [ EW ∶ EID ]ᵐ ≡ Λ (EW↑↑ ·[ ` 0 ⇒ ` 0 , ` 0 ])
_ = refl

E₃ : Term
E₃ = (Λ (EW↑↑ ·[ ` 0 ⇒ ` 0 , ` 0 ])) ⟪ morph (`ℕ ∷ []) [] , Eid∀ ⟫

estep₃ : [] ⊢ E₂ -→ E₃
estep₃ = ξ-⟪⟫ (Beta val-EW)

-- ── THE STEP THE OLD DESIGN DIED ON ────────────────────────────────────
--
-- E₃'s inner redex is `EW↑↑ ·[ ` 0 ⇒ ` 0 , ` 0 ]`: the crossed value,
-- type-applied to the Λ-bound Y — a variable bound AFTER the boundary
-- was born.  Here are the two type contexts, at THE SHIFTED VALUE's
-- position — i.e. one layer in, inside the dual wrapper.

EΔ₃ : Ctxᵗ                       -- the ambient: Y abstract, X := ℕ
EΔ₃ = unmasked abst ∷ unmasked (bind `ℕ) ∷ []

_ : interior (morph (`ℕ ∷ []) []) [] ≡ unmasked (bind `ℕ) ∷ []
_ = refl

-- (a) THE FRAME THE DUAL WRAPPER GIVES THE PLANTED VALUE.  This is the
-- frame identity of strong.TermSubst §5b at this point: the exterior with
-- ΛY's slot MASKED — i.e. the value's BIRTH frame `X := ℕ`, one masked
-- entry in.  Nothing gained, nothing lost.  RENDERED
-- (`showTCtxAt 99 0 (λ { 0 → "Y" ; _ → "X" })`, so that the names agree
-- with the trace above):
--
--   E-dual-int   ⌷[Y Λ-bound] , X := ℕ
--   E-dual-ext   Y Λ-bound , X := ℕ
E-dual-int E-dual-ext : Ctxᵗ
E-dual-int = interior (morph [] (lock 0 ∷ [])) EΔ₃
E-dual-ext = convCtx  (morph [] (lock 0 ∷ [])) EΔ₃

_ : E-dual-int ≡ masked abst ∷ unmasked (bind `ℕ) ∷ []
_ = refl

_ : E-dual-ext ≡ EΔ₃
_ = refl

-- Y IS NOT NAMEABLE INSIDE, and that is the repair: the value was born
-- before ΛY existed, and now the frame says so.  BEFORE FRAME-EXACT BETA
-- the value sat at `EΔ₃` itself, where Y IS nameable — sound (its shifted
-- indices cannot reach slot 0) but one entry wider than its birth frame.
E-Y-not-inside : ¬ (E-dual-int ⊢ᵗ ` 0)
E-Y-not-inside (wf-var (_ , ez , ()))

-- (b) AND INSIDE THE VALUE'S OWN (Peel-minted) WRAPPER: the exterior with
-- X masked too — NOT TRUNCATED.  The old design's interior at this point
-- was Γ↓X = ∅.
--
--   E-int   ⌷[Y Λ-bound] , ⌷[X := ℕ]
--   E-ext   ⌷[Y Λ-bound] , X := ℕ
E-int E-ext : Ctxᵗ
E-int = interior (morph [] (lock 1 ∷ [])) E-dual-int
E-ext = convCtx  (morph [] (lock 1 ∷ [])) E-dual-int

_ : E-int ≡ masked abst ∷ masked (bind `ℕ) ∷ []
_ = refl

_ : E-ext ≡ E-dual-int
_ = refl

-- X still is not nameable: the mask does its job.
E-X-hidden : ¬ (E-int ⊢ᵗ ` 1)
E-X-hidden (wf-var (_ , es ez , ()))

-- ── STEP 4 — TYPEELR, under ξ-Λ, ON THE DUAL WRAPPER.  The type argument
-- Y is NOT pushed into the crossed body; it is recorded as a NEW BIND,
-- `bind (` 0)`, and the interior is instantiated at that bind's own name.
-- The conversion's abstract slot becomes the fresh binder, so each
-- identity leaf becomes the instantiation step.
--
-- IT IS NOW THE OUTER (Beta-minted) WRAPPER THAT PEELS FIRST — its
-- conversion is `mkId EID = Eid∀`, a `` `∀ `` — and the value's own
-- Peel-minted wrapper peels in step 5.  Y is read where the BIND is
-- recorded, on the wrapper's conversion context `E-dual-ext`, where it is
-- nameable; it never has to be nameable inside.

E-convCtx : Ctxᵗ
E-convCtx = unmasked abst ∷ convCtx (morph [] (lock 0 ∷ [])) EΔ₃

-- the conversion premise, at ANY conversion context: both leaves read the
-- ∀-bound slot 0, which is `abst` wherever the `` `∀ `` is.
⊢Es : ∀ {Δ} → (unmasked abst ∷ Δ)
    ⊢ id (` 0) ↦ id (` 0) ∶ (` 0 ⇒ ` 0) ⇝ (` 0 ⇒ ` 0)
⊢Es = conv-fun (conv-idv (unmasked abst , ez , nameable))
               (conv-idv (unmasked abst , ez , nameable))

_ : E-convCtx ⊢ id (` 0) ↦ id (` 0) ∶ (` 0 ⇒ ` 0) ⇝ (` 0 ⇒ ` 0)
_ = ⊢Es

_ : instReveal 0 (id (` 0) ↦ id (` 0)) ≡ seal 0 ↦ unseal 0
_ = refl

EW↑₂ : Term                      -- the value, moved past TyPeelR's binder
EW↑₂ = Earg ⟪ morph [] (lock 2 ∷ []) , Eid∀ ⟫

_ : wkᴹ 1 EW↑ ≡ EW↑₂
_ = refl

E₄ : Term
E₄ = (Λ ((EW↑₂ ·[ ` 0 ⇒ ` 0 , ` 0 ])
           ⟪ morph ((` 0) ∷ []) (lock 0 ∷ []) , seal 0 ↦ unseal 0 ⟫))
       ⟪ morph (`ℕ ∷ []) [] , Eid∀ ⟫

estep₄ : [] ⊢ E₃ -→ E₄
estep₄ = ξ-⟪⟫ (ξ-Λ (TyPeelR (V-⟪⟫ (V-Λ V-ƛ) I-all) ⊢Es))

-- ── STEP 5 — TYPEELR AGAIN, one layer in: the value's OWN Peel-minted
-- wrapper.  THIS IS THE STEP FRAME-EXACT BETA ADDS, and it is the step
-- the old design died on: the crossed value type-applied to a variable
-- bound after the boundary was born.

E₅ : Term
E₅ = (Λ (((Earg ·[ ` 0 ⇒ ` 0 , ` 0 ])
            ⟪ morph ((` 0) ∷ []) (lock 2 ∷ []) , seal 0 ↦ unseal 0 ⟫)
           ⟪ morph ((` 0) ∷ []) (lock 0 ∷ []) , seal 0 ↦ unseal 0 ⟫))
       ⟪ morph (`ℕ ∷ []) [] , Eid∀ ⟫

estep₅ : [] ⊢ E₄ -→ E₅
estep₅ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (TyPeelR (V-Λ V-ƛ) ⊢Es)))

-- ── STEP 6 — TYBETA, inside.  The ΛZ is consumed against the bind
-- TyPeelR just made, and the result is a VALUE.

_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

E₆ : Term
E₆ = (Λ ((((ƛ (` 0) ∙ (` 0)) ⟪ morph ((` 0) ∷ []) [] , seal 0 ↦ unseal 0 ⟫)
             ⟪ morph ((` 0) ∷ []) (lock 2 ∷ []) , seal 0 ↦ unseal 0 ⟫)
            ⟪ morph ((` 0) ∷ []) (lock 0 ∷ []) , seal 0 ↦ unseal 0 ⟫))
       ⟪ morph (`ℕ ∷ []) [] , Eid∀ ⟫

estep₆ : [] ⊢ E₅ -→ E₆
estep₆ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (ξ-⟪⟫ (TyBeta V-ƛ))))

val-E₆ : Value E₆
val-E₆ =
  V-⟪⟫ (V-Λ (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun) I-fun)) I-all

run-E : [] ⊢ E₀ -→* E₆
run-E = estep₁ then estep₂ then estep₃ then estep₄ then estep₅
    then estep₆ then done

-- … and the generated run agrees, the step the OLD design died on (now
-- step 5) included.
_ : evalTerms 6 ⊢E₀ ≡ E₀ ∷ E₁ ∷ E₂ ∷ E₃ ∷ E₄ ∷ E₅ ∷ E₆ ∷ []
_ = refl

-- THE ANSWER TYPES, at the source's own type ∀Y. Y ⇒ Y.
⊢E₆ : [] ∣ [] ⊢ E₆ ⦂ EID
⊢E₆ = preservation* ⊢E₀ run-E

-- ── DETERMINISM PINS: the run above is THE run.

edet₁ : ∀ {M′} → [] ⊢ E₀ -→ M′ → M′ ≡ E₁
edet₁ st = det st estep₁

edet₂ : ∀ {M′} → [] ⊢ E₁ -→ M′ → M′ ≡ E₂
edet₂ st = det st estep₂

edet₃ : ∀ {M′} → [] ⊢ E₂ -→ M′ → M′ ≡ E₃
edet₃ st = det st estep₃

edet₄ : ∀ {M′} → [] ⊢ E₃ -→ M′ → M′ ≡ E₄
edet₄ st = det st estep₄

edet₅ : ∀ {M′} → [] ⊢ E₄ -→ M′ → M′ ≡ E₅
edet₅ st = det st estep₅

edet₆ : ∀ {M′} → [] ⊢ E₅ -→ M′ → M′ ≡ E₆
edet₆ st = det st estep₆

------------------------------------------------------------------------
-- §15  TIGHTNESS, RULE BY RULE — JEREMY'S TEST APPLIED TO EVERY RULE
--      THAT MOVES A SUBTERM
------------------------------------------------------------------------

-- THE METHOD (Jeremy, 2026-09-06; proof/DualTightness for `Peel`).  Take
-- a redex that is ILL TYPED, and ill typed for exactly one localized
-- reason: a subterm NAMES a type variable that the frame at its position
-- does not offer — the entry is `masked`, or there is no entry at all.
-- The fault is always the SAME premise, `wf-var` in `⊢·[]`'s
-- `Δ ⊢ᵗ A`.  Take the step.  The rule MOVES that subterm into a NEW
-- frame.  If the contractum types, the reduction relation has GAINED
-- SCOPE: it relates a term the exterior refuses to one it accepts, and
-- design law 2 is false for the relation (`Design.md` §8).  If the
-- contractum is refused for the same reason, the rule is TIGHT.
--
-- This is a theorem rather than an anecdote because each rule's new
-- frame is a KNOWN FUNCTION of the old one — the frame identities
-- collected at the end of the section.  The example only exhibits the
-- identity at one point; the identity is what makes the verdict general.
--
-- ONE PROBE serves every rule:
--
--   scripts/render_term.sh 'showTmIn 1 (prb 0)'  =  (λx:ℕ. (ΛY. 3) [X])
--
-- a VALUE (`V-ƛ`) whose only free type name is the type argument of its
-- vacuous `ΛY`.  `prb k` names slot k; nothing else in it can fail.
--
-- THE ONE EXPECTED EXCEPTION IS `Beta` AT AN ERASING BODY — §15d.
--
-- The masked exterior every test but §15b and §15c uses:
--
--   scripts/render_term.sh 'showTCtx Δ✦'  =  ⌷[X := ℕ]

prb : ℕ → Term
prb k = ƛ `ℕ ∙ ((Λ ($ 3)) ·[ `ℕ , ` k ])

val-prb : ∀ {k} → Value (prb k)
val-prb = V-ƛ

Δ✦ : Ctxᵗ
Δ✦ = masked (bind `ℕ) ∷ []

-- THE THREE FRAME IDENTITIES THAT HAD NO NAME (§15f collects all six).
-- All three are `refl`: `interior Θ Δ` is `pushBinds (binds Θ) (scope Θ Δ)`,
-- a bind contributes to the BIND half alone (leaving `scope` untouched),
-- and a lone `lock 0` is one `maskEnt` at the head.
interior-TyBeta : (A : Ty) (Δ : Ctxᵗ)
  → interior (morph (A ∷ []) []) Δ ≡ unmasked (bind A) ∷ Δ
interior-TyBeta A Δ = refl

interior-TyPeelR : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (morph (A ∷ binds Θ) (changes Θ)) Δ
      ≡ unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ
interior-TyPeelR A Θ Δ = refl

-- FRAME-EXACT BETA'S OWN (2026-09-08, strong.TermSubst §5b): the wrapper
-- an image acquires when it crosses a `Λ` is that binder's DUAL, and its
-- interior is the image's BIRTH frame with the crossed slot masked.
interior-Beta-Λ : (Δ : Ctxᵗ)
  → interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ)
      ≡ masked abst ∷ Δ
interior-Beta-Λ Δ = refl

------------------------------------------------------------------------
-- §15a  TYBETA — the mint.  `abst` REFINES to `bind`, and nothing else
--       moves
------------------------------------------------------------------------

-- `TyBeta` types its body `N` at `unmasked abst ∷ Δ` (that is `⊢Λ`) and
-- the contractum types it at `interior (morph (A ∷ []) []) Δ`.  Those two
-- type contexts differ AT SLOT 0 ONLY, and there the change is a
-- REFINEMENT (`abst ⊑ᵇ bind A` under `la-uu`) — intended: TyBeta REVEALS,
-- it
-- is the rule that installs a representation.  Every OTHER slot is `Δ`
-- itself, on the nose.  So a body that names a slot Δ masks is refused
-- on both sides.
--
--   showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξa₀  =  Y Λ-bound , ⌷[X := ℕ]
--   showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξa   =  Y := ℕ , ⌷[X := ℕ]

Nᵃ : Term
Nᵃ = prb 1

-- showTmIn 1 Rᵃ  =  (ΛY. (λx:ℕ. (ΛZ. 3) [X])) [ℕ]
Rᵃ : Term
Rᵃ = (Λ Nᵃ) ·[ (`ℕ ⇒ `ℕ) , `ℕ ]

-- THE FAULT, LOCALIZED: `⊢·[]`'s `Δ ⊢ᵗ A` at `` ` 1 `` = X, which
-- `unmasked abst ∷ Δ✦` masks.
¬⊢Nᵃ-abst : ∀ {Γ A} → ¬ ((unmasked abst ∷ Δ✦) ∣ Γ ⊢ Nᵃ ⦂ A)
¬⊢Nᵃ-abst (⊢ƛ _ (⊢·[] _ (wf-var (_ , es ez , ()))))

¬⊢Rᵃ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Rᵃ ⦂ A)
¬⊢Rᵃ (⊢·[] (⊢Λ ⊢N) _) = ¬⊢Nᵃ-abst ⊢N

-- showTmIn 1 Cᵃ  =
--   ((λx:ℕ. (ΛZ. 3) [X]) ⟪ ↑Y:=ℕ , (id ℕ ↦ id ℕ) ⟫)
Cᵃ : Term
Cᵃ = Nᵃ ⟪ morph (`ℕ ∷ []) [] , reveal 0 (`ℕ ⇒ `ℕ) ⟫

stepᵃ : Δ✦ ⊢ Rᵃ -→ Cᵃ
stepᵃ = TyBeta val-prb

-- THE FRAME IDENTITY, at this Δ.
_ : interior (morph (`ℕ ∷ []) []) Δ✦ ≡ unmasked (bind `ℕ) ∷ Δ✦
_ = interior-TyBeta `ℕ Δ✦

-- … and X is masked there too.
¬⊢Nᵃ-bind : ∀ {Γ A} → ¬ ((unmasked (bind `ℕ) ∷ Δ✦) ∣ Γ ⊢ Nᵃ ⦂ A)
¬⊢Nᵃ-bind (⊢ƛ _ (⊢·[] _ (wf-var (_ , es ez , ()))))

¬⊢Cᵃ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Cᵃ ⦂ A)
¬⊢Cᵃ (env _ ⊢N _ _) = ¬⊢Nᵃ-bind ⊢N

-- THE REFINEMENT THE RULE DOES MAKE, and its exact extent: slot 0 gains
-- a representation, slot 1 keeps its mask.  This is preservation's ONE
-- `⊢retag` call site (`Design.md` §7).
_ : (unmasked abst ∷ Δ✦) ⊑ᵃ (unmasked (bind `ℕ) ∷ Δ✦)
_ = la∷ (la-uu le-ab) (la∷ (la-mm le-bb) la[])

-- THE ABSENT COMPANION.  A slot that exists in NEITHER type context
-- still exists in neither.  (Not rendered: `Show` names a free slot from
-- its supply whether or not the type context has one, so an out-of-range
-- index would print as a name that means something else.)
Nᵃ∅ : Term
Nᵃ∅ = prb 2

¬⊢Nᵃ∅-abst : ∀ {Γ A} → ¬ ((unmasked abst ∷ Δ✦) ∣ Γ ⊢ Nᵃ∅ ⦂ A)
¬⊢Nᵃ∅-abst (⊢ƛ _ (⊢·[] _ (wf-var (_ , es (es ()) , _))))

¬⊢Nᵃ∅-bind : ∀ {Γ A} → ¬ ((unmasked (bind `ℕ) ∷ Δ✦) ∣ Γ ⊢ Nᵃ∅ ⦂ A)
¬⊢Nᵃ∅-bind (⊢ƛ _ (⊢·[] _ (wf-var (_ , es (es ()) , _))))

stepᵃ∅ : Δ✦ ⊢ (Λ Nᵃ∅) ·[ (`ℕ ⇒ `ℕ) , `ℕ ]
           -→ Nᵃ∅ ⟪ morph (`ℕ ∷ []) [] , reveal 0 (`ℕ ⇒ `ℕ) ⟫
stepᵃ∅ = TyBeta val-prb

------------------------------------------------------------------------
-- §15b  TYPEELR — the value moves one bind deeper, and its `wkᴹ` shift
--       tracks it
------------------------------------------------------------------------

-- `V` moves from `interior Θ Δ` into
-- `interior (morph (A ∷ binds Θ) (changes Θ)) Δ`, which is
-- that type context with ONE binder prepended — and the rule shifts `V`
-- by `wkᴹ 1` to match.  A slot Θ MASKS is therefore masked on both
-- sides, one index apart.
--
--   showTCtx Δᵇ                                   =  X := ℕ
--   showTCtxAt 9 0 (λ _ → "X") Ξb                 =  ⌷[X := ℕ]
--   showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξb′  =  Y := ℕ , ⌷[X := ℕ]

Δᵇ : Ctxᵗ
Δᵇ = unmasked (bind `ℕ) ∷ []

Θᵇ : CtxMorph
Θᵇ = morph [] (lock 0 ∷ [])

_ : interior Θᵇ Δᵇ ≡ masked (bind `ℕ) ∷ []
_ = refl

_ : convCtx Θᵇ Δᵇ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

Vᵇ : Term
Vᵇ = prb 0

-- showTmIn 1 Rᵇ  =
--   ((λx:ℕ. (ΛY. 3) [X]) ⟪ ↓X , (∀Y. id ℕ) ⟫) [ℕ]
Rᵇ : Term
Rᵇ = (Vᵇ ⟪ Θᵇ , `∀ (id `ℕ) ⟫) ·[ `ℕ , `ℕ ]

¬⊢Vᵇ-int : ∀ {Γ A} → ¬ ((masked (bind `ℕ) ∷ []) ∣ Γ ⊢ Vᵇ ⦂ A)
¬⊢Vᵇ-int (⊢ƛ _ (⊢·[] _ (wf-var (_ , ez , ()))))

¬⊢Rᵇ : ∀ {A} → ¬ (Δᵇ ∣ [] ⊢ Rᵇ ⦂ A)
¬⊢Rᵇ (⊢·[] (env _ ⊢V _ _) _) = ¬⊢Vᵇ-int ⊢V

-- the rule's conversion-typing premise, read under one `abst`
⊢sᵇ : (unmasked abst ∷ convCtx Θᵇ Δᵇ) ⊢ id `ℕ ∶ `ℕ ⇝ `ℕ
⊢sᵇ = conv-id base-ℕ

-- showTmIn 1 Cᵇ  =
--   ((λx:ℕ. (ΛZ. 3) [X]) [Y] ⟪ ↑Y:=ℕ , ↓X , id ℕ ⟫)
Cᵇ : Term
Cᵇ = (wkᴹ 1 Vᵇ ·[ renameᵗ (extᵗ suc) `ℕ , ` 0 ])
       ⟪ morph (`ℕ ∷ binds Θᵇ) (changes Θᵇ) , instReveal 0 (id `ℕ) ⟫

stepᵇ : Δᵇ ⊢ Rᵇ -→ Cᵇ
stepᵇ = TyPeelR val-prb ⊢sᵇ

-- THE SHIFT AND THE FRAME MOVE TOGETHER: `wkᴹ 1` sends the fault from
-- slot 0 to slot 1, and `interior` puts the new binder at slot 0.
_ : wkᴹ 1 Vᵇ ≡ prb 1
_ = refl

_ : interior (morph (`ℕ ∷ binds Θᵇ) (changes Θᵇ)) Δᵇ
      ≡ unmasked (bind `ℕ) ∷ interior Θᵇ Δᵇ
_ = interior-TyPeelR `ℕ Θᵇ Δᵇ

_ : interior (morph (`ℕ ∷ binds Θᵇ) (changes Θᵇ)) Δᵇ
      ≡ unmasked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []
_ = refl

¬⊢wkVᵇ : ∀ {Γ A}
  → ¬ ((unmasked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []) ∣ Γ ⊢ prb 1 ⦂ A)
¬⊢wkVᵇ (⊢ƛ _ (⊢·[] _ (wf-var (_ , es ez , ()))))

¬⊢Cᵇ : ∀ {A} → ¬ (Δᵇ ∣ [] ⊢ Cᵇ ⦂ A)
¬⊢Cᵇ (env _ (⊢·[] ⊢V _) _ _) = ¬⊢wkVᵇ ⊢V

------------------------------------------------------------------------
-- §15c  IDPUSH and CANCELR — the scope move preserves the frame ON THE
--       NOSE
------------------------------------------------------------------------

-- Both rules move `V` from `interior Θ₁ (interior Θ₂ Δ)` to
-- `interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)`, and those two type
-- contexts are EQUAL (`interior-⋉-rewind`, proof/MoveScope) — so the
-- test is immediate, and it is immediate for EVERY `Θ₁`, `Θ₂` and `Δ`
-- with `Δ ⊢ᵐ Θ₂`, not just for the configuration below.  That is what
-- "the value's frame is preserved on the nose" means, and it is why
-- neither case uses `⊢retag`.
--
--   showTCtxAt 9 0 (λ { 0 → "X" ; _ → "Y" }) Δᶜ  =  X := ℕ , Y := ℕ
--   showTCtxAt 9 0 (λ { 0 → "Z" ; 1 → "X" ; _ → "Y" }) Ξc
--     =  Z := ℕ , X := ℕ , ⌷[Y := ℕ]

Δᶜ : Ctxᵗ
Δᶜ = unmasked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ []

Θᶜ₂ : CtxMorph
Θᶜ₂ = morph [] (lock 1 ∷ [])

Θᶜ₁ : CtxMorph
Θᶜ₁ = morph (`ℕ ∷ []) []

⊢ᵐΘᶜ₂ : Δᶜ ⊢ᵐ Θᶜ₂
⊢ᵐΘᶜ₂ = (mw rw[] (sw-l (unmasked (bind `ℕ) , es ez , nameable) sw[]))

-- the move, spelled out at this configuration
_ : _≡_ {A = CtxMorph} (Θᶜ₁ ⋉ Θᶜ₂) (morph (`ℕ ∷ []) (lock 1 ∷ []))
_ = refl

_ : _≡_ {A = CtxMorph} (rewind Θᶜ₂)
        (morph [] (unlock 1 ∷ lock 1 ∷ []))
_ = refl

_ : interior (rewind Θᶜ₂) Δᶜ ≡ Δᶜ
_ = refl

-- THE FRAME IDENTITY — an EQUALITY, so the test needs no example at all.
_ : interior (Θᶜ₁ ⋉ Θᶜ₂) (interior (rewind Θᶜ₂) Δᶜ)
      ≡ interior Θᶜ₁ (interior Θᶜ₂ Δᶜ)
_ = interior-⋉-rewind Θᶜ₁ Θᶜ₂ ⊢ᵐΘᶜ₂

Vᶜ : Term
Vᶜ = prb 2

_ : interior Θᶜ₁ (interior Θᶜ₂ Δᶜ)
      ≡ unmasked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []
_ = refl

-- V NAMES THE SLOT Θ₂ LOCKS (Y, exterior slot 1; interior slot 2 past
-- Θ₁'s binder Z).
¬⊢Vᶜ : ∀ {Γ A}
  → ¬ ((unmasked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ masked (bind `ℕ) ∷ [])
         ∣ Γ ⊢ Vᶜ ⦂ A)
¬⊢Vᶜ (⊢ƛ _ (⊢·[] _ (wf-var (_ , es (es ez) , ()))))

-- the lookup premise both rules carry
lkᶜ : convCtx Θᶜ₂ Δᶜ ∋ 0 := `ℕ
lkᶜ = ez

-- ── IDPUSH.  The name relation `X ≡ numBinds Θ₁ + Y` (`idpush-name`,
-- proof/IdLayer) forces `X = 1` here, so the redex below is the shape
-- the rule actually meets.
--
-- showTmIn 2 Rᶜ  =
--   (((λx:ℕ. (ΛX′. 3) [Y]) ⟪ ↑Z:=ℕ , id X ⟫) ⟪ ↓Y , unseal X ⟫)
Rᶜ : Term
Rᶜ = (Vᶜ ⟪ Θᶜ₁ , id (` 1) ⟫) ⟪ Θᶜ₂ , unseal 0 ⟫

¬⊢Rᶜ : ∀ {A} → ¬ (Δᶜ ∣ [] ⊢ Rᶜ ⦂ A)
¬⊢Rᶜ (env _ (env _ ⊢V _ _) _ _) = ¬⊢Vᶜ ⊢V

-- showTmIn 2 Cᶜ  =
--   (((λx:ℕ. (ΛX′. 3) [Y]) ⟪ ↑Z:=ℕ , ↓Y , unseal X ⟫)
--      ⟪ ↥Y , ↓Y , id ℕ ⟫)
Cᶜ : Term
Cᶜ = (Vᶜ ⟪ Θᶜ₁ ⋉ Θᶜ₂ , unseal 1 ⟫) ⟪ rewind Θᶜ₂ , mkId `ℕ ⟫

stepᶜ : Δᶜ ⊢ Rᶜ -→ Cᶜ
stepᶜ = IdPush val-prb lkᶜ

¬⊢Cᶜ : ∀ {A} → ¬ (Δᶜ ∣ [] ⊢ Cᶜ ⦂ A)
¬⊢Cᶜ (env _ (env _ ⊢V _ _) _ _) = ¬⊢Vᶜ ⊢V

-- ── CANCELR, at the same configuration (`cancel-name` forces the same
-- `X`).
--
-- showTmIn 2 Rᶜ′  =
--   (((λx:ℕ. (ΛX′. 3) [Y]) ⟪ ↑Z:=ℕ , seal X ⟫) ⟪ ↓Y , unseal X ⟫)
Rᶜ′ : Term
Rᶜ′ = (Vᶜ ⟪ Θᶜ₁ , seal 1 ⟫) ⟪ Θᶜ₂ , unseal 0 ⟫

¬⊢Rᶜ′ : ∀ {A} → ¬ (Δᶜ ∣ [] ⊢ Rᶜ′ ⦂ A)
¬⊢Rᶜ′ (env _ (env _ ⊢V _ _) _ _) = ¬⊢Vᶜ ⊢V

-- showTmIn 2 Cᶜ′  =
--   (((λx:ℕ. (ΛX′. 3) [Y]) ⟪ ↑Z:=ℕ , ↓Y , id ℕ ⟫) ⟪ ↥Y , ↓Y , id ℕ ⟫)
Cᶜ′ : Term
Cᶜ′ = (Vᶜ ⟪ Θᶜ₁ ⋉ Θᶜ₂ , mkId (shiftBy (numBinds Θᶜ₁) `ℕ) ⟫)
        ⟪ rewind Θᶜ₂ , mkId `ℕ ⟫

stepᶜ′ : Δᶜ ⊢ Rᶜ′ -→ Cᶜ′
stepᶜ′ = CancelR val-prb lkᶜ

¬⊢Cᶜ′ : ∀ {A} → ¬ (Δᶜ ∣ [] ⊢ Cᶜ′ ⦂ A)
¬⊢Cᶜ′ (env _ (env _ ⊢V _ _) _ _) = ¬⊢Vᶜ ⊢V

------------------------------------------------------------------------
-- §15d  BETA — and the ONE EXPECTED EXCEPTION
------------------------------------------------------------------------

-- `Beta` changes no frame WHERE NO BINDER IS CROSSED: `N [ W ∶ A ]ᵐ` is
-- read at the redex's own `Δ`, so an argument the exterior refuses is
-- refused wherever it lands, and the frame identity is the identity
-- function.  WHERE A `Λ` IS CROSSED the frame is not Δ but `masked abst ∷
-- Δ` — `interior-Beta-Λ` above — which is EXACT rather than trivial, and
-- is the case §15d₂ below runs.

Wᵈ : Term
Wᵈ = prb 0

¬⊢Wᵈ : ∀ {Γ A} → ¬ (Δ✦ ∣ Γ ⊢ Wᵈ ⦂ A)
¬⊢Wᵈ (⊢ƛ _ (⊢·[] _ (wf-var (_ , ez , ()))))

-- showTmIn 1 Rᵈ  =
--   ((λx:(ℕ⇒ℕ). x) · (λx:ℕ. (ΛY. 3) [X]))
Rᵈ : Term
Rᵈ = (ƛ (`ℕ ⇒ `ℕ) ∙ (` 0)) · Wᵈ

¬⊢Rᵈ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Rᵈ ⦂ A)
¬⊢Rᵈ (⊢· _ ⊢W) = ¬⊢Wᵈ ⊢W

-- showTmIn 1 Cᵈ  =  (λx:ℕ. (ΛY. 3) [X])
Cᵈ : Term
Cᵈ = (` 0) [ Wᵈ ∶ `ℕ ⇒ `ℕ ]ᵐ

_ : Cᵈ ≡ Wᵈ
_ = refl

stepᵈ : Δ✦ ⊢ Rᵈ -→ Cᵈ
stepᵈ = Beta val-prb

¬⊢Cᵈ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Cᵈ ⦂ A)
¬⊢Cᵈ = ¬⊢Wᵈ

-- ── THE ERASURE EXCEPTION, RECORDED.  Substitution may DROP its
-- argument, and then an ill-typed redex has a WELL-TYPED contractum.
-- This is NOT a scope gain: nothing MOVED into a new frame — the
-- offending subterm was DELETED, and what remains was already typed
-- inside the redex.  The test is about what happens to a subterm that
-- CROSSES into another frame, and an erased subterm crosses nowhere.
-- (Every other rule in the table moves its subterm; `Beta` is the only
-- one that can discard one.)
--
-- showTmIn 1 Rᵈ′  =  ((λx:(ℕ⇒ℕ). 3) · (λx:ℕ. (ΛY. 3) [X]))
Rᵈ′ : Term
Rᵈ′ = (ƛ (`ℕ ⇒ `ℕ) ∙ ($ 3)) · Wᵈ

¬⊢Rᵈ′ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Rᵈ′ ⦂ A)
¬⊢Rᵈ′ (⊢· _ ⊢W) = ¬⊢Wᵈ ⊢W

stepᵈ′ : Δ✦ ⊢ Rᵈ′ -→ ($ 3)
stepᵈ′ = Beta val-prb

⊢Cᵈ′ : Δ✦ ∣ [] ⊢ ($ 3) ⦂ `ℕ
⊢Cᵈ′ = ⊢$

------------------------------------------------------------------------
-- §15d₂  BETA UNDER A Λ — THE FRAME-EXACT CASE
------------------------------------------------------------------------

-- THE CASE THE TEST HAD NO INSTANCE OF, because before 2026-09-08 there
-- was nothing to test: the argument was SHIFTED under the Λ and read at
-- the Λ's own frame, one entry WIDER than its birth frame.  Now it is
-- wrapped in the crossed binder's DUAL, and the frame it is read at is
-- `interior-Beta-Λ Δ✦` — Δ✦ with the crossed slot masked, i.e. exactly
-- its birth frame.  The verdict is the one the test wants: the argument
-- names a slot Δ✦ MASKS, and it is refused inside for that same reason.

Nᵈ Rᵈ↑ Cᵈ↑ : Term
Nᵈ  = Λ (` 0)                    -- ΛY. x — the body that crosses a Λ
Rᵈ↑ = (ƛ (`ℕ ⇒ `ℕ) ∙ Nᵈ) · Wᵈ
Cᵈ↑ = Nᵈ [ Wᵈ ∶ `ℕ ⇒ `ℕ ]ᵐ

-- the contractum: the shifted probe under ΛY's dual, at the identity
-- conversion its type gives (`mkId (`ℕ ⇒ `ℕ)`).
_ : Cᵈ↑ ≡ Λ (prb 1 ⟪ morph [] (lock 0 ∷ []) , id `ℕ ↦ id `ℕ ⟫)
_ = refl

¬⊢Rᵈ↑ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Rᵈ↑ ⦂ A)
¬⊢Rᵈ↑ (⊢· _ ⊢W) = ¬⊢Wᵈ ⊢W

stepᵈ↑ : Δ✦ ⊢ Rᵈ↑ -→ Cᵈ↑
stepᵈ↑ = Beta val-prb

-- THE FRAME IDENTITY, at this Δ — W's BIRTH FRAME, SHIFTED, EXACT.
_ : interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ✦)
      ≡ masked abst ∷ Δ✦
_ = interior-Beta-Λ Δ✦

-- … so the shifted argument is refused inside, and for the SAME
-- localized reason: slot 1 is the masked binder it names.
¬⊢shiftWᵈ : ∀ {Γ A} → ¬ ((masked abst ∷ Δ✦) ∣ Γ ⊢ prb 1 ⦂ A)
¬⊢shiftWᵈ (⊢ƛ _ (⊢·[] _ (wf-var (_ , es ez , ()))))

¬⊢Cᵈ↑ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Cᵈ↑ ⦂ A)
¬⊢Cᵈ↑ (⊢Λ (env _ ⊢W _ _)) = ¬⊢shiftWᵈ ⊢W

-- AND THE CROSSED Λ'S OWN SLOT IS NOT NAMEABLE INSIDE EITHER — which is
-- what "the frame gained nothing" means, stated as a refusal.
¬∋tv-crossΛ : ¬ (interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ✦)
                   ∋tv 0)
¬∋tv-crossΛ (_ , ez , ())

------------------------------------------------------------------------
-- §15e  PEEL — the `bind` half, and `hideBinds`
------------------------------------------------------------------------

-- The `unlock` half is proof/DualTightness: the exterior masks X, `Θ`
-- UNLOCKS it, and the contractum used to type.  It is closed there by
-- the restoring, reversed `dualScope`, and `¬⊢Contractum` is the
-- machine-checked verdict.
--
-- HERE IS THE OTHER HALF.  `Θ` carries a BIND, so the crossing frame is
-- the exterior under a MASKED bind prefix — (†) `interior-dual`,
-- proof/PeelDual — and the rule shifts the argument by
-- `wkᴹ (numBinds Θ)` to land past it.  Two facts have to hold at once,
-- and both do: a slot the EXTERIOR masks stays masked one index in, and
-- the boundary's OWN binder, which did not exist at the exterior, is
-- MASKED by `hideBinds` rather than handed to the argument.
--
--   showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξe  =  ⌷[Y := ℕ] , ⌷[X := ℕ]

Θᵉ : CtxMorph
Θᵉ = morph (`ℕ ∷ []) []

⊢ᵐΘᵉ : Δ✦ ⊢ᵐ Θᵉ
⊢ᵐΘᵉ = (mw (rw-b wf-ℕ rw[]) sw[])

Vᵉ : Term
Vᵉ = ƛ `ℕ ∙ (` 0)

Wᵉ : Term
Wᵉ = prb 0

-- showTmIn 1 Rᵉ  =
--   (((λx:ℕ. x) ⟪ ↑Y:=ℕ , (id ℕ ↦ id ℕ) ⟫) · (λx:ℕ. (ΛZ. 3) [X]))
Rᵉ : Term
Rᵉ = (Vᵉ ⟪ Θᵉ , id `ℕ ↦ id `ℕ ⟫) · Wᵉ

¬⊢Rᵉ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Rᵉ ⦂ A)
¬⊢Rᵉ (⊢· _ ⊢W) = ¬⊢Wᵈ ⊢W

-- showTmIn 1 Cᵉ  =
--   (((λx:ℕ. x) · ((λx:ℕ. (ΛZ. 3) [X]) ⟪ ↓Y , id ℕ ⟫))
--      ⟪ ↑Y:=ℕ , id ℕ ⟫)
Cᵉ : Term
Cᵉ = (Vᵉ · (wkᴹ (numBinds Θᵉ) Wᵉ ⟪ dual Θᵉ , id `ℕ ⟫)) ⟪ Θᵉ , id `ℕ ⟫

stepᵉ : Δ✦ ⊢ Rᵉ -→ Cᵉ
stepᵉ = Peel V-ƛ val-prb

-- THE DUAL LOCKS THE BOUNDARY'S OWN BINDER …
_ : _≡_ {A = CtxMorph} (dual Θᵉ) (morph [] (lock 0 ∷ []))
_ = refl

-- … so (†) reads, at this Θ: the crossing frame is Δ✦ under one MASKED
-- bind.
_ : interior (dual Θᵉ) (interior Θᵉ Δ✦)
      ≡ map maskEnt (pushBinds (binds Θᵉ) []) ++ Δ✦
_ = interior-dual Θᵉ Δ✦ ⊢ᵐΘᵉ

_ : interior (dual Θᵉ) (interior Θᵉ Δ✦)
      ≡ masked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []
_ = refl

_ : wkᴹ (numBinds Θᵉ) Wᵉ ≡ prb 1
_ = refl

¬⊢wkWᵉ : ∀ {Γ A}
  → ¬ ((masked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []) ∣ Γ ⊢ prb 1 ⦂ A)
¬⊢wkWᵉ (⊢ƛ _ (⊢·[] _ (wf-var (_ , es ez , ()))))

¬⊢Cᵉ : ∀ {A} → ¬ (Δ✦ ∣ [] ⊢ Cᵉ ⦂ A)
¬⊢Cᵉ (env _ (⊢· _ (env _ ⊢W _ _)) _ _) = ¬⊢wkWᵉ ⊢W

-- THE `hideBinds` HALF, in two pieces.  First: the boundary's own
-- binder sits at slot 0 of the crossing frame and is NOT nameable there.
¬∋tv-hideBinds : ¬ (interior (dual Θᵉ) (interior Θᵉ Δ✦) ∋tv 0)
¬∋tv-hideBinds (_ , ez , ())

-- Second: an argument naming a slot that does NOT EXIST at the exterior
-- is shifted by `wkᴹ` and still names no slot — the bind prefix is
-- masked, so it is not a landing place.  (Not rendered, for the reason
-- given in §15a.)
Wᵉ∅ : Term
Wᵉ∅ = prb 1

¬⊢Wᵉ∅ : ∀ {Γ A} → ¬ (Δ✦ ∣ Γ ⊢ Wᵉ∅ ⦂ A)
¬⊢Wᵉ∅ (⊢ƛ _ (⊢·[] _ (wf-var (_ , es () , _))))

stepᵉ∅ : Δ✦ ⊢ (Vᵉ ⟪ Θᵉ , id `ℕ ↦ id `ℕ ⟫) · Wᵉ∅
           -→ (Vᵉ · (wkᴹ (numBinds Θᵉ) Wᵉ∅ ⟪ dual Θᵉ , id `ℕ ⟫))
                ⟪ Θᵉ , id `ℕ ⟫
stepᵉ∅ = Peel V-ƛ val-prb

_ : wkᴹ (numBinds Θᵉ) Wᵉ∅ ≡ prb 2
_ = refl

¬⊢wkWᵉ∅ : ∀ {Γ A}
  → ¬ ((masked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []) ∣ Γ ⊢ prb 2 ⦂ A)
¬⊢wkWᵉ∅ (⊢ƛ _ (⊢·[] _ (wf-var (_ , es (es ()) , _))))

------------------------------------------------------------------------
-- §15f  THE FRAMES ARE PRESERVED — what makes §15 a theorem
------------------------------------------------------------------------

-- Each example above exhibits, at one point, an identity that holds
-- everywhere.  Collected, with the rule each one serves:
--
--   TyBeta   interior (morph (A ∷ []) []) Δ ≡ bind A ∷ Δ
--              — `Δ` on the nose, one REFINEMENT (abst → bind) at the
--                slot the rule is there to reveal
--   TyPeelR  interior (morph (A ∷ binds Θ) (changes Θ)) Δ
--              ≡ bind (shiftBy (numBinds Θ) A) ∷ interior Θ Δ
--              — the redex's frame, one binder in; `wkᴹ 1` matches it
--   Peel     interior (dual Θ) (interior Θ Δ)
--              ≡ map masked (pushBinds (binds Θ) []) ++ Δ   (Δ ⊢ᵐ Θ)
--              — (†), proof/PeelDual.interior-dual: THE CROSSING FRAME
--                IS THE EXTERIOR, under a MASKED bind prefix
--   CancelR  interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)
--   IdPush     ≡ interior Θ₁ (interior Θ₂ Δ)                 (Δ ⊢ᵐ Θ₂)
--              — proof/MoveScope.interior-⋉-rewind: preserved ON THE
--                NOSE, which is why neither case uses `⊢retag`
--   Beta     Δ ≡ Δ where no binder is crossed; the exception is ERASURE
--              (§15d)
--   Beta,    interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ)
--   under Λ    ≡ masked abst ∷ Δ
--              — `interior-Beta-Λ`: the image's BIRTH frame with the
--                crossed Λ's slot masked.  This is the identity
--                frame-exact Beta buys (2026-09-08); before it the image
--                was read at `unmasked abst ∷ Δ`, one entry WIDER than
--                the frame it was born in — sound, because its shifted
--                indices cannot reach slot 0, but not exact.  §15d₂ runs
--                the test on it.
--
-- `Drop$` and the five congruences move nothing into a new frame:
-- `Drop$`'s contractum is a numeral, and each `ξ` rule reduces a
-- subterm IN PLACE, at the frame the rule's own premise reads it on.
--
-- The three identities that had no name are `interior-TyBeta`,
-- `interior-TyPeelR` and `interior-Beta-Λ` at the head of this section;
-- all three are `refl`,
-- because `interior` is `pushBinds ∘ binds` over `scope` and a bind
-- entry touches `scope` not at all.  The other two are theorems with
-- a `Δ ⊢ᵐ Θ` premise, and that premise is exactly where the sequential
-- judgement pays: (†) needs `sw-u`'s LOCKED slot for the dual's
-- restoring `lock` to be `mask ∘ unmask` at that slot (`mask-unmask`,
-- strong.Ctx §6b), and the scope move needs the rep half read past the
-- tail's unlocks (proof/MwUObstruct §4).

------------------------------------------------------------------------
-- §16  THE CHANGE LISTS, MEASURED — `E₀` INSTANTIATED AND APPLIED
------------------------------------------------------------------------

-- THE PROGRAM (Jeremy, 2026-09-08).  §14's `E₀` runs to a VALUE of type
-- `∀Y. Y ⇒ Y` in five steps; instantiate it once more and APPLY it, and
-- the run continues through the whole scope-move machinery — four
-- crossings (`Peel`), a `CancelR`/`IdPush` cascade, and eight `Drop$`
-- layers — to the numeral 42, in 36 steps:
--
--   F₀ = (E₀ ·[ ` 0 ⇒ ` 0 , `ℕ ]) · $ 42                          : ℕ
--
--   TyBeta Peel Beta TyPeelR TyBeta TyPeelR TyBeta
--   Peel Peel Peel Peel Beta
--   CancelR IdPush IdPush CancelR IdPush IdPush IdPush IdPush
--   CancelR IdPush IdPush IdPush IdPush IdPush IdPush CancelR
--   Drop$ Drop$ Drop$ Drop$ Drop$ Drop$ Drop$ Drop$
--
-- THIS IS THE RUN THAT MEASURES THE CHANGE-LIST BLOWUP.  Every
-- `CancelR`/`IdPush` replays the outer frame's changes (`rewind Θ₂`) and
-- moves them into the inner frame (`Θ₁ ⋉ Θ₂`), and BOTH used to copy a
-- list that already carried the same entries, so the lists roughly
-- DOUBLED at every pass.  The peak state carried, at one boundary,
--
--   ↥4 ↧4 ↥4 ↧4 ↥4 ↧4 ↥4 ↧4 ↥4 ↥0 ↧0 ↧4 ↥4 ↥0 ↧0 ↧4 …
--
-- 130 entries of it, and 389 change entries across the whole state.
--
-- WITH THE TWO REDUNDANCY TESTS (strong.CtxMorph §4) the peak is 50 and
-- 101, and neither the step count nor the answer moves:
--
--   longest change list at one boundary   130 → 50
--   change entries in one state           389 → 101
--   steps                                  36 = 36
--   answer                                  42 = 42
--
-- The residue is NOT a replay and NOT a duplicate: it is the merge of two
-- lists that unlock DIFFERENT slots, which no exact rewriting can shrink
-- (proof/RewindNorm §2).  Bounding it needs the CANONICAL per-slot form —
-- at most three entries per slot mentioned, so at most 15 on this run,
-- where at most five slots are ever named — and the two facts that form
-- still lacks are stated in proof/RewindNorm §4.
--
-- The measurements below are `refl`, so they are pinned: a frame redesign
-- that changes them fails this section.

F₀ : Term
F₀ = (E₀ ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 42)

⊢F₀ : [] ∣ [] ⊢ F₀ ⦂ `ℕ
⊢F₀ = ⊢· (⊢·[] ⊢E₀ wf-ℕ) ⊢$

open import strong.Eval using (eval; traceTerms; traceLen; traceEnd)
open import Data.Nat using (_⊔_)
open import Data.List using (foldr)

-- The longest change list at any one boundary of a term, and the total
-- number of change entries in it.
maxChanges sumChanges : Term → ℕ
maxChanges (` x)          = 0
maxChanges ($ n)          = 0
maxChanges (ƛ A ∙ N)      = maxChanges N
maxChanges (L · M)        = maxChanges L ⊔ maxChanges M
maxChanges (Λ N)          = maxChanges N
maxChanges (L ·[ B , A ]) = maxChanges L
maxChanges (M ⟪ Θ , c ⟫)  = length (changes Θ) ⊔ maxChanges M

sumChanges (` x)          = 0
sumChanges ($ n)          = 0
sumChanges (ƛ A ∙ N)      = sumChanges N
sumChanges (L · M)        = sumChanges L + sumChanges M
sumChanges (Λ N)          = sumChanges N
sumChanges (L ·[ B , A ]) = sumChanges L
sumChanges (M ⟪ Θ , c ⟫)  = length (changes Θ) + sumChanges M

peak : (Term → ℕ) → List Term → ℕ
peak f Ms = foldr (λ M n → f M ⊔ n) 0 Ms

-- 36 STEPS TO 42.
_ : traceLen (eval 40 ⊢F₀) ≡ 36
_ = refl

_ : traceEnd (eval 40 ⊢F₀) ≡ $ 42
_ = refl

-- THE TWO MEASUREMENTS.  Before the redundancy tests these were 130 and
-- 389.
_ : peak maxChanges (traceTerms (eval 40 ⊢F₀)) ≡ 50
_ = refl

_ : peak sumChanges (traceTerms (eval 40 ⊢F₀)) ≡ 101
_ = refl

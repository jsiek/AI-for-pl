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
-- §7  two regressions on substᵐ; §8 progress on §6; §9 preservation on §6.
-- §10 IdPush — the reachability verdict of proof/IdPushReach.
-- §11 IDPUSH FROM CLOSED, PLAIN SOURCE — the run `Q` Jeremy asked for,
--     plus the three variants: (ii) a CHAINED face rep (`R`), (iii)
--     IdPush firing TWICE (`D`), and (i) a multi-bind Θ₁, which turns out
--     to be reachable only through TyPeelR — whose contractum is here
--     refuted from closed source for the first time (`G`).
-- §12 the WALL, probed for reachability post-Peel-repair (`L`): the
--     c10/c11 blocked type context IS reached from closed source, but in
--     a Θ₁ position, never as the Θ₂ a rule reads a rep out of.
-- §13 TYPEELR FROM CLOSED, PLAIN SOURCE, at both faces: `J` (a CONCEAL
--     ∀-face, the polymorphic argument) runs to its answer 3 through the
--     TyPeelR contractum the retired polarity index used to refuse, `H`
--     is the REVEAL mirror, and §13c records the contracta weighed
--     against the landed rule.
-- §14 THE PRE-BOUNDARY COUNTEREXAMPLE: `E`, the closed program that
--     refuted the per-variable design (v1's historical Example 8), run
--     in v2 to a VALUE — the step that used to produce an ill-typed
--     term is `estep₄`, and `E-int`/`E-ext` are its two type contexts.
--
-- Every `_ : … ≡ …` in this file is a machine-checked frame computation.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
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
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- §1  T₆ — the transparent layer, and its run to 7
------------------------------------------------------------------------

-- T₆ = ((7 ⟪ [] , seal 1 ⟫) ⟪ bind ℕ , id (` 1) ⟫) ⟪ bind ℕ , unseal 0 ⟫
-- typed at ℕ, not a value, and — before IdPush — no rule fired: Cancel
-- wanted a seal-topped interior, Drop$ a base face, ξ-⟪⟫ a stepping
-- interior.  The middle wrapper is the "transparent layer".

Δ₆ S₆₁ S₆₂ : Ctxᵗ
Δ₆  = bind `ℕ ∷ []
S₆₁ = bind `ℕ ∷ Δ₆
S₆₂ = bind `ℕ ∷ S₆₁

W₆₀ W₆₁ T₆ : Term
W₆₀ = ($ 7) ⟪ [] , seal 1 ⟫
W₆₁ = W₆₀ ⟪ bind `ℕ ∷ [] , id (` 1) ⟫
T₆  = W₆₁ ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

⊢W₆₀ : S₆₂ ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀ = env mw[] ⊢$ (conv-seal (es ez))
           (wf-var (bind `ℕ , es ez , nameable-b))

⊢W₆₁ : S₆₁ ∣ [] ⊢ W₆₁ ⦂ ` 0
⊢W₆₁ = env (mw-b wf-ℕ mw[]) ⊢W₆₀
           (conv-idv (bind `ℕ , es ez , nameable-b))
           (wf-var (bind `ℕ , ez , nameable-b))

⊢T₆ : Δ₆ ∣ [] ⊢ T₆ ⦂ `ℕ
⊢T₆ = env (mw-b wf-ℕ mw[]) ⊢W₆₁ (conv-unseal ez) wf-ℕ

¬val-T₆ : ¬ Value T₆
¬val-T₆ (V-⟪⟫ _ ())

-- STEP 1 — IDPUSH.  The two FACES are swapped; both frames are untouched.
-- The pushed name `1` is the id-face's bind variable (proof/IdLayer.agda,
-- `idpush-name`), and the residue face is the identity at the LOOKED-UP
-- rep — the lookup premise, exactly as ruled.
T₆-1 : Term
T₆-1 = (W₆₀ ⟪ bind `ℕ ∷ [] , unseal 1 ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

push-T₆ : Δ₆ ⊢ T₆ -→ T₆-1
push-T₆ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢T₆-1-in : S₆₁ ∣ [] ⊢ W₆₀ ⟪ bind `ℕ ∷ [] , unseal 1 ⟫ ⦂ `ℕ
⊢T₆-1-in = env (mw-b wf-ℕ mw[]) ⊢W₆₀ (conv-unseal (es ez)) wf-ℕ

⊢T₆-1 : Δ₆ ∣ [] ⊢ T₆-1 ⦂ `ℕ
⊢T₆-1 = env (mw-b wf-ℕ mw[]) ⊢T₆-1-in (conv-id base-ℕ) wf-ℕ

-- STEP 2 — the seal/unseal pair is now ADJACENT: the ordinary cancel
-- fires.  BOTH FRAMES STAY (the repaired rule) and both faces become the
-- identity at the looked-up rep, so the seal's own (here empty) frame
-- survives as one more transparent layer.
T₆-2 : Term
T₆-2 = ((($ 7) ⟪ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫)
         ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

cancel-T₆ : Δ₆ ⊢ T₆-1 -→ T₆-2
cancel-T₆ = ξ-⟪⟫ (CancelR V-$ (es ez))

⊢T₆-2-in : S₆₁ ∣ [] ⊢ ($ 7) ⟪ [] , id `ℕ ⟫ ⟪ bind `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢T₆-2-in = env (mw-b wf-ℕ mw[])
                (env mw[] ⊢$ (conv-id base-ℕ) wf-ℕ)
                (conv-id base-ℕ) wf-ℕ

⊢T₆-2 : Δ₆ ∣ [] ⊢ T₆-2 ⦂ `ℕ
⊢T₆-2 = env (mw-b wf-ℕ mw[]) ⊢T₆-2-in (conv-id base-ℕ) wf-ℕ

-- STEPS 3, 4, 5 — base faces over a numeral, innermost first.
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

-- (7 ⟪ ↓X , seal 0 ⟫) ⟪ ↑X:=ℕ , unseal 0 ⟫ — outer face ACTIVE, inner face
-- INERT, read straight off the conversion constructors.

Θ↑ Θ↓ : CtxMorph
Θ↑ = bind `ℕ ∷ []
Θ↓ = lock 0 ∷ []

cancelTm : Term
cancelTm = (($ 7) ⟪ Θ↓ , seal 0 ⟫) ⟪ Θ↑ , unseal 0 ⟫

⊢cancelTm : [] ∣ [] ⊢ cancelTm ⦂ `ℕ
⊢cancelTm =
  env (mw-b wf-ℕ mw[])
      (env (mw-l (_ , ez , nameable-b) mw[]) ⊢$
           (conv-seal ez) (wf-var (_ , ez , nameable-b)))
      (conv-unseal ez)
      wf-ℕ

-- the pair is NOT a value (the outer face is active) and the cancel
-- fires.  BOTH FRAMES STAY and both faces become the identity at the
-- looked-up rep (the repaired rule): nothing that `V` might name is
-- dropped, and the mini-core's extra `hideBinds` — which masked an
-- exterior slot that does not exist (proof/MaskFacts `¬MorphWf-cancel-residue`)
-- — is gone for good.
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
LA = (($ 7) ⟪ [] , seal 2 ⟫) ⟪ bind (` 0) ∷ [] , id (` 2) ⟫
LB = LA ⟪ bind `ℕ ∷ [] , id (` 1) ⟫
T₈ = LB ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

SA : Ctxᵗ
SA = bind (` 0) ∷ S₆₂            -- the interior type context of LA

⊢LA-in : SA ∣ [] ⊢ ($ 7) ⟪ [] , seal 2 ⟫ ⦂ ` 2
⊢LA-in = env mw[] ⊢$ (conv-seal (es (es ez)))
             (wf-var (bind `ℕ , es (es ez) , nameable-b))

⊢LA : S₆₂ ∣ [] ⊢ LA ⦂ ` 1
⊢LA = env (mw-b (wf-var (bind `ℕ , ez , nameable-b)) mw[]) ⊢LA-in
          (conv-idv (bind `ℕ , es (es ez) , nameable-b))
          (wf-var (bind `ℕ , es ez , nameable-b))

⊢LB : S₆₁ ∣ [] ⊢ LB ⦂ ` 0
⊢LB = env (mw-b wf-ℕ mw[]) ⊢LA
          (conv-idv (bind `ℕ , es ez , nameable-b))
          (wf-var (bind `ℕ , ez , nameable-b))

⊢T₈ : Δ₆ ∣ [] ⊢ T₈ ⦂ `ℕ
⊢T₈ = env (mw-b wf-ℕ mw[]) ⊢LB (conv-unseal ez) wf-ℕ

-- The stack resolves ONE LAYER PER STEP, outermost first: each IdPush moves
-- the active face one layer inward toward the seal, so any depth
-- terminates.  (IdAbsorb needed `⊳` to merge the frames and could not do
-- this one — the inner layer's context morphism `bind (` 0)` names the next layer's
-- owner, IdLayerProbe §4c.  IdPush touches no frame.)
T₈-1 T₈-2 T₈-3 : Term
T₈-1 = (LA ⟪ bind `ℕ ∷ [] , unseal 1 ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
T₈-2 = (((($ 7) ⟪ [] , seal 2 ⟫) ⟪ bind (` 0) ∷ [] , unseal 2 ⟫)
          ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
T₈-3 = (((($ 7) ⟪ [] , id `ℕ ⟫) ⟪ bind (` 0) ∷ [] , id `ℕ ⟫)
          ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

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
-- variable: `reveal 0 (` 1)` is the identity face, and the owner it binds
-- is never read.
_ : reveal 0 (` 1) ≡ id (` 1)
_ = refl

⊢W₆₀Λ : (abst ∷ S₆₁) ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀Λ = env mw[] ⊢$ (conv-seal (es ez))
            (wf-var (bind `ℕ , es ez , nameable-b))

Pkg : Term
Pkg = (Λ W₆₀) ⟪ [] , `∀ (id (` 1)) ⟫

⊢Pkg : S₆₁ ∣ [] ⊢ Pkg ⦂ `∀ (` 1)
⊢Pkg = env mw[] (⊢Λ ⊢W₆₀Λ)
           (conv-all (conv-idv (bind `ℕ , es ez , nameable-b)))
           (wf-∀ (wf-var (bind `ℕ , es ez , nameable-b)))

T₉ : Term
T₉ = (Pkg ·[ ` 1 , `ℕ ]) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

⊢T₉ : Δ₆ ∣ [] ⊢ T₉ ⦂ `ℕ
⊢T₉ = env (mw-b wf-ℕ mw[]) (⊢·[] ⊢Pkg wf-ℕ) (conv-unseal ez) wf-ℕ

-- TyPeelR mints the id-layer no matter what TyBeta does.  On an IDENTITY
-- ∀-face the minted face is the face itself (`instReveal 0 (id (` 1)) =
-- id (` 1)`, since slot 1 is not the new owner) and the pushed-in
-- annotation is the interior ∀-body, SHIFTED past the owner the rule
-- binds: `` ` 2 `` rather than `` ` 1 ``.
Pk-1 : Term
Pk-1 = ((Λ (($ 7) ⟪ [] , seal 2 ⟫)) ·[ ` 2 , ` 0 ])
         ⟪ bind `ℕ ∷ [] , id (` 1) ⟫

⊢Pk-face : (abst ∷ exterior [] S₆₁) ⊢ id (` 1) ∶ ` 1 ⇝ ` 1
⊢Pk-face = conv-idv (bind `ℕ , es ez , nameable-b)

typeel-T₉ : Δ₆ ⊢ T₉ -→ Pk-1 ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
typeel-T₉ = ξ-⟪⟫ (TyPeelR (V-Λ (V-⟪⟫ V-$ I-seal)) ⊢Pk-face)

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
                -→ ($ 1) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
then-tybeta = TyBeta V-$

run-Ωt : [] ⊢ Ωt ·[ `ℕ , `ℕ ] -→* $ 1
run-Ωt = body-first then then-tybeta then Drop$ base-ℕ then done

------------------------------------------------------------------------
-- §4  The two adversaries `⊳` could not clear
------------------------------------------------------------------------

-- ── Tᵣ (IdLayerProbe §4c): the id-layer's context morphism carries a rep that
-- NAMES the outer boundary's owner.  Merging the frames would have to
-- SUBSTITUTE reps into reps — rep arithmetic, i.e. the retired `⊕`.
-- IdPush touches no frame, so the instance is ordinary.

Θᵣ₁ Θᵣ₂ : CtxMorph
Θᵣ₁ = bind (` 0) ∷ []
Θᵣ₂ = bind `ℕ ∷ []

Sᵣ : Ctxᵗ
Sᵣ = bind (` 0) ∷ bind `ℕ ∷ []

Vᵣ Tᵣ : Term
Vᵣ = ($ 7) ⟪ [] , seal 1 ⟫
Tᵣ = (Vᵣ ⟪ Θᵣ₁ , id (` 1) ⟫) ⟪ Θᵣ₂ , unseal 0 ⟫

_ : interior Θᵣ₁ (interior Θᵣ₂ []) ≡ Sᵣ
_ = refl

⊢Vᵣ : Sᵣ ∣ [] ⊢ Vᵣ ⦂ ` 1
⊢Vᵣ = env mw[] ⊢$ (conv-seal (es ez)) (wf-var (bind `ℕ , es ez , nameable-b))

⊢Tᵣ : [] ∣ [] ⊢ Tᵣ ⦂ `ℕ
⊢Tᵣ = env (mw-b wf-ℕ mw[])
          (env (mw-b (wf-var (bind `ℕ , ez , nameable-b)) mw[]) ⊢Vᵣ
               (conv-idv (bind `ℕ , es ez , nameable-b))
               (wf-var (bind `ℕ , ez , nameable-b)))
          (conv-unseal ez) wf-ℕ

push-Tᵣ : [] ⊢ Tᵣ -→ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫
push-Tᵣ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢push-Tᵣ : [] ∣ [] ⊢ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tᵣ = env (mw-b wf-ℕ mw[])
               (env (mw-b (wf-var (bind `ℕ , ez , nameable-b)) mw[]) ⊢Vᵣ
                    (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tᵣ : [] ⊢ Tᵣ -→* $ 7
run-Tᵣ = push-Tᵣ
    then ξ-⟪⟫ (CancelR V-$ (es ez))
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── Tₘ (IdLayerProbe §4b): Θ₂ re-exposes a masked slot (`unlock 0`) and the
-- id-layer masks it again (`lock 0`).  The merged context morphism computed both
-- type contexts correctly and yet `MorphWf` refused it, because `MorphWf`
-- checks every entry against the PLAIN exterior.  Again: IdPush merges nothing.

Δₘ Mₘ : Ctxᵗ
Δₘ = masked (bind `𝔹) ∷ bind `ℕ ∷ []
Mₘ = bind `𝔹 ∷ bind `ℕ ∷ []

Θₘ₁ Θₘ₂ : CtxMorph
Θₘ₁ = lock 0 ∷ []
Θₘ₂ = unlock 0 ∷ []

Vₘ Tₘ : Term
Vₘ = ($ 7) ⟪ [] , seal 1 ⟫
Tₘ = (Vₘ ⟪ Θₘ₁ , id (` 1) ⟫) ⟪ Θₘ₂ , unseal 1 ⟫

_ : interior Θₘ₂ Δₘ ≡ Mₘ
_ = refl

⊢Vₘ : Δₘ ∣ [] ⊢ Vₘ ⦂ ` 1
⊢Vₘ = env mw[] ⊢$ (conv-seal (es ez)) (wf-var (bind `ℕ , es ez , nameable-b))

⊢Tₘ : Δₘ ∣ [] ⊢ Tₘ ⦂ `ℕ
⊢Tₘ = env (mw-u ez mw[])
          (env (mw-l (bind `𝔹 , ez , nameable-b) mw[]) ⊢Vₘ
               (conv-idv (bind `ℕ , es ez , nameable-b))
               (wf-var (bind `ℕ , es ez , nameable-b)))
          (conv-unseal (es ez)) wf-ℕ

-- THE SCOPE MOVE IS VISIBLE HERE, and this is the one run on which it
-- is: `Θₘ₂` is not binds-only (it carries the re-exposing `unlock 0`), so
-- the contractum's inner frame gains it at the tail — where `scope`
-- applies it FIRST, exactly where `Θₘ₂` applied it.  The outer frame
-- keeps it too (`dropLocks Θₘ₂ ≡ Θₘ₂`): unmasking twice is unmasking.
Θₘ₁′ : CtxMorph
Θₘ₁′ = lock 0 ∷ unlock 0 ∷ []

_ : _≡_ {A = CtxMorph} (Θₘ₁ ⋉ Θₘ₂) Θₘ₁′
_ = refl

_ : _≡_ {A = CtxMorph} (dropLocks Θₘ₂) Θₘ₂
_ = refl

-- … and the value's own frame is unchanged: the moved `unlock 0` is
-- undone by the `lock 0` that already stood in front of it.
_ : interior Θₘ₁′ (interior Θₘ₂ Δₘ) ≡ interior Θₘ₁ (interior Θₘ₂ Δₘ)
_ = refl

push-Tₘ : Δₘ ⊢ Tₘ -→ (Vₘ ⟪ Θₘ₁′ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫
push-Tₘ = IdPush (V-⟪⟫ V-$ I-seal) (es ez)

⊢push-Tₘ : Δₘ ∣ [] ⊢ (Vₘ ⟪ Θₘ₁′ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tₘ = env (mw-u ez mw[])
               (env (mw-l (bind `𝔹 , ez , nameable-b) (mw-u ez mw[])) ⊢Vₘ
                    (conv-unseal (es ez)) wf-ℕ)
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
Δd = bind (` 0) ∷ abst ∷ bind `ℕ ∷ []

-- W's rep, read on Δd, is the Λ-bound X — the chained spelling that broke.
_ : Δd ∋ 0 := ` 1
_ = ez

Θ2 : CtxMorph                       -- bind(W) , conceal V
Θ2 = bind (` 0) ∷ lock 2 ∷ []

-- ONE frame change: the owner is pushed on, V is MASKED IN PLACE (the entry
-- `bind `ℕ` survives as `masked (bind `ℕ)`), nothing is dropped.
_ : interior Θ2 Δd ≡ bind (` 0) ∷ bind (` 0) ∷ abst ∷ masked (bind `ℕ) ∷ []
_ = refl

-- the FACE type context keeps every slot live, so a conceal's licence resolves.
_ : exterior Θ2 Δd ≡ bind (` 0) ∷ bind (` 0) ∷ abst ∷ bind `ℕ ∷ []
_ = refl

cΘ2 : Conv                      -- (X⇒X)⇒ℕ  ⇝  (W⇒W)⇒ℕ
cΘ2 = (unseal 0 ↦ seal 0) ↦ id `ℕ

Vd Wd : Term
Vd = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
Wd = (ƛ (` 1) ∙ (` 0)) ⟪ lock 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

⊢cΘ2 : exterior Θ2 Δd ⊢ cΘ2 ∶ ((` 0 ⇒ ` 0) ⇒ `ℕ) ⇝ ((` 1 ⇒ ` 1) ⇒ `ℕ)
⊢cΘ2 = conv-fun (conv-fun (conv-unseal ez) (conv-seal ez)) (conv-id base-ℕ)

⊢Fnd : Δd ∣ [] ⊢ Vd ⟪ Θ2 , cΘ2 ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fnd = env (mw-b (wf-var (_ , ez , nameable-b))
                 (mw-l (_ , es (es ez) , nameable-b) mw[]))
           (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable-b))
                     (wf-var (_ , ez , nameable-b))) ⊢$)
           ⊢cΘ2
           (wf-⇒ (wf-⇒ (wf-var (_ , ez , nameable-b))
                       (wf-var (_ , ez , nameable-b))) wf-ℕ)

-- THE CROSSING VALUE.  Its bind boundary masks W and seals at it: the licence
-- `seal 0` cites the owner at slot 0 of Δd, whose rep is X = ` 1.
_ : interior (lock 0 ∷ []) Δd ≡ masked (bind (` 0)) ∷ abst ∷ bind `ℕ ∷ []
_ = refl

⊢Wd : Δd ∣ [] ⊢ Wd ⦂ (` 0 ⇒ ` 0)
⊢Wd = env (mw-l (_ , ez , nameable-b) mw[])
          (⊢ƛ (wf-var (_ , es ez , nameable-a)) (⊢` here))
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (_ , ez , nameable-b))
                (wf-var (_ , ez , nameable-b)))

Wd-value : Value Wd
Wd-value = V-⟪⟫ V-ƛ I-fun

⊢Redexd : Δd ∣ [] ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd ⦂ `ℕ
⊢Redexd = ⊢· ⊢Fnd ⊢Wd

peel-d : Δd ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd
           -→ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
                ⟪ Θ2 , id `ℕ ⟫
peel-d = Peel V-ƛ Wd-value

-- THE DUAL is two names and nothing else: mask the owner, re-expose V.
_ : dual Θ2 ≡ lock 0 ∷ unlock 3 ∷ []
_ = refl

-- THE REPOINTING.  The dual's interior is Δd with ONE masked slot in front:
-- every entry of Δd is still there, in the same order, with the same rep.
-- W's entry — the one the old design demoted to `abst` — is untouched.
_ : interior (dual Θ2) (interior Θ2 Δd) ≡ masked (bind (` 0)) ∷ Δd
_ = refl

-- and the dual's FACE type context is IDENTICAL to the crossed boundary's, so `s`
-- transplants verbatim (no swapᵇ, no re-derivation).
_ : exterior (dual Θ2) (interior Θ2 Δd) ≡ exterior Θ2 Δd
_ = refl

-- THE CONTRACTUM IS TYPED.  (The previous design has `¬⊢contractum` here.)
⊢contractumd :
  Δd ∣ [] ⊢ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
              ⟪ Θ2 , id `ℕ ⟫ ⦂ `ℕ
⊢contractumd =
  env (mw-b (wf-var (_ , ez , nameable-b))
            (mw-l (_ , es (es ez) , nameable-b) mw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable-b))
                    (wf-var (_ , ez , nameable-b))) ⊢$)
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
    env (mw-l (_ , ez , nameable-b)
              (mw-u (es (es (es ez))) mw[]))
        ⊢Wd-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , nameable-b))
              (wf-var (_ , ez , nameable-b)))

-- ── n1b (the break, minimized) ─────────────────────────────────────────
-- The chain X:=Y over a Λ-bound Y, with the ambient's third slot and the
-- rep-carrying conceal both removed.

Δ1b : Ctxᵗ
Δ1b = bind (` 0) ∷ abst ∷ []

Θ1b : CtxMorph
Θ1b = bind (` 0) ∷ lock 1 ∷ []

_ : interior Θ1b Δ1b ≡ bind (` 0) ∷ bind (` 0) ∷ masked abst ∷ []
_ = refl

V1b W1b : Term
V1b = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
W1b = (ƛ (` 1) ∙ (` 0)) ⟪ lock 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

cΘ1b : Conv
cΘ1b = (unseal 0 ↦ seal 0) ↦ id `ℕ

⊢W1b : Δ1b ∣ [] ⊢ W1b ⦂ (` 0 ⇒ ` 0)
⊢W1b = env (mw-l (_ , ez , nameable-b) mw[])
           (⊢ƛ (wf-var (_ , es ez , nameable-a)) (⊢` here))
           (conv-fun (conv-unseal ez) (conv-seal ez))
           (wf-⇒ (wf-var (_ , ez , nameable-b))
                 (wf-var (_ , ez , nameable-b)))

⊢Fn1b : Δ1b ∣ [] ⊢ V1b ⟪ Θ1b , cΘ1b ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fn1b = env (mw-b (wf-var (_ , ez , nameable-b))
                  (mw-l (_ , es ez , nameable-a) mw[]))
            (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable-b))
                      (wf-var (_ , ez , nameable-b))) ⊢$)
            (conv-fun (conv-fun (conv-unseal ez) (conv-seal ez))
                      (conv-id base-ℕ))
            (wf-⇒ (wf-⇒ (wf-var (_ , ez , nameable-b))
                        (wf-var (_ , ez , nameable-b))) wf-ℕ)

⊢Redex1b : Δ1b ∣ [] ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b ⦂ `ℕ
⊢Redex1b = ⊢· ⊢Fn1b ⊢W1b

_ : dual Θ1b ≡ lock 0 ∷ unlock 2 ∷ []
_ = refl

-- the repointing again: nothing dropped, nothing demoted …
_ : interior (dual Θ1b) (interior Θ1b Δ1b) ≡ masked (bind (` 0)) ∷ Δ1b
_ = refl

-- … and the crossing value's licence, re-based one slot out, is STILL A
-- LIVE OWNER.
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
  env (mw-b (wf-var (_ , ez , nameable-b)) (mw-l (_ , es ez , nameable-a) mw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , nameable-b))
                    (wf-var (_ , ez , nameable-b))) ⊢$)
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
    env (mw-l (_ , ez , nameable-b) (mw-u (es (es ez)) mw[]))
        ⊢W1b-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , nameable-b)) (wf-var (_ , ez , nameable-b)))

-- ── n4 (the x-alias break) ─────────────────────────────────────────────
-- There is no x-entry and no rep-less reveal to alias: a conceal cites an
-- owner, full stop.  The n4 configuration becomes an ordinary owner + alias.

Δ4 : Ctxᵗ
Δ4 = masked (bind `ℕ) ∷ []          -- a slot masked by an enclosing boundary

Θ4 : CtxMorph                        -- re-expose it
Θ4 = unlock 0 ∷ []

_ : interior Θ4 Δ4 ≡ bind `ℕ ∷ []
_ = refl

-- the alias RESTORES NAMEABILITY, and with it the owner's knowledge — the
-- fact `demote-x-always` denied.  It invents nothing: the rep `ℕ` was
-- already sitting in the masked entry.
_ : interior Θ4 Δ4 ∋ 0 := `ℕ
_ = ez

-- ── E★′ (the shape-IV survivor) ────────────────────────────────────────

Γ★ : Ctxᵗ
Γ★ = abst ∷ bind `ℕ ∷ []

Θ★ : CtxMorph
Θ★ = bind (` 0) ∷ lock 1 ∷ []

_ : interior Θ★ Γ★ ≡ bind (` 0) ∷ abst ∷ masked (bind `ℕ) ∷ []
_ = refl

_ : dual Θ★ ≡ lock 0 ∷ unlock 2 ∷ []
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
--   TyBeta  — the boundary is BORN, at the owner X := ℕ
--   Peel    — the crossing: the argument 7 acquires the DUAL
--   Beta    — the ordinary β step, i.e. ⊢subst (strong.TermSubst)
--   CancelR — the seal/unseal pair, minted by TyBeta and Peel, annihilates
--   Drop$   — the surviving base face over a numeral is dropped

polyid : Term
polyid = Λ (ƛ (` 0) ∙ (` 0))

⊢polyid : [] ∣ [] ⊢ polyid ⦂ `∀ (` 0 ⇒ ` 0)
⊢polyid = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) (⊢` here))

P₀ : Term
P₀ = (polyid ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢P₀ : [] ∣ [] ⊢ P₀ ⦂ `ℕ
⊢P₀ = ⊢· (⊢·[] ⊢polyid wf-ℕ) ⊢$

-- ── STEP 1 — TYBETA.  The ∀-elimination mints THE OWNER of the event and
-- derives its face from the body type: `reveal 0 (X⇒X)` is the ↦-pair
-- that seals on the domain and unseals on the codomain.

_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

P₁ : Term
P₁ = ((ƛ (` 0) ∙ (` 0)) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)

step₁ : [] ⊢ P₀ -→ P₁
step₁ = ξ-·-l (TyBeta V-ƛ)

⊢fn₁ : [] ∣ [] ⊢ (ƛ (` 0) ∙ (` 0)) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫
         ⦂ (`ℕ ⇒ `ℕ)
⊢fn₁ = env (mw-b wf-ℕ mw[])
           (⊢ƛ (wf-var (bind `ℕ , ez , nameable-b)) (⊢` here))
           (conv-fun (conv-seal ez) (conv-unseal ez))
           (wf-⇒ wf-ℕ wf-ℕ)

⊢P₁ : [] ∣ [] ⊢ P₁ ⦂ `ℕ
⊢P₁ = ⊢· ⊢fn₁ ⊢$

-- ── STEP 2 — PEEL.  The application is pushed one layer in and the argument
-- acquires the DUAL: one `lock` per owner of the crossed boundary and
-- nothing else.  Its face is `s`, the ↦'s domain component, transplanted
-- VERBATIM — the dual's face type context IS the crossed boundary's.

_ : dual (bind `ℕ ∷ []) ≡ lock 0 ∷ []
_ = refl

_ : exterior (dual (bind `ℕ ∷ [])) (interior (bind `ℕ ∷ []) [])
      ≡ exterior (bind `ℕ ∷ []) []
_ = refl

P₂ : Term
P₂ = ((ƛ (` 0) ∙ (` 0)) · (($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫))
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

step₂ : [] ⊢ P₁ -→ P₂
step₂ = Peel V-ƛ V-$

-- the crossing argument, typed INSIDE: 7 is sealed at the new owner, so the
-- interior sees it at the abstract name X.
⊢arg₂ : (bind `ℕ ∷ []) ∣ [] ⊢ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫ ⦂ ` 0
⊢arg₂ = env (mw-l (bind `ℕ , ez , nameable-b) mw[]) ⊢$
            (conv-seal ez) (wf-var (bind `ℕ , ez , nameable-b))

⊢P₂ : [] ∣ [] ⊢ P₂ ⦂ `ℕ
⊢P₂ = env (mw-b wf-ℕ mw[])
          (⊢· (⊢ƛ (wf-var (bind `ℕ , ez , nameable-b)) (⊢` here)) ⊢arg₂)
          (conv-unseal ez) wf-ℕ

-- ── STEP 3 — BETA, under the boundary.  This is the step ⊢subst pays for:
-- the contractum's typing below is `preserve-Beta` (strong.TermSubst),
-- i.e. ⊢subst applied to the interior redex.

P₃ : Term
P₃ = (($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

_ : (` 0) [ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫ ]ᵐ
      ≡ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫
_ = refl

step₃ : [] ⊢ P₂ -→ P₃
step₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

⊢P₃-in : (bind `ℕ ∷ []) ∣ [] ⊢ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫ ⦂ ` 0
⊢P₃-in = preserve-Beta
           (⊢· (⊢ƛ (wf-var (bind `ℕ , ez , nameable-b)) (⊢` here)) ⊢arg₂)

⊢P₃ : [] ∣ [] ⊢ P₃ ⦂ `ℕ
⊢P₃ = env (mw-b wf-ℕ mw[]) ⊢P₃-in (conv-unseal ez) wf-ℕ

-- ── STEP 4 — CANCEL.  The seal minted by Peel and the unseal minted by
-- TyBeta are now adjacent and cite THE SAME ENTRY, so the face match is
-- definitional; each face becomes the identity at the LOOKED-UP rep, and
-- BOTH FRAMES STAY (the repaired rule) — so the crossing's own `lock 0`
-- survives as a transparent layer, to be dropped in its own right.

P₄ : Term
P₄ = (($ 7) ⟪ lock 0 ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

step₄ : [] ⊢ P₃ -→ P₄
step₄ = CancelR V-$ ez

⊢P₄-in : (bind `ℕ ∷ []) ∣ [] ⊢ ($ 7) ⟪ lock 0 ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢P₄-in = env (mw-l (bind `ℕ , ez , nameable-b) mw[])
              ⊢$ (conv-id base-ℕ) wf-ℕ

⊢P₄ : [] ∣ [] ⊢ P₄ ⦂ `ℕ
⊢P₄ = env (mw-b wf-ℕ mw[]) ⊢P₄-in (conv-id base-ℕ) wf-ℕ

-- ── STEPS 5, 6 — the two base faces over the numeral, and the whole run.

P₅ : Term
P₅ = ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

step₅ : [] ⊢ P₄ -→ P₅
step₅ = ξ-⟪⟫ (Drop$ base-ℕ)

⊢P₅ : [] ∣ [] ⊢ P₅ ⦂ `ℕ
⊢P₅ = env (mw-b wf-ℕ mw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

step₆ : [] ⊢ P₅ -→ $ 7
step₆ = Drop$ base-ℕ

run-P₀ : [] ⊢ P₀ -→* $ 7
run-P₀ = step₁ then step₂ then step₃ then step₄ then step₅ then step₆
    then done

val-P₀ : Value ($ 7)
val-P₀ = V-$

------------------------------------------------------------------------
-- §7  Two regressions on substᵐ itself
------------------------------------------------------------------------

-- ── the Λ clause: an image is TYPE-SHIFTED past the new Λ-bound slot ────
-- Under a Λ the term context is ⤊ Γ, so a term written over Δ must have its
-- boundary NAMES shifted before it is planted inside.  Here `seal 0` becomes
-- `seal 1` — and it must, since slot 0 inside the Λ is `abst`, where
-- `conv-seal` has no owner to cite.

Δₛ : Ctxᵗ
Δₛ = bind `ℕ ∷ []

Wₛ Nₛ : Term
Wₛ = ($ 7) ⟪ [] , seal 0 ⟫
Nₛ = Λ (` 0)

⊢Wₛ : Δₛ ∣ [] ⊢ Wₛ ⦂ ` 0
⊢Wₛ = env mw[] ⊢$ (conv-seal ez) (wf-var (bind `ℕ , ez , nameable-b))

⊢Nₛ : Δₛ ∣ (` 0 ∷ []) ⊢ Nₛ ⦂ `∀ (` 1)
⊢Nₛ = ⊢Λ (⊢` here)

_ : Nₛ [ Wₛ ]ᵐ ≡ Λ (($ 7) ⟪ [] , seal 1 ⟫)
_ = refl

⊢Nₛ[Wₛ] : Δₛ ∣ [] ⊢ Nₛ [ Wₛ ]ᵐ ⦂ `∀ (` 1)
⊢Nₛ[Wₛ] = ⊢subst ⊢Nₛ ⊢Wₛ

-- ── the ƛ clause: `shiftᵐ` protects the ƛ-bound slot ───────────────────
-- `extᵐ` weakens an image by ONE TERM VARIABLE, so the image's own binders
-- must be skipped: the substituted identity keeps naming its own argument.

_ : (ƛ `ℕ ∙ (` 1)) [ ƛ `ℕ ∙ (` 0) ]ᵐ ≡ ƛ `ℕ ∙ (ƛ `ℕ ∙ (` 0))
_ = refl

_ : [] ∣ [] ⊢ (ƛ `ℕ ∙ (` 1)) [ ƛ `ℕ ∙ (` 0) ]ᵐ ⦂ (`ℕ ⇒ (`ℕ ⇒ `ℕ))
_ = ⊢subst (⊢ƛ wf-ℕ (⊢` (there here))) (⊢ƛ wf-ℕ (⊢` here))

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

-- P₃ is the CANCEL state: the interior is a value, the face is the ACTIVE
-- `unseal 0`, and canon-var picks out the seal-faced layer under it.
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

-- P₅ is the last DROP$ state: the face is the ACTIVE `id `ℕ` and
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
⊢P₃-pres = env (mw-b wf-ℕ mw[]) ⊢P₃-in (conv-unseal ez) wf-ℕ

-- STEP 6 — Drop$ (step 5 is the same rule, under ξ-⟪⟫).
⊢P₆-pres : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
⊢P₆-pres = preservation-Drop$ base-ℕ ⊢P₅

------------------------------------------------------------------------
-- §10  IDPUSH — THE REACHABILITY VERDICT (soundness, not a break)
------------------------------------------------------------------------

-- SUPERSEDED BY THE SCOPE MOVE (2026-09-06), and kept as the record of
-- the question it answered.  The old IdPush contractum was refuted on a
-- HAND-BUILT redex whose Θ₂ = `lock 1 ∷ []` blocks the very slot the
-- id-face's owner rep (` 1) names, and this section asked whether that
-- configuration was REACHABLE.  The repaired rule MOVES Θ₂'s scope into
-- the inner frame, so the configuration is no longer a problem whether
-- it is reachable or not (§12b runs the witness), and the scoping
-- side-condition below is no longer asked of anything.  The verdict as
-- it stood:  NO — once the separately-diagnosed Peel/`dual` bug (§3 of
-- PreserveObstruct) is fixed.
--
--   * TyBeta, the ONLY rule that mints a boundary from a plain redex, mints
--     a LOCK-FREE `bind A ∷ []`; so a lock reaches an ACTIVE outer face only
--     via a Peel's `dual Θ`.
--   * A REPAIRED dual installs only the owner locks `hideBinds (numBinds Θ)`,
--     which block Θ's own new owner slots.  By SIMULTANEITY (`pushBinds` lifts
--     each rep past the owners bound inside it — a rep is a type over the
--     PLAIN exterior) NO owner's rep names another owner slot, so those
--     owner locks never block a face's rep.
--   * The `¬IdPushCase` witness has its lock on a NON-owner slot the rep
--     names; that shape is producible ONLY by the current dual's
--     `unlock X ↦ lock (n+X)` defect — the §3 Peel refutation — not by
--     IdPush.
--
-- THE SOUNDNESS FIX (machine-checked in proof/IdPushReach).  `idPush⁺`
-- discharges the IdPush case under the single added scoping side-condition
-- `interior Θ₂ Δ ⊢ᵗ A` (Q3(a)); the companion
-- `owner : interior Θ₂ Δ ∋ Y := A` is a CONSEQUENCE of the redex typing
-- (mask-only), not an assumption.

open import strong.proof.IdPushReach
  using (idPush⁺; idPushCase-scoped; owner-holds; scoped-fails)

-- The interior of the counterexample: slot 1 blocked under the lock.
§10-Ξi : Ctxᵗ
§10-Ξi = bind (` 0) ∷ masked (bind `ℕ) ∷ []

-- The scoping premise is EXACTLY what the counterexample denies: on the
-- witness the owner fact still holds, but the rep ` 1 is not well formed
-- inside the locked interior.
§10-verdict : (§10-Ξi ∋ 0 := ` 1) × ¬ (§10-Ξi ⊢ᵗ ` 1)
§10-verdict = owner-holds , scoped-fails

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
-- THE SHAPE THAT MAKES AN ID-LAYER.  TyBeta's minted face is
-- `reveal 0 B`, and `reveal 0 (` k)` is `id (` k)` for every k ≠ 0.
-- So an id-layer is born exactly when a type abstraction is instantiated
-- at a body type that is an OUTER type variable — a VACUOUS `Λ`, whose
-- body mentions a variable bound further out.  The smallest source with
-- that shape is the supervisor's candidate:
--
--   Q = ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [ℕ]) · 7
--
-- de Bruijn: under Z the outer Y is slot 1, so `ΛZ. x` has type `∀ (` 1)
-- and the inner TyBeta mints `reveal 0 (` 1) = id (` 1)` — an id-faced
-- layer around x's value, sitting inside the OUTER package's
-- unseal-faced wrapper.  That two-wrapper stack IS the IdPush redex.

open import strong.proof.PeelDual using (preserve-Peel; repsOf-dual)

-- ── the source ─────────────────────────────────────────────────────────

Qvac Qbody Qfun Q₀ : Term
Qvac  = Λ (` 0)                          -- ΛZ. x
Qbody = Qvac ·[ ` 1 , `ℕ ]               -- (ΛZ. x) [ℕ]
Qfun  = Λ (ƛ (` 0) ∙ Qbody)              -- ΛY. λx:Y. (ΛZ. x) [ℕ]
Q₀    = (Qfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Qbody : (abst ∷ []) ∣ (` 0 ∷ []) ⊢ Qbody ⦂ ` 0
⊢Qbody = ⊢·[] (⊢Λ (⊢` here)) wf-ℕ

⊢Qfun : [] ∣ [] ⊢ Qfun ⦂ `∀ (` 0 ⇒ ` 0)
⊢Qfun = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) ⊢Qbody)

⊢Q₀ : [] ∣ [] ⊢ Q₀ ⦂ `ℕ
⊢Q₀ = ⊢· (⊢·[] ⊢Qfun wf-ℕ) ⊢$

-- The two type contexts the run works in: the outer boundary's interior,
-- and the id-layer's interior.
QΔ₁ QΞ₂ : Ctxᵗ
QΔ₁ = bind `ℕ ∷ []
QΞ₂ = bind `ℕ ∷ bind `ℕ ∷ []

_ : interior (bind `ℕ ∷ []) [] ≡ QΔ₁
_ = refl

_ : interior (bind `ℕ ∷ []) QΔ₁ ≡ QΞ₂
_ = refl

-- ── STEP 1 — TYBETA (outer).  The owner Y := ℕ is minted.

_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

Q₁ : Term
Q₁ = ((ƛ (` 0) ∙ Qbody) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)

qstep₁ : [] ⊢ Q₀ -→ Q₁
qstep₁ = ξ-·-l (TyBeta V-ƛ)

⊢Qbody₁ : QΔ₁ ∣ (` 0 ∷ []) ⊢ Qbody ⦂ ` 0
⊢Qbody₁ = ⊢·[] (⊢Λ (⊢` here)) wf-ℕ

⊢Q₁ : [] ∣ [] ⊢ Q₁ ⦂ `ℕ
⊢Q₁ = ⊢· (preservation-TyBeta (⊢·[] ⊢Qfun wf-ℕ)) ⊢$

-- ── STEP 2 — PEEL.  7 crosses; `dual (bind ℕ ∷ []) = lock 0 ∷ []`, so
-- the argument acquires a seal-faced wrapper that hides the new owner.

_ : dual (bind `ℕ ∷ []) ≡ lock 0 ∷ []
_ = refl

QS₇ : Term
QS₇ = ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫

Q₂ : Term
Q₂ = ((ƛ (` 0) ∙ Qbody) · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

qstep₂ : [] ⊢ Q₁ -→ Q₂
qstep₂ = Peel V-ƛ V-$

⊢QS₇ : QΔ₁ ∣ [] ⊢ QS₇ ⦂ ` 0
⊢QS₇ = env (mw-l (bind `ℕ , ez , nameable-b) mw[]) ⊢$
            (conv-seal ez) (wf-var (bind `ℕ , ez , nameable-b))

⊢Q₂ : [] ∣ [] ⊢ Q₂ ⦂ `ℕ
⊢Q₂ = preserve-Peel V-ƛ V-$ ⊢Q₁

-- ── STEP 3 — BETA, under ξ-⟪⟫.  substᵐ's Λ clause ⇑ᴹ-shifts the sealed 7
-- past ΛZ: the seal NAME moves (seal 0 ↦ seal 1) and so does the lock.

_ : ⇑ᴹ QS₇ ≡ ($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫
_ = refl

_ : Qbody [ QS₇ ]ᵐ ≡ (Λ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)) ·[ ` 1 , `ℕ ]
_ = refl

Q₃ : Term
Q₃ = ((Λ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)) ·[ ` 1 , `ℕ ])
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

qstep₃ : [] ⊢ Q₂ -→ Q₃
qstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

⊢Q₃-in : QΔ₁ ∣ [] ⊢ (Λ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)) ·[ ` 1 , `ℕ ] ⦂ ` 0
⊢Q₃-in = preservation-Beta (⊢· (⊢ƛ (wf-var (bind `ℕ , ez , nameable-b)) ⊢Qbody₁)
                              ⊢QS₇)

⊢Q₃ : [] ∣ [] ⊢ Q₃ ⦂ `ℕ
⊢Q₃ = env (mw-b wf-ℕ mw[]) ⊢Q₃-in (conv-unseal ez) wf-ℕ

-- ── STEP 4 — TYBETA (inner), under ξ-⟪⟫.  THE ID-LAYER IS BORN: the body
-- type is the OUTER variable, so the minted face is an identity.

_ : reveal 0 (` 1) ≡ id (` 1)
_ = refl

Q₄ : Term
Q₄ = ((($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ bind `ℕ ∷ [] , id (` 1) ⟫)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

qstep₄ : [] ⊢ Q₃ -→ Q₄
qstep₄ = ξ-⟪⟫ (TyBeta (V-⟪⟫ V-$ I-seal))

⊢Qseal₇ : QΞ₂ ∣ [] ⊢ ($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫ ⦂ ` 1
⊢Qseal₇ = env (mw-l (bind `ℕ , es ez , nameable-b) mw[]) ⊢$
               (conv-seal (es ez)) (wf-var (bind `ℕ , es ez , nameable-b))

⊢Q₄-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)
                      ⟪ bind `ℕ ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢Q₄-in = preservation-TyBeta ⊢Q₃-in

⊢Q₄ : [] ∣ [] ⊢ Q₄ ⦂ `ℕ
⊢Q₄ = env (mw-b wf-ℕ mw[]) ⊢Q₄-in (conv-unseal ez) wf-ℕ

-- ── STEP 5 — THE IDPUSH REDEX, AND IDPUSH.  Θ₁ = Θ₂ = `bind ℕ ∷ []`,
-- X = 1, Y = 0, A = ℕ (the looked-up rep).  Both frames are untouched;
-- only the two faces swap.

Q₅ : Term
Q₅ = ((($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ bind `ℕ ∷ [] , unseal 1 ⟫)
       ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

qstep₅ : [] ⊢ Q₄ -→ Q₅
qstep₅ = IdPush (V-⟪⟫ V-$ I-seal) ez

-- the contractum TYPES: the rep ℕ is well formed inside Θ₂'s interior.
⊢Q₅-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)
                      ⟪ bind `ℕ ∷ [] , unseal 1 ⟫ ⦂ `ℕ
⊢Q₅-in = env (mw-b wf-ℕ mw[]) ⊢Qseal₇ (conv-unseal (es ez)) wf-ℕ

⊢Q₅ : [] ∣ [] ⊢ Q₅ ⦂ `ℕ
⊢Q₅ = env (mw-b wf-ℕ mw[]) ⊢Q₅-in (conv-id base-ℕ) wf-ℕ

-- ── STEP 6 — CANCEL, under ξ-⟪⟫.  The seal minted by Peel and the unseal
-- IdPush just moved inwards are now adjacent.  BOTH FRAMES STAY: the
-- crossing's own `lock 1` survives under an identity face, one more
-- transparent layer for Drop$ to finish.

Q₆ : Term
Q₆ = ((($ 7) ⟪ lock 1 ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫)
       ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

qstep₆ : [] ⊢ Q₅ -→ Q₆
qstep₆ = ξ-⟪⟫ (CancelR V-$ (es ez))

⊢Q₆-in2 : QΞ₂ ∣ [] ⊢ ($ 7) ⟪ lock 1 ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢Q₆-in2 = env (mw-l (bind `ℕ , es ez , nameable-b) mw[])
               ⊢$ (conv-id base-ℕ) wf-ℕ

⊢Q₆-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 1 ∷ [] , id `ℕ ⟫)
                      ⟪ bind `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢Q₆-in = env (mw-b wf-ℕ mw[]) ⊢Q₆-in2 (conv-id base-ℕ) wf-ℕ

⊢Q₆ : [] ∣ [] ⊢ Q₆ ⦂ `ℕ
⊢Q₆ = env (mw-b wf-ℕ mw[]) ⊢Q₆-in (conv-id base-ℕ) wf-ℕ

-- ── STEPS 7, 8, 9 — the three base faces over the numeral.

Q₇ Q₈ : Term
Q₇ = (($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
Q₈ = ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

qstep₇ : [] ⊢ Q₆ -→ Q₇
qstep₇ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

⊢Q₇-in : QΔ₁ ∣ [] ⊢ ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢Q₇-in = env (mw-b wf-ℕ mw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

⊢Q₇ : [] ∣ [] ⊢ Q₇ ⦂ `ℕ
⊢Q₇ = env (mw-b wf-ℕ mw[]) ⊢Q₇-in (conv-id base-ℕ) wf-ℕ

qstep₈ : [] ⊢ Q₇ -→ Q₈
qstep₈ = ξ-⟪⟫ (Drop$ base-ℕ)

⊢Q₈ : [] ∣ [] ⊢ Q₈ ⦂ `ℕ
⊢Q₈ = env (mw-b wf-ℕ mw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

qstep₉ : [] ⊢ Q₈ -→ $ 7
qstep₉ = Drop$ base-ℕ

⊢Q₉ : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
⊢Q₉ = preservation-Drop$ base-ℕ ⊢Q₈

run-Q₀ : [] ⊢ Q₀ -→* $ 7
run-Q₀ = qstep₁ then qstep₂ then qstep₃ then qstep₄ then qstep₅
    then qstep₆ then qstep₇ then qstep₈ then qstep₉ then done

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

qdet₉ : ∀ {M′} → [] ⊢ Q₈ -→ M′ → M′ ≡ $ 7
qdet₉ st = det st qstep₉

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

⊢Dbody : (abst ∷ []) ∣ (` 0 ∷ []) ⊢ Dbody ⦂ ` 0
⊢Dbody = ⊢·[] (⊢Λ (⊢·[] (⊢Λ (⊢` here)) wf-ℕ)) wf-ℕ

⊢Dfun : [] ∣ [] ⊢ Dfun ⦂ `∀ (` 0 ⇒ ` 0)
⊢Dfun = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) ⊢Dbody)

⊢D₀ : [] ∣ [] ⊢ D₀ ⦂ `ℕ
⊢D₀ = ⊢· (⊢·[] ⊢Dfun wf-ℕ) ⊢$

QΞ₃ : Ctxᵗ
QΞ₃ = bind `ℕ ∷ QΞ₂

D₁ D₂ D₃ D₄ D₅ D₆ D₇ D₈ D₉ D₁₀ D₁₁ : Term
D₁  = ((ƛ (` 0) ∙ Dbody) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
D₂  = ((ƛ (` 0) ∙ Dbody) · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
D₃  = ((Λ ((Λ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)) ·[ ` 2 , `ℕ ]))
         ·[ ` 1 , `ℕ ]) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
D₄  = ((Λ ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
              ⟪ bind `ℕ ∷ [] , id (` 2) ⟫)) ·[ ` 1 , `ℕ ])
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
D₅  = (((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫) ⟪ bind `ℕ ∷ [] , id (` 2) ⟫)
          ⟪ bind `ℕ ∷ [] , id (` 1) ⟫) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
D₆  = (((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫) ⟪ bind `ℕ ∷ [] , id (` 2) ⟫)
          ⟪ bind `ℕ ∷ [] , unseal 1 ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
D₇  = (((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫) ⟪ bind `ℕ ∷ [] , unseal 2 ⟫)
          ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
D₈  = (((($ 7) ⟪ lock 2 ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫)
          ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
D₉  = ((($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫)
        ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
D₁₀ = (($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
D₁₁ = ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

dstep₁ : [] ⊢ D₀ -→ D₁
dstep₁ = ξ-·-l (TyBeta V-ƛ)

dstep₂ : [] ⊢ D₁ -→ D₂
dstep₂ = Peel V-ƛ V-$

dstep₃ : [] ⊢ D₂ -→ D₃
dstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- the INNER vacuous Λ fires first — under ξ-Λ, because `Λ N` is a value
-- only when N is (V-Λ's premise, repair (1)).
dstep₄ : [] ⊢ D₃ -→ D₄
dstep₄ = ξ-⟪⟫ (ξ-·[] (ξ-Λ (TyBeta (V-⟪⟫ V-$ I-seal))))

dstep₅ : [] ⊢ D₄ -→ D₅
dstep₅ = ξ-⟪⟫ (TyBeta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv))

-- IDPUSH #1 — the outer id-layer.
dstep₆ : [] ⊢ D₅ -→ D₆
dstep₆ = IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) ez

-- IDPUSH #2 — the unseal IdPush #1 pushed inwards meets the NEXT layer.
dstep₇ : [] ⊢ D₆ -→ D₇
dstep₇ = ξ-⟪⟫ (IdPush (V-⟪⟫ V-$ I-seal) (es ez))

dstep₈ : [] ⊢ D₇ -→ D₈
dstep₈ = ξ-⟪⟫ (ξ-⟪⟫ (CancelR V-$ (es (es ez))))

dstep₉ : [] ⊢ D₈ -→ D₉
dstep₉ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))

dstep₁₀ : [] ⊢ D₉ -→ D₁₀
dstep₁₀ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

dstep₁₁ : [] ⊢ D₁₀ -→ D₁₁
dstep₁₁ = ξ-⟪⟫ (Drop$ base-ℕ)

dstep₁₂ : [] ⊢ D₁₁ -→ $ 7
dstep₁₂ = Drop$ base-ℕ

run-D₀ : [] ⊢ D₀ -→* $ 7
run-D₀ = dstep₁ then dstep₂ then dstep₃ then dstep₄ then dstep₅
    then dstep₆ then dstep₇ then dstep₈ then dstep₉ then dstep₁₀
    then dstep₁₁ then dstep₁₂ then done

-- ── BOTH IDPUSH CONTRACTA TYPE ─────────────────────────────────────────

⊢Dseal₇ : QΞ₃ ∣ [] ⊢ ($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫ ⦂ ` 2
⊢Dseal₇ = env (mw-l (bind `ℕ , es (es ez) , nameable-b) mw[]) ⊢$
               (conv-seal (es (es ez)))
               (wf-var (bind `ℕ , es (es ez) , nameable-b))

⊢Did₂ : QΞ₂ ∣ [] ⊢ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                     ⟪ bind `ℕ ∷ [] , id (` 2) ⟫ ⦂ ` 1
⊢Did₂ = env (mw-b wf-ℕ mw[]) ⊢Dseal₇
             (conv-idv (bind `ℕ , es (es ez) , nameable-b))
             (wf-var (bind `ℕ , es ez , nameable-b))

⊢D₅-in : QΔ₁ ∣ [] ⊢ ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                        ⟪ bind `ℕ ∷ [] , id (` 2) ⟫)
                       ⟪ bind `ℕ ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢D₅-in = env (mw-b wf-ℕ mw[]) ⊢Did₂
              (conv-idv (bind `ℕ , es ez , nameable-b))
              (wf-var (bind `ℕ , ez , nameable-b))

⊢D₅ : [] ∣ [] ⊢ D₅ ⦂ `ℕ
⊢D₅ = env (mw-b wf-ℕ mw[]) ⊢D₅-in (conv-unseal ez) wf-ℕ

⊢D₆-in : QΔ₁ ∣ [] ⊢ ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                        ⟪ bind `ℕ ∷ [] , id (` 2) ⟫)
                       ⟪ bind `ℕ ∷ [] , unseal 1 ⟫ ⦂ `ℕ
⊢D₆-in = env (mw-b wf-ℕ mw[]) ⊢Did₂ (conv-unseal (es ez)) wf-ℕ

⊢D₆ : [] ∣ [] ⊢ D₆ ⦂ `ℕ
⊢D₆ = env (mw-b wf-ℕ mw[]) ⊢D₆-in (conv-id base-ℕ) wf-ℕ

⊢D₇-in2 : QΞ₂ ∣ [] ⊢ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                        ⟪ bind `ℕ ∷ [] , unseal 2 ⟫ ⦂ `ℕ
⊢D₇-in2 = env (mw-b wf-ℕ mw[]) ⊢Dseal₇
               (conv-unseal (es (es ez))) wf-ℕ

⊢D₇-in : QΔ₁ ∣ [] ⊢ ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                        ⟪ bind `ℕ ∷ [] , unseal 2 ⟫)
                       ⟪ bind `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢D₇-in = env (mw-b wf-ℕ mw[]) ⊢D₇-in2 (conv-id base-ℕ) wf-ℕ

⊢D₇ : [] ∣ [] ⊢ D₇ ⦂ `ℕ
⊢D₇ = env (mw-b wf-ℕ mw[]) ⊢D₇-in (conv-id base-ℕ) wf-ℕ

------------------------------------------------------------------------
-- §11b  VARIANT (ii) — AN ID-LAYER WHOSE FACE REP IS CHAINED
------------------------------------------------------------------------

-- The Θ₂ of §11's IdPush redex is `bind ℕ ∷ []`: the rep it hands back is
-- the BASE TYPE ℕ, which names nothing.  This variant makes the rep a
-- VARIABLE that names ANOTHER OWNER — the "chained rep" shape that is the
-- whole content of the c10/c11 obstruction (proof/PreserveObstruct §4).
-- It is obtained by running Q's own program INSIDE one more package, at
-- the OUTER package's type variable:
--
--   R = ((ΛX. λy:X. ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [X]) · y) [ℕ]) · 7
--
-- The inner instantiation `[X]` mints an owner whose rep is `X`, so at
-- the IdPush redex `exterior Θ₂ Δ ∋ 0 := ` 1` — Y's rep NAMES the outer owner
-- X.  IDPUSH FIRES AND THE CONTRACTUM TYPES: nothing in Θ₂ is locked, so
-- the scoping fact `interior Θ₂ Δ ⊢ᵗ ` 1` holds.

Rbody Rfun R₀ : Term
Rbody = (Qfun ·[ ` 0 ⇒ ` 0 , ` 0 ]) · (` 0)
Rfun  = Λ (ƛ (` 0) ∙ Rbody)
R₀    = (Rfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Qfun-any : ∀ {Δ Γ} → Δ ∣ Γ ⊢ Qfun ⦂ `∀ (` 0 ⇒ ` 0)
⊢Qfun-any = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) (⊢·[] (⊢Λ (⊢` here)) wf-ℕ))

⊢Rbody : (abst ∷ []) ∣ (` 0 ∷ []) ⊢ Rbody ⦂ ` 0
⊢Rbody = ⊢· (⊢·[] ⊢Qfun-any (wf-var (abst , ez , nameable-a))) (⊢` here)

⊢R₀ : [] ∣ [] ⊢ R₀ ⦂ `ℕ
⊢R₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) ⊢Rbody)) wf-ℕ) ⊢$

-- the three type contexts the chained run works in
RΞ RΞ′ RΞ″ : Ctxᵗ
RΞ  = bind (` 0) ∷ bind `ℕ ∷ []
RΞ′ = bind `ℕ ∷ RΞ
RΞ″ = bind `ℕ ∷ masked (bind (` 0)) ∷ bind `ℕ ∷ []

_ : interior (bind (` 0) ∷ []) QΔ₁ ≡ RΞ
_ = refl

_ : interior (bind `ℕ ∷ []) RΞ ≡ RΞ′
_ = refl

_ : interior (lock 1 ∷ []) RΞ′ ≡ RΞ″
_ = refl

-- THE CHAINED REP, as a lookup: Θ₂'s owner 0 has rep ` 1, which NAMES
-- the outer owner — and that slot is VISIBLE inside Θ₂ (nothing locks it).
Rchain : exterior (bind (` 0) ∷ []) QΔ₁ ∋ 0 := ` 1
Rchain = ez

Rchain-scoped : interior (bind (` 0) ∷ []) QΔ₁ ⊢ᵗ ` 1
Rchain-scoped = wf-var (_ , es ez , nameable-b)

-- ── the states ─────────────────────────────────────────────────────────

RS RS↑ RW : Term
RS  = (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ lock 0 ∷ [] , seal 0 ⟫
RS↑ = (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫) ⟪ lock 1 ∷ [] , seal 1 ⟫
RW  = ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫) ⟪ lock 1 ∷ [] , id (` 2) ⟫)
        ⟪ bind `ℕ ∷ [] , id (` 2) ⟫

_ : wkᴹ 1 QS₇ ≡ ($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫
_ = refl

_ : ⇑ᴹ RS ≡ RS↑
_ = refl

R₁ R₂ R₃ R₄ R₅ R₆ R₇ R₈ R₉ : Term
R₁  = ((ƛ (` 0) ∙ Rbody) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
R₂  = ((ƛ (` 0) ∙ Rbody) · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₃  = ((Qfun ·[ ` 0 ⇒ ` 0 , ` 0 ]) · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₄  = (((ƛ (` 0) ∙ Qbody) ⟪ bind (` 0) ∷ [] , seal 0 ↦ unseal 0 ⟫) · QS₇)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₅  = (((ƛ (` 0) ∙ Qbody) · RS) ⟪ bind (` 0) ∷ [] , unseal 0 ⟫)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₆  = (((Λ RS↑) ·[ ` 1 , `ℕ ]) ⟪ bind (` 0) ∷ [] , unseal 0 ⟫)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₇  = ((RS↑ ⟪ bind `ℕ ∷ [] , id (` 1) ⟫) ⟪ bind (` 0) ∷ [] , unseal 0 ⟫)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₈  = ((RS↑ ⟪ bind `ℕ ∷ [] , unseal 1 ⟫) ⟪ bind (` 0) ∷ [] , id (` 1) ⟫)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
R₉  = (RW ⟪ bind (` 0) ∷ [] , id (` 1) ⟫) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

rstep₁ : [] ⊢ R₀ -→ R₁
rstep₁ = ξ-·-l (TyBeta V-ƛ)

rstep₂ : [] ⊢ R₁ -→ R₂
rstep₂ = Peel V-ƛ V-$

rstep₃ : [] ⊢ R₂ -→ R₃
rstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- the INNER package is instantiated at the OUTER owner: rep ` 0.
rstep₄ : [] ⊢ R₃ -→ R₄
rstep₄ = ξ-⟪⟫ (ξ-·-l (TyBeta V-ƛ))

rstep₅ : [] ⊢ R₄ -→ R₅
rstep₅ = ξ-⟪⟫ (Peel V-ƛ (V-⟪⟫ V-$ I-seal))

rstep₆ : [] ⊢ R₅ -→ R₆
rstep₆ = ξ-⟪⟫ (ξ-⟪⟫ (Beta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal)))

rstep₇ : [] ⊢ R₆ -→ R₇
rstep₇ = ξ-⟪⟫ (ξ-⟪⟫ (TyBeta (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal)))

-- IDPUSH #1, AT A CHAINED REP.
rstep₈ : [] ⊢ R₇ -→ R₈
rstep₈ = ξ-⟪⟫ (IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal) ez)

-- CANCEL, at the chained rep.  Both frames stay, so the crossing's own
-- `lock 1` survives as a transparent layer carrying the CHAINED rep ` 2 —
-- which is where the run's remaining id-layers come from.
rstep₉ : [] ⊢ R₈ -→ R₉
rstep₉ = ξ-⟪⟫ (ξ-⟪⟫ (CancelR (V-⟪⟫ V-$ I-seal) (es ez)))

-- The tail: three more IdPushes (each residue face is ITSELF an
-- id-layer), the last seal/unseal pair, and five transparent layers over
-- the numeral.  The states are the ones the rules compute.
run-R₀ : [] ⊢ R₀ -→* $ 7
run-R₀ = rstep₁ then rstep₂ then rstep₃ then rstep₄ then rstep₅
    then rstep₆ then rstep₇ then rstep₈ then rstep₉
    then IdPush (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) I-idv) ez
    then ξ-⟪⟫ (IdPush (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) (es ez))
    then ξ-⟪⟫ (ξ-⟪⟫ (IdPush (V-⟪⟫ V-$ I-seal) (es (es ez))))
    then ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (CancelR V-$ (es (es ez)))))
    then ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))))
    then ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ)))
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── THE CHAINED IDPUSH REDEX AND ITS CONTRACTUM BOTH TYPE ──────────────

⊢RV₂ : RΞ″ ∣ [] ⊢ ($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫ ⦂ ` 2
⊢RV₂ = env (mw-l (_ , es (es ez) , nameable-b) mw[]) ⊢$
            (conv-seal (es (es ez))) (wf-var (_ , es (es ez) , nameable-b))

⊢RS↑ : RΞ′ ∣ [] ⊢ RS↑ ⦂ ` 1
⊢RS↑ = env (mw-l (_ , es ez , nameable-b) mw[]) ⊢RV₂
            (conv-seal (es ez)) (wf-var (_ , es ez , nameable-b))

⊢Rlayer : RΞ ∣ [] ⊢ RS↑ ⟪ bind `ℕ ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢Rlayer = env (mw-b wf-ℕ mw[]) ⊢RS↑
               (conv-idv (_ , es ez , nameable-b))
               (wf-var (_ , ez , nameable-b))

⊢R₇-in : QΔ₁ ∣ [] ⊢ (RS↑ ⟪ bind `ℕ ∷ [] , id (` 1) ⟫)
                       ⟪ bind (` 0) ∷ [] , unseal 0 ⟫ ⦂ ` 0
⊢R₇-in = env (mw-b (wf-var (_ , ez , nameable-b)) mw[]) ⊢Rlayer
              (conv-unseal ez) (wf-var (_ , ez , nameable-b))

⊢R₇ : [] ∣ [] ⊢ R₇ ⦂ `ℕ
⊢R₇ = env (mw-b wf-ℕ mw[]) ⊢R₇-in (conv-unseal ez) wf-ℕ

-- the contractum: the inner wrapper now EXPORTS the chained rep ` 1, and
-- `env`'s last premise `RΞ ⊢ᵗ ` 1` is exactly `Rchain-scoped`.
⊢R₈-mid : RΞ ∣ [] ⊢ RS↑ ⟪ bind `ℕ ∷ [] , unseal 1 ⟫ ⦂ ` 1
⊢R₈-mid = env (mw-b wf-ℕ mw[]) ⊢RS↑
               (conv-unseal (es ez)) Rchain-scoped

⊢R₈-in : QΔ₁ ∣ [] ⊢ (RS↑ ⟪ bind `ℕ ∷ [] , unseal 1 ⟫)
                       ⟪ bind (` 0) ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢R₈-in = env (mw-b (wf-var (_ , ez , nameable-b)) mw[]) ⊢R₈-mid
              (conv-idv (_ , es ez , nameable-b)) (wf-var (_ , ez , nameable-b))

⊢R₈ : [] ∣ [] ⊢ R₈ ⦂ `ℕ
⊢R₈ = env (mw-b wf-ℕ mw[]) ⊢R₈-in (conv-unseal ez) wf-ℕ

------------------------------------------------------------------------
-- §11c  VARIANT (i) — AN ID-LAYER WITH A NON-TRIVIAL Θ₁
------------------------------------------------------------------------

-- Variant (i) asks for an IdPush redex whose INNER frame Θ₁ binds more
-- than one owner.  WHICH RULE COULD EVER MINT ONE?  Exactly one:
--
--   TyBeta   mints `bind A ∷ []`                       numBinds 1
--   Peel     mints `dual Θ`, which is ALL locks/unlocks numBinds 0
--   CancelR  mints NO frame (both are carried over)
--   IdPush   mints NO frame (both are carried over)
--   TyPeelR  mints `bind A ∷ Θ`               numBinds = 1 + numBinds Θ
--
-- so `numBinds Θ ≥ 2` is reachable ONLY through TyPeelR.  Those facts,
-- machine-checked:

numBinds-TyBeta : (A : Ty) → numBinds (bind A ∷ []) ≡ 1
numBinds-TyBeta A = refl

numBinds-dual : (Θ : CtxMorph) → numBinds (dual Θ) ≡ 0
numBinds-dual Θ = cong length (repsOf-dual Θ)

numBinds-TyPeelR : (A : Ty) (Θ : CtxMorph)
  → numBinds (bind A ∷ Θ) ≡ suc (numBinds Θ)
numBinds-TyPeelR A Θ = refl

-- ── A CLOSED SOURCE THAT REACHES TYPEELR ───────────────────────────────
--
--   G = ((ΛX. λx:X. ((ΛY. ΛZ. x) [ℕ]) [ℕ]) [ℕ]) · 7
--
-- `ΛY. ΛZ. x` has type ∀Y.∀Z.X, so the FIRST inner instantiation mints
-- the face `reveal 0 (`∀ (` 2)) = `∀ (id (` 2))` — an INERT ∀-face on a
-- one-owner frame — and the SECOND instantiation is a TyPeelR redex.  Its
-- contractum would be the wanted `numBinds 2` id-layer …

Gpoly Gbody Gfun G₀ : Term
Gpoly = Λ (Λ (` 0))                         -- ΛY. ΛZ. x
Gbody = (Gpoly ·[ `∀ (` 2) , `ℕ ]) ·[ ` 1 , `ℕ ]
Gfun  = Λ (ƛ (` 0) ∙ Gbody)
G₀    = (Gfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Gbody : (abst ∷ []) ∣ (` 0 ∷ []) ⊢ Gbody ⦂ ` 0
⊢Gbody = ⊢·[] (⊢·[] (⊢Λ (⊢Λ (⊢` here))) wf-ℕ) wf-ℕ

⊢G₀ : [] ∣ [] ⊢ G₀ ⦂ `ℕ
⊢G₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) ⊢Gbody)) wf-ℕ) ⊢$

_ : reveal 0 (`∀ (` 2)) ≡ `∀ (id (` 2))
_ = refl

GV G₁ G₂ G₃ G₄ G₅ : Term
GV = Λ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
G₁ = ((ƛ (` 0) ∙ Gbody) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
G₂ = ((ƛ (` 0) ∙ Gbody) · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
G₃ = (((Λ GV) ·[ `∀ (` 2) , `ℕ ]) ·[ ` 1 , `ℕ ])
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
G₄ = ((GV ⟪ bind `ℕ ∷ [] , `∀ (id (` 2)) ⟫) ·[ ` 1 , `ℕ ])
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
G₅ = ((Λ (($ 7) ⟪ lock 3 ∷ [] , seal 3 ⟫)) ·[ ` 3 , ` 0 ])
       ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , id (` 2) ⟫
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

gstep₁ : [] ⊢ G₀ -→ G₁
gstep₁ = ξ-·-l (TyBeta V-ƛ)

gstep₂ : [] ⊢ G₁ -→ G₂
gstep₂ = Peel V-ƛ V-$

gstep₃ : [] ⊢ G₂ -→ G₃
gstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

gstep₄ : [] ⊢ G₃ -→ G₄
gstep₄ = ξ-⟪⟫ (ξ-·[] (TyBeta (V-Λ (V-⟪⟫ V-$ I-seal))))

-- the TyPeelR step, whose contractum is the wanted `numBinds Θ₁ ≡ 2` layer.
-- Its face premise is the redex's own conversion, one `` `∀ `` inside —
-- here the identity at the OUTER owner, read under the ∀-binder.
⊢Gface : (abst ∷ exterior (bind `ℕ ∷ []) QΔ₁) ⊢ id (` 2) ∶ ` 2 ⇝ ` 2
⊢Gface = conv-idv (bind `ℕ , es (es ez) , nameable-b)

gstep₅ : [] ⊢ G₄ -→ G₅
gstep₅ = ξ-⟪⟫ (TyPeelR (V-Λ (V-⟪⟫ V-$ I-seal)) ⊢Gface)

_ : numBinds (bind `ℕ ∷ bind `ℕ ∷ []) ≡ 2
_ = refl

-- G₄ IS WELL TYPED …
⊢GV : QΞ₂ ∣ [] ⊢ GV ⦂ `∀ (` 2)
⊢GV = ⊢Λ (env (mw-l (_ , es (es ez) , nameable-b) mw[]) ⊢$
               (conv-seal (es (es ez))) (wf-var (_ , es (es ez) , nameable-b)))

⊢Gpkg : QΔ₁ ∣ [] ⊢ GV ⟪ bind `ℕ ∷ [] , `∀ (id (` 2)) ⟫ ⦂ `∀ (` 1)
⊢Gpkg = env (mw-b wf-ℕ mw[]) ⊢GV
             (conv-all (conv-idv (_ , es (es ez) , nameable-b)))
             (wf-∀ (wf-var (_ , es ez , nameable-b)))

⊢G₄ : [] ∣ [] ⊢ G₄ ⦂ `ℕ
⊢G₄ = env (mw-b wf-ℕ mw[]) (⊢·[] ⊢Gpkg wf-ℕ) (conv-unseal ez) wf-ℕ

-- … AND SO IS ITS TYPEELR CONTRACTUM, with the repaired rule.  The
-- pushed-in annotation is the INTERIOR ∀-body shifted past the new owner
-- (`` ` 3 ``, matching `wkᴹ 1 GV : `∀ (` 3)`), and the frame is plain `Θ`
-- — the `renᴮ suc Θ` double-shift that made `¬⊢G₅` true is gone.  So
-- variant (i) now HAS a well-typed closed-source instance.
⊢G₅-Λ : QΞ₃ ∣ [] ⊢ Λ (($ 7) ⟪ lock 3 ∷ [] , seal 3 ⟫) ⦂ `∀ (` 3)
⊢G₅-Λ = ⊢Λ (env (mw-l (bind `ℕ , es (es (es ez)) , nameable-b) mw[]) ⊢$
                (conv-seal (es (es (es ez))))
                (wf-var (bind `ℕ , es (es (es ez)) , nameable-b)))

⊢G₅-in : QΔ₁ ∣ [] ⊢ ((Λ (($ 7) ⟪ lock 3 ∷ [] , seal 3 ⟫)) ·[ ` 3 , ` 0 ])
                      ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , id (` 2) ⟫ ⦂ ` 0
⊢G₅-in = env (mw-b wf-ℕ (mw-b wf-ℕ mw[]))
              (⊢·[] ⊢G₅-Λ (wf-var (bind `ℕ , ez , nameable-b)))
              (conv-idv (bind `ℕ , es (es ez) , nameable-b))
              (wf-var (bind `ℕ , ez , nameable-b))

⊢G₅ : [] ∣ [] ⊢ G₅ ⦂ `ℕ
⊢G₅ = env (mw-b wf-ℕ mw[]) ⊢G₅-in (conv-unseal ez) wf-ℕ

-- ── AND THE MULTI-BIND ID-LAYER IT DELIVERS ────────────────────────────
-- The same shape, hand-built at the frame the repaired rule produces
-- (`bind A ∷ Θ`, no double shift): IdPush fires at `numBinds Θ₁ ≡ 2` and the
-- contractum TYPES.  So the multi-bind case is not itself an obstruction
-- — the lifting `shiftBy 2` is exactly absorbed by `pushBinds`.

K₀ K₁ : Term
K₀ = ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
        ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , id (` 2) ⟫) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
K₁ = ((($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
        ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , unseal 2 ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

_ : interior (bind `ℕ ∷ bind `ℕ ∷ []) QΔ₁ ≡ QΞ₃
_ = refl

⊢K₀-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                       ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , id (` 2) ⟫ ⦂ ` 0
⊢K₀-in = env (mw-b wf-ℕ (mw-b wf-ℕ mw[])) ⊢Dseal₇
              (conv-idv (_ , es (es ez) , nameable-b))
              (wf-var (_ , ez , nameable-b))

⊢K₀ : [] ∣ [] ⊢ K₀ ⦂ `ℕ
⊢K₀ = env (mw-b wf-ℕ mw[]) ⊢K₀-in (conv-unseal ez) wf-ℕ

kstep : [] ⊢ K₀ -→ K₁
kstep = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢K₁-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫)
                       ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , unseal 2 ⟫ ⦂ `ℕ
⊢K₁-in = env (mw-b wf-ℕ (mw-b wf-ℕ mw[])) ⊢Dseal₇
              (conv-unseal (es (es ez))) wf-ℕ

⊢K₁ : [] ∣ [] ⊢ K₁ ⦂ `ℕ
⊢K₁ = env (mw-b wf-ℕ mw[]) ⊢K₁-in (conv-id base-ℕ) wf-ℕ

------------------------------------------------------------------------
-- §12  THE WALL, PROBED FOR REACHABILITY POST-REPAIR
------------------------------------------------------------------------

-- THE WALL (notes/DECISIONS.md, "Peel FIXED and PROVEN"): IdPush,
-- CancelR and TyPeelR all need a contractum's inner wrapper to PRESENT A
-- REP `A` inside `Θ₂`'s interior, which fails when `Θ₂` LOCKS a slot that
-- `A` names.  The `¬IdPushCase` witness (proof/PreserveObstruct §4) is
-- exactly that: `Δi = bind (` 0) ∷ bind ℕ ∷ []`, `Θ₂ = lock 1 ∷ []`, so
-- `interior Θ₂ Δi = bind (` 0) ∷ masked (bind ℕ) ∷ []` — the owner at slot
-- 0 has rep ` 1, and slot 1 is blocked.
--
-- §10 recorded the verdict "NOT reachable".  THIS SECTION SHARPENS IT.
-- Change ONE character of §11's Q — instantiate the vacuous `ΛZ` at the
-- OUTER type variable `Y` instead of at `ℕ`:
--
--   L = ((ΛY. λx:Y. ((ΛZ. x) [Y])) [ℕ]) · 7
--
-- and the witness type context IS REACHED, from closed plain source:
-- after the inner TyBeta the owner's rep is the chained `` ` 0 ``, and the
-- Peel-minted `lock 1` inside blocks the very slot that rep names.
--
-- BUT NOT WHERE IT HURTS.  The blocked context appears as the interior of
-- the SEAL-faced (inert) wrapper, i.e. in a `Θ₁` position; the `Θ₂` of
-- every IdPush/CancelR redex on this run is lock-free, and both
-- contracta type.  The run reaches a VALUE.  So: THE WALL CONTEXT IS
-- REACHABLE, THE WALL CONFIGURATION IS NOT — which is precisely what
-- proof/WallReach turns into an invariant.

Lbody Lfun L₀ : Term
Lbody = (Λ (` 0)) ·[ ` 1 , ` 0 ]         -- (ΛZ. x) [Y]
Lfun  = Λ (ƛ (` 0) ∙ Lbody)
L₀    = (Lfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢Lbody : (abst ∷ []) ∣ (` 0 ∷ []) ⊢ Lbody ⦂ ` 0
⊢Lbody = ⊢·[] (⊢Λ (⊢` here)) (wf-var (abst , ez , nameable-a))

⊢L₀ : [] ∣ [] ⊢ L₀ ⦂ `ℕ
⊢L₀ = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) ⊢Lbody)) wf-ℕ) ⊢$

-- THE WITNESS CONTEXTS, verbatim from proof/PreserveObstruct §4.
LΔ LΞ : Ctxᵗ
LΔ = bind (` 0) ∷ bind `ℕ ∷ []
LΞ = bind (` 0) ∷ masked (bind `ℕ) ∷ []

_ : interior (bind (` 0) ∷ []) QΔ₁ ≡ LΔ
_ = refl

_ : interior (lock 1 ∷ []) LΔ ≡ LΞ
_ = refl

L₁ L₂ L₃ L₄ L₅ L₆ L₇ L₈ : Term
L₁ = ((ƛ (` 0) ∙ Lbody) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)
L₂ = ((ƛ (` 0) ∙ Lbody) · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
L₃ = ((Λ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)) ·[ ` 1 , ` 0 ])
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
L₄ = ((($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ bind (` 0) ∷ [] , id (` 1) ⟫)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
L₅ = ((($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ bind (` 0) ∷ [] , unseal 1 ⟫)
       ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
L₆ = ((($ 7) ⟪ lock 1 ∷ [] , id `ℕ ⟫) ⟪ bind (` 0) ∷ [] , id `ℕ ⟫)
       ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
L₇ = (($ 7) ⟪ bind (` 0) ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
L₈ = ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

lstep₁ : [] ⊢ L₀ -→ L₁
lstep₁ = ξ-·-l (TyBeta V-ƛ)

lstep₂ : [] ⊢ L₁ -→ L₂
lstep₂ = Peel V-ƛ V-$

lstep₃ : [] ⊢ L₂ -→ L₃
lstep₃ = ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal))

-- THE STEP THAT BUILDS THE WALL CONTEXT: the owner minted here has the
-- CHAINED rep ` 0, and the Peel-minted `lock 1` sits inside it.
lstep₄ : [] ⊢ L₃ -→ L₄
lstep₄ = ξ-⟪⟫ (TyBeta (V-⟪⟫ V-$ I-seal))

-- … and IdPush still fires, because its Θ₂ (`bind ℕ ∷ []`) is LOCK-FREE.
lstep₅ : [] ⊢ L₄ -→ L₅
lstep₅ = IdPush (V-⟪⟫ V-$ I-seal) ez

lstep₆ : [] ⊢ L₅ -→ L₆
lstep₆ = ξ-⟪⟫ (CancelR V-$ (es ez))

lstep₇ : [] ⊢ L₆ -→ L₇
lstep₇ = ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))

lstep₈ : [] ⊢ L₇ -→ L₈
lstep₈ = ξ-⟪⟫ (Drop$ base-ℕ)

lstep₉ : [] ⊢ L₈ -→ $ 7
lstep₉ = Drop$ base-ℕ

run-L₀ : [] ⊢ L₀ -→* $ 7
run-L₀ = lstep₁ then lstep₂ then lstep₃ then lstep₄ then lstep₅
    then lstep₆ then lstep₇ then lstep₈ then lstep₉ then done

-- ── every state on the run TYPES, including the two the wall touches ───

⊢Lseal₇ : LΔ ∣ [] ⊢ ($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫ ⦂ ` 1
⊢Lseal₇ = env (mw-l (_ , es ez , nameable-b) mw[]) ⊢$
               (conv-seal (es ez)) (wf-var (_ , es ez , nameable-b))

⊢L₄-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)
                       ⟪ bind (` 0) ∷ [] , id (` 1) ⟫ ⦂ ` 0
⊢L₄-in = env (mw-b (wf-var (_ , ez , nameable-b)) mw[]) ⊢Lseal₇
              (conv-idv (_ , es ez , nameable-b)) (wf-var (_ , ez , nameable-b))

⊢L₄ : [] ∣ [] ⊢ L₄ ⦂ `ℕ
⊢L₄ = env (mw-b wf-ℕ mw[]) ⊢L₄-in (conv-unseal ez) wf-ℕ

⊢L₅-in : QΔ₁ ∣ [] ⊢ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫)
                       ⟪ bind (` 0) ∷ [] , unseal 1 ⟫ ⦂ `ℕ
⊢L₅-in = env (mw-b (wf-var (_ , ez , nameable-b)) mw[]) ⊢Lseal₇
              (conv-unseal (es ez)) wf-ℕ

⊢L₅ : [] ∣ [] ⊢ L₅ ⦂ `ℕ
⊢L₅ = env (mw-b wf-ℕ mw[]) ⊢L₅-in (conv-id base-ℕ) wf-ℕ

-- THE PRECISE READING.  On this run the blocked slot lives inside a
-- wrapper that is a `Θ₁` (an INERT `seal` face, the CancelR pattern's
-- inner layer); the `Θ₂` of `lstep₅`'s IdPush and of `lstep₆`'s CancelR
-- is `bind ℕ ∷ []`, which locks nothing.  proof/WallReach turns "a Θ₂
-- never locks a slot a visible owner's rep names" into a theorem about
-- the only rule that mints locks at all (Peel's `dual`).

------------------------------------------------------------------------
-- §12b  THE WALL WITNESS, AFTER THE SCOPE MOVE
------------------------------------------------------------------------

-- §12 asked whether the wall CONFIGURATION is reachable.  The scope move
-- (strong.Reduction §2b, 2026-09-06) makes the question moot: the
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
-- it.  The rep `Y` the reveal hands back is therefore presented on the
-- outer boundary's own type context — where Y is live — instead of
-- inside the lock, which is exactly what `env`'s last premise refused.
-- The value's frame is unchanged, so `V` retypes where it was.

open import strong.proof.PreserveObstruct
  using (Δi; Θi; Vi; Ri; ⊢Ri; step-i)

wallR₁ : Term
wallR₁ = (Vi ⟪ [] ⋉ Θi , unseal 0 ⟫) ⟪ dropLocks Θi , mkId (` 1) ⟫

_ : wallR₁ ≡ (Vi ⟪ lock 1 ∷ [] , unseal 0 ⟫) ⟪ [] , id (` 1) ⟫
_ = refl

-- THE STEP THE OLD RULE COULD NOT TAKE SOUNDLY …
wallstep₁ : Δi ⊢ Ri -→ wallR₁
wallstep₁ = step-i

-- … AND THE CONTRACTUM TYPES, by the theorem.
⊢wallR₁ : Δi ∣ [] ⊢ wallR₁ ⦂ ` 1
⊢wallR₁ = preservation ⊢Ri wallstep₁

-- the value's own frame is untouched by the move
_ : interior ([] ⋉ Θi) (interior (dropLocks Θi) Δi)
      ≡ interior [] (interior Θi Δi)
_ = refl

-- AND THE RUN FINISHES.  The move brought the `seal X` of `Vi`'s own
-- outer layer directly under the pushed `unseal X`, so CancelR fires and
-- the result is a VALUE (at the abstract type Y — `7` is still sealed):
--
--   R₂ = ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫) ⟪ id Y ⟫) ⟪ id Y ⟫)
--
-- the mask/unmask pair sitting inertly on the frame it was moved into.
wallR₂ : Term
wallR₂ = (((($ 7) ⟪ [] , seal 1 ⟫)
             ⟪ unlock 1 ∷ lock 1 ∷ [] , id (` 1) ⟫)
             ⟪ [] , id (` 1) ⟫) ⟪ [] , id (` 1) ⟫

wallstep₂ : Δi ⊢ wallR₁ -→ wallR₂
wallstep₂ = ξ-⟪⟫ (CancelR (V-⟪⟫ V-$ I-seal) ez)

run-wall : Δi ⊢ Ri -→* wallR₂
run-wall = wallstep₁ then wallstep₂ then done

val-wallR₂ : Value wallR₂
val-wallR₂ = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) I-idv) I-idv

⊢wallR₂ : Δi ∣ [] ⊢ wallR₂ ⦂ ` 1
⊢wallR₂ = preservation* ⊢Ri run-wall

------------------------------------------------------------------------
-- §13  TYPEELR FROM CLOSED, PLAIN SOURCE — THE TWO FACES
------------------------------------------------------------------------

-- §11c's G reaches TyPeelR at an IDENTITY ∀-face, where the annotation
-- repair cannot fire.  This section reaches it at the two faces that DO
-- exercise the minted face `instReveal 0 s`, from ordinary System F:
--
--   §13a  a CONCEAL ∀-face — a POLYMORPHIC ARGUMENT that crossed a Peel.
--         Two machine-checked facts: (i) keeping `s` is untypeable, and
--         (ii) the mint `instReveal 0 s` TYPES, by the theorem — the case
--         the retired polarity index used to refuse.  The run then
--         continues to a value.
--   §13b  the REVEAL mirror image, likewise by the theorem.
--   §13c  the RECORD of the other contracta weighed for §13a's redex —
--         Jeremy's candidate and its neighbours — and why each was not
--         taken.
--
-- The two sources differ by ONE thing — whether the ∀ crosses the
-- boundary INWARD (as an argument, §13a) or OUTWARD (as a result, §13b).
-- Under the polarity index that difference decided TYPEABILITY; now it
-- decides only which owner each minted leaf cites.

open import strong.Preservation using (preservation-TyPeelR)
open import strong.proof.PreserveObstruct
  using (Δt; Wt; val-Wt; ⊢Wt; Θt; st; ⊢st; Wft; ⊢Wft; Rt; ⊢Rt; step-t;
         ⊢t-contractum)

------------------------------------------------------------------------
-- §13a  A CONCEAL ∀-FACE: the polymorphic argument
------------------------------------------------------------------------

--   J = ((ΛX. λx:X. λf:(∀Y. Y ⇒ X). (f [X]) · x) [ℕ]) · 7 · (ΛY. λy:Y. 3)
--
-- `f`'s type mentions X, so TyBeta's minted face CONCEALS X on f's
-- domain: `conceal 0 (∀Y. Y ⇒ X) = ∀ (id Y ↦ seal X)`, a CONCEAL ∀-face.
-- The Peel hands it to the crossing argument verbatim, and the body's
-- `f [X]` is then a TyPeelR redex at that face.

JT : Ty                                  -- ∀Y. Y ⇒ X, read under X
JT = `∀ (` 0 ⇒ ` 1)

JB : Ty                                  -- the ΛX body type
JB = ` 0 ⇒ (JT ⇒ ` 0)

Jbody Jfun J₀ : Term
Jbody = ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · (` 1))
Jfun  = Λ (ƛ (` 0) ∙ Jbody)
J₀    = ((Jfun ·[ JB , `ℕ ]) · ($ 7)) · Wt

⊢JT : ∀ {Δ} → (abst ∷ Δ) ⊢ᵗ JT
⊢JT = wf-∀ (wf-⇒ (wf-var (abst , ez , nameable-a))
                 (wf-var (abst , es ez , nameable-a)))

⊢Jfun : [] ∣ [] ⊢ Jfun ⦂ `∀ JB
⊢Jfun = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a))
               (⊢ƛ ⊢JT (⊢· (⊢·[] (⊢` here) (wf-var (abst , ez , nameable-a)))
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
         ⟪ bind `ℕ ∷ [] , seal 0 ↦ ((`∀ st) ↦ unseal 0) ⟫) · ($ 7)) · Wt
J₂ = (((ƛ (` 0) ∙ Jbody) · QS₇)
        ⟪ bind `ℕ ∷ [] , (`∀ st) ↦ unseal 0 ⟫) · Wt
J₃ = ((ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · QS₇))
        ⟪ bind `ℕ ∷ [] , (`∀ st) ↦ unseal 0 ⟫) · Wt
J₄ = ((ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · QS₇)) · Wft)
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
J₅ = (Rt · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

jstep₁ : [] ⊢ J₀ -→ J₁
jstep₁ = ξ-·-l (ξ-·-l (TyBeta V-ƛ))

jstep₂ : [] ⊢ J₁ -→ J₂
jstep₂ = ξ-·-l (Peel V-ƛ V-$)

jstep₃ : [] ⊢ J₂ -→ J₃
jstep₃ = ξ-·-l (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal)))

-- THE CROSSING: the polymorphic argument acquires the CONCEAL ∀-face.
jstep₄ : [] ⊢ J₃ -→ J₄
jstep₄ = Peel V-ƛ (V-Λ V-ƛ)

jstep₅ : [] ⊢ J₄ -→ J₅
jstep₅ = ξ-⟪⟫ (Beta (V-⟪⟫ (V-Λ V-ƛ) I-all))

run-J₀ : [] ⊢ J₀ -→* J₅
run-J₀ = jstep₁ then jstep₂ then jstep₃ then jstep₄ then jstep₅ then done

-- J₅'s head IS proof/PreserveObstruct §2's redex, and it is TYPED there.
_ : J₅ ≡ (((Wt ⟪ Θt , `∀ st ⟫) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · QS₇)
           ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
_ = refl

⊢J₅-head : Δt ∣ [] ⊢ Rt ⦂ (` 0 ⇒ ` 0)
⊢J₅-head = ⊢Rt

J₆head J₆ : Term
J₆head = (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 0 ])
           ⟪ bind (` 0) ∷ Θt , instReveal 0 st ⟫
J₆     = (J₆head · QS₇) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

-- … and TyPeelR fires on it, from this closed source.  (Fact (ii) below
-- types both `J₆head` and `J₆`.)
jstep₆ : [] ⊢ J₅ -→ J₆
jstep₆ = ξ-⟪⟫ (ξ-·-l step-t)

-- ── FACT (i): KEEPING `s` IS UNTYPEABLE ────────────────────────────────
-- The note's contractum keeps the face `s`, whose exterior body still
-- mentions the ∀-bound `` ` 0 `` where `env` now demands the
-- INSTANTIATED body: the domain leaf `id (` 0)` would have to convert
-- `` ` 1 `` (the new owner's rep, read inside) to `` ` 0 ``, and an
-- identity converts a type to ITSELF (`conv-id-refl`).
¬⊢J-plain :
  ¬ (Δt ∣ [] ⊢ (wkᴹ 1 Wt ·[ ` 0 ⇒ `ℕ , ` 0 ])
                 ⟪ bind (` 0) ∷ Θt , st ⟫ ⦂ (` 0 ⇒ ` 0))
¬⊢J-plain (env _ (⊢·[] _ _) (conv-fun ⊢s ⊢t) _) with conv-id-refl ⊢s
... | ()

-- ── FACT (ii): THE MINT TYPES ──────────────────────────────────────────
-- `instReveal 0 st` inserts the instantiation leaf at the ∀-bound slot:

_ : instReveal 0 st ≡ seal 0 ↦ seal 1
_ = refl

J-face-ctx : Ctxᵗ
J-face-ctx = exterior (bind (` 0) ∷ Θt) Δt

_ : J-face-ctx ≡ bind (` 0) ∷ bind `ℕ ∷ []
_ = refl

-- EACH LEAF CONCEALS AT ITS OWN OWNER, and that is the whole content …
-- the INSERTED leaf: the new owner's rep ` 1, concealed at its own name
J-dom : J-face-ctx ⊢ seal 0 ∶ ` 1 ⇝ ` 0
J-dom = conv-seal ez

-- the face's OWN leaf: ℕ concealed at the crossed boundary's owner
J-cod : J-face-ctx ⊢ seal 1 ∶ `ℕ ⇝ ` 1
J-cod = conv-seal (es ez)

-- … and so does the TREE.  Under the retired polarity index this was the
-- REFUTATION: `seal 0` sits CONTRAVARIANTLY and `seal 1` COVARIANTLY, so
-- no single `p` typed both.  Per variable there is nothing to reconcile —
-- Y's name is on the interior side (the `bind` this rule just pushed),
-- X's on the exterior side (behind Θt's `lock`).
⊢J-face : J-face-ctx ⊢ seal 0 ↦ seal 1 ∶ (` 0 ⇒ `ℕ) ⇝ (` 1 ⇒ ` 1)
⊢J-face = conv-fun J-dom J-cod

-- HENCE THE LANDED CONTRACTUM TYPES, by the theorem — the head of J₆.
⊢J₆head : Δt ∣ [] ⊢ J₆head ⦂ (` 0 ⇒ ` 0)
⊢J₆head = preservation-TyPeelR val-Wt ⊢st ⊢Rt

_ : ⊢J₆head ≡ ⊢t-contractum
_ = refl

-- … and so does the whole state, one `env` out.
⊢J₆ : [] ∣ [] ⊢ J₆ ⦂ `ℕ
⊢J₆ = env (mw-b wf-ℕ mw[]) (⊢· ⊢J₆head ⊢QS₇) (conv-unseal ez) wf-ℕ

-- ── THE RUN CONTINUES, TO A VALUE ──────────────────────────────────────
--
-- Eight more steps: the TyBeta the peel exposed (the interior ∀ is now
-- instantiated at the owner TyPeelR bound), TWO Peels — the argument `7`
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

-- TyBeta's mint at the new owner: a conceal on the domain, a transparent
-- base identity on the codomain.
_ : reveal 0 (` 0 ⇒ `ℕ) ≡ seal 0 ↦ id `ℕ
_ = refl

JV : Term                      -- λy. 3, behind the freshly born boundary
JV = (ƛ (` 0) ∙ ($ 3)) ⟪ bind (` 0) ∷ [] , seal 0 ↦ id `ℕ ⟫

val-JV : Value JV
val-JV = V-⟪⟫ V-ƛ I-fun

-- the two duals the two Peels mint
_ : dual (bind (` 0) ∷ Θt) ≡ lock 0 ∷ unlock 1 ∷ []
_ = refl

_ : dual (bind (` 0) ∷ []) ≡ lock 0 ∷ []
_ = refl

JW JW′ : Term                  -- `7` after the first / the second crossing
JW  = wkᴹ 1 QS₇ ⟪ dual (bind (` 0) ∷ Θt) , seal 0 ⟫
JW′ = wkᴹ 1 JW ⟪ dual (bind (` 0) ∷ []) , seal 0 ⟫

_ : JW ≡ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫) ⟪ lock 0 ∷ unlock 1 ∷ [] , seal 0 ⟫
_ = refl

val-JW : Value JW
val-JW = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal

val-JW′ : Value JW′
val-JW′ = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal) I-seal

J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ J₁₃ : Term
J₇  = ((JV ⟪ bind (` 0) ∷ Θt , seal 0 ↦ seal 1 ⟫) · QS₇)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
J₈  = ((JV · JW) ⟪ bind (` 0) ∷ Θt , seal 1 ⟫) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
J₉  = ((((ƛ (` 0) ∙ ($ 3)) · JW′) ⟪ bind (` 0) ∷ [] , id `ℕ ⟫)
         ⟪ bind (` 0) ∷ Θt , seal 1 ⟫)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
J₁₀ = ((($ 3) ⟪ bind (` 0) ∷ [] , id `ℕ ⟫) ⟪ bind (` 0) ∷ Θt , seal 1 ⟫)
        ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
J₁₁ = (($ 3) ⟪ bind (` 0) ∷ Θt , seal 1 ⟫) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
J₁₂ = (($ 3) ⟪ bind (` 0) ∷ Θt , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
J₁₃ = ($ 3) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

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

-- the CANCEL: the inner conceal at the owner the TyPeelR-born frame
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
⊢Hfun = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a))
               (⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) (⊢` (there here)))))

⊢H₀ : [] ∣ [] ⊢ H₀ ⦂ (`ℕ ⇒ `ℕ)
⊢H₀ = ⊢·[] (⊢· (⊢·[] ⊢Hfun wf-ℕ) ⊢$) wf-ℕ

-- the REVEAL ∀-face, minted by the same rule that minted §13a's conceal
_ : reveal 0 HB ≡ seal 0 ↦ (`∀ (id (` 0) ↦ unseal 1))
_ = refl

HV H₁ H₂ H₃ H₄ : Term
HV = Λ (ƛ (` 0) ∙ (($ 7) ⟪ lock 1 ∷ [] , seal 1 ⟫))
H₁ = (((ƛ (` 0) ∙ (Λ (ƛ (` 0) ∙ (` 1))))
         ⟪ bind `ℕ ∷ [] , seal 0 ↦ (`∀ (id (` 0) ↦ unseal 1)) ⟫) · ($ 7))
       ·[ ` 0 ⇒ `ℕ , `ℕ ]
H₂ = (((ƛ (` 0) ∙ (Λ (ƛ (` 0) ∙ (` 1)))) · QS₇)
        ⟪ bind `ℕ ∷ [] , `∀ (id (` 0) ↦ unseal 1) ⟫) ·[ ` 0 ⇒ `ℕ , `ℕ ]
H₃ = (HV ⟪ bind `ℕ ∷ [] , `∀ (id (` 0) ↦ unseal 1) ⟫) ·[ ` 0 ⇒ `ℕ , `ℕ ]
H₄ = ((Λ (ƛ (` 0) ∙ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫))) ·[ ` 0 ⇒ ` 2 , ` 0 ])
       ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , seal 0 ↦ unseal 1 ⟫

hstep₁ : [] ⊢ H₀ -→ H₁
hstep₁ = ξ-·[] (ξ-·-l (TyBeta V-ƛ))

hstep₂ : [] ⊢ H₁ -→ H₂
hstep₂ = ξ-·[] (Peel V-ƛ V-$)

hstep₃ : [] ⊢ H₂ -→ H₃
hstep₃ = ξ-·[] (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ I-seal)))

-- THE FACE PREMISE, read off the redex's own `env`, one `` `∀ `` inside.
⊢Hface : (abst ∷ exterior (bind `ℕ ∷ []) []) ⊢ id (` 0) ↦ unseal 1
           ∶ (` 0 ⇒ ` 1) ⇝ (` 0 ⇒ `ℕ)
⊢Hface = conv-fun (conv-idv (abst , ez , nameable-a)) (conv-unseal (es ez))

-- the mint: the inserted `seal 0` conceals the owner this rule binds,
-- under an `unseal 1` that reveals the crossed boundary's.
_ : instReveal 0 (id (` 0) ↦ unseal 1) ≡ seal 0 ↦ unseal 1
_ = refl

hstep₄ : [] ⊢ H₃ -→ H₄
hstep₄ = TyPeelR (V-Λ V-ƛ) ⊢Hface

run-H₀ : [] ⊢ H₀ -→* H₄
run-H₀ = hstep₁ then hstep₂ then hstep₃ then hstep₄ then done

-- ── AND THE CONTRACTUM TYPES — by the theorem, not by hand ─────────────

⊢HV : (bind `ℕ ∷ []) ∣ [] ⊢ HV ⦂ `∀ (` 0 ⇒ ` 1)
⊢HV = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a))
             (env (mw-l (bind `ℕ , es ez , nameable-b) mw[]) ⊢$
                  (conv-seal (es ez))
                  (wf-var (bind `ℕ , es ez , nameable-b))))

⊢H₃ : [] ∣ [] ⊢ H₃ ⦂ (`ℕ ⇒ `ℕ)
⊢H₃ = ⊢·[] (env (mw-b wf-ℕ mw[]) ⊢HV
                (conv-all ⊢Hface)
                (wf-∀ (wf-⇒ (wf-var (abst , ez , nameable-a)) wf-ℕ)))
           wf-ℕ

⊢H₄ : [] ∣ [] ⊢ H₄ ⦂ (`ℕ ⇒ `ℕ)
⊢H₄ = preservation-TyPeelR (V-Λ V-ƛ) ⊢Hface ⊢H₃

-- and H₄ is ONE TyBeta from a value, so the repaired rule does not
-- strand the run either.
hstep₅ : [] ⊢ H₄
       -→ ((ƛ (` 0) ∙ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫))
             ⟪ bind (` 0) ∷ [] , reveal 0 (` 0 ⇒ ` 2) ⟫)
            ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , seal 0 ↦ unseal 1 ⟫
hstep₅ = ξ-⟪⟫ (TyBeta V-ƛ)

val-H₅ : Value (((ƛ (` 0) ∙ (($ 7) ⟪ lock 2 ∷ [] , seal 2 ⟫))
                   ⟪ bind (` 0) ∷ [] , reveal 0 (` 0 ⇒ ` 2) ⟫)
                  ⟪ bind `ℕ ∷ bind `ℕ ∷ [] , seal 0 ↦ unseal 1 ⟫)
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

-- (i) JEREMY'S CANDIDATE, first form: keep the face `id X ↦ seal X` and
--     instantiate the interior at the FRESH owner Y.  The id leaf's
--     source is then X while the interior's domain is Y, and an identity
--     converts a type to ITSELF.
Cj1 : Term
Cj1 = (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 0 ])
        ⟪ bind (` 0) ∷ Θt , id (` 1) ↦ seal 1 ⟫

¬⊢Cj1 : ¬ (Δt ∣ [] ⊢ Cj1 ⦂ (` 0 ⇒ ` 0))
¬⊢Cj1 (env _ (⊢·[] _ _) (conv-fun ⊢s ⊢t) _) with conv-id-refl ⊢s
... | ()

-- (ii) … second form: instantiate the interior at X itself.  X is MASKED
--      inside the boundary (`↓X`), so the instantiation is not even a
--      well-formed type there.
Cj2 : Term
Cj2 = (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 1 ])
        ⟪ bind (` 0) ∷ Θt , id (` 1) ↦ seal 1 ⟫

¬⊢Cj2 : ∀ {B} → ¬ (Δt ∣ [] ⊢ Cj2 ⦂ B)
¬⊢Cj2 (env _ (⊢·[] _ (wf-var (_ , es ez , ()))) _ _)

-- (iii) the same face with the lock LIFTED for the instantiation (`scope`
--       applies the head last, so an `unlock X` in front makes X visible
--       inside).  TYPES — but it un-masks what the crossing masked.
Cu : Term
Cu = (Wt ·[ ` 0 ⇒ `ℕ , ` 0 ]) ⟪ unlock 0 ∷ Θt , id (` 0) ↦ seal 0 ⟫

⊢Cu : Δt ∣ [] ⊢ Cu ⦂ (` 0 ⇒ ` 0)
⊢Cu = env (mw-u ez (mw-l (bind `ℕ , ez , nameable-b) mw[]))
          (⊢·[] ⊢Wt (wf-var (bind `ℕ , ez , nameable-b)))
          (conv-fun (conv-idv (bind `ℕ , ez , nameable-b)) (conv-seal ez))
          (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b))
                (wf-var (bind `ℕ , ez , nameable-b)))

-- (iv) or the lock simply REMOVED (a lock binds nothing, so dropping it
--      is shift-free).  TYPES — but it discards the crossing's mask.
Cr : Term
Cr = (Wt ·[ ` 0 ⇒ `ℕ , ` 0 ]) ⟪ [] , id (` 0) ↦ seal 0 ⟫

⊢Cr : Δt ∣ [] ⊢ Cr ⦂ (` 0 ⇒ ` 0)
⊢Cr = env mw[]
          (⊢·[] ⊢Wt (wf-var (bind `ℕ , ez , nameable-b)))
          (conv-fun (conv-idv (bind `ℕ , ez , nameable-b)) (conv-seal ez))
          (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b))
                (wf-var (bind `ℕ , ez , nameable-b)))

-- (v) OPTION B: instantiate the interior at the RESOLVED argument (X's
--     own rep ℕ), keep Θ, and mint the face by `conceal` on the type.
--     TYPES — but it RESOLVES the owner, which the interior may not see.
Cb : Term
Cb = (Wt ·[ ` 0 ⇒ `ℕ , `ℕ ]) ⟪ Θt , unseal 0 ↦ seal 0 ⟫

_ : conceal 0 (` 0 ⇒ ` 0) ≡ unseal 0 ↦ seal 0
_ = refl

⊢Cb : Δt ∣ [] ⊢ Cb ⦂ (` 0 ⇒ ` 0)
⊢Cb = env (mw-l (bind `ℕ , ez , nameable-b) mw[])
          (⊢·[] ⊢Wt wf-ℕ)
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b))
                (wf-var (bind `ℕ , ez , nameable-b)))

-- (vi) Option B's REVEAL mirror, on §13b's H: no lock is in the way, so
--      the resolve variant lands on the same shape the theorem gives.
CbH : Term
CbH = (HV ·[ ` 0 ⇒ ` 1 , `ℕ ]) ⟪ bind `ℕ ∷ [] , id `ℕ ↦ unseal 0 ⟫

⊢CbH : [] ∣ [] ⊢ CbH ⦂ (`ℕ ⇒ `ℕ)
⊢CbH = env (mw-b wf-ℕ mw[]) (⊢·[] ⊢HV wf-ℕ)
           (conv-fun (conv-id base-ℕ) (conv-unseal ez)) (wf-⇒ wf-ℕ wf-ℕ)

-- THE VERDICT.  (i) and (ii) are untypeable outright; (iii)–(vi) type,
-- but each pays with the boundary's own discipline — (iii)/(iv) weaken
-- the mask the crossing installed, (v)/(vi) resolve the owner inside.
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
--      BIND on the boundary (`bind A ∷ Θ`) and instantiates the interior
--      at the fresh NAME `` ` 0 ``; that is why the boundary is a LIST —
--      a context morphism — and not a single reveal-or-conceal.
--
-- Below: the SAME closed program, in v2, run to a VALUE in five steps,
-- with every step pinned by `det`.  Step 4 is the one that used to die.
--
-- RENDERED (scripts/render_term.sh, `showTmIn 0`):
--
--  E₀  ((ΛX. (λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))) [ℕ] · (ΛZ. (λx:Z. x)))
--  E₁  (((λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))
--         ⟪ ↑X:=ℕ , ((∀Y. (id Y ↦ id Y)) ↦ (∀Y. (id Y ↦ id Y))) ⟫)
--        · (ΛZ. (λx:Z. x)))
--  E₂  (((λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))
--         · ((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Y. (id Y ↦ id Y)) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₃  ((ΛY. ((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Z. (id Z ↦ id Z)) ⟫) [Y])
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₄  ((ΛY. ((ΛX′. (λx:X′. x)) [Z] ⟪ ↑Z:=Y , ↓X , (seal Z ↦ unseal Z) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
--  E₅  ((ΛY. (((λx:X′. x) ⟪ ↑X′:=Z , (seal X′ ↦ unseal X′) ⟫)
--               ⟪ ↑Z:=Y , ↓X , (seal Z ↦ unseal Z) ⟫))
--        ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)                      -- a VALUE
--
-- E₃ is the old design's fourth line, and E₄ is where the two designs
-- part: `↑Z:=Y , ↓X` is a boundary that MASKS X and BINDS a fresh Z at
-- the rep Y — no type is pushed into the sealed body, and Y is read in
-- the plain exterior, where it is in scope.

-- ── the source ─────────────────────────────────────────────────────────

EID EBod : Ty
EID  = `∀ (` 0 ⇒ ` 0)                    -- ∀Z. Z ⇒ Z   (= ∀Y. Y ⇒ Y)
EBod = EID ⇒ EID                         -- the ΛX body type

Earg Ebody Efun E₀ : Term
Earg  = Λ (ƛ (` 0) ∙ (` 0))              -- ΛZ. λz:Z. z
Ebody = Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ])   -- ΛY. f [Y]
Efun  = Λ (ƛ EID ∙ Ebody)                -- ΛX. λf:(∀Z.Z⇒Z). ΛY. f [Y]
E₀    = (Efun ·[ EBod , `ℕ ]) · Earg

⊢EID : ∀ {Δ} → (abst ∷ Δ) ⊢ᵗ EID
⊢EID = wf-∀ (wf-⇒ (wf-var (abst , ez , nameable-a))
                  (wf-var (abst , ez , nameable-a)))

⊢Earg : ∀ {Δ Γ} → Δ ∣ Γ ⊢ Earg ⦂ EID
⊢Earg = ⊢Λ (⊢ƛ (wf-var (abst , ez , nameable-a)) (⊢` here))

⊢Efun : [] ∣ [] ⊢ Efun ⦂ `∀ EBod
⊢Efun = ⊢Λ (⊢ƛ ⊢EID
               (⊢Λ (⊢·[] (⊢` here) (wf-var (abst , ez , nameable-a)))))

⊢E₀ : [] ∣ [] ⊢ E₀ ⦂ EID
⊢E₀ = ⊢· (⊢·[] ⊢Efun wf-ℕ) ⊢Earg

-- ── the two faces the run uses ─────────────────────────────────────────

-- X does not occur in EBod, so TyBeta's mint is TRANSPARENT on both
-- halves: the crossing hands the argument an all-identity ∀-face.
Eid∀ : Conv
Eid∀ = `∀ (id (` 0) ↦ id (` 0))

_ : reveal 0 EBod ≡ Eid∀ ↦ Eid∀
_ = refl

-- ── STEP 1 — TYBETA.  The owner X := ℕ is minted.

E₁ : Term
E₁ = ((ƛ EID ∙ Ebody) ⟪ bind `ℕ ∷ [] , Eid∀ ↦ Eid∀ ⟫) · Earg

estep₁ : [] ⊢ E₀ -→ E₁
estep₁ = ξ-·-l (TyBeta V-ƛ)

-- ── STEP 2 — PEEL.  `ΛZ. λz:Z. z` crosses; the dual masks the new owner.

_ : dual (bind `ℕ ∷ []) ≡ lock 0 ∷ []
_ = refl

_ : wkᴹ 1 Earg ≡ Earg
_ = refl

EW : Term                        -- the argument, behind the crossing
EW = Earg ⟪ lock 0 ∷ [] , Eid∀ ⟫

val-EW : Value EW
val-EW = V-⟪⟫ (V-Λ V-ƛ) I-all

E₂ : Term
E₂ = ((ƛ EID ∙ Ebody) · EW) ⟪ bind `ℕ ∷ [] , Eid∀ ⟫

estep₂ : [] ⊢ E₁ -→ E₂
estep₂ = Peel V-ƛ (V-Λ V-ƛ)

-- ── STEP 3 — BETA, under ξ-⟪⟫.  `substᵐ`'s Λ clause shifts the crossed
-- value past ΛY: the LOCK's name moves (lock 0 ↦ lock 1) and nothing
-- else does — a name, not a spelling.

EW↑ : Term
EW↑ = Earg ⟪ lock 1 ∷ [] , Eid∀ ⟫

_ : ⇑ᴹ EW ≡ EW↑
_ = refl

_ : Ebody [ EW ]ᵐ ≡ Λ (EW↑ ·[ ` 0 ⇒ ` 0 , ` 0 ])
_ = refl

E₃ : Term
E₃ = (Λ (EW↑ ·[ ` 0 ⇒ ` 0 , ` 0 ])) ⟪ bind `ℕ ∷ [] , Eid∀ ⟫

estep₃ : [] ⊢ E₂ -→ E₃
estep₃ = ξ-⟪⟫ (Beta val-EW)

-- ── THE STEP THE OLD DESIGN DIED ON ────────────────────────────────────
--
-- E₃'s inner redex is `EW↑ ·[ ` 0 ⇒ ` 0 , ` 0 ]`: the crossed value,
-- type-applied to the Λ-bound Y — a variable bound AFTER the boundary
-- was born.  Here are the two type contexts, at that redex.

EΔ₃ : Ctxᵗ                       -- the ambient: Y abstract, X := ℕ
EΔ₃ = abst ∷ bind `ℕ ∷ []

_ : interior (bind `ℕ ∷ []) [] ≡ bind `ℕ ∷ []
_ = refl

E-int E-ext : Ctxᵗ
E-int = interior (lock 1 ∷ []) EΔ₃
E-ext = exterior (lock 1 ∷ []) EΔ₃

-- THE INTERIOR IS THE EXTERIOR WITH X MASKED — NOT TRUNCATED.  The old
-- design's interior at this point was Γ↓X = ∅.  RENDERED
-- (`showTCtxAt 99 0 (λ { 0 → "Y" ; _ → "X" })`, so that the names agree
-- with the trace above):
--
--   E-int   Y Λ-bound , ⌷[X := ℕ]
--   E-ext   Y Λ-bound , X := ℕ
--
_ : E-int ≡ abst ∷ masked (bind `ℕ) ∷ []
_ = refl

_ : E-ext ≡ EΔ₃
_ = refl

-- Y is still nameable inside …
E-Y-inside : E-int ⊢ᵗ ` 0
E-Y-inside = wf-var (abst , ez , nameable-a)

-- … and X still is not: the mask does its job.
E-X-hidden : ¬ (E-int ⊢ᵗ ` 1)
E-X-hidden (wf-var (_ , es ez , ()))

-- ── STEP 4 — TYPEELR, under ξ-Λ.  The type argument Y is NOT pushed into
-- the crossed body; it is recorded as a NEW BIND, `bind (` 0)`, and the
-- interior is instantiated at that bind's own name.  The face's abstract
-- slot becomes the fresh owner, so each identity leaf becomes the
-- instantiation step.

E-face-ctx : Ctxᵗ
E-face-ctx = abst ∷ exterior (lock 1 ∷ []) EΔ₃

⊢Es : E-face-ctx ⊢ id (` 0) ↦ id (` 0) ∶ (` 0 ⇒ ` 0) ⇝ (` 0 ⇒ ` 0)
⊢Es = conv-fun (conv-idv (abst , ez , nameable-a))
               (conv-idv (abst , ez , nameable-a))

_ : instReveal 0 (id (` 0) ↦ id (` 0)) ≡ seal 0 ↦ unseal 0
_ = refl

E₄ : Term
E₄ = (Λ ((Earg ·[ ` 0 ⇒ ` 0 , ` 0 ])
           ⟪ bind (` 0) ∷ lock 1 ∷ [] , seal 0 ↦ unseal 0 ⟫))
       ⟪ bind `ℕ ∷ [] , Eid∀ ⟫

estep₄ : [] ⊢ E₃ -→ E₄
estep₄ = ξ-⟪⟫ (ξ-Λ (TyPeelR (V-Λ V-ƛ) ⊢Es))

-- ── STEP 5 — TYBETA, inside.  The ΛZ is consumed against the bind
-- TyPeelR just made, and the result is a VALUE.

_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

E₅ : Term
E₅ = (Λ (((ƛ (` 0) ∙ (` 0)) ⟪ bind (` 0) ∷ [] , seal 0 ↦ unseal 0 ⟫)
           ⟪ bind (` 0) ∷ lock 1 ∷ [] , seal 0 ↦ unseal 0 ⟫))
       ⟪ bind `ℕ ∷ [] , Eid∀ ⟫

estep₅ : [] ⊢ E₄ -→ E₅
estep₅ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (TyBeta V-ƛ)))

val-E₅ : Value E₅
val-E₅ = V-⟪⟫ (V-Λ (V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun)) I-all

run-E : [] ⊢ E₀ -→* E₅
run-E = estep₁ then estep₂ then estep₃ then estep₄ then estep₅ then done

-- THE ANSWER TYPES, at the source's own type ∀Y. Y ⇒ Y.
⊢E₅ : [] ∣ [] ⊢ E₅ ⦂ EID
⊢E₅ = preservation* ⊢E₀ run-E

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

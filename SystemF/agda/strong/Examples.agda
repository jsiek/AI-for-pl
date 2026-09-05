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
⊢W₆₀ = env bw[] ⊢$ (conv-seal (es ez))
           (wf-var (bind `ℕ , es ez , vis-b))

⊢W₆₁ : S₆₁ ∣ [] ⊢ W₆₁ ⦂ ` 0
⊢W₆₁ = env (bw-b wf-ℕ bw[]) ⊢W₆₀
           (conv-idv {p = ↑ˢ} (bind `ℕ , es ez , vis-b))
           (wf-var (bind `ℕ , ez , vis-b))

⊢T₆ : Δ₆ ∣ [] ⊢ T₆ ⦂ `ℕ
⊢T₆ = env (bw-b wf-ℕ bw[]) ⊢W₆₁ (conv-unseal ez) wf-ℕ

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
⊢T₆-1-in = env (bw-b wf-ℕ bw[]) ⊢W₆₀ (conv-unseal (es ez)) wf-ℕ

⊢T₆-1 : Δ₆ ∣ [] ⊢ T₆-1 ⦂ `ℕ
⊢T₆-1 = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢T₆-1-in (conv-id base-ℕ) wf-ℕ

-- STEP 2 — the seal/unseal pair is now ADJACENT: the ordinary cancel fires.
T₆-2 : Term
T₆-2 = (($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

cancel-T₆ : Δ₆ ⊢ T₆-1 -→ T₆-2
cancel-T₆ = ξ-⟪⟫ (CancelR V-$ (es ez))

⊢T₆-2-in : S₆₁ ∣ [] ⊢ ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢T₆-2-in = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

⊢T₆-2 : Δ₆ ∣ [] ⊢ T₆-2 ⦂ `ℕ
⊢T₆-2 = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢T₆-2-in (conv-id base-ℕ) wf-ℕ

-- STEPS 3, 4 — base faces over a numeral.
run-T₆ : Δ₆ ⊢ T₆ -→* $ 7
run-T₆ = push-T₆
    then cancel-T₆
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
  env (bw-b wf-ℕ bw[])
      (env (bw-l (_ , ez , vis-b) bw[]) ⊢$
           (conv-seal ez) (wf-var (_ , ez , vis-b)))
      (conv-unseal ez)
      wf-ℕ

-- the pair is NOT a value (the outer face is active) and the cancel fires.
-- The residue binds Θ↑'s owner and nothing else: the mini-core's extra
-- `lockBinds` masked an exterior slot that does not exist (repair 3a,
-- proof/MaskFacts.agda `¬Bwf-cancel-residue`).
cancel-step : [] ⊢ cancelTm -→ ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
cancel-step = CancelR V-$ ez

drop-step : [] ⊢ ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫ -→ $ 7
drop-step = Drop$ base-ℕ

run-cancelTm : [] ⊢ cancelTm -→* $ 7
run-cancelTm = cancel-step then drop-step then done

_ : idc `ℕ ≡ id `ℕ
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
⊢LA-in = env bw[] ⊢$ (conv-seal (es (es ez)))
             (wf-var (bind `ℕ , es (es ez) , vis-b))

⊢LA : S₆₂ ∣ [] ⊢ LA ⦂ ` 1
⊢LA = env (bw-b (wf-var (bind `ℕ , ez , vis-b)) bw[]) ⊢LA-in
          (conv-idv {p = ↑ˢ} (bind `ℕ , es (es ez) , vis-b))
          (wf-var (bind `ℕ , es ez , vis-b))

⊢LB : S₆₁ ∣ [] ⊢ LB ⦂ ` 0
⊢LB = env (bw-b wf-ℕ bw[]) ⊢LA
          (conv-idv {p = ↑ˢ} (bind `ℕ , es ez , vis-b))
          (wf-var (bind `ℕ , ez , vis-b))

⊢T₈ : Δ₆ ∣ [] ⊢ T₈ ⦂ `ℕ
⊢T₈ = env (bw-b wf-ℕ bw[]) ⊢LB (conv-unseal ez) wf-ℕ

-- The stack resolves ONE LAYER PER STEP, outermost first: each IdPush moves
-- the active face one layer inward toward the seal, so any depth
-- terminates.  (IdAbsorb needed `⊳` to merge the frames and could not do
-- this one — the inner layer's context morphism `bind (` 0)` names the next layer's
-- owner, IdLayerProbe §4c.  IdPush touches no frame.)
T₈-1 T₈-2 T₈-3 : Term
T₈-1 = (LA ⟪ bind `ℕ ∷ [] , unseal 1 ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
T₈-2 = (((($ 7) ⟪ [] , seal 2 ⟫) ⟪ bind (` 0) ∷ [] , unseal 2 ⟫)
          ⟪ bind `ℕ ∷ [] , id `ℕ ⟫) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫
T₈-3 = ((($ 7) ⟪ bind (` 0) ∷ [] , id `ℕ ⟫)
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
    then ξ-⟪⟫ (ξ-⟪⟫ (Drop$ base-ℕ))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── the birth story ────────────────────────────────────────────────────
-- An id-layer is minted by an ordinary TyBeta whose body type is an OUTER
-- variable: `unsealAt 0 (` 1)` is the identity face, and the owner it binds
-- is never read.
_ : unsealAt 0 (` 1) ≡ id (` 1)
_ = refl

⊢W₆₀Λ : (abst ∷ S₆₁) ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀Λ = env bw[] ⊢$ (conv-seal (es ez))
            (wf-var (bind `ℕ , es ez , vis-b))

Pkg : Term
Pkg = (Λ W₆₀) ⟪ [] , `∀ (id (` 1)) ⟫

⊢Pkg : S₆₁ ∣ [] ⊢ Pkg ⦂ `∀ (` 1)
⊢Pkg = env bw[] (⊢Λ ⊢W₆₀Λ)
           (conv-all (conv-idv {p = ↑ˢ} (bind `ℕ , es ez , vis-b)))
           (wf-∀ (wf-var (bind `ℕ , es ez , vis-b)))

T₉ : Term
T₉ = (Pkg ·[ ` 1 , `ℕ ]) ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

⊢T₉ : Δ₆ ∣ [] ⊢ T₉ ⦂ `ℕ
⊢T₉ = env (bw-b wf-ℕ bw[]) (⊢·[] ⊢Pkg wf-ℕ) (conv-unseal ez) wf-ℕ

-- TyPeelR copies the ∀-face's body verbatim, so the id-layer is minted no
-- matter what TyBeta does.  Note the SHIFTED annotation (repair 2): the
-- contractum reads `B` one owner further out, `` ` 2 `` rather than `` ` 1 ``.
Pk-1 : Term
Pk-1 = ((Λ (($ 7) ⟪ [] , seal 2 ⟫)) ·[ ` 2 , ` 0 ])
         ⟪ bind `ℕ ∷ [] , id (` 1) ⟫

typeel-T₉ : Δ₆ ⊢ T₉ -→ Pk-1 ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
typeel-T₉ = ξ-⟪⟫ (TyPeelR (V-Λ (V-⟪⟫ V-$ I-seal)))

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

_ : intC Θᵣ₁ (intC Θᵣ₂ []) ≡ Sᵣ
_ = refl

⊢Vᵣ : Sᵣ ∣ [] ⊢ Vᵣ ⦂ ` 1
⊢Vᵣ = env bw[] ⊢$ (conv-seal (es ez)) (wf-var (bind `ℕ , es ez , vis-b))

⊢Tᵣ : [] ∣ [] ⊢ Tᵣ ⦂ `ℕ
⊢Tᵣ = env (bw-b wf-ℕ bw[])
          (env (bw-b (wf-var (bind `ℕ , ez , vis-b)) bw[]) ⊢Vᵣ
               (conv-idv {p = ↑ˢ} (bind `ℕ , es ez , vis-b))
               (wf-var (bind `ℕ , ez , vis-b)))
          (conv-unseal ez) wf-ℕ

push-Tᵣ : [] ⊢ Tᵣ -→ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫
push-Tᵣ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢push-Tᵣ : [] ∣ [] ⊢ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tᵣ = env {p = ↑ˢ} (bw-b wf-ℕ bw[])
               (env (bw-b (wf-var (bind `ℕ , ez , vis-b)) bw[]) ⊢Vᵣ
                    (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tᵣ : [] ⊢ Tᵣ -→* $ 7
run-Tᵣ = push-Tᵣ
    then ξ-⟪⟫ (CancelR V-$ (es ez))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── Tₘ (IdLayerProbe §4b): Θ₂ re-exposes a masked slot (`unlock 0`) and the
-- id-layer masks it again (`lock 0`).  The merged context morphism computed both
-- type contexts correctly and yet `Bwf` refused it, because `Bwf` checks every
-- entry against the PLAIN exterior.  Again: IdPush merges nothing.

Δₘ Mₘ : Ctxᵗ
Δₘ = blk (bind `𝔹) ∷ bind `ℕ ∷ []
Mₘ = bind `𝔹 ∷ bind `ℕ ∷ []

Θₘ₁ Θₘ₂ : CtxMorph
Θₘ₁ = lock 0 ∷ []
Θₘ₂ = unlock 0 ∷ []

Vₘ Tₘ : Term
Vₘ = ($ 7) ⟪ [] , seal 1 ⟫
Tₘ = (Vₘ ⟪ Θₘ₁ , id (` 1) ⟫) ⟪ Θₘ₂ , unseal 1 ⟫

_ : intC Θₘ₂ Δₘ ≡ Mₘ
_ = refl

⊢Vₘ : Δₘ ∣ [] ⊢ Vₘ ⦂ ` 1
⊢Vₘ = env bw[] ⊢$ (conv-seal (es ez)) (wf-var (bind `ℕ , es ez , vis-b))

⊢Tₘ : Δₘ ∣ [] ⊢ Tₘ ⦂ `ℕ
⊢Tₘ = env (bw-u ez bw[])
          (env (bw-l (bind `𝔹 , ez , vis-b) bw[]) ⊢Vₘ
               (conv-idv {p = ↑ˢ} (bind `ℕ , es ez , vis-b))
               (wf-var (bind `ℕ , es ez , vis-b)))
          (conv-unseal (es ez)) wf-ℕ

push-Tₘ : Δₘ ⊢ Tₘ -→ (Vₘ ⟪ Θₘ₁ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫
push-Tₘ = IdPush (V-⟪⟫ V-$ I-seal) (es ez)

⊢push-Tₘ : Δₘ ∣ [] ⊢ (Vₘ ⟪ Θₘ₁ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tₘ = env {p = ↑ˢ} (bw-u ez bw[])
               (env (bw-l (bind `𝔹 , ez , vis-b) bw[]) ⊢Vₘ
                    (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tₘ : Δₘ ⊢ Tₘ -→* $ 7
run-Tₘ = push-Tₘ
    then ξ-⟪⟫ (CancelR V-$ (es ez))
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
-- `bind `ℕ` survives as `blk (bind `ℕ)`), nothing is dropped.
_ : intC Θ2 Δd ≡ bind (` 0) ∷ bind (` 0) ∷ abst ∷ blk (bind `ℕ) ∷ []
_ = refl

-- the FACE type context keeps every slot live, so a conceal's licence resolves.
_ : fceC Θ2 Δd ≡ bind (` 0) ∷ bind (` 0) ∷ abst ∷ bind `ℕ ∷ []
_ = refl

cΘ2 : Conv                      -- (X⇒X)⇒ℕ  ⇝  (W⇒W)⇒ℕ
cΘ2 = (unseal 0 ↦ seal 0) ↦ id `ℕ

Vd Wd : Term
Vd = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
Wd = (ƛ (` 1) ∙ (` 0)) ⟪ lock 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

⊢cΘ2 : fceC Θ2 Δd ⊢ cΘ2 ∶ ((` 0 ⇒ ` 0) ⇒ `ℕ) ⇝ ((` 1 ⇒ ` 1) ⇒ `ℕ) ∙ ↑ˢ
⊢cΘ2 = conv-fun (conv-fun (conv-unseal ez) (conv-seal ez)) (conv-id base-ℕ)

⊢Fnd : Δd ∣ [] ⊢ Vd ⟪ Θ2 , cΘ2 ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fnd = env (bw-b (wf-var (_ , ez , vis-b))
                 (bw-l (_ , es (es ez) , vis-b) bw[]))
           (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-b))
                     (wf-var (_ , ez , vis-b))) ⊢$)
           ⊢cΘ2
           (wf-⇒ (wf-⇒ (wf-var (_ , ez , vis-b))
                       (wf-var (_ , ez , vis-b))) wf-ℕ)

-- THE CROSSING VALUE.  Its bind boundary masks W and seals at it: the licence
-- `seal 0` cites the owner at slot 0 of Δd, whose rep is X = ` 1.
_ : intC (lock 0 ∷ []) Δd ≡ blk (bind (` 0)) ∷ abst ∷ bind `ℕ ∷ []
_ = refl

⊢Wd : Δd ∣ [] ⊢ Wd ⦂ (` 0 ⇒ ` 0)
⊢Wd = env (bw-l (_ , ez , vis-b) bw[])
          (⊢ƛ (wf-var (_ , es ez , vis-a)) (⊢` here))
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (_ , ez , vis-b))
                (wf-var (_ , ez , vis-b)))

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
_ : intC (dual Θ2) (intC Θ2 Δd) ≡ blk (bind (` 0)) ∷ Δd
_ = refl

-- and the dual's FACE type context is IDENTICAL to the crossed boundary's, so `s`
-- transplants verbatim (no swapᵇ, no re-derivation).
_ : fceC (dual Θ2) (intC Θ2 Δd) ≡ fceC Θ2 Δd
_ = refl

-- THE CONTRACTUM IS TYPED.  (The previous design has `¬⊢contractum` here.)
⊢contractumd :
  Δd ∣ [] ⊢ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
              ⟪ Θ2 , id `ℕ ⟫ ⦂ `ℕ
⊢contractumd =
  env {p = ↑ˢ}
      (bw-b (wf-var (_ , ez , vis-b))
            (bw-l (_ , es (es ez) , vis-b) bw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-b))
                    (wf-var (_ , ez , vis-b))) ⊢$)
          ⊢Wd-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  -- the crossing argument, re-typed INSIDE, by ⊢rename at the weakening.
  ⊢Wd-in : (blk (bind (` 0)) ∷ Δd) ∣ [] ⊢ wkᴹ 1 Wd ⦂ (` 1 ⇒ ` 1)
  ⊢Wd-in = ⊢rename Ren-suc suc-inj ⊢Wd
  ⊢Wd-crossed : intC Θ2 Δd ∣ []
                  ⊢ wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫
                  ⦂ (` 0 ⇒ ` 0)
  ⊢Wd-crossed =
    env (bw-l (_ , ez , vis-b)
              (bw-u (es (es (es ez))) bw[]))
        ⊢Wd-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , vis-b))
              (wf-var (_ , ez , vis-b)))

-- ── n1b (the break, minimized) ─────────────────────────────────────────
-- The chain X:=Y over a Λ-bound Y, with the ambient's third slot and the
-- rep-carrying conceal both removed.

Δ1b : Ctxᵗ
Δ1b = bind (` 0) ∷ abst ∷ []

Θ1b : CtxMorph
Θ1b = bind (` 0) ∷ lock 1 ∷ []

_ : intC Θ1b Δ1b ≡ bind (` 0) ∷ bind (` 0) ∷ blk abst ∷ []
_ = refl

V1b W1b : Term
V1b = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
W1b = (ƛ (` 1) ∙ (` 0)) ⟪ lock 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

cΘ1b : Conv
cΘ1b = (unseal 0 ↦ seal 0) ↦ id `ℕ

⊢W1b : Δ1b ∣ [] ⊢ W1b ⦂ (` 0 ⇒ ` 0)
⊢W1b = env (bw-l (_ , ez , vis-b) bw[])
           (⊢ƛ (wf-var (_ , es ez , vis-a)) (⊢` here))
           (conv-fun (conv-unseal ez) (conv-seal ez))
           (wf-⇒ (wf-var (_ , ez , vis-b))
                 (wf-var (_ , ez , vis-b)))

⊢Fn1b : Δ1b ∣ [] ⊢ V1b ⟪ Θ1b , cΘ1b ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fn1b = env (bw-b (wf-var (_ , ez , vis-b))
                  (bw-l (_ , es ez , vis-a) bw[]))
            (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-b))
                      (wf-var (_ , ez , vis-b))) ⊢$)
            (conv-fun (conv-fun (conv-unseal ez) (conv-seal ez))
                      (conv-id base-ℕ))
            (wf-⇒ (wf-⇒ (wf-var (_ , ez , vis-b))
                        (wf-var (_ , ez , vis-b))) wf-ℕ)

⊢Redex1b : Δ1b ∣ [] ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b ⦂ `ℕ
⊢Redex1b = ⊢· ⊢Fn1b ⊢W1b

_ : dual Θ1b ≡ lock 0 ∷ unlock 2 ∷ []
_ = refl

-- the repointing again: nothing dropped, nothing demoted …
_ : intC (dual Θ1b) (intC Θ1b Δ1b) ≡ blk (bind (` 0)) ∷ Δ1b
_ = refl

-- … and the crossing value's licence, re-based one slot out, is STILL A
-- LIVE OWNER.
_ : (blk (bind (` 0)) ∷ Δ1b) ∋ 1 := ` 2
_ = es ez

peel-1b : Δ1b ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b
            -→ (V1b · (wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫))
                 ⟪ Θ1b , id `ℕ ⟫
peel-1b = Peel V-ƛ (V-⟪⟫ V-ƛ I-fun)

⊢contractum1b :
  Δ1b ∣ [] ⊢ (V1b · (wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫))
               ⟪ Θ1b , id `ℕ ⟫ ⦂ `ℕ
⊢contractum1b =
  env {p = ↑ˢ}
      (bw-b (wf-var (_ , ez , vis-b)) (bw-l (_ , es ez , vis-a) bw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-b))
                    (wf-var (_ , ez , vis-b))) ⊢$)
          ⊢W1b-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  ⊢W1b-in : (blk (bind (` 0)) ∷ Δ1b) ∣ [] ⊢ wkᴹ 1 W1b ⦂ (` 1 ⇒ ` 1)
  ⊢W1b-in = ⊢rename Ren-suc suc-inj ⊢W1b
  ⊢W1b-crossed : intC Θ1b Δ1b ∣ []
                   ⊢ wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫
                   ⦂ (` 0 ⇒ ` 0)
  ⊢W1b-crossed =
    env (bw-l (_ , ez , vis-b) (bw-u (es (es ez)) bw[]))
        ⊢W1b-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , vis-b)) (wf-var (_ , ez , vis-b)))

-- ── n4 (the x-alias break) ─────────────────────────────────────────────
-- There is no x-entry and no rep-less reveal to alias: a conceal cites an
-- owner, full stop.  The n4 configuration becomes an ordinary owner + alias.

Δ4 : Ctxᵗ
Δ4 = blk (bind `ℕ) ∷ []          -- a slot masked by an enclosing boundary

Θ4 : CtxMorph                        -- re-expose it
Θ4 = unlock 0 ∷ []

_ : intC Θ4 Δ4 ≡ bind `ℕ ∷ []
_ = refl

-- the alias RESTORES NAMEABILITY, and with it the owner's knowledge — the
-- fact `demote-x-always` denied.  It invents nothing: the rep `ℕ` was
-- already sitting in the masked entry.
_ : intC Θ4 Δ4 ∋ 0 := `ℕ
_ = ez

-- ── E★′ (the shape-IV survivor) ────────────────────────────────────────

Γ★ : Ctxᵗ
Γ★ = abst ∷ bind `ℕ ∷ []

Θ★ : CtxMorph
Θ★ = bind (` 0) ∷ lock 1 ∷ []

_ : intC Θ★ Γ★ ≡ bind (` 0) ∷ abst ∷ blk (bind `ℕ) ∷ []
_ = refl

_ : dual Θ★ ≡ lock 0 ∷ unlock 2 ∷ []
_ = refl

_ : intC (dual Θ★) (intC Θ★ Γ★) ≡ blk (bind (` 0)) ∷ Γ★
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
⊢polyid = ⊢Λ (⊢ƛ (wf-var (abst , ez , vis-a)) (⊢` here))

P₀ : Term
P₀ = (polyid ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

⊢P₀ : [] ∣ [] ⊢ P₀ ⦂ `ℕ
⊢P₀ = ⊢· (⊢·[] ⊢polyid wf-ℕ) ⊢$

-- ── STEP 1 — TYBETA.  The ∀-elimination mints THE OWNER of the event and
-- derives its face from the body type: `unsealAt 0 (X⇒X)` is the ↦-pair
-- that seals on the domain and unseals on the codomain.

_ : unsealAt 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

P₁ : Term
P₁ = ((ƛ (` 0) ∙ (` 0)) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫) · ($ 7)

step₁ : [] ⊢ P₀ -→ P₁
step₁ = ξ-·-l (TyBeta V-ƛ)

⊢fn₁ : [] ∣ [] ⊢ (ƛ (` 0) ∙ (` 0)) ⟪ bind `ℕ ∷ [] , seal 0 ↦ unseal 0 ⟫
         ⦂ (`ℕ ⇒ `ℕ)
⊢fn₁ = env {p = ↑ˢ} (bw-b wf-ℕ bw[])
           (⊢ƛ (wf-var (bind `ℕ , ez , vis-b)) (⊢` here))
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

_ : fceC (dual (bind `ℕ ∷ [])) (intC (bind `ℕ ∷ []) [])
      ≡ fceC (bind `ℕ ∷ []) []
_ = refl

P₂ : Term
P₂ = ((ƛ (` 0) ∙ (` 0)) · (($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫))
       ⟪ bind `ℕ ∷ [] , unseal 0 ⟫

step₂ : [] ⊢ P₁ -→ P₂
step₂ = Peel V-ƛ V-$

-- the crossing argument, typed INSIDE: 7 is sealed at the new owner, so the
-- interior sees it at the abstract name X.
⊢arg₂ : (bind `ℕ ∷ []) ∣ [] ⊢ ($ 7) ⟪ lock 0 ∷ [] , seal 0 ⟫ ⦂ ` 0
⊢arg₂ = env {p = ↓ˢ} (bw-l (bind `ℕ , ez , vis-b) bw[]) ⊢$
            (conv-seal ez) (wf-var (bind `ℕ , ez , vis-b))

⊢P₂ : [] ∣ [] ⊢ P₂ ⦂ `ℕ
⊢P₂ = env {p = ↑ˢ} (bw-b wf-ℕ bw[])
          (⊢· (⊢ƛ (wf-var (bind `ℕ , ez , vis-b)) (⊢` here)) ⊢arg₂)
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
           (⊢· (⊢ƛ (wf-var (bind `ℕ , ez , vis-b)) (⊢` here)) ⊢arg₂)

⊢P₃ : [] ∣ [] ⊢ P₃ ⦂ `ℕ
⊢P₃ = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢P₃-in (conv-unseal ez) wf-ℕ

-- ── STEP 4 — CANCEL.  The seal minted by Peel and the unseal minted by
-- TyBeta are now adjacent and cite THE SAME ENTRY, so the face match is
-- definitional; the residue is the identity at the LOOKED-UP rep.

P₄ : Term
P₄ = ($ 7) ⟪ bind `ℕ ∷ [] , id `ℕ ⟫

step₄ : [] ⊢ P₃ -→ P₄
step₄ = CancelR V-$ ez

⊢P₄ : [] ∣ [] ⊢ P₄ ⦂ `ℕ
⊢P₄ = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

-- ── STEP 5 — DROP$, and the whole run.

step₅ : [] ⊢ P₄ -→ $ 7
step₅ = Drop$ base-ℕ

run-P₀ : [] ⊢ P₀ -→* $ 7
run-P₀ = step₁ then step₂ then step₃ then step₄ then step₅ then done

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
⊢Wₛ = env {p = ↓ˢ} bw[] ⊢$ (conv-seal ez) (wf-var (bind `ℕ , ez , vis-b))

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

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

-- T₆ = ((7 ⟪ [] , seal 1 ⟫) ⟪ own ℕ , id (` 1) ⟫) ⟪ own ℕ , unseal 0 ⟫
-- typed at ℕ, not a value, and — before IdPush — no rule fired: Cancel
-- wanted a seal-topped interior, Drop$ a base face, ξ-⟪⟫ a stepping
-- interior.  The middle wrapper is the "transparent layer".

Δ₆ S₆₁ S₆₂ : Ctxᵗ
Δ₆  = own `ℕ ∷ []
S₆₁ = own `ℕ ∷ Δ₆
S₆₂ = own `ℕ ∷ S₆₁

W₆₀ W₆₁ T₆ : Term
W₆₀ = ($ 7) ⟪ [] , seal 1 ⟫
W₆₁ = W₆₀ ⟪ own `ℕ ∷ [] , id (` 1) ⟫
T₆  = W₆₁ ⟪ own `ℕ ∷ [] , unseal 0 ⟫

⊢W₆₀ : S₆₂ ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀ = env bw[] ⊢$ (conv-seal (es ez))
           (wf-var (own `ℕ , es ez , vis-o))

⊢W₆₁ : S₆₁ ∣ [] ⊢ W₆₁ ⦂ ` 0
⊢W₆₁ = env (bw-o wf-ℕ bw[]) ⊢W₆₀
           (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
           (wf-var (own `ℕ , ez , vis-o))

⊢T₆ : Δ₆ ∣ [] ⊢ T₆ ⦂ `ℕ
⊢T₆ = env (bw-o wf-ℕ bw[]) ⊢W₆₁ (conv-unseal ez) wf-ℕ

¬val-T₆ : ¬ Value T₆
¬val-T₆ (V-⟪⟫ _ ())

-- STEP 1 — IDPUSH.  The two FACES are swapped; both frames are untouched.
-- The pushed name `1` is the id-face's own variable (proof/IdLayer.agda,
-- `idpush-name`), and the residue face is the identity at the LOOKED-UP
-- rep — the lookup premise, exactly as ruled.
T₆-1 : Term
T₆-1 = (W₆₀ ⟪ own `ℕ ∷ [] , unseal 1 ⟫) ⟪ own `ℕ ∷ [] , id `ℕ ⟫

push-T₆ : Δ₆ ⊢ T₆ -→ T₆-1
push-T₆ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢T₆-1-in : S₆₁ ∣ [] ⊢ W₆₀ ⟪ own `ℕ ∷ [] , unseal 1 ⟫ ⦂ `ℕ
⊢T₆-1-in = env (bw-o wf-ℕ bw[]) ⊢W₆₀ (conv-unseal (es ez)) wf-ℕ

⊢T₆-1 : Δ₆ ∣ [] ⊢ T₆-1 ⦂ `ℕ
⊢T₆-1 = env {p = ↑ˢ} (bw-o wf-ℕ bw[]) ⊢T₆-1-in (conv-id base-ℕ) wf-ℕ

-- STEP 2 — the seal/unseal pair is now ADJACENT: the ordinary cancel fires.
T₆-2 : Term
T₆-2 = (($ 7) ⟪ own `ℕ ∷ [] , id `ℕ ⟫) ⟪ own `ℕ ∷ [] , id `ℕ ⟫

cancel-T₆ : Δ₆ ⊢ T₆-1 -→ T₆-2
cancel-T₆ = ξ-⟪⟫ (CancelR V-$ (es ez))

⊢T₆-2-in : S₆₁ ∣ [] ⊢ ($ 7) ⟪ own `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢T₆-2-in = env {p = ↑ˢ} (bw-o wf-ℕ bw[]) ⊢$ (conv-id base-ℕ) wf-ℕ

⊢T₆-2 : Δ₆ ∣ [] ⊢ T₆-2 ⦂ `ℕ
⊢T₆-2 = env {p = ↑ˢ} (bw-o wf-ℕ bw[]) ⊢T₆-2-in (conv-id base-ℕ) wf-ℕ

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

Θ↑ Θ↓ : BCtx
Θ↑ = own `ℕ ∷ []
Θ↓ = cnc 0 ∷ []

cancelTm : Term
cancelTm = (($ 7) ⟪ Θ↓ , seal 0 ⟫) ⟪ Θ↑ , unseal 0 ⟫

⊢cancelTm : [] ∣ [] ⊢ cancelTm ⦂ `ℕ
⊢cancelTm =
  env (bw-o wf-ℕ bw[])
      (env (bw-c (_ , ez , vis-o) bw[]) ⊢$
           (conv-seal ez) (wf-var (_ , ez , vis-o)))
      (conv-unseal ez)
      wf-ℕ

-- the pair is NOT a value (the outer face is active) and the cancel fires.
-- The residue binds Θ↑'s owner and nothing else: the mini-core's extra
-- `maskOwns` masked an exterior slot that does not exist (repair 3a,
-- proof/MaskFacts.agda `¬Bwf-cancel-residue`).
cancel-step : [] ⊢ cancelTm -→ ($ 7) ⟪ own `ℕ ∷ [] , id `ℕ ⟫
cancel-step = CancelR V-$ ez

drop-step : [] ⊢ ($ 7) ⟪ own `ℕ ∷ [] , id `ℕ ⟫ -→ $ 7
drop-step = Drop$ base-ℕ

run-cancelTm : [] ⊢ cancelTm -→* $ 7
run-cancelTm = cancel-step then drop-step then done

_ : idc `ℕ ≡ id `ℕ
_ = refl

------------------------------------------------------------------------
-- §3  T₈ — stacked id-layers, and where they come from
------------------------------------------------------------------------

LA LB T₈ : Term
LA = (($ 7) ⟪ [] , seal 2 ⟫) ⟪ own (` 0) ∷ [] , id (` 2) ⟫
LB = LA ⟪ own `ℕ ∷ [] , id (` 1) ⟫
T₈ = LB ⟪ own `ℕ ∷ [] , unseal 0 ⟫

SA : Ctxᵗ
SA = own (` 0) ∷ S₆₂            -- the interior spine of LA

⊢LA-in : SA ∣ [] ⊢ ($ 7) ⟪ [] , seal 2 ⟫ ⦂ ` 2
⊢LA-in = env bw[] ⊢$ (conv-seal (es (es ez)))
             (wf-var (own `ℕ , es (es ez) , vis-o))

⊢LA : S₆₂ ∣ [] ⊢ LA ⦂ ` 1
⊢LA = env (bw-o (wf-var (own `ℕ , ez , vis-o)) bw[]) ⊢LA-in
          (conv-idv {p = ↑ˢ} (own `ℕ , es (es ez) , vis-o))
          (wf-var (own `ℕ , es ez , vis-o))

⊢LB : S₆₁ ∣ [] ⊢ LB ⦂ ` 0
⊢LB = env (bw-o wf-ℕ bw[]) ⊢LA
          (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
          (wf-var (own `ℕ , ez , vis-o))

⊢T₈ : Δ₆ ∣ [] ⊢ T₈ ⦂ `ℕ
⊢T₈ = env (bw-o wf-ℕ bw[]) ⊢LB (conv-unseal ez) wf-ℕ

-- The stack resolves ONE LAYER PER STEP, outermost first: each IdPush moves
-- the active face one layer inward toward the seal, so any depth
-- terminates.  (IdAbsorb needed `⊳` to merge the frames and could not do
-- this one — the inner layer's skeleton `own (` 0)` names the next layer's
-- owner, IdLayerProbe §4c.  IdPush touches no frame.)
T₈-1 T₈-2 T₈-3 : Term
T₈-1 = (LA ⟪ own `ℕ ∷ [] , unseal 1 ⟫) ⟪ own `ℕ ∷ [] , id `ℕ ⟫
T₈-2 = (((($ 7) ⟪ [] , seal 2 ⟫) ⟪ own (` 0) ∷ [] , unseal 2 ⟫)
          ⟪ own `ℕ ∷ [] , id `ℕ ⟫) ⟪ own `ℕ ∷ [] , id `ℕ ⟫
T₈-3 = ((($ 7) ⟪ own (` 0) ∷ [] , id `ℕ ⟫)
          ⟪ own `ℕ ∷ [] , id `ℕ ⟫) ⟪ own `ℕ ∷ [] , id `ℕ ⟫

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
            (wf-var (own `ℕ , es ez , vis-o))

Pkg : Term
Pkg = (Λ W₆₀) ⟪ [] , `∀ (id (` 1)) ⟫

⊢Pkg : S₆₁ ∣ [] ⊢ Pkg ⦂ `∀ (` 1)
⊢Pkg = env bw[] (⊢Λ ⊢W₆₀Λ)
           (conv-all (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o)))
           (wf-∀ (wf-var (own `ℕ , es ez , vis-o)))

T₉ : Term
T₉ = (Pkg ·[ ` 1 , `ℕ ]) ⟪ own `ℕ ∷ [] , unseal 0 ⟫

⊢T₉ : Δ₆ ∣ [] ⊢ T₉ ⦂ `ℕ
⊢T₉ = env (bw-o wf-ℕ bw[]) (⊢·[] ⊢Pkg wf-ℕ) (conv-unseal ez) wf-ℕ

-- TyPeelR copies the ∀-face's body verbatim, so the id-layer is minted no
-- matter what TyBeta does.  Note the SHIFTED annotation (repair 2): the
-- contractum reads `B` one owner further out, `` ` 2 `` rather than `` ` 1 ``.
Pk-1 : Term
Pk-1 = ((Λ (($ 7) ⟪ [] , seal 2 ⟫)) ·[ ` 2 , ` 0 ])
         ⟪ own `ℕ ∷ [] , id (` 1) ⟫

typeel-T₉ : Δ₆ ⊢ T₉ -→ Pk-1 ⟪ own `ℕ ∷ [] , unseal 0 ⟫
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
                -→ ($ 1) ⟪ own `ℕ ∷ [] , id `ℕ ⟫
then-tybeta = TyBeta V-$

run-Ωt : [] ⊢ Ωt ·[ `ℕ , `ℕ ] -→* $ 1
run-Ωt = body-first then then-tybeta then Drop$ base-ℕ then done

------------------------------------------------------------------------
-- §4  The two adversaries `⊳` could not clear
------------------------------------------------------------------------

-- ── Tᵣ (IdLayerProbe §4c): the id-layer's skeleton carries a rep that
-- NAMES the outer boundary's owner.  Merging the frames would have to
-- SUBSTITUTE reps into reps — rep arithmetic, i.e. the retired `⊕`.
-- IdPush touches no frame, so the instance is ordinary.

Θᵣ₁ Θᵣ₂ : BCtx
Θᵣ₁ = own (` 0) ∷ []
Θᵣ₂ = own `ℕ ∷ []

Sᵣ : Ctxᵗ
Sᵣ = own (` 0) ∷ own `ℕ ∷ []

Vᵣ Tᵣ : Term
Vᵣ = ($ 7) ⟪ [] , seal 1 ⟫
Tᵣ = (Vᵣ ⟪ Θᵣ₁ , id (` 1) ⟫) ⟪ Θᵣ₂ , unseal 0 ⟫

_ : intC Θᵣ₁ (intC Θᵣ₂ []) ≡ Sᵣ
_ = refl

⊢Vᵣ : Sᵣ ∣ [] ⊢ Vᵣ ⦂ ` 1
⊢Vᵣ = env bw[] ⊢$ (conv-seal (es ez)) (wf-var (own `ℕ , es ez , vis-o))

⊢Tᵣ : [] ∣ [] ⊢ Tᵣ ⦂ `ℕ
⊢Tᵣ = env (bw-o wf-ℕ bw[])
          (env (bw-o (wf-var (own `ℕ , ez , vis-o)) bw[]) ⊢Vᵣ
               (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
               (wf-var (own `ℕ , ez , vis-o)))
          (conv-unseal ez) wf-ℕ

push-Tᵣ : [] ⊢ Tᵣ -→ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫
push-Tᵣ = IdPush (V-⟪⟫ V-$ I-seal) ez

⊢push-Tᵣ : [] ∣ [] ⊢ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tᵣ = env {p = ↑ˢ} (bw-o wf-ℕ bw[])
               (env (bw-o (wf-var (own `ℕ , ez , vis-o)) bw[]) ⊢Vᵣ
                    (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tᵣ : [] ⊢ Tᵣ -→* $ 7
run-Tᵣ = push-Tᵣ
    then ξ-⟪⟫ (CancelR V-$ (es ez))
    then ξ-⟪⟫ (Drop$ base-ℕ)
    then Drop$ base-ℕ
    then done

-- ── Tₘ (IdLayerProbe §4b): Θ₂ re-exposes a masked slot (`ali 0`) and the
-- id-layer masks it again (`cnc 0`).  The merged skeleton computed both
-- spines correctly and yet `Bwf` refused it, because `Bwf` checks every
-- entry against the PLAIN exterior.  Again: IdPush merges nothing.

Δₘ Mₘ : Ctxᵗ
Δₘ = blk (own `𝔹) ∷ own `ℕ ∷ []
Mₘ = own `𝔹 ∷ own `ℕ ∷ []

Θₘ₁ Θₘ₂ : BCtx
Θₘ₁ = cnc 0 ∷ []
Θₘ₂ = ali 0 ∷ []

Vₘ Tₘ : Term
Vₘ = ($ 7) ⟪ [] , seal 1 ⟫
Tₘ = (Vₘ ⟪ Θₘ₁ , id (` 1) ⟫) ⟪ Θₘ₂ , unseal 1 ⟫

_ : intC Θₘ₂ Δₘ ≡ Mₘ
_ = refl

⊢Vₘ : Δₘ ∣ [] ⊢ Vₘ ⦂ ` 1
⊢Vₘ = env bw[] ⊢$ (conv-seal (es ez)) (wf-var (own `ℕ , es ez , vis-o))

⊢Tₘ : Δₘ ∣ [] ⊢ Tₘ ⦂ `ℕ
⊢Tₘ = env (bw-a ez bw[])
          (env (bw-c (own `𝔹 , ez , vis-o) bw[]) ⊢Vₘ
               (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
               (wf-var (own `ℕ , es ez , vis-o)))
          (conv-unseal (es ez)) wf-ℕ

push-Tₘ : Δₘ ⊢ Tₘ -→ (Vₘ ⟪ Θₘ₁ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫
push-Tₘ = IdPush (V-⟪⟫ V-$ I-seal) (es ez)

⊢push-Tₘ : Δₘ ∣ [] ⊢ (Vₘ ⟪ Θₘ₁ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tₘ = env {p = ↑ˢ} (bw-a ez bw[])
               (env (bw-c (own `𝔹 , ez , vis-o) bw[]) ⊢Vₘ
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
--   The reveal's rep NAMES the chained slot W, whose own knowledge is the
--   Λ-bound X; the old dual DEMOTED W and the crossing value's licence died.

Δd : Ctxᵗ                       -- W:=X , X abstract , V:=ℕ
Δd = own (` 0) ∷ abst ∷ own `ℕ ∷ []

-- W's rep, read on Δd, is the Λ-bound X — the chained spelling that broke.
_ : Δd ∋ 0 := ` 1
_ = ez

Θ2 : BCtx                       -- own(W) , conceal V
Θ2 = own (` 0) ∷ cnc 2 ∷ []

-- ONE frame change: the owner is pushed on, V is MASKED IN PLACE (the entry
-- `own `ℕ` survives as `blk (own `ℕ)`), nothing is dropped.
_ : intC Θ2 Δd ≡ own (` 0) ∷ own (` 0) ∷ abst ∷ blk (own `ℕ) ∷ []
_ = refl

-- the FACE spine keeps every slot live, so a conceal's licence resolves.
_ : fceC Θ2 Δd ≡ own (` 0) ∷ own (` 0) ∷ abst ∷ own `ℕ ∷ []
_ = refl

cΘ2 : Conv                      -- (X⇒X)⇒ℕ  ⇝  (W⇒W)⇒ℕ
cΘ2 = (unseal 0 ↦ seal 0) ↦ id `ℕ

Vd Wd : Term
Vd = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
Wd = (ƛ (` 1) ∙ (` 0)) ⟪ cnc 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

⊢cΘ2 : fceC Θ2 Δd ⊢ cΘ2 ∶ ((` 0 ⇒ ` 0) ⇒ `ℕ) ⇝ ((` 1 ⇒ ` 1) ⇒ `ℕ) ∙ ↑ˢ
⊢cΘ2 = conv-fun (conv-fun (conv-unseal ez) (conv-seal ez)) (conv-id base-ℕ)

⊢Fnd : Δd ∣ [] ⊢ Vd ⟪ Θ2 , cΘ2 ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fnd = env (bw-o (wf-var (_ , ez , vis-o))
                 (bw-c (_ , es (es ez) , vis-o) bw[]))
           (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                     (wf-var (_ , ez , vis-o))) ⊢$)
           ⊢cΘ2
           (wf-⇒ (wf-⇒ (wf-var (_ , ez , vis-o))
                       (wf-var (_ , ez , vis-o))) wf-ℕ)

-- THE CROSSING VALUE.  Its own boundary masks W and seals at it: the licence
-- `seal 0` cites the owner at slot 0 of Δd, whose rep is X = ` 1.
_ : intC (cnc 0 ∷ []) Δd ≡ blk (own (` 0)) ∷ abst ∷ own `ℕ ∷ []
_ = refl

⊢Wd : Δd ∣ [] ⊢ Wd ⦂ (` 0 ⇒ ` 0)
⊢Wd = env (bw-c (_ , ez , vis-o) bw[])
          (⊢ƛ (wf-var (_ , es ez , vis-a)) (⊢` here))
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (_ , ez , vis-o))
                (wf-var (_ , ez , vis-o)))

Wd-value : Value Wd
Wd-value = V-⟪⟫ V-ƛ I-fun

⊢Redexd : Δd ∣ [] ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd ⦂ `ℕ
⊢Redexd = ⊢· ⊢Fnd ⊢Wd

peel-d : Δd ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd
           -→ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
                ⟪ Θ2 , id `ℕ ⟫
peel-d = Peel V-ƛ Wd-value

-- THE DUAL is two names and nothing else: mask the owner, re-expose V.
_ : dual Θ2 ≡ cnc 0 ∷ ali 3 ∷ []
_ = refl

-- THE REPOINTING.  The dual's interior is Δd with ONE masked slot in front:
-- every entry of Δd is still there, in the same order, with the same rep.
-- W's entry — the one the old design demoted to `abst` — is untouched.
_ : intC (dual Θ2) (intC Θ2 Δd) ≡ blk (own (` 0)) ∷ Δd
_ = refl

-- and the dual's FACE spine is IDENTICAL to the crossed boundary's, so `s`
-- transplants verbatim (no swapᵇ, no re-derivation).
_ : fceC (dual Θ2) (intC Θ2 Δd) ≡ fceC Θ2 Δd
_ = refl

-- THE CONTRACTUM IS TYPED.  (The previous design has `¬⊢contractum` here.)
⊢contractumd :
  Δd ∣ [] ⊢ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫))
              ⟪ Θ2 , id `ℕ ⟫ ⦂ `ℕ
⊢contractumd =
  env {p = ↑ˢ}
      (bw-o (wf-var (_ , ez , vis-o))
            (bw-c (_ , es (es ez) , vis-o) bw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                    (wf-var (_ , ez , vis-o))) ⊢$)
          ⊢Wd-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  -- the crossing argument, re-typed INSIDE, by ⊢rename at the weakening.
  ⊢Wd-in : (blk (own (` 0)) ∷ Δd) ∣ [] ⊢ wkᴹ 1 Wd ⦂ (` 1 ⇒ ` 1)
  ⊢Wd-in = ⊢rename Ren-suc suc-inj ⊢Wd
  ⊢Wd-crossed : intC Θ2 Δd ∣ []
                  ⊢ wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫
                  ⦂ (` 0 ⇒ ` 0)
  ⊢Wd-crossed =
    env (bw-c (_ , ez , vis-o)
              (bw-a (es (es (es ez))) bw[]))
        ⊢Wd-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , vis-o))
              (wf-var (_ , ez , vis-o)))

-- ── n1b (the break, minimized) ─────────────────────────────────────────
-- The chain X:=Y over a Λ-bound Y, with the ambient's third slot and the
-- rep-carrying conceal both removed.

Δ1b : Ctxᵗ
Δ1b = own (` 0) ∷ abst ∷ []

Θ1b : BCtx
Θ1b = own (` 0) ∷ cnc 1 ∷ []

_ : intC Θ1b Δ1b ≡ own (` 0) ∷ own (` 0) ∷ blk abst ∷ []
_ = refl

V1b W1b : Term
V1b = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
W1b = (ƛ (` 1) ∙ (` 0)) ⟪ cnc 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

cΘ1b : Conv
cΘ1b = (unseal 0 ↦ seal 0) ↦ id `ℕ

⊢W1b : Δ1b ∣ [] ⊢ W1b ⦂ (` 0 ⇒ ` 0)
⊢W1b = env (bw-c (_ , ez , vis-o) bw[])
           (⊢ƛ (wf-var (_ , es ez , vis-a)) (⊢` here))
           (conv-fun (conv-unseal ez) (conv-seal ez))
           (wf-⇒ (wf-var (_ , ez , vis-o))
                 (wf-var (_ , ez , vis-o)))

⊢Fn1b : Δ1b ∣ [] ⊢ V1b ⟪ Θ1b , cΘ1b ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fn1b = env (bw-o (wf-var (_ , ez , vis-o))
                  (bw-c (_ , es ez , vis-a) bw[]))
            (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                      (wf-var (_ , ez , vis-o))) ⊢$)
            (conv-fun (conv-fun (conv-unseal ez) (conv-seal ez))
                      (conv-id base-ℕ))
            (wf-⇒ (wf-⇒ (wf-var (_ , ez , vis-o))
                        (wf-var (_ , ez , vis-o))) wf-ℕ)

⊢Redex1b : Δ1b ∣ [] ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b ⦂ `ℕ
⊢Redex1b = ⊢· ⊢Fn1b ⊢W1b

_ : dual Θ1b ≡ cnc 0 ∷ ali 2 ∷ []
_ = refl

-- the repointing again: nothing dropped, nothing demoted …
_ : intC (dual Θ1b) (intC Θ1b Δ1b) ≡ blk (own (` 0)) ∷ Δ1b
_ = refl

-- … and the crossing value's licence, re-based one slot out, is STILL A
-- LIVE OWNER.
_ : (blk (own (` 0)) ∷ Δ1b) ∋ 1 := ` 2
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
      (bw-o (wf-var (_ , ez , vis-o)) (bw-c (_ , es ez , vis-a) bw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                    (wf-var (_ , ez , vis-o))) ⊢$)
          ⊢W1b-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  ⊢W1b-in : (blk (own (` 0)) ∷ Δ1b) ∣ [] ⊢ wkᴹ 1 W1b ⦂ (` 1 ⇒ ` 1)
  ⊢W1b-in = ⊢rename Ren-suc suc-inj ⊢W1b
  ⊢W1b-crossed : intC Θ1b Δ1b ∣ []
                   ⊢ wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫
                   ⦂ (` 0 ⇒ ` 0)
  ⊢W1b-crossed =
    env (bw-c (_ , ez , vis-o) (bw-a (es (es ez)) bw[]))
        ⊢W1b-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , vis-o)) (wf-var (_ , ez , vis-o)))

-- ── n4 (the x-alias break) ─────────────────────────────────────────────
-- There is no x-entry and no rep-less reveal to alias: a conceal cites an
-- owner, full stop.  The n4 configuration becomes an ordinary owner + alias.

Δ4 : Ctxᵗ
Δ4 = blk (own `ℕ) ∷ []          -- a slot masked by an enclosing boundary

Θ4 : BCtx                        -- re-expose it
Θ4 = ali 0 ∷ []

_ : intC Θ4 Δ4 ≡ own `ℕ ∷ []
_ = refl

-- the alias RESTORES NAMEABILITY, and with it the owner's knowledge — the
-- fact `demote-x-always` denied.  It invents nothing: the rep `ℕ` was
-- already sitting in the masked entry.
_ : intC Θ4 Δ4 ∋ 0 := `ℕ
_ = ez

-- ── E★′ (the shape-IV survivor) ────────────────────────────────────────

Γ★ : Ctxᵗ
Γ★ = abst ∷ own `ℕ ∷ []

Θ★ : BCtx
Θ★ = own (` 0) ∷ cnc 1 ∷ []

_ : intC Θ★ Γ★ ≡ own (` 0) ∷ abst ∷ blk (own `ℕ) ∷ []
_ = refl

_ : dual Θ★ ≡ cnc 0 ∷ ali 2 ∷ []
_ = refl

_ : intC (dual Θ★) (intC Θ★ Γ★) ≡ blk (own (` 0)) ∷ Γ★
_ = refl

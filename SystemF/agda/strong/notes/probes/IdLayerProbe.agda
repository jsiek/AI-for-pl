module strong.notes.probes.IdLayerProbe where

-- THE ID-LAYER PROBE — the β2 / transparent-layer progress obligation.
--
-- ConvBoundaryProbe §6 leaves a STUCK WELL-TYPED term in the redesign
-- mini-core:
--
--   T₆ = ((7 ⟪ [] , seal 1 ⟫) ⟪ own ℕ , id (` 1) ⟫) ⟪ own ℕ , unseal 0 ⟫
--
-- typed at ℕ, not a value, and no rule fires: `Cancel` wants a seal-topped
-- interior, `Drop$` a base face over a numeral, `ξ-⟪⟫` a stepping interior.
-- The middle wrapper — an INERT `id (` X)` face over a boundary that binds
-- an owner nothing reads — is the "transparent layer".
--
-- This file is a self-contained COPY/EXTENSION of the mini-core's reduction
-- relation (`_⊢_⇛_`) in which candidate repairs are tested side by side.
-- The relation is deliberately the UNION of several candidate rule sets (so
-- it is NOT a proposed system: TyBeta′ and TyBeta-vac overlap by design);
-- every determinism claim below is therefore about a NAMED PAIR of rules.
--
--   §0  preliminaries: occurrence check, lowering, the merge `_⊳_`
--   §1  the extended relation
--   §2  the laws that gate every candidate (values, id-faces, canonical form)
--   §3  R3  IdAbsorb  (Jeremy's ruling: `Active c` is the load-bearing premise)
--   §4  R3's adversaries: the mask jam, the rep jam, the Bwf jam  (no-⊕ test)
--   §5  R1  vacuous instantiation, as the optional companion
--   §6  R2  deep Cancel — comparison note only
--   §7  (e) the naked drop `V ⟪ Θ , id A ⟫ -→ V` — the door, closed
--   §8  R5  IdPush: IdAbsorb's degenerate form, which needs no `⊳` at all
--   §9  the determinism table, and the mini-core defects found on the way
--
-- HEADLINE.  IdAbsorb with `Active c` runs T₆ to 7 and resolves stacked
-- id-layers outermost-first; its ONE cost is `⊳`, which must merge two
-- skeletons and therefore inherits two side conditions (§4).  §8 shows the
-- same LHS admits a rule with NO merge at all.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.notes.probes.ConvBoundaryCore
open import strong.notes.probes.ConvBoundaryTerms
open import strong.notes.probes.ConvBoundaryProbe

------------------------------------------------------------------------
-- §0  Preliminaries
------------------------------------------------------------------------

-- R1's decidable side condition: does the Λ-bound slot occur in the body
-- type at all?  (`unsealAt 0 B` is an IDENTITY face exactly when it is not
-- reached — see `unsealAt-id` in §5.)
data Occ : ℕ → Ty → Set where
  oc-var : ∀ {X}     → Occ X (` X)
  oc-⇒-l : ∀ {X A B} → Occ X A → Occ X (A ⇒ B)
  oc-⇒-r : ∀ {X A B} → Occ X B → Occ X (A ⇒ B)
  oc-∀   : ∀ {X A}   → Occ (suc X) A → Occ X (`∀ A)

occ? : (X : ℕ) (A : Ty) → Dec (Occ X A)
occ? X (` Y) with X ≟ℕ Y
... | yes refl = yes oc-var
... | no ne    = no λ { oc-var → ne refl }
occ? X `ℕ = no λ ()
occ? X `𝔹 = no λ ()
occ? X (A ⇒ B) with occ? X A
... | yes o = yes (oc-⇒-l o)
... | no na with occ? X B
...   | yes o = yes (oc-⇒-r o)
...   | no nb = no λ { (oc-⇒-l o) → na o ; (oc-⇒-r o) → nb o }
occ? X (`∀ A) with occ? (suc X) A
... | yes o = yes (oc-∀ o)
... | no na = no λ { (oc-∀ o) → na o }

-- R1's contractum: strengthening a term past a binder it does not use.
predᵗ : Renameᵗ
predᵗ X = X ∸ 1

lowᴹ : Term → Term
lowᴹ = renᴹ predᵗ

-- R3's merge.  Θ₁ is the id-layer's skeleton, read on `intC Θ₂ Δ`; Θ₂ is
-- the surviving wrapper's, read on `Δ`.  Flattening puts Θ₁'s owners first
-- (that is the layout `intC Θ₁ (intC Θ₂ Δ)` already has), so Θ₁'s names —
-- and Θ₁'s owner REPS — must be re-read one frame out: exactly `∸ nrev Θ₂`.
-- NAMES AND OWNERS ONLY: no conversion is composed, no rep is substituted
-- (`id` is composition's unit, so the face carries through as `renᶜ`).
dropN : ℕ → Renameᵗ
dropN n X = X ∸ n

infixl 6 _⊳_
_⊳_ : BCtx → BCtx → BCtx
Θ₁ ⊳ Θ₂ = renᴮ (dropN (nrev Θ₂)) Θ₁ ++ Θ₂

------------------------------------------------------------------------
-- §1  The extended relation
------------------------------------------------------------------------

infix 2 _⊢_⇛_
data _⊢_⇛_ : Ctxᵗ → Term → Term → Set where

  -- ── the mini-core's rules, copied ──────────────────────────────────

  TyBeta′ : ∀ {Δ B A N}
    → Δ ⊢ (Λ N) ·[ B , A ] ⇛ N ⟪ own A ∷ [] , unsealAt 0 B ⟫

  Beta′ : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W ⇛ N [ W ]ᵐ

  Peel′ : ∀ {Δ V W Θ s t} → Value V → Value W
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        ⇛ (V · (wkᴹ (nrev Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫

  -- TyPeel, WITH THE ANNOTATION REPAIR of §9(ii): the body type `B` is read
  -- over `abst ∷ Δ`, and the contractum reads it over `abst ∷ own A ∷ Δ`.
  TyPeelR : ∀ {Δ V Θ s B A} → Value V
    → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        ⇛ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) B , ` 0 ]) ⟪ own A ∷ renᴮ suc Θ , s ⟫

  -- Cancel, WITH THE RESIDUE REPAIR of §9(i): `maskOwns (nrev Θ₂)` masks
  -- EXTERIOR slots that need not exist (`¬Bwf-cancelTm-residue`).
  CancelR : ∀ {Δ V Θ₁ Θ₂ X B} → Value V
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal X ⟫
        ⇛ V ⟪ reps→own (reps Θ₂) , idc B ⟫

  Drop$′ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ ⇛ $ n

  ξ-·-l′ : ∀ {Δ L L′ M} → Δ ⊢ L ⇛ L′ → Δ ⊢ L · M ⇛ L′ · M
  ξ-·-r′ : ∀ {Δ V M M′} → Value V → Δ ⊢ M ⇛ M′ → Δ ⊢ V · M ⇛ V · M′
  ξ-·[]′ : ∀ {Δ L L′ B A} → Δ ⊢ L ⇛ L′ → Δ ⊢ L ·[ B , A ] ⇛ L′ ·[ B , A ]
  ξ-Λ′   : ∀ {Δ N N′} → (abst ∷ Δ) ⊢ N ⇛ N′ → Δ ⊢ Λ N ⇛ Λ N′
  ξ-⟪⟫′  : ∀ {Δ M M′ Θ c} → intC Θ Δ ⊢ M ⇛ M′
         → Δ ⊢ M ⟪ Θ , c ⟫ ⇛ M′ ⟪ Θ , c ⟫

  -- ── R1  VACUOUS INSTANTIATION (§5) ─────────────────────────────────
  TyBeta-vac : ∀ {Δ B A N} → ¬ Occ 0 B
    → Δ ⊢ (Λ N) ·[ B , A ] ⇛ lowᴹ N

  -- ── R3  ID-LAYER ABSORPTION (§3) ───────────────────────────────────
  -- `Active c` is load-bearing TWICE: without it the LHS is a VALUE
  -- (`V-⟪⟫ (V-⟪⟫ V ic) c`), and stacked id-layers would have TWO redexes.
  -- The inner face is `id (` X)` and NOT `id A`: at a base face the inner
  -- wrapper is itself active and steps (`Drop$`), which would overlap.
  IdAbsorb : ∀ {Δ V Θ₁ Θ₂ X c} → Value V → Active c
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , c ⟫
        ⇛ V ⟪ Θ₁ ⊳ Θ₂ , renᶜ (wkN (nrev Θ₁)) c ⟫

  -- ── R5  ID-PUSH (§8): the same LHS, no skeleton merge at all ───────
  IdPush : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        ⇛ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫

  -- ── R2  DEEP CANCEL (§6): comparison only ──────────────────────────
  -- the inner seal and the id-face share their NAME (both are read on the
  -- id-layer's face spine when Θ₀ binds no owner); the outer `unseal Y` is
  -- one frame out, so typing forces X ≡ nrev Θ₁ + Y.
  CancelDeep : ∀ {Δ V Θ₀ Θ₁ Θ₂ X Y B} → Value V
    → Δ ⊢ ((V ⟪ Θ₀ , seal X ⟫) ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        ⇛ V ⟪ Θ₀ ⊳ (Θ₁ ⊳ Θ₂) , idc B ⟫

infix  2 _⊢_⇛*_
data _⊢_⇛*_ : Ctxᵗ → Term → Term → Set where
  done : ∀ {Δ M} → Δ ⊢ M ⇛* M
  _then_ : ∀ {Δ L M N} → Δ ⊢ L ⇛ M → Δ ⊢ M ⇛* N → Δ ⊢ L ⇛* N

infixr 2 _then_

------------------------------------------------------------------------
-- §2  The laws every candidate is gated on
------------------------------------------------------------------------

-- (i)  "VALUES DON'T STEP" — the honest form.  It is FALSE on the nose in
-- the mini-core, and was already false before this file: `Λ N` is a value
-- for EVERY N (`V-Λ`), and `ξ-Λ` steps under it.  What does hold is that
-- the only values that step are Λ-HEADED (possibly under inert wrappers).
data ΛH : Term → Set where
  λh-Λ   : ∀ {N} → ΛH (Λ N)
  λh-⟪⟫  : ∀ {M Θ c} → ΛH M → ΛH (M ⟪ Θ , c ⟫)

value-step-ΛH : ∀ {Δ M M′} → Value M → Δ ⊢ M ⇛ M′ → ΛH M
value-step-ΛH (V-⟪⟫ v I-idv) (Drop$′ ())
value-step-ΛH (V-⟪⟫ v ic) (IdAbsorb _ ac) = ⊥-elim (act-not-inert ac ic)
value-step-ΛH (V-⟪⟫ v ic) (ξ-⟪⟫′ st)      = λh-⟪⟫ (value-step-ΛH v st)
value-step-ΛH V-Λ         (ξ-Λ′ st)       = λh-Λ

-- The COROLLARY the candidates are actually judged by: no NEW rule steps a
-- value.  For IdAbsorb this is exactly the `Active c` premise.
IdAbsorb-lhs-not-value : ∀ {V Θ₁ Θ₂ X c} → Active c
  → ¬ Value ((V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , c ⟫)
IdAbsorb-lhs-not-value ac (V-⟪⟫ _ ic) = act-not-inert ac ic

-- (ii)  Face inversions used throughout.
liftN-base : ∀ {A} (n : ℕ) → Base A → liftN n A ≡ A
liftN-base zero    b = refl
liftN-base (suc n) b rewrite liftN-base n b = base-ren b

conv-idv-tgt : ∀ {Δ X A B p} → Δ ⊢ id (` X) ∶ A ⇝ B ∙ p → B ≡ ` X
conv-idv-tgt (conv-idv _) = refl

conv-idv-src : ∀ {Δ X A B p} → Δ ⊢ id (` X) ∶ A ⇝ B ∙ p → A ≡ ` X
conv-idv-src (conv-idv _) = refl

conv-id-base-src : ∀ {Δ A B C p} → Base A → Δ ⊢ id A ∶ B ⇝ C ∙ p → B ≡ A
conv-id-base-src bA (conv-id _) = refl
conv-id-base-src () (conv-idv _)

-- (iii)  THE ANSWER TO "IS THE id-BASE CASE OF `Active c` REACHABLE?": NO.
-- An `id (` X)`-faced wrapper has a VARIABLE exterior type, and an outer
-- `id A` face at a BASE type demands a base interior.  So the only active
-- face IdAbsorb ever meets is `unseal Y`.
base≢var : ∀ {A X} (n : ℕ) → Base A → liftN n A ≡ ` X → ⊥
base≢var n base-ℕ eq with trans (sym (liftN-base n base-ℕ)) eq
... | ()
base≢var n base-𝔹 eq with trans (sym (liftN-base n base-𝔹)) eq
... | ()

outer-id-base-untypeable : ∀ {Δ Γ V Θ₁ Θ₂ X A C} → Base A
  → ¬ (Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , id A ⟫ ⦂ C)
outer-id-base-untypeable {Θ₁ = Θ₁} bA (env _ (env _ _ ⊢cᵢ _) ⊢cₒ _)
  with conv-id-base-src bA ⊢cₒ
... | refl = base≢var (nrev Θ₁) bA (conv-idv-tgt ⊢cᵢ)

-- (iv)  CANONICAL FORMS AT A VARIABLE, and THE MASK JAM, in one line.
-- A value's type is checked by `env`'s last conjunct on the value's OWN
-- spine, so a value can never have a type the spine masks.  Hence the
-- configuration "the id-layer's own skeleton conceals the slot its face
-- names" is UNTYPEABLE, not merely awkward: the jam is a phantom.
value-var-visible : ∀ {Δ V X} → Value V → Δ ∣ [] ⊢ V ⦂ ` X → Δ ∋tv X
value-var-visible (V-⟪⟫ _ _) (env _ _ _ (wf-var tv)) = tv

------------------------------------------------------------------------
-- §3  R3 — IdAbsorb, verbatim, and T₆'s run
------------------------------------------------------------------------

--   IdAbsorb : Value V → Active c
--     → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , c ⟫
--         ⇛ V ⟪ Θ₁ ⊳ Θ₂ , renᶜ (wkN (nrev Θ₁)) c ⟫
--
-- The merge on T₆'s skeletons is TWO OWNERS AND NOTHING ELSE …
_ : (own `ℕ ∷ []) ⊳ (own `ℕ ∷ []) ≡ own `ℕ ∷ own `ℕ ∷ []
_ = refl

-- … and the face is the OUTER face with its NAME re-based past Θ₁'s owners.
-- No conversion is composed: `id` is the unit, so `⊕` does not reappear.
_ : renᶜ (wkN 1) (unseal 0) ≡ unseal 1
_ = refl

-- THE MERGE EQUATIONS the typing needs.  Both are DEFINITIONAL here — this
-- is what makes the contractum type with no transport at all.
_ : intC ((own `ℕ ∷ []) ⊳ (own `ℕ ∷ [])) Δ₆
      ≡ intC (own `ℕ ∷ []) (intC (own `ℕ ∷ []) Δ₆)
_ = refl

_ : fceC ((own `ℕ ∷ []) ⊳ (own `ℕ ∷ [])) Δ₆
      ≡ fceC (own `ℕ ∷ []) (intC (own `ℕ ∷ []) Δ₆)
_ = refl

T₆-1 T₆-2 : Term
T₆-1 = W₆₀ ⟪ own `ℕ ∷ own `ℕ ∷ [] , unseal 1 ⟫
T₆-2 = ($ 7) ⟪ own `ℕ ∷ own `ℕ ∷ [] , id `ℕ ⟫

-- STEP 1 — the id-layer is absorbed; its owner survives as the merged
-- skeleton's first binder, and the `unseal` is re-based 0 ↦ 1.
absorb-T₆ : Δ₆ ⊢ T₆ ⇛ T₆-1
absorb-T₆ = IdAbsorb (V-⟪⟫ V-$ I-seal) A-unseal

⊢T₆-1 : Δ₆ ∣ [] ⊢ T₆-1 ⦂ `ℕ
⊢T₆-1 = env (bw-o wf-ℕ (bw-o wf-ℕ bw[])) ⊢W₆₀ (conv-unseal (es ez)) wf-ℕ

-- STEP 2 — the seal/unseal pair is now ADJACENT: the ordinary cancel fires.
cancel-T₆ : Δ₆ ⊢ T₆-1 ⇛ T₆-2
cancel-T₆ = CancelR {B = `ℕ} V-$

⊢T₆-2 : Δ₆ ∣ [] ⊢ T₆-2 ⦂ `ℕ
⊢T₆-2 = env {p = ↑ˢ} (bw-o wf-ℕ (bw-o wf-ℕ bw[])) ⊢$ (conv-id base-ℕ) wf-ℕ

-- STEP 3 — a base face over a numeral.
run-T₆ : Δ₆ ⊢ T₆ ⇛* $ 7
run-T₆ = absorb-T₆ then cancel-T₆ then Drop$′ base-ℕ then done

------------------------------------------------------------------------
-- §3b  STACKED id-layers resolve OUTERMOST-ACTIVE-FIRST
------------------------------------------------------------------------

-- This is exactly what `Active c` buys.  The stack below is REACHABLE:
-- §5's `TyPeelR` + the mini-core's `TyBeta′` build it.  Its inner id-layer
-- has the skeleton `own (` 0)` — an owner whose rep NAMES the next layer's
-- owner, the shape §4c is about.

LA LB T₈ : Term
LA = (($ 7) ⟪ [] , seal 2 ⟫) ⟪ own (` 0) ∷ [] , id (` 2) ⟫
LB = LA ⟪ own `ℕ ∷ [] , id (` 1) ⟫
T₈ = LB ⟪ own `ℕ ∷ [] , unseal 0 ⟫

SA SB : Ctxᵗ
SA = own (` 0) ∷ S₆₂            -- the NESTED interior spine of LA
SB = own (` 2) ∷ own `ℕ ∷ own `ℕ ∷ own `ℕ ∷ []   -- the MERGED one

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

-- stuck in the mini-core, exactly like T₆ …
stuck-T₈ : ∀ {M} → ¬ (Δ₆ ⊢ T₈ -→ M)
stuck-T₈ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ ()))))

-- … and the ONLY IdAbsorb redex is the OUTERMOST pair, because the inner
-- pair's outer face `id (` 1)` is INERT.  (Without the `Active c` premise
-- both pairs would be redexes and `ξ-⟪⟫` would fire as well.)
inner-pair-not-active : ¬ Active (id (` 1))
inner-pair-not-active (A-idb ())

T₈-1 T₈-2 T₈-3 : Term
T₈-1 = LA ⟪ own `ℕ ∷ own `ℕ ∷ [] , unseal 1 ⟫
T₈-2 = (($ 7) ⟪ [] , seal 2 ⟫)
         ⟪ own (` 0) ∷ own `ℕ ∷ own `ℕ ∷ [] , unseal 2 ⟫
T₈-3 = ($ 7) ⟪ own (` 0) ∷ own `ℕ ∷ own `ℕ ∷ [] , id `ℕ ⟫

⊢T₈-1 : Δ₆ ∣ [] ⊢ T₈-1 ⦂ `ℕ
⊢T₈-1 = env (bw-o wf-ℕ (bw-o wf-ℕ bw[])) ⊢LA (conv-unseal (es ez)) wf-ℕ

⊢T₈-2-in : SB ∣ [] ⊢ ($ 7) ⟪ [] , seal 2 ⟫ ⦂ ` 2
⊢T₈-2-in = env bw[] ⊢$ (conv-seal (es (es ez)))
               (wf-var (own `ℕ , es (es ez) , vis-o))

⊢T₈-2 : Δ₆ ∣ [] ⊢ T₈-2 ⦂ `ℕ
⊢T₈-2 = env (bw-o (wf-var (own `ℕ , ez , vis-o))
                  (bw-o wf-ℕ (bw-o wf-ℕ bw[])))
            ⊢T₈-2-in (conv-unseal (es (es ez))) wf-ℕ

⊢T₈-3 : Δ₆ ∣ [] ⊢ T₈-3 ⦂ `ℕ
⊢T₈-3 = env {p = ↑ˢ} (bw-o (wf-var (own `ℕ , ez , vis-o))
                  (bw-o wf-ℕ (bw-o wf-ℕ bw[])))
            ⊢$ (conv-id base-ℕ) wf-ℕ

run-T₈ : Δ₆ ⊢ T₈ ⇛* $ 7
run-T₈ = IdAbsorb (V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv) A-unseal
    then IdAbsorb (V-⟪⟫ V-$ I-seal) A-unseal
    then CancelR {B = `ℕ} V-$
    then Drop$′ base-ℕ
    then done

-- BUT NOTE what the second absorption did to the spine: `own (` 0)` was
-- re-read one frame out by `∸ 2`, which is the IDENTITY on 0, so the merged
-- interior binds `own (` 2)` where the nested one binds `own (` 0)`.
-- The run survives only because nothing in T₈ READS that owner.
⊳-spine-mismatch :
  intC ((own (` 0) ∷ []) ⊳ (own `ℕ ∷ own `ℕ ∷ [])) Δ₆
    ≢ intC (own (` 0) ∷ []) (intC (own `ℕ ∷ own `ℕ ∷ []) Δ₆)
⊳-spine-mismatch ()

_ : intC ((own (` 0) ∷ []) ⊳ (own `ℕ ∷ own `ℕ ∷ [])) Δ₆ ≡ SB
_ = refl

_ : intC (own (` 0) ∷ []) (intC (own `ℕ ∷ own `ℕ ∷ []) Δ₆) ≡ SA
_ = refl

------------------------------------------------------------------------
-- §4  R3's adversaries — where `⊳` may and may not go (THE NO-⊕ TEST)
------------------------------------------------------------------------

-- §4a  THE MASK JAM IS A PHANTOM, twice over.
--
-- (1) A conceal is INVISIBLE to the face spine: `fscp` skips `cnc`, so the
--     re-based face never lands on a slot the id-layer masks.
fceC-cnc : ∀ {X} (Θ : BCtx) (Δ : Ctxᵗ) → fceC (cnc X ∷ Θ) Δ ≡ fceC Θ Δ
fceC-cnc Θ Δ = refl

-- (2) And the id-layer can never conceal the slot ITS OWN FACE names:
--     `value-var-visible` (§2) says a value's variable type is visible on
--     the value's own spine, because `env`'s last conjunct checks it there.
--     So "Θ₁ contains `cnc Y` while the face cites Y" is untypeable, not
--     merely awkward.

-- §4b  THE REAL JAM #1: Bwf IS NOT COMPOSITIONAL.
--
-- Θ₂ re-exposes a masked slot (`ali 0`) and the id-layer masks it again
-- (`cnc 0`).  The term below TYPES, `⊳` computes BOTH SPINES CORRECTLY,
-- and yet `Bwf` rejects the merged skeleton — because `Bwf` checks every
-- entry against the PLAIN exterior instead of against the spine the
-- entries after it produce.

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

-- the merged skeleton is `cnc 0 ∷ ali 0 ∷ []` …
_ : Θₘ₁ ⊳ Θₘ₂ ≡ cnc 0 ∷ ali 0 ∷ []
_ = refl

-- … and it computes the RIGHT interior and face spines …
_ : intC (Θₘ₁ ⊳ Θₘ₂) Δₘ ≡ intC Θₘ₁ (intC Θₘ₂ Δₘ)
_ = refl

_ : fceC (Θₘ₁ ⊳ Θₘ₂) Δₘ ≡ fceC Θₘ₁ (intC Θₘ₂ Δₘ)
_ = refl

-- … but it is not Bwf, so the contractum is UNTYPEABLE.
¬Bwf-merge-mask : ¬ Bwf Δₘ (Θₘ₁ ⊳ Θₘ₂)
¬Bwf-merge-mask (bw-c (_ , ez , ()) _)

-- §4c  THE REAL JAM #2: an inner OWNER REP that names an outer owner.
-- Flattening would have to SUBSTITUTE Θ₂'s reps into Θ₁'s — rep arithmetic,
-- i.e. exactly the boundary composition `⊕` the CANCEL PROBE VERDICT
-- forbids.  `⊳` refuses to do it (it only re-reads names), so the merged
-- skeleton is ill-formed outright.

Θᵣ₁ Θᵣ₂ : BCtx
Θᵣ₁ = own (` 0) ∷ []
Θᵣ₂ = own `ℕ ∷ []

Sᵣ : Ctxᵗ
Sᵣ = own (` 0) ∷ own `ℕ ∷ []

Vᵣ Tᵣ : Term
Vᵣ = ($ 7) ⟪ [] , seal 1 ⟫
Tᵣ = (Vᵣ ⟪ Θᵣ₁ , id (` 1) ⟫) ⟪ Θᵣ₂ , unseal 0 ⟫

⊢Vᵣ : Sᵣ ∣ [] ⊢ Vᵣ ⦂ ` 1
⊢Vᵣ = env bw[] ⊢$ (conv-seal (es ez)) (wf-var (own `ℕ , es ez , vis-o))

⊢Tᵣ : [] ∣ [] ⊢ Tᵣ ⦂ `ℕ
⊢Tᵣ = env (bw-o wf-ℕ bw[])
          (env (bw-o (wf-var (own `ℕ , ez , vis-o)) bw[]) ⊢Vᵣ
               (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
               (wf-var (own `ℕ , ez , vis-o)))
          (conv-unseal ez) wf-ℕ

stuck-Tᵣ : ∀ {M} → ¬ ([] ⊢ Tᵣ -→ M)
stuck-Tᵣ (ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ ())))

-- IdAbsorb applies to it (V is a value, `unseal 0` is active) …
absorb-Tᵣ : [] ⊢ Tᵣ ⇛ Vᵣ ⟪ own (` 0) ∷ own `ℕ ∷ [] , unseal 1 ⟫
absorb-Tᵣ = IdAbsorb (V-⟪⟫ V-$ I-seal) A-unseal

-- … and the contractum is UNTYPEABLE: the rep `` ` 0 `` named Θ₂'s owner,
-- which the flat skeleton no longer binds before it.
¬Bwf-merge-rep : ¬ Bwf [] (Θᵣ₁ ⊳ Θᵣ₂)
¬Bwf-merge-rep (bw-o (wf-var (_ , () , _)) _)

-- and the spines disagree as well (`⊳` lifts by 1 what should have been
-- resolved to `ℕ`):
_ : intC (Θᵣ₁ ⊳ Θᵣ₂) [] ≡ own (` 1) ∷ own `ℕ ∷ []
_ = refl

_ : intC Θᵣ₁ (intC Θᵣ₂ []) ≡ Sᵣ
_ = refl

------------------------------------------------------------------------
-- §5  R1 — VACUOUS INSTANTIATION, the optional companion
------------------------------------------------------------------------

--   TyBeta-vac : ¬ Occ 0 B → Δ ⊢ (Λ N) ·[ B , A ] ⇛ lowᴹ N
--   (and the mini-core's TyBeta′ for the `Occ 0 B` branch)
--
-- (c) THE TWO BRANCHES ARE DISJOINT by the decidable condition `occ? 0 B`.
TyBeta-branches-disjoint : ∀ {B} → Occ 0 B → ¬ Occ 0 B → ⊥
TyBeta-branches-disjoint o ¬o = ¬o o

-- (a) T₆'s BIRTH STORY.  The transparent layer of T₆ is minted by an
-- ordinary TyBeta whose body type is an OUTER variable: `unsealAt 0 (` 1)`
-- is the identity face, and the owner it binds is never read.
_ : unsealAt 0 (` 1) ≡ id (` 1)
_ = refl

⊢W₆₀Λ : (abst ∷ S₆₁) ∣ [] ⊢ W₆₀ ⦂ ` 1
⊢W₆₀Λ = env bw[] ⊢$ (conv-seal (es ez)) (wf-var (own `ℕ , es ez , vis-o))

⊢birth : S₆₁ ∣ [] ⊢ (Λ W₆₀) ·[ ` 1 , `ℕ ] ⦂ ` 0
⊢birth = ⊢·[] (⊢Λ ⊢W₆₀Λ) wf-ℕ

-- the mini-core mints the id-layer …
birth-orig : S₆₁ ⊢ (Λ W₆₀) ·[ ` 1 , `ℕ ] ⇛ W₆₁
birth-orig = TyBeta′

-- … R1 does not: no wrapper is born, and the body is strengthened.
birth-vac : S₆₁ ⊢ (Λ W₆₀) ·[ ` 1 , `ℕ ] ⇛ ($ 7) ⟪ [] , seal 0 ⟫
birth-vac = TyBeta-vac (λ ())

-- R1's contractum is typed at the redex's type (the strengthening
-- obligation, discharged on this instance).
⊢birth-vac : S₆₁ ∣ [] ⊢ ($ 7) ⟪ [] , seal 0 ⟫ ⦂ ` 0
⊢birth-vac = env bw[] ⊢$ (conv-seal ez) (wf-var (own `ℕ , ez , vis-o))

-- and T₆'s enclosing wrapper then finds an ORDINARY cancel pair.
T₆′ : Term
T₆′ = (($ 7) ⟪ [] , seal 0 ⟫) ⟪ own `ℕ ∷ [] , unseal 0 ⟫

⊢T₆′ : Δ₆ ∣ [] ⊢ T₆′ ⦂ `ℕ
⊢T₆′ = env (bw-o wf-ℕ bw[]) ⊢birth-vac (conv-unseal ez) wf-ℕ

run-T₆′ : Δ₆ ⊢ T₆′ ⇛* $ 7
run-T₆′ = CancelR {B = `ℕ} V-$ then Drop$′ base-ℕ then done

-- (b) BUT R1 CANNOT PREVENT THE TyPeel-MINTED ID-LAYERS.  `TyPeel` copies
-- the ∀-face's BODY `s` into the contractum's face verbatim, so a package
-- whose inner ∀-body returns an OUTER variable mints `id (` X)` no matter
-- what TyBeta does.  Here it lands on T₆ ITSELF.

Pkg : Term
Pkg = (Λ W₆₀) ⟪ [] , `∀ (id (` 1)) ⟫

⊢Pkg : S₆₁ ∣ [] ⊢ Pkg ⦂ `∀ (` 1)
⊢Pkg = env bw[] (⊢Λ ⊢W₆₀Λ)
           (conv-all (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o)))
           (wf-∀ (wf-var (own `ℕ , es ez , vis-o)))

⊢PkgApp : S₆₁ ∣ [] ⊢ Pkg ·[ ` 1 , `ℕ ] ⦂ ` 0
⊢PkgApp = ⊢·[] ⊢Pkg wf-ℕ

Pk-1 : Term
Pk-1 = ((Λ (($ 7) ⟪ [] , seal 2 ⟫)) ·[ ` 2 , ` 0 ])
         ⟪ own `ℕ ∷ [] , id (` 1) ⟫

⊢Pk-1-in : S₆₂ ∣ [] ⊢ (Λ (($ 7) ⟪ [] , seal 2 ⟫)) ·[ ` 2 , ` 0 ] ⦂ ` 1
⊢Pk-1-in = ⊢·[] (⊢Λ (env bw[] ⊢$ (conv-seal (es (es ez)))
                        (wf-var (own `ℕ , es (es ez) , vis-o))))
                (wf-var (own `ℕ , ez , vis-o))

⊢Pk-1 : S₆₁ ∣ [] ⊢ Pk-1 ⦂ ` 0
⊢Pk-1 = env (bw-o wf-ℕ bw[]) ⊢Pk-1-in
            (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
            (wf-var (own `ℕ , ez , vis-o))

-- WITH R1 ON, the TyPeel'd package reduces to exactly W₆₁ — the stuck
-- transparent layer of §6 of ConvBoundaryProbe.
run-TyPeel : S₆₁ ⊢ Pkg ·[ ` 1 , `ℕ ] ⇛* W₆₁
run-TyPeel = TyPeelR V-Λ then ξ-⟪⟫′ (TyBeta-vac (λ ())) then done

T₉ : Term
T₉ = (Pkg ·[ ` 1 , `ℕ ]) ⟪ own `ℕ ∷ [] , unseal 0 ⟫

⊢T₉ : Δ₆ ∣ [] ⊢ T₉ ⦂ `ℕ
⊢T₉ = env (bw-o wf-ℕ bw[]) ⊢PkgApp (conv-unseal ez) wf-ℕ

R1-does-not-prevent : Δ₆ ⊢ T₉ ⇛* T₆
R1-does-not-prevent =
      ξ-⟪⟫′ (TyPeelR V-Λ)
 then ξ-⟪⟫′ (ξ-⟪⟫′ (TyBeta-vac (λ ())))
 then done

-- WITH R1 OFF, the same package reaches the depth-2 STACK of §3b — which
-- is how T₈ is reachable, and how an id-layer acquires the rep-carrying
-- skeleton `own (` 0)` that §4c is about.
run-TyPeel-stack : Δ₆ ⊢ T₉ ⇛* T₈
run-TyPeel-stack =
      ξ-⟪⟫′ (TyPeelR V-Λ)
 then ξ-⟪⟫′ (ξ-⟪⟫′ TyBeta′)
 then done

------------------------------------------------------------------------
-- §6  R2 — DEEP CANCEL, comparison note
------------------------------------------------------------------------

--   CancelDeep : Value V
--     → Δ ⊢ ((V ⟪ Θ₀ , seal X′ ⟫) ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal X ⟫
--         ⇛ V ⟪ Θ₀ ⊳ (Θ₁ ⊳ Θ₂) , idc B ⟫
--
-- On T₆ it is exactly IdAbsorb ⨟ CancelR, fused: same contractum.
CancelDeep-T₆ : Δ₆ ⊢ T₆ ⇛ T₆-2
CancelDeep-T₆ = CancelDeep {B = `ℕ} V-$

-- It buys nothing and costs completeness: it names ONE id-layer, so the
-- depth-2 stack T₈ is not a redex (T₈'s id-layer's interior is another
-- id-layer, not a seal-topped value), and the same argument defeats any
-- fixed depth.  It also uses `⊳` TWICE, so it inherits §4b/§4c twice over.
-- IdAbsorb, by contrast, peels one layer per step (`run-T₈`).

------------------------------------------------------------------------
-- §7  (e)  THE NAKED DROP — the door, closed
------------------------------------------------------------------------

-- `V ⟪ Θ , id A ⟫ -→ V` is unsound because V is typed on `intC Θ Δ`, not
-- on Δ: the CancelProbe context-conjunct trap.  A concrete failing instance
-- (the boundary binds an owner, and V's licence cites a slot Δ does not
-- even have):

Δₑ : Ctxᵗ
Δₑ = own `ℕ ∷ []

Nₑ : Term
Nₑ = (($ 7) ⟪ [] , seal 1 ⟫) ⟪ own `𝔹 ∷ [] , id (` 1) ⟫

⊢Nₑ : Δₑ ∣ [] ⊢ Nₑ ⦂ ` 0
⊢Nₑ = env (bw-o wf-𝔹 bw[])
          (env bw[] ⊢$ (conv-seal (es ez))
               (wf-var (own `ℕ , es ez , vis-o)))
          (conv-idv {p = ↑ˢ} (own `ℕ , es ez , vis-o))
          (wf-var (own `ℕ , ez , vis-o))

-- the interior is not typeable in the EXTERIOR spine, at any type
Δₑ-no-1 : ∀ {E} → Δₑ ∋e 1 , E → ⊥
Δₑ-no-1 (es ())

naked-drop-trap : ∀ {C} → ¬ (Δₑ ∣ [] ⊢ ($ 7) ⟪ [] , seal 1 ⟫ ⦂ C)
naked-drop-trap (env _ _ (conv-seal d) _) = Δₑ-no-1 d

-- THE SOUND SIDE CONDITION: the drop is sound exactly when the boundary
-- changes NO FRAME.  Then `intC [] Δ ≡ Δ` and the identity face fixes the
-- type, so the interior derivation is already the exterior one.
conv-id-refl : ∀ {Δ A B C p} → Δ ⊢ id A ∶ B ⇝ C ∙ p → B ≡ C
conv-id-refl (conv-id _)  = refl
conv-id-refl (conv-idv _) = refl

drop-empty-frame : ∀ {Δ Γ V A B} → Δ ∣ Γ ⊢ V ⟪ [] , id A ⟫ ⦂ B
                 → Δ ∣ [] ⊢ V ⦂ B
drop-empty-frame {Δ = Δ} {V = V} (env _ ⊢V ⊢c _) =
  subst (λ T → Δ ∣ [] ⊢ V ⦂ T) (conv-id-refl ⊢c) ⊢V

------------------------------------------------------------------------
-- §8  R5 — IdPush: IdAbsorb's degenerate form, with NO merge at all
------------------------------------------------------------------------

--   IdPush : Value V
--     → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
--         ⇛ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫
--
-- Same LHS as IdAbsorb, same methodology (`unseal` is the ONLY active face
-- an id-(` X) layer can meet — `outer-id-base-untypeable`), but instead of
-- merging the two skeletons it SWAPS THE TWO FACES: the transparent layer
-- becomes the revealing one, and the outer becomes transparent.  BOTH
-- FRAMES ARE UNTOUCHED, so §4b and §4c cannot arise.
--
-- The name needs no arithmetic either: typing forces X ≡ nrev Θ₁ + Y, so
-- the pushed conversion is literally the id-face's own variable.

liftN-var : (n Y : ℕ) → liftN n (` Y) ≡ ` (n + Y)
liftN-var zero    Y = refl
liftN-var (suc n) Y rewrite liftN-var n Y = refl

tvar-inj : ∀ {X Y : ℕ} → _≡_ {A = Ty} (` X) (` Y) → X ≡ Y
tvar-inj refl = refl

conv-unseal-src : ∀ {Δ X A B p} → Δ ⊢ unseal X ∶ A ⇝ B ∙ p → A ≡ ` X
conv-unseal-src (conv-unseal _) = refl

-- THE NAME IS ALREADY THERE (general, not an instance): in any typed
-- id-layer under an `unseal`, the id-face's variable IS the pushed
-- conversion's name.  So IdPush moves no index and invents no slot.
idpush-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → X ≡ nrev Θ₁ + Y
idpush-name {Θ₁ = Θ₁} (env _ (env _ _ ⊢cᵢ _) ⊢cₒ _)
  with conv-unseal-src ⊢cₒ
... | refl = tvar-inj (trans (sym (conv-idv-tgt ⊢cᵢ)) (liftN-var (nrev Θ₁) _))

push-T₆ : Δ₆ ⊢ T₆ ⇛ (W₆₀ ⟪ own `ℕ ∷ [] , unseal 1 ⟫) ⟪ own `ℕ ∷ [] , id `ℕ ⟫
push-T₆ = IdPush {A = `ℕ} (V-⟪⟫ V-$ I-seal)

⊢push-T₆-in : S₆₁ ∣ [] ⊢ W₆₀ ⟪ own `ℕ ∷ [] , unseal 1 ⟫ ⦂ `ℕ
⊢push-T₆-in = env (bw-o wf-ℕ bw[]) ⊢W₆₀ (conv-unseal (es ez)) wf-ℕ

⊢push-T₆ : Δ₆ ∣ [] ⊢ (W₆₀ ⟪ own `ℕ ∷ [] , unseal 1 ⟫)
                        ⟪ own `ℕ ∷ [] , id `ℕ ⟫ ⦂ `ℕ
⊢push-T₆ = env {p = ↑ˢ} (bw-o wf-ℕ bw[]) ⊢push-T₆-in (conv-id base-ℕ) wf-ℕ

run-T₆-push : Δ₆ ⊢ T₆ ⇛* $ 7
run-T₆-push = push-T₆
         then ξ-⟪⟫′ (CancelR {B = `ℕ} V-$)
         then ξ-⟪⟫′ (Drop$′ base-ℕ)
         then Drop$′ base-ℕ
         then done

-- AND IT CLEARS §4c, the instance `⊳` cannot express at all.
push-Tᵣ : [] ⊢ Tᵣ ⇛ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫
push-Tᵣ = IdPush {A = `ℕ} (V-⟪⟫ V-$ I-seal)

⊢push-Tᵣ : [] ∣ [] ⊢ (Vᵣ ⟪ Θᵣ₁ , unseal 1 ⟫) ⟪ Θᵣ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tᵣ = env {p = ↑ˢ} (bw-o wf-ℕ bw[])
               (env (bw-o (wf-var (own `ℕ , ez , vis-o)) bw[]) ⊢Vᵣ
                    (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

run-Tᵣ-push : [] ⊢ Tᵣ ⇛* $ 7
run-Tᵣ-push = push-Tᵣ
         then ξ-⟪⟫′ (CancelR {B = `ℕ} V-$)
         then ξ-⟪⟫′ (Drop$′ base-ℕ)
         then Drop$′ base-ℕ
         then done

-- and it clears §4b as well, for the same reason (no skeleton moves).
push-Tₘ : Δₘ ⊢ Tₘ ⇛ (Vₘ ⟪ Θₘ₁ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫
push-Tₘ = IdPush {A = `ℕ} (V-⟪⟫ V-$ I-seal)

⊢push-Tₘ : Δₘ ∣ [] ⊢ (Vₘ ⟪ Θₘ₁ , unseal 1 ⟫) ⟪ Θₘ₂ , id `ℕ ⟫ ⦂ `ℕ
⊢push-Tₘ = env {p = ↑ˢ} (bw-a ez bw[])
               (env (bw-c (own `𝔹 , ez , vis-o) bw[]) ⊢Vₘ
                    (conv-unseal (es ez)) wf-ℕ)
               (conv-id base-ℕ) wf-ℕ

------------------------------------------------------------------------
-- §9  THE DETERMINISM TABLE, and two defects found on the way
------------------------------------------------------------------------

-- (A)  DISJOINTNESS OF THE NEW RULE FROM THE OLD ONES, syntactically.
IdAbsorb≢Cancel : ∀ {V V′ Θ₁ Θ₁′ Θ₂ Θ₂′ X X′ c}
  → (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , c ⟫
      ≢ (V′ ⟪ Θ₁′ , seal X′ ⟫) ⟪ Θ₂′ , unseal X′ ⟫
IdAbsorb≢Cancel ()

IdAbsorb≢Drop$ : ∀ {V Θ₁ Θ₂ X c n Θ A}
  → (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , c ⟫ ≢ ($ n) ⟪ Θ , id A ⟫
IdAbsorb≢Drop$ ()

-- vs ξ-⟪⟫: the LHS's interior is a VALUE, so it can step only if it is
-- Λ-headed — which is the ξ-Λ escape hatch of (C), not a new overlap.
ΛH-⟪⟫-inv : ∀ {M Θ c} → ΛH (M ⟪ Θ , c ⟫) → ΛH M
ΛH-⟪⟫-inv (λh-⟪⟫ h) = h

IdAbsorb-vs-ξ⟪⟫ : ∀ {Δ V Θ₁ X M′} → Value V
  → Δ ⊢ V ⟪ Θ₁ , id (` X) ⟫ ⇛ M′ → ΛH V
IdAbsorb-vs-ξ⟪⟫ v st = ΛH-⟪⟫-inv (value-step-ΛH (V-⟪⟫ v I-idv) st)

-- vs itself on a stack: `inner-pair-not-active` (§3b).
-- vs IdPush: SAME LHS — they are ALTERNATIVES, never a combination.

-- (B)  DEFECT (i) OF THE MINI-CORE: `Cancel`'s residue masks EXTERIOR
-- slots that need not exist.  `maskOwns (nrev Θ₂)` is `cnc (n-1) ∷ … ∷ cnc 0`
-- and `scp` applies those to Δ, not to the boundary's own owners.  The
-- mini-core's OWN cancel example (`cancel-step`, ConvBoundaryProbe §5)
-- produces an un-Bwf-able residue:
¬Bwf-cancelTm-residue : ¬ Bwf [] (own `ℕ ∷ cnc 0 ∷ [])
¬Bwf-cancelTm-residue (bw-o _ (bw-c (_ , () , _) _))

-- Dropping `maskOwns` (rule `CancelR` here) types on every instance in
-- this file; the masks were unnecessary because `intC` retains the entries
-- anyway and `⊢retag` covers the extra knowledge.

-- (C)  DEFECT (ii): `TyPeel` does not shift its type annotation.  `B` is
-- read over `abst ∷ Δ`, the contractum over `abst ∷ own A ∷ Δ`.  On the §5
-- package the unshifted contractum is ill-typed:
TyPeel-orig-ill-typed :
  ¬ (S₆₂ ∣ [] ⊢ (Λ (($ 7) ⟪ [] , seal 2 ⟫)) ·[ ` 1 , ` 0 ] ⦂ ` 1)
TyPeel-orig-ill-typed ()

-- (D)  "DET AND VALUES-DON'T-STEP ARE DESIGN LAWS" — both are ALREADY
-- FALSE in the mini-core, before any new rule, because reduction goes
-- under Λ (`ξ-Λ`) while `Λ N` is a value for every N.  A value that steps:
Ω : Term
Ω = Λ ((ƛ `ℕ ∙ ($ 1)) · ($ 2))

value-that-steps : Value Ω × ([] ⊢ Ω ⇛ Λ ($ 1))
value-that-steps = V-Λ , ξ-Λ′ (Beta′ V-$)

-- … and a TYPED term with two distinct steps (Cancel vs ξ-⟪⟫ ⨟ ξ-Λ):
Mᵈ N₁ᵈ N₂ᵈ : Term
Mᵈ  = (Ω ⟪ [] , seal 0 ⟫) ⟪ own (`∀ `ℕ) ∷ [] , unseal 0 ⟫
N₁ᵈ = Ω ⟪ own (`∀ `ℕ) ∷ [] , `∀ (id `ℕ) ⟫
N₂ᵈ = ((Λ ($ 1)) ⟪ [] , seal 0 ⟫) ⟪ own (`∀ `ℕ) ∷ [] , unseal 0 ⟫

⊢Ω : (own (`∀ `ℕ) ∷ []) ∣ [] ⊢ Ω ⦂ `∀ `ℕ
⊢Ω = ⊢Λ (⊢· (⊢ƛ wf-ℕ ⊢$) ⊢$)

⊢Mᵈ : [] ∣ [] ⊢ Mᵈ ⦂ `∀ `ℕ
⊢Mᵈ = env (bw-o (wf-∀ wf-ℕ) bw[])
          (env bw[] ⊢Ω (conv-seal ez) (wf-var (own (`∀ `ℕ) , ez , vis-o)))
          (conv-unseal ez) (wf-∀ wf-ℕ)

det-already-broken : ([] ⊢ Mᵈ ⇛ N₁ᵈ) × ([] ⊢ Mᵈ ⇛ N₂ᵈ) × (N₁ᵈ ≢ N₂ᵈ)
det-already-broken =
  CancelR {B = `∀ `ℕ} V-Λ , ξ-⟪⟫′ (ξ-⟪⟫′ (ξ-Λ′ (Beta′ V-$))) , λ ()

------------------------------------------------------------------------
-- §10  VERDICT
------------------------------------------------------------------------
--
-- R3 IdAbsorb (with `Active c`) — RECOMMENDED SHAPE.
--   T₆ runs to 7 (`run-T₆`), every contractum types (`⊢T₆-1`, `⊢T₆-2`),
--   stacks resolve outermost-active-first and any depth terminates
--   (`run-T₈`), no value steps (`IdAbsorb-lhs-not-value`), and the rule is
--   syntactically disjoint from Cancel and Drop$.  The only active face it
--   can ever meet is `unseal` (`outer-id-base-untypeable`), so the id-base
--   branch of `Active` is vacuous, and the inner face MUST be spelled
--   `id (` X)` (at `id A` with A base the interior is itself active and
--   `Drop$` overlaps).
--   ITS ONE COST is `⊳`.  Preservation for IdAbsorb needs, in general:
--     (1)  intC (Θ₁ ⊳ Θ₂) Δ ≡ intC Θ₁ (intC Θ₂ Δ)
--     (2)  fceC (Θ₁ ⊳ Θ₂) Δ ≡ fceC Θ₁ (intC Θ₂ Δ)
--     (3)  Bwf Δ (Θ₁ ⊳ Θ₂)
--   (1) and (2) hold definitionally whenever no entry of Θ₁ reaches into
--   Θ₂'s owners; §4c is a typed, stuck instance where (1) FAILS and the
--   repair would be substituting Θ₂'s reps into Θ₁'s — rep arithmetic,
--   i.e. `⊕`.  §4b is a typed instance where (1) and (2) HOLD and (3)
--   fails, because `Bwf` checks every entry against the plain exterior
--   rather than against the spine the entries after it build.
--
-- R1 TyBeta-vac — OPTIONAL, and it does NOT discharge `⊳`'s side condition.
--   It kills EVERY TyBeta-born id-layer (`unsealAt 0 B` is an identity face
--   only when 0 ∉ B), including §4c's; but TyPeel copies the ∀-face's body
--   verbatim, so `run-TyPeel` mints the very same W₆₁ with R1 on.  Keep R1
--   as hygiene (fewer wrappers, smaller reachable set), not as a fix.
--
-- R2 CancelDeep — NO.  Fused, depth-limited, and it uses `⊳` twice.
--
-- R5 IdPush — the same LHS with `⊳` deleted.  It swaps the two faces
--   instead of merging the two frames, so (1)-(3) never arise; the pushed
--   name is already written in the id-face (`idpush-name`); and it clears
--   BOTH adversaries R3 cannot (`run-Tᵣ-push`, `push-Tₘ`).  Its residue is
--   an identity face at the exterior rep — the same implicit `Cancel`
--   already carries.  If `⊳`'s two side conditions are not paid for
--   (compositional `Bwf`, plus a discipline that keeps an id-layer's
--   owners exterior-readable), this is the rule to take.

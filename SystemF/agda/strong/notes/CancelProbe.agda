module strong.notes.CancelProbe where

------------------------------------------------------------------------
-- CANCEL — a design probe for Decision 6 (notes/DECISIONS.md).
--
-- Decision 6's conflict: progress needs a COLLAPSE at a reveal-variable
-- face (§9i) and the determinism law forbids a rule whose LHS is a VALUE
-- (§9j).  Jeremy's direction: "that example looks like it needs a Cancel
-- reduction, not Merge", refined to
--
--   "merge and cancel are related — cancel is a special form of merge +
--    drop.  Cancel is the special case where the inner value has type X
--    that is CONCEALED by the inner boundary and REVEALED by the outer
--    boundary."
--
-- This file is a PROBE: it defines nothing live, adds nothing to All.agda,
-- and answers Q1–Q4 with machine-checked evidence.  Everything below is
-- checked by `agda --safe`.
--
-- ROADMAP
--   §1  the side condition (Q1): the preservation form (P), the
--       face-anchored form (F), the lineage form (L), and the general
--       PRESERVATION THEOREM for a bare `-→ V` cancel.
--   §2  the §9i instance: Cancel fires, and CANCEL = MERGE + DROP∅.
--   §3  the two refutations (Q1(b), Q1-extra-entries).
--   §4  determinism placements (Q2): B′ standalone + value restriction,
--       A′ folded into the elimination.
--   §5  the crux (Q3): the well-typed variable-face nesting shapes, and
--       the two ADVERSARIES on which no Cancel form fires.
--   §6  what dies (Q4) — prose, plus the machine facts it rests on.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_;
                            s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.Context
open import strong.Unfold
open import strong.Boundary
open import strong.BReduction
open import strong.Canonical using (canon-var; Wrapped)
open import strong.notes.InstallGauntlet
  using (Θr; Θrᵈ; Ψr; rvQ₅; ⊢rvQ₅; Δcx; Θcx1; Θcx2; Vcx)

------------------------------------------------------------------------
-- §1.  THE SIDE CONDITION (Q1)
--
-- A Cancel rule has the shape
--
--   Cancel : Value V → (side condition)
--          → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V
--
-- and the contractum is the BARE body.  Inverting (env) twice says
-- exactly what the redex gives us and what the contractum needs:
--
--   redex     : Δ ∣ Γₜ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ ⦂ substᵗ (ρᵇ Θ₂) B₂
--   body      : intOf (intOf Δ Θ₂) Θ₁ ∣ [] ⊢ V ⦂ substᵗ (γᵇ Θ₁) B₁
--   wanted    : Δ ∣ [] ⊢ V ⦂ substᵗ (ρᵇ Θ₂) B₂
--
-- so the side condition is FORCED to imply the two equations below.  That
-- is form (P): it is not a design choice, it is the preservation
-- obligation itself, and §1.1 proves it discharges preservation with no
-- further hypothesis.
------------------------------------------------------------------------

-- (P) THE PRESERVATION FORM.  Nothing but what `-→ V` needs.
CancelOK : TCtx → BCtx → BCtx → Ty → Ty → Set
CancelOK Δ Θ₁ Θ₂ B₁ B₂ =
    (intOf (intOf Δ Θ₂) Θ₁ ≡ Δ)                       -- CONTEXTS undo
  × (substᵗ (γᵇ Θ₁) B₁ ≡ substᵗ (ρᵇ Θ₂) B₂)           -- FACES agree

-- (F) THE FACE-ANCHORED FORM (Jeremy, 2026-09-04).  ` Y is Θ₁'s name for
-- the exterior slot X, Θ₁ CONCEALS X, and Θ₂ REVEALS it; the conceal's rep
-- and the reveal's rep agree.  The LAST conjunct is the same context
-- equation as (P) — §3.2 shows by counterexample that it CANNOT be
-- dropped: the face pair alone does not preserve types.
CancelFace : TCtx → BCtx → BCtx → ℕ → ℕ → Set
CancelFace Δ Θ₁ Θ₂ Y X =
    (X < revs Θ₂)                                     -- ` X is a REVEAL
  × (isConc X Θ₁ ≡ true)                              -- … Θ₁ CONCEALS it
  × (Y ≡ revs Θ₁ + X)                                 -- ` Y is Θ₁'s name
  × (substᵗ (γᵇ Θ₁) (` Y) ≡ substᵗ (ρᵇ Θ₂) (` X))     -- the REPS agree
  × (intOf (intOf Δ Θ₂) Θ₁ ≡ Δ)                       -- CONTEXTS undo

-- the face form is a special case of the preservation form
face→OK : ∀ {Δ Θ₁ Θ₂ Y X} → CancelFace Δ Θ₁ Θ₂ Y X
        → CancelOK Δ Θ₁ Θ₂ (` Y) (` X)
face→OK (_ , _ , _ , fc , ctx) = ctx , fc

-- (L) THE LINEAGE FORM: Θ₁ is the boundary Peel minted as Θ₂'s dual.  It
-- is a BIRTH-SITE condition, not a checkable-at-the-redex one; §2 shows it
-- holds on §9i's reachable witness.
Lineage : TCtx → BCtx → BCtx → Set
Lineage Δ Θ₁ Θ₂ = Θ₁ ≡ dualᴳ Δ Θ₂

------------------------------------------------------------------------
-- §1.1  PRESERVATION FOR CANCEL, IN GENERAL.
--
-- Under (P) the bare contractum types, for EVERY Δ, Θ₁, Θ₂, B₁, B₂, V —
-- no bwf, no Reversal, no ≈, no MergeOK.  This is the whole of Cancel's
-- preservation case.
------------------------------------------------------------------------

-- (env) inversion, with a FREE result index (strong.Progress's idiom —
-- the unifier must never match a constructor against substᵗ (ρᵇ Θ) B₀)
inv-ty : ∀ {Δ Γₜ V Θ B₀ T} → Δ ∣ Γₜ ⊢ V ⟪ Θ , B₀ ⟫ ⦂ T
       → T ≡ substᵗ (ρᵇ Θ) B₀
inv-ty (env _ _ _) = refl

inv-bd : ∀ {Δ Γₜ V Θ B₀ T} → Δ ∣ Γₜ ⊢ V ⟪ Θ , B₀ ⟫ ⦂ T
       → intOf Δ Θ ∣ [] ⊢ V ⦂ substᵗ (γᵇ Θ) B₀
inv-bd (env _ _ ⊢V) = ⊢V

cancel-pres : ∀ {Δ Γₜ V Θ₁ Θ₂ B₁ B₂ T}
            → Δ ∣ Γₜ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ ⦂ T
            → CancelOK Δ Θ₁ Θ₂ B₁ B₂
            → Δ ∣ [] ⊢ V ⦂ T
cancel-pres {Δ} {Γₜ} {V} {Θ₁} {Θ₂} {B₁} {B₂} ⊢M (ctx , fc)
  with inv-ty ⊢M
cancel-pres {Δ} {Γₜ} {V} {Θ₁} {Θ₂} {B₁} {B₂} ⊢M (ctx , fc) | refl =
  subst (λ Δ′ → Δ′ ∣ [] ⊢ V ⦂ substᵗ (ρᵇ Θ₂) B₂) ctx
    (subst (λ T′ → intOf (intOf Δ Θ₂) Θ₁ ∣ [] ⊢ V ⦂ T′) fc
      (inv-bd (inv-bd ⊢M)))

------------------------------------------------------------------------
-- §1.2  DECIDABILITY of the side condition (needed by placement B′).
------------------------------------------------------------------------

`-inj : ∀ {X Y : ℕ} → _≡_ {A = Ty} (` X) (` Y) → X ≡ Y
`-inj refl = refl

⇒-injˡ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → A ≡ C
⇒-injˡ refl = refl

⇒-injʳ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → B ≡ D
⇒-injʳ refl = refl

∀-inj : ∀ {A B} → `∀ A ≡ `∀ B → A ≡ B
∀-inj refl = refl

_≟ᵗ_ : (A B : Ty) → Dec (A ≡ B)
(` X)   ≟ᵗ (` Y)   with X ≟ Y
(` X)   ≟ᵗ (` Y)   | yes refl = yes refl
(` X)   ≟ᵗ (` Y)   | no  ne   = no λ e → ne (`-inj e)
(` X)   ≟ᵗ `ℕ      = no λ ()
(` X)   ≟ᵗ `𝔹      = no λ ()
(` X)   ≟ᵗ (C ⇒ D) = no λ ()
(` X)   ≟ᵗ `∀ D    = no λ ()
`ℕ      ≟ᵗ (` Y)   = no λ ()
`ℕ      ≟ᵗ `ℕ      = yes refl
`ℕ      ≟ᵗ `𝔹      = no λ ()
`ℕ      ≟ᵗ (C ⇒ D) = no λ ()
`ℕ      ≟ᵗ `∀ D    = no λ ()
`𝔹      ≟ᵗ (` Y)   = no λ ()
`𝔹      ≟ᵗ `ℕ      = no λ ()
`𝔹      ≟ᵗ `𝔹      = yes refl
`𝔹      ≟ᵗ (C ⇒ D) = no λ ()
`𝔹      ≟ᵗ `∀ D    = no λ ()
(A ⇒ B) ≟ᵗ (` Y)   = no λ ()
(A ⇒ B) ≟ᵗ `ℕ      = no λ ()
(A ⇒ B) ≟ᵗ `𝔹      = no λ ()
(A ⇒ B) ≟ᵗ `∀ D    = no λ ()
(A ⇒ B) ≟ᵗ (C ⇒ D) with A ≟ᵗ C
(A ⇒ B) ≟ᵗ (C ⇒ D) | no  ne = no λ e → ne (⇒-injˡ e)
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl with B ≟ᵗ D
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl | yes refl = yes refl
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl | no  ne   = no λ e → ne (⇒-injʳ e)
`∀ A    ≟ᵗ (` Y)   = no λ ()
`∀ A    ≟ᵗ `ℕ      = no λ ()
`∀ A    ≟ᵗ `𝔹      = no λ ()
`∀ A    ≟ᵗ (C ⇒ D) = no λ ()
`∀ A    ≟ᵗ `∀ D    with A ≟ᵗ D
`∀ A    ≟ᵗ `∀ D    | yes refl = yes refl
`∀ A    ≟ᵗ `∀ D    | no  ne   = no λ e → ne (∀-inj e)

rvld-inj : ∀ {A B} → rvld A ≡ rvld B → A ≡ B
rvld-inj refl = refl

xrvld-inj : ∀ {A B} → xrvld A ≡ xrvld B → A ≡ B
xrvld-inj refl = refl

_≟ᴱ_ : (E F : TyEntry) → Dec (E ≡ F)
abst     ≟ᴱ abst     = yes refl
abst     ≟ᴱ rvld B   = no λ ()
abst     ≟ᴱ xrvld B  = no λ ()
rvld A   ≟ᴱ abst     = no λ ()
rvld A   ≟ᴱ xrvld B  = no λ ()
rvld A   ≟ᴱ rvld B   with A ≟ᵗ B
rvld A   ≟ᴱ rvld B   | yes refl = yes refl
rvld A   ≟ᴱ rvld B   | no  ne   = no λ e → ne (rvld-inj e)
xrvld A  ≟ᴱ abst     = no λ ()
xrvld A  ≟ᴱ rvld B   = no λ ()
xrvld A  ≟ᴱ xrvld B  with A ≟ᵗ B
xrvld A  ≟ᴱ xrvld B  | yes refl = yes refl
xrvld A  ≟ᴱ xrvld B  | no  ne   = no λ e → ne (xrvld-inj e)

∷-injʰ : ∀ {E F : TyEntry} {Δ Δ′} → (E ∷ Δ) ≡ (F ∷ Δ′) → E ≡ F
∷-injʰ refl = refl

∷-injᵗ : ∀ {E F : TyEntry} {Δ Δ′} → (E ∷ Δ) ≡ (F ∷ Δ′) → Δ ≡ Δ′
∷-injᵗ refl = refl

_≟ᶜ_ : (Δ Δ′ : TCtx) → Dec (Δ ≡ Δ′)
[]      ≟ᶜ []       = yes refl
[]      ≟ᶜ (F ∷ Δ′) = no λ ()
(E ∷ Δ) ≟ᶜ []       = no λ ()
(E ∷ Δ) ≟ᶜ (F ∷ Δ′) with E ≟ᴱ F
(E ∷ Δ) ≟ᶜ (F ∷ Δ′) | no  ne   = no λ e → ne (∷-injʰ e)
(E ∷ Δ) ≟ᶜ (F ∷ Δ′) | yes refl with Δ ≟ᶜ Δ′
(E ∷ Δ) ≟ᶜ (F ∷ Δ′) | yes refl | yes refl = yes refl
(E ∷ Δ) ≟ᶜ (F ∷ Δ′) | yes refl | no  ne   = no λ e → ne (∷-injᵗ e)

-- (P) IS DECIDABLE — two equations between first-order data.
cancelOK? : ∀ Δ Θ₁ Θ₂ B₁ B₂ → Dec (CancelOK Δ Θ₁ Θ₂ B₁ B₂)
cancelOK? Δ Θ₁ Θ₂ B₁ B₂ with intOf (intOf Δ Θ₂) Θ₁ ≟ᶜ Δ
cancelOK? Δ Θ₁ Θ₂ B₁ B₂ | no ne = no λ p → ne (proj₁ p)
cancelOK? Δ Θ₁ Θ₂ B₁ B₂ | yes c
  with substᵗ (γᵇ Θ₁) B₁ ≟ᵗ substᵗ (ρᵇ Θ₂) B₂
cancelOK? Δ Θ₁ Θ₂ B₁ B₂ | yes c | yes f = yes (c , f)
cancelOK? Δ Θ₁ Θ₂ B₁ B₂ | yes c | no ne = no λ p → ne (proj₂ p)

------------------------------------------------------------------------
-- §1.3  THE FACE CONJUNCT, READ AS "the conceal's rep IS the reveal's
-- rep".  γᵇ sends Θ₁'s name for a CONCEALED exterior slot to that
-- conceal's stored rep — so the fourth conjunct of (F) really is a
-- comparison of the two REPS, on the nose.
------------------------------------------------------------------------

-- strong.BReduction already has the general step (prepId-hi): the frame
-- map is the identity below revs and γcnc above it.  Composed with
-- γcnc's `sover` clause at a CONCEALED index, that is exactly
--
--   substᵗ (γᵇ Θ₁) (` (revs Θ₁ + X))  ≡  repOf X Θ₁     (isConc X Θ₁)
--
-- verified here on the instances that matter (§2 rv-face-is-reps, and
-- the extra-entry instance §3.2 e-face-is-reps).

------------------------------------------------------------------------
-- §2.  §9i's PAIR: Cancel fires, and CANCEL = MERGE + DROP∅ (Q1(a)).
--
--   Θ₂ = Θr  = ↑X:=ℕ⇒ℕ        (rvl (ℕ⇒ℕ) ∷ [])
--   Θ₁ = Θrᵈ = ↓X:=ℕ⇒ℕ        (cnc 0 (ℕ⇒ℕ) ∷ [])   — Peel's own dual
--   B₁ = B₂ = ` 0             both faces are the SAME variable
------------------------------------------------------------------------

-- the contexts undo each other exactly: Ψr = intOf [] Θr, and Θrᵈ takes
-- Ψr back to []
rv-ctx : intOf (intOf [] Θr) Θrᵈ ≡ []
rv-ctx = refl

-- the faces agree on the nose: the conceal's rep IS the reveal's rep
rv-face : substᵗ (γᵇ Θrᵈ) (` 0) ≡ substᵗ (ρᵇ Θr) (` 0)
rv-face = refl

rv-face-is-reps : (substᵗ (γᵇ Θrᵈ) (` 0) ≡ repOf 0 Θrᵈ)
                × (substᵗ (ρᵇ Θr) (` 0) ≡ `ℕ ⇒ `ℕ)
rv-face-is-reps = refl , refl

-- form (P) holds
rv-CancelOK : CancelOK [] Θrᵈ Θr (` 0) (` 0)
rv-CancelOK = refl , refl

-- form (F) holds, at Y = X = 0 (revs Θrᵈ = 0, so ` Y is Θrᵈ's own name
-- for the exterior slot 0, which it conceals; Θr reveals slot 0)
rv-CancelFace : CancelFace [] Θrᵈ Θr 0 0
rv-CancelFace = s≤s z≤n , refl , refl , refl , refl

-- form (L) holds: Θrᵈ is literally the dual Peel minted from Θr
rv-Lineage : Lineage [] Θrᵈ Θr
rv-Lineage = refl

------------------------------------------------------------------------
-- §2.1  *** CANCEL = MERGE + DROP∅ ***  (Jeremy's identity, on the
-- machine).  The exact sense: on this redex Merge's composite is EMPTY,
-- Merge's merged boundary type is the agreed rep, and Drop∅ then deletes
-- the wrapper — so Merge;Drop∅ reaches EXACTLY the bare V that Cancel
-- reaches in ONE step.
------------------------------------------------------------------------

Vrv : Term
Vrv = ƛ `ℕ ∙ ($ 7)

-- (a) the composite is empty …
rv-⊕-empty : Θrᵈ ⊕ Θr ≡ []
rv-⊕-empty = refl

-- (b) … so the intermediate Merge contractum is `V ⟪ [] , ℕ⇒ℕ ⟫ …
rv-merge-step : [] ⊢ (Vrv ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫
                  -→ Vrv ⟪ Θrᵈ ⊕ Θr , mrgB Θrᵈ Θr (` 0) ⟫
rv-merge-step = Merge (V-G G-ƛ)
  (s≤s z≤n , bwf[] , sc-⇒ sc-ℕ sc-ℕ , ≼≈[] , refl)

-- … whose boundary really is EMPTY and whose boundary type is the rep
rv-merge-shape : (Θrᵈ ⊕ Θr ≡ []) × (mrgB Θrᵈ Θr (` 0) ≡ `ℕ ⇒ `ℕ)
rv-merge-shape = refl , refl

-- (c) … and Drop∅ deletes it, reaching the bare V
rv-drop-step : [] ⊢ Vrv ⟪ [] , `ℕ ⇒ `ℕ ⟫ -→ Vrv
rv-drop-step = Drop∅ (V-G G-ƛ)

-- (d) THE IDENTITY: Merge's contractum, dropped, IS Cancel's contractum.
-- (Cancel's contractum is `Vrv` by definition of the rule; this is the
-- machine statement that the two-step route lands on the same term.)
cancel-≡-merge+drop :
    (Vrv ⟪ Θrᵈ ⊕ Θr , mrgB Θrᵈ Θr (` 0) ⟫ ≡ Vrv ⟪ [] , `ℕ ⇒ `ℕ ⟫)
cancel-≡-merge+drop = refl

-- and the general reading of the identity: whenever the composite is
-- empty, Merge's contractum is a Drop∅ redex over the SAME body, so
-- Merge;Drop∅ = Cancel.  (`mrgB` is then irrelevant — Drop∅ erases it.)
merge+drop-general : ∀ {Δ V Θ₁ Θ₂ B₁} → Value V → Θ₁ ⊕ Θ₂ ≡ []
                   → Δ ⊢ V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ B₁ ⟫ -→ V
merge+drop-general {Δ} {V} {Θ₁} {Θ₂} {B₁} v eq =
  subst (λ Θ → Δ ⊢ V ⟪ Θ , mrgB Θ₁ Θ₂ B₁ ⟫ -→ V) (sym eq) (Drop∅ v)

------------------------------------------------------------------------
-- §3.  THE TWO REFUTATIONS (Q1(b) and the extra-entry question).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §3.1  THE "SYNTACTIC MISMATCH BUT ≈" PAIR DOES NOT TYPE.
--
-- The candidate: spell the inner conceal's rep as ` 0 (= X, "licensed by
-- Reversal≈ through the ambient knowledge X:=ℕ⇒ℕ") rather than as ℕ⇒ℕ:
--
--   Θmis = ↓X:=(` 0)  = cnc 0 (` 0) ∷ []   under   Θr = ↑X:=ℕ⇒ℕ
--
-- IT IS UNTYPEABLE, and not for a subtle reason: a conceal's rep is a type
-- over the boundary's INTERIOR (the `Ψ ⊢ A` premise of bwf↓ / bwf↓x), and
-- the interior here is EMPTY.  `` ` 0 `` over the interior would name the
-- interior's own slot 0, which is a different variable from the exterior's
-- X — the rep is not "the same type spelled differently", it is a type in
-- the wrong context.  So candidate (ii), the ≈-agreement form, has NO
-- witness at this shape: there is nothing for it to catch that (i)/(P)
-- misses.
------------------------------------------------------------------------

Θmis : BCtx
Θmis = cnc 0 (` 0) ∷ []

-- the interior is empty …
mis-int : intOf Ψr Θmis ≡ []
mis-int = refl

-- … so NO wrapper over Θmis types at the ambient Ψr, whatever its body
-- and whatever its boundary type
¬⊢mis : ∀ {M B₀ T} → ¬ (Ψr ∣ [] ⊢ M ⟪ Θmis , B₀ ⟫ ⦂ T)
¬⊢mis (env (bwf↓  _ _ (wf-var ()) _)   _ _)
¬⊢mis (env (bwf↓x _ _ _ (wf-var ()) _) _ _)

------------------------------------------------------------------------
-- §3.2  EXTRA ENTRIES BEYOND THE INVERSE PAIR: the FACE conjunct alone is
-- NOT type-preserving.  *** This is the answer to "does well-typedness of
-- the face shape already force the extra entries to be irrelevant?" — NO.
--
--   Θe = ↑W:=ℕ , ↓X:=ℕ⇒ℕ   =  rvl `ℕ ∷ cnc 0 (`ℕ ⇒ `ℕ) ∷ []
--
-- Θe conceals exactly the slot Θr reveals, at exactly Θr's rep, so
-- CancelFace's FOUR face conjuncts all hold.  But Θe also REVEALS a fresh
-- slot, which survives into the interior: intOf Ψr Θe = rvld `ℕ ∷ [] ≠ [].
-- A body that USES that slot then types inside and NOT outside, so the
-- bare contractum is ill-typed: Ve below has type ℕ⇒ℕ at intOf Ψr Θe and
-- no type at all at Δ = [].
------------------------------------------------------------------------

Θe : BCtx
Θe = rvl `ℕ ∷ cnc 0 (`ℕ ⇒ `ℕ) ∷ []

Ψe : TCtx
Ψe = rvld `ℕ ∷ []

-- Θe's interior keeps the extra reveal
e-int : intOf (intOf [] Θr) Θe ≡ Ψe
e-int = refl

-- Ve : a value of type ℕ⇒ℕ whose OWN boundary reveals at the rep ` 0 —
-- legal at Ψe (whose slot 0 exists), illegal at []
Ve : Term
Ve = (ƛ `ℕ ∙ ($ 7)) ⟪ rvl (` 0) ∷ [] , `ℕ ⇒ `ℕ ⟫

⊢Ve : Ψe ∣ [] ⊢ Ve ⦂ (`ℕ ⇒ `ℕ)
⊢Ve = env (bwf↑ (wf-var here-rvld) bwf[]) (sc-⇒ sc-ℕ sc-ℕ) (⊢ƛ wf-ℕ ⊢$)

-- *** the bare contractum does NOT type at Δ = [] ***
¬⊢Ve : ∀ {T} → ¬ ([] ∣ [] ⊢ Ve ⦂ T)
¬⊢Ve (env (bwf↑ (wf-var ()) _) _ _)

-- the whole nesting, well typed at Δ = [] …
Me : Term
Me = (Ve ⟪ Θe , ` 1 ⟫) ⟪ Θr , ` 0 ⟫

⊢Me : [] ∣ [] ⊢ Me ⦂ (`ℕ ⇒ `ℕ)
⊢Me = env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
        (env (bwf↑ wf-ℕ
               (bwf↓ here (≡→≈ refl) (wf-⇒ wf-ℕ wf-ℕ) bwf[]))
             (sc-var (thereᵒ hereᵒ))
             ⊢Ve)

-- … whose FOUR face conjuncts hold …
e-face : (0 < revs Θr) × (isConc 0 Θe ≡ true) × (1 ≡ revs Θe + 0)
       × (substᵗ (γᵇ Θe) (` 1) ≡ substᵗ (ρᵇ Θr) (` 0))
e-face = s≤s z≤n , refl , refl , refl

-- … and the face conjunct really is the rep comparison
e-face-is-reps : (substᵗ (γᵇ Θe) (` 1) ≡ repOf 0 Θe)
               × (repOf 0 Θe ≡ `ℕ ⇒ `ℕ)
e-face-is-reps = refl , refl

-- … and whose CONTEXT conjunct fails, so neither (P) nor (F) fires
¬e-CancelOK : ¬ (CancelOK [] Θe Θr (` 1) (` 0))
¬e-CancelOK (() , _)

¬e-CancelFace : ¬ (CancelFace [] Θe Θr 1 0)
¬e-CancelFace (_ , _ , _ , _ , ())

-- VERDICT for the extra-entry question: whole-boundary Cancel simply does
-- NOT fire, and that is FORCED (¬⊢Ve) — a Cancel that fired here would be
-- unsound.  MERGE, by contrast, does fire and keeps the extra reveal:
e-⊕ : Θe ⊕ Θr ≡ rvl `ℕ ∷ []
e-⊕ = refl

e-MergeOK : MergeOK [] Θe Θr (` 1) (` 0)
e-MergeOK = s≤s z≤n , bwf↑ wf-ℕ bwf[] , sc-⇒ sc-ℕ sc-ℕ
          , ≼≈rvld ≼≈[] (≈unf refl) , refl

e-merge : [] ⊢ Me -→ Ve ⟪ Θe ⊕ Θr , mrgB Θe Θr (` 1) ⟫
e-merge = Merge (V-⟪⟫ (V-G G-ƛ)) e-MergeOK

------------------------------------------------------------------------
-- §4.  DETERMINISM PLACEMENT (Q2).  Two local experimental relations,
-- each = the LIVE rule set MINUS Merge/Drop∅ PLUS a Cancel.
--
-- RULE-PAIR DISJOINTNESS TABLE (both placements; ξ frames are
-- left-to-right with Value premises throughout, so only the head rules
-- can clash).  "fn" = the term in function position.
--
--   pair                  separated by
--   ------------------------------------------------------------------
--   Beta   / Peel         fn is a bare ƛ        vs a wrapper
--   Beta   / Cancel*      fn is a bare ƛ        vs a wrapper
--   Peel   / Cancel*      boundary type ⇒-shaped vs a VARIABLE ` X
--                         (Progress's cf-⇒-B₀ split — the two branches
--                          are exclusive by the constructor of B₀)
--   TyBeta / TyWrap       bare Λ                vs a wrapper
--   TyBeta / TyPeel       bare Λ                vs a wrapper
--   TyWrap / TyPeel       wrapper's body is Λ   vs a wrapper
--   TyWrap / CancelT*     boundary type `∀ B₀   vs a variable ` X
--   TyPeel / CancelT*     boundary type `∀ B₀   vs a variable ` X
--   ξ-·-l  / ξ-·-r        fn steps              vs fn is a value
--   ξ-·-r  / head rules   argument steps        vs argument is a value
--
--   *** THE ONE PAIR THAT NEEDS WORK, AND THE WHOLE POINT OF THE TWO
--   PLACEMENTS ***
--   Peel / ξ-·-r+Cancel   §9j's overlap.  In B′ it is closed by the
--                         VALUE RESTRICTION (a cancellable tower is not a
--                         value, so Peel's `Valᶜ Δ W` premise fails —
--                         ¬nd-val).  In A′ it does not arise at all: the
--                         standalone rule is gone, so a tower in ARGUMENT
--                         position simply does not step (nd-arg-stuckᴬ).
--   Cancel / Cancel       one redex, one contractum (the side condition
--                         is a pair of EQUATIONS, so there is nothing to
--                         choose).
--
-- Both placements therefore restore `values-don't-step` and `det` as far
-- as §9j is concerned; §4.4 checks the §9j term is a UNIQUE-step term in
-- each (nd-onlyᴮ / nd-onlyᴬ, coverage-complete).  In B′ value-hood is
-- KNOWLEDGE-RELATIVE (Δ-indexed), which is the price; in A′ the value
-- grammar is untouched.
------------------------------------------------------------------------

-- Cancellable Δ V Θ₂ B₂ : the wrapper `V ⟪ Θ₂ , B₂ ⟫` is a Cancel redex
Cancellable : TCtx → Term → BCtx → Ty → Set
Cancellable Δ V Θ₂ B₂ =
  Σ Term λ V′ → Σ BCtx λ Θ₁ → Σ Ty λ B₁ →
    (V ≡ V′ ⟪ Θ₁ , B₁ ⟫) × CancelOK Δ Θ₁ Θ₂ B₁ B₂

-- … and it is DECIDABLE (the existentials are read off V's head)
cancellable? : ∀ Δ V Θ₂ B₂ → Dec (Cancellable Δ V Θ₂ B₂)
cancellable? Δ (` x)          Θ₂ B₂ = no λ { (_ , _ , _ , () , _) }
cancellable? Δ ($ n)          Θ₂ B₂ = no λ { (_ , _ , _ , () , _) }
cancellable? Δ (ƛ A ∙ N)      Θ₂ B₂ = no λ { (_ , _ , _ , () , _) }
cancellable? Δ (L · M)        Θ₂ B₂ = no λ { (_ , _ , _ , () , _) }
cancellable? Δ (Λ N)          Θ₂ B₂ = no λ { (_ , _ , _ , () , _) }
cancellable? Δ (L ·[ B , A ]) Θ₂ B₂ = no λ { (_ , _ , _ , () , _) }
cancellable? Δ (M ⟪ Θ₁ , B₁ ⟫) Θ₂ B₂ with cancelOK? Δ Θ₁ Θ₂ B₁ B₂
cancellable? Δ (M ⟪ Θ₁ , B₁ ⟫) Θ₂ B₂ | yes okc =
  yes (M , Θ₁ , B₁ , refl , okc)
cancellable? Δ (M ⟪ Θ₁ , B₁ ⟫) Θ₂ B₂ | no ne =
  no λ { (_ , _ , _ , refl , okc) → ne okc }

------------------------------------------------------------------------
-- §4.1  PLACEMENT B′ — STANDALONE Cancel + a VALUE RESTRICTION.
--
-- A nested wrapper is a value only when it is NOT a Cancel redex, so
-- value-hood becomes KNOWLEDGE-RELATIVE (indexed by Δ) — the TOPLAS
-- p.1074 move, and Decision 6's option (B) in its Cancel form.  The
-- restriction is legitimate because the side condition is decidable
-- (cancellable? above).
------------------------------------------------------------------------

data GValᶜ : TCtx → Term → Set
data Valᶜ  : TCtx → Term → Set

data GValᶜ where
  G-ƛᶜ : ∀ {Δ A N}   → GValᶜ Δ (ƛ A ∙ N)
  G-Λᶜ : ∀ {Δ V} → Valᶜ (abst ∷ Δ) V → GValᶜ Δ (Λ V)

data Valᶜ where
  V-$ᶜ  : ∀ {Δ n} → Valᶜ Δ ($ n)
  V-Gᶜ  : ∀ {Δ V} → GValᶜ Δ V → Valᶜ Δ V
  V-⟪⟫ᶜ : ∀ {Δ V Θ B₀} → Valᶜ (intOf Δ Θ) V
        → ¬ Cancellable Δ V Θ B₀ → Valᶜ Δ (V ⟪ Θ , B₀ ⟫)

infix 2 _⊢_-→ᴮ_
data _⊢_-→ᴮ_ : TCtx → Term → Term → Set where

  TyBetaᴮ : ∀ {Δ V B A} → Valᶜ (abst ∷ Δ) V
      → Δ ⊢ (Λ V) ·[ B , A ] -→ᴮ V ⟪ rvl A ∷ [] , B ⟫

  Betaᴮ : ∀ {Δ A N W} → Valᶜ Δ W
      → Δ ⊢ (ƛ A ∙ N) · W -→ᴮ N [ W ]ᵐ

  TyWrapᴮ : ∀ {Δ V Θ B₀ B A} → Valᶜ (abst ∷ intOf Δ Θ) V
      → Δ ⊢ ((Λ V) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ᴮ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  TyPeelᴮ : ∀ {Δ V Θ Θ₁ B₁ B₀ B A}
      → Valᶜ (intOf (intOf Δ Θ) Θ₁) V
      → Δ ⊢ ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ᴮ (⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ peelB Θ B₀ , ` 0 ])
            ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  Peelᴮ : ∀ {Δ V W Θ B₁ B₂} → Valᶜ (intOf Δ Θ) V → Valᶜ Δ W
      → Δ ⊢ ((V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W)
        -→ᴮ (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫

  -- *** THE NEW RULE ***
  Cancelᴮ : ∀ {Δ V Θ₁ Θ₂ B₁ B₂} → Valᶜ (intOf (intOf Δ Θ₂) Θ₁) V
      → CancelOK Δ Θ₁ Θ₂ B₁ B₂
      → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ᴮ V

  ξ-·-lᴮ : ∀ {Δ L L′ M} → Δ ⊢ L -→ᴮ L′ → Δ ⊢ L · M -→ᴮ L′ · M
  ξ-·-rᴮ : ∀ {Δ V M M′} → Valᶜ Δ V → Δ ⊢ M -→ᴮ M′ → Δ ⊢ V · M -→ᴮ V · M′
  ξ-·[]ᴮ : ∀ {Δ L L′ B A} → Δ ⊢ L -→ᴮ L′
         → Δ ⊢ L ·[ B , A ] -→ᴮ L′ ·[ B , A ]
  ξ-Λᴮ   : ∀ {Δ N N′} → (abst ∷ Δ) ⊢ N -→ᴮ N′ → Δ ⊢ Λ N -→ᴮ Λ N′
  ξ-⟪⟫ᴮ  : ∀ {Δ M M′ Θ B₀} → intOf Δ Θ ⊢ M -→ᴮ M′
         → Δ ⊢ M ⟪ Θ , B₀ ⟫ -→ᴮ M′ ⟪ Θ , B₀ ⟫

------------------------------------------------------------------------
-- §4.2  PLACEMENT A′ — Cancel FOLDED INTO THE ELIMINATION.  The LHS is
-- the APPLICATION (resp. type application), restricted to a
-- VARIABLE-FACED outer boundary — exactly where Peel/TyPeel cannot fire,
-- since their boundary types are ⇒ / ∀-shaped.  The value grammar is the
-- LIVE one, untouched: towers at rest stay values.
------------------------------------------------------------------------

infix 2 _⊢_-→ᴬ_
data _⊢_-→ᴬ_ : TCtx → Term → Term → Set where

  TyBetaᴬ : ∀ {Δ V B A} → Value V
      → Δ ⊢ (Λ V) ·[ B , A ] -→ᴬ V ⟪ rvl A ∷ [] , B ⟫

  Betaᴬ : ∀ {Δ A N W} → Value W → Δ ⊢ (ƛ A ∙ N) · W -→ᴬ N [ W ]ᵐ

  TyWrapᴬ : ∀ {Δ V Θ B₀ B A} → Value V
      → Δ ⊢ ((Λ V) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ᴬ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  TyPeelᴬ : ∀ {Δ V Θ Θ₁ B₁ B₀ B A} → Value V
      → Δ ⊢ ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ᴬ (⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ peelB Θ B₀ , ` 0 ])
            ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  Peelᴬ : ∀ {Δ V W Θ B₁ B₂} → Value V → Value W
      → Δ ⊢ ((V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W)
        -→ᴬ (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫

  -- *** THE NEW RULES ***  variable-faced outer boundary only
  CancelAppᴬ : ∀ {Δ V W Θ₁ Θ₂ Y X} → Value V → Value W
      → CancelOK Δ Θ₁ Θ₂ (` Y) (` X) → X < revs Θ₂
      → Δ ⊢ ((V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫) · W -→ᴬ V · W

  CancelTAppᴬ : ∀ {Δ V Θ₁ Θ₂ Y X B A} → Value V
      → CancelOK Δ Θ₁ Θ₂ (` Y) (` X) → X < revs Θ₂
      → Δ ⊢ ((V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫) ·[ B , A ] -→ᴬ V ·[ B , A ]

  ξ-·-lᴬ : ∀ {Δ L L′ M} → Δ ⊢ L -→ᴬ L′ → Δ ⊢ L · M -→ᴬ L′ · M
  ξ-·-rᴬ : ∀ {Δ V M M′} → Value V → Δ ⊢ M -→ᴬ M′ → Δ ⊢ V · M -→ᴬ V · M′
  ξ-·[]ᴬ : ∀ {Δ L L′ B A} → Δ ⊢ L -→ᴬ L′
         → Δ ⊢ L ·[ B , A ] -→ᴬ L′ ·[ B , A ]
  ξ-Λᴬ   : ∀ {Δ N N′} → (abst ∷ Δ) ⊢ N -→ᴬ N′ → Δ ⊢ Λ N -→ᴬ Λ N′
  ξ-⟪⟫ᴬ  : ∀ {Δ M M′ Θ B₀} → intOf Δ Θ ⊢ M -→ᴬ M′
         → Δ ⊢ M ⟪ Θ , B₀ ⟫ -→ᴬ M′ ⟪ Θ , B₀ ⟫

------------------------------------------------------------------------
-- §4.3  BOTH PLACEMENTS ON §9i's REACHABLE WITNESS: the step exists, and
-- both reach the SAME contractum, which then runs to 7.
------------------------------------------------------------------------

rvᴮ : [] ⊢ rvQ₅ -→ᴮ Vrv · ($ 5)
rvᴮ = ξ-·-lᴮ (Cancelᴮ (V-Gᶜ G-ƛᶜ) rv-CancelOK)

rvᴬ : [] ⊢ rvQ₅ -→ᴬ Vrv · ($ 5)
rvᴬ = CancelAppᴬ (V-G G-ƛ) V-$ rv-CancelOK (s≤s z≤n)

-- and the contractum is well typed at the program's type, by the GENERAL
-- preservation theorem — no instance-specific argument
rv-pres : [] ∣ [] ⊢ Vrv ⦂ (`ℕ ⇒ `ℕ)
rv-pres = cancel-pres {Γₜ = []}
  (env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
       (env (bwf↓ here (≡→≈ refl) (wf-⇒ wf-ℕ wf-ℕ) bwf[])
            (sc-var hereᵒ) (⊢ƛ wf-ℕ ⊢$)))
  rv-CancelOK

rv-finishᴮ : [] ⊢ Vrv · ($ 5) -→ᴮ ($ 7)
rv-finishᴮ = Betaᴮ V-$ᶜ

rv-finishᴬ : [] ⊢ Vrv · ($ 5) -→ᴬ ($ 7)
rv-finishᴬ = Betaᴬ V-$

------------------------------------------------------------------------
-- §4.4  §9j's NON-DETERMINISM EXAMPLE, IN BOTH PLACEMENTS.
--
--   nd = (Vcx ⟪ ↑W:=ℕ , ` 0 ⇒ ℕ ⟫) · ((5 ⟪ ↓X:=ℕ , ` 0 ⟫) ⟪ ↑W:=ℕ , ` 0 ⟫)
--
-- With Merge live, Peel and ξ-·-r+Merge BOTH fire, with distinct
-- contracta.  Below: in B′ the argument tower is NOT a value, so Peel is
-- blocked and ξ-·-r+Cancel is the unique step; in A′ the tower IS a value
-- and does not step at all, so Peel is the unique step.  Both are
-- coverage-complete (every constructor case is listed).
------------------------------------------------------------------------

nd-arg nd : Term
nd-arg = (($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫
nd     = (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) · nd-arg

-- the argument tower IS a Cancel redex
nd-CancelOK : CancelOK Δcx Θcx2 Θcx1 (` 0) (` 0)
nd-CancelOK = refl , refl

nd-cancellable : Cancellable Δcx (($ 5) ⟪ Θcx2 , ` 0 ⟫) Θcx1 (` 0)
nd-cancellable = ($ 5) , Θcx2 , (` 0) , refl , nd-CancelOK

-- (B′)  … hence it is NOT a value, and Peel's `Valᶜ Δ W` premise fails
¬nd-val : ¬ (Valᶜ Δcx nd-arg)
¬nd-val (V-⟪⟫ᶜ _ nc) = nc nd-cancellable

-- (B′)  the unique step: ξ-·-r + Cancel
nd-stepᴮ : Δcx ⊢ nd -→ᴮ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) · ($ 5)
nd-stepᴮ = ξ-·-rᴮ (V-⟪⟫ᶜ (V-Gᶜ G-ƛᶜ) ¬fun-cancel) (Cancelᴮ V-$ᶜ nd-CancelOK)
  where
  ¬fun-cancel : ¬ Cancellable Δcx Vcx Θcx1 (` 0 ⇒ `ℕ)
  ¬fun-cancel (_ , _ , _ , () , _)

nd-onlyᴮ : ∀ {M′} → Δcx ⊢ nd -→ᴮ M′
         → M′ ≡ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) · ($ 5)
nd-onlyᴮ (Peelᴮ _ w)                     = ⊥-elim (¬nd-val w)
nd-onlyᴮ (ξ-·-lᴮ (ξ-⟪⟫ᴮ ()))
nd-onlyᴮ (ξ-·-rᴮ _ (Cancelᴮ _ _))        = refl
nd-onlyᴮ (ξ-·-rᴮ _ (ξ-⟪⟫ᴮ (ξ-⟪⟫ᴮ ())))

-- (A′)  the tower is an ordinary value and does NOT step …
nd-valᴬ : Value nd-arg
nd-valᴬ = V-⟪⟫ (V-⟪⟫ V-$)

nd-arg-stuckᴬ : ∀ {M′} → ¬ (Δcx ⊢ nd-arg -→ᴬ M′)
nd-arg-stuckᴬ (ξ-⟪⟫ᴬ (ξ-⟪⟫ᴬ ()))

-- … so Peel is the unique step
nd-stepᴬ : Δcx ⊢ nd
         -→ᴬ (Vcx · (nd-arg ⟪ dualᴳ Δcx Θcx1 , ` 0 ⟫)) ⟪ Θcx1 , `ℕ ⟫
nd-stepᴬ = Peelᴬ (V-G G-ƛ) nd-valᴬ

nd-onlyᴬ : ∀ {M′} → Δcx ⊢ nd -→ᴬ M′
         → M′ ≡ (Vcx · (nd-arg ⟪ dualᴳ Δcx Θcx1 , ` 0 ⟫)) ⟪ Θcx1 , `ℕ ⟫
nd-onlyᴬ (Peelᴬ _ _)              = refl
nd-onlyᴬ (ξ-·-lᴬ (ξ-⟪⟫ᴬ ()))
nd-onlyᴬ (ξ-·-rᴬ _ st)            = ⊥-elim (nd-arg-stuckᴬ st)

------------------------------------------------------------------------
-- §5.  THE CRUX (Q3): WHICH VARIABLE-FACE NESTINGS TYPE, AND WHAT STEPS
-- THEM.
--
-- CLASSIFICATION (read off (env) twice; the proof is the analysis below,
-- and each family is WITNESSED by a typed term).  A well-typed
--
--     (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫   with   X < revs Θ₂
--
-- forces  substᵗ (ρᵇ Θ₁) (` Y) ≡ ` X , and ρᵇ splits at revs Θ₁:
--
--   (α) Y < revs Θ₁ and Θ₁'s Y-th reveal has rep exactly ` X
--       — the ALIAS-REVEAL family.  Interior face is ` Y (γᵇ-lo), so V is
--         AGAIN a variable-faced wrapper.  NO conceal, so NOTHING cancels.
--   (β) Y ≡ revs Θ₁ + X, and Scoped forces slotAt Θ₁ X ≡ ok, i.e.
--       (β1) Θ₁ CONCEALS X — *** the CANCEL family *** (Jeremy's case);
--       (β2) X ≥ cmax Θ₁ and X is NOT concealed — the TRANSPARENT-LAYER
--            family: Θ₁ passes X through untouched.  Interior face is a
--            variable again, so V is AGAIN a variable-faced wrapper.
--
-- Cancel fires ONLY in (β1), and only when the CONTEXT conjunct also holds
-- (§3.2).  (α) and (β2) are witnessed by well-typed terms below, and NO
-- form of Cancel fires on either.  ***  So the rv parameters do NOT die
-- under Cancel alone.  ***  Both are Merge redexes with MergeOK FULLY
-- DISCHARGED, which is direct evidence for Decision 6's option (A).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §5.1  ADVERSARY (α) — THE ALIAS-REVEAL TOWER.
--
--   Θa = ↑Y:=(` 0)   = rvl (` 0) ∷ []      -- a reveal whose rep IS X
--
-- under Θr = ↑X:=ℕ⇒ℕ, over the bottom conceal Θrᵈ = ↓X:=ℕ⇒ℕ.  The middle
-- boundary REVEALS an alias of X instead of concealing anything, so the
-- outer pair is reveal-over-reveal: there is no inverse and no cancel.
------------------------------------------------------------------------

Θa : BCtx
Θa = rvl (` 0) ∷ []

Ψa : TCtx
Ψa = rvld (` 0) ∷ rvld (`ℕ ⇒ `ℕ) ∷ []

a-int : intOf (intOf [] Θr) Θa ≡ Ψa
a-int = refl

Ma : Term
Ma = ((Vrv ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θa , ` 0 ⟫) ⟪ Θr , ` 0 ⟫

-- *** IT TYPES ***, at Δ = [], and the application types at ℕ
⊢Ma : [] ∣ [] ⊢ Ma · ($ 5) ⦂ `ℕ
⊢Ma =
  ⊢· (env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
        (env (bwf↑ (wf-var here-rvld) bwf[]) (sc-var hereᵒ)
          (env (bwf↓ here (≈unf refl) (wf-⇒ wf-ℕ wf-ℕ) bwf[])
               (sc-var hereᵒ)
               (⊢ƛ wf-ℕ ⊢$))))
     ⊢$

-- the alias entry really is an alias: Ψa's slot 0 is Ψr's ` 0
a-alias : intOf (intOf [] Θr) Θa ≡ rvld (` 0) ∷ Ψr
a-alias = refl

-- *** NO CANCEL FIRES ON THE OUTER PAIR ***
¬a-CancelOK : ¬ (CancelOK [] Θa Θr (` 0) (` 0))
¬a-CancelOK (() , _)

¬a-CancelFace : ∀ {Y X} → ¬ (CancelFace [] Θa Θr Y X)
¬a-CancelFace (_ , () , _)          -- isConc X Θa ≡ false, for every X

-- … nor on the INNER pair, so no ξ-⟪⟫ route either.  *** AND THIS IS THE
-- REFUTATION OF CANDIDATE (ii), the ≈-AGREEMENT SIDE CONDITION. ***  The
-- inner pair is conceal-under-reveal, its CONTEXTS undo each other
-- exactly, and its two faces agree UP TO ≈Δ̄ (ℕ⇒ℕ against the alias ` 0,
-- which unfolds to ℕ⇒ℕ at Ψr) — everything the "Reversal now guarantees
-- it" reading asks for.  They do NOT agree syntactically, and a Cancel
-- that fired here would be UNSOUND: the bare body is a ƛ, and no ƛ has a
-- variable type.  So ≈-agreement is strictly too weak; only the ≡ form
-- (P) is type-preserving.
a-inner-ctx : intOf (intOf Ψr Θa) Θrᵈ ≡ Ψr
a-inner-ctx = refl

a-inner-≈ : substᵗ (γᵇ Θrᵈ) (` 0) ≈Δ̄⟨ Ψr ⟩ substᵗ (ρᵇ Θa) (` 0)
a-inner-≈ = ≈unf refl

¬a-inner : ¬ (CancelOK Ψr Θrᵈ Θa (` 0) (` 0))
¬a-inner (_ , ())

-- and the reason it must not fire: the bare contractum is ill-typed
¬a-inner-pres : ¬ (Ψr ∣ [] ⊢ Vrv ⦂ substᵗ (ρᵇ Θa) (` 0))
¬a-inner-pres ()

-- but MERGE fires on the outer pair, MergeOK fully discharged
a-⊕ : Θa ⊕ Θr ≡ rvl (`ℕ ⇒ `ℕ) ∷ rvl (`ℕ ⇒ `ℕ) ∷ []
a-⊕ = refl

a-MergeOK : MergeOK [] Θa Θr (` 0) (` 0)
a-MergeOK = z≤n
          , bwf↑ (wf-⇒ wf-ℕ wf-ℕ) (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[])
          , sc-var hereᵒ
          , ≼≈rvld (≼≈rvld ≼≈[] (≈unf refl)) (≈unf refl)
          , refl

a-merge : [] ⊢ (Vrv ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θa , ` 0 ⟫ ⟪ Θr , ` 0 ⟫
            -→ (Vrv ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θa ⊕ Θr , mrgB Θa Θr (` 0) ⟫
a-merge = Merge (V-⟪⟫ (V-G G-ƛ)) a-MergeOK

------------------------------------------------------------------------
-- §5.2  ADVERSARY (β2) — THE TRANSPARENT LAYER.
--
--   Θtp = ↑W:=ℕ = rvl `ℕ ∷ []          -- reveals a FRESH slot, and
--                                     -- passes X straight through
--
-- Its boundary type is ` 1 = Θtp's own name for the exterior slot 0 = X.
-- Nothing is concealed, so again there is no inverse pair.  The bottom is
-- a conceal at Θtp's frame index 1.
------------------------------------------------------------------------

Θtp Θbq : BCtx
Θtp = rvl `ℕ ∷ []
Θbq = cnc 1 (`ℕ ⇒ `ℕ) ∷ []

Ψtp : TCtx
Ψtp = rvld `ℕ ∷ rvld (`ℕ ⇒ `ℕ) ∷ []

p-int : intOf (intOf [] Θr) Θtp ≡ Ψtp
p-int = refl

p-bottom-int : intOf Ψtp Θbq ≡ []
p-bottom-int = refl

Mtp : Term
Mtp = ((Vrv ⟪ Θbq , ` 1 ⟫) ⟪ Θtp , ` 1 ⟫) ⟪ Θr , ` 0 ⟫

-- *** IT TYPES ***
⊢Mtp : [] ∣ [] ⊢ Mtp · ($ 5) ⦂ `ℕ
⊢Mtp =
  ⊢· (env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
        (env (bwf↑ wf-ℕ bwf[]) (sc-var (thereᵒ hereᵒ))
          (env (bwf↓ (skip-rvld here) (≡→≈ refl) (wf-⇒ wf-ℕ wf-ℕ) bwf[])
               (sc-var (thereᵒ hereᵒ))
               (⊢ƛ wf-ℕ ⊢$))))
     ⊢$

-- *** NO CANCEL FIRES ***: neither conjunct holds
¬p-CancelOK : ¬ (CancelOK [] Θtp Θr (` 1) (` 0))
¬p-CancelOK (() , _)

¬p-conc : isConc 0 Θtp ≡ false
¬p-conc = refl

-- MERGE fires, MergeOK fully discharged, and the collapse is exactly
-- "delete the transparent layer, keep the outer reveal"
p-⊕ : Θtp ⊕ Θr ≡ rvl `ℕ ∷ rvl (`ℕ ⇒ `ℕ) ∷ []
p-⊕ = refl

p-mrgB : mrgB Θtp Θr (` 1) ≡ ` 1
p-mrgB = refl

p-MergeOK : MergeOK [] Θtp Θr (` 1) (` 0)
p-MergeOK = z≤n
          , bwf↑ wf-ℕ (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[])
          , sc-var (thereᵒ hereᵒ)
          , ≼≈rvld (≼≈rvld ≼≈[] (≈unf refl)) (≈unf refl)
          , refl

p-merge : [] ⊢ Mtp -→ (Vrv ⟪ Θbq , ` 1 ⟫) ⟪ Θtp ⊕ Θr , mrgB Θtp Θr (` 1) ⟫
p-merge = Merge (V-⟪⟫ (V-G G-ƛ)) p-MergeOK

------------------------------------------------------------------------
-- §5.3  THE VERDICT, AS A MACHINE STATEMENT.
--
-- A Cancel-only design cannot discharge RevealVarApp: here is a well
-- typed instance of the parameter's EXACT hypothesis on which no
-- CancelOK/CancelFace holds — for BOTH adversaries.  (The parameter also
-- demands `Value V`, which both satisfy.)
------------------------------------------------------------------------

-- the rv-parameter hypotheses, met by adversary (α)
a-rv-shape : Value (Vrv ⟪ Θrᵈ , ` 0 ⟫) × Value ($ 5)
           × ([] ∣ [] ⊢ (Vrv ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θa , ` 0 ⟫ ⟪ Θr , ` 0 ⟫
                ⦂ (`ℕ ⇒ `ℕ))
           × (0 < revs Θr)
a-rv-shape = V-⟪⟫ (V-G G-ƛ) , V-$
           , env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
               (env (bwf↑ (wf-var here-rvld) bwf[]) (sc-var hereᵒ)
                 (env (bwf↓ here (≈unf refl) (wf-⇒ wf-ℕ wf-ℕ) bwf[])
                      (sc-var hereᵒ) (⊢ƛ wf-ℕ ⊢$)))
           , s≤s z≤n

-- the rv-parameter hypotheses, met by adversary (β2)
p-rv-shape : Value (Vrv ⟪ Θbq , ` 1 ⟫) × Value ($ 5)
           × ([] ∣ [] ⊢ Mtp ⦂ (`ℕ ⇒ `ℕ))
           × (0 < revs Θr)
p-rv-shape = V-⟪⟫ (V-G G-ƛ) , V-$
           , env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
               (env (bwf↑ wf-ℕ bwf[]) (sc-var (thereᵒ hereᵒ))
                 (env (bwf↓ (skip-rvld here) (≡→≈ refl)
                            (wf-⇒ wf-ℕ wf-ℕ) bwf[])
                      (sc-var (thereᵒ hereᵒ)) (⊢ƛ wf-ℕ ⊢$)))
           , s≤s z≤n

-- and in placement A′ neither adversary steps at all: CancelApp needs
-- CancelOK, Peel needs an ⇒-shaped boundary type, Beta a bare ƛ, and
-- ξ-·-r a stepping argument.  (Coverage-complete for (β2); the same
-- analysis applies verbatim to (α).)
p-stuckᴬ : ∀ {M′} → ¬ ([] ⊢ Mtp · ($ 5) -→ᴬ M′)
p-stuckᴬ (CancelAppᴬ _ _ okc _)                    = ¬p-CancelOK okc
p-stuckᴬ (ξ-·-lᴬ (ξ-⟪⟫ᴬ (ξ-⟪⟫ᴬ (ξ-⟪⟫ᴬ ()))))
p-stuckᴬ (ξ-·-rᴬ _ ())

a-stuckᴬ : ∀ {M′} → ¬ ([] ⊢ Ma · ($ 5) -→ᴬ M′)
a-stuckᴬ (CancelAppᴬ _ _ okc _)                    = ¬a-CancelOK okc
a-stuckᴬ (ξ-·-lᴬ (ξ-⟪⟫ᴬ (ξ-⟪⟫ᴬ (ξ-⟪⟫ᴬ ()))))
a-stuckᴬ (ξ-·-rᴬ _ ())

-- … and in placement B′ they do not step either: the standalone Cancel
-- fails on the outer pair AND on the inner one
¬p-inner : ¬ (CancelOK Ψr Θbq Θtp (` 1) (` 1))
¬p-inner (() , _)

p-stuckᴮ : ∀ {M′} → ¬ ([] ⊢ Mtp · ($ 5) -→ᴮ M′)
p-stuckᴮ (ξ-·-lᴮ (Cancelᴮ _ okc))                    = ¬p-CancelOK okc
p-stuckᴮ (ξ-·-lᴮ (ξ-⟪⟫ᴮ (Cancelᴮ _ okc)))            = ¬p-inner okc
p-stuckᴮ (ξ-·-lᴮ (ξ-⟪⟫ᴮ (ξ-⟪⟫ᴮ (ξ-⟪⟫ᴮ ()))))
p-stuckᴮ (ξ-·-rᴮ _ ())

a-stuckᴮ : ∀ {M′} → ¬ ([] ⊢ Ma · ($ 5) -→ᴮ M′)
a-stuckᴮ (ξ-·-lᴮ (Cancelᴮ _ okc))                    = ¬a-CancelOK okc
a-stuckᴮ (ξ-·-lᴮ (ξ-⟪⟫ᴮ (Cancelᴮ _ okc)))            = ¬a-inner okc
a-stuckᴮ (ξ-·-lᴮ (ξ-⟪⟫ᴮ (ξ-⟪⟫ᴮ (ξ-⟪⟫ᴮ ()))))
a-stuckᴮ (ξ-·-rᴮ _ ())

------------------------------------------------------------------------
-- §5.4  *** PROGRESS FAILS FOR THE CANCEL-ONLY CALCULUS. ***  Not merely
-- "the rv parameter is not discharged": both adversaries are CLOSED,
-- WELL TYPED at ℕ, NOT values, and take NO step in EITHER placement.
------------------------------------------------------------------------

p-¬value : ¬ (Value (Mtp · ($ 5)))
p-¬value (V-G ())

a-¬value : ¬ (Value (Ma · ($ 5)))
a-¬value (V-G ())

progress-failsᴬ :
    (([] ∣ [] ⊢ Mtp · ($ 5) ⦂ `ℕ) × ¬ (Value (Mtp · ($ 5)))
       × (∀ {M′} → ¬ ([] ⊢ Mtp · ($ 5) -→ᴬ M′)))
  × (([] ∣ [] ⊢ Ma · ($ 5) ⦂ `ℕ) × ¬ (Value (Ma · ($ 5)))
       × (∀ {M′} → ¬ ([] ⊢ Ma · ($ 5) -→ᴬ M′)))
progress-failsᴬ = (⊢Mtp , p-¬value , p-stuckᴬ)
                , (⊢Ma  , a-¬value , a-stuckᴬ)

progress-failsᴮ :
    (([] ∣ [] ⊢ Mtp · ($ 5) ⦂ `ℕ) × (∀ {M′} → ¬ ([] ⊢ Mtp · ($ 5) -→ᴮ M′)))
  × (([] ∣ [] ⊢ Ma · ($ 5) ⦂ `ℕ) × (∀ {M′} → ¬ ([] ⊢ Ma · ($ 5) -→ᴮ M′)))
progress-failsᴮ = (⊢Mtp , p-stuckᴮ) , (⊢Ma , a-stuckᴮ)

------------------------------------------------------------------------
-- §5.5  IS THE (β2) ADVERSARY REACHABLE?  YES — in ONE TyBeta step, by
-- the LIVE relation, from a well-typed term.  The transparent layer is
-- exactly what TyBeta mints when a ∀-body returns an OUTER type variable:
--
--   Ψr ⊢ (Λ (V ⟪ ↓X:=ℕ⇒ℕ , ` 1 ⟫)) ·[ ` 1 , ℕ ]
--        --TyBeta-->  (V ⟪ ↓X:=ℕ⇒ℕ , ` 1 ⟫) ⟪ ↑W:=ℕ , ` 1 ⟫
--
-- (the ∀-body ` 1 names Ψr's own X, not the Λ-binder), all of it inside
-- the ambient X-boundary Θr.  So the family is NOT an artefact of writing
-- boundaries by hand.
--
-- (α) is a different matter: the naive TyBeta route to it does NOT work —
-- the pre-step body would need a CONCEAL licensed at the Λ-binder's
-- `abst` slot, and bwf↓ needs knowledge there.  Its reachability is left
-- OPEN; ProgressDef's parameters quantify over well-typed terms, not
-- reachable ones, so (α) is an adversary either way.
------------------------------------------------------------------------

p-src : Term
p-src = (Λ (Vrv ⟪ Θbq , ` 1 ⟫)) ·[ ` 1 , `ℕ ]

⊢p-src : Ψr ∣ [] ⊢ p-src ⦂ ` 0
⊢p-src =
  ⊢·[] (⊢Λ (env (bwf↓ (skip-abst here) (≡→≈ refl)
                      (wf-⇒ wf-ℕ wf-ℕ) bwf[])
                (sc-var (thereᵒ hereᵒ))
                (⊢ƛ wf-ℕ ⊢$)))
       wf-ℕ

p-birth : Ψr ⊢ p-src -→ (Vrv ⟪ Θbq , ` 1 ⟫) ⟪ Θtp , ` 1 ⟫
p-birth = TyBeta (V-⟪⟫ (V-G G-ƛ))

⊢p-whole : [] ∣ [] ⊢ (p-src ⟪ Θr , ` 0 ⟫) · ($ 5) ⦂ `ℕ
⊢p-whole =
  ⊢· (env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ) ⊢p-src) ⊢$

p-reaches : [] ⊢ (p-src ⟪ Θr , ` 0 ⟫) · ($ 5) -→ (Mtp · ($ 5))
p-reaches = ξ-·-l (ξ-⟪⟫ (TyBeta (V-⟪⟫ (V-G G-ƛ))))

------------------------------------------------------------------------
-- §6.  WHAT DIES (Q4) — the honest inventory.
--
-- §5 does not merely fail to discharge the rv parameters — it REFUTES
-- progress for the Cancel-only calculus (progress-failsᴬ /
-- progress-failsᴮ: two closed, well-typed, non-value, non-stepping
-- terms, one of them reachable in a single live TyBeta step).  So the
-- flatten machinery is NOT deletable: ⊕ / mrgB / MergeOK / Merge remain
-- the only rules that step the (α) and (β2) families (a-MergeOK,
-- p-MergeOK, e-MergeOK — all three FULLY DISCHARGED, which is positive
-- evidence for Decision 6's option (A)), and Drop∅ is still wanted
-- because Merge can mint an empty boundary (rv-⊕-empty).
--
-- Under option (A) — MergeApp / MergeTApp folded into the elimination —
-- Cancel is REDUNDANT: it is exactly the Θ₁ ⊕ Θ₂ ≡ [] instance
-- (merge+drop-general), and its virtue is only that its side condition
-- is two equations instead of MergeOK's five components.
--
-- WHAT *WOULD* DIE if a Cancel-only design were adopted together with a
-- TYPING STRENGTHENING that rules (α) and (β2) out at birth:
--   strong/BReduction.agda  : Merge, Drop∅, _⊕_, mapL, mapR, mrgB, mrg₁,
--                             mrg₂, mrgΨ, R⊕, C⊕, upF, up⊕, inSub,
--                             MergeOK, ⊕-γ and the whole ⊕ metatheory
--                             block (≈ lines 257–420 plus the proofs at
--                             the foot of the file);
--   strong/BReduction.agda  : the ≼≈ ordering, IF nothing else uses it
--                             (⊢retag≈ does, so it stays);
--   notes/InstallGauntlet   : §9a–§9f and §9j's val-cancel/val-steps/
--                             nd-* would freeze to notes/old (they are
--                             statements ABOUT Merge); §9i survives,
--                             restated with Cancel;
--   strong/ProgressDef.agda : RevealVarApp / RevealVarTApp — ONLY under
--                             that strengthening; as things stand §5's
--                             adversaries keep them alive.
------------------------------------------------------------------------

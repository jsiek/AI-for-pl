module strong.notes.DualLicenseProbe where

-- ADVERSARIAL PROBE of the LICENSING PREMISE for the DUAL's
-- CONCEAL-OF-A-REVEAL (notes/DECISIONS.md, candidate (b); the STAR-CONCEAL
-- PROBE VERDICT block and its counterexample E★′).
--
-- THE QUESTION.  At E★′'s Wrap the dual must conceal the reveal Z whose
-- knowledge ("Z is Y", Y Λ-bound) is inexpressible in an interior that drops
-- Y and un-unfoldable (unfoldᵉ is the identity at an abstract variable).  The
-- REP-KEEPING dual ↓Z:=Y is semantically right there — StarConcealProbe's
-- face-int-E★′ / face-ext-E★′ / sc-live-E★′ — and its ONLY defect is bwf↓'s
-- knowledge LOOKUP.  cnc⋆ (rep-less) trades that boundary failure for a scope
-- failure (¬Scoped-⋆-E★′), because the boundary type NAMES Z.  So the design
-- needs a licence for a REP-KEEPING conceal.  Constraint: the contractum must
-- be typable by the ORDINARY typing (env + ONE boundary judgement), so the
-- licence must live in the boundary judgement, be grounded (minted by the
-- relation, no companion predicate) and be local to the boundary plus its
-- exterior.
--
-- THE CANDIDATES, each installed as a LOCAL variant of the boundary
-- judgement and run through the same gauntlet (E★′, E★, Pn, bad, bad₂,
-- near-bad/far-bad, dual-of-dual, one renaming transport):
--
--   (b1) §2  READ-BACK IDENTITY   ↓Z:=A licensed when A, read back out
--            through the boundary, IS the slot: outRead Θᵈ A ≡ ` Z.
--   (b2) §3  FACES-AS-PREMISE     the knowledge lookup replaced by the two
--            face laws for the pair, stated per entry.
--   (b3) §4  EXTERIOR-READ ENTRY  a third TyEntry `Z:=x A` — "revealed, rep
--            readable ONE LEVEL OUT" — minted by ⟦·⟧ where neither the raw
--            reading nor the unfolding is expressible, and consumed ONLY by a
--            new bwf↓ clause with syntactic rep equality.  §4.6 REFUTES the
--            naive form and §4.7 installs the SOUND form (the rep must be
--            abstract in the interior).
--   (b4) §5  a dual-only judgement parameterised by the CO-boundary: ruled
--            out structurally, with a checked witness.
--
-- METHOD.  The live files are UNTOUCHED and StarConcealProbe's apparatus is
-- REUSED verbatim: BEntry★ (which already carries cnc⋆), every
-- face/scope/interior function over it, its E★ and E★′ terms, faces and
-- refutations.  Only what a candidate CHANGES is redefined: the boundary
-- judgement (§2/§3/§4) and, for (b3), the interior's entry algebra (a third
-- entry form forces a local TCtx³).  The typing judgement is written ONCE, in
-- §1, parameterised by the context algebra and the boundary judgement, and
-- instantiated per candidate — so every candidate meets character-for-
-- character the same (env).

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties using (_≟_; m+n≮m; m+n∸m≡n)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (¬_; Dec; yes; no; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)
open import strong.Types
open import strong.Context hiding (Δ; Γ; A; B; C; X; Y; Z; x; E)
open import strong.Boundary
open import strong.BReduction
  using (entAt; repOf; copyRep; dualᴳ; swapᵇ; intRen; renᴮ;
         liftⁿ; deepRen; restrictRen;
         Value; GVal; G-ƛ; G-Λ; V-$; V-G; V-⟪⟫;
         _⊢_-→_; Wrap; TyWrap; TyBeta; ξ-·-l; ξ-Λ; ξ-⟪⟫)
open import strong.notes.UnfoldProbe using (unfSub; unfoldᵉ; rvld≢abst)
open import strong.notes.UpToProbe
  using (_≈Δ̄[_]_; ≈unf; ≈-refl; ≈-sym; ≈-trans; ≡→≈; ≈-⇒;
         cnc-needs-knowledge; Γnb; Θnb)
open import strong.notes.StarConcealProbe

private
  variable
    X j n : ℕ

------------------------------------------------------------------------
-- §1.  THE SHARED TYPING JUDGEMENT.
--
-- One (env) rule, four worlds.  A world is (C, fg, ab, it, bw): the context
-- algebra — carrier, forgetful map to a plain TCtx (what type
-- well-formedness and the scope stack read), the Λ-extension, the interior
-- map — plus the boundary judgement.  EVERY rule but (env) is
-- character-for-character today's rule, and (env)'s three premises are
-- today's with intOf ↦ it and ⊢ᵇ ↦ bw.  The candidates therefore differ ONLY
-- in the boundary judgement (and, for (b3), in the interior's entries).
------------------------------------------------------------------------

module Gen (C : Set) (fg : C → TCtx) (ab : C → C)
           (it : C → BCtx★ → C) (bw : C → C → BCtx★ → Set) where

  data Tg : C → Ctx → Term★ → Ty → Set where
    g`   : ∀ {Δ₁ Γ₁ x₁ A₁} → Γ₁ ∋ x₁ ⦂ A₁ → Tg Δ₁ Γ₁ (`★ x₁) A₁
    g$   : ∀ {Δ₁ Γ₁ n₁} → Tg Δ₁ Γ₁ ($★ n₁) `ℕ
    gƛ   : ∀ {Δ₁ Γ₁ A₁ B₁ N₁} → fg Δ₁ ⊢ A₁ → Tg Δ₁ (A₁ ∷ Γ₁) N₁ B₁
         → Tg Δ₁ Γ₁ (ƛ★ A₁ ∙ N₁) (A₁ ⇒ B₁)
    g·   : ∀ {Δ₁ Γ₁ A₁ B₁ L₁ M₁} → Tg Δ₁ Γ₁ L₁ (A₁ ⇒ B₁) → Tg Δ₁ Γ₁ M₁ A₁
         → Tg Δ₁ Γ₁ (L₁ ·★ M₁) B₁
    gΛ   : ∀ {Δ₁ Γ₁ C₁ N₁} → Tg (ab Δ₁) (⤊ Γ₁) N₁ C₁
         → Tg Δ₁ Γ₁ (Λ★ N₁) (`∀ C₁)
    g·[] : ∀ {Δ₁ Γ₁ A₁ B₁ L₁} → Tg Δ₁ Γ₁ L₁ (`∀ B₁) → fg Δ₁ ⊢ A₁
         → Tg Δ₁ Γ₁ (L₁ ·★[ B₁ , A₁ ]) (B₁ [ A₁ ]ᵗ)
    genv : ∀ {Δ₁ Γ₁ Ξ₁ B₁ M₁} → bw Δ₁ (it Δ₁ Ξ₁) Ξ₁
         → Scoped (baseS★ Ξ₁ (fg Δ₁)) B₁
         → Tg (it Δ₁ Ξ₁) [] M₁ (substᵗ (γᵇ★ Ξ₁) B₁)
           ---------------------------------------------------
         → Tg Δ₁ Γ₁ (M₁ ⟪ Ξ₁ , B₁ ⟫★) (substᵗ (ρᵇ★ Ξ₁) B₁)

------------------------------------------------------------------------
-- Shared small lemmas.
------------------------------------------------------------------------

sover-diag : ∀ X₁ A₁ (σ : Substᵗ) → sover X₁ A₁ σ X₁ ≡ A₁
sover-diag X₁ A₁ σ with X₁ ≟ X₁
sover-diag X₁ A₁ σ | yes _  = refl
sover-diag X₁ A₁ σ | no  ¬p = ⊥-elim (¬p refl)

prepId-hi : ∀ r (σ : Substᵗ) X₁ → prepId r σ (r + X₁) ≡ σ X₁
prepId-hi r σ X₁ with (r + X₁) <? r
prepId-hi r σ X₁ | yes lt = ⊥-elim (m+n≮m r X₁ lt)
prepId-hi r σ X₁ | no  _  = cong σ (m+n∸m≡n r X₁)

isAbst : TyEntry → Bool
isAbst abst      = true
isAbst (rvld A₁) = false

isAbst-abst : ∀ (E₁ : TyEntry) → isAbst E₁ ≡ true → E₁ ≡ abst
isAbst-abst abst      e = refl
isAbst-abst (rvld A₁) ()

-- absOnly Ψ d A : every FREE variable of A (d binders passed) has an
-- ABSTRACT entry in Ψ — "A asserts no knowledge in Ψ".
absOnly : TCtx → ℕ → Ty → Bool
absOnly Ψ₁ d (` X₁)   = ⌊ X₁ <? d ⌋ ∨ isAbst (entAt Ψ₁ (X₁ ∸ d))
absOnly Ψ₁ d `ℕ       = true
absOnly Ψ₁ d `𝔹       = true
absOnly Ψ₁ d (A₁ ⇒ B₁) = absOnly Ψ₁ d A₁ ∧ absOnly Ψ₁ d B₁
absOnly Ψ₁ d (`∀ A₁)  = absOnly Ψ₁ (suc d) A₁

absOnly-var : ∀ (Ψ₁ : TCtx) s → absOnly Ψ₁ 0 (` s) ≡ true
            → entAt Ψ₁ s ≡ abst
absOnly-var Ψ₁ s e = isAbst-abst (entAt Ψ₁ s) e

------------------------------------------------------------------------
-- Names shared by every section.  E★ and E★′ live at Γ★ = [Y (Λ-bound) ,
-- X:=ℕ] with the boundary Θ★ˢ = ↑Z:=Y , ↓X:=ℕ; the REP-KEEPING dual is
-- StarConcealProbe's dualᵛ (embedded), the REP-LESS one its dual⋆.
------------------------------------------------------------------------

dualᵛ★ : BCtx★
dualᵛ★ = emb dualᵛ

_ : dualᵛ★ ≡ rvl⋆★ ∷ rvl★ `ℕ ∷ cnc★ 0 (` 0) ∷ []
_ = refl

_ : dual⋆ ≡ rvl⋆★ ∷ rvl★ `ℕ ∷ cnc⋆ 0 ∷ []
_ = refl

-- the interior that must license the dual's conceal: Z ALONE, abstract
_ : intOf★ Γ★ Θ★ˢ ≡ abst ∷ []
_ = refl

-- Pn's data (StarConcealProbe §5.1, case 2) and its dual
ΘPnᵈ : BCtx★
ΘPnᵈ = rvl★ `ℕ ∷ rvl★ `ℕ ∷ cnc★ 0 (` 0) ∷ []

_ : dualᴳ★ ΓPn ΘPn ≡ ΘPnᵈ
_ = refl

_ : intOf★ ΓPn ΘPn ≡ rvld `ℕ ∷ []          -- the (a″) hybrid fired
_ = refl

-- bad / bad₂ / near-bad / far-bad, in BEntry★ form
Θbad Θbad₂ Θnb★ Θfar : BCtx★
Θbad  = cnc★ 0 `ℕ ∷ []                     -- ↓X:=ℕ  under  ↑X:=∀Z.Z→Z
Θbad₂ = cnc★ 0 (` 0) ∷ rvl★ `ℕ ∷ []        -- Boundary's Θb
Θnb★  = cnc★ 0 `ℕ ∷ []                     -- UpToProbe's Θnb, over Γnb
Θfar  = cnc★ 0 ∀ZZ ∷ []                    -- far-bad, over Γnb

Γbad Γb★ : TCtx
Γbad = rvld ∀ZZ ∷ []
Γb★  = rvld (` 0) ∷ rvld ∀ZZ ∷ []          -- Boundary's Γb

badᵗ : Term★
badᵗ = (($★ 7) ⟪ Θbad , ` 0 ⟫★) ⟪ rvl★ ∀ZZ ∷ [] , ` 0 ⟫★

_ : badᵗ ≡ embT bad
_ = refl

wf-∀ZZ : ∀ {Δ₁ : TCtx} → Δ₁ ⊢ ∀ZZ
wf-∀ZZ = wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst))

------------------------------------------------------------------------
-- §2.  CANDIDATE (b1) — READ-BACK IDENTITY.
--
-- PRECISE FORM.  A conceal ↓Z:=A is licensed when A, read back out through
-- the WHOLE boundary, is Z's own exterior face — and a conceal leaves the
-- exterior face of its own slot alone, so that face is ` Z:
--
--     RevId Ξ Z A  =  outRead★ Ξ A ≡ ` Z
--
-- ("concealing-then-revealing is the identity on the slot": the Reversal
-- premise with the exterior's KNOWLEDGE replaced by the SLOT.)  It is an
-- ADDITIONAL clause: today's knowledge-licensed conceal stays, and so does
-- cnc⋆.  The variant that compares against `upRep Z A₀` for some knowledge A₀
-- IS today's premise, so the identity form is the only new content.
------------------------------------------------------------------------

RevId : BCtx★ → ℕ → Ty → Set
RevId Ξ₁ X₁ A₁ = outRead★ Ξ₁ A₁ ≡ ` X₁

data Bwf1 (Γ Ψ : TCtx) (Ξ : BCtx★) : BCtx★ → Set where
  bwf1[] : Bwf1 Γ Ψ Ξ []
  bwf1↑  : ∀ {A₁ Ζ} → Γ ⊢ A₁ → Bwf1 Γ Ψ Ξ Ζ → Bwf1 Γ Ψ Ξ (rvl★ A₁ ∷ Ζ)
  bwf1⋆  : ∀ {Ζ} → Bwf1 Γ Ψ Ξ Ζ → Bwf1 Γ Ψ Ξ (rvl⋆★ ∷ Ζ)
  bwf1↓  : ∀ {X₁ A₁ A₀ Ζ}
         → Γ ∋ X₁ := A₀ → Reversal★ Γ Ξ X₁ A₁ A₀ → Ψ ⊢ A₁
         → Bwf1 Γ Ψ Ξ Ζ → Bwf1 Γ Ψ Ξ (cnc★ X₁ A₁ ∷ Ζ)
  bwf1↓i : ∀ {X₁ A₁ Ζ}                            -- *** (b1)'s clause ***
         → Γ ∋tv X₁ → RevId Ξ X₁ A₁ → Ψ ⊢ A₁
         → Bwf1 Γ Ψ Ξ Ζ → Bwf1 Γ Ψ Ξ (cnc★ X₁ A₁ ∷ Ζ)
  bwf1⋆↓ : ∀ {X₁ Ζ} → Γ ∋tv X₁ → Bwf1 Γ Ψ Ξ Ζ → Bwf1 Γ Ψ Ξ (cnc⋆ X₁ ∷ Ζ)

module G1 = Gen TCtx (λ Γ₁ → Γ₁) (abst ∷_) intOf★
                (λ Γ₁ Ψ₁ Ξ₁ → Bwf1 Γ₁ Ψ₁ Ξ₁ Ξ₁)

infix 3 _∣_⊢1_⦂_
_∣_⊢1_⦂_ : TCtx → Ctx → Term★ → Ty → Set
Δ₁ ∣ Γ₁ ⊢1 M₁ ⦂ A₁ = G1.Tg Δ₁ Γ₁ M₁ A₁

------------------------------------------------------------------------
-- §2.1  E★′ — REFUTED, exactly as predicted: A = Y is the dual's OWN
-- ⋆-REVEAL slot, whose external face is the DUMMY `ℕ, so the read-back is
-- garbage and can never be the slot.
------------------------------------------------------------------------

dummy-read-back : outRead★ dualᵛ★ (` 0) ≡ `ℕ
dummy-read-back = refl

¬RevId-E★′ : ¬ RevId dualᵛ★ 0 (` 0)
¬RevId-E★′ ()

-- the contractum types in NEITHER way: the ordinary clause is the old
-- failure (Z's interior entry is abstract), the new one is the dummy.
¬⊢1-T4′ : ¬ (Γ★ ∣ [] ⊢1 embT T4′ ⦂ (` 0 ⇒ `ℕ))
¬⊢1-T4′ (G1.genv _ _ (G1.gƛ _ (G1.g·
  (G1.genv (bwf1⋆ (bwf1↑ _ (bwf1↓ () _ _ _))) _ _) _)))
¬⊢1-T4′ (G1.genv _ _ (G1.gƛ _ (G1.g·
  (G1.genv (bwf1⋆ (bwf1↑ _ (bwf1↓i _ () _ _))) _ _) _)))

-- and with the REP-LESS dual instead, (b1) inherits StarConcealProbe's scope
-- failure unchanged (¬Scoped-⋆-E★′ is a statement about baseS★ alone).
¬⊢1-T4′⋆ : ¬ (Γ★ ∣ [] ⊢1 T4′⋆ ⦂ (` 0 ⇒ `ℕ))
¬⊢1-T4′⋆ (G1.genv _ _ (G1.gƛ _ (G1.g· (G1.genv _ sc _) _))) =
  ¬Scoped-⋆-E★′ sc

------------------------------------------------------------------------
-- §2.2  THE GARBAGE (b1) DOES admit: a conceal of an ABSTRACT variable.
-- Take Γg = [X Λ-bound] and Ξg = ↑Z:=X , ↓X:=Z — the reveal makes the
-- read-back of Z be X on the nose, so the identity holds with NO knowledge
-- premise at all.  Bwf★ refuses that boundary; Bwf1 accepts it.  The
-- admission is not (yet) unsound — the paired reveal's interior entry comes
-- out ABSTRACT, so the sealed value would have to inhabit an abstract type —
-- but it re-opens the dependence on no-abstract-value that cnc⋆ had closed
-- for DualCnc (StarConcealProbe §5).
------------------------------------------------------------------------

Γg : TCtx
Γg = abst ∷ []

Ξg : BCtx★
Ξg = rvl★ (` 0) ∷ cnc★ 0 (` 0) ∷ []

RevId-Ξg : RevId Ξg 0 (` 0)
RevId-Ξg = refl

¬know-Γg : ∀ {A₁} → ¬ (Γg ∋ 0 := A₁)
¬know-Γg ()

_ : intOf★ Γg Ξg ≡ abst ∷ []
_ = refl

_ : substᵗ (γᵇ★ Ξg) (` 1) ≡ ` 0            -- X's internal face is Z …
_ = refl

_ : entAt (intOf★ Γg Ξg) 0 ≡ abst          -- … and Z is abstract
_ = refl

bwf1-garbage : Bwf1 Γg (intOf★ Γg Ξg) Ξg Ξg
bwf1-garbage = bwf1↑ (wf-var here-abst)
                     (bwf1↓i here-abst RevId-Ξg (wf-var here-abst) bwf1[])

¬bwf★-garbage : ¬ (Γg ∣ intOf★ Γg Ξg ⊢ᵇ★ Ξg)
¬bwf★-garbage (bwf★↑ _ (bwf★↓ () _ _ _))

------------------------------------------------------------------------
-- §2.3  The rest of the gauntlet for (b1).  E★ passes only by falling back
-- to cnc⋆ (b1's clause is silent there — same dummy), Pn by the ORDINARY
-- clause under the (a″) hybrid, and every soundness test is untouched
-- because RevId cannot hold at any of them.
------------------------------------------------------------------------

bwf1-Θ★ : Bwf1 Γ★ (intOf★ Γ★ Θ★ˢ) Θ★ˢ Θ★ˢ
bwf1-Θ★ = bwf1↑ (wf-var here-abst)
                (bwf1↓ (skip-abst here) ≈-refl wf-ℕ bwf1[])

bwf1-dual⋆ : Bwf1 (intOf★ Γ★ Θ★ˢ) (intOf★ (intOf★ Γ★ Θ★ˢ) dual⋆) dual⋆ dual⋆
bwf1-dual⋆ = bwf1⋆ (bwf1↑ wf-ℕ (bwf1⋆↓ here-abst bwf1[]))

⊢1-T4★ : Γ★ ∣ [] ⊢1 T4★ ⦂ `ℕ                     -- E★ ✓ (via cnc⋆)
⊢1-T4★ = G1.genv bwf1-Θ★ sc-ℕ (G1.genv bwf1-dual⋆ sc-ℕ G1.g$)

bwf1-Pn : Bwf1 (intOf★ ΓPn ΘPn)                    -- Pn ✓ (ordinary clause)
               (intOf★ (intOf★ ΓPn ΘPn) ΘPnᵈ) ΘPnᵈ ΘPnᵈ
bwf1-Pn = bwf1↑ wf-ℕ (bwf1↑ wf-ℕ
                       (bwf1↓ here ≈-refl (wf-var here-rvld) bwf1[]))

bwf1-dd : Bwf1 Γ★ (intOf★ Γ★ dd) dd dd            -- dual of dual ✓
bwf1-dd = bwf1⋆ (bwf1⋆↓ here-abst
                  (bwf1↓ (skip-abst here) ≈-refl wf-ℕ bwf1[]))

¬Rev★-bad : ¬ (Reversal★ Γbad Θbad 0 `ℕ ∀ZZ)
¬Rev★-bad (≈unf ())

¬RevId-bad : ¬ RevId Θbad 0 `ℕ
¬RevId-bad ()

¬⊢1-bad : ¬ ([] ∣ [] ⊢1 badᵗ ⦂ ∀ZZ)               -- bad stays refuted
¬⊢1-bad (G1.genv _ _ (G1.genv (bwf1↓ here rev _ _) _ _)) = ¬Rev★-bad rev
¬⊢1-bad (G1.genv _ _ (G1.genv (bwf1↓i _ () _ _) _ _))

¬Rev★-bad₂ : ¬ (Reversal★ Γb★ Θbad₂ 0 (` 0) (` 0))  -- bad₂ stays refuted
¬Rev★-bad₂ (≈unf ())

¬RevId-bad₂ : ¬ RevId Θbad₂ 0 (` 0)
¬RevId-bad₂ ()

Rev★-near : Reversal★ Γnb Θnb★ 0 `ℕ (` 0)          -- near-bad ADMITTED
Rev★-near = ≈unf refl

⊢1-near-bad : Γnb ∣ [] ⊢1 ($★ 3) ⟪ Θnb★ , ` 0 ⟫★ ⦂ ` 0
⊢1-near-bad =
  G1.genv (bwf1↓ here Rev★-near wf-ℕ bwf1[]) (sc-var hereᵒ) G1.g$

¬Rev★-far : ¬ (Reversal★ Γnb Θfar 0 ∀ZZ (` 0))     -- far-bad REJECTED
¬Rev★-far (≈unf ())

¬RevId-far : ¬ RevId Θfar 0 ∀ZZ
¬RevId-far ()

-- RENAMING.  (b1)'s premise is an equation between two things the boundary
-- ITSELF computes, so it transports: renaming Ξg by suc moves both sides.
_ : renᴮ★ suc (intRen★ suc Ξg) Ξg ≡ rvl★ (` 1) ∷ cnc★ 1 (` 0) ∷ []
_ = refl

RevId-Ξg-ren : RevId (renᴮ★ suc (intRen★ suc Ξg) Ξg) 1 (` 0)
RevId-Ξg-ren = refl

------------------------------------------------------------------------
-- §3.  CANDIDATE (b2) — FACES AS THE PREMISE.
--
-- IS IT STATEABLE PER ENTRY?  The two laws preservation consumes are
-- WHOLE-BOUNDARY statements about the pair, and E★′ exhibits them:
--
--   face-int-E★′ : substᵗ (γᵇ dualᵛ) (` 2 ⇒ ℕ) ≡ (` 0 ⇒ ℕ)
--   face-ext-E★′ : substᵗ (ρᵇ dualᵛ) (` 2 ⇒ ℕ) ≡ substᵗ (γᵇ Θ★) (` 0 ⇒ ℕ)
--
-- The internal law is about the SEALED VALUE's type, not about any one
-- entry; the external law mentions γᵇ Θ★ — the CO-BOUNDARY — so as a premise
-- of the dual's own well-formedness it is exactly candidate (b4) (§5).  What
-- IS stateable per entry is the pair of laws restricted to the slot: the
-- conceal's γ image is its rep, and its ρ image is the slot.  That is what
-- (b2) becomes — and it is a DEFINITIONAL IDENTITY.
------------------------------------------------------------------------

Faces : BCtx★ → ℕ → Ty → Set
Faces Ξ₁ X₁ A₁ = (substᵗ (γᵇ★ Ξ₁) (` (revs★ Ξ₁ + X₁)) ≡ A₁)
               × (substᵗ (ρᵇ★ Ξ₁) (` (revs★ Ξ₁ + X₁)) ≡ ` X₁)

faces-ρ : ∀ Ξ₁ X₁ → ρᵇ★ Ξ₁ (revs★ Ξ₁ + X₁) ≡ ` X₁
faces-ρ []                 X₁ = refl
faces-ρ (rvl★ A₁ ∷ Ξ₁)     X₁ = faces-ρ Ξ₁ X₁
faces-ρ (rvl⋆★ ∷ Ξ₁)       X₁ = faces-ρ Ξ₁ X₁
faces-ρ (cnc★ Y₁ A₁ ∷ Ξ₁)  X₁ = faces-ρ Ξ₁ X₁
faces-ρ (cnc⋆ Y₁ ∷ Ξ₁)     X₁ = faces-ρ Ξ₁ X₁

-- THEOREM (vacuity).  At the entry the rule is checking, both laws hold BY
-- COMPUTATION — for every X and every rep A whatever.
faces-head : ∀ X₁ A₁ Ζ → Faces (cnc★ X₁ A₁ ∷ Ζ) X₁ A₁
faces-head X₁ A₁ Ζ =
    trans (prepId-hi (revs★ Ζ) (γcnc★ (revs★ Ζ)
                                      (suc X₁ ⊔ cmax★ Ζ)
                                      (cnc★ X₁ A₁ ∷ Ζ)) X₁)
          (sover-diag X₁ A₁ (γcnc★ (revs★ Ζ) (suc X₁ ⊔ cmax★ Ζ) Ζ))
  , faces-ρ (cnc★ X₁ A₁ ∷ Ζ) X₁

data Bwf2 (Γ Ψ : TCtx) (Ξ : BCtx★) : BCtx★ → Set where
  bwf2[] : Bwf2 Γ Ψ Ξ []
  bwf2↑  : ∀ {A₁ Ζ} → Γ ⊢ A₁ → Bwf2 Γ Ψ Ξ Ζ → Bwf2 Γ Ψ Ξ (rvl★ A₁ ∷ Ζ)
  bwf2⋆  : ∀ {Ζ} → Bwf2 Γ Ψ Ξ Ζ → Bwf2 Γ Ψ Ξ (rvl⋆★ ∷ Ζ)
  bwf2↓  : ∀ {X₁ A₁ Ζ}                            -- *** (b2)'s clause ***
         → Γ ∋tv X₁ → Faces Ξ X₁ A₁ → Ψ ⊢ A₁
         → Bwf2 Γ Ψ Ξ Ζ → Bwf2 Γ Ψ Ξ (cnc★ X₁ A₁ ∷ Ζ)
  bwf2⋆↓ : ∀ {X₁ Ζ} → Γ ∋tv X₁ → Bwf2 Γ Ψ Ξ Ζ → Bwf2 Γ Ψ Ξ (cnc⋆ X₁ ∷ Ζ)

module G2 = Gen TCtx (λ Γ₁ → Γ₁) (abst ∷_) intOf★
                (λ Γ₁ Ψ₁ Ξ₁ → Bwf2 Γ₁ Ψ₁ Ξ₁ Ξ₁)

infix 3 _∣_⊢2_⦂_
_∣_⊢2_⦂_ : TCtx → Ctx → Term★ → Ty → Set
Δ₁ ∣ Γ₁ ⊢2 M₁ ⦂ A₁ = G2.Tg Δ₁ Γ₁ M₁ A₁

-- *** THE REFUTATION ***  bad SLIPS THROUGH: its conceal's faces are the
-- identity too, so (b2) types the very term the reversal premise was
-- introduced to kill.
faces-bad : Faces Θbad 0 `ℕ
faces-bad = faces-head 0 `ℕ []

⊢2-bad : [] ∣ [] ⊢2 badᵗ ⦂ ∀ZZ
⊢2-bad = G2.genv (bwf2↑ wf-∀ZZ bwf2[]) (sc-var hereᵒ)
           (G2.genv (bwf2↓ here-rvld faces-bad wf-ℕ bwf2[])
                    (sc-var hereᵒ) G2.g$)

faces-bad₂ : Faces Θbad₂ 0 (` 0)                   -- bad₂ slips through too
faces-bad₂ = faces-head 0 (` 0) (rvl★ `ℕ ∷ [])

¬Rev★-bad₂-again : ¬ (Reversal★ Γb★ Θbad₂ 0 (` 0) (` 0))
¬Rev★-bad₂-again (≈unf ())

-- far-bad slips through as well, so (b2) does not even distinguish the
-- near/far pair: both are licensed, and the whole knowledge column is gone.
faces-far : Faces Θfar 0 ∀ZZ
faces-far = faces-head 0 ∀ZZ []

⊢2-near-bad : Γnb ∣ [] ⊢2 ($★ 3) ⟪ Θnb★ , ` 0 ⟫★ ⦂ ` 0
⊢2-near-bad =
  G2.genv (bwf2↓ here-rvld faces-bad wf-ℕ bwf2[]) (sc-var hereᵒ) G2.g$

-- The rest of the gauntlet is met, but VACUOUSLY — which is the point.
faces-Θ★ : Faces Θ★ˢ 1 `ℕ
faces-Θ★ = refl , refl

bwf2-Θ★ : Bwf2 Γ★ (intOf★ Γ★ Θ★ˢ) Θ★ˢ Θ★ˢ
bwf2-Θ★ = bwf2↑ (wf-var here-abst)
                (bwf2↓ (skip-abst here-rvld) faces-Θ★ wf-ℕ bwf2[])

bwf2-dual⋆ : Bwf2 (intOf★ Γ★ Θ★ˢ) (intOf★ (intOf★ Γ★ Θ★ˢ) dual⋆) dual⋆ dual⋆
bwf2-dual⋆ = bwf2⋆ (bwf2↑ wf-ℕ (bwf2⋆↓ here-abst bwf2[]))

⊢2-T4★ : Γ★ ∣ [] ⊢2 T4★ ⦂ `ℕ                       -- E★ ✓ (via cnc⋆)
⊢2-T4★ = G2.genv bwf2-Θ★ sc-ℕ (G2.genv bwf2-dual⋆ sc-ℕ G2.g$)

bwf2-Pn : Bwf2 (intOf★ ΓPn ΘPn)                     -- Pn ✓ (vacuously)
               (intOf★ (intOf★ ΓPn ΘPn) ΘPnᵈ) ΘPnᵈ ΘPnᵈ
bwf2-Pn = bwf2↑ wf-ℕ (bwf2↑ wf-ℕ
                       (bwf2↓ here-rvld (refl , refl)
                              (wf-var here-rvld) bwf2[]))

bwf2-dd : Bwf2 Γ★ (intOf★ Γ★ dd) dd dd              -- dual of dual ✓
bwf2-dd = bwf2⋆ (bwf2⋆↓ here-abst
                  (bwf2↓ (skip-abst here-rvld) (refl , refl) wf-ℕ bwf2[]))

-- E★′ under (b2): with the REP-KEEPING dual the faces hold (that is the
-- whole content of face-int-E★′ / face-ext-E★′), so (b2) DOES type E★′'s
-- contractum — it just types everything else as well.
faces-E★′ : Faces dualᵛ★ 0 (` 0)
faces-E★′ = refl , refl

bwf2-dualᵛ : Bwf2 (intOf★ Γ★ Θ★ˢ)
                  (intOf★ (intOf★ Γ★ Θ★ˢ) dualᵛ★) dualᵛ★ dualᵛ★
bwf2-dualᵛ = bwf2⋆ (bwf2↑ wf-ℕ
                     (bwf2↓ here-abst faces-E★′ (wf-var here-abst) bwf2[]))

⊢2-T4′ : Γ★ ∣ [] ⊢2 embT T4′ ⦂ (` 0 ⇒ `ℕ)
⊢2-T4′ = G2.genv bwf2-Θ★ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
           (G2.gƛ (wf-var here-abst)
             (G2.g· (G2.genv bwf2-dualᵛ sc-live-E★′
                             (G2.gƛ (wf-var here-abst) G2.g$))
                    (G2.g` here)))

-- RENAMING is free for (b2) — a definitional identity is recomputed at the
-- renamed boundary — which is the other half of the diagnosis: a premise
-- that transports for free carries no information.
_ : renᴮ★ suc (intRen★ suc Θbad) Θbad ≡ cnc★ 1 `ℕ ∷ []
_ = refl

faces-bad-ren : Faces (renᴮ★ suc (intRen★ suc Θbad) Θbad) 1 `ℕ
faces-bad-ren = faces-head 1 `ℕ []

------------------------------------------------------------------------
-- §4.  CANDIDATE (b3) — THE EXTERIOR-READ KNOWLEDGE ENTRY  Z:=x A.
--
-- A THIRD TyEntry.  ⟦·⟧ today falls back to `abst` when a reveal's rep is
-- neither expressible raw nor unfoldable.  (b3) splits that fallback by
-- whether there IS a rep: a REP-CARRYING reveal contributes
--
--     Z :=x A        "revealed, with rep A readable ONE LEVEL OUT"
--
-- storing the rep AS THE REVEAL STORED IT — i.e. read in the boundary's
-- EXTERIOR Γ, which is exactly one level out from the interior the entry
-- lives in — while rvl⋆ still contributes `abst` (there is no rep).  The new
-- bwf↓ clause licenses a conceal ↓Z:=A by  Γ ∋ Z :=x A  with SYNTACTIC rep
-- equality: the homes align, because the dual's interior is an index-aligned
-- rebuild of that same exterior, and cncOfRevs copies the reveal's rep
-- VERBATIM.
--
-- A third entry form cannot be simulated inside TyEntry, so §4 carries a
-- local TCtx³ and a forgetful map fgt³ (x-entries ↦ abst) through which every
-- OTHER consumer — type well-formedness, ∋tv, ∋:=, the scope stack, unfoldᵉ,
-- entᴳ★ — reads the context unchanged.  That is the whole point of the
-- design: an x-entry is consumed ONLY by the new clause.
------------------------------------------------------------------------

data TyEntry³ : Set where
  abst³  : TyEntry³
  rvld³  : Ty → TyEntry³
  xrvld³ : Ty → TyEntry³            -- *** the third entry ***

TCtx³ : Set
TCtx³ = List TyEntry³

fgt³ : TCtx³ → TCtx
fgt³ []                = []
fgt³ (abst³ ∷ Γ₁)      = abst ∷ fgt³ Γ₁
fgt³ (rvld³ A₁ ∷ Γ₁)   = rvld A₁ ∷ fgt³ Γ₁
fgt³ (xrvld³ A₁ ∷ Γ₁)  = abst ∷ fgt³ Γ₁

infix 4 _∋_:=x_
data _∋_:=x_ : TCtx³ → ℕ → Ty → Set where
  herex : ∀ {Γ₁ A₁} → (xrvld³ A₁ ∷ Γ₁) ∋ 0 :=x A₁
  skipx : ∀ {Γ₁ E₁ X₁ A₁} → Γ₁ ∋ X₁ :=x A₁ → (E₁ ∷ Γ₁) ∋ suc X₁ :=x A₁

dropN³ : ℕ → TCtx³ → TCtx³
dropN³ zero    Γ₁       = Γ₁
dropN³ (suc k) []       = []
dropN³ (suc k) (E₁ ∷ Γ₁) = dropN³ k Γ₁

-- raw reading, else the ambient unfolding (the (a″) hybrid), else the
-- EXTERIOR-READ entry.  `abst` survives only for rvl⋆ (revEnts³ below).
hyb³ : Ty → TyEntry → TyEntry → TyEntry³
hyb³ A₁ (rvld B₁) (rvld C₁) = rvld³ B₁
hyb³ A₁ (rvld B₁) abst      = rvld³ B₁
hyb³ A₁ abst      (rvld B₁) = rvld³ B₁
hyb³ A₁ abst      abst      = xrvld³ A₁

⟦_∣_⟧³ : TCtx³ → BCtx★ → ℕ → Ty → TyEntry³
⟦ Γ₁ ∣ Ξ₁ ⟧³ j₁ A₁ =
  hyb³ A₁ (⟦ Ξ₁ ⟧ᵉ★ j₁ A₁) (⟦ Ξ₁ ⟧ᵉ★ j₁ (unfoldᵉ (fgt³ Γ₁) A₁))

-- the same WITHOUT the (a″) unfold retry — question (iii) of §4.5
⟦_∣_⟧³ⁿ : TCtx³ → BCtx★ → ℕ → Ty → TyEntry³
⟦ Γ₁ ∣ Ξ₁ ⟧³ⁿ j₁ A₁ = hyb³ A₁ (⟦ Ξ₁ ⟧ᵉ★ j₁ A₁) abst

revEntsW : (ℕ → Ty → TyEntry³) → ℕ → BCtx★ → TCtx³
revEntsW f j₁ []               = []
revEntsW f j₁ (rvl★ A₁ ∷ Ζ)    = f j₁ A₁ ∷ revEntsW f (suc j₁) Ζ
revEntsW f j₁ (rvl⋆★ ∷ Ζ)      = abst³ ∷ revEntsW f (suc j₁) Ζ
revEntsW f j₁ (cnc★ X₁ A₁ ∷ Ζ) = revEntsW f j₁ Ζ
revEntsW f j₁ (cnc⋆ X₁ ∷ Ζ)    = revEntsW f j₁ Ζ

intOf³ intOf³ⁿ : TCtx³ → BCtx★ → TCtx³
intOf³  Γ₁ Ξ₁ = revEntsW (⟦ Γ₁ ∣ Ξ₁ ⟧³)  0 Ξ₁ ++ dropN³ (cmax★ Ξ₁) Γ₁
intOf³ⁿ Γ₁ Ξ₁ = revEntsW (⟦ Γ₁ ∣ Ξ₁ ⟧³ⁿ) 0 Ξ₁ ++ dropN³ (cmax★ Ξ₁) Γ₁

-- THE DUAL SIMPLIFIES.  StarConcealProbe's cncOfRevs★ had to CONSULT the
-- interior entry to choose between cnc★ and cnc⋆; under (b3) every
-- rep-carrying reveal is licensable (rvld ⇒ ordinary clause, xrvld ⇒ new
-- clause), so the conceal block is entry-INDEPENDENT again — today's live
-- cncOfRevs with its one bug fixed (rvl⋆ ↦ cnc⋆, not the invented `cnc j ℕ`).
cncOfRevs³ : ℕ → BCtx★ → BCtx★
cncOfRevs³ j₁ []               = []
cncOfRevs³ j₁ (rvl★ A₁ ∷ Ζ)    = cnc★ j₁ A₁ ∷ cncOfRevs³ (suc j₁) Ζ
cncOfRevs³ j₁ (rvl⋆★ ∷ Ζ)      = cnc⋆ j₁ ∷ cncOfRevs³ (suc j₁) Ζ
cncOfRevs³ j₁ (cnc★ X₁ A₁ ∷ Ζ) = cncOfRevs³ j₁ Ζ
cncOfRevs³ j₁ (cnc⋆ X₁ ∷ Ζ)    = cncOfRevs³ j₁ Ζ

dualᴳ³ : TCtx³ → BCtx★ → BCtx★
dualᴳ³ Γ₁ Ξ₁ = rvlsᴳ★ (cmax★ Ξ₁) 0 (fgt³ Γ₁) Ξ₁ ++ cncOfRevs³ 0 Ξ₁

Reversal³ : TCtx³ → BCtx★ → ℕ → Ty → Ty → Set
Reversal³ Γ₁ Ξ₁ X₁ A₁ A₀ = outRead★ Ξ₁ A₁ ≈Δ̄[ fgt³ Γ₁ ] upRep X₁ A₀

data Bwf³ (XL : TCtx³ → TCtx³ → ℕ → Ty → Set)
          (Γ Ψ : TCtx³) (Ξ : BCtx★) : BCtx★ → Set where
  bwf³[] : Bwf³ XL Γ Ψ Ξ []
  bwf³↑  : ∀ {A₁ Ζ} → fgt³ Γ ⊢ A₁
         → Bwf³ XL Γ Ψ Ξ Ζ → Bwf³ XL Γ Ψ Ξ (rvl★ A₁ ∷ Ζ)
  bwf³⋆  : ∀ {Ζ} → Bwf³ XL Γ Ψ Ξ Ζ → Bwf³ XL Γ Ψ Ξ (rvl⋆★ ∷ Ζ)
  bwf³↓  : ∀ {X₁ A₁ A₀ Ζ}
         → fgt³ Γ ∋ X₁ := A₀ → Reversal³ Γ Ξ X₁ A₁ A₀ → fgt³ Ψ ⊢ A₁
         → Bwf³ XL Γ Ψ Ξ Ζ → Bwf³ XL Γ Ψ Ξ (cnc★ X₁ A₁ ∷ Ζ)
  bwf³↓x : ∀ {X₁ A₁ Ζ}                            -- *** (b3)'s clause ***
         → XL Γ Ψ X₁ A₁ → fgt³ Ψ ⊢ A₁
         → Bwf³ XL Γ Ψ Ξ Ζ → Bwf³ XL Γ Ψ Ξ (cnc★ X₁ A₁ ∷ Ζ)
  bwf³⋆↓ : ∀ {X₁ Ζ} → fgt³ Γ ∋tv X₁
         → Bwf³ XL Γ Ψ Ξ Ζ → Bwf³ XL Γ Ψ Ξ (cnc⋆ X₁ ∷ Ζ)

-- the NAIVE licence (the mandate's form) and the SOUND one (§4.6/§4.7)
XLicN XLicS : TCtx³ → TCtx³ → ℕ → Ty → Set
XLicN Γ₁ Ψ₁ X₁ A₁ = Γ₁ ∋ X₁ :=x A₁
XLicS Γ₁ Ψ₁ X₁ A₁ = (Γ₁ ∋ X₁ :=x A₁) × (absOnly (fgt³ Ψ₁) 0 A₁ ≡ true)

module G3n = Gen TCtx³ fgt³ (abst³ ∷_) intOf³
                 (λ Γ₁ Ψ₁ Ξ₁ → Bwf³ XLicN Γ₁ Ψ₁ Ξ₁ Ξ₁)
module G3s = Gen TCtx³ fgt³ (abst³ ∷_) intOf³
                 (λ Γ₁ Ψ₁ Ξ₁ → Bwf³ XLicS Γ₁ Ψ₁ Ξ₁ Ξ₁)

infix 3 _∣_⊢3n_⦂_
_∣_⊢3n_⦂_ : TCtx³ → Ctx → Term★ → Ty → Set
Δ₁ ∣ Γ₁ ⊢3n M₁ ⦂ A₁ = G3n.Tg Δ₁ Γ₁ M₁ A₁

infix 3 _∣_⊢3s_⦂_
_∣_⊢3s_⦂_ : TCtx³ → Ctx → Term★ → Ty → Set
Δ₁ ∣ Γ₁ ⊢3s M₁ ⦂ A₁ = G3s.Tg Δ₁ Γ₁ M₁ A₁

------------------------------------------------------------------------
-- §4.1  E★′ END TO END.  The reduction rule is UNCHANGED: the live Wrap
-- already mints the rep-keeping dual, and dualᴳ³ agrees with it here — so
-- StarConcealProbe's step34′ IS this step, and only the contractum's typing
-- was missing.
------------------------------------------------------------------------

Γ★³ : TCtx³
Γ★³ = abst³ ∷ rvld³ `ℕ ∷ []

_ : fgt³ Γ★³ ≡ Γ★
_ = refl

Γz³ : TCtx³                        -- Θ★'s interior: Z alone, x-revealed as Y
Γz³ = xrvld³ (` 0) ∷ []

_ : intOf³ Γ★³ Θ★ˢ ≡ Γz³
_ = refl

_ : dualᴳ³ Γ★³ Θ★ˢ ≡ dualᵛ★         -- the live, rep-keeping dual
_ = refl

_ : dualᴳ Γ★ Θ★ ≡ dualᵛ             -- … which is what the live rule mints
_ = refl

_ : intOf³ Γz³ dualᵛ★ ≡ Γ★³         -- exact rebuild
_ = refl

-- the faces, reused (StarConcealProbe's face-int-E★′ / face-ext-E★′)
_ : substᵗ (γᵇ★ dualᵛ★) (` 2 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
_ = refl

_ : substᵗ (ρᵇ★ dualᵛ★) (` 2 ⇒ `ℕ) ≡ substᵗ (γᵇ★ Θ★ˢ) (` 0 ⇒ `ℕ)
_ = refl

xlic-E★′ : Γz³ ∋ 0 :=x (` 0)
xlic-E★′ = herex

abs-E★′ : absOnly (fgt³ Γ★³) 0 (` 0) ≡ true
abs-E★′ = refl

bwf3-dual : Bwf³ XLicS Γz³ (intOf³ Γz³ dualᵛ★) dualᵛ★ dualᵛ★
bwf3-dual =
  bwf³⋆ (bwf³↑ wf-ℕ
          (bwf³↓x (xlic-E★′ , abs-E★′) (wf-var here-abst) bwf³[]))

bwf3-Θ★ : Bwf³ XLicS Γ★³ (intOf³ Γ★³ Θ★ˢ) Θ★ˢ Θ★ˢ
bwf3-Θ★ = bwf³↑ (wf-var here-abst)
                (bwf³↓ (skip-abst here) ≈-refl wf-ℕ bwf³[])

⊢3s-T4′ : Γ★³ ∣ [] ⊢3s embT T4′ ⦂ (` 0 ⇒ `ℕ)       -- *** E★′ PASSES ***
⊢3s-T4′ = G3s.genv bwf3-Θ★ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
            (G3s.gƛ (wf-var here-abst)
              (G3s.g· (G3s.genv bwf3-dual sc-live-E★′
                                (G3s.gƛ (wf-var here-abst) G3s.g$))
                      (G3s.g` here)))

------------------------------------------------------------------------
-- §4.2  E★ — the same licence, so cnc⋆ is NOT needed for a rep-carrying
-- reveal.  It IS still needed for a rvl⋆ dual, and E★'s own dual contains
-- ↑Y:⋆ — so §4.3's dual of dual mints one (StarConcealProbe §4.3's finding
-- stands: today's `cnc j ℕ` for a rvl⋆ is unlicensable).
------------------------------------------------------------------------

⊢3s-T4 : Γ★³ ∣ [] ⊢3s embT T4 ⦂ `ℕ
⊢3s-T4 = G3s.genv bwf3-Θ★ sc-ℕ (G3s.genv bwf3-dual sc-ℕ G3s.g$)

------------------------------------------------------------------------
-- §4.3  DUAL OF DUAL.  The ⋆-reveal duals to cnc⋆, the copied reveal to an
-- ordinary conceal, and the reveal of the (concealed) Z slot re-reveals its
-- rep — the round trip is exact.
------------------------------------------------------------------------

dd³ : BCtx★
dd³ = rvl★ (` 0) ∷ cnc⋆ 0 ∷ cnc★ 1 `ℕ ∷ []

_ : dualᴳ³ Γz³ dualᵛ★ ≡ dd³
_ = refl

_ : intOf³ Γ★³ dd³ ≡ Γz³
_ = refl

bwf3-dd : Bwf³ XLicS Γ★³ (intOf³ Γ★³ dd³) dd³ dd³
bwf3-dd = bwf³↑ (wf-var here-abst)
                (bwf³⋆↓ here-abst
                  (bwf³↓ (skip-abst here) ≈-refl wf-ℕ bwf³[]))

------------------------------------------------------------------------
-- §4.4  Pn — by the ORDINARY clause: the (a″) hybrid resolves Z:=Y through
-- Γn's knowledge to Z:=ℕ, so no x-entry is minted at all.
------------------------------------------------------------------------

ΓPn³ : TCtx³
ΓPn³ = rvld³ `ℕ ∷ rvld³ `ℕ ∷ []

_ : fgt³ ΓPn³ ≡ ΓPn
_ = refl

_ : intOf³ ΓPn³ ΘPn ≡ rvld³ `ℕ ∷ []
_ = refl

_ : dualᴳ³ ΓPn³ ΘPn ≡ ΘPnᵈ
_ = refl

_ : intOf³ (intOf³ ΓPn³ ΘPn) ΘPnᵈ ≡ ΓPn³
_ = refl

bwf3-Pn : Bwf³ XLicS (intOf³ ΓPn³ ΘPn)
                (intOf³ (intOf³ ΓPn³ ΘPn) ΘPnᵈ) ΘPnᵈ ΘPnᵈ
bwf3-Pn = bwf³↑ wf-ℕ (bwf³↑ wf-ℕ
                       (bwf³↓ here ≈-refl (wf-var here-rvld) bwf³[]))

------------------------------------------------------------------------
-- §4.5  QUESTION (iii): does (b3) SUBSUME the (a″) hybrid?  Give Pn an
-- x-entry instead of the unfolded ℕ and ask whether the dual's conceal still
-- licenses.  ANSWER: only under the NAIVE licence — which §4.6 refutes.  The
-- SOUND licence rejects it, because Y's entry in the rebuild is KNOWLEDGE,
-- not an abstract slot.  So the unfold retry CANNOT be dropped.
------------------------------------------------------------------------

_ : intOf³ⁿ ΓPn³ ΘPn ≡ xrvld³ (` 0) ∷ []
_ = refl

xlic-Pnⁿ : intOf³ⁿ ΓPn³ ΘPn ∋ 0 :=x (` 0)
xlic-Pnⁿ = herex

_ : intOf³ⁿ (intOf³ⁿ ΓPn³ ΘPn) ΘPnᵈ ≡ ΓPn³
_ = refl

¬abs-Pnⁿ : ¬ (absOnly (fgt³ ΓPn³) 0 (` 0) ≡ true)
¬abs-Pnⁿ ()

------------------------------------------------------------------------
-- §4.6  SOUNDNESS: THE NAIVE LICENCE IS REFUTED.
--
-- The x-entry says "Z's rep is A, read ONE LEVEL OUT".  The clause compares
-- A with a conceal's rep, which lives over the CONSUMING boundary's INTERIOR.
-- Those two homes coincide only when that interior is the index-aligned
-- rebuild — i.e. when the boundary really is the dual — and nothing in the
-- entry pins that down.  The adversary keeps the legitimately minted entry
-- Z:=x Y of Γz³ (the very context in which E★′'s SEALED BODY is typed, so
-- this term is plantable in a real program) and supplies a DIFFERENT
-- boundary: ↑W:=ℕ , ↓Z:=W.  The rep ` 0 now means W, and W is ℕ.
------------------------------------------------------------------------

Ξadv : BCtx★
Ξadv = rvl★ `ℕ ∷ cnc★ 0 (` 0) ∷ []

_ : intOf³ Γz³ Ξadv ≡ rvld³ `ℕ ∷ []       -- the rep's slot is KNOWLEDGE here
_ = refl

_ : substᵗ (γᵇ★ Ξadv) (` 1) ≡ ` 0         -- internal: the value is a W = ℕ
_ = refl

_ : substᵗ (ρᵇ★ Ξadv) (` 1) ≡ ` 0         -- external: it is exported as Z
_ = refl

_ : entAt (fgt³ Γ★³) 0 ≡ abst             -- … and Z is the Λ-BOUND Y
_ = refl

advᵗ : Term★
advᵗ = (($★ 7) ⟪ cnc★ 0 `ℕ ∷ [] , ` 0 ⟫★) ⟪ Ξadv , ` 1 ⟫★

-- *** THE COUNTEREXAMPLE ***  7 : ℕ acquires the abstract type Z.
⊢3n-adv : Γz³ ∣ [] ⊢3n advᵗ ⦂ ` 0
⊢3n-adv = G3n.genv (bwf³↑ wf-ℕ (bwf³↓x herex (wf-var here-rvld) bwf³[]))
                   (sc-var (thereᵒ hereᵒ))
                   (G3n.genv (bwf³↓ here ≈-refl wf-ℕ bwf³[])
                             (sc-var hereᵒ) G3n.g$)

------------------------------------------------------------------------
-- §4.7  THE SOUND FORM.  Add to the licence: the rep must ASSERT NOTHING in
-- the interior (absOnly) — every slot it names is abstract there.  Then an
-- x-licensed conceal is cnc⋆'s "claims nothing" WITH a rep for the faces,
-- which is exactly what E★′ needs and exactly what cnc⋆ could not give
-- (¬Scoped-⋆-E★′).  §4.1–§4.4 already used the sound form; here is what it
-- rules out.
------------------------------------------------------------------------

¬⊢3s-adv : ¬ (Γz³ ∣ [] ⊢3s advᵗ ⦂ ` 0)
¬⊢3s-adv (G3s.genv (bwf³↑ _ (bwf³↓ () _ _ _)) _ _)
¬⊢3s-adv (G3s.genv (bwf³↑ _ (bwf³↓x (herex , ()) _ _)) _ _)

-- The residual freedom is an ALIAS BETWEEN TWO ABSTRACT SLOTS: the adversary
-- may still pair Z with a FRESH abstract reveal (↑V:⋆ , ↓Z:=V).  That is
-- sound in the same sense cnc⋆ is: neither side carries knowledge, so nothing
-- is transported either way — the interior has NO knowledge about the rep's
-- slot, and the exterior none about Z.
Ξalias : BCtx★
Ξalias = rvl⋆★ ∷ cnc★ 0 (` 0) ∷ []

_ : intOf³ Γz³ Ξalias ≡ abst³ ∷ []
_ = refl

abs-alias : absOnly (fgt³ (intOf³ Γz³ Ξalias)) 0 (` 0) ≡ true
abs-alias = refl

no-know-alias : ∀ {A₁} → ¬ (fgt³ (intOf³ Γz³ Ξalias) ∋ 0 := A₁)
no-know-alias ()

no-know-Z : ∀ {A₁} → ¬ (fgt³ Γz³ ∋ 0 := A₁)
no-know-Z ()

-- machine-checked, so the supervisor can see exactly what survives: a
-- (V→ℕ)-value exported as (Z→ℕ), V a fresh abstract reveal, Z x-revealed as
-- the Λ-bound Y.  Both slots abstract, no knowledge either way — the same
-- licence cnc⋆ already grants, now with a rep so the type can be
-- TRANSLATED, which is the entire point of E★′.
aliasᵗ : Term★
aliasᵗ = (ƛ★ (` 0) ∙ ($★ 5)) ⟪ Ξalias , ` 1 ⇒ `ℕ ⟫★

⊢3s-alias : Γz³ ∣ [] ⊢3s aliasᵗ ⦂ (` 0 ⇒ `ℕ)
⊢3s-alias =
  G3s.genv (bwf³⋆ (bwf³↓x (herex , abs-alias) (wf-var here-abst) bwf³[]))
           (sc-⇒ (sc-var (thereᵒ hereᵒ)) sc-ℕ)
           (G3s.gƛ (wf-var here-abst) G3s.g$)

------------------------------------------------------------------------
-- §4.8  GROUNDING (question (v)).  x-entries are minted ONLY by ⟦·⟧³, from a
-- reveal's own rep (which bwf³↑ has certified well formed in the exterior),
-- and the judgement extends a context in exactly two ways: `ab` (= abst³ ∷_)
-- and `it` (= intOf³).  So no program conjures one, and at every soundness
-- test the exterior carries ORDINARY knowledge, where the clause cannot fire.
------------------------------------------------------------------------

Γbad³ Γb³ Γnb³ : TCtx³
Γbad³ = rvld³ ∀ZZ ∷ []
Γb³   = rvld³ (` 0) ∷ rvld³ ∀ZZ ∷ []
Γnb³  = rvld³ (` 0) ∷ rvld³ `ℕ ∷ []

_ : intOf³ [] (rvl★ ∀ZZ ∷ []) ≡ Γbad³
_ = refl

¬xlic-bad : ∀ {A₁} → ¬ (Γbad³ ∋ 0 :=x A₁)
¬xlic-bad ()

¬xlic-bad₂ : ∀ {A₁} → ¬ (Γb³ ∋ 0 :=x A₁)
¬xlic-bad₂ ()

¬xlic-nb : ∀ {A₁} → ¬ (Γnb³ ∋ 0 :=x A₁)
¬xlic-nb ()

¬Rev³-bad : ¬ (Reversal³ Γbad³ Θbad 0 `ℕ ∀ZZ)
¬Rev³-bad (≈unf ())

¬⊢3s-bad : ¬ ([] ∣ [] ⊢3s badᵗ ⦂ ∀ZZ)              -- bad stays refuted
¬⊢3s-bad (G3s.genv _ _ (G3s.genv (bwf³↓ here rev _ _) _ _)) = ¬Rev³-bad rev
¬⊢3s-bad (G3s.genv _ _ (G3s.genv (bwf³↓x (() , _) _ _) _ _))

¬⊢3n-bad : ¬ ([] ∣ [] ⊢3n badᵗ ⦂ ∀ZZ)              -- … in both forms
¬⊢3n-bad (G3n.genv _ _ (G3n.genv (bwf³↓ here rev _ _) _ _)) = ¬Rev³-bad rev
¬⊢3n-bad (G3n.genv _ _ (G3n.genv (bwf³↓x () _ _) _ _))

¬Rev³-bad₂ : ¬ (Reversal³ Γb³ Θbad₂ 0 (` 0) (` 0))  -- bad₂ stays refuted
¬Rev³-bad₂ (≈unf ())

Rev³-near : Reversal³ Γnb³ Θnb★ 0 `ℕ (` 0)          -- near-bad ADMITTED
Rev³-near = ≈unf refl

⊢3s-near-bad : Γnb³ ∣ [] ⊢3s ($★ 3) ⟪ Θnb★ , ` 0 ⟫★ ⦂ ` 0
⊢3s-near-bad =
  G3s.genv (bwf³↓ here Rev³-near wf-ℕ bwf³[]) (sc-var hereᵒ) G3s.g$

¬Rev³-far : ¬ (Reversal³ Γnb³ Θfar 0 ∀ZZ (` 0))     -- far-bad REJECTED
¬Rev³-far (≈unf ())

------------------------------------------------------------------------
-- §4.9  RENAMING (question (iv)) — THE ONE HARD COST.
--
-- An x-entry's rep lives over the EXTERIOR-OF-THE-EXTERIOR, so ⟦·⟧³ mints it
-- renamed by ρ; a conceal's rep lives over the boundary's INTERIOR, so renᴮ★
-- renames it by intRen★ ρ′ Ξ′.  Weaken Γ★ by a fresh Λ-bound V (ρ = suc):
-- the renaming ⊢renameᵀ hands the sealed body is ρ₁ = intRen★ suc Θ★ˢ, which
-- is the IDENTITY on the dual's frame — so the term's conceal rep is FROZEN
-- at ` 0 while the context's x-rep moves to ` 1.  Syntactic equality does not
-- survive ⊢renameᵀ.
------------------------------------------------------------------------

Δw : TCtx³
Δw = abst³ ∷ Γ★³

ρ₁ : ℕ → ℕ
ρ₁ = intRen★ suc Θ★ˢ

Θ★w : BCtx★
Θ★w = renᴮ★ suc ρ₁ Θ★ˢ

_ : Θ★w ≡ rvl★ (` 1) ∷ cnc★ 2 `ℕ ∷ []
_ = refl

_ : intOf³ Δw Θ★w ≡ xrvld³ (` 1) ∷ []       -- the x-rep moved by ρ = suc …
_ = refl

_ : renᴮ★ ρ₁ (intRen★ ρ₁ dualᵛ★) dualᵛ★ ≡ dualᵛ★   -- … the term's did not
_ = refl

¬xlic-ren : ¬ (intOf³ Δw Θ★w ∋ 0 :=x (` 0))
¬xlic-ren ()

-- The transport the clause WOULD need, stated: the rep renames by ρ, not by
-- the ordinary `restrictRen Y (intRen★ ρ Ξ)` of ∋:=-int.  It holds …
XRen : (ℕ → ℕ) → BCtx★ → TCtx³ → TCtx³ → Set
XRen ρ Ξ₁ Δ₁ Δ₂ = ∀ {Y₁ A₁} → intOf³ Δ₁ Ξ₁ ∋ Y₁ :=x A₁
  → intOf³ Δ₂ (renᴮ★ ρ (intRen★ ρ Ξ₁) Ξ₁) ∋ intRen★ ρ Ξ₁ Y₁
      :=x renameᵗ ρ A₁

xren-E★′ : XRen suc Θ★ˢ Γ★³ Δw
xren-E★′ herex     = herex
xren-E★′ (skipx ())

-- … and is USELESS on its own, because the consumer moved by a different
-- renaming.  What DOES work is recomputing the dual from the renamed data:
-- then both reps are ` 1 and the interior rebuilds Δw exactly.
_ : dualᴳ³ Δw Θ★w ≡ rvl⋆★ ∷ rvl⋆★ ∷ rvl★ `ℕ ∷ cnc★ 0 (` 1) ∷ []
_ = refl

_ : intOf³ (intOf³ Δw Θ★w) (dualᴳ³ Δw Θ★w) ≡ Δw
_ = refl

xlic-ren-ok : intOf³ Δw Θ★w ∋ 0 :=x (` 1)
xlic-ren-ok = herex

abs-ren-ok : absOnly (fgt³ Δw) 0 (` 1) ≡ true
abs-ren-ok = refl

-- So renaming does NOT commute with the dual on x-conceal reps: renaming the
-- dual freezes the rep, dualising the renamed data moves it.
¬dual-ren-comm : ¬ (renᴮ★ ρ₁ (intRen★ ρ₁ dualᵛ★) dualᵛ★ ≡ dualᴳ³ Δw Θ★w)
¬dual-ren-comm ()

-- DOES (b3) DODGE ¬hk-int?  Yes, in the sense the mandate asks: an x-entry is
-- never read as a TELESCOPE entry, so ⊢renameᵀ's ordinary knowledge
-- hypothesis is vacuous at an x-slot (fgt³ sends it to abst) …
_ : fgt³ Γz³ ≡ abst ∷ []
_ = refl

-- … but the SAME shape of mismatch reappears one level up, at the new
-- clause: ¬xlic-ren is ¬hk-int's phenomenon for an exterior-read rep.

------------------------------------------------------------------------
-- §4.10  QUESTION (vi): no-abstract-value / the canonical form.
--
-- The canonical form at a variable type is unchanged in shape — a wrapper
-- chain (val-var-wrapper³) — but a conceal is now licensed by := OR :=x, so
-- the vacuity argument gains one case.  It is discharged: an x-licensed
-- conceal's rep is absOnly in the interior, so if it is a variable its
-- interior entry is ABSTRACT and the induction (on the strictly smaller
-- value) applies; the := case dies by cnc-needs-knowledge as before.  Values
-- of type ` Z for an x-revealed Z therefore still do not exist — what DOES
-- now exist is a value at a type MENTIONING Z (E★′'s W′ : Z→ℕ), which is
-- precisely the redex StarConcealProbe could rule out neither way, and
-- vacuity is silent there (vacuity-silent′).
------------------------------------------------------------------------

NoAbstractValue³ : Set
NoAbstractValue³ = ∀ {Δ₁ : TCtx³} {V₁ : Term★} {X₁}
  → Value★ V₁ → Δ₁ ∣ [] ⊢3s V₁ ⦂ ` X₁ → entAt (fgt³ Δ₁) X₁ ≡ abst → ⊥

val-var-wrapper³ : ∀ {Δ₁ Γ₁ V₁ X₁} → Value★ V₁ → Δ₁ ∣ Γ₁ ⊢3s V₁ ⦂ ` X₁
  → Σ Term★ λ V' → Σ BCtx★ λ Ξ' → Σ Ty λ B' → V₁ ≡ V' ⟪ Ξ' , B' ⟫★
val-var-wrapper³ V★-$            ()
val-var-wrapper³ (V★-G G★-ƛ)     ()
val-var-wrapper³ (V★-G (G★-Λ _)) ()
val-var-wrapper³ (V★-⟪⟫ {V★ = V'} {Ξ⋆ = Ξ'} {B₀ = B'} _) _ =
  V' , Ξ' , B' , refl

-- the := case (unchanged)
cnc-abst-dead : ∀ {Γ₁ : TCtx³} {X₁ A₀} → fgt³ Γ₁ ∋ X₁ := A₀
              → entAt (fgt³ Γ₁) X₁ ≡ abst → ⊥
cnc-abst-dead p e = cnc-needs-knowledge p e

-- the NEW case: an x-licensed conceal hands the induction an abstract slot
xlic-rep-abst : ∀ (Ψ₁ : TCtx³) s → absOnly (fgt³ Ψ₁) 0 (` s) ≡ true
              → entAt (fgt³ Ψ₁) s ≡ abst
xlic-rep-abst Ψ₁ s = absOnly-var (fgt³ Ψ₁) s

-- measured on E★′'s own dual: the sealed value sits at the ABSTRACT Y
_ : substᵗ (γᵇ★ dualᵛ★) (` 2) ≡ ` 0
_ = refl

_ : entAt (fgt³ (intOf³ Γz³ dualᵛ★)) 0 ≡ abst
_ = refl

------------------------------------------------------------------------
-- §5.  WHY (b4) IS RULED OUT — a dual-only judgement parameterised by the
-- CO-boundary.
--
-- STRUCTURAL ARGUMENT.  Wrap's contractum is
--     N[x := W ⟪ Θᵈ , renameᵗ (swapᵇ Θ) B₁ ⟫] ⟪ Θ , B₂ ⟫
-- and the inner wrapper is typed by the ORDINARY (env) rule, whose boundary
-- premise — §1's `bw Δ₁ (it Δ₁ Ξ₁) Ξ₁` — is a predicate on (exterior,
-- interior, boundary).  There is no third position for a co-boundary, and
-- preservation must produce a PLAIN derivation, so a co-boundary-indexed
-- judgement cannot be what (env) invokes.  Two consequences, both checked:
--
--   (1) the same boundary occurs in terms that have NO co-boundary at all,
--       and they must keep typing.  handᵗ is an ordinary wrapper carrying
--       E★′'s dual at E★′'s own exterior, licensed by the same x-entry; a
--       judgement demanding a co-boundary would reject a term nothing is
--       wrong with (and progress would have to invent one).
--   (2) the existential repair — "Θᵈ is SOME boundary's dual" — is a
--       companion predicate over a quantified co-boundary, which the
--       grounded-invariant law forbids; and it does not discriminate anyway,
--       since §4.6's adversary reuses a legitimate exterior with a different
--       boundary, and legitimate duals are themselves duals of duals (§4.3).
------------------------------------------------------------------------

handᵗ : Term★
handᵗ = ($★ 9) ⟪ dualᵛ★ , `ℕ ⟫★

⊢3s-hand : Γz³ ∣ [] ⊢3s handᵗ ⦂ `ℕ
⊢3s-hand = G3s.genv bwf3-dual sc-ℕ G3s.g$

_ : dualᴳ³ Γ★³ Θ★ˢ ≡ dualᵛ★          -- handᵗ's boundary IS a dual …
_ = refl

_ : dualᴳ³ Γz³ dualᵛ★ ≡ dd³           -- … and so is the dual of it
_ = refl

------------------------------------------------------------------------
-- §6.  VERDICT
--
-- (b1) READ-BACK IDENTITY — REFUTED, as predicted.  E★′'s rep IS the dual's
--   own ⋆-reveal slot, whose external face is the dummy `ℕ (dummy-read-back),
--   so the identity cannot hold (¬RevId-E★′) and the contractum types in
--   neither regime (¬⊢1-T4′ rep-keeping, ¬⊢1-T4′⋆ rep-less).  What the clause
--   DOES admit is garbage of a different kind: a conceal of an ABSTRACT
--   variable, licensed with no knowledge premise at all (bwf1-garbage vs
--   ¬bwf★-garbage), which re-opens the no-abstract-value dependence that cnc⋆
--   had closed.  Soundness is otherwise untouched (¬⊢1-bad, ¬RevId-bad₂,
--   ⊢1-near-bad, ¬Rev★-far) and the premise transports (RevId-Ξg-ren).
--
-- (b2) FACES AS PREMISE — REFUTED, twice over.  Per entry the two laws are a
--   DEFINITIONAL IDENTITY (faces-head: for every X and every rep), so the
--   premise is vacuous and bad is typable (⊢2-bad), as are bad₂ (faces-bad₂)
--   and far-bad (faces-far) — so it does not even separate the near/far pair
--   (⊢2-near-bad is admitted for the same reason far-bad is).  It does type
--   E★′'s contractum (⊢2-T4′), as anything else.  Whole-boundary the laws are
--   not per-entry
--   stateable: the external law is `substᵗ (ρᵇ Θᵈ) B₁ ≡ substᵗ (γᵇ Θ★) B₁`,
--   which names the CO-boundary — i.e. it collapses into (b4) (§5).
--
-- (b3) EXTERIOR-READ ENTRY — the winner, in its SOUND form, with one real
--   cost.  NAIVE form (syntactic rep equality alone): UNSOUND — ⊢3n-adv
--   types 7 : ℕ at the abstract Z, reusing a legitimately minted x-entry with
--   a boundary that is not the dual (the entry's two homes coincide only for
--   an index-aligned rebuild, and nothing in the entry pins that down).
--   SOUND form: add that the rep must ASSERT NOTHING in the interior
--   (absOnly) — the x-conceal is then cnc⋆'s "claims nothing" WITH a rep for
--   the faces.  Gauntlet: E★′ ✓ (⊢3s-T4′, faces reused, dual and rebuild
--   exact), E★ ✓ (⊢3s-T4, no cnc⋆ needed), Pn ✓ by the ORDINARY clause after
--   the hybrid unfold (bwf3-Pn), bad/bad₂ ✓ refuted (¬⊢3s-bad, ¬Rev³-bad₂,
--   and the clause cannot fire: ¬xlic-bad/¬xlic-bad₂), near/far ✓
--   (⊢3s-near-bad, ¬Rev³-far), dual-of-dual ✓ (bwf3-dd, exact round trip,
--   cnc⋆ retained exactly for rvl⋆), adversary ✓ refuted (¬⊢3s-adv).
--   BONUS: the dual's conceal block becomes entry-INDEPENDENT again
--   (cncOfRevs³ = live cncOfRevs with rvl⋆ ↦ cnc⋆), and the REDUCTION RULES
--   ARE UNCHANGED — the live Wrap already mints this dual (dualᴳ Γ★ Θ★ ≡
--   dualᵛ), so StarConcealProbe's step34′ is this step.
--   WHAT THE SOUND FORM STILL ADMITS, machine-checked: an alias between two
--   ABSTRACT slots (⊢3s-alias — a fresh ↑V:⋆ paired with ↓Z:=V), exactly the
--   freedom cnc⋆ already has, with no knowledge on either side (abs-alias,
--   no-know-alias, no-know-Z).  The absOnly premise is load-bearing: dropping
--   it makes ¬⊢3s-adv unprovable.
--   COST: renaming.  ¬xlic-ren — under a weakening the x-rep moves by the
--   exterior ρ while renᴮ★ freezes the conceal's rep, so the premise is not
--   stable under ⊢renameᵀ, and ¬dual-ren-comm shows recomputing the dual is
--   not a renaming either.  XRen (xren-E★′) is the transport the entry
--   satisfies; the clause needs the two renamings to AGREE, which is not
--   entry-wise stateable.  This is ¬hk-int's phenomenon relocated: the x-entry
--   dodges it as a telescope entry (fgt³) and meets it at its own clause.
--   (iii) NO: (b3) does NOT subsume the (a″) hybrid.  Pn's x-entry licenses
--   only under the naive form (xlic-Pnⁿ vs ¬abs-Pnⁿ), so the unfold retry
--   stays.  OUT OF SCOPE for (b) entirely: entᴳ's chained COPY site (a
--   dual's reveal for a dropped slot whose knowledge names another dropped
--   slot — UpToProbe's Γq/entᴳ≈), which is a REVEAL, not a conceal, and is
--   untouched by any licence; and an x-slot that a later boundary drops
--   without concealing, whose knowledge is lost to rvl⋆ as an abstract slot's
--   would be.
--
-- (b4) RULED OUT structurally (§5): (env)'s boundary premise has no
--   co-boundary position, and ⊢3s-hand exhibits a term that must type without
--   one.
--
-- RANKED: (b3)-sound ≫ (b1) ≈ (b2).  For the design description: syntax gains
-- ONE context entry form (`Z:=x A`) and no boundary form (cnc⋆ stays, for
-- rvl⋆ duals only); ⟦·⟧ gains one branch (rep-carrying ∧ raw-blocked ∧
-- un-unfoldable ⇒ :=x, replacing `abst`); bwf↓ gains one clause (`Γ ∋ Z :=x A`
-- with syntactic rep equality PLUS absOnly A in the interior); cncOfRevs
-- loses its entry test; ⊢renameᵀ needs XRen plus a decision about the
-- coordinate mismatch (¬xlic-ren) — the one open obligation.
------------------------------------------------------------------------

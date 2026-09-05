module strong.notes.old.UpToProbe where

-- SUPERSEDED 2026-09-04 by the dual-conceal licence install
-- (notes/DualLicenseDesign.md): the congruence and its renaming transport
-- are live in strong.Unfold, and Reversal-approx / the retag ordering /
-- the retag lemma in strong.Boundary and strong.BReduction.  The one
-- probed piece NOT installed is the hybrid entry's AMBIENT unfold retry --
-- see strong.Boundary's flagged deviation and notes/InstallGauntlet.agda.

-- ADVERSARIAL PROBE of candidate (a″) — "keep RAW entries, make the
-- KNOWLEDGE COMPARISONS up to unfolding" (notes/DECISIONS.md, the
-- "RECOMMENDATION → (a″)" block closing the (a′) probe verdict).
--
-- (a′) was refuted at ONE site (notes/UnfoldProbe.agda §6, ¬DualCnc-a′): it
-- unfolds the interior ENTRY while SIMULTANEITY keeps the reveal's stored rep
-- raw, so the dual's conceal-of-a-reveal compares an unfolded entry against a
-- raw read-back.  (a″) keeps every entry raw and replaces the three syntactic
-- comparisons by the UNFOLDING CONGRUENCE.  This file installs local variants
-- of every changed rule and hunts for a counterexample at each of the six
-- sites the (a′) probe surveyed.
--
-- Verdict in §10.  In one line: every comparison site is SAFE, and the one
-- thing (a″) alone does NOT fix is Pn/R2 — the reveal whose rep names a slot
-- its own boundary drops has NO knowledge to compare, and no congruence can
-- conjure one.  The HYBRID entry (⟦·⟧ᴴ: raw where expressible, minimally
-- unfolded where not) is therefore REQUIRED, and the resulting raw/unfolded
-- mixture is ≈-coherent (§9).

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; z≤n; s≤s;
                            _<?_; _≤?_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (¬_; Dec; yes; no; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)
open import strong.Types
open import strong.TypeSubst
  using (_⨟ᵗ_; subst-cong; sub-sub; subst-id; rename-subst;
         rename-subst-commute)
open import strong.Context hiding (Δ; Γ; A; B; C; X; Y; Z; x; E)
open import strong.Boundary
open import strong.BReduction
  using (repOf; entAt; copyRep; entᴳ; rvlsᴳ; cncOfRevs; dualᴳ;
         swapᵇ; swapIdx; shiftReps; restrictRen; Mono;
         _≼_; ≼[]; ≼abst; ≼rvld; ≼-refl;
         GVal; Value; G-ƛ; G-Λ; V-$; V-G; V-⟪⟫;
         _⊢_-→_; Wrap; Γp; Θp)
open import strong.DualDef using (BlkRepWf; DualRep; DualCnc; DualInt)
open import strong.notes.old.UnfoldProbe
  using (unfSub; unfoldᵉ; UnfRen; unf-ren; ¬UnfRen-hk; Γid; Γ′id; idρ;
         KNF; KNFᵗ; knf[]; knfabst; knfrvld; absSlots; okS;
         unf-scoped; knf-fix; unf-idem; wf→sc; ∋:=-entAt; rvld≢abst;
         suc-inj; len-++; ∋tv-len; ⊢-len; baseS-len;
         Γ1; ΘW; Γ2ʳ; Γ2ᵁ; Θcv; Θv; ΓPc; ΘWᵈ;
         Θm₁; Θm₂; Θm₁₂; ¬⊕-int-raw; ¬⊕-retag-raw; ¬≼-unfold;
         unf-eq-entries; routes-agree; ¬routes-agree-raw; ¬cnc-W-raw;
         DualCnc-raw; ¬DualCnc-a′)

private
  variable
    Γ Δ Δ' Ψ Ψ' : TCtx
    Γₜ : Ctx
    A B C B₀ A₀ : Ty
    L M N : Term
    Θ Ξ : BCtx
    i j k n x X : ℕ

------------------------------------------------------------------------
-- §1.  THE UNFOLDING CONGRUENCE  _≈Δ̄[_]_
--
-- DESIGN CHOICE, and why: ≈Δ̄ IS the propositional equality of unfoldings —
-- not an inductive congruence with one rule per type former.  It is wrapped
-- in a single constructor (≈unf) purely for Agda's benefit: as a bare
-- definition `unfoldᵉ Γ A ≡ unfoldᵉ Γ B` the type former is not rigid, so no
-- implicit Γ/A/B is ever inferable and every consumer must spell all three
-- out (this was tried first and produced 30 unsolved metas).  The wrapper
-- costs one ≈unf per witness and nothing else.  Three reasons for the
-- equality-of-unfoldings reading over a genuine inductive congruence, all
-- cashed out below:
--   (1) equivalence and congruence come for free — ≈-refl/sym/trans are
--       refl/sym/trans under the wrapper, and the ⇒ and ∀ congruence rules
--       are THEOREMS (≈-⇒, ≈-∀), the ∀ one resting on unfSub-exts, so an
--       inductive presentation would only re-derive them as constructors;
--   (2) every witness in this file is then refl-checkable, and every
--       REFUTATION is a one-line absurd pattern on two closed normal forms
--       (§6) — an inductive relation would need a no-confusion argument;
--   (3) transport (§7) is a statement about unfSub, identical for either
--       presentation, so the inductive form buys nothing there either.
-- The cost is that ≈Δ̄ is not obviously decidable; nothing here needs it.
--
-- The CONTEXT argument is always the context over which BOTH sides are read.
-- Every use below says which context that is, at the point of use.
------------------------------------------------------------------------

infix 4 _≈Δ̄[_]_
data _≈Δ̄[_]_ : Ty → TCtx → Ty → Set where
  ≈unf : ∀ {Γ A B} → unfoldᵉ Γ A ≡ unfoldᵉ Γ B → A ≈Δ̄[ Γ ] B

≈-refl : ∀ {Γ A} → A ≈Δ̄[ Γ ] A
≈-refl = ≈unf refl

≈-sym : ∀ {Γ A B} → A ≈Δ̄[ Γ ] B → B ≈Δ̄[ Γ ] A
≈-sym (≈unf e) = ≈unf (sym e)

≈-trans : ∀ {Γ A B C} → A ≈Δ̄[ Γ ] B → B ≈Δ̄[ Γ ] C → A ≈Δ̄[ Γ ] C
≈-trans (≈unf e₁) (≈unf e₂) = ≈unf (trans e₁ e₂)

-- syntactic equality is the strongest form of ≈ (soundness of every
-- comparison the design has today)
≡→≈ : ∀ {Γ A B} → A ≡ B → A ≈Δ̄[ Γ ] B
≡→≈ {Γ} e = ≈unf (cong (unfoldᵉ Γ) e)

≈-⇒ : ∀ {Γ A A' B B'} → A ≈Δ̄[ Γ ] A' → B ≈Δ̄[ Γ ] B'
    → (A ⇒ B) ≈Δ̄[ Γ ] (A' ⇒ B')
≈-⇒ (≈unf e₁) (≈unf e₂) = ≈unf (cong₂ _⇒_ e₁ e₂)

-- the ∀ case: going under a binder is going under a fresh ABSTRACT entry
unfSub-exts : ∀ (Γ₁ : TCtx) X → extsᵗ (unfSub Γ₁) X ≡ unfSub (abst ∷ Γ₁) X
unfSub-exts Γ₁ zero    = refl
unfSub-exts Γ₁ (suc X) = refl

≈-∀ : ∀ {Γ A B} → A ≈Δ̄[ abst ∷ Γ ] B → (`∀ A) ≈Δ̄[ Γ ] (`∀ B)
≈-∀ {Γ} {A} {B} (≈unf e) =
  ≈unf (cong `∀ (trans (subst-cong (unfSub-exts Γ) A)
                       (trans e (sym (subst-cong (unfSub-exts Γ) B)))))

-- MONOTONICITY in the context.  Absorbs Δ Δ′ says Δ′'s unfolding swallows
-- Δ's (Δ′ knows at least what Δ knows, resolved the same way); then every
-- ≈ at Δ is an ≈ at Δ′.  This is the transport ⊢retag≈ needs (§4).
Absorbs : TCtx → TCtx → Set
Absorbs Δ Δ' = ∀ X → unfoldᵉ Δ' (unfSub Δ X) ≡ unfSub Δ' X

unf-absorb : ∀ (Δ Δ' : TCtx) → Absorbs Δ Δ' → ∀ A
           → unfoldᵉ Δ' (unfoldᵉ Δ A) ≡ unfoldᵉ Δ' A
unf-absorb Δ Δ' h A =
  trans (sub-sub (unfSub Δ) (unfSub Δ') A) (subst-cong h A)

≈-mono : ∀ (Δ Δ' : TCtx) → Absorbs Δ Δ' → ∀ {A B}
       → A ≈Δ̄[ Δ ] B → A ≈Δ̄[ Δ' ] B
≈-mono Δ Δ' h {A} {B} (≈unf e) =
  ≈unf (trans (sym (unf-absorb Δ Δ' h A))
              (trans (cong (unfoldᵉ Δ') e) (unf-absorb Δ Δ' h B)))

------------------------------------------------------------------------
-- §2.  THE (a″) SITES, AS LOCAL VARIANTS.  The live files are untouched.
--
--  (i)   Reversal≈ / Bwf≈  — bwf↓'s licensing, up to ≈ at the EXTERIOR Γ.
--        WHICH Γ: in `Bwf Γ Ψ Θ Ξ` the conceal premise relates
--        `outRead Θ A` (an interior type read BACK OUT, hence a Γ-type) to
--        `upRep X A₀` (Γ's own knowledge, lifted to a Γ-type).  Both are
--        types over the boundary's EXTERIOR Γ, so ≈ is taken at Γ.  Not at
--        Ψ (where only A lives), and not at Γ ↓ X (where only A₀ lives).
--  (ii)  entᴳ≈ / dualᴳ≈ — the dual's copy at a CHAINED slot: the rvl⋆
--        fallback becomes the UNFOLD of Γ's entry, in Γ's own tail Γ ↓ i.
--        cncOfRevs is UNCHANGED (its reps stay raw — that is the ruling
--        (a′) fell over).
--  (iii) _≼≈_ — ⊢retag's context ordering, rvld against rvld up to ≈.
--        WHICH Γ: entries are read over their own TAILS, and a retag
--        transports a derivation from Δ to Δ′, re-establishing every premise
--        over Δ′ — so the reps are compared in the TARGET's tail.
--  (iv)  DualRep≈ / DualCnc≈ / DualInt≈ — DualDef's three statements.
--  (v)   ⟦·⟧ᴴ / intOfᴴ — the HYBRID entry, needed for Pn (§5).
------------------------------------------------------------------------

Reversal≈ : TCtx → BCtx → ℕ → Ty → Ty → Set
Reversal≈ Γ Θ X A A₀ = outRead Θ A ≈Δ̄[ Γ ] upRep X A₀

Reversal→≈ : ∀ Γ Θ X A A₀ → Reversal Θ X A A₀ → Reversal≈ Γ Θ X A A₀
Reversal→≈ Γ Θ X A A₀ = ≡→≈

------------------------------------------------------------------------
-- The HYBRID entry map.  ⟦ Γ ∣ Θ ⟧ᴴ j A is today's ⟦ Θ ⟧ᵉ j A wherever that
-- yields knowledge, and RETRIES with the ambient unfolding of the rep
-- exactly where today's guards give up (`abst`).  So: raw where expressible,
-- unfolded-just-enough where not, and never both for one slot.
------------------------------------------------------------------------

⟦_∣_⟧ᴴ : TCtx → BCtx → ℕ → Ty → TyEntry
⟦ Γ ∣ Θ ⟧ᴴ j A = hyb (⟦ Θ ⟧ᵉ j A)
  where
    hyb : TyEntry → TyEntry
    hyb (rvld B) = rvld B
    hyb abst     = ⟦ Θ ⟧ᵉ j (unfoldᵉ Γ A)

revEntsᴴ : TCtx → BCtx → ℕ → BCtx → TCtx
revEntsᴴ Γ Θ j []            = []
revEntsᴴ Γ Θ j (rvl A ∷ Ξ)   = ⟦ Γ ∣ Θ ⟧ᴴ j A ∷ revEntsᴴ Γ Θ (suc j) Ξ
revEntsᴴ Γ Θ j (rvl⋆ ∷ Ξ)    = abst ∷ revEntsᴴ Γ Θ (suc j) Ξ
revEntsᴴ Γ Θ j (cnc X A ∷ Ξ) = revEntsᴴ Γ Θ j Ξ

intOfᴴ : TCtx → BCtx → TCtx
intOfᴴ Γ Θ = revEntsᴴ Γ Θ 0 Θ ++ dropN (cmax Θ) Γ

------------------------------------------------------------------------
-- Bwf≈ : today's Bwf with the conceal premise up to ≈.  Identical
-- otherwise — the reveal block (bwf≈↑ / bwf≈⋆) is untouched.
------------------------------------------------------------------------

data Bwf≈ (Γ Ψ : TCtx) (Θ : BCtx) : BCtx → Set where
  bwf≈[] : Bwf≈ Γ Ψ Θ []
  bwf≈↑  : ∀ {A Ξ} → Γ ⊢ A
         → Bwf≈ Γ Ψ Θ Ξ → Bwf≈ Γ Ψ Θ (rvl A ∷ Ξ)
  bwf≈⋆  : ∀ {Ξ} → Bwf≈ Γ Ψ Θ Ξ → Bwf≈ Γ Ψ Θ (rvl⋆ ∷ Ξ)
  bwf≈↓  : ∀ {X A A₀ Ξ}
         → Γ ∋ X := A₀ → Reversal≈ Γ Θ X A A₀ → Ψ ⊢ A
         → Bwf≈ Γ Ψ Θ Ξ → Bwf≈ Γ Ψ Θ (cnc X A ∷ Ξ)

infix 4 _∣_⊢ᵇ≈_
_∣_⊢ᵇ≈_ : TCtx → TCtx → BCtx → Set
Γ ∣ Ψ ⊢ᵇ≈ Θ = Bwf≈ Γ Ψ Θ Θ

-- today's boundaries are still well formed (soundness of the relaxation)
bwf→bwf≈ : ∀ {Γ Ψ Θ} Ξ → Bwf Γ Ψ Θ Ξ → Bwf≈ Γ Ψ Θ Ξ
bwf→bwf≈ []            bwf[]              = bwf≈[]
bwf→bwf≈ (rvl A ∷ Ξ)   (bwf↑ w b)         = bwf≈↑ w (bwf→bwf≈ Ξ b)
bwf→bwf≈ (rvl⋆ ∷ Ξ)    (bwf⋆ b)           = bwf≈⋆ (bwf→bwf≈ Ξ b)
bwf→bwf≈ (cnc X A ∷ Ξ) (bwf↓ p rev w b)   =
  bwf≈↓ p (≡→≈ rev) w (bwf→bwf≈ Ξ b)

------------------------------------------------------------------------
-- The typing judgement, copied with (env) reading Bwf≈ and the HYBRID
-- interior.  NOTHING ELSE CHANGES: every other rule is character-for-
-- character today's rule (the (a″) delta in `_∣_⊢_⦂_` is confined to
-- (env)'s two premises that mention the boundary and its interior).
------------------------------------------------------------------------

infix 3 _∣_⊢≈_⦂_
data _∣_⊢≈_⦂_ : TCtx → Ctx → Term → Ty → Set where
  ⊢`≈   : Γₜ ∋ x ⦂ A → Δ ∣ Γₜ ⊢≈ ` x ⦂ A
  ⊢$≈   : Δ ∣ Γₜ ⊢≈ $ n ⦂ `ℕ
  ⊢ƛ≈   : Δ ⊢ A → Δ ∣ A ∷ Γₜ ⊢≈ N ⦂ B → Δ ∣ Γₜ ⊢≈ ƛ A ∙ N ⦂ (A ⇒ B)
  ⊢·≈   : Δ ∣ Γₜ ⊢≈ L ⦂ (A ⇒ B) → Δ ∣ Γₜ ⊢≈ M ⦂ A → Δ ∣ Γₜ ⊢≈ L · M ⦂ B
  ⊢Λ≈   : (abst ∷ Δ) ∣ ⤊ Γₜ ⊢≈ N ⦂ C → Δ ∣ Γₜ ⊢≈ Λ N ⦂ `∀ C
  ⊢·[]≈ : Δ ∣ Γₜ ⊢≈ L ⦂ `∀ B → Δ ⊢ A
        → Δ ∣ Γₜ ⊢≈ L ·[ B , A ] ⦂ B [ A ]ᵗ
  env≈  : Δ ∣ intOfᴴ Δ Θ ⊢ᵇ≈ Θ
        → Scoped (baseS Θ Δ) B₀
        → intOfᴴ Δ Θ ∣ [] ⊢≈ M ⦂ substᵗ (γᵇ Θ) B₀
          ---------------------------------------------------
        → Δ ∣ Γₜ ⊢≈ M ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀

------------------------------------------------------------------------
-- (ii) the dual's copy.  Only the CHAINED case changes: instead of losing
-- the knowledge to rvl⋆, copy the UNFOLD of Γ's entry through Γ's own tail.
------------------------------------------------------------------------

unfEnt : TCtx → ℕ → Ty → Ty
unfEnt Γ i B = unfoldᵉ (Γ ↓ i) B

entᴳ≈ : TCtx → BCtx → ℕ → ℕ → BEntry
entᴳ≈ Γ Θ i k with isConc i Θ
entᴳ≈ Γ Θ i k | true  = rvl (repOf i Θ)
entᴳ≈ Γ Θ i k | false with entAt Γ i
entᴳ≈ Γ Θ i k | false | abst   = rvl⋆
entᴳ≈ Γ Θ i k | false | rvld B with dfree 0 k B
entᴳ≈ Γ Θ i k | false | rvld B | true  = rvl (copyRep k (revs Θ) B)
entᴳ≈ Γ Θ i k | false | rvld B | false with dfree 0 k (unfEnt Γ i B)
entᴳ≈ Γ Θ i k | false | rvld B | false | true  =
  rvl (copyRep k (revs Θ) (unfEnt Γ i B))
entᴳ≈ Γ Θ i k | false | rvld B | false | false = rvl⋆

rvlsᴳ≈ : ℕ → ℕ → TCtx → BCtx → BCtx
rvlsᴳ≈ zero    s Γ Θ = []
rvlsᴳ≈ (suc k) s Γ Θ = entᴳ≈ Γ Θ s k ∷ rvlsᴳ≈ k (suc s) Γ Θ

dualᴳ≈ : TCtx → BCtx → BCtx
dualᴳ≈ Γ Θ = rvlsᴳ≈ (cmax Θ) 0 Γ Θ ++ cncOfRevs 0 Θ

------------------------------------------------------------------------
-- (iii) _≼≈_ : the retag ordering, up to ≈ in the TARGET's tail.
------------------------------------------------------------------------

infix 4 _≼≈_
data _≼≈_ : TCtx → TCtx → Set where
  ≼≈[]   : [] ≼≈ []
  ≼≈abst : ∀ {Δ Δ' E} → Δ ≼≈ Δ' → (abst ∷ Δ) ≼≈ (E ∷ Δ')
  ≼≈rvld : ∀ {Δ Δ' A B} → Δ ≼≈ Δ' → A ≈Δ̄[ Δ' ] B
         → (rvld A ∷ Δ) ≼≈ (rvld B ∷ Δ')

≼≈-refl : ∀ (Δ : TCtx) → Δ ≼≈ Δ
≼≈-refl []           = ≼≈[]
≼≈-refl (abst ∷ Δ)   = ≼≈abst (≼≈-refl Δ)
≼≈-refl (rvld A ∷ Δ) = ≼≈rvld (≼≈-refl Δ) ≈-refl

≼→≼≈ : ∀ {Δ Δ'} → Δ ≼ Δ' → Δ ≼≈ Δ'
≼→≼≈ ≼[]       = ≼≈[]
≼→≼≈ (≼abst p) = ≼≈abst (≼→≼≈ p)
≼→≼≈ (≼rvld p) = ≼≈rvld (≼→≼≈ p) ≈-refl

≼≈-len : ∀ {Δ Δ'} → Δ ≼≈ Δ' → length Δ ≡ length Δ'
≼≈-len ≼≈[]         = refl
≼≈-len (≼≈abst p)   = cong suc (≼≈-len p)
≼≈-len (≼≈rvld p _) = cong suc (≼≈-len p)

-- the knowledge lookup a retag must re-establish: the target knows the same
-- variable, with a rep that is ≈-equal in the target's own tail
≼≈-∋:= : ∀ {Δ Δ' X A₀} → Δ ≼≈ Δ' → Δ ∋ X := A₀
       → Σ Ty λ A₀' → (Δ' ∋ X := A₀') × (A₀ ≈Δ̄[ Δ' ↓ X ] A₀')
≼≈-∋:= (≼≈rvld {B = B} p e) here          = B , here , e
≼≈-∋:= (≼≈abst {E = abst}   p) (skip-abst q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-abst r , e
≼≈-∋:= (≼≈abst {E = rvld C} p) (skip-abst q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-rvld r , e
≼≈-∋:= (≼≈rvld p _)            (skip-rvld q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-rvld r , e

------------------------------------------------------------------------
-- (iv) DualDef's three statements, up-to.  Shapes as in strong.DualDef,
-- with intOf ↦ intOfᴴ, dualᴳ ↦ dualᴳ≈, Bwf ↦ Bwf≈, _≼_ ↦ _≼≈_ — and
-- DualRep≈ carrying the extra (chained) copy the fallback now emits.
------------------------------------------------------------------------

BlkRepWf≈ : TCtx → BCtx → Set
BlkRepWf≈ Δ Θ = ∀ k i B → isConc i Θ ≡ false → entAt Δ i ≡ rvld B
  → (dfree 0 k B ≡ true → intOfᴴ Δ Θ ⊢ copyRep k (revs Θ) B)
  × (dfree 0 k (unfEnt Δ i B) ≡ true
     → intOfᴴ Δ Θ ⊢ copyRep k (revs Θ) (unfEnt Δ i B))

DualRep≈ : Set
DualRep≈ = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOfᴴ Δ Θ ⊢ᵇ≈ Θ → BlkRepWf≈ Δ Θ

DualCnc≈ : Set
DualCnc≈ = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOfᴴ Δ Θ ⊢ᵇ≈ Θ
  → Bwf≈ (intOfᴴ Δ Θ) (intOfᴴ (intOfᴴ Δ Θ) (dualᴳ≈ Δ Θ)) (dualᴳ≈ Δ Θ)
         (cncOfRevs 0 Θ)

DualInt≈ : Set
DualInt≈ = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOfᴴ Δ Θ ⊢ᵇ≈ Θ
  → Δ ≼≈ intOfᴴ (intOfᴴ Δ Θ) (dualᴳ≈ Δ Θ)

------------------------------------------------------------------------
-- §3.  SITE 1a — THE (a′) KILLER, REVERSED.
--
-- UnfoldProbe's ¬DualCnc-a′ site: ΓPc = Y:=ℕ (0) , X:=ℕ (1) and
-- ΘW = ↑W:=Y.  Under (a′) the entry was ℕ and the raw read-back ` 1, with
-- nothing to bridge them.  Under (a″) the entry stays RAW (W:=Y), the raw
-- read-back IS the raw knowledge, and DualCnc≈ holds — by ≡→≈ on today's
-- refl.  So (a″) needs NOTHING at the site that killed (a′).
------------------------------------------------------------------------

DualCnc≈-Pc : Σ Ty λ A₀ → (intOf ΓPc ΘW ∋ 0 := A₀)
                        × Reversal≈ (intOf ΓPc ΘW) ΘWᵈ 0 (ρᵇ ΘW 0) A₀
DualCnc≈-Pc = ` 0 , here , ≡→≈ refl

-- with the hybrid entry the site is unchanged: ΘW's rep is expressible,
-- so ⟦·⟧ᴴ takes the RAW branch and the interior is bit-identical
intOfᴴ-ΘW : intOfᴴ ΓPc ΘW ≡ intOf ΓPc ΘW
intOfᴴ-ΘW = refl

DualCnc≈ᴴ-Pc : Σ Ty λ A₀ → (intOfᴴ ΓPc ΘW ∋ 0 := A₀)
                         × Reversal≈ (intOfᴴ ΓPc ΘW) ΘWᵈ 0 (ρᵇ ΘW 0) A₀
DualCnc≈ᴴ-Pc = ` 0 , here , ≡→≈ refl

------------------------------------------------------------------------
-- §4.  SITE 1b — Pc END TO END, at the seal's dual.
--
-- Γq = W:=Y (0) , Y:=ℕ (1) , X:=ℕ (2) is Pc's ambient after T5 (the same
-- context as BReduction's Γp, with ℕ for 𝔹 because the term language has no
-- boolean literal), and Θq = ↓X:=ℕ is the seal, which drops all three slots.
-- W's entry is the CHAIN "W is Y", and Θq drops Y too, so today's dual loses
-- it to rvl⋆ (BReduction's Γp/Θp block).  (a″)'s dual copies the UNFOLD.
------------------------------------------------------------------------

Γq : TCtx
Γq = rvld (` 0) ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

Θq : BCtx
Θq = cnc 2 `ℕ ∷ []

Γq′ : TCtx                       -- the rebuild:  W:=ℕ , Y:=ℕ , X:=ℕ
Γq′ = rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

_ : intOf Γq Θq ≡ []
_ = refl

-- today: the chained slot's knowledge is DROPPED (the standing DualInt gap,
-- BReduction's Γp comment) …
_ : dualᴳ Γq Θq ≡ rvl⋆ ∷ rvl `ℕ ∷ rvl `ℕ ∷ []
_ = refl

¬DualInt-Γq : ¬ (Γq ≼ intOf (intOf Γq Θq) (dualᴳ Γq Θq))
¬DualInt-Γq ()

-- … and under (a″)'s entᴳ≈ it is COPIED, as the one-step unfold of W:=Y
_ : dualᴳ≈ Γq Θq ≡ rvl `ℕ ∷ rvl `ℕ ∷ rvl `ℕ ∷ []
_ = refl

_ : intOfᴴ (intOfᴴ Γq Θq) (dualᴳ≈ Γq Θq) ≡ Γq′
_ = refl

-- THEOREM (site 1b, context law).  The rebuild differs from Γq by exactly
-- one unfolding at the chained slot — which is what _≼≈_ compares.
DualInt≈-Γq : Γq ≼≈ intOfᴴ (intOfᴴ Γq Θq) (dualᴳ≈ Γq Θq)
DualInt≈-Γq = ≼≈rvld (≼≈rvld (≼≈rvld ≼≈[] ≈-refl) ≈-refl) (≈unf refl)

-- the dual itself is well formed (every rep it carries is now closed)
⊢dualᴳ≈-Γq : intOfᴴ Γq Θq ∣ intOfᴴ (intOfᴴ Γq Θq) (dualᴳ≈ Γq Θq)
             ⊢ᵇ≈ dualᴳ≈ Γq Θq
⊢dualᴳ≈-Γq = bwf≈↑ wf-ℕ (bwf≈↑ wf-ℕ (bwf≈↑ wf-ℕ bwf≈[]))

------------------------------------------------------------------------
-- THE SITE ≈ WAS INTRODUCED FOR: the argument's ↓W:=Y conceal, retyped in
-- the rebuilt context.  argW is the shape any Pc argument at W has — a
-- wrapper chain ↓W:=Y over ↓Y:=ℕ ending in a literal.
------------------------------------------------------------------------

argW : Term
argW = (($ 3) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ cnc 0 (` 0) ∷ [] , ` 0 ⟫

Θo Θi : BCtx
Θo = cnc 0 (` 0) ∷ []            -- ↓W:=Y   (rep = the interior's Y)
Θi = cnc 0 `ℕ ∷ []               -- ↓Y:=ℕ

-- in the ORIGINAL context the conceal is licensed on the nose
⊢argW : Γq ∣ [] ⊢≈ argW ⦂ ` 0
⊢argW =
  env≈ (bwf≈↓ here (≡→≈ refl) (wf-var here-rvld) bwf≈[])
       (sc-var hereᵒ)
       (env≈ (bwf≈↓ here (≡→≈ refl) wf-ℕ bwf≈[])
             (sc-var hereᵒ)
             ⊢$≈)

-- *** THE COMPARISON ***  in the REBUILT context the knowledge for W is the
-- unfolded ℕ, while the conceal's read-back is still the raw variable ` 1.
-- Syntactic Reversal FAILS …
¬Reversal-argW′ : ¬ (Reversal Θo 0 (` 0) `ℕ)
¬Reversal-argW′ ()

-- … and Reversal≈ SUCCEEDS, by refl on the unfoldings (` 1 unfolds to ℕ in
-- Γq′, and ℕ is already unfolded).  This is (a″)'s whole content.
Reversal≈-argW′ : Reversal≈ Γq′ Θo 0 (` 0) `ℕ
Reversal≈-argW′ = ≈unf refl

-- THEOREM (site 1b, end to end).  argW retypes in the rebuilt context.
⊢argW-rebuilt : Γq′ ∣ [] ⊢≈ argW ⦂ ` 0
⊢argW-rebuilt =
  env≈ (bwf≈↓ here Reversal≈-argW′ (wf-var here-rvld) bwf≈[])
       (sc-var hereᵒ)
       (env≈ (bwf≈↓ here (≡→≈ refl) wf-ℕ bwf≈[])
             (sc-var hereᵒ)
             ⊢$≈)

-- and the retag that licenses it is exactly DualInt≈-Γq's slot-0 component
-- (the ∋:= half, mechanised)
≼≈-∋:=-Γq : Σ Ty λ A₀' → (Γq′ ∋ 0 := A₀') × ((` 0) ≈Δ̄[ Γq′ ↓ 0 ] A₀')
≼≈-∋:=-Γq = ≼≈-∋:= DualInt≈-Γq here

------------------------------------------------------------------------
-- §5.  SITE 2 — Pn / R2.
--
-- Γn = Y:=ℕ (0) , X:=ℕ (1) with Y REVEALED, Θn = ↑Z:=Y , ↓X:=ℕ.  Θn's
-- interior BLOCKS Y (↓X drops everything up to X), so today's ⟦·⟧ has no
-- interior reading for Z's rep and the entry is `abst`.
------------------------------------------------------------------------

Γn : TCtx
Γn = rvld `ℕ ∷ rvld `ℕ ∷ []

Θn : BCtx
Θn = cnc 1 `ℕ ∷ rvl (` 0) ∷ []

_ : intOf Γn Θn ≡ abst ∷ []          -- Z ABSTRACT (today, and under pure a″)
_ = refl

-- (2a) PURE (a″), raw entries: STILL STUCK.  The dual must conceal Z, and
-- bwf≈↓'s FIRST premise is a knowledge LOOKUP, which ≈ never relaxes: there
-- is no `Δ ∋ 0 := A₀` at all, so no congruence can license the conceal.
-- This is the precise sense in which (a″) alone does not fix Pn.
¬DualCnc≈-Pn-raw :
  ¬ (Σ Ty λ A₀ → (intOf Γn Θn ∋ 0 := A₀)
               × Reversal≈ (intOf Γn Θn) (dualᴳ≈ Γn Θn) 0 (ρᵇ Θn 0) A₀)
¬DualCnc≈-Pn-raw (A₀ , () , _)

-- (2b) THE HYBRID.  ⟦·⟧ᴴ retries with unfoldᵉ Γn (` 0) = ℕ, so Z:=ℕ.
_ : intOfᴴ Γn Θn ≡ rvld `ℕ ∷ []
_ = refl

Θnᵈ : BCtx
Θnᵈ = rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []

_ : dualᴳ≈ Γn Θn ≡ Θnᵈ
_ = refl

_ : dualᴳ Γn Θn ≡ Θnᵈ                -- no chained slot here: same dual
_ = refl

-- the dual's interior rebuilds Γn EXACTLY (not merely up to ≈)
_ : intOfᴴ (intOfᴴ Γn Θn) Θnᵈ ≡ Γn
_ = refl

DualInt≈-Pn : Γn ≼≈ intOfᴴ (intOfᴴ Γn Θn) (dualᴳ≈ Γn Θn)
DualInt≈-Pn = ≼≈-refl Γn

-- THEOREM (site 2b, the licensing).  The dual's ↓Z conceal is licensed.  Its
-- read-back is NOT the raw Y the memo expected: outSub sends Θnᵈ's interior
-- index 0 through Θnᵈ's OWN reveal for Y, whose rep is the copied ℕ — so the
-- read-back is ℕ, the knowledge is ℕ, and the premise holds SYNTACTICALLY.
_ : outRead Θnᵈ (` 0) ≡ `ℕ
_ = refl

DualCnc≈ᴴ-Pn : Σ Ty λ A₀ → (intOfᴴ Γn Θn ∋ 0 := A₀)
                         × Reversal≈ (intOfᴴ Γn Θn) Θnᵈ 0 (ρᵇ Θn 0) A₀
DualCnc≈ᴴ-Pn = `ℕ , here , ≡→≈ refl

DualCnc-Pn-syntactic : Reversal Θnᵈ 0 (ρᵇ Θn 0) `ℕ
DualCnc-Pn-syntactic = refl

------------------------------------------------------------------------
-- Pn's FAILING WRAP STEP, typed end to end under the hybrid.
--   redex       ((λz:Z. z) ⟪ Θn , Z⇒Z ⟫) · W        : Y  over Γn
--   contractum  (W ⟪ Θnᵈ , Z ⟫) ⟪ Θn , Z ⟫          : Y  over Γn
-- with W the canonical argument at Y (a conceal ↓Y:=ℕ over a literal).
-- swapᵇ Θn sends B₁ = ` 0 (Θn's reveal slot) to ` 2 in the dual's frame.
------------------------------------------------------------------------

Wval : Term
Wval = ($ 1) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫

⊢Wval : Γn ∣ [] ⊢≈ Wval ⦂ ` 0
⊢Wval = env≈ (bwf≈↓ here (≡→≈ refl) wf-ℕ bwf≈[]) (sc-var hereᵒ) ⊢$≈

bwf≈-Θn : Γn ∣ intOfᴴ Γn Θn ⊢ᵇ≈ Θn
bwf≈-Θn = bwf≈↓ (skip-rvld here) (≡→≈ refl) wf-ℕ
                (bwf≈↑ (wf-var here-rvld) bwf≈[])

⊢redex-Pn : Γn ∣ [] ⊢≈
  ((ƛ ` 0 ∙ ` 0) ⟪ Θn , (` 0 ⇒ ` 0) ⟫) · Wval ⦂ ` 0
⊢redex-Pn =
  ⊢·≈ (env≈ bwf≈-Θn (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
            (⊢ƛ≈ (wf-var here-rvld) (⊢`≈ here)))
      ⊢Wval

_ : swapᵇ Θn 0 ≡ 2
_ = refl

-- the step itself, by the LIVE rule (so the two derivations really are a
-- preservation instance: Wrap's dual here is dualᴳ = dualᴳ≈, and its
-- boundary type is renameᵗ (swapᵇ Θn) (` 0) = ` 2)
step-Pn : Γn ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θn , (` 0 ⇒ ` 0) ⟫) · Wval
          -→ (Wval ⟪ Θnᵈ , ` 2 ⟫) ⟪ Θn , ` 0 ⟫
step-Pn = Wrap (V-⟪⟫ V-$)

⊢contractum-Pn : Γn ∣ [] ⊢≈
  (Wval ⟪ Θnᵈ , ` 2 ⟫) ⟪ Θn , ` 0 ⟫ ⦂ ` 0
⊢contractum-Pn =
  env≈ bwf≈-Θn (sc-var hereᵒ)
       (env≈ (bwf≈↑ wf-ℕ
               (bwf≈↑ wf-ℕ
                 (bwf≈↓ here (≡→≈ refl) (wf-var here-rvld) bwf≈[])))
             (sc-var (thereᵒ (thereᵒ hereᵒ)))
             ⊢Wval)

------------------------------------------------------------------------
-- THE Λ-BOUND VARIANT (Boundary's Γ₈ = X Λ-bound , Y:=ℕ, and Θ₈ = Θn's
-- shape).  unfoldᵉ is the IDENTITY on an abstract variable, so the hybrid
-- changes nothing: the entry stays `abst` and the dual's conceal stays
-- unlicensed.  The residual case is CONJECTURED VACUOUS.
------------------------------------------------------------------------

_ : intOfᴴ Γ₈ Θ₈ ≡ abst ∷ []
_ = refl

¬DualCnc≈ᴴ-E8 :
  ¬ (Σ Ty λ A₀ → (intOfᴴ Γ₈ Θ₈ ∋ 0 := A₀)
               × Reversal≈ (intOfᴴ Γ₈ Θ₈) (dualᴳ≈ Γ₈ Θ₈) 0 (ρᵇ Θ₈ 0) A₀)
¬DualCnc≈ᴴ-E8 (A₀ , () , _)

-- PROVEN, and the base of the vacuity argument: a conceal of an ABSTRACT
-- variable is unlicensed, in either regime (bwf↓/bwf≈↓ share the premise).
cnc-needs-knowledge : ∀ {Γ₁ : TCtx} {X A₀} → Γ₁ ∋ X := A₀
                    → entAt Γ₁ X ≡ abst → ⊥
cnc-needs-knowledge p ea = rvld≢abst (trans (sym (∋:=-entAt p)) ea)

-- PROVEN, and the other base: a value at a VARIABLE type is a WRAPPER — the
-- three other value forms have base/⇒/∀ type.
val-var-wrapper : ∀ {Δ Γₜ V X} → Value V → Δ ∣ Γₜ ⊢≈ V ⦂ ` X
  → Σ Term λ V' → Σ BCtx λ Θ' → Σ Ty λ B' → V ≡ V' ⟪ Θ' , B' ⟫
val-var-wrapper V-$            ()
val-var-wrapper (V-G G-ƛ)      ()
val-var-wrapper (V-G (G-Λ _))  ()
val-var-wrapper (V-⟪⟫ {V = V'} {Θ = Θ'} {B₀ = B'} _) _ = V' , Θ' , B' , refl

-- CONJECTURE (no-abstract-value), stated but not proved: if Δ ∣ [] ⊢≈ V ⦂ ` X
-- and entAt Δ X ≡ abst then ⊥.  ARGUMENT (induction on the VALUE, which
-- strictly decreases through val-var-wrapper): V = V′ ⟪ Θ′ , B₀′ ⟫ with
-- substᵗ (ρᵇ Θ′) B₀′ ≡ ` X, and B₀′ is Scoped, so B₀′ = ` s for an ACCESSIBLE
-- frame slot s.  Either (a) s < revs Θ′ and Θ′'s reveal at s has rep ` X, so
-- V′'s interior type is the reveal slot itself and ⟦·⟧/⟦·⟧ᴴ leaves that entry
-- ABSTRACT (unfoldᵉ is the identity at an abstract X — the witness above), so
-- the IH applies to V′; or (b) s is a Γ-slot, in which case it is CONCEALED
-- (a kept slot's ρᵇ image is its own index, and it is X, contradicting that a
-- conceal is needed) and cnc-needs-knowledge refutes it directly.  Closing
-- (a) needs the interior entry lemma for ⟦·⟧ᴴ at an abstract rep, which is
-- the `hyb abst` clause — deliberately left as the install's obligation.

------------------------------------------------------------------------
-- §6.  SITE 3 — bad / bad₂ MUST STAY REFUTED, and a NEAR-BAD MUST BE
-- ADMITTED.  The up-to congruence relaxes the comparison, so this is the
-- soundness test: it must relax it EXACTLY as far as Γ's knowledge reaches.
------------------------------------------------------------------------

-- bad = (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫ : the inner conceal's rep ℕ
-- reads back to ℕ, the exterior knows ∀Z.Z→Z, and BOTH are closed, so their
-- unfoldings are themselves — ≈ cannot bridge them.
_ : intOfᴴ [] (rvl ∀ZZ ∷ []) ≡ intOf [] (rvl ∀ZZ ∷ [])
_ = refl

¬Reversal≈-bad : ¬ (Reversal≈ (rvld ∀ZZ ∷ []) (cnc 0 `ℕ ∷ []) 0 `ℕ ∀ZZ)
¬Reversal≈-bad (≈unf ())

¬⊢bad≈ : ¬ ([] ∣ [] ⊢≈ bad ⦂ ∀ZZ)
¬⊢bad≈ (env≈ _ _ (env≈ (bwf≈↓ here rev _ _) _ _)) = ¬Reversal≈-bad rev

-- bad₂ (Γb = X:=X′ , X′:=∀Z.Z→Z ;  Θb = ↓X:=X′ , ↑?:=ℕ): the read-back is ℕ
-- and the knowledge is X′, which unfolds to ∀Z.Z→Z.  Still refuted.
¬Reversal≈-bad₂ : ¬ (Reversal≈ Γb Θb 0 (` 0) (` 0))
¬Reversal≈-bad₂ (≈unf ())

-- A NEAR-BAD THAT MUST BE ACCEPTED: Γnb = W:=Y (0) , Y:=ℕ (1).  The conceal
-- ↓W:=ℕ reaches W's knowledge by the OTHER ROUTE (through Y).  Today's
-- syntactic premise REJECTS it (read-back ℕ vs knowledge ` 1) …
Γnb : TCtx
Γnb = rvld (` 0) ∷ rvld `ℕ ∷ []

Θnb : BCtx
Θnb = cnc 0 `ℕ ∷ []

¬Reversal-near-bad : ¬ (Reversal Θnb 0 `ℕ (` 0))
¬Reversal-near-bad ()

-- … and (a″) ACCEPTS it, which is the point: W really is ℕ.
Reversal≈-near-bad : Reversal≈ Γnb Θnb 0 `ℕ (` 0)
Reversal≈-near-bad = ≈unf refl

⊢near-bad : Γnb ∣ [] ⊢≈ ($ 3) ⟪ Θnb , ` 0 ⟫ ⦂ ` 0
⊢near-bad = env≈ (bwf≈↓ here Reversal≈-near-bad wf-ℕ bwf≈[])
                 (sc-var hereᵒ) ⊢$≈

-- … while knowledge that GENUINELY differs is still rejected: ↓W:=∀Z.Z→Z
-- over the same Γnb (W unfolds to ℕ, not to ∀Z.Z→Z).
¬Reversal≈-far-bad : ¬ (Reversal≈ Γnb (cnc 0 ∀ZZ ∷ []) 0 ∀ZZ (` 0))
¬Reversal≈-far-bad (≈unf ())

------------------------------------------------------------------------
-- §7.  SITE 4 — RENAMING.
--
-- UnfoldProbe's ¬UnfRen-hk: the OPERATOR unfoldᵉ does not commute with
-- renaming under ⊢renameᵀ's three hypotheses (Γid = X Λ-bound, Γ′id = X:=ℕ,
-- idρ satisfies h-∋tv / h-mono / h-∋:= and UnfRen still fails).  KEY
-- QUESTION: does the CONGRUENCE transport with less?  YES — and with the
-- hypothesis in ABSORBED form, which is exactly what fails to hold on the
-- nose but holds up to ≈.
------------------------------------------------------------------------

UnfRen≈ : (ℕ → ℕ) → TCtx → TCtx → Set
UnfRen≈ ρ Γ₁ Γ₂ = ∀ X → unfoldᵉ Γ₂ (renameᵗ ρ (unfSub Γ₁ X)) ≡ unfSub Γ₂ (ρ X)

-- THEOREM (site 4).  Under UnfRen≈ the congruence transports — for every
-- pair of types, with no scope restriction.
≈-ren : ∀ {ρ} (Γ₁ Γ₂ : TCtx) → UnfRen≈ ρ Γ₁ Γ₂ → ∀ {A B}
      → A ≈Δ̄[ Γ₁ ] B → renameᵗ ρ A ≈Δ̄[ Γ₂ ] renameᵗ ρ B
≈-ren {ρ} Γ₁ Γ₂ h {A} {B} (≈unf e) =
  ≈unf (trans (sym (step A))
              (trans (cong (λ T → unfoldᵉ Γ₂ (renameᵗ ρ T)) e) (step B)))
  where
    step : ∀ T → unfoldᵉ Γ₂ (renameᵗ ρ (unfoldᵉ Γ₁ T))
                 ≡ unfoldᵉ Γ₂ (renameᵗ ρ T)
    step T =
      trans (cong (substᵗ (unfSub Γ₂)) (rename-subst ρ (unfSub Γ₁) T))
        (trans (sub-sub (λ X → renameᵗ ρ (unfSub Γ₁ X)) (unfSub Γ₂) T)
          (trans (subst-cong h T)
                 (sym (rename-subst-commute ρ (unfSub Γ₂) T))))

-- *** THE FIND ***  the ABSTRACT-to-REVEALED case, which is precisely what
-- broke UnfRen, is FREE for UnfRen≈: an abstract slot unfolds to itself, so
-- the equation becomes unfSub Γ₂ (ρ X) ≡ unfSub Γ₂ (ρ X).
UnfRen≈-abst : ∀ (ρ : ℕ → ℕ) (Γ₁ Γ₂ : TCtx) X → unfSub Γ₁ X ≡ ` X
             → unfoldᵉ Γ₂ (renameᵗ ρ (unfSub Γ₁ X)) ≡ unfSub Γ₂ (ρ X)
UnfRen≈-abst ρ Γ₁ Γ₂ X e = cong (λ T → unfoldᵉ Γ₂ (renameᵗ ρ T)) e

-- and concretely, on the very witness that refutes UnfRen:
UnfRen≈-idρ : UnfRen≈ idρ Γid Γ′id
UnfRen≈-idρ zero    = refl
UnfRen≈-idρ (suc X) = refl

-- so the strengthening ¬UnfRen-hk demanded of ⊢renameᵀ DISSOLVES: (a″) does
-- not unfold anything in the context, and where the relation must move, the
-- absorbed hypothesis holds at the abstract-to-revealed step that killed the
-- operator form.
UnfRen-vs-UnfRen≈ : (¬ (UnfRen idρ Γid Γ′id)) × UnfRen≈ idρ Γid Γ′id
UnfRen-vs-UnfRen≈ = ¬UnfRen-hk , UnfRen≈-idρ

------------------------------------------------------------------------
-- §7b.  SITE 4, THE HYBRID'S SHARE.  The `hyb abst` branch DOES put an
-- unfolding inside a context, so ¬UnfRen-hk's phenomenon reappears there —
-- and this is the one residual obligation the hybrid carries.  Measured
-- exactly: Γe = X Λ-bound , Y:=ℕ and Γe′ = X:=𝔹 , Y:=ℕ under idρ, with
-- Θe = ↑Z:=X , ↓Y:=ℕ blocking X.  All three ⊢renameᵀ hypotheses hold
-- (h-∋:=-e below; h-∋tv and Mono are the identity).
------------------------------------------------------------------------

Γe Γe′ : TCtx
Γe  = abst ∷ rvld `ℕ ∷ []
Γe′ = rvld `𝔹 ∷ rvld `ℕ ∷ []

Θe : BCtx
Θe = cnc 1 `ℕ ∷ rvl (` 0) ∷ []

h-∋:=-e : ∀ {X A₀} → Γe ∋ X := A₀
        → Γe′ ∋ idρ X := renameᵗ (restrictRen X idρ) A₀
h-∋:=-e (skip-abst here)            = skip-rvld here
h-∋:=-e (skip-abst (skip-rvld ()))

_ : intOfᴴ Γe  Θe ≡ abst ∷ []          -- nothing to unfold: X is abstract
_ = refl

_ : intOfᴴ Γe′ Θe ≡ rvld `𝔹 ∷ []       -- the fallback fires: Z:=𝔹
_ = refl

-- MISMATCH: ⟦·⟧ᴴ does NOT commute with the renaming on the nose (the
-- source's entry is abstract, the target's is knowledge) …
¬⟦⟧ᴴ-ren : ¬ (intOfᴴ Γe Θe ≡ intOfᴴ Γe′ Θe)
¬⟦⟧ᴴ-ren ()

-- … but it moves in the USABLE direction: the interiors are ordered by
-- _≼≈_ source-to-target, which is precisely what ⊢retag≈ consumes.  So the
-- install pays for the hybrid with a ⊢retag≈ in ⊢renameᵀ's (env) case, NOT
-- with the strengthened entrywise hypothesis (a′) demanded.
⟦⟧ᴴ-ren≼≈ : intOfᴴ Γe Θe ≼≈ intOfᴴ Γe′ Θe
⟦⟧ᴴ-ren≼≈ = ≼≈abst ≼≈[]

------------------------------------------------------------------------
-- §8.  SITE 5 — MERGE'S MIDDLE TYPE, UP TO ≈.
--
-- MergeProbe's shapes (UnfoldProbe §5): Θm₁ = ↑W:=Z, Θm₂ = ↑Z:=ℕ and
-- Θm₁ ⊕ Θm₂ = Θm₁₂.  Nested, W's entry is the raw reveal variable Z;
-- merged, it is ℕ.  ¬⊕-int-raw says they are not equal and ¬⊕-retag-raw
-- says _≼_ cannot cross the gap.  Under (a″) they are ≈-equal, so Merge's
-- "retyping along unfolding" obligation COLLAPSES INTO _≼≈_.
------------------------------------------------------------------------

⊕-retag≈ : intOf (intOf [] Θm₂) Θm₁ ≼≈ intOf [] Θm₁₂
⊕-retag≈ = ≼≈rvld (≼≈rvld ≼≈[] ≈-refl) (≈unf refl)

-- and in the other direction, so the two interiors are ≈-INTERCHANGEABLE
⊕-retag≈-back : intOf [] Θm₁₂ ≼≈ intOf (intOf [] Θm₂) Θm₁
⊕-retag≈-back = ≼≈rvld (≼≈rvld ≼≈[] ≈-refl) (≈unf refl)

-- the middle-type comparison itself, isolated: raw W:=Z vs merged W:=ℕ
⊕-int≈ : (` 0) ≈Δ̄[ rvld `ℕ ∷ [] ] `ℕ
⊕-int≈ = ≈unf refl

-- the hybrid does not disturb it (both reps are expressible)
_ : intOfᴴ (intOfᴴ [] Θm₂) Θm₁ ≡ intOf (intOf [] Θm₂) Θm₁
_ = refl

------------------------------------------------------------------------
-- §9.  SITE 6 — IDEMPOTENCE AND COHERENCE OF THE MIXTURE.
--
-- The hybrid produces contexts with SOME raw and SOME unfolded entries
-- (Γq raw-chained vs Γq′ unfolded, §4).  Three checks: the mixture is
-- ≈-coherent in both directions, a second dual is a no-op on the already
-- unfolded side, and the two ROUTES to one piece of knowledge agree.
------------------------------------------------------------------------

-- ≈-COHERENCE: raw and unfolded are interchangeable as contexts
mix-≼≈ : Γq ≼≈ Γq′
mix-≼≈ = DualInt≈-Γq

mix-≼≈-back : Γq′ ≼≈ Γq
mix-≼≈-back = ≼≈rvld (≼≈rvld (≼≈rvld ≼≈[] ≈-refl) ≈-refl) (≈unf refl)

-- … whereas _≼_ orders them in NEITHER direction (UnfoldProbe's ¬≼-unfold
-- is the same phenomenon one slot wide)
¬mix-≼ : ¬ (Γq ≼ Γq′)
¬mix-≼ ()

¬mix-≼-back : ¬ (Γq′ ≼ Γq)
¬mix-≼-back ()

-- IDEMPOTENCE: dualising the already-unfolded context reproduces it exactly,
-- so no slot is ever unfolded twice and no raw/unfolded pair can arise for
-- one and the same slot.
mix-idem : intOfᴴ (intOfᴴ Γq′ Θq) (dualᴳ≈ Γq′ Θq) ≡ Γq′
mix-idem = refl

-- and the hybrid ENTRY map is idempotent in the rep at Pn's own slot
⟦⟧ᴴ-idem-Pn : ⟦ Γn ∣ Θn ⟧ᴴ 0 (unfoldᵉ Γn (` 0)) ≡ ⟦ Γn ∣ Θn ⟧ᴴ 0 (` 0)
⟦⟧ᴴ-idem-Pn = refl

-- TWO ROUTES.  In the raw regime the chained slot and the direct slot hold
-- DIFFERENT entries (UnfoldProbe's ¬routes-agree-raw) — but they are the
-- same knowledge up to ≈, read in the common ambient.
routes-agree≈ : (` 0) ≈Δ̄[ Γ2ʳ ] (` 2)
routes-agree≈ = ≈unf refl

routes-agree≈-Γq : (` 0) ≈Δ̄[ Γq ] (` 1)
routes-agree≈-Γq = ≈unf refl

------------------------------------------------------------------------
-- THE ABSTRACTION BARRIER SURVIVES THE HYBRID.  ⟦·⟧ᴴ changes only the
-- knowledge column, entry for entry, so the interior has the same SHAPE and
-- everything the sealed body reads about its context other than knowledge
-- (which variables exist, which types are well formed, which slots a nested
-- boundary blocks) is unchanged — reusing UnfoldProbe's length transports.
------------------------------------------------------------------------

len-revEntsᴴ : ∀ (Γ₁ : TCtx) Θ₁ j Ξ₁
             → length (revEntsᴴ Γ₁ Θ₁ j Ξ₁) ≡ revs Ξ₁
len-revEntsᴴ Γ₁ Θ₁ j []             = refl
len-revEntsᴴ Γ₁ Θ₁ j (rvl A ∷ Ξ₁)   =
  cong suc (len-revEntsᴴ Γ₁ Θ₁ (suc j) Ξ₁)
len-revEntsᴴ Γ₁ Θ₁ j (rvl⋆ ∷ Ξ₁)    =
  cong suc (len-revEntsᴴ Γ₁ Θ₁ (suc j) Ξ₁)
len-revEntsᴴ Γ₁ Θ₁ j (cnc X A ∷ Ξ₁) = len-revEntsᴴ Γ₁ Θ₁ j Ξ₁

intOfᴴ-len : ∀ (Γ₁ : TCtx) Θ₁
           → length (intOfᴴ Γ₁ Θ₁) ≡ length (intOf Γ₁ Θ₁)
intOfᴴ-len Γ₁ Θ₁ =
  trans (len-++ (revEntsᴴ Γ₁ Θ₁ 0 Θ₁) (dropN (cmax Θ₁) Γ₁))
    (trans (cong (_+ length (dropN (cmax Θ₁) Γ₁))
                 (trans (len-revEntsᴴ Γ₁ Θ₁ 0 Θ₁)
                        (sym (len-revEnts Θ₁ 0 Θ₁))))
           (sym (len-++ (revEnts Θ₁ 0 Θ₁) (dropN (cmax Θ₁) Γ₁))))

barrierᴴ-∋tv : ∀ (Γ₁ : TCtx) Θ₁ {X}
             → intOf Γ₁ Θ₁ ∋tv X → intOfᴴ Γ₁ Θ₁ ∋tv X
barrierᴴ-∋tv Γ₁ Θ₁ = ∋tv-len (sym (intOfᴴ-len Γ₁ Θ₁))

barrierᴴ-⊢ : ∀ (Γ₁ : TCtx) Θ₁ {A} → intOf Γ₁ Θ₁ ⊢ A → intOfᴴ Γ₁ Θ₁ ⊢ A
barrierᴴ-⊢ Γ₁ Θ₁ = ⊢-len (sym (intOfᴴ-len Γ₁ Θ₁))

barrierᴴ-baseS : ∀ (Γ₁ : TCtx) Θ₁ Θ₂
               → baseS Θ₂ (intOf Γ₁ Θ₁) ≡ baseS Θ₂ (intOfᴴ Γ₁ Θ₁)
barrierᴴ-baseS Γ₁ Θ₁ Θ₂ =
  baseS-len Θ₂ (intOf Γ₁ Θ₁) (intOfᴴ Γ₁ Θ₁) (sym (intOfᴴ-len Γ₁ Θ₁))

------------------------------------------------------------------------
-- §10.  VERDICT
--
-- SAFE, with the theorem naming it:
--   site 1a  the (a′) killer, reversed        DualCnc≈-Pc, DualCnc≈ᴴ-Pc
--   site 1b  Pc end to end                    DualInt≈-Γq, Reversal≈-argW′,
--                                             ⊢argW-rebuilt  (and the raw
--                                             comparison fails there:
--                                             ¬Reversal-argW′)
--   site 2b  Pn end to end, HYBRID            DualCnc≈ᴴ-Pn, DualInt≈-Pn,
--                                             ⊢redex-Pn, ⊢contractum-Pn
--   site 3   bad / bad₂ stay refuted          ¬⊢bad≈, ¬Reversal≈-bad₂,
--            near-bad admitted, far-bad not   ⊢near-bad, ¬Reversal≈-far-bad
--   site 4   ≈ transports where unfoldᵉ does   ≈-ren, UnfRen≈-idρ,
--            not                               UnfRen-vs-UnfRen≈
--   site 5   Merge middle type                ⊕-retag≈, ⊕-retag≈-back,
--                                             ⊕-int≈
--   site 6   mixture coherent / idempotent    mix-≼≈, mix-≼≈-back,
--                                             mix-idem, ⟦⟧ᴴ-idem-Pn,
--                                             routes-agree≈, barrierᴴ-*
--
-- MISMATCH, with the witness naming it:
--   site 2a  PURE (a″) does NOT fix Pn         ¬DualCnc≈-Pn-raw
--   the Λ-bound residue is untouched by
--            either regime                     ¬DualCnc≈ᴴ-E8
--   site 4b  the HYBRID entry does not
--            commute with renaming             ¬⟦⟧ᴴ-ren
--            — but it moves source-to-target
--              along _≼≈_, which ⊢retag≈ eats  ⟦⟧ᴴ-ren≼≈
--
-- So the HYBRID ENTRY FALLBACK IS REQUIRED for Pn, not avoidable: bwf↓'s
-- first premise is a LOOKUP (Γ ∋ X := A₀), and no congruence on the second
-- premise can supply a missing entry.  The mixture it creates is safe (§9),
-- and the hybrid's one cost is a ⊢retag≈ in ⊢renameᵀ's (env) case (§7b) —
-- strictly cheaper than (a′)'s entrywise ⊢renameᵀ hypothesis.
------------------------------------------------------------------------

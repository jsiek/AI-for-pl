module strong.notes.probes.DualCncProbe where

-- PROBE for the DualCnc≈ design plan (strong/DualDef.agda's residue (2);
-- notes/DualLicenseDesign.md §4; notes/DECISIONS.md's "(a″) PROBE VERDICT",
-- "STAR-CONCEAL PROBE VERDICT" and "AGENDA ITEM 1 IN DETAIL — R2 /
-- DualCnc").  Four machine-checked verdicts:
--
--   Q1  DualCnc≈ IS FALSE as stated — the Pn shape, with the hypothesis
--       Δ ∣ intOf Δ Θ ⊢ᵇ Θ DISCHARGED and ¬ CncLic … proven.
--   Q2  THE PER-SLOT CONFLICT: Pn and the rebuild collide ON THE SAME SLOT,
--       and the collision is a THEOREM, not an accident of the example —
--       at EVERY slot where copy-suppression would be needed, Δ's own entry
--       is rvld or xrvld (forced by Bwf's own conceal premises), and _≼≈_
--       has no clause putting `abst` above either.
--   Q3  the copy-suppression candidate dualᴳ′ (defined here): it DOES
--       license Pn's dual conceal, and it REFUTES DualInt≈ at Pn.
--   Q4  the "claims nothing NEW" alternative: REFUTED BY DESIGN.  Pn's dual
--       conceal and the ⊢3n-adv adversary are LITERALLY THE SAME INSTANCE
--       of (bwf-↓x) — same Γ, same Ψ, same Θ, same X, same A, same A′ — so
--       no premise stated over (bwf-↓x)'s data can license one and refuse
--       the other.  Machine-checked as an implication: the three DualDef
--       residues together type the adversary.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _<?_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; entAt; _⊢_; wf-ℕ; wf-𝔹; wf-var;
         _∋_:=_; here; skip-abst; skip-rvld; skip-xrvld;
         _∋_:=x_; herex; skipx; _∋tv_; here-abst; here-rvld; here-xrvld)
open import strong.Unfold using (_≈Δ̄⟨_⟩_; ≈unf; ≡→≈; ≈-refl)
open import strong.Boundary
  using (BEntry; rvl; rvl⋆; cnc; cnc⋆; BCtx; revs; cmax; ρᵇ; γᵇ; isConc;
         intOf; revEnts; ⟦_⟧ᴴ; starOnly; revStar; SkelEq; sk-var; sk-ℕ;
         Bwf; bwf[]; bwf↑; bwf⋆; bwf↓; bwf↓x; bwf⋆↓; _∣_⊢ᵇ_;
         Scoped; sc-var; sc-⇒; sc-ℕ; baseS; _∋ok_; hereᵒ; thereᵒ;
         Slot; ok; blk; Reversal≈;
         Term; `_; $_; ƛ_∙_; _·_; _⟪_,_⟫; _∣_⊢_⦂_; ⊢`; ⊢$; ⊢ƛ; env;
         Γ₈; Θ₈; Γn; Θn; Γz; Ξadv)
open import strong.BReduction
  using (repOf; copyRep; unfEnt; entᴳ; rvlsᴳ; cncOfRevs; dualᴳ; CncLic;
         _≼≈_; ≼≈[]; ≼≈abst; ≼≈xrvld; ≼≈rvld; Γp; Θp)
open import strong.DualDef
  using (entᴳ-⋆; DualRep≈; DualCnc≈; DualInt≈; bwf-dual)

------------------------------------------------------------------------
-- §0  Small entry facts used throughout.
------------------------------------------------------------------------

∋:=→entAt : ∀ {Δ X A} → Δ ∋ X := A → entAt Δ X ≡ rvld A
∋:=→entAt here           = refl
∋:=→entAt (skip-abst p)  = ∋:=→entAt p
∋:=→entAt (skip-rvld p)  = ∋:=→entAt p
∋:=→entAt (skip-xrvld p) = ∋:=→entAt p

∋:=x→entAt : ∀ {Δ X A} → Δ ∋ X :=x A → entAt Δ X ≡ xrvld A
∋:=x→entAt herex     = refl
∋:=x→entAt (skipx p) = ∋:=x→entAt p

abst≢rvld : ∀ {B} → abst ≡ rvld B → ⊥
abst≢rvld ()

abst≢xrvld : ∀ {B} → abst ≡ xrvld B → ⊥
abst≢xrvld ()

⋆≢rvl : ∀ {R} → rvl⋆ ≡ rvl R → ⊥
⋆≢rvl ()

------------------------------------------------------------------------
-- §1  Q1.  DualCnc≈ IS FALSE AS STATED.
--
-- The Pn shape, verbatim from strong/Boundary.agda:
--
--     Γn = Y:=ℕ , X:=ℕ            Θn = ↑Z:=Y , ↓X:=ℕ
--
-- The reveal ↑Z:=Y is REP-CARRYING and its raw reading is BLOCKED (↓X drops
-- everything up to X, Y included), so the interior entry is the
-- exterior-read Z:=ˣY — invisible to ∋:= .  But Y is AMBIENT KNOWLEDGE
-- (Γn ∋ 0 := ℕ), so the dual's copy at slot Y fires REP-CARRYINGLY and the
-- claims-nothing premise dies too.  BOTH disjuncts of CncLic are refuted.
------------------------------------------------------------------------

-- the hypothesis of DualCnc≈, DISCHARGED (Boundary.agda's own witness)
⊢Θn : Γn ∣ intOf Γn Θn ⊢ᵇ Θn
⊢Θn = bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ
           (bwf↑ (wf-var here-rvld) bwf[])

-- the exterior-read interior (the dual's exterior) — and it is EXACTLY the
-- context Γz over which strong/Boundary.agda plants the ⊢3n-adv adversary
Ψn : TCtx
Ψn = intOf Γn Θn

Ψn≡Γz : Ψn ≡ Γz
Ψn≡Γz = refl

-- the dual, computed
Θᵈn : BCtx
Θᵈn = dualᴳ Γn Θn

Θᵈn-is : Θᵈn ≡ rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
Θᵈn-is = refl

-- slot Y (= 0) is re-revealed REP-CARRYINGLY by the RAW copy: Γn's own
-- entry rvld ℕ is dfree, so the first guard fires (there is no need for the
-- second-chance copy here — the raw one already claims something)
copy-at-Y : entᴳ Γn Θn 0 1 ≡ rvl (copyRep 1 (revs Θn) `ℕ)
copy-at-Y = refl

-- the reveal's stored rep, which the dual's conceal carries
ρΘn0 : ρᵇ Θn 0 ≡ ` 0
ρΘn0 = refl

-- … and so the claims-nothing premise COMPUTES FALSE
¬starOnly-Pn : starOnly Θᵈn 0 (ρᵇ Θn 0) ≡ false
¬starOnly-Pn = refl

-- *** Q1's VERDICT ***  DualCnc≈'s per-reveal obligation at Pn, refuted.
-- inj₁ dies on the ∋:= lookup (the interior entry is xrvld, which ordinary
-- knowledge lookup does not see); inj₂ dies on starOnly.
¬DualCnc-Pn : ¬ (CncLic Ψn Θᵈn (0 + 0) (ρᵇ Θn 0))
¬DualCnc-Pn (inj₁ (A₀ , () , rev))
¬DualCnc-Pn (inj₂ (A′ , herex , () , sk))

-- so the STATEMENT strong.BPreservation is parameterised over is FALSE
¬DualCnc≈ : ¬ DualCnc≈
¬DualCnc≈ dc = ¬DualCnc-Pn (dc ⊢Θn 0 (s≤s z≤n))

------------------------------------------------------------------------
-- §1.1  THE SAME FAILURE DRIVEN BY THE SECOND-CHANCE COPY.
--
-- At Pn it is the RAW copy that re-reveals Y rep-carryingly (Γn's entry ℕ
-- is closed, so the first guard passes).  The design plan's shape — the
-- SECOND-CHANCE copy doing it — is Pn crossed with Pc: put Pn's reveal
-- ↑Z:=Y over Pc's CHAINED ambient Γp = Y:=Y′ , Y′:=𝔹 , X:=ℕ.  Now the raw
-- guard REFUSES (the rep ` 0 names another dropped slot) and the retry at
-- the rep unfolded in its own tail collapses Y to 𝔹 — so the dual copies
-- 𝔹 at slot Y, rep-carryingly, and starOnly dies exactly as at Pn.
------------------------------------------------------------------------

Δq : TCtx                    -- = Γp : Y:=Y′ , Y′:=𝔹 , X:=ℕ
Δq = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

Θq : BCtx                    -- ↑Z:=Y , ↓X:=ℕ  over that chained ambient
Θq = cnc 2 `ℕ ∷ rvl (` 0) ∷ []

⊢Θq : Δq ∣ intOf Δq Θq ⊢ᵇ Θq
⊢Θq = bwf↓ (skip-rvld (skip-rvld here)) (≡→≈ refl) wf-ℕ
           (bwf↑ (wf-var here-rvld) bwf[])

-- Z's entry is again the exterior-read one (Y is blocked)
Ψq-is : intOf Δq Θq ≡ xrvld (` 0) ∷ []
Ψq-is = refl

-- the RAW guard refuses at slot Y …
raw-refused-q : entᴳ Δq Θq 0 2 ≡ rvl (copyRep 2 (revs Θq) (unfEnt Δq 0 (` 0)))
raw-refused-q = refl

-- … and the SECOND-CHANCE copy fires, at the collapsed chain 𝔹
Θᵈq-is : dualᴳ Δq Θq ≡ rvl `𝔹 ∷ rvl `𝔹 ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
Θᵈq-is = refl

¬starOnly-q : starOnly (dualᴳ Δq Θq) 0 (ρᵇ Θq 0) ≡ false
¬starOnly-q = refl

¬DualCnc-q : ¬ (CncLic (intOf Δq Θq) (dualᴳ Δq Θq) (0 + 0) (ρᵇ Θq 0))
¬DualCnc-q (inj₁ (A₀ , () , rev))
¬DualCnc-q (inj₂ (A′ , herex , () , sk))

------------------------------------------------------------------------
-- §2  Q2.  THE PER-SLOT CONFLICT — and it is a THEOREM.
--
-- The suppression idea: at a slot named by some conceal rep of the emitted
-- conceal block, emit rvl⋆ instead of copying, so that starOnly holds.
-- A rep-less reveal contributes `abst` to the dual's interior, so
-- suppression at slot s puts `abst` at s in the REBUILD.
--
-- THE COLLISION.  _≼≈_ (BReduction) has FOUR clauses: ≼≈[], ≼≈abst (abst
-- below ANY entry), ≼≈xrvld (xrvld A below the SAME xrvld A), ≼≈rvld (rvld
-- below rvld, up to ≈).  There is NO clause putting rvld or xrvld below
-- `abst`.  So a rebuild that is `abst` at s forces Δ to be `abst` at s.
--
-- And at every slot the dual currently copies rep-carryingly, Δ is NOT
-- `abst`: either Θ conceals the slot — and then Bwf's own (bwf-↓)/(bwf-↓x)
-- premise hands back Δ ∋ s := B or Δ ∋ s :=x B — or the copy fired off
-- Δ's own `rvld B` entry.  The two demands therefore ALWAYS target the same
-- slot, whenever suppression is wanted at all.
------------------------------------------------------------------------

-- (2a) a conceal of Θ pins Δ's entry at that slot — this is where Bwf's own
-- premises do the work
conc-ent : ∀ {Δ Ψ Θ} Ξ → Bwf Δ Ψ Θ Ξ → ∀ s → isConc s Ξ ≡ true
         → (Σ Ty λ B → entAt Δ s ≡ rvld B)
         ⊎ (Σ Ty λ B → entAt Δ s ≡ xrvld B)
conc-ent []            bwf[]                s ()
conc-ent (rvl A ∷ Ξ)   (bwf↑ wfA b)         s ec = conc-ent Ξ b s ec
conc-ent (rvl⋆ ∷ Ξ)    (bwf⋆ b)             s ec = conc-ent Ξ b s ec
conc-ent (cnc⋆ X ∷ Ξ)  (bwf⋆↓ p b)          s ec = conc-ent Ξ b s ec
conc-ent (cnc X A ∷ Ξ) (bwf↓ p rev wfA b)   s ec with s ≟ X
conc-ent (cnc X A ∷ Ξ) (bwf↓ p rev wfA b)   s ec | yes refl =
  inj₁ (_ , ∋:=→entAt p)
conc-ent (cnc X A ∷ Ξ) (bwf↓ p rev wfA b)   s ec | no  _ =
  conc-ent Ξ b s ec
conc-ent (cnc X A ∷ Ξ) (bwf↓x p so sk wfA b) s ec with s ≟ X
conc-ent (cnc X A ∷ Ξ) (bwf↓x p so sk wfA b) s ec | yes refl =
  inj₂ (_ , ∋:=x→entAt p)
conc-ent (cnc X A ∷ Ξ) (bwf↓x p so sk wfA b) s ec | no  _ =
  conc-ent Ξ b s ec

-- (2b) a slot the dual copies REP-CARRYINGLY is never `abst` in Δ
copied-not-abst : ∀ {Δ} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
                → ∀ s k R → entᴳ Δ Θ s k ≡ rvl R → entAt Δ s ≡ abst → ⊥
copied-not-abst {Δ} Θ bwf s k R e ea = go (isConc s Θ) refl
  where
    go : ∀ c → isConc s Θ ≡ c → ⊥
    go true  ec with conc-ent Θ bwf s ec
    go true  ec | inj₁ (B , eb) = abst≢rvld  (trans (sym ea) eb)
    go true  ec | inj₂ (B , eb) = abst≢xrvld (trans (sym ea) eb)
    go false ec =
      ⋆≢rvl (trans (sym (entᴳ-⋆ Δ Θ s k ec ea)) e)

-- (2c) _≼≈_ never puts a KNOWLEDGE or exterior-read entry below `abst`
≼≈-abst : ∀ {Δ Δ'} → Δ ≼≈ Δ' → ∀ s → entAt Δ' s ≡ abst → entAt Δ s ≡ abst
≼≈-abst ≼≈[]           s       e  = refl
≼≈-abst (≼≈abst d)     zero    e  = refl
≼≈-abst (≼≈abst d)     (suc s) e  = ≼≈-abst d s e
≼≈-abst (≼≈xrvld d)    zero    ()
≼≈-abst (≼≈xrvld d)    (suc s) e  = ≼≈-abst d s e
≼≈-abst (≼≈rvld d ap)  zero    ()
≼≈-abst (≼≈rvld d ap)  (suc s) e  = ≼≈-abst d s e

-- *** Q2's VERDICT, in general ***  NO context satisfying the rebuild law
-- can be `abst` at a slot the dual copies.  Since suppression is exactly
-- "make that slot rep-less", and a rep-less reveal's interior entry is
-- `abst`, PER-SLOT COPY SUPPRESSION IS INCOHERENT AT EVERY SLOT WHERE IT
-- WOULD BE NEEDED.  The Pn demand and the Pc demand are not two slots that
-- might happen to be disjoint: they are the same slot, always.
no-per-slot-suppression :
  ∀ {Δ Δᵈ} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
  → ∀ s k R → entᴳ Δ Θ s k ≡ rvl R
  → Δ ≼≈ Δᵈ → entAt Δᵈ s ≡ abst → ⊥
no-per-slot-suppression Θ bwf s k R e di ed =
  copied-not-abst Θ bwf s k R e (≼≈-abst di s ed)

-- and the fact that closes the loop: a rep-LESS reveal's interior entry IS
-- `abst` (revEnts's rvl⋆ clause), at the slot it occupies
suppressed-is-abst : ∀ Θᵈ j Ξ (Γ : TCtx)
                   → entAt (revEnts Θᵈ j (rvl⋆ ∷ Ξ) ++ Γ) 0 ≡ abst
suppressed-is-abst Θᵈ j Ξ Γ = refl

------------------------------------------------------------------------
-- §3  Q3.  THE COPY-SUPPRESSION CANDIDATE, DEFINED AND RUN.
--
-- GUARD (decidable, birth-time, boundary-only): suppress the copy at slot s
-- exactly when s is named by the rep of some REP-CARRYING reveal of Θ —
-- i.e. by some ρᵇ Θ k, which is exactly the rep the emitted conceal block
-- cncOfRevs 0 Θ carries at its k-th conceal.  Nothing else changes.
------------------------------------------------------------------------

-- occ d s A : the free variable s occurs in A, under d binders
occ : ℕ → ℕ → Ty → Bool
occ d s (` X)   = if ⌊ X <? d ⌋ then false else ⌊ (X ∸ d) ≟ s ⌋
occ d s `ℕ      = false
occ d s `𝔹      = false
occ d s (A ⇒ B) = occ d s A ∨ occ d s B
occ d s (`∀ A)  = occ (suc d) s A

cncNames : BCtx → ℕ → Bool          -- some emitted conceal's rep names s
cncNames []            s = false
cncNames (rvl A ∷ Θ)   s = occ 0 s A ∨ cncNames Θ s
cncNames (rvl⋆ ∷ Θ)    s = cncNames Θ s
cncNames (cnc X A ∷ Θ) s = cncNames Θ s
cncNames (cnc⋆ X ∷ Θ)  s = cncNames Θ s

entᴳ′ : TCtx → BCtx → ℕ → ℕ → BEntry
entᴳ′ Γ Θ i k = if cncNames Θ i then rvl⋆ else entᴳ Γ Θ i k

rvlsᴳ′ : ℕ → ℕ → TCtx → BCtx → BCtx
rvlsᴳ′ zero    s Γ Θ = []
rvlsᴳ′ (suc k) s Γ Θ = entᴳ′ Γ Θ s k ∷ rvlsᴳ′ k (suc s) Γ Θ

dualᴳ′ : TCtx → BCtx → BCtx
dualᴳ′ Γ Θ = rvlsᴳ′ (cmax Θ) 0 Γ Θ ++ cncOfRevs 0 Θ

Θᵈ′n : BCtx
Θᵈ′n = dualᴳ′ Γn Θn

-- the guard fires at slot 0 (the conceal block's only rep, ` 0, names it)
-- and nowhere else, so the dual loses exactly the Y copy
Θᵈ′n-is : Θᵈ′n ≡ rvl⋆ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
Θᵈ′n-is = refl

-- (3a) THE LICENCE NOW FIRES.  starOnly computes true, the x-lookup is
-- there (revE-lo:=x's shape) and SkelEq comes from the xrep-stored pattern
-- (both reps are ` 0 on the nose at the dual's birth).
DualCnc′-Pn : CncLic Ψn Θᵈ′n (0 + 0) (ρᵇ Θn 0)
DualCnc′-Pn = inj₂ (` 0 , herex , refl , sk-var)

-- (3b) … AND THE REBUILD BREAKS, at the very same slot.  With the copy the
-- rebuild is EXACT (Γn on the nose); without it slot 0 is `abst` while Γn
-- has knowledge there, and _≼≈_ has no clause for that pair.
rebuild-Pn : intOf Ψn Θᵈn ≡ Γn
rebuild-Pn = refl

DualInt-Pn : Γn ≼≈ intOf Ψn Θᵈn
DualInt-Pn = ≼≈rvld (≼≈rvld ≼≈[] ≈-refl) ≈-refl

rebuild′-Pn : intOf Ψn Θᵈ′n ≡ abst ∷ rvld `ℕ ∷ []
rebuild′-Pn = refl

¬DualInt′-Pn : ¬ (Γn ≼≈ intOf Ψn Θᵈ′n)
¬DualInt′-Pn ()

-- the same refutation from the GENERAL theorem, so it is not an accident of
-- the example: slot 0 is copied (copy-at-Y) and Γn ≼≈ · forbids `abst` there
collision-Pn : ∀ {Δᵈ} → Γn ≼≈ Δᵈ → entAt Δᵈ 0 ≡ abst → ⊥
collision-Pn di ed =
  no-per-slot-suppression Θn ⊢Θn 0 1 (copyRep 1 (revs Θn) `ℕ) refl di ed

-- (3c) Pc's ORIGINAL site is untouched — Θp has NO reveals, so the emitted
-- conceal block is empty and the guard never fires.  That disjointness is a
-- coincidence of Θp, though, not the reason.
Pc-untouched : dualᴳ′ Γp Θp ≡ dualᴳ Γp Θp
Pc-untouched = refl

-- (3d) *** THE ONE-SLOT WITNESS Q2 ASKS FOR ***  At Δq/Θq (§1.1) the SAME
-- slot 0 is needed BOTH ways: the conceal rep ` 0 names it (so Pn's licence
-- wants it rep-less) AND its SECOND-CHANCE copy is exactly what makes the
-- Pc-style rebuild work — the copied 𝔹 is Δq's chain Y:=Y′ collapsed, one
-- unfolding away, which is precisely what _≼≈_ absorbs (BReduction's
-- Γp / Γp′).  With the copy the rebuild holds; with it suppressed the slot
-- is `abst` and _≼≈_ has nothing.
rebuild-q : intOf (intOf Δq Θq) (dualᴳ Δq Θq)
          ≡ rvld `𝔹 ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []
rebuild-q = refl

DualInt-q : Δq ≼≈ intOf (intOf Δq Θq) (dualᴳ Δq Θq)
DualInt-q = ≼≈rvld (≼≈rvld (≼≈rvld ≼≈[] ≈-refl) ≈-refl) (≈unf refl)

Θᵈ′q-is : dualᴳ′ Δq Θq ≡ rvl⋆ ∷ rvl `𝔹 ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
Θᵈ′q-is = refl

DualCnc′-q : CncLic (intOf Δq Θq) (dualᴳ′ Δq Θq) (0 + 0) (ρᵇ Θq 0)
DualCnc′-q = inj₂ (` 0 , herex , refl , sk-var)

rebuild′-q : intOf (intOf Δq Θq) (dualᴳ′ Δq Θq)
           ≡ abst ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []
rebuild′-q = refl

¬DualInt′-q : ¬ (Δq ≼≈ intOf (intOf Δq Θq) (dualᴳ′ Δq Θq))
¬DualInt′-q ()

------------------------------------------------------------------------
-- §4  Q4.  "CLAIMS NOTHING NEW" — REFUTED BY DESIGN.
--
-- THE STRUCTURAL FACT FIRST.  Pn's dual conceal and strong/Boundary.agda's
-- ⊢3n-adv adversary are the SAME instance of (bwf-↓x).  The adversary is
-- planted over Γz = E★′'s sealed interior; Pn's dual is a boundary over
-- intOf Γn Θn — AND THOSE TWO CONTEXTS ARE EQUAL (Ψn≡Γz above).  Both
-- conceal index 0 at the rep ` 0 against the x-entry 0 :=ˣ ` 0, and in both
-- the named slot is the boundary's own reveal at the rep ℕ.  So every datum
-- (bwf-↓x) can see — Γ, Ψ, Θ, X, A, A′ — coincides.
--
-- Consequence, machine-checked below: the three DualDef residues TOGETHER
-- type advᴰ, a ℕ literal exported at the abstract Z over Γz, which is the
-- ⊢3n-adv shape strong/Boundary.agda permanently refutes (¬⊢adv).
------------------------------------------------------------------------

Ψᵈn : TCtx
Ψᵈn = intOf Ψn Θᵈn

Ψᵈn-is : Ψᵈn ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
Ψᵈn-is = refl

-- the adversary, built on PN'S OWN DUAL (Boundary.agda's Ξadv is the same
-- boundary with one fewer reveal)
advᴰ : Term
advᴰ = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ Θᵈn , ` 2 ⟫

Ξadv-is : Ξadv ≡ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
Ξadv-is = refl

-- the inner half types outright (the dual's rebuilt slot 0 really is ℕ)
adv-inner : Ψᵈn ∣ [] ⊢ ($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫ ⦂ ` 0
adv-inner = env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$

-- … so the ONLY missing piece is the dual's own well-formedness
advᴰ-from-bwf : Ψn ∣ Ψᵈn ⊢ᵇ Θᵈn → Ψn ∣ [] ⊢ advᴰ ⦂ ` 0
advᴰ-from-bwf b = env b (sc-var (thereᵒ (thereᵒ hereᵒ))) adv-inner

-- *** THE SOUNDNESS ALARM ***  the three residues produce exactly that
advᴰ-from-residues : DualRep≈ → DualCnc≈ → DualInt≈ → Ψn ∣ [] ⊢ advᴰ ⦂ ` 0
advᴰ-from-residues dr dc di = advᴰ-from-bwf (bwf-dual dr dc di ⊢Θn)

-- … and advᴰ is REFUTED today, by the same premise that refutes ⊢3n-adv
¬advᴰ : ¬ (Ψn ∣ [] ⊢ advᴰ ⦂ ` 0)
¬advᴰ (env (bwf↑ _ (bwf↑ _ (bwf↓  () _ _ _)))       _ _)
¬advᴰ (env (bwf↑ _ (bwf↑ _ (bwf↓x herex () _ _ _))) _ _)

-- so DualCnc≈ fails for a REASON, not by an index accident: it is
-- inconsistent with the standing adversary refutation
¬DualCnc≈-soundness : DualRep≈ → DualInt≈ → ¬ DualCnc≈
¬DualCnc≈-soundness dr di dc = ¬advᴰ (advᴰ-from-residues dr dc di)

------------------------------------------------------------------------
-- §4.1  THE CANDIDATE, STATED PRECISELY, AND RUN.
--
--   starOnly′ (= CNN below):  every free variable X of A either
--     (⋆)  names a REP-LESS reveal of Θᵈ                     — today's rule
--     (b)  is bound under A's own binders                    — hygiene
--     (kn) names a REP-CARRYING reveal of Θᵈ whose STORED REP ρᵇ Θᵈ X
--          SkelEq-agrees with the dual interior's own knowledge at X.
--
-- (kn) is the "claims nothing NEW" clause: the rep may name a slot the
-- interior knows, provided it repeats what the knowledge chain already
-- says rather than asserting something fresh.
------------------------------------------------------------------------

data CNN (Ψᵈ : TCtx) (Θᵈ : BCtx) : ℕ → Ty → Set where
  cnn-⋆  : ∀ {d X} → revStar Θᵈ (X ∸ d) ≡ true → CNN Ψᵈ Θᵈ d (` X)
  cnn-bd : ∀ {d X} → X < d                     → CNN Ψᵈ Θᵈ d (` X)
  cnn-kn : ∀ {d X B} → Ψᵈ ∋ (X ∸ d) := B
         → SkelEq (ρᵇ Θᵈ (X ∸ d)) B            → CNN Ψᵈ Θᵈ d (` X)
  cnn-ℕ  : ∀ {d}                               → CNN Ψᵈ Θᵈ d `ℕ
  cnn-𝔹  : ∀ {d}                               → CNN Ψᵈ Θᵈ d `𝔹
  cnn-⇒  : ∀ {d A B} → CNN Ψᵈ Θᵈ d A → CNN Ψᵈ Θᵈ d B
                                               → CNN Ψᵈ Θᵈ d (A ⇒ B)
  cnn-∀  : ∀ {d A} → CNN Ψᵈ Θᵈ (suc d) A       → CNN Ψᵈ Θᵈ d (`∀ A)

-- (4a) it DOES license Pn: the dual's reveal 0 stores ℕ and the rebuild
-- knows slot 0 := ℕ, so the rep ` 0 claims nothing new
CNN-Pn : CNN Ψᵈn Θᵈn 0 (ρᵇ Θn 0)
CNN-Pn = cnn-kn here sk-ℕ

-- (4b) *** AND IT ADMITS THE ADVERSARY ***, by the SAME constructor.
-- Boundary.agda's Ξadv over Γz: its interior is rvld ℕ ∷ [], its reveal 0
-- stores ℕ, and its conceal's rep is ` 0.  Nothing distinguishes it.
CNN-adv : CNN (intOf Γz Ξadv) Ξadv 0 (` 0)
CNN-adv = cnn-kn here sk-ℕ

-- and on PN'S OWN dual planted over Γz — which IS the adversary's home,
-- since Γz ≡ Ψn — the very licence used at (4a) is the one at (4b)
CNN-advᴰ : CNN Ψᵈn Θᵈn 0 (` 0)
CNN-advᴰ = CNN-Pn

-- (4c) the WEAKER reading — compare the stored rep against the RECORDED
-- x-rep A′ instead of against the interior's knowledge — does not license
-- Pn at all: ρᵇ Θᵈn 0 is the closed ℕ and A′ is the variable ` 0
¬CNN-vs-xrep-Pn : ¬ (SkelEq (ρᵇ Θᵈn 0) (` 0))
¬CNN-vs-xrep-Pn ()

-- (4d) THE D1 LESSON, as a type-level observation.  starOnly's type is
-- `BCtx → ℕ → Ty → Bool` — it mentions NO context, which is exactly why it
-- is renaming- and retag-stable (Boundary.agda's D2 note).  CNN's (kn)
-- clause is a CONTEXT lookup Ψᵈ ∋ X := B against a rep ρᵇ Θᵈ X that renᴮ
-- moves by the induced INTERIOR renaming while a context renaming moves the
-- entry by the exterior ρ — the same split that refuted the ≡ / ≈Δ̄ rep
-- comparison at (bwf-↓x) (D1Probe §2.2, InstallGauntlet §7b).  So CNN is
-- non-stable by construction as well as unsound by (4b): REFUTED BY DESIGN,
-- on the D1 precedent, not half-endorsed.
starOnly-mentions-no-context : BCtx → ℕ → Ty → Bool
starOnly-mentions-no-context = starOnly

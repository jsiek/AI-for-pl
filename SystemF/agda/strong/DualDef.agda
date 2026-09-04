module strong.DualDef where

-- The AMBIENT DUAL's well-formedness, up to the unfolding congruence, and
-- exactly which part of it is still open (notes/DualLicenseDesign.md §4;
-- the "(a″) PROBE VERDICT" and "STAR-CONCEAL PROBE VERDICT" blocks of
-- notes/DECISIONS.md).
--
-- Wrap's preservation case needs two facts about  Θᵈ = dualᴳ Δ Θ  beyond the
-- two face laws (which ARE theorems — ρᵇ-dual-ty / γᵇ-dual-ty):
--
--   (i)  Θᵈ is a WELL-FORMED boundary over the exterior intOf Δ Θ, so that
--        (env) can be applied to the dual-wrapped argument;
--   (ii) Θᵈ's INTERIOR rebuilds Δ, at least up to _≼≈_ (abstract and
--        exterior-read below anything, knowledge up to ≈), so that the
--        argument W — typed at Δ — retypes there.
--
-- WHAT THIS INSTALL PROVED, and what it did not:
--
--   * repOf-wf / dual-rep-conc — a conceal rep of Θ is well formed in Θ's
--     interior, which is the dual's exterior, so the dual's reveal at a
--     CONCEALED slot is well formed.  PROVEN (unchanged).
--   * bwf-dualᴳ — the whole dual is well formed as soon as the reveal-rep
--     residue and the conceal block are supplied.  PROVEN, and the conceal
--     block's assembly (strong.BReduction's bwf-cncOfRevs) is proven too.
--   * cnc⋆-licensed — the ⋆ half of the conceal block needs NOTHING: every
--     reveal slot of Θ exists in Θ's interior, whatever entry it carries,
--     so the dual's cnc⋆ for a rep-LESS reveal is licensed outright.
--     PROVEN here (StarConcealProbe §5's case (3), in general).
--   * dual-rep-ok — the dual's copied reveal reps are well formed in its
--     interior as soon as DualInt≈ holds, since the rebuild ≼≈-dominates Δ
--     and bwf↑ already certified them there.  PROVEN here.
--
--   * DualRep≈ (BlkRepWf≈) — RESIDUE.  At a slot the boundary drops without
--     concealing and which Δ REVEALS, the dual copies Δ's own entry
--     `rvld B`; B is a type over Δ ↓ i, and its well-formedness THERE is a
--     fact about ⊢ Δ, which the preservation statement does not carry
--     (adding it would in turn demand ⊢ intOf Δ Θ — the same obligation one
--     level down).  Λ-BOUND and EXTERIOR-READ blocked slots are fine: the
--     dual emits the rep-less reveal rvl⋆, which carries no premise at all.
--     The statement now has TWO conjuncts, one per copy attempt: the raw
--     copy and the SECOND-CHANCE copy at the rep unfolded in its own tail
--     (BReduction's entᴳ / unfEnt), which is what recovers Pc's chained
--     knowledge (BReduction's Γp / Γp′).
--
--   * DualCnc≈ — RESIDUE, and the sharpest one.  Per rep-carrying reveal at
--     interior slot j with rep A, the dual's conceal needs ONE of
--       (a) ordinary knowledge:  intOf Δ Θ ∋ j := B  with the read-back of A
--           through Θᵈ ≈-equal to that knowledge (Reversal≈) — available
--           exactly when the RAW reading of A was expressible, and then the
--           read-back resolves through Θᵈ's own copied reveal;
--       (b) exterior-read knowledge:  intOf Δ Θ ∋ j :=x A′ (which the
--           entry map always supplies for a rep-carrying reveal whose raw
--           reading is blocked) PLUS "A claims nothing" — every variable of
--           A names a REP-LESS reveal of Θᵈ.
--     (b)'s lookup is a theorem (revE-lo:=x below); its claims-nothing half
--     is not, and E★′ is exactly where it holds (the dual re-reveals the
--     Λ-bound Y with ↑Y:⋆) while Pn is exactly where it fails (the dual
--     re-reveals Y at the KNOWLEDGE ℕ, so the rep claims something).  Pn was
--     closed by the AMBIENT unfold retry in the probes; that retry is gone
--     (strong.Boundary's flagged deviation — it breaks both ⊢renameᵀ and
--     ⊢retag), so Pn's shape now lives here.
--
--   * DualInt≈ — RESIDUE.  The rebuild law.  Its Λ-bound slots are exact by
--     construction and a CONCEALED or COPIED slot is exact (or one
--     unfolding away, which _≼≈_ absorbs — BReduction's Γp/Γp′); what is
--     open is a slot whose copy BOTH guards refuse, and an EXTERIOR-READ
--     slot of Δ, which the dual re-reveals rep-lessly and so rebuilds as
--     `abst` (notes/DualLicenseDesign.md §4's third bullet).
--
-- strong.BPreservation is parameterised over the three (the repo's `…Def`
-- convention, as strong.Progress is over strong.ProgressDef).

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import Data.Nat.Properties using (_≟_)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_; _⊢_; wf-ℕ; entAt;
         _∋_:=_; here; skip-abst; skip-rvld; skip-xrvld;
         _∋_:=x_; herex; skipx; _∋tv_)
open import strong.Unfold using (_≈Δ̄⟨_⟩_)
open import strong.Boundary
open import strong.BReduction
  using (repOf; copyRep; unfEnt; entᴳ; rvlsᴳ; cncOfRevs; dualᴳ;
         bwf-++; bwf-ent; bwf-rvlsᴳ; bwf-cncOfRevs; CncLic;
         revE-lo; ent-here; ent-skip; _≼≈_; ≼≈-⊢)

private
  variable
    Δ Δ' Ψ : TCtx
    Θ Ξ : BCtx

------------------------------------------------------------------------
-- PROVEN.  A conceal rep lives in the interior, which is the dual's
-- exterior — so the dual's reveal at a CONCEALED slot is well formed.
------------------------------------------------------------------------

repOf-wf : ∀ Ξ → Bwf Δ Ψ Θ Ξ → ∀ i → Ψ ⊢ repOf i Ξ
repOf-wf []            bwf[]                i = wf-ℕ
repOf-wf (rvl A ∷ Ξ)   (bwf↑ wfA b)         i = repOf-wf Ξ b i
repOf-wf (rvl⋆ ∷ Ξ)    (bwf⋆ b)             i = repOf-wf Ξ b i
repOf-wf (cnc⋆ X ∷ Ξ)  (bwf⋆↓ p b)          i = repOf-wf Ξ b i
repOf-wf (cnc X A ∷ Ξ) (bwf↓ p rev wfA b)   i with i ≟ X
repOf-wf (cnc X A ∷ Ξ) (bwf↓ p rev wfA b)   i | yes _ = wfA
repOf-wf (cnc X A ∷ Ξ) (bwf↓ p rev wfA b)   i | no  _ = repOf-wf Ξ b i
repOf-wf (cnc X A ∷ Ξ) (bwf↓x p so wfA b)   i with i ≟ X
repOf-wf (cnc X A ∷ Ξ) (bwf↓x p so wfA b)   i | yes _ = wfA
repOf-wf (cnc X A ∷ Ξ) (bwf↓x p so wfA b)   i | no  _ = repOf-wf Ξ b i

rvl-inj : ∀ {A B} → rvl A ≡ rvl B → A ≡ B
rvl-inj refl = refl

⋆≢rvl : ∀ {R} → rvl⋆ ≡ rvl R → ⊥
⋆≢rvl ()

-- what the dual emits at a slot it does NOT conceal, by Δ's own entry
entᴳ-⋆ : ∀ (Δ : TCtx) Θ s k → isConc s Θ ≡ false → entAt Δ s ≡ abst
       → entᴳ Δ Θ s k ≡ rvl⋆
entᴳ-⋆ Δ Θ s k ec ee with isConc s Θ | ec
entᴳ-⋆ Δ Θ s k ec ee | true  | ()
entᴳ-⋆ Δ Θ s k ec ee | false | _ with entAt Δ s | ee
entᴳ-⋆ Δ Θ s k ec ee | false | _ | abst    | _  = refl
entᴳ-⋆ Δ Θ s k ec ee | false | _ | rvld B  | ()
entᴳ-⋆ Δ Θ s k ec ee | false | _ | xrvld B | ()

-- an EXTERIOR-READ blocked slot goes the same way: its rep lives one level
-- further out than the dual's exterior, so there is nothing to copy
entᴳ-x : ∀ (Δ : TCtx) Θ s k B → isConc s Θ ≡ false → entAt Δ s ≡ xrvld B
       → entᴳ Δ Θ s k ≡ rvl⋆
entᴳ-x Δ Θ s k B ec ee with isConc s Θ | ec
entᴳ-x Δ Θ s k B ec ee | true  | ()
entᴳ-x Δ Θ s k B ec ee | false | _ with entAt Δ s | ee
entᴳ-x Δ Θ s k B ec ee | false | _ | abst    | ()
entᴳ-x Δ Θ s k B ec ee | false | _ | rvld C  | ()
entᴳ-x Δ Θ s k B ec ee | false | _ | xrvld C | _ = refl

-- the RAW copy happens when the first guard holds …
entᴳ-B : ∀ (Δ : TCtx) Θ s k B → isConc s Θ ≡ false → entAt Δ s ≡ rvld B
       → dfree 0 k B ≡ true
       → entᴳ Δ Θ s k ≡ rvl (copyRep k (revs Θ) B)
entᴳ-B Δ Θ s k B ec ee eg with isConc s Θ | ec
entᴳ-B Δ Θ s k B ec ee eg | true  | ()
entᴳ-B Δ Θ s k B ec ee eg | false | _ with entAt Δ s | ee
entᴳ-B Δ Θ s k B ec ee eg | false | _ | abst    | ()
entᴳ-B Δ Θ s k B ec ee eg | false | _ | xrvld C | ()
entᴳ-B Δ Θ s k B ec ee eg | false | _ | rvld C  | refl
  with dfree 0 k C | eg
entᴳ-B Δ Θ s k B ec ee eg | false | _ | rvld C | refl | true  | _  = refl
entᴳ-B Δ Θ s k B ec ee eg | false | _ | rvld C | refl | false | ()

-- … and the SECOND-CHANCE copy (the rep unfolded in its own tail) when the
-- first guard fails and the second holds — this is what recovers a CHAINED
-- rep, which used to be lost to rvl⋆ (BReduction's Γp / Γp′).
entᴳ-U : ∀ (Δ : TCtx) Θ s k B → isConc s Θ ≡ false → entAt Δ s ≡ rvld B
       → dfree 0 k B ≡ false → dfree 0 k (unfEnt Δ s B) ≡ true
       → entᴳ Δ Θ s k ≡ rvl (copyRep k (revs Θ) (unfEnt Δ s B))
entᴳ-U Δ Θ s k B ec ee eg eu with isConc s Θ | ec
entᴳ-U Δ Θ s k B ec ee eg eu | true  | ()
entᴳ-U Δ Θ s k B ec ee eg eu | false | _ with entAt Δ s | ee
entᴳ-U Δ Θ s k B ec ee eg eu | false | _ | abst    | ()
entᴳ-U Δ Θ s k B ec ee eg eu | false | _ | xrvld C | ()
entᴳ-U Δ Θ s k B ec ee eg eu | false | _ | rvld C  | refl
  with dfree 0 k C | eg
entᴳ-U Δ Θ s k B ec ee eg eu | false | _ | rvld C | refl | true  | ()
entᴳ-U Δ Θ s k B ec ee eg eu | false | _ | rvld C | refl | false | _
  with dfree 0 k (unfEnt Δ s C) | eu
entᴳ-U Δ Θ s k B ec ee eg eu
  | false | _ | rvld C | refl | false | _ | true  | _  = refl
entᴳ-U Δ Θ s k B ec ee eg eu
  | false | _ | rvld C | refl | false | _ | false | ()

-- both guards refuse: the knowledge is lost to the rep-less reveal
entᴳ-B⋆ : ∀ (Δ : TCtx) Θ s k B → isConc s Θ ≡ false → entAt Δ s ≡ rvld B
        → dfree 0 k B ≡ false → dfree 0 k (unfEnt Δ s B) ≡ false
        → entᴳ Δ Θ s k ≡ rvl⋆
entᴳ-B⋆ Δ Θ s k B ec ee eg eu with isConc s Θ | ec
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | true  | ()
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | false | _ with entAt Δ s | ee
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | false | _ | abst    | ()
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | false | _ | xrvld C | ()
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | false | _ | rvld C  | refl
  with dfree 0 k C | eg
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | false | _ | rvld C | refl | true  | ()
entᴳ-B⋆ Δ Θ s k B ec ee eg eu | false | _ | rvld C | refl | false | _
  with dfree 0 k (unfEnt Δ s C) | eu
entᴳ-B⋆ Δ Θ s k B ec ee eg eu
  | false | _ | rvld C | refl | false | _ | true  | ()
entᴳ-B⋆ Δ Θ s k B ec ee eg eu
  | false | _ | rvld C | refl | false | _ | false | _ = refl

dual-rep-conc : ∀ Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → ∀ k i → isConc i Θ ≡ true
              → ∀ R → entᴳ Δ Θ i k ≡ rvl R
              → intOf Δ Θ ⊢ R
dual-rep-conc {Δ = Δ} Θ bwf k i c R e
  with isConc i Θ | c
dual-rep-conc {Δ = Δ} Θ bwf k i c R e | true  | _ =
  subst (λ T → intOf Δ Θ ⊢ T) (rvl-inj e) (repOf-wf Θ bwf i)
dual-rep-conc {Δ = Δ} Θ bwf k i c R e | false | ()

------------------------------------------------------------------------
-- PROVEN.  The ⋆ HALF OF THE CONCEAL BLOCK NEEDS NOTHING.  Every reveal
-- slot of Θ exists in Θ's interior, whatever entry the fallback chain gave
-- it, so the dual's cnc⋆ for a rep-LESS reveal is licensed outright
-- (StarConcealProbe §5, cnc⋆-licensed — here in general).
------------------------------------------------------------------------

cnc⋆-licensed : ∀ (Δ₀ : TCtx) Θ j → j < revs Θ → intOf Δ₀ Θ ∋tv j
cnc⋆-licensed Δ₀ Θ j lt = revE-lo Θ 0 Θ j lt

------------------------------------------------------------------------
-- PROVEN.  The EXTERIOR-READ lookup the x-clause needs is always there: a
-- rep-carrying reveal whose raw reading is blocked gets exactly the entry
-- `xrvld A`, and the interior's reveal block holds it at that slot.
------------------------------------------------------------------------

revE-lo:=x : ∀ Θ j Ξ {Γ : TCtx} {A} → expr Θ j A ≡ false
           → (revEnts Θ j (rvl A ∷ Ξ) ++ Γ) ∋ 0 :=x A
revE-lo:=x Θ j Ξ {A = A} ef
  with expr Θ j A | ef
revE-lo:=x Θ j Ξ {A = A} ef | false | _ = herex

------------------------------------------------------------------------
-- RESIDUE (1).  The reveal the dual emits at a slot that Θ drops without
-- concealing and that Δ REVEALS: it copies Δ's entry `rvld B` into the
-- dual's PLAIN exterior by copyRep — raw when the first guard permits, and
-- otherwise at the rep UNFOLDED in its own tail.
------------------------------------------------------------------------

BlkRepWf≈ : TCtx → BCtx → Set
BlkRepWf≈ Δ Θ = ∀ k i B → isConc i Θ ≡ false → entAt Δ i ≡ rvld B
  → (dfree 0 k B ≡ true → intOf Δ Θ ⊢ copyRep k (revs Θ) B)
  × (dfree 0 k B ≡ false → dfree 0 k (unfEnt Δ i B) ≡ true
     → intOf Δ Θ ⊢ copyRep k (revs Θ) (unfEnt Δ i B))

------------------------------------------------------------------------
-- PROVEN.  Given (1) and the conceal block, the whole dual is well formed.
------------------------------------------------------------------------

bwf-dualᴳ : ∀ {Δ Δ'} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → BlkRepWf≈ Δ Θ
  → Bwf (intOf Δ Θ) Δ' (dualᴳ Δ Θ) (cncOfRevs 0 Θ)
  → intOf Δ Θ ∣ Δ' ⊢ᵇ dualᴳ Δ Θ
bwf-dualᴳ {Δ} {Δ'} Θ bwf hblk bcnc =
  bwf-rvlsᴳ (cmax Θ) 0 Δ Θ (cncOfRevs 0 Θ) hrvl bcnc
  where
    hrvl : ∀ k s R → entᴳ Δ Θ s k ≡ rvl R → intOf Δ Θ ⊢ R
    hrvl k s R e = go (isConc s Θ) refl
      where
        go : ∀ b → isConc s Θ ≡ b → intOf Δ Θ ⊢ R
        go true  ec = dual-rep-conc Θ bwf k s ec R e
        go false ec = blkcase (entAt Δ s) refl
          where
            blkcase : ∀ (E : TyEntry) → entAt Δ s ≡ E → intOf Δ Θ ⊢ R
            blkcase abst      ee =
              ⊥-elim (⋆≢rvl (trans (sym (entᴳ-⋆ Δ Θ s k ec ee)) e))
            blkcase (xrvld B) ee =
              ⊥-elim (⋆≢rvl (trans (sym (entᴳ-x Δ Θ s k B ec ee)) e))
            blkcase (rvld B)  ee = guardcase (dfree 0 k B) refl
              where
                guardcase : ∀ g → dfree 0 k B ≡ g → intOf Δ Θ ⊢ R
                guardcase true  eg =
                  subst (λ T → intOf Δ Θ ⊢ T)
                        (rvl-inj
                          (trans (sym (entᴳ-B Δ Θ s k B ec ee eg)) e))
                        (proj₁ (hblk k s B ec ee) eg)
                guardcase false eg =
                  ucase (dfree 0 k (unfEnt Δ s B)) refl
                  where
                    ucase : ∀ u → dfree 0 k (unfEnt Δ s B) ≡ u
                          → intOf Δ Θ ⊢ R
                    ucase true  eu =
                      subst (λ T → intOf Δ Θ ⊢ T)
                            (rvl-inj
                              (trans (sym (entᴳ-U Δ Θ s k B ec ee eg eu))
                                     e))
                            (proj₂ (hblk k s B ec ee) eg eu)
                    ucase false eu =
                      ⊥-elim (⋆≢rvl
                        (trans (sym (entᴳ-B⋆ Δ Θ s k B ec ee eg eu)) e))

------------------------------------------------------------------------
-- PROVEN.  The dual's conceal block also needs each reveal's STORED rep to
-- be well formed in the dual's INTERIOR.  bwf↑ certified it in Δ, and the
-- rebuild ≼≈-dominates Δ, so DualInt≈ carries it across.
------------------------------------------------------------------------

rep-wf-lo : ∀ {Δ₀ Ψ₀ : TCtx} Θ Ξ → Bwf Δ₀ Ψ₀ Θ Ξ
          → ∀ k → k < revs Ξ → Δ₀ ⊢ ρᵇ Ξ k
rep-wf-lo Θ []            bwf[]              k       ()
rep-wf-lo Θ (rvl A ∷ Ξ)   (bwf↑ wfA b)       zero    lt = wfA
rep-wf-lo Θ (rvl A ∷ Ξ)   (bwf↑ wfA b) (suc k) (s≤s lt) =
  rep-wf-lo Θ Ξ b k lt
rep-wf-lo Θ (rvl⋆ ∷ Ξ)    (bwf⋆ b)           zero    lt = wf-ℕ
rep-wf-lo Θ (rvl⋆ ∷ Ξ)    (bwf⋆ b)     (suc k) (s≤s lt) =
  rep-wf-lo Θ Ξ b k lt
rep-wf-lo Θ (cnc X A ∷ Ξ) (bwf↓ p rev wfA b) k       lt =
  rep-wf-lo Θ Ξ b k lt
rep-wf-lo Θ (cnc X A ∷ Ξ) (bwf↓x p so wfA b) k       lt =
  rep-wf-lo Θ Ξ b k lt
rep-wf-lo Θ (cnc⋆ X ∷ Ξ)  (bwf⋆↓ p b)        k       lt =
  rep-wf-lo Θ Ξ b k lt

dual-rep-ok : ∀ {Δ₀ : TCtx} Θ → Δ₀ ∣ intOf Δ₀ Θ ⊢ᵇ Θ
  → Δ₀ ≼≈ intOf (intOf Δ₀ Θ) (dualᴳ Δ₀ Θ)
  → ∀ k → k < revs Θ
  → intOf (intOf Δ₀ Θ) (dualᴳ Δ₀ Θ) ⊢ ρᵇ Θ k
dual-rep-ok Θ bwf di k lt = ≼≈-⊢ di (rep-wf-lo Θ Θ bwf k lt)

------------------------------------------------------------------------
-- THE THREE STATEMENTS strong.BPreservation is parameterised over.
------------------------------------------------------------------------

-- (1) every copied knowledge rep is well formed in the dual's exterior
DualRep≈ : Set
DualRep≈ = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → BlkRepWf≈ Δ Θ

-- (2) the dual's CONCEAL block: per rep-carrying reveal, EITHER the
-- interior's ordinary knowledge meets the read-back of the stored rep
-- (bwf-↓, up to ≈), OR the interior's exterior-read mark licenses it and
-- the rep claims nothing (bwf-↓x).  The ⋆ half is a theorem
-- (cnc⋆-licensed) and the rep well-formedness half is a theorem given (3)
-- (dual-rep-ok), so this is exactly the licensing residue.
DualCnc≈ : Set
DualCnc≈ = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
         → ∀ k → k < revs Θ
         → CncLic (intOf Δ Θ) (dualᴳ Δ Θ) (0 + k) (ρᵇ Θ k)

-- (3) the CONTEXT law: the dual's interior rebuilds the exterior, up to
-- _≼≈_ (abstract and exterior-read below anything, knowledge up to the
-- unfolding congruence)
DualInt≈ : Set
DualInt≈ = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
         → Δ ≼≈ intOf (intOf Δ Θ) (dualᴳ Δ Θ)

------------------------------------------------------------------------
-- PROVEN.  The three assemble into the dual's well-formedness — so the
-- residue really is only the three statements above.
------------------------------------------------------------------------

bwf-dual : DualRep≈ → DualCnc≈ → DualInt≈
  → ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
  → intOf Δ Θ ∣ intOf (intOf Δ Θ) (dualᴳ Δ Θ) ⊢ᵇ dualᴳ Δ Θ
bwf-dual dr dc di {Δ} {Θ} bwf =
  bwf-dualᴳ Θ bwf (dr bwf)
    (bwf-cncOfRevs 0 Θ (dc bwf)
      (λ k lt → dual-rep-ok Θ bwf (di bwf) k lt)
      (λ k lt → cnc⋆-licensed Δ Θ (0 + k) lt))

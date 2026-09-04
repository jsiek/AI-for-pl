module strong.DualDef where

-- The AMBIENT DUAL's well-formedness, and exactly which part of it is still
-- open (notes/DECISIONS.md, Decision 4's residue (R2)).
--
-- Wrap's preservation case needs two facts about  Θᵈ = dualᴳ Δ Θ  beyond the
-- two face laws (which ARE theorems — ρᵇ-dual-ty / γᵇ-dual-ty):
--
--   (i)  Θᵈ is a WELL-FORMED boundary over the exterior intOf Δ Θ, so that
--        (env) can be applied to the dual-wrapped argument;
--   (ii) Θᵈ's INTERIOR rebuilds Δ, at least up to _≼_ (abstract below
--        anything), so that the argument W — typed at Δ — retypes there.
--
-- This module proves as much of (i) as is provable and states the rest.
-- What is PROVEN here:
--
--   * repOf-wf     — a conceal rep of Θ is well formed in Θ's interior,
--                    which is the dual's exterior;
--   * dual-rep-conc — hence the dual's reveal at a CONCEALED slot is well
--                    formed (its rep is that conceal rep, lifted past the
--                    deeper dual reveals);
--   * bwf-dualᴳ    — the whole dual is well formed as soon as the two
--                    residues below are supplied.
--
-- What is OPEN, and why:
--
--   * BlkRepWf (parameter DualRep).  At a slot the boundary drops WITHOUT
--     concealing and which Δ REVEALS, the dual copies Δ's own entry `rvld B`.
--     B is a type over Δ ↓ i, and its well-formedness there is a fact about
--     the well-formedness of the CONTEXT Δ, which the preservation statement
--     does not carry (adding ⊢ Δ would in turn demand ⊢ intOf Δ Θ, i.e. that
--     every knowledge entry ⟦A⟧ is well formed over its own tail — the same
--     obligation one level down).  Λ-BOUND blocked slots are fine: the dual
--     emits the rep-less reveal rvl⋆, which carries no premise at all.
--
--   * DualCnc.  The dual CONCEALS each reveal variable of Θ, and the
--     reversal premise asks the dual's exterior — Θ's interior — to KNOW
--     that variable.  It does, unless the reveal's rep names a slot Θ itself
--     blocks, in which case ⟦·⟧ makes the entry `abst` and there is no
--     knowledge to meet.  That is exactly Example 8's Θn = ↑Z:=Y , ↓X:=ℕ
--     with Y Λ-bound (notes/old/AmbientDualProbe.agda §6a, ¬⊢dualᴳΘn): a
--     STRUCTURAL obstruction — "Z is Y" is not expressible in a context that
--     dropped Y — which neither the ambient dual nor W3 dissolves.
--
--   * DualInt.  The rebuild law.  Its Λ-bound and abstract slots are exact
--     by construction; a concealed or copied slot is exact exactly when the
--     rep round-trips through ⟦·⟧, which is the same knowledge question as
--     DualCnc one level out.
--
-- strong.BPreservation is parameterised over the three (the repo's `…Def`
-- convention, as strong.Progress is over strong.ProgressDef).

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Properties using (_≟_; +-identityʳ)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; _⊢_; wf-ℕ)
open import strong.Boundary
open import strong.BReduction
  using (repOf; entAt; upFrom; entᴳ; rvlsᴳ; cncOfRevs; dualᴳ;
         revs-cncOfRevs; bwf-++; bwf-ent; bwf-rvlsᴳ; bwf-cncOfRevs;
         wf-ren; prepAbst-hi; _≼_)

private
  variable
    Δ Δ' Ψ : TCtx
    Θ Ξ : BCtx

------------------------------------------------------------------------
-- PROVEN.  A conceal rep lives in the interior, which is the dual's
-- exterior — so the dual's reveal at a CONCEALED slot is well formed.
------------------------------------------------------------------------

repOf-wf : ∀ Ξ → Bwf Δ Ψ Θ Ξ → ∀ i → Ψ ⊢ repOf i Ξ
repOf-wf []            bwf[]              i = wf-ℕ
repOf-wf (rvl A ∷ Ξ)   (bwf↑ wfA b)       i = repOf-wf Ξ b i
repOf-wf (rvl⋆ ∷ Ξ)    (bwf⋆ b)           i = repOf-wf Ξ b i
repOf-wf (cnc X A ∷ Ξ) (bwf↓ p rev wfA b) i with i ≟ X
repOf-wf (cnc X A ∷ Ξ) (bwf↓ p rev wfA b) i | yes _ = wfA
repOf-wf (cnc X A ∷ Ξ) (bwf↓ p rev wfA b) i | no  _ = repOf-wf Ξ b i

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
entᴳ-⋆ Δ Θ s k ec ee | false | _ | abst   | _  = refl
entᴳ-⋆ Δ Θ s k ec ee | false | _ | rvld B | ()

entᴳ-B : ∀ (Δ : TCtx) Θ s k B → isConc s Θ ≡ false → entAt Δ s ≡ rvld B
       → entᴳ Δ Θ s k ≡ rvl (renameᵗ (upFrom k (revs Θ)) B)
entᴳ-B Δ Θ s k B ec ee with isConc s Θ | ec
entᴳ-B Δ Θ s k B ec ee | true  | ()
entᴳ-B Δ Θ s k B ec ee | false | _ with entAt Δ s | ee
entᴳ-B Δ Θ s k B ec ee | false | _ | abst   | ()
entᴳ-B Δ Θ s k B ec ee | false | _ | rvld C | refl = refl

dual-rep-conc : ∀ Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → ∀ k i → isConc i Θ ≡ true
              → ∀ R → entᴳ Δ Θ i k ≡ rvl R
              → prepAbst k (intOf Δ Θ) ⊢ R
dual-rep-conc {Δ = Δ} Θ bwf k i c R e
  with isConc i Θ | c
dual-rep-conc {Δ = Δ} Θ bwf k i c R e | true  | _ =
  subst (λ T → prepAbst k (intOf Δ Θ) ⊢ T) (rvl-inj e)
        (wf-ren (λ {X} p → prepAbst-hi k (intOf Δ Θ) X p)
                (repOf-wf Θ bwf i))
dual-rep-conc {Δ = Δ} Θ bwf k i c R e | false | ()

------------------------------------------------------------------------
-- OPEN (1).  The reveal the dual emits at a slot that Θ drops without
-- concealing and that Δ REVEALS: it copies Δ's entry `rvld B`, transported
-- into the dual's telescopic reveal block by upFrom.
------------------------------------------------------------------------

BlkRepWf : TCtx → BCtx → Set
BlkRepWf Δ Θ = ∀ k i B → isConc i Θ ≡ false → entAt Δ i ≡ rvld B
             → prepAbst k (intOf Δ Θ) ⊢ renameᵗ (upFrom k (revs Θ)) B

------------------------------------------------------------------------
-- PROVEN.  Given (1) and the conceal block, the whole dual is well formed.
------------------------------------------------------------------------

bwf-dualᴳ : ∀ {Δ Δ'} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → BlkRepWf Δ Θ
  → Bwf (intOf Δ Θ) Δ' (dualᴳ Δ Θ) (cncOfRevs 0 Θ)
  → intOf Δ Θ ∣ Δ' ⊢ᵇ dualᴳ Δ Θ
bwf-dualᴳ {Δ} {Δ'} Θ bwf hblk bcnc =
  bwf-rvlsᴳ (cmax Θ) 0 Δ Θ (cncOfRevs 0 Θ) hrvl bcnc
  where
    fix : ∀ k → prepAbst (k + revs (cncOfRevs 0 Θ)) (intOf Δ Θ)
              ≡ prepAbst k (intOf Δ Θ)
    fix k = cong (λ n → prepAbst n (intOf Δ Θ))
                 (trans (cong (k +_) (revs-cncOfRevs 0 Θ)) (+-identityʳ k))
    hrvl : ∀ k s R → entᴳ Δ Θ s k ≡ rvl R
         → prepAbst (k + revs (cncOfRevs 0 Θ)) (intOf Δ Θ) ⊢ R
    hrvl k s R e =
      subst (λ Ψ → Ψ ⊢ R) (sym (fix k)) (go (isConc s Θ) refl)
      where
        go : ∀ b → isConc s Θ ≡ b → prepAbst k (intOf Δ Θ) ⊢ R
        go true  ec = dual-rep-conc Θ bwf k s ec R e
        go false ec = blkcase (entAt Δ s) refl
          where
            blkcase : ∀ (E : TyEntry) → entAt Δ s ≡ E
                → prepAbst k (intOf Δ Θ) ⊢ R
            blkcase abst     ee =
              ⊥-elim (⋆≢rvl (trans (sym (entᴳ-⋆ Δ Θ s k ec ee)) e))
            blkcase (rvld B) ee =
              subst (λ T → prepAbst k (intOf Δ Θ) ⊢ T)
                    (rvl-inj (trans (sym (entᴳ-B Δ Θ s k B ec ee)) e))
                    (hblk k s B ec ee)

------------------------------------------------------------------------
-- OPEN (2) and (3).  The two statements strong.BPreservation is
-- parameterised over, together with the reveal-rep one.
------------------------------------------------------------------------

-- (1) every copied knowledge rep is well formed in the dual's telescope
DualRep : Set
DualRep = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → BlkRepWf Δ Θ

-- (2) the dual's CONCEAL block: every reveal variable of Θ is KNOWN in Θ's
-- interior, and Θ's external face for it reads back to that knowledge.
-- Refuted for a reveal whose rep names a slot its own boundary blocks (R2).
DualCnc : Set
DualCnc = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
        → Bwf (intOf Δ Θ) (intOf (intOf Δ Θ) (dualᴳ Δ Θ)) (dualᴳ Δ Θ)
               (cncOfRevs 0 Θ)

-- (3) the CONTEXT law: the dual's interior rebuilds the exterior, up to
-- _≼_ (an abstract entry sits below anything)
DualInt : Set
DualInt = ∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
        → Δ ≼ intOf (intOf Δ Θ) (dualᴳ Δ Θ)

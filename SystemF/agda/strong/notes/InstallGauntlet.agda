module strong.notes.InstallGauntlet where

-- THE INSTALL GAUNTLET for the dual-conceal licence design
-- (notes/DualLicenseDesign.md; the four probes now under notes/old/).
--
-- Everything here is run against the LIVE definitions — strong.Boundary,
-- strong.BReduction — with no local copies of anything.  It is deliberately
-- NOT in strong/All.agda: it is evidence, not development.
--
-- CONTENTS
--   §1  E★′ END TO END.  The counterexample that motivated the whole
--       design: a reachable Wrap redex whose contractum typed in NEITHER
--       the rep-keeping nor the rep-less regime.  All four steps are live
--       `_⊢_-→_` inhabitants, T0′ … T3′ type, and the CONTRACTUM now types
--       — through (bwf-↓x), with the dual's own ↑Y:⋆ supplying the
--       claims-nothing premise.
--   §2  E★ END TO END, the cnc⋆ path — and the finding that with the
--       x-licence E★ needs NO cnc⋆ at all; cnc⋆ is needed for the dual of a
--       REP-LESS reveal, which is what §4's dual-of-dual mints.
--   §3  Pn — the case the AMBIENT unfold retry used to close, and the
--       machine-checked reason it is now a DualCnc≈ residue.
--   §4  DUAL-OF-DUAL on E★′'s shapes: exact round trip, cnc⋆ retained
--       exactly where a rep-less reveal has to be re-hidden.
--   §5  Pc's CHAINED-COPY site: the dual's SECOND-CHANCE copy recovers the
--       knowledge the raw guard refuses, and the rebuild is one unfolding
--       away — which _≼≈_ absorbs and ⊢retag≈ consumes.
--   §6  SOUNDNESS: bad / bad₂ refuted, near-bad admitted, far-bad refused,
--       the ⊢3n-adv adversary refuted (and refuted UNDER ≈ — the §5(ii)
--       gauntlet item), the conceal of a plain Λ-bound variable refused.
--   §7  RENAMING: a transport instance that touches an xrvld entry, and the
--       counter-instance showing why (bwf-↓x)'s rep comparison can be
--       neither ≡ nor ≈Δ̄.
--   §8  THE SkelEq REPAIR: the premise discharged at the dual's birth by
--       xrep-stored, surviving §7b's weakening, refusing the soundness hole
--       the comparison-free licence had, and leaving ⊢3n-adv to starOnly.

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Unfold
open import strong.Boundary
open import strong.BReduction
open import strong.DualDef using (xrep-stored; dual-cnc-skel)

------------------------------------------------------------------------
-- §1.  E★′, END TO END
--
--   E★′ = (ΛX. λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) [ℕ]
--           · (ΛZ. λg:(Z→ℕ). λz:Z. g z)      : ∀Y. Y→ℕ
--
-- At the ξ TyWrap(Z) step the boundary  ↑Z:=Y , ↓X:=ℕ  is minted at
-- exterior  Y (Λ-bound) , X:=ℕ .  The knowledge "Z is Y" is inexpressible
-- in the interior (Y is blocked) and un-unfoldable (Y is Λ-bound), so Z's
-- entry is the EXTERIOR-READ one.  The later Wrap's dual conceals Z with
-- that very rep, licensed by (bwf-↓x).
------------------------------------------------------------------------

polyg : Ty                     -- ∀Z. (Z→ℕ)→(Z→ℕ)
polyg = `∀ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ))

B₀′ : Ty
B₀′ = (` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)

Bprog′ : Ty
Bprog′ = polyg ⇒ `∀ (` 0 ⇒ `ℕ)

idg : Term                     -- ΛZ. λg:(Z→ℕ). λz:Z. g z
idg = Λ (ƛ (` 0 ⇒ `ℕ) ∙ (ƛ ` 0 ∙ ((` 1) · (` 0))))

argY : Term                    -- λy:Y. 5   — a VALUE at type Y→ℕ
argY = ƛ ` 0 ∙ ($ 5)

fn′ : Term
fn′ = ƛ polyg ∙ (Λ (((` 0) ·[ B₀′ , ` 0 ]) · argY))

Θ1 : BCtx                      -- ↑X:=ℕ, the boundary TyBeta is born with
Θ1 = rvl `ℕ ∷ []

Θd′ : BCtx                     -- ↓X:=ℕ, under the ΛY (index 1)
Θd′ = cnc 1 `ℕ ∷ []

Γ★ : TCtx                      -- Y (Λ-bound, 0) , X:=ℕ (1)  — Boundary's Γ₈
Γ★ = Γ₈

Θ★ : BCtx                      -- ↑Z:=Y , ↓X:=ℕ, minted by TyWrap at Γ★
Θ★ = rvl (` 0) ∷ cnc 1 `ℕ ∷ []

-- the LIVE dual at the failing step: ↑Y:⋆ (Y is Λ-bound, so REP-LESS),
-- ↑X:=ℕ (copied from Θ★'s conceal rep), ↓Z:=Y (the once-unlicensable one)
dualᵛ : BCtx
dualᵛ = rvl⋆ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []

_ : dualᴳ Γ★ Θ★ ≡ dualᵛ
_ = refl

W′ : Term
W′ = argY ⟪ dualᵛ , (` 2 ⇒ `ℕ) ⟫

T0′ T1′ T2′ T3′ T4′ T4full′ : Term
T0′ = ((Λ fn′) ·[ Bprog′ , `ℕ ]) · idg
T1′ = (fn′ ⟪ Θ1 , Bprog′ ⟫) · idg
T2′ = (Λ (((idg ⟪ Θd′ , polyg ⟫) ·[ B₀′ , ` 0 ]) · argY))
      ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
T3′ = (Λ ((((ƛ (` 0 ⇒ `ℕ) ∙ (ƛ ` 0 ∙ ((` 1) · (` 0)))) ⟪ Θ★ , B₀′ ⟫)
           · argY))) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
T4′ = (ƛ ` 0 ∙ (W′ · (` 0))) ⟪ Θ★ , ` 0 ⇒ `ℕ ⟫
T4full′ = (Λ T4′) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫

------------------------------------------------------------------------
-- §1.1  the four steps, by the LIVE reduction relation
------------------------------------------------------------------------

step01′ : [] ⊢ T0′ -→ T1′
step01′ = ξ-·-l (TyBeta (V-G G-ƛ))

step12′ : [] ⊢ T1′ -→ T2′
step12′ = Wrap (V-G (G-Λ (V-G G-ƛ)))

step23′ : [] ⊢ T2′ -→ T3′
step23′ = ξ-⟪⟫ (ξ-Λ (ξ-·-l (TyWrap (V-G G-ƛ))))

step34′ : [] ⊢ T3′ -→ T4full′
step34′ = ξ-⟪⟫ (ξ-Λ (Wrap (V-G G-ƛ)))

-- the failing Wrap is FORCED: at T3′ the only redex is that application
_ : Value argY
_ = V-G G-ƛ

------------------------------------------------------------------------
-- §1.2  T0′ … T3′ type, at the program's type ∀Y. Y→ℕ
------------------------------------------------------------------------

wf-polyg : ∀ {Δ₁ : TCtx} → Δ₁ ⊢ polyg
wf-polyg = wf-∀ (wf-⇒ (wf-⇒ (wf-var here-abst) wf-ℕ)
                      (wf-⇒ (wf-var here-abst) wf-ℕ))

sc-polyg : ∀ {Ψ₁ : SCtx} → Scoped Ψ₁ polyg
sc-polyg = sc-∀ (sc-⇒ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
                      (sc-⇒ (sc-var hereᵒ) sc-ℕ))

⊢idg : ∀ {Δ₁ : TCtx} {Γ₁ : Ctx} → Δ₁ ∣ Γ₁ ⊢ idg ⦂ polyg
⊢idg = ⊢Λ (⊢ƛ (wf-⇒ (wf-var here-abst) wf-ℕ)
              (⊢ƛ (wf-var here-abst) (⊢· (⊢` (there here)) (⊢` here))))

⊢argY : Γ★ ∣ [] ⊢ argY ⦂ (` 0 ⇒ `ℕ)
⊢argY = ⊢ƛ (wf-var here-abst) ⊢$

⊢fn′ : ∀ {Δ₁ : TCtx} → Δ₁ ∣ [] ⊢ fn′ ⦂ Bprog′
⊢fn′ = ⊢ƛ wf-polyg
          (⊢Λ (⊢· (⊢·[] (⊢` here) (wf-var here-abst))
                  (⊢ƛ (wf-var here-abst) ⊢$)))

⊢T0′ : [] ∣ [] ⊢ T0′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T0′ = ⊢· (⊢·[] (⊢Λ ⊢fn′) wf-ℕ) ⊢idg

⊢T1′ : [] ∣ [] ⊢ T1′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T1′ = ⊢· (env (bwf↑ wf-ℕ bwf[])
               (sc-⇒ sc-polyg (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ)))
               ⊢fn′) ⊢idg

⊢T2′ : [] ∣ [] ⊢ T2′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T2′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
           (⊢Λ (⊢· (⊢·[] (env (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[])
                              sc-polyg ⊢idg)
                         (wf-var here-abst))
                   (⊢ƛ (wf-var here-abst) ⊢$)))

-- Z's interior entry: the EXTERIOR-READ one.  "Z is Y" is not expressible
-- where Y is blocked, and unfolding is the identity at the Λ-bound Y.
_ : intOf Γ★ Θ★ ≡ xrvld (` 0) ∷ []
_ = refl

bwf-Θ★ : Γ★ ∣ intOf Γ★ Θ★ ⊢ᵇ Θ★
bwf-Θ★ = bwf↑ (wf-var here-abst)
              (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[])

⊢T3′ : [] ∣ [] ⊢ T3′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T3′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
           (⊢Λ (⊢· (env bwf-Θ★
                        (sc-⇒ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
                              (sc-⇒ (sc-var hereᵒ) sc-ℕ))
                        (⊢ƛ (wf-⇒ (wf-var here-xrvld) wf-ℕ)
                            (⊢ƛ (wf-var here-xrvld)
                                (⊢· (⊢` (there here)) (⊢` here)))))
                   (⊢ƛ (wf-var here-abst) ⊢$)))

------------------------------------------------------------------------
-- §1.3  *** THE CONTRACTUM TYPES ***  The dual's conceal of Z is licensed
-- by (bwf-↓x): Z is x-revealed in the interior, and the rep ` 0 names the
-- dual's OWN rep-less reveal ↑Y:⋆, so it claims nothing.  Both faces were
-- already exactly right; only the licence was missing.
------------------------------------------------------------------------

-- the two faces, at exactly the boundary type Wrap hands the dual
face-int-E★′ : substᵗ (γᵇ dualᵛ) (` 2 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
face-int-E★′ = refl

face-ext-E★′ : substᵗ (ρᵇ dualᵛ) (` 2 ⇒ `ℕ)
             ≡ substᵗ (γᵇ Θ★) (` 0 ⇒ `ℕ)
face-ext-E★′ = refl

-- the licence, isolated: the x-lookup and the claims-nothing premise
xlic-E★′ : intOf Γ★ Θ★ ∋ 0 :=x (` 0)
xlic-E★′ = herex

star-E★′ : starOnly dualᵛ 0 (` 0) ≡ true
star-E★′ = refl

-- there is NO ordinary knowledge of Z, which is why (bwf-↓) cannot fire
no-know-E★′ : ∀ {A₁} → intOf Γ★ Θ★ ∋ 0 := A₁ → ⊥
no-know-E★′ ()

-- the dual's interior rebuilds Γ★ ON THE NOSE
rebuild-E★′ : intOf (intOf Γ★ Θ★) dualᵛ ≡ Γ★
rebuild-E★′ = refl

DualInt-E★′ : Γ★ ≼≈ intOf (intOf Γ★ Θ★) dualᵛ
DualInt-E★′ = ≼≈-refl Γ★

bwf-dualᵛ : Γz ∣ intOf Γz dualᵛ ⊢ᵇ dualᵛ
bwf-dualᵛ =
  bwf⋆ (bwf↑ wf-ℕ (bwf↓x herex refl sk-var (wf-var here-abst) bwf[]))

⊢W′ : ∀ {Γ₁ : Ctx} → Γz ∣ Γ₁ ⊢ W′ ⦂ (` 0 ⇒ `ℕ)
⊢W′ = env bwf-dualᵛ
          (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ))) sc-ℕ)
          (⊢ƛ (wf-var here-abst) ⊢$)

⊢T4′ : Γ★ ∣ [] ⊢ T4′ ⦂ (` 0 ⇒ `ℕ)
⊢T4′ = env bwf-Θ★ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
           (⊢ƛ (wf-var here-xrvld) (⊢· ⊢W′ (⊢` here)))

⊢T4full′ : [] ∣ [] ⊢ T4full′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T4full′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
               (⊢Λ ⊢T4′)

------------------------------------------------------------------------
-- §2.  E★ END TO END.  Same program with the ∀-body NOT mentioning its own
-- variable (f : ∀Z. ℕ→ℕ), so the Wrap's argument is `5 : ℕ`.  It types by
-- the SAME licence — so with the x-clause, E★ needs no cnc⋆ at all.
------------------------------------------------------------------------

polyf : Ty                     -- ∀Z. ℕ→ℕ   (Z UNUSED)
polyf = `∀ (`ℕ ⇒ `ℕ)

T4 T4full : Term
T4     = (($ 5) ⟪ dualᵛ , `ℕ ⟫) ⟪ Θ★ , `ℕ ⟫
T4full = (Λ T4) ⟪ Θ1 , `∀ `ℕ ⟫

⊢T4 : Γ★ ∣ [] ⊢ T4 ⦂ `ℕ
⊢T4 = env bwf-Θ★ sc-ℕ (env bwf-dualᵛ sc-ℕ ⊢$)

⊢T4full : [] ∣ [] ⊢ T4full ⦂ `∀ `ℕ
⊢T4full = env (bwf↑ wf-ℕ bwf[]) (sc-∀ sc-ℕ) (⊢Λ ⊢T4)

-- … and it is a VALUE of the program's type: E★ terminates
val-T4full : Value T4full
val-T4full = V-⟪⟫ (V-G (G-Λ (V-⟪⟫ (V-⟪⟫ V-$))))

------------------------------------------------------------------------
-- §3.  Pn — THE PRICE OF DROPPING THE AMBIENT UNFOLD RETRY.
--
-- Γn = Y:=ℕ , X:=ℕ with ↑Z:=Y , ↓X:=ℕ.  The interior DROPS Y, so the raw
-- reading of Z's rep is blocked; the probes' middle step retried at
-- unfoldᵉ Γn (` 0) = ℕ and got genuine knowledge Z:=ℕ.  That step is gone
-- (strong.Boundary's flagged deviation: it breaks BOTH ⊢renameᵀ's ⟦⟧-ren
-- and ⊢retag's interior monotonicity), so Z gets the exterior-read entry
-- and its dual's conceal is licensed by NEITHER clause — the ONE gauntlet
-- item this install loses, and it lands in DualCnc≈.
------------------------------------------------------------------------

_ : intOf Γn Θn ≡ xrvld (` 0) ∷ []
_ = refl

dualⁿ : BCtx
dualⁿ = rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []

_ : dualᴳ Γn Θn ≡ dualⁿ
_ = refl

-- (bwf-↓) cannot fire: the interior has no ORDINARY knowledge of Z …
¬know-Pn : ∀ {A₁} → intOf Γn Θn ∋ 0 := A₁ → ⊥
¬know-Pn ()

-- … and (bwf-↓x) cannot either: the rep ` 0 names the dual's slot 0, which
-- is a REP-CARRYING reveal ↑Y:=ℕ, so it claims something.
¬star-Pn : ¬ (starOnly dualⁿ 0 (` 0) ≡ true)
¬star-Pn ()

-- the x-lookup itself IS there — it is only the claims-nothing half that
-- fails, which is exactly DualLicenseProbe §4.5's xlic-Pnⁿ vs ¬abs-Pnⁿ
xlic-Pn : intOf Γn Θn ∋ 0 :=x (` 0)
xlic-Pn = herex

------------------------------------------------------------------------
-- §4.  DUAL OF DUAL, on E★′'s shapes.  The ⋆-reveal duals to cnc⋆ (this is
-- where cnc⋆ is indispensable — there is no rep to keep), the copied
-- reveal to an ordinary conceal, and the reveal of the concealed Z slot
-- re-reveals its rep.  The round trip is EXACT.
------------------------------------------------------------------------

dd : BCtx
dd = rvl (` 0) ∷ cnc⋆ 0 ∷ cnc 1 `ℕ ∷ []

_ : dualᴳ Γz dualᵛ ≡ dd
_ = refl

_ : intOf Γ★ dd ≡ Γz                 -- the round trip
_ = refl

⊢dd : Γ★ ∣ intOf Γ★ dd ⊢ᵇ dd
⊢dd = bwf↑ (wf-var here-abst)
           (bwf⋆↓ here-abst
             (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))

-- and the ⋆-concealed slot is UNNAMEABLE, which is what keeps cnc⋆ honest
_ : baseS dd Γ★ ≡ ok ∷ blk ∷ ok ∷ []
_ = refl

¬Scoped-dd : ¬ Scoped (baseS dd Γ★) (` 1)
¬Scoped-dd (sc-var (thereᵒ ()))

------------------------------------------------------------------------
-- §5.  Pc's CHAINED-COPY SITE.  Γq = W:=Y , Y:=ℕ , X:=ℕ is reachable
-- (TyBeta turns a Λ-bound Y into W:=Y without renaming) and Θq = ↓X:=ℕ
-- drops all three.  W's entry is the CHAIN "W is Y", and Θq drops Y too, so
-- the RAW copy's guard refuses it — the knowledge used to be LOST to rvl⋆.
-- The SECOND-CHANCE copy retries at the rep unfolded in its own tail, which
-- collapses the chain, so all three slots come back with knowledge and the
-- rebuild is ONE UNFOLDING away from Γq — which _≼≈_ absorbs.
------------------------------------------------------------------------

Γq Γq′ : TCtx
Γq  = rvld (` 0) ∷ rvld `ℕ ∷ rvld `ℕ ∷ []
Γq′ = rvld `ℕ   ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

Θq : BCtx
Θq = cnc 2 `ℕ ∷ []

_ : intOf Γq Θq ≡ []
_ = refl

-- the raw guard refuses W's chained rep …
_ : dfree 0 2 (` 0) ≡ false
_ = refl

-- … and the second chance takes it, at the collapsed rep ℕ
_ : unfEnt Γq 0 (` 0) ≡ `ℕ
_ = refl

_ : dualᴳ Γq Θq ≡ rvl `ℕ ∷ rvl `ℕ ∷ rvl `ℕ ∷ []
_ = refl

_ : intOf (intOf Γq Θq) (dualᴳ Γq Θq) ≡ Γq′
_ = refl

-- THE CONTEXT LAW.  Syntactic _≼_ ordered Γq and Γq′ in neither direction;
-- _≼≈_ orders them, because the difference is exactly one unfolding.
DualInt-Γq : Γq ≼≈ intOf (intOf Γq Θq) (dualᴳ Γq Θq)
DualInt-Γq = ≼≈rvld (≼≈rvld (≼≈rvld ≼≈[] ≈-refl) ≈-refl) (≈unf refl)

⊢dualᴳ-Γq : intOf Γq Θq ∣ intOf (intOf Γq Θq) (dualᴳ Γq Θq)
            ⊢ᵇ dualᴳ Γq Θq
⊢dualᴳ-Γq = bwf↑ wf-ℕ (bwf↑ wf-ℕ (bwf↑ wf-ℕ bwf[]))

-- THE SITE ≈ WAS INTRODUCED FOR: the argument's ↓W:=Y conceal, retyped in
-- the rebuilt context.  In Γq the conceal is licensed on the nose; in Γq′
-- the knowledge for W is the unfolded ℕ while the read-back is still the
-- raw variable ` 1, so the SYNTACTIC premise fails and only ≈ carries it.
argW : Term
argW = (($ 3) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ cnc 0 (` 0) ∷ [] , ` 0 ⟫

⊢argW : Γq ∣ [] ⊢ argW ⦂ ` 0
⊢argW =
  env (bwf↓ here (≡→≈ refl) (wf-var here-rvld) bwf[])
      (sc-var hereᵒ)
      (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

¬Reversal-argW′ : ¬ (Reversal (cnc 0 (` 0) ∷ []) 0 (` 0) `ℕ)
¬Reversal-argW′ ()

Reversal≈-argW′ : Reversal≈ Γq′ (cnc 0 (` 0) ∷ []) 0 (` 0) `ℕ
Reversal≈-argW′ = ≈unf refl

-- … and ⊢retag≈ does it wholesale, which is what Wrap's preservation case
-- consumes
⊢argW-rebuilt : Γq′ ∣ [] ⊢ argW ⦂ ` 0
⊢argW-rebuilt = ⊢retag≈ DualInt-Γq ⊢argW

------------------------------------------------------------------------
-- §6.  SOUNDNESS.  The relaxation must reach exactly as far as the
-- exterior's knowledge, and no further.
------------------------------------------------------------------------

-- bad / bad₂ stay refuted (strong.Boundary's ¬⊢bad / ¬Reversal≈-bad₂), and
-- the x-clause cannot fire at either, because the exterior carries ORDINARY
-- knowledge there rather than an x-mark
¬⊢bad-here : ¬ ([] ∣ [] ⊢ bad ⦂ ∀ZZ)
¬⊢bad-here = ¬⊢bad

¬xlic-bad : ∀ {A₁} → (rvld ∀ZZ ∷ []) ∋ 0 :=x A₁ → ⊥
¬xlic-bad ()

¬xlic-bad₂ : ∀ {A₁} → Γb ∋ 0 :=x A₁ → ⊥
¬xlic-bad₂ ()

-- the NEAR-bad is ADMITTED (W really is ℕ, by the other route) …
near-bad-ok : Reversal≈ Γnb Θnb 0 `ℕ (` 0)
near-bad-ok = Reversal≈-near-bad

-- … and the FAR-bad is refused
far-bad-no : ¬ (Reversal≈ Γnb (cnc 0 ∀ZZ ∷ []) 0 ∀ZZ (` 0))
far-bad-no = ¬Reversal≈-far-bad

-- THE ⊢3n-adv ADVERSARY, AND THE §5(ii) GAUNTLET ITEM.  It reuses E★′'s own
-- legitimately-minted x-entry with a boundary that is NOT the dual, and it
-- is REFUTED.  What refutes it is the claims-nothing premise alone: its
-- conceal rep IS the recorded one, so both the syntactic rep comparison and
-- the ≈Δ̄ one HOLD for it.  VERDICT: refuted under ≈; the ≈ addition is not
-- what refutes it, so §5(ii)'s expectation is confirmed.
¬⊢adv-here : ¬ (Γz ∣ [] ⊢ adv ⦂ ` 0)
¬⊢adv-here = ¬⊢adv

adv-rep-holds≈ : (` 0) ≈Δ̄⟨ Γz ⟩ (` 0)
adv-rep-holds≈ = adv-rep-match≈

adv-claims-something : ¬ (starOnly Ξadv 0 (` 0) ≡ true)
adv-claims-something = ¬starOnly-adv

-- a conceal of a PLAIN Λ-bound abstract variable stays unlicensed: the
-- x-lookup is what discriminates (bwf1-garbage's shape)
¬x-plain : ∀ {A₁} → (abst ∷ []) ∋ 0 :=x A₁ → ⊥
¬x-plain = ¬x-plain-abst

------------------------------------------------------------------------
-- §7.  RENAMING.
--
-- (a) A transport instance that TOUCHES an xrvld entry: weakening E★′'s
--     dual-wrapped argument by a fresh Λ-bound slot.  The exterior Γz's
--     x-entry rides the transport (hx-suc), and its rep is carried across
--     verbatim — a weakening does not rewrite stored entries.
------------------------------------------------------------------------

h-suc : ∀ {Δ₁ : TCtx} {X} → Δ₁ ∋tv X → (abst ∷ Δ₁) ∋tv suc X
h-suc p = skip-abst p

⊢W′-weakened :
  (abst ∷ Γz) ∣ map (renameᵗ suc) [] ⊢ renameᵀ suc W′ ⦂ renameᵗ suc (` 0 ⇒ `ℕ)
⊢W′-weakened = ⊢renameᵀ h-suc Mono-suc hk-suc hx-suc (⊢W′ {Γ₁ = []})

-- the renamed wrapper, computed: the ⋆-conceal's INDEX moves and nothing
-- else does, while the exterior's x-entry stays put
_ : renameᵀ suc W′ ≡ argY ⟪ rvl⋆ ∷ rvl `ℕ ∷ cnc 1 (` 0) ∷ []
                          , (` 3 ⇒ `ℕ) ⟫
_ = refl

------------------------------------------------------------------------
-- (b) WHY (bwf-↓x)'s COMPARISON IS NEITHER ≡ NOR ≈Δ̄
--     (notes/DualLicenseDesign.md §5).  Weaken Γ★ by a fresh Λ-bound V.
--     The renaming ⊢renameᵀ hands the sealed body is ρ₁ = intRen suc Θ★,
--     which is the IDENTITY on the dual's frame — so the TERM's conceal rep
--     is FROZEN at ` 0 while the CONTEXT's x-rep moves to ` 1.  The
--     syntactic comparison fails, and so does the ≈Δ̄ one: in the renamed
--     interior ` 0 is the x-revealed Z and ` 1 is out of range, so their
--     unfoldings are themselves and differ.  Ruling (ii) therefore does NOT
--     make EITHER of those forms ⊢renameᵀ-stable; §8 is the form that
--     survives, and it survives exactly this instance.
------------------------------------------------------------------------

Δw : TCtx
Δw = abst ∷ Γ★

ρ₁ : ℕ → ℕ
ρ₁ = intRen suc Θ★

Θ★w : BCtx
Θ★w = renᴮ suc ρ₁ Θ★

_ : Θ★w ≡ rvl (` 1) ∷ cnc 2 `ℕ ∷ []
_ = refl

_ : intOf Δw Θ★w ≡ xrvld (` 1) ∷ []       -- the x-rep moved by ρ = suc …
_ = refl

_ : renᴮ ρ₁ (intRen ρ₁ dualᵛ) dualᵛ ≡ dualᵛ   -- … the term's did not
_ = refl

-- the SYNTACTIC comparison fails …
¬x-rep-match-ren : ¬ (intOf Δw Θ★w ∋ 0 :=x (` 0))
¬x-rep-match-ren ()

-- … and so does the ≈Δ̄ one, at the renamed interior
¬x-rep-match-ren≈ : ¬ ((` 0) ≈Δ̄⟨ intOf Δw Θ★w ⟩ (` 1))
¬x-rep-match-ren≈ (≈unf ())

-- what DOES hold, and is what the rule asks for: the x-LOOKUP at the moved
-- slot, and the claims-nothing premise (which mentions no context at all)
xlic-ren-ok : intOf Δw Θ★w ∋ 0 :=x (` 1)
xlic-ren-ok = herex

star-ren-ok : starOnly (renᴮ ρ₁ (intRen ρ₁ dualᵛ) dualᵛ) 0 (` 0) ≡ true
star-ren-ok = refl

------------------------------------------------------------------------
-- §8.  THE SkelEq REPAIR (notes/DECISIONS.md's "D1 PROBE VERDICT — … the
-- SkelEq repair"; the reference probe is notes/D1Probe.agda §7).
--
-- (bwf-↓x) now carries a third premise: SkelEq A A′, "the conceal's rep has
-- the same SKELETON as the recorded x-rep" — the constructor tree, with
-- VARIABLE POSITIONS IDENTIFIED.  Four things had to be true of it, and all
-- four are checked below:
--
--   §8.1  it is DISCHARGED AT BIRTH by a theorem — at every dual's birth the
--         two reps are SYNTACTICALLY equal (xrep-stored / dual-cnc-skel), so
--         the only rule that mints x-conceals pays nothing;
--   §8.2  it SURVIVES §7b's weakening, the very instance that refutes ≡ and
--         ≈Δ̄ — and by the hypothesis-free stability theorem, not by
--         computation;
--   §8.3  it REFUSES the soundness hole the comparison-free licence had: a
--         CLOSED rep at an x-slot, which starOnly admits;
--   §8.4  the ⊢3n-adv adversary still PASSES it, so §6's refutation is
--         still carried by starOnly alone — the repair is orthogonal.
------------------------------------------------------------------------

-- §8.1  BIRTH.  E★′'s dual conceals Z at the rep ` 0 and the interior's
-- x-entry records ` 0 — not by coincidence: the x-lookup inside a reveal
-- block RETURNS the stored reveal rep, which is the rep cncOfRevs hands the
-- dual's conceal.
xrep-stored-E★′ : (` 0) ≡ ρᵇ Θ★ 0
xrep-stored-E★′ = xrep-stored Θ★ 0 Θ★ 0 (s≤s z≤n) xlic-E★′

skel-birth-E★′ : SkelEq (ρᵇ Θ★ 0) (` 0)
skel-birth-E★′ = dual-cnc-skel {Δ₀ = Γ★} Θ★ 0 (s≤s z≤n) xlic-E★′

-- … which is exactly the premise the live bwf-dualᵛ now supplies
skel-live-E★′ : SkelEq (` 0) (` 0)
skel-live-E★′ = sk-var

-- and the whole contractum still types through it (§1.3, re-run)
⊢T4′-still : Γ★ ∣ [] ⊢ T4′ ⦂ (` 0 ⇒ `ℕ)
⊢T4′-still = ⊢T4′

------------------------------------------------------------------------
-- §8.2  THE WEAKENING.  §7b's pair — the frozen conceal rep ` 0 against the
-- moved x-rep ` 1 — is still LICENSED, because skeletons identify variable
-- positions.  The witness comes from skel-ren applied to the two INDEPENDENT
-- renamings (the interior one, which absorbs the shift, and the exterior
-- suc): no Mono, no transport hypothesis, no absorption side condition.
------------------------------------------------------------------------

skel-post-ren : SkelEq (renameᵗ (intRen ρ₁ dualᵛ) (` 0)) (renameᵗ suc (` 0))
skel-post-ren = skel-ren (intRen ρ₁ dualᵛ) suc sk-var

skel-ok-ren : SkelEq (` 0) (` 1)
skel-ok-ren = skel-post-ren

-- the same pair, in the two forms that FAIL there (cited from §7b)
skel-vs-≡ : ¬ (intOf Δw Θ★w ∋ 0 :=x (` 0))
skel-vs-≡ = ¬x-rep-match-ren

skel-vs-≈ : ¬ ((` 0) ≈Δ̄⟨ intOf Δw Θ★w ⟩ (` 1))
skel-vs-≈ = ¬x-rep-match-ren≈

-- … and §7a's live transport instance is unchanged: hx-suc now carries the
-- SkelEq witness too (skel-refl — a weakening copies the entry verbatim),
-- so ⊢renameᵀ's strengthened hypothesis is discharged by the same term
⊢W′-weakened-still :
  (abst ∷ Γz) ∣ map (renameᵗ suc) [] ⊢ renameᵀ suc W′ ⦂ renameᵗ suc (` 0 ⇒ `ℕ)
⊢W′-weakened-still = ⊢renameᵀ h-suc Mono-suc hk-suc SkelX-suc (⊢W′ {Γ₁ = []})

------------------------------------------------------------------------
-- §8.3  THE HOLE, CLOSED.  Θg conceals E★′'s own x-slot at the CLOSED rep
-- ℕ.  starOnly ADMITS it (starOnly Θ d `ℕ = true), so the comparison-free
-- licence typed a ℕ literal at the Λ-BOUND Y — and, one ⊢retag≈ away, at a
-- slot the exterior knows to be ∀Z.Z→Z, which is `bad`'s own configuration.
-- Both are now REFUTED, by the skeleton premise alone.
------------------------------------------------------------------------

starOnly-does-not-refuse : starOnly Θg 0 `ℕ ≡ true
starOnly-does-not-refuse = starOnly-ground

skel-does-refuse : ¬ (SkelEq `ℕ (` 0))
skel-does-refuse = ¬skel-ground

-- the inner half and the two towers (strong.Boundary's refutations, cited)
¬⊢gnd-here : ¬ (Γz ∣ [] ⊢ ($ 7) ⟪ Θg , ` 0 ⟫ ⦂ ` 0)
¬⊢gnd-here = ¬⊢gnd

¬⊢Tg-here : ¬ (Γ₈ ∣ [] ⊢ Tg ⦂ ` 0)
¬⊢Tg-here = ¬⊢Tg

¬⊢Tbad-here : ¬ (Δbad ∣ [] ⊢ Tg ⦂ ` 0)
¬⊢Tbad-here = ¬⊢Tbad

-- the same tower on E★′'s OWN boundary ordering (D1Probe's ⊢Tg verbatim),
-- so the refutation is not an artefact of Θ₈'s entry order
Tg★ : Term
Tg★ = (($ 7) ⟪ Θg , ` 0 ⟫) ⟪ Θ★ , ` 0 ⟫

¬⊢Tg★ : ¬ (Γ★ ∣ [] ⊢ Tg★ ⦂ ` 0)
¬⊢Tg★ (env _ _ (env (bwf↓  () _ _ _) _ _))
¬⊢Tg★ (env _ _ (env (bwf↓x herex _ () _ _) _ _))

-- REACHABILITY, for the record: ⊢retag≈ along Γ★ ≼≈ Γ𝔹 is the transport
-- TyBeta performs when the Λ is instantiated, and it carried D1Probe's ⊢Tg
-- into a context that KNOWS Y.  With the tower refuted at BOTH ends there is
-- nothing left to transport.
Γ𝔹 : TCtx
Γ𝔹 = rvld `𝔹 ∷ rvld `ℕ ∷ []

Γ★≼Γ𝔹 : Γ★ ≼≈ Γ𝔹
Γ★≼Γ𝔹 = ≼≈abst (≼≈rvld ≼≈[] ≈-refl)

¬⊢Tg★-instantiated : ¬ (Γ𝔹 ∣ [] ⊢ Tg★ ⦂ ` 0)
¬⊢Tg★-instantiated (env _ _ (env (bwf↓  () _ _ _) _ _))
¬⊢Tg★-instantiated (env _ _ (env (bwf↓x herex _ () _ _) _ _))

------------------------------------------------------------------------
-- §8.4  ORTHOGONALITY.  The ⊢3n-adv adversary's conceal rep IS the recorded
-- one, so it passes SkelEq exactly as it passes ≡ and ≈Δ̄ (§6).  Its
-- refutation is still carried entirely by claims-nothing — so the repair
-- adds a refutation and removes none.
------------------------------------------------------------------------

adv-passes-skel : SkelEq (` 0) (` 0)
adv-passes-skel = adv-rep-skel

adv-still-refuted : ¬ (Γz ∣ [] ⊢ adv ⦂ ` 0)
adv-still-refuted = ¬⊢adv

adv-still-by-starOnly : ¬ (starOnly Ξadv 0 (` 0) ≡ true)
adv-still-by-starOnly = ¬starOnly-adv

-- and the ⊢3s-alias residue and a COMPOUND blocked rep are still admitted,
-- so the premise is not over-restrictive (a "the rep must BE the recorded
-- variable" premise would have refused the latter)
skel-alias : SkelEq (` 0) (` 0)
skel-alias = sk-var

skel-compound-ok : SkelEq (` 0 ⇒ `ℕ) (` 1 ⇒ `ℕ)
skel-compound-ok = skel-compound

------------------------------------------------------------------------
-- §9.  MERGE AND Drop∅ (Decision 3 + its addendum; the landing of
-- 2026-09-04).  The suite is in five parts:
--
--   §9a  the cancel pair, end to end: Merge then Drop∅ to the bare value;
--   §9b  E★'s own continuation tower merged — an X-PAIR cancel, licensed
--        by (bwf-↓x), with the two reps agreeing by xrep-stored;
--   §9c  the Example-3-shaped tower merged twice, and the REFUTATION of the
--        mrg₂ (TOPLAS "keep the outer type") form on it;
--   §9d  THE TWO LIMITS of the landed ⊕: the external-face equation is a
--        rule PREMISE and not a lemma (an ⇒-faced counterexample), and the
--        scope premise can fail on an alias cancel.  Both come with the
--        alternative merged boundary that DOES work, so the obstruction is
--        ⊕'s eager push-out and not Merge itself;
--   §9e  the TOPLAS three-agent adversary re-checked against the live ⊕:
--        their shape does not reach our cancel clause (nor, under ⊕-γ's
--        side condition, our Merge at all), the appended merge types with
--        both authorities kept — and there the RIGHT B₂′ is the mrg₂ one,
--        which is the other half of §9c's refutation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §9a.  THE CANCEL PAIR.  (7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ --Merge--→ 7 ⟪ ∅ , ℕ ⟫
-- --Drop∅--→ 7.  Cited from strong.BReduction, where the rule's worked
-- example lives (PLAN §1's Method).
------------------------------------------------------------------------

merge-c : [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ -→ ($ 7) ⟪ [] , `ℕ ⟫
merge-c = Merge V-$ ok-c

drop-c : [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ -→ $ 7
drop-c = Drop∅ V-$

types-c : [] ∣ [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ ⦂ `ℕ
types-c = ⊢redex-c

types-c′ : [] ∣ [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ ⦂ `ℕ
types-c′ = ⊢contractum-c

types-c″ : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
types-c″ = ⊢final-c

-- *** CANCEL-AGREE FOR AN ORDINARY PAIR ***, through the GENERAL lemma
-- (strong.BReduction's rep-stored / cancel-agree — the ≡-analogue of
-- DualDef's xrep-stored): the interior's knowledge at a reveal slot IS the
-- reading of that reveal's STORED rep …
cancel-agree-gen : `ℕ ≡ dnT 1 (rawRead Θ2c (ρᵇ Θ2c 0))
cancel-agree-gen = cancel-agree {Δ₀ = []} Θ2c 0 (s≤s z≤n) here

-- … and the deleted conceal's own (bwf-↓) premise ties ITS rep to that same
-- knowledge, read BACK OUT through the boundary.  Between them, the rep the
-- cancel keeps and the rep the deleted reveal carried are one type.
cancel-rev-c : Reversal≈ (intOf [] Θ2c) Θ1c 0 `ℕ `ℕ
cancel-rev-c = ≡→≈ refl

cancel-agree-c : outRead Θ1c `ℕ ≡ upRep 0 `ℕ
cancel-agree-c = refl

------------------------------------------------------------------------
-- §9b.  E★'s CONTINUATION TOWER, MERGED — THE X-PAIR CANCEL.
--
-- T4 = (5 ⟪ Θᵈ , ℕ ⟫) ⟪ ↑Z:=Y , ↓X:=ℕ , ℕ ⟫  (§2) is a nested wrapper, and
-- the cancelling pair is Θᵈ's ↓Z:=Y — the conceal the whole x-licence
-- exists for — against Θ★'s ↑Z:=Y.  The composite keeps the dual's ↑Y:⋆
-- and ↑X:=ℕ and Θ★'s ↓X:=ℕ; both faces are ℕ, so the merge is exact.
------------------------------------------------------------------------

Θmg : BCtx
Θmg = dualᵛ ⊕ Θ★

_ : Θmg ≡ rvl⋆ ∷ rvl `ℕ ∷ cnc 1 `ℕ ∷ []
_ = refl

-- the interiors compose ON THE NOSE here (the dual's rebuild is exact)
_ : intOf Γ★ Θmg ≡ Γ★
_ = refl

bwf-Θmg : Γ★ ∣ intOf Γ★ Θmg ⊢ᵇ Θmg
bwf-Θmg =
  bwf⋆ (bwf↑ wf-ℕ (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))

ok-★ : MergeOK Γ★ dualᵛ Θ★ `ℕ `ℕ
ok-★ = s≤s z≤n , bwf-Θmg , sc-ℕ , ≼≈-refl Γ★ , refl

merge-★ : Γ★ ⊢ T4 -→ ($ 5) ⟪ Θmg , `ℕ ⟫
merge-★ = Merge V-$ ok-★

⊢merged-★ : Γ★ ∣ [] ⊢ ($ 5) ⟪ Θmg , `ℕ ⟫ ⦂ `ℕ
⊢merged-★ = env bwf-Θmg sc-ℕ ⊢$

-- *** CANCEL-AGREE FOR THE X-PAIR ***  the interior's x-entry at Θ★'s
-- reveal slot records exactly the stored rep (xrep-stored), so the two reps
-- of the cancelling pair are SYNTACTICALLY EQUAL at the dual's birth, and
-- the skeleton premise the licence carries is free (dual-cnc-skel).
cancel-agree-x : (` 0) ≡ ρᵇ Θ★ 0
cancel-agree-x = xrep-stored Θ★ 0 Θ★ 0 (s≤s z≤n) xlic-E★′

cancel-skel-x : SkelEq (ρᵇ Θ★ 0) (` 0)
cancel-skel-x = dual-cnc-skel {Δ₀ = Γ★} Θ★ 0 (s≤s z≤n) xlic-E★′

-- … and the whole tower under the outermost ↑X:=ℕ still steps, by ξ-Λ /
-- ξ-⟪⟫ carrying the index into the interior where the merge happens
merge-★full : [] ⊢ T4full -→ (Λ (($ 5) ⟪ Θmg , `ℕ ⟫)) ⟪ Θ1 , `∀ `ℕ ⟫
merge-★full = ξ-⟪⟫ (ξ-Λ merge-★)

------------------------------------------------------------------------
-- §9c.  THE EXAMPLE-3-SHAPED TOWER, MERGED TWICE (strong.BReduction's
-- worked example (c)) — and the REFUTATION of the mrg₂ form.
------------------------------------------------------------------------

tower-types : Δtw ∣ []
  ⊢ ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  ⦂ (` 0 ⇒ ` 0)
tower-types = ⊢tower

tower-merge₁ : Δtw ⊢
  ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  -→ (Vtw ⟪ Θtw1 ⊕ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
tower-merge₁ = ξ-⟪⟫ (Merge (V-G G-ƛ) ok-tw1)

tower-merge₂ : Δtw ⊢ (Vtw ⟪ Θtw1 ⊕ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  -→ Vtw ⟪ Θtw⊕ , ` 0 ⇒ ` 0 ⟫
tower-merge₂ = Merge (V-G G-ƛ) ok-tw2

tower-merged : Δtw ∣ [] ⊢ Vtw ⟪ Θtw⊕ , ` 0 ⇒ ` 0 ⟫ ⦂ (` 0 ⇒ ` 0)
tower-merged = ⊢tower″

-- *** THE mrg₂ FORM IS REFUTED HERE. ***  "Keep the OUTER boundary type"
-- transports B₂ = Z₂→Z₂ to the composite's Z₂ SLOT — but the body is typed
-- at Z₃, the composite's own first reveal, and the two differ (they are
-- ≈Δ̄-equal in the merged interior, which typing does not see).  This is
-- why the landed B₂′ is the B₁-pushed-out form mrgB.
_ : substᵗ (mrg₂ Θtw1 Θtw2) (` 0 ⇒ ` 0) ≡ (` 1 ⇒ ` 1)
_ = refl

¬γ-mrg₂-tower :
  ¬ (substᵗ (γᵇ (Θtw1 ⊕ Θtw2)) (substᵗ (mrg₂ Θtw1 Θtw2) (` 0 ⇒ ` 0))
     ≡ substᵗ (γᵇ Θtw1) (` 0 ⇒ ` 0))
¬γ-mrg₂-tower ()

-- the landed form, by contrast, is exact on both faces here
γ-mrgB-tower : substᵗ (γᵇ (Θtw1 ⊕ Θtw2)) (mrgB Θtw1 Θtw2 (` 0 ⇒ ` 0))
             ≡ substᵗ (γᵇ Θtw1) (` 0 ⇒ ` 0)
γ-mrgB-tower = refl

ρ-mrgB-tower : substᵗ (ρᵇ (Θtw1 ⊕ Θtw2)) (mrgB Θtw1 Θtw2 (` 0 ⇒ ` 0))
             ≡ substᵗ (ρᵇ Θtw2) (` 0 ⇒ ` 0)
ρ-mrgB-tower = refl

------------------------------------------------------------------------
-- §9d.  THE TWO LIMITS OF THE LANDED ⊕.
--
-- (i) THE EXTERNAL FACE IS A PREMISE, NOT A LEMMA.  Δcx = X:=ℕ; the outer
-- boundary CONCEALS X at ℕ and its boundary type NAMES X (X⇒ℕ); the inner
-- one re-reveals a fresh W at that same ℕ (W⇒ℕ).  Everything type-checks,
-- and the term is an ⇒-faced nested wrapper — a NestedApp redex.  But ⊕
-- pushes the inner reveal's rep OUT through Θ₂, which resolves it to ℕ, so
-- the composite exports ℕ⇒ℕ where the redex had X⇒ℕ: the merge would DROP
-- X's abstraction (TOPLAS's authority warning, in our syntax).  The
-- boundary that DOES work keeps the abstract witness — rvl (` 0), i.e. the
-- reveal re-abstracted AT X — so the obstruction is ⊕'s eager push-out,
-- not Merge.
------------------------------------------------------------------------

Δcx : TCtx
Δcx = rvld `ℕ ∷ []

Θcx2 Θcx1 : BCtx
Θcx2 = cnc 0 `ℕ ∷ []                   -- ↓X:=ℕ  (the OUTER boundary)
Θcx1 = rvl `ℕ ∷ []                     -- ↑W:=ℕ  (the INNER one)

Vcx : Term
Vcx = ƛ ` 0 ∙ ($ 3)

⊢redex-cx : Δcx ∣ []
  ⊢ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫ ⦂ (` 0 ⇒ `ℕ)
⊢redex-cx =
  env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[])
      (sc-⇒ (sc-var hereᵒ) sc-ℕ)
      (env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) sc-ℕ)
           (⊢ƛ (wf-var here-rvld) ⊢$))

_ : Θcx1 ⊕ Θcx2 ≡ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

_ : mrgB Θcx1 Θcx2 (` 0 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
_ = refl

-- the composite's external face is ℕ⇒ℕ, the redex's type is X⇒ℕ
¬ext-cx : ¬ (substᵗ (ρᵇ (Θcx1 ⊕ Θcx2)) (mrgB Θcx1 Θcx2 (` 0 ⇒ `ℕ))
             ≡ substᵗ (ρᵇ Θcx2) (` 0 ⇒ `ℕ))
¬ext-cx ()

-- … so the merged wrapper is NOT typable at the redex's type: MergeOK's
-- last component is genuinely load-bearing
¬⊢merged-cx : ¬ (Δcx ∣ []
  ⊢ Vcx ⟪ Θcx1 ⊕ Θcx2 , mrgB Θcx1 Θcx2 (` 0 ⇒ `ℕ) ⟫ ⦂ (` 0 ⇒ `ℕ))
¬⊢merged-cx ⊢M with env-ty ⊢M
¬⊢merged-cx ⊢M | ()

-- THE REPAIR: a merged boundary whose reveal keeps the abstract witness.
-- Both faces are then exactly the redex's, and its interior is the nested
-- one on the nose.
Θcx′ : BCtx
Θcx′ = rvl (` 0) ∷ cnc 0 `ℕ ∷ []

_ : intOf Δcx Θcx′ ≡ intOf (intOf Δcx Θcx2) Θcx1
_ = refl

_ : substᵗ (γᵇ Θcx′) (` 0 ⇒ `ℕ) ≡ substᵗ (γᵇ Θcx1) (` 0 ⇒ `ℕ)
_ = refl

_ : substᵗ (ρᵇ Θcx′) (` 0 ⇒ `ℕ) ≡ substᵗ (ρᵇ Θcx2) (` 0 ⇒ `ℕ)
_ = refl

⊢repair-cx : Δcx ∣ [] ⊢ Vcx ⟪ Θcx′ , ` 0 ⇒ `ℕ ⟫ ⦂ (` 0 ⇒ `ℕ)
⊢repair-cx =
  env (bwf↑ (wf-var here-rvld) (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) sc-ℕ)
      (⊢ƛ (wf-var here-rvld) ⊢$)

------------------------------------------------------------------------
-- (ii) THE SCOPE PREMISE CAN FAIL ON AN ALIAS CANCEL.  Take E★′'s admitted
-- alias residue (strong.Boundary's Ξalias: ↑V:⋆ , ↓Z:=V) as the INNER
-- boundary over Θ★'s interior, with a boundary type that NAMES the aliased
-- slot.  The cancel deletes ↓Z:=V against Θ★'s ↑Z:=Y and leaves the
-- rep-less ↑V:⋆ — whose baseS slot is `blk`, so the merged boundary type
-- (which is that very slot) is UNSCOPED.  Again the repair exists: keep
-- Θ★'s reveal instead of the alias's ⋆-reveal.
------------------------------------------------------------------------

Θal : BCtx
Θal = Ξalias                           -- ↑V:⋆ , ↓Z:=V  over Θ★'s interior

Val : Term
Val = ƛ ` 0 ∙ ($ 5)

⊢redex-al : Γ★ ∣ []
  ⊢ (Val ⟪ Θal , ` 1 ⇒ `ℕ ⟫) ⟪ Θ★ , ` 0 ⇒ ` 2 ⟫ ⦂ (` 0 ⇒ ` 1)
⊢redex-al =
  env bwf-Θ★ (sc-⇒ (sc-var hereᵒ) (sc-var (thereᵒ (thereᵒ hereᵒ))))
      (env (bwf⋆ (bwf↓x herex refl sk-var (wf-var here-abst) bwf[]))
           (sc-⇒ (sc-var (thereᵒ hereᵒ)) sc-ℕ)
           (⊢ƛ (wf-var here-abst) ⊢$))

_ : Θal ⊕ Θ★ ≡ rvl⋆ ∷ cnc 1 `ℕ ∷ []
_ = refl

_ : mrgB Θal Θ★ (` 1 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
_ = refl

_ : baseS (Θal ⊕ Θ★) Γ★ ≡ blk ∷ blk ∷ ok ∷ []
_ = refl

¬sc-al : ¬ (Scoped (baseS (Θal ⊕ Θ★) Γ★) (mrgB Θal Θ★ (` 1 ⇒ `ℕ)))
¬sc-al (sc-⇒ (sc-var ()) _)

-- THE REPAIR: re-reveal at Y (Θ★'s own rep) instead of keeping the ⋆-slot
Θal′ : BCtx
Θal′ = rvl (` 0) ∷ cnc 1 `ℕ ∷ []

_ : intOf Γ★ Θal′ ≡ intOf Γ★ Θ★                -- the same interior
_ = refl

_ : substᵗ (γᵇ Θal′) (` 0 ⇒ ` 2) ≡ substᵗ (γᵇ Θal) (` 1 ⇒ `ℕ)
_ = refl

_ : substᵗ (ρᵇ Θal′) (` 0 ⇒ ` 2) ≡ substᵗ (ρᵇ Θ★) (` 0 ⇒ ` 2)
_ = refl

⊢repair-al : Γ★ ∣ [] ⊢ Val ⟪ Θal′ , ` 0 ⇒ ` 2 ⟫ ⦂ (` 0 ⇒ ` 1)
⊢repair-al =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var (thereᵒ (thereᵒ hereᵒ))))
      (⊢ƛ (wf-var here-xrvld) ⊢$)

------------------------------------------------------------------------
-- §9e.  THE TOPLAS THREE-AGENT ADVERSARY (p. 1048–49), against the LIVE ⊕
-- (ported from notes/old/D1Probe.agda §5).
--
--   δ_i(t) = int , δ_j(s) = t , δ_k = ⊥ ,  the k-term ⌈⌈3_i⌉^t_i⌉^s_j
--
-- Their shape is CONCEAL-OF-CONCEAL, so our deleting cancel never fires on
-- it: ⊕ APPENDS both hidings and the middle agent's contribution survives
-- as the pushed-in rep.  It does not even reach Merge here, because ⊕-γ's
-- side condition (Θ₁ drops only slots Θ₂ reveals) fails — a sufficient
-- condition, not a necessary one, and this is the shape it over-refuses.
------------------------------------------------------------------------

Δag : TCtx                             -- s := t (0) , t := ℕ (1)
Δag = rvld (` 0) ∷ rvld `ℕ ∷ []

Θag-o Θag-i : BCtx
Θag-o = cnc 0 (` 0) ∷ []               -- agent j: hide s, rep t
Θag-i = cnc 0 `ℕ ∷ []                  -- agent i: hide t, rep ℕ

_ : intOf Δag Θag-o ≡ rvld `ℕ ∷ []
_ = refl

⊢Tag : Δag ∣ [] ⊢ (($ 3) ⟪ Θag-i , ` 0 ⟫) ⟪ Θag-o , ` 0 ⟫ ⦂ ` 0
⊢Tag = env (bwf↓ here (≡→≈ refl) (wf-var here-rvld) bwf[])
           (sc-var hereᵒ)
           (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

-- ⊕ APPENDS: no entry is deleted, so no authority is dropped
_ : Θag-i ⊕ Θag-o ≡ cnc 1 `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

-- the middle authority ("s is t") is what discharges the second conceal's
-- reversal premise, through Δag's own chain — the ≈Δ̄ congruence's job
mid-authority : `ℕ ≈Δ̄⟨ Δag ⟩ (` 1)
mid-authority = ≈unf refl

⊢merged-ag : Δag ∣ [] ⊢ ($ 3) ⟪ Θag-i ⊕ Θag-o , ` 0 ⟫ ⦂ ` 0
⊢merged-ag =
  env (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ
            (bwf↓ here mid-authority wf-ℕ bwf[]))
      (sc-var hereᵒ) ⊢$

-- *** THE OTHER HALF OF THE B₂′ DILEMMA. ***  On THIS shape the merged
-- boundary type that works is the mrg₂ (outer) one — ` 0, the concealed
-- variable itself — while the landed mrg₁ form gives the composite's
-- SECOND slot and the wrong external face.  §9c refutes mrg₂ and this
-- refutes mrg₁: NEITHER single transport is right everywhere, which is
-- exactly why the external face is a rule premise.
_ : substᵗ (mrg₂ Θag-i Θag-o) (` 0) ≡ ` 0
_ = refl

_ : mrgB Θag-i Θag-o (` 0) ≡ ` 1
_ = refl

ρ-mrg₂-ag : substᵗ (ρᵇ (Θag-i ⊕ Θag-o)) (substᵗ (mrg₂ Θag-i Θag-o) (` 0))
          ≡ substᵗ (ρᵇ Θag-o) (` 0)
ρ-mrg₂-ag = refl

¬ρ-mrgB-ag : ¬ (substᵗ (ρᵇ (Θag-i ⊕ Θag-o)) (mrgB Θag-i Θag-o (` 0))
                ≡ substᵗ (ρᵇ Θag-o) (` 0))
¬ρ-mrgB-ag ()

-- APPEND-ONLY, for the record, is still not available to US where the
-- cancel DOES fire: the appended boundary is inadmissible over any
-- exterior, because an inner conceal of an outer REVEAL points at a slot
-- that exists only in the composite's own reveal block.
Θ⊞ : BCtx
Θ⊞ = cnc 0 `ℕ ∷ rvl `ℕ ∷ []

¬bwf-append : ∀ {Ψ : TCtx} → Bwf [] Ψ Θ⊞ Θ⊞ → ⊥
¬bwf-append (bwf↓  () _ _ _)
¬bwf-append (bwf↓x () _ _ _ _)

-- and towers DO collapse to bare values where the composite empties: §9a's
-- cancel pair is the witness, and Drop∅ is what finishes it
tower-collapses : [] ⊢ ($ 7) ⟪ Θ1c ⊕ Θ2c , mrgB Θ1c Θ2c (` 0) ⟫ -→ $ 7
tower-collapses = Drop∅ V-$

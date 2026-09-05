module strong.DualIntProof where

-- THE REBUILD LAW, IN ITS STRONGEST TRUE FORM.
--
-- strong.DualDef's third residue is
--
--   DualInt≈ :  Δ ∣ intOf Δ Θ ⊢ᵇ Θ  →  Δ ≼≈ intOf (intOf Δ Θ) (dualᴳ Δ Θ)
--
-- and it is FALSE as stated — machine-checked in
-- notes/probes/DualIntProbe.agda, at TWO slots, both of which the dual
-- sends to the rep-LESS reveal rvl⋆ and the rebuild therefore reads back
-- as `abst`, while Δ's own entry is not abst:
--
--   (x)  an EXTERIOR-READ slot of Δ that Θ drops without concealing
--        (DualDef's entᴳ-x)                       — ¬DualInt-x
--   (B⋆) a REVEALED slot of Δ whose rep BOTH copy guards refuse
--        (DualDef's entᴳ-B⋆)                      — ¬DualInt-B⋆
--
-- and _≼≈_ has no clause putting xrvld or rvld on the LEFT above abst on
-- the RIGHT.  WEAKENING _≼≈_ to add such a clause is UNSOUND, also
-- machine-checked there (§3): the three transports ⊢retag≈ runs on
-- (≼≈-∋:= , ≼≈-∋:=x , ≼≈→Absorbs) all fail at the new clause, and the
-- failure is REACHABLE — probe §3.3 exhibits a live Peel redex whose
-- crossing argument W is a value whose own boundary conceals the demoted
-- slot by ordinary knowledge, and W does not retype in the rebuild
-- (¬⊢W-rebuild).  The crossing's type discipline does not exclude it,
-- because the crossing type reaches the blocked slot through a REVEAL REP
-- of Θ, and bwf↑ licenses a reveal rep to be any Δ-type.
--
-- So the repair is route 3(ii): keep _≼≈_ and add a HYPOTHESIS.  This file
-- delivers the sharpest such statement — the hypothesis is exactly a
-- PER-SLOT condition on the cmax Θ slots that Θ DROPS, and nothing else:
--
--   dual-int≈ : (∀ {Δ Θ} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → DualIntHead Δ Θ) → DualInt≈
--
-- Everything the residue used to contain about the KEPT slots, about the
-- length bookkeeping, and about the dual's conceal block is discharged
-- here as a theorem:
--
--   * cmax-bwf     — a well-formed boundary never conceals past Δ's end,
--                    so the length side condition is free;
--   * rebuild-≡    — the rebuild really is [dual's reveal block] ++ Δ's
--                    KEPT tail: the dual's conceal block contributes no
--                    interior entry, and its cmax eats exactly Θ's reveal
--                    block (revs-dual / cmax-dual);
--   * ≼≈-head      — the kept tail is therefore related to itself, on the
--                    nose, and the ordering is decided slot by slot on the
--                    dropped block alone.
--
-- Two closed corollaries fall out with no residue at all:
--
--   dual-int-nodrop — a boundary that conceals nothing rebuilds Δ EXACTLY;
--   dual-int-abst   — if every dropped slot of Δ is abstract (the Λ-bound
--                     case), the rebuild law holds outright, whatever the
--                     dual does at those slots.
--
-- WHICH REPAIR THIS EMBODIES: 3(ii), the hypothesis route, in its
-- strongest form (the hypothesis mentions only the dropped block).  The
-- weakened-_≼≈_ route 3(i) is refuted, not deferred.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n; _⊔_)
open import Data.Nat.Properties
  using (suc-injective; ⊔-lub; +-identityʳ; +-suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_; entAt; _∋tv_;
         here-abst; here-rvld; here-xrvld;
         skip-abst; skip-rvld; skip-xrvld; ∋:=→∋tv; ∋:=x→∋tv)
open import strong.Unfold using (_≈Δ̄⟨_⟩_)
open import strong.Boundary
  using (BCtx; BEntry; rvl; rvl⋆; cnc; cnc⋆; revs; cmax; dropN;
         revEnts; len-revEnts; intOf; Bwf; bwf[]; bwf↑; bwf⋆; bwf↓;
         bwf↓x; bwf⋆↓; _∣_⊢ᵇ_)
open import strong.BReduction
  using (rvlsᴳ; cncOfRevs; dualᴳ; entᴳ; revs-rvlsᴳ; cmax-dual;
         RvlE; is-rvl; is-⋆; entᴳ-RvlE;
         _≼≈_; ≼≈[]; ≼≈abst; ≼≈xrvld; ≼≈rvld; ≼≈-refl)
open import strong.DualDef using (DualInt≈)

------------------------------------------------------------------------
-- §1  THE PER-SLOT ORDERING.  One constructor per clause of _≼≈_, read as
-- a relation between the entry Δ holds at a slot and the entry the rebuild
-- holds there, with the rebuild's own TAIL at that slot as the context in
-- which knowledge is compared (that is where ≼≈rvld takes its ≈Δ̄).
------------------------------------------------------------------------

data EntLe (T : TCtx) : TyEntry → TyEntry → Set where
  el-abst : ∀ {E}   → EntLe T abst E                       -- abst ≼ anything
  el-x    : ∀ {A}   → EntLe T (xrvld A) (xrvld A)          -- x-mark preserved
  el-rvld : ∀ {A B} → A ≈Δ̄⟨ T ⟩ B → EntLe T (rvld A) (rvld B)

el-≡ : ∀ {T T' E E' F F'} → T ≡ T' → E ≡ E' → F ≡ F'
     → EntLe T E F → EntLe T' E' F'
el-≡ refl refl refl p = p

------------------------------------------------------------------------
-- §2  THE ORDERING IS DECIDED BLOCK BY BLOCK.  Two contexts sharing a
-- TAIL are ordered as soon as their HEADS are ordered slot by slot — and
-- the shared tail contributes nothing to prove, which is the whole reason
-- the residue below mentions only the dropped block.
------------------------------------------------------------------------

≼≈-head : ∀ (H H' T : TCtx) → length H ≡ length H'
        → (∀ s → s < length H
             → EntLe ((H' ++ T) ↓ s) (entAt H s) (entAt H' s))
        → (H ++ T) ≼≈ (H' ++ T)
≼≈-head []       []          T le h = ≼≈-refl T
≼≈-head []       (E' ∷ H₁')  T ()  h
≼≈-head (E ∷ H₁) []          T ()  h
≼≈-head (E ∷ H₁) (abst ∷ H₁')     T le h with h 0 (s≤s z≤n)
≼≈-head (abst ∷ H₁) (abst ∷ H₁')  T le h | el-abst =
  ≼≈abst (≼≈-head H₁ H₁' T (suc-injective le)
                  (λ s lt → h (suc s) (s≤s lt)))
≼≈-head (E ∷ H₁) (rvld B ∷ H₁')      T le h with h 0 (s≤s z≤n)
≼≈-head (abst ∷ H₁) (rvld B ∷ H₁')   T le h | el-abst =
  ≼≈abst (≼≈-head H₁ H₁' T (suc-injective le)
                  (λ s lt → h (suc s) (s≤s lt)))
≼≈-head (rvld A ∷ H₁) (rvld B ∷ H₁') T le h | el-rvld e =
  ≼≈rvld (≼≈-head H₁ H₁' T (suc-injective le)
                  (λ s lt → h (suc s) (s≤s lt))) e
≼≈-head (E ∷ H₁) (xrvld B ∷ H₁')       T le h with h 0 (s≤s z≤n)
≼≈-head (abst ∷ H₁) (xrvld B ∷ H₁')    T le h | el-abst =
  ≼≈abst (≼≈-head H₁ H₁' T (suc-injective le)
                  (λ s lt → h (suc s) (s≤s lt)))
≼≈-head (xrvld B ∷ H₁) (xrvld B ∷ H₁') T le h | el-x =
  ≼≈xrvld (≼≈-head H₁ H₁' T (suc-injective le)
                   (λ s lt → h (suc s) (s≤s lt)))

------------------------------------------------------------------------
-- §3  LIST BOOKKEEPING.  takeN is the complement of the development's own
-- dropN; nothing here knows about boundaries.
------------------------------------------------------------------------

takeN : ℕ → TCtx → TCtx
takeN zero    Γ       = []
takeN (suc n) []      = []
takeN (suc n) (E ∷ Γ) = E ∷ takeN n Γ

take++drop : ∀ n (Γ : TCtx) → takeN n Γ ++ dropN n Γ ≡ Γ
take++drop zero    Γ       = refl
take++drop (suc n) []      = refl
take++drop (suc n) (E ∷ Γ) = cong (E ∷_) (take++drop n Γ)

len-take : ∀ n (Γ : TCtx) → n ≤ length Γ → length (takeN n Γ) ≡ n
len-take zero    Γ       le       = refl
len-take (suc n) []      ()
len-take (suc n) (E ∷ Γ) (s≤s le) = cong suc (len-take n Γ le)

entAt-take : ∀ n (Γ : TCtx) s → s < n → entAt (takeN n Γ) s ≡ entAt Γ s
entAt-take zero    Γ       s       ()
entAt-take (suc n) []      s       lt       = refl
entAt-take (suc n) (E ∷ Γ) zero    lt       = refl
entAt-take (suc n) (E ∷ Γ) (suc s) (s≤s lt) = entAt-take n Γ s lt

entAt-app : ∀ (L M : TCtx) s → s < length L → entAt (L ++ M) s ≡ entAt L s
entAt-app []      M s       ()
entAt-app (E ∷ L) M zero    lt       = refl
entAt-app (E ∷ L) M (suc s) (s≤s lt) = entAt-app L M s lt

dropN-app : ∀ (L M : TCtx) n → length L ≡ n → dropN n (L ++ M) ≡ M
dropN-app []      M zero    e = refl
dropN-app []      M (suc n) ()
dropN-app (E ∷ L) M zero    ()
dropN-app (E ∷ L) M (suc n) e = dropN-app L M n (suc-injective e)

------------------------------------------------------------------------
-- §4  THE LENGTH SIDE CONDITION IS FREE.  A well-formed boundary conceals
-- only slots that exist, so cmax never runs past Δ's end.
------------------------------------------------------------------------

∋tv-len : ∀ {Δ : TCtx} {X} → Δ ∋tv X → suc X ≤ length Δ
∋tv-len here-abst      = s≤s z≤n
∋tv-len here-rvld      = s≤s z≤n
∋tv-len here-xrvld     = s≤s z≤n
∋tv-len (skip-abst p)  = s≤s (∋tv-len p)
∋tv-len (skip-rvld p)  = s≤s (∋tv-len p)
∋tv-len (skip-xrvld p) = s≤s (∋tv-len p)

cmax-bwf : ∀ {Δ Ψ : TCtx} {Θ : BCtx} (Ξ : BCtx)
         → Bwf Δ Ψ Θ Ξ → cmax Ξ ≤ length Δ
cmax-bwf []             bwf[]                    = z≤n
cmax-bwf (rvl A ∷ Ξ)    (bwf↑ wfA b)             = cmax-bwf Ξ b
cmax-bwf (rvl⋆ ∷ Ξ)     (bwf⋆ b)                 = cmax-bwf Ξ b
cmax-bwf (cnc X A ∷ Ξ)  (bwf↓ p rev wfA b)       =
  ⊔-lub (∋tv-len (∋:=→∋tv p)) (cmax-bwf Ξ b)
cmax-bwf (cnc X A ∷ Ξ)  (bwf↓x p so sk wfA b)    =
  ⊔-lub (∋tv-len (∋:=x→∋tv p)) (cmax-bwf Ξ b)
cmax-bwf (cnc⋆ X ∷ Ξ)   (bwf⋆↓ p b)              =
  ⊔-lub (∋tv-len p) (cmax-bwf Ξ b)

------------------------------------------------------------------------
-- §5  THE SHAPE OF THE REBUILD.  The dual's CONCEAL block (cncOfRevs)
-- contributes no interior entry at all — it is all conceals — and its cmax
-- is exactly revs Θ, which is the length of Θ's own reveal block, so it
-- eats it whole.  What is left is [the dual's reveal block, read] ++ [Δ's
-- kept tail].
------------------------------------------------------------------------

revEnts-cnc : ∀ (Θᵈ : BCtx) j j' (Θ : BCtx)
            → revEnts Θᵈ j (cncOfRevs j' Θ) ≡ []
revEnts-cnc Θᵈ j j' []            = refl
revEnts-cnc Θᵈ j j' (rvl A ∷ Θ)   = revEnts-cnc Θᵈ j (suc j') Θ
revEnts-cnc Θᵈ j j' (rvl⋆ ∷ Θ)    = revEnts-cnc Θᵈ j (suc j') Θ
revEnts-cnc Θᵈ j j' (cnc X A ∷ Θ) = revEnts-cnc Θᵈ j j' Θ
revEnts-cnc Θᵈ j j' (cnc⋆ X ∷ Θ)  = revEnts-cnc Θᵈ j j' Θ

revEnts-++cnc : ∀ (Θᵈ : BCtx) j (Ξ Θ : BCtx)
              → revEnts Θᵈ j (Ξ ++ cncOfRevs 0 Θ) ≡ revEnts Θᵈ j Ξ
revEnts-++cnc Θᵈ j []            Θ = revEnts-cnc Θᵈ j 0 Θ
revEnts-++cnc Θᵈ j (rvl A ∷ Ξ)   Θ =
  cong (_∷_ _) (revEnts-++cnc Θᵈ (suc j) Ξ Θ)
revEnts-++cnc Θᵈ j (rvl⋆ ∷ Ξ)    Θ =
  cong (abst ∷_) (revEnts-++cnc Θᵈ (suc j) Ξ Θ)
revEnts-++cnc Θᵈ j (cnc X A ∷ Ξ) Θ = revEnts-++cnc Θᵈ j Ξ Θ
revEnts-++cnc Θᵈ j (cnc⋆ X ∷ Ξ)  Θ = revEnts-++cnc Θᵈ j Ξ Θ

-- the dual's reveal block, READ into the rebuild's dropped block
headᴰ : TCtx → BCtx → TCtx
headᴰ Δ Θ = revEnts (dualᴳ Δ Θ) 0 (rvlsᴳ (cmax Θ) 0 Δ Θ)

len-headᴰ : ∀ (Δ : TCtx) (Θ : BCtx) → length (headᴰ Δ Θ) ≡ cmax Θ
len-headᴰ Δ Θ =
  trans (len-revEnts (dualᴳ Δ Θ) 0 (rvlsᴳ (cmax Θ) 0 Δ Θ))
        (revs-rvlsᴳ (cmax Θ) 0 Δ Θ)

rebuild-≡ : ∀ (Δ : TCtx) (Θ : BCtx)
          → intOf (intOf Δ Θ) (dualᴳ Δ Θ) ≡ headᴰ Δ Θ ++ dropN (cmax Θ) Δ
rebuild-≡ Δ Θ =
  cong₂ _++_
    (revEnts-++cnc (dualᴳ Δ Θ) 0 (rvlsᴳ (cmax Θ) 0 Δ Θ) Θ)
    (trans (cong (λ n → dropN n (intOf Δ Θ)) (cmax-dual Δ Θ))
           (dropN-app (revEnts Θ 0 Θ) (dropN (cmax Θ) Δ) (revs Θ)
                      (len-revEnts Θ 0 Θ)))

------------------------------------------------------------------------
-- §6  THE THEOREM.  The rebuild law reduces, with no residue anywhere
-- else, to a PER-SLOT condition on the cmax Θ slots the boundary DROPS.
------------------------------------------------------------------------

-- the residue, stated slot by slot on the dropped block alone
DualIntHead : TCtx → BCtx → Set
DualIntHead Δ Θ = ∀ s → s < cmax Θ
  → EntLe (intOf (intOf Δ Θ) (dualᴳ Δ Θ) ↓ s)
          (entAt Δ s)
          (entAt (intOf (intOf Δ Θ) (dualᴳ Δ Θ)) s)

dual-int-head : ∀ (Δ : TCtx) (Θ : BCtx) → cmax Θ ≤ length Δ
              → DualIntHead Δ Θ
              → Δ ≼≈ intOf (intOf Δ Θ) (dualᴳ Δ Θ)
dual-int-head Δ Θ le h =
  subst₂ _≼≈_ (take++drop (cmax Θ) Δ) (sym (rebuild-≡ Δ Θ))
    (≼≈-head (takeN (cmax Θ) Δ) (headᴰ Δ Θ) (dropN (cmax Θ) Δ)
             (trans (len-take (cmax Θ) Δ le) (sym (len-headᴰ Δ Θ)))
             h')
  where
    h' : ∀ s → s < length (takeN (cmax Θ) Δ)
       → EntLe ((headᴰ Δ Θ ++ dropN (cmax Θ) Δ) ↓ s)
               (entAt (takeN (cmax Θ) Δ) s) (entAt (headᴰ Δ Θ) s)
    h' s lt = el-≡ (cong (_↓ s) (rebuild-≡ Δ Θ))
                   (sym (entAt-take (cmax Θ) Δ s lt'))
                   (trans (cong (λ Ψ → entAt Ψ s) (rebuild-≡ Δ Θ))
                          (entAt-app (headᴰ Δ Θ) (dropN (cmax Θ) Δ) s
                                     (subst (s <_) (sym (len-headᴰ Δ Θ))
                                            lt')))
                   (h s lt')
      where
        lt' : s < cmax Θ
        lt' = subst (s <_) (len-take (cmax Θ) Δ le) lt

-- *** THE DELIVERED STATEMENT ***  DualInt≈ holds as soon as the dropped
-- block does, and the dropped block is all that is left to rule on.
dual-int≈ : (∀ {Δ : TCtx} {Θ : BCtx} → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → DualIntHead Δ Θ)
          → DualInt≈
dual-int≈ h {Δ} {Θ} bwf = dual-int-head Δ Θ (cmax-bwf Θ bwf) (h bwf)

------------------------------------------------------------------------
-- §7  TWO CLOSED COROLLARIES — no residue, no hypothesis beyond a
-- condition on Δ and Θ that is decidable by inspection.
------------------------------------------------------------------------

-- (a) a boundary that CONCEALS NOTHING rebuilds Δ exactly.
dual-int-nodrop : ∀ (Δ : TCtx) (Θ : BCtx) → cmax Θ ≡ 0
                → Δ ≼≈ intOf (intOf Δ Θ) (dualᴳ Δ Θ)
dual-int-nodrop Δ Θ e =
  dual-int-head Δ Θ (subst (_≤ length Δ) (sym e) z≤n) hd
  where
    hd : DualIntHead Δ Θ
    hd s lt with subst (s <_) e lt
    hd s lt | ()

-- (b) if every DROPPED slot of Δ is abstract — the Λ-bound case, which
-- is what the design's own commentary calls exact by construction — the
-- rebuild law holds outright, WHATEVER the dual emits at those slots.
-- This is the corner the two counterexamples sit just outside of: they
-- differ from it only in that Δ's dropped entry is xrvld / rvld.
dual-int-abst : ∀ (Δ : TCtx) (Θ : BCtx) → cmax Θ ≤ length Δ
              → (∀ s → s < cmax Θ → entAt Δ s ≡ abst)
              → Δ ≼≈ intOf (intOf Δ Θ) (dualᴳ Δ Θ)
dual-int-abst Δ Θ le ha =
  dual-int-head Δ Θ le
    (λ s lt → el-≡ refl (sym (ha s lt)) refl el-abst)

------------------------------------------------------------------------
-- §8  … AND THAT COROLLARY IS EXACTLY AS FAR AS ONE CAN GET AT AN rvl⋆
-- SLOT.  Wherever the dual falls back on the rep-LESS reveal, the rebuild
-- entry is `abst` on the nose, and then the residue at that slot DEMANDS
-- entAt Δ s ≡ abst — there is no other EntLe with abst on the right.  So
-- the two counterexamples of notes/probes/DualIntProbe.agda are not
-- accidents of their instances: DualDef's entᴳ-x and entᴳ-B⋆ each produce
-- an rvl⋆ at a NON-abstract slot of Δ, and every such slot refutes the
-- rebuild law.  This is the general statement of the residue's obstruction.
------------------------------------------------------------------------

entAt-rev-R : ∀ {E} → RvlE E → ∀ (Θᵈ : BCtx) j (Ξ : BCtx) q
            → entAt (revEnts Θᵈ j (E ∷ Ξ)) (suc q)
            ≡ entAt (revEnts Θᵈ (suc j) Ξ) q
entAt-rev-R is-rvl Θᵈ j Ξ q = refl
entAt-rev-R is-⋆   Θᵈ j Ξ q = refl

-- the dual's reveal at the p-th dropped slot is entᴳ Δ Θ (s + p) (c ∸ suc p)
-- (rvlsᴳ counts the deeper dual reveals DOWN as it walks the slots UP)
entAt-rvls-⋆ : ∀ (Θᵈ : BCtx) (Δ : TCtx) (Θ : BCtx) c s j p → p < c
             → entᴳ Δ Θ (s + p) (c ∸ suc p) ≡ rvl⋆
             → entAt (revEnts Θᵈ j (rvlsᴳ c s Δ Θ)) p ≡ abst
entAt-rvls-⋆ Θᵈ Δ Θ zero    s j p       ()       e
entAt-rvls-⋆ Θᵈ Δ Θ (suc c) s j zero    lt       e
  with entᴳ Δ Θ s c
     | subst (λ n → entᴳ Δ Θ n c ≡ rvl⋆) (+-identityʳ s) e
entAt-rvls-⋆ Θᵈ Δ Θ (suc c) s j zero lt e | rvl A   | ()
entAt-rvls-⋆ Θᵈ Δ Θ (suc c) s j zero lt e | rvl⋆    | _  = refl
entAt-rvls-⋆ Θᵈ Δ Θ (suc c) s j zero lt e | cnc X A | ()
entAt-rvls-⋆ Θᵈ Δ Θ (suc c) s j zero lt e | cnc⋆ X  | ()
entAt-rvls-⋆ Θᵈ Δ Θ (suc c) s j (suc p) (s≤s lt) e =
  trans (entAt-rev-R (entᴳ-RvlE Δ Θ s c) Θᵈ j (rvlsᴳ c (suc s) Δ Θ) p)
        (entAt-rvls-⋆ Θᵈ Δ Θ c (suc s) (suc j) p lt
          (subst (λ n → entᴳ Δ Θ n (c ∸ suc p) ≡ rvl⋆) (+-suc s p) e))

rebuild-⋆ : ∀ (Δ : TCtx) (Θ : BCtx) s → s < cmax Θ
          → entᴳ Δ Θ s (cmax Θ ∸ suc s) ≡ rvl⋆
          → entAt (intOf (intOf Δ Θ) (dualᴳ Δ Θ)) s ≡ abst
rebuild-⋆ Δ Θ s lt e =
  trans (cong (λ Ψ → entAt Ψ s) (rebuild-≡ Δ Θ))
        (trans (entAt-app (headᴰ Δ Θ) (dropN (cmax Θ) Δ) s
                          (subst (s <_) (sym (len-headᴰ Δ Θ)) lt))
               (entAt-rvls-⋆ (dualᴳ Δ Θ) Δ Θ (cmax Θ) 0 0 s lt e))

el-abst⁻ : ∀ {T E} → EntLe T E abst → E ≡ abst
el-abst⁻ el-abst = refl

-- *** THE RESIDUE'S EXACT OBSTRUCTION ***  at every slot the dual sends to
-- rvl⋆, DualIntHead says nothing more and nothing less than "Δ was abstract
-- there".  DualDef's entᴳ-x (an x-revealed dropped slot) and entᴳ-B⋆ (a
-- revealed dropped slot both guards refuse) are precisely the two ways that
-- fails.
head-⋆-abst : ∀ (Δ : TCtx) (Θ : BCtx) → DualIntHead Δ Θ
            → ∀ s → s < cmax Θ → entᴳ Δ Θ s (cmax Θ ∸ suc s) ≡ rvl⋆
            → entAt Δ s ≡ abst
head-⋆-abst Δ Θ h s lt e =
  el-abst⁻ (el-≡ refl refl (rebuild-⋆ Δ Θ s lt e) (h s lt))

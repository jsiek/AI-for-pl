module strong.notes.MergeProbe where

-- DESIGN PROBE (not part of the development) for DECISIONS.md Decision 3:
-- the boundary composition  Θ₁ ⊕ Θ₂  behind Zdancewic et al.'s rule (8),
--
--   Merge : Value V → (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V ⟪ Θ₁ ⊕ Θ₂ , B? ⟫
--
-- Setting: exterior Δ; Θ₂ has interior Ψ₂ = intOf Δ Θ₂; Θ₁ has exterior Ψ₂
-- and interior Ψ₁ = intOf Ψ₂ Θ₁; the middle-type equation
--   substᵗ (ρᵇ Θ₁) B₁ ≡ substᵗ (γᵇ Θ₂) B₂  (both = the type of V ⟪ Θ₁ , B₁ ⟫).
--
-- Contents
--   §1  the three index maps and the definition of _⊕_
--   §2  revs/cmax of Θ₁ ⊕ Θ₂; ⊕-int                          ✓ general (shape)
--       ¬⊕-int′ / ¬⊕-intR: FAILS for either knowledge-carrying interior
--   §3  the frame maps mrg₁ (Θ₁'s frame → ⊕'s frame) and mrg₂
--   §4  the faces on Example 8's T5; the cancel pair; THE OBSTRUCTION
--       (no-merge: a typed redex with NO merged boundary type at all)
--   §5  ⊕-γ (internal face)               ✓ general, given cmax Θ₁ ≤ revs Θ₂
--   §6  ⊕-ρ-pt (external face, away from the cancelled slots)   ✓ general
--   §7  ⊕-ρ            ✓ general, given the cancelled-slot round trip (§7b)
--   §8  the Merge rule, B₂′, Aligned / MergeOK, the counterexamples
--   §9  ⊕-bwf: refuted for GroundedProbe's untransported bwf↓′; scope
--   §10 depth-1 values, and the stuck term Merge cannot reach
--
-- Nothing here edits any other file.

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (+-identityʳ; +-suc; +-assoc; +-comm; ⊔-assoc; ⊔-comm;
         ⊔-identityʳ; ⊔-lub; m≤m⊔n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m; ≤-trans; <⇒≤;
         ≰⇒>; +-distribˡ-⊔; ∸-distribʳ-⊔; m+n∸m≡n; n≤1+n; ≤-refl;
         m≤m+n; +-cancelˡ-≡; _≟_; m≤n⊔m; m+[n∸m]≡n; 0∸n≡0;
         m≤n⇒m∸n≡0; ≮⇒≥; +-∸-assoc; m+n≮m; ≤⇒≯; ∸-monoˡ-<; +-monoʳ-<;
         n≤0⇒n≡0; ≤-pred)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import strong.Types
open import strong.TypeSubst using (_⨟ᵗ_; sub-sub; subst-cong; subst-id)
open import strong.Types using (substᵗ-renᵗ)
open import strong.Context
  using (TCtx; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         _∋_:=_; here; Ctx; _∋_⦂_; there; ⤊)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; _-→_;
         TyBeta; Beta; TyWrap; Wrap; ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫;
         repOf; dualᵇ; shiftReps; polyid; ∀ZZ;
         prepId-lo; prepId-hi; split; acc-of; baseS-acc)
open import strong.notes.GroundedProbe
  using (intOf′; revEnts; _∣_⊢ᵇ′_; bwf[]′; bwf↑′; bwf↓′;
         _∣_⊢′_⦂_; ⊢`′; ⊢$′; ⊢ƛ′; ⊢·′; ⊢Λ′; ⊢·[]′; env′;
         _≼_; ≼[]; ≼abst; ≼rvld; ≼-refl; ⊢retag′; cancel-agree;
         bwf-repOf; ∋:=-head; Θi; Θn; Δ8′; ⊢T5body; ⊢inner)

private
  variable
    Δ Ψ : TCtx
    Γₜ : Ctx
    A B B₀ B₁ B₂ : Ty
    M V : Term
    Θ Θ₁ Θ₂ : BCtx
    X i j : ℕ

------------------------------------------------------------------------
-- §1.  The index maps, and _⊕_
--
-- Three index spaces meet.  Write r₁ = revs Θ₁, c₁ = cmax Θ₁, r₂ = revs Θ₂,
-- c₂ = cmax Θ₂.
--
--   Δ    : the exterior.
--   Ψ₂   = intOf Δ Θ₂  = [r₂ reveals of Θ₂] ++ dropN c₂ Δ.
--          So Ψ₂-slot X<r₂ is Θ₂'s reveal X, and Ψ₂-slot r₂+i is Δ-slot c₂+i.
--   Ψ₁   = intOf Ψ₂ Θ₁ = [r₁ reveals of Θ₁] ++ dropN c₁ Ψ₂.
--
-- and two boundary FRAMES (the space B₀ is read in):
--   frame Θ₂ = [r₂ reveals] ++ Δ    (X<r₂ ↦ reveal X; r₂+i ↦ Δ-slot i)
--   frame Θ₁ = [r₁ reveals] ++ Ψ₂
--
-- `outSub Θ₂` pushes a Ψ₂-type OUT to a Δ-type (used on Θ₁'s reveal reps, which
-- must become Δ-types in the composite); `inSub Θ₁` pushes a Ψ₂-type IN to a
-- Ψ₁-type (used on Θ₂'s conceal reps, which must become Ψ₁-types).
------------------------------------------------------------------------

outSub : BCtx → Substᵗ                 -- Ψ₂-index ↦ Δ-type
outSub Θ X with X <? revs Θ
outSub Θ X | yes _ = ρᵇ Θ X
outSub Θ X | no  _ = ` (cmax Θ + (X ∸ revs Θ))

inSub : BCtx → Substᵗ                  -- Ψ₂-index ↦ Ψ₁-type
inSub Θ = γcnc (revs Θ) (cmax Θ) Θ

-- Θ₁'s entries, re-based from Ψ₂ to Δ.  A reveal keeps being a reveal, its rep
-- pushed out.  A conceal of a Ψ₂-slot that is one of Θ₂'s REVEALS cancels
-- against that reveal (both disappear — Zdancewic (H4) / (8)); a conceal of an
-- inherited exterior slot Ψ₂-slot r₂+k = Δ-slot c₂+k re-indexes to Δ.
mapL : BCtx → BCtx → BCtx              -- mapL Θ₂ Θ₁
mapL Θ₂ []             = []
mapL Θ₂ (rvl A   ∷ Θ) = rvl (substᵗ (outSub Θ₂) A) ∷ mapL Θ₂ Θ
mapL Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
mapL Θ₂ (cnc X A ∷ Θ) | yes _ = mapL Θ₂ Θ
mapL Θ₂ (cnc X A ∷ Θ) | no  _ =
  cnc (cmax Θ₂ + (X ∸ revs Θ₂)) A ∷ mapL Θ₂ Θ

-- Θ₂'s entries, re-based to the interior Ψ₁.  A reveal survives iff Θ₁ did not
-- drop its slot (reveal j is Ψ₂-slot j, dropped iff j < c₁); its rep is a
-- Δ-type already.  A conceal keeps its Δ-index; its rep is pushed in.
-- j = the running reveal index of Θ₂.
mapR : BCtx → ℕ → BCtx → BCtx          -- mapR Θ₁ j Θ₂
mapR Θ₁ j []             = []
mapR Θ₁ j (rvl A   ∷ Θ) with j <? cmax Θ₁
mapR Θ₁ j (rvl A   ∷ Θ) | yes _ = mapR Θ₁ (suc j) Θ
mapR Θ₁ j (rvl A   ∷ Θ) | no  _ = rvl A ∷ mapR Θ₁ (suc j) Θ
mapR Θ₁ j (cnc X A ∷ Θ) =
  cnc X (substᵗ (inSub Θ₁) A) ∷ mapR Θ₁ j Θ

infixl 5 _⊕_
_⊕_ : BCtx → BCtx → BCtx
Θ₁ ⊕ Θ₂ = mapL Θ₂ Θ₁ ++ mapR Θ₁ 0 Θ₂

------------------------------------------------------------------------
-- §2.  revs / cmax of the composite, and ⊕-int.
--
--   revs (Θ₁ ⊕ Θ₂) = r₁ + (r₂ ∸ c₁)     cmax (Θ₁ ⊕ Θ₂) = c₂ + (c₁ ∸ r₂)
--
-- (the two are complementary: if c₁ ≤ r₂ only reveals of Θ₂ are lost and the
-- composite's cmax is Θ₂'s; if c₁ > r₂ ALL of Θ₂'s reveals are lost and the
-- composite additionally drops c₁ ∸ r₂ exterior slots below c₂.)
------------------------------------------------------------------------

revs-++ : ∀ Θ Θ' → revs (Θ ++ Θ') ≡ revs Θ + revs Θ'
revs-++ []            Θ' = refl
revs-++ (rvl A   ∷ Θ) Θ' = cong suc (revs-++ Θ Θ')
revs-++ (cnc X A ∷ Θ) Θ' = revs-++ Θ Θ'

cmax-++ : ∀ Θ Θ' → cmax (Θ ++ Θ') ≡ cmax Θ ⊔ cmax Θ'
cmax-++ []            Θ' = refl
cmax-++ (rvl A   ∷ Θ) Θ' = cmax-++ Θ Θ'
cmax-++ (cnc X A ∷ Θ) Θ' =
  trans (cong (suc X ⊔_) (cmax-++ Θ Θ'))
        (sym (⊔-assoc (suc X) (cmax Θ) (cmax Θ')))

revs-mapL : ∀ Θ₂ Θ₁ → revs (mapL Θ₂ Θ₁) ≡ revs Θ₁
revs-mapL Θ₂ []             = refl
revs-mapL Θ₂ (rvl A   ∷ Θ) = cong suc (revs-mapL Θ₂ Θ)
revs-mapL Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
revs-mapL Θ₂ (cnc X A ∷ Θ) | yes _ = revs-mapL Θ₂ Θ
revs-mapL Θ₂ (cnc X A ∷ Θ) | no  _ = revs-mapL Θ₂ Θ

cmax-mapR : ∀ Θ₁ j Θ₂ → cmax (mapR Θ₁ j Θ₂) ≡ cmax Θ₂
cmax-mapR Θ₁ j []             = refl
cmax-mapR Θ₁ j (rvl A   ∷ Θ) with j <? cmax Θ₁
cmax-mapR Θ₁ j (rvl A   ∷ Θ) | yes _ = cmax-mapR Θ₁ (suc j) Θ
cmax-mapR Θ₁ j (rvl A   ∷ Θ) | no  _ = cmax-mapR Θ₁ (suc j) Θ
cmax-mapR Θ₁ j (cnc X A ∷ Θ) = cong (suc X ⊔_) (cmax-mapR Θ₁ j Θ)

-- number of surviving Θ₂-reveals, counted from reveal index j
drop-lo : ∀ m n → n < m → m ∸ n ≡ suc (m ∸ suc n)
drop-lo (suc m) zero    _       = refl
drop-lo (suc m) (suc n) (s≤s p) = drop-lo m n p

revs-mapR : ∀ Θ₁ j Θ₂ → revs (mapR Θ₁ j Θ₂) ≡ revs Θ₂ ∸ (cmax Θ₁ ∸ j)
revs-mapR Θ₁ j []            = sym (0∸n≡0 (cmax Θ₁ ∸ j))
revs-mapR Θ₁ j (rvl A ∷ Θ) with j <? cmax Θ₁
revs-mapR Θ₁ j (rvl A ∷ Θ) | yes lt
  rewrite drop-lo (cmax Θ₁) j lt = revs-mapR Θ₁ (suc j) Θ
revs-mapR Θ₁ j (rvl A ∷ Θ) | no  ge rewrite m≤n⇒m∸n≡0 (≮⇒≥ ge) =
  cong suc (trans (revs-mapR Θ₁ (suc j) Θ)
                  (cong (revs Θ ∸_)
                        (m≤n⇒m∸n≡0 (≤-trans (≮⇒≥ ge) (n≤1+n j)))))
revs-mapR Θ₁ j (cnc X A ∷ Θ) = revs-mapR Θ₁ j Θ

-- mapL's conceals: those at an inherited exterior slot re-index to Δ; the ones
-- that cancel are gone.  Only the ⊔ with cmax Θ₂ is uniform (when c₁ ≤ r₂ the
-- left side contributes nothing at all).
cmax-mapL⊔ : ∀ Θ₂ Θ₁
  → cmax (mapL Θ₂ Θ₁) ⊔ cmax Θ₂ ≡ cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)
cmax-mapL⊔ Θ₂ []            =
  sym (trans (cong (cmax Θ₂ +_) (0∸n≡0 (revs Θ₂)))
             (+-identityʳ (cmax Θ₂)))
cmax-mapL⊔ Θ₂ (rvl A ∷ Θ)   = cmax-mapL⊔ Θ₂ Θ
cmax-mapL⊔ Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
cmax-mapL⊔ Θ₂ (cnc X A ∷ Θ) | yes lt =
  trans (cmax-mapL⊔ Θ₂ Θ)
        (cong (cmax Θ₂ +_)
              (sym (trans (∸-distribʳ-⊔ (revs Θ₂) (suc X) (cmax Θ))
                          (cong (_⊔ (cmax Θ ∸ revs Θ₂))
                                (m≤n⇒m∸n≡0 lt)))))
cmax-mapL⊔ Θ₂ (cnc X A ∷ Θ) | no ge =
  trans (⊔-assoc (suc (cmax Θ₂ + (X ∸ revs Θ₂)))
                 (cmax (mapL Θ₂ Θ)) (cmax Θ₂))
        (trans (cong (suc (cmax Θ₂ + (X ∸ revs Θ₂)) ⊔_) (cmax-mapL⊔ Θ₂ Θ))
               (sym rhs))
  where
    ge′ : revs Θ₂ ≤ X
    ge′ = ≮⇒≥ ge
    step : suc X ∸ revs Θ₂ ≡ suc (X ∸ revs Θ₂)
    step = +-∸-assoc 1 ge′
    rhs : cmax Θ₂ + ((suc X ⊔ cmax Θ) ∸ revs Θ₂)
        ≡ suc (cmax Θ₂ + (X ∸ revs Θ₂)) ⊔ (cmax Θ₂ + (cmax Θ ∸ revs Θ₂))
    rhs = trans (cong (cmax Θ₂ +_) (∸-distribʳ-⊔ (revs Θ₂) (suc X) (cmax Θ)))
          (trans (+-distribˡ-⊔ (cmax Θ₂) (suc X ∸ revs Θ₂) (cmax Θ ∸ revs Θ₂))
                 (cong (_⊔ (cmax Θ₂ + (cmax Θ ∸ revs Θ₂)))
                       (trans (cong (cmax Θ₂ +_) step)
                              (+-suc (cmax Θ₂) (X ∸ revs Θ₂)))))

revs-⊕ : ∀ Θ₁ Θ₂ → revs (Θ₁ ⊕ Θ₂) ≡ revs Θ₁ + (revs Θ₂ ∸ cmax Θ₁)
revs-⊕ Θ₁ Θ₂ =
  trans (revs-++ (mapL Θ₂ Θ₁) (mapR Θ₁ 0 Θ₂))
        (cong₂ _+_ (revs-mapL Θ₂ Θ₁)
                   (trans (revs-mapR Θ₁ 0 Θ₂) refl))

cmax-⊕ : ∀ Θ₁ Θ₂ → cmax (Θ₁ ⊕ Θ₂) ≡ cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)
cmax-⊕ Θ₁ Θ₂ =
  trans (cmax-++ (mapL Θ₂ Θ₁) (mapR Θ₁ 0 Θ₂))
        (trans (cong (cmax (mapL Θ₂ Θ₁) ⊔_) (cmax-mapR Θ₁ 0 Θ₂))
               (cmax-mapL⊔ Θ₂ Θ₁))

-- context plumbing
prepAbst-+ : ∀ m n (Φ : TCtx) → prepAbst (m + n) Φ ≡ prepAbst m (prepAbst n Φ)
prepAbst-+ zero    n Φ = refl
prepAbst-+ (suc m) n Φ = cong (abst ∷_) (prepAbst-+ m n Φ)

dropN-dropN : ∀ m n (Δ : TCtx) → dropN n (dropN m Δ) ≡ dropN (m + n) Δ
dropN-dropN zero    n Δ       = refl
dropN-dropN (suc m) n []      = drop[] n
  where
    drop[] : ∀ k → dropN k [] ≡ []
    drop[] zero    = refl
    drop[] (suc k) = refl
dropN-dropN (suc m) n (E ∷ Δ) = dropN-dropN m n Δ

dropN-prepAbst : ∀ c r (Φ : TCtx)
  → dropN c (prepAbst r Φ) ≡ prepAbst (r ∸ c) (dropN (c ∸ r) Φ)
dropN-prepAbst zero    r       Φ = cong (prepAbst r) (sym dz)
  where
    dz : dropN (0 ∸ r) Φ ≡ Φ
    dz rewrite 0∸n≡0 r = refl
dropN-prepAbst (suc c) zero    Φ = refl
dropN-prepAbst (suc c) (suc r) Φ = dropN-prepAbst c r Φ

-- ⊕-int : contexts compose (the CURRENT intOf, abstract reveal entries).
⊕-int : ∀ (Δ : TCtx) Θ₁ Θ₂ → intOf Δ (Θ₁ ⊕ Θ₂) ≡ intOf (intOf Δ Θ₂) Θ₁
⊕-int Δ Θ₁ Θ₂
  rewrite revs-⊕ Θ₁ Θ₂ | cmax-⊕ Θ₁ Θ₂
        | dropN-prepAbst (cmax Θ₁) (revs Θ₂) (dropN (cmax Θ₂) Δ)
  = trans (prepAbst-+ (revs Θ₁) (revs Θ₂ ∸ cmax Θ₁)
                      (dropN (cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)) Δ))
          (cong (λ Φ → prepAbst (revs Θ₁) (prepAbst (revs Θ₂ ∸ cmax Θ₁) Φ))
                (sym (dropN-dropN (cmax Θ₂) (cmax Θ₁ ∸ revs Θ₂) Δ)))

-- … but ⊕-int FAILS for GroundedProbe's intOf′ (Decision 1's KNOWLEDGE
-- entries).  intOf′ stores a reveal's rep as written — read in the boundary's
-- exterior — and the composite's exterior is Δ while Θ₁'s is Ψ₂, so the entry
-- that ⊕ contributes is the PUSHED-OUT rep.  Both readings denote the same
-- type, but ≼ (and bwf↓′) compare them syntactically.
Θa Θb : BCtx
Θa = rvl (` 0) ∷ []            -- Θ₁ : reveal W := Z   (Z = Θ₂'s reveal)
Θb = rvl `ℕ ∷ []               -- Θ₂ : reveal Z := ℕ

_ : intOf′ [] Θb ≡ rvld `ℕ ∷ []
_ = refl

_ : Θa ⊕ Θb ≡ rvl `ℕ ∷ rvl `ℕ ∷ []
_ = refl

_ : intOf′ (intOf′ [] Θb) Θa ≡ rvld (` 0) ∷ rvld `ℕ ∷ []
_ = refl

_ : intOf′ [] (Θa ⊕ Θb) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

¬⊕-int′ : ¬ (intOf′ [] (Θa ⊕ Θb) ≡ intOf′ (intOf′ [] Θb) Θa)
¬⊕-int′ ()

¬⊕-int′≼ : ¬ (intOf′ (intOf′ [] Θb) Θa ≼ intOf′ [] (Θa ⊕ Θb))
¬⊕-int′≼ ()

-- The same pair also refutes ⊕-int for the REFINED reading of Decision 1
-- (DECISIONS.md 2026-09-04: the interior entry is ⟦A⟧ = A[γΘ], the INTERIOR
-- reading of the reveal's rep).  Nested, W's entry is the reveal variable Z;
-- merged, it is Z's own rep ℕ — the two agree only after UNFOLDING, i.e.
-- only under Zdancewic's Δ̄_i (iterate δ), never syntactically.  So no
-- knowledge-carrying interior composes on the nose, and Merge's contractum
-- must be retyped along an unfolding relation (a ≼ with an unfold step),
-- not along _≡_ or GroundedProbe's _≼_.
rdRep : BCtx → Ty → Ty
rdRep Θ A = substᵗ (γᵇ Θ) (renameᵗ (revs Θ +_) A)

revEntsR : BCtx → BCtx → TCtx
revEntsR Θ []            = []
revEntsR Θ (rvl A   ∷ Ξ) = rvld (rdRep Θ A) ∷ revEntsR Θ Ξ
revEntsR Θ (cnc X A ∷ Ξ) = revEntsR Θ Ξ

intOfR : TCtx → BCtx → TCtx
intOfR Δ Θ = revEntsR Θ Θ ++ dropN (cmax Θ) Δ

_ : intOfR [] Θb ≡ rvld `ℕ ∷ []
_ = refl

_ : intOfR (intOfR [] Θb) Θa ≡ rvld (` 1) ∷ rvld `ℕ ∷ []
_ = refl

_ : intOfR [] (Θa ⊕ Θb) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

¬⊕-intR : ¬ (intOfR [] (Θa ⊕ Θb) ≡ intOfR (intOfR [] Θb) Θa)
¬⊕-intR ()

¬⊕-intR≼ : ¬ (intOfR (intOfR [] Θb) Θa ≼ intOfR [] (Θa ⊕ Θb))
¬⊕-intR≼ ()

-- (the same pair is fine for the current intOf: both sides all-abstract)
_ : intOf [] (Θa ⊕ Θb) ≡ intOf (intOf [] Θb) Θa
_ = ⊕-int [] Θa Θb

------------------------------------------------------------------------
-- §3.  The frame maps.
--
-- ⊕'s frame is [r₁ reveals of Θ₁][surviving reveals of Θ₂][Δ], of width
-- R = revs (Θ₁ ⊕ Θ₂) before Δ, and its interior Ψ₁ drops C = cmax (Θ₁ ⊕ Θ₂)
-- exterior slots.  upF embeds Ψ₁ back into that frame; mrg₁ / mrg₂ carry
-- Θ₁'s / Θ₂'s frame into it.  Both are SUBSTITUTIONS, not renamings: a slot
-- killed by the cancel clause has to be replaced by the agreed rep.
------------------------------------------------------------------------

R⊕ C⊕ : BCtx → BCtx → ℕ
R⊕ Θ₁ Θ₂ = revs Θ₁ + (revs Θ₂ ∸ cmax Θ₁)
C⊕ Θ₁ Θ₂ = cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)

upF : ℕ → ℕ → ℕ → ℕ                  -- Ψ₁-index ↦ ⊕-frame index
upF R C j with j <? R
upF R C j | yes _ = j
upF R C j | no  _ = R + (C + (j ∸ R))

up⊕ : BCtx → BCtx → ℕ → ℕ
up⊕ Θ₁ Θ₂ = upF (R⊕ Θ₁ Θ₂) (C⊕ Θ₁ Θ₂)

-- a Ψ₂-index, into ⊕'s frame
mrgΨ : BCtx → BCtx → ℕ → Ty
mrgΨ Θ₁ Θ₂ X with X <? revs Θ₂
mrgΨ Θ₁ Θ₂ X | yes _ with X <? cmax Θ₁
mrgΨ Θ₁ Θ₂ X | yes _ | yes _ =
  renameᵗ (up⊕ Θ₁ Θ₂) (repOf X Θ₁)                       -- CANCELLED slot
mrgΨ Θ₁ Θ₂ X | yes _ | no  _ = ` (revs Θ₁ + (X ∸ cmax Θ₁))
mrgΨ Θ₁ Θ₂ X | no  _ =
  ` (R⊕ Θ₁ Θ₂ + (cmax Θ₂ + (X ∸ revs Θ₂)))

mrg₁ : BCtx → BCtx → Substᵗ          -- Θ₁'s frame ↦ ⊕'s frame
mrg₁ Θ₁ Θ₂ j with j <? revs Θ₁
mrg₁ Θ₁ Θ₂ j | yes _ = ` j
mrg₁ Θ₁ Θ₂ j | no  _ = mrgΨ Θ₁ Θ₂ (j ∸ revs Θ₁)

mrg₂ : BCtx → BCtx → Substᵗ          -- Θ₂'s frame ↦ ⊕'s frame
mrg₂ Θ₁ Θ₂ j with j <? revs Θ₂
mrg₂ Θ₁ Θ₂ j | yes _ with j <? cmax Θ₁
mrg₂ Θ₁ Θ₂ j | yes _ | yes _ =
  renameᵗ (up⊕ Θ₁ Θ₂) (repOf j Θ₁)                       -- CANCELLED slot
mrg₂ Θ₁ Θ₂ j | yes _ | no  _ = ` (revs Θ₁ + (j ∸ cmax Θ₁))
mrg₂ Θ₁ Θ₂ j | no  _ = ` (R⊕ Θ₁ Θ₂ + (j ∸ revs Θ₂))

------------------------------------------------------------------------
-- §4.  The two faces on Example 8's T5 — and why NEITHER B₁ nor B₂ alone
-- can be the merged boundary type.
--
--   T5body = ((ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫) ⟪ Θn , ` 0 ⇒ ` 0 ⟫   : Y→Y
--   Δ8′ = [Y , X:=ℕ] ;  Ψ₂ = intOf Δ8′ Θn = [Z] ;  Ψ₁ = [W , Z]
------------------------------------------------------------------------

Δ8 : TCtx
Δ8 = abst ∷ abst ∷ []

Θ⊕8 : BCtx
Θ⊕8 = Θi ⊕ Θn

_ : Θ⊕8 ≡ rvl (` 0) ∷ rvl (` 0) ∷ cnc 1 `ℕ ∷ []
_ = refl

_ : intOf Δ8 Θ⊕8 ≡ intOf (intOf Δ8 Θn) Θi          -- ⊕-int, on the example
_ = ⊕-int Δ8 Θi Θn

_ : intOf′ Δ8′ Θ⊕8 ≡ intOf′ (intOf′ Δ8′ Θn) Θi     -- and for intOf′ too here
_ = refl

-- the two transported boundary types
B₁8 B₂8 : Ty
B₁8 = substᵗ (mrg₁ Θi Θn) (` 0 ⇒ ` 0)    -- from the INNER boundary type
B₂8 = substᵗ (mrg₂ Θi Θn) (` 0 ⇒ ` 0)    -- from the OUTER boundary type

_ : B₁8 ≡ ` 0 ⇒ ` 0
_ = refl

_ : B₂8 ≡ ` 1 ⇒ ` 1
_ = refl

-- internal face: B₁'s transport is right, B₂'s is WRONG (it names Z, but the
-- merged interior types V = ƛ ` 0 ∙ ` 0 at W→W).
_ : substᵗ (γᵇ Θ⊕8) B₁8 ≡ substᵗ (γᵇ Θi) (` 0 ⇒ ` 0)
_ = refl

¬γ-B₂8 : ¬ (substᵗ (γᵇ Θ⊕8) B₂8 ≡ substᵗ (γᵇ Θi) (` 0 ⇒ ` 0))
¬γ-B₂8 ()

-- external face: both happen to be right here (Θi's reveal rep IS Θn's
-- reveal variable, so pushing it out lands on the same Δ-slot)
_ : substᵗ (ρᵇ Θ⊕8) B₁8 ≡ substᵗ (ρᵇ Θn) (` 0 ⇒ ` 0)
_ = refl

_ : substᵗ (ρᵇ Θ⊕8) B₂8 ≡ substᵗ (ρᵇ Θn) (` 0 ⇒ ` 0)
_ = refl

-- so on T5 the merged wrapper is  (ƛ ` 0 ∙ ` 0) ⟪ Θ⊕8 , ` 0 ⇒ ` 0 ⟫ , and it
-- types at the same type as T5body, both under ⊢ and under ⊢′.
mergedT5 : Term
mergedT5 = (ƛ ` 0 ∙ ` 0) ⟪ Θ⊕8 , ` 0 ⇒ ` 0 ⟫

⊢mergedT5 : Δ8′ ∣ [] ⊢′ mergedT5 ⦂ (` 0 ⇒ ` 0)
⊢mergedT5 =
  env′ (bwf↑′ (wf-var here-abst)
        (bwf↑′ (wf-var here-abst)
         (bwf↓′ (skip-abst here) wf-ℕ bwf[]′)))
       (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       (⊢ƛ′ (wf-var here-rvld) (⊢`′ here))

_ : Δ8′ ∣ [] ⊢′ ((ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫) ⟪ Θn , ` 0 ⇒ ` 0 ⟫
      ⦂ (` 0 ⇒ ` 0)
_ = ⊢T5body

------------------------------------------------------------------------
-- §4b.  The Cancel pair.  Θ₁ = ↓X:=ℕ conceals the very slot Θ₂ = ↑X:=ℕ
-- reveals: both entries disappear and the composite is EMPTY.  B₂ = ` 0
-- names the cancelled slot, so it must be REWRITTEN through the agreed rep —
-- which is what mrg₂'s cancel clause does (and mrg₁ agrees here).
------------------------------------------------------------------------

Θ1c Θ2c : BCtx
Θ1c = cnc 0 `ℕ ∷ []
Θ2c = rvl `ℕ ∷ []

_ : Θ1c ⊕ Θ2c ≡ []
_ = refl

_ : substᵗ (mrg₂ Θ1c Θ2c) (` 0) ≡ `ℕ
_ = refl

_ : substᵗ (mrg₁ Θ1c Θ2c) (` 0) ≡ `ℕ
_ = refl

_ : intOf′ [] (Θ1c ⊕ Θ2c) ≡ intOf′ (intOf′ [] Θ2c) Θ1c
_ = refl

⊢redex-c : [] ∣ [] ⊢′ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ ⦂ `ℕ
⊢redex-c = env′ (bwf↑′ wf-ℕ bwf[]′) (sc-var hereᵒ)
                (env′ (bwf↓′ here wf-ℕ bwf[]′) (sc-var hereᵒ) ⊢$′)

⊢contractum-c : [] ∣ [] ⊢′ ($ 7) ⟪ [] , `ℕ ⟫ ⦂ `ℕ
⊢contractum-c = env′ bwf[]′ sc-ℕ ⊢$′

------------------------------------------------------------------------
-- §4c.  THE OBSTRUCTION.  Merge needs ONE boundary type whose internal face
-- is V's type in Ψ₁ and whose external face is the redex's type in Δ.  Take
--
--   Δo = [X := ℕ→ℕ]      Θ₂ = ↓X:=ℕ→ℕ  (Ψ₂ = ∅)      Θ₁ = ↑W:=ℕ  (Ψ₁ = [W])
--   B₁ = W→W             B₂ = X        V  = ƛ ` 0 ∙ ` 0   (a PRIMVAL)
--
-- redex : X.  Internal face wanted: W→W (a type mentioning the fresh reveal).
-- External face wanted: the VARIABLE X.  In any composite, the only frame
-- slots whose ρ-face is a variable are the exterior slots, and the γ-face of
-- an exterior slot is either a variable (kept) or its conceal rep — which
-- Decision 1's invariant pins to Δo's knowledge ℕ→ℕ, never W→W.  So NO
-- boundary type works: Merge is stuck here.
------------------------------------------------------------------------

Δo : TCtx
Δo = rvld (`ℕ ⇒ `ℕ) ∷ []

Θ1o Θ2o : BCtx
Θ1o = rvl `ℕ ∷ []
Θ2o = cnc 0 (`ℕ ⇒ `ℕ) ∷ []

Vo : Term
Vo = ƛ ` 0 ∙ ` 0

redexo : Term
redexo = (Vo ⟪ Θ1o , ` 0 ⇒ ` 0 ⟫) ⟪ Θ2o , ` 0 ⟫

⊢redexo : Δo ∣ [] ⊢′ redexo ⦂ ` 0
⊢redexo =
  env′ (bwf↓′ here (wf-⇒ wf-ℕ wf-ℕ) bwf[]′) (sc-var hereᵒ)
       (env′ (bwf↑′ wf-ℕ bwf[]′) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
             (⊢ƛ′ (wf-var here-rvld) (⊢`′ here)))

redexo-value : Value redexo
redexo-value = V-⟪⟫ (V-⟪⟫ (V-G G-ƛ))

Θ⊕o : BCtx
Θ⊕o = Θ1o ⊕ Θ2o

_ : Θ⊕o ≡ rvl `ℕ ∷ cnc 0 (`ℕ ⇒ `ℕ) ∷ []
_ = refl

-- the contexts DO compose (both for intOf and intOf′) — the obstruction is
-- entirely about the boundary type.
_ : intOf Δo Θ⊕o ≡ intOf (intOf Δo Θ2o) Θ1o
_ = ⊕-int Δo Θ1o Θ2o

_ : intOf′ Δo Θ⊕o ≡ intOf′ (intOf′ Δo Θ2o) Θ1o
_ = refl

rvld-inj : ∀ {A B} → rvld A ≡ rvld B → A ≡ B
rvld-inj refl = refl

-- generic face lemmas
ρᵇ-hi : ∀ Θ i → ρᵇ Θ (revs Θ + i) ≡ ` i
ρᵇ-hi []            i = refl
ρᵇ-hi (rvl A ∷ Θ)   i = ρᵇ-hi Θ i
ρᵇ-hi (cnc X A ∷ Θ) i = ρᵇ-hi Θ i

γcnc-cases : ∀ r m Θ i
  → (γcnc r m Θ i ≡ ` (r + (i ∸ m)))
  ⊎ (isConc i Θ ≡ true × γcnc r m Θ i ≡ repOf i Θ)
γcnc-cases r m []            i = inj₁ refl
γcnc-cases r m (rvl A ∷ Θ)   i = γcnc-cases r m Θ i
γcnc-cases r m (cnc X A ∷ Θ) i with X ≟ i | i ≟ X
γcnc-cases r m (cnc X A ∷ Θ) i | yes _  | yes _ = inj₂ (refl , refl)
γcnc-cases r m (cnc X A ∷ Θ) i | yes p  | no ¬q = ⊥-elim (¬q (sym p))
γcnc-cases r m (cnc X A ∷ Θ) i | no ¬p | yes q  = ⊥-elim (¬p (sym q))
γcnc-cases r m (cnc X A ∷ Θ) i | no ¬p | no ¬q with γcnc-cases r m Θ i
γcnc-cases r m (cnc X A ∷ Θ) i | no ¬p | no ¬q | inj₁ e = inj₁ e
γcnc-cases r m (cnc X A ∷ Θ) i | no ¬p | no ¬q | inj₂ (c , e) = inj₂ (c , e)

γᵇ-lo : ∀ Θ X → X < revs Θ → γᵇ Θ X ≡ ` X
γᵇ-lo Θ X lt = prepId-lo (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) X lt

γᵇ-hi : ∀ Θ i → γᵇ Θ (revs Θ + i) ≡ γcnc (revs Θ) (cmax Θ) Θ i
γᵇ-hi Θ i = prepId-hi (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) i

-- THE THEOREM: over Δo, no ⊢ᵇ′-well-formed boundary and boundary type has
-- external face ` 0 and internal face ` 0 ⇒ ` 0.
no-merge : ∀ {Ψ} Θ B′ → Δo ∣ Ψ ⊢ᵇ′ Θ
  → substᵗ (ρᵇ Θ) B′ ≡ ` 0
  → ¬ (substᵗ (γᵇ Θ) B′ ≡ (` 0 ⇒ ` 0))
no-merge Θ (` X) b eρ eγ with split (revs Θ) X
no-merge Θ (` X) b eρ eγ | inj₁ lt
  with trans (sym (γᵇ-lo Θ X lt)) eγ
no-merge Θ (` X) b eρ eγ | inj₁ lt | ()
no-merge Θ (` X) b eρ eγ | inj₂ (i , refl)
  with trans (sym (ρᵇ-hi Θ i)) eρ
no-merge Θ (` X) b eρ eγ | inj₂ (.0 , refl) | refl
  with γcnc-cases (revs Θ) (cmax Θ) Θ 0
no-merge Θ (` X) b eρ eγ | inj₂ (.0 , refl) | refl | inj₁ e
  with trans (sym (trans (γᵇ-hi Θ 0) e)) eγ
... | ()
no-merge Θ (` X) b eρ eγ | inj₂ (.0 , refl) | refl | inj₂ (c , e)
  with trans (rvld-inj (∋:=-head (bwf-repOf Θ b 0 c)))
             (trans (sym (trans (γᵇ-hi Θ 0) e)) eγ)
... | ()
no-merge Θ `ℕ      b () eγ
no-merge Θ `𝔹      b () eγ
no-merge Θ (A ⇒ B) b () eγ
no-merge Θ (`∀ A)  b () eγ

-- … and the obstruction is EXACTLY Decision 1's invariant: under the current
-- (env)/bwf↓ — which lets a conceal invent any well-formed interior rep — the
-- merged wrapper DOES exist (rep ` 0 ⇒ ` 0 instead of Δo's knowledge ℕ→ℕ).
Θold : BCtx
Θold = rvl `ℕ ∷ cnc 0 (` 0 ⇒ ` 0) ∷ []

⊢redexo-old : Δo ∣ [] ⊢ redexo ⦂ ` 0
⊢redexo-old =
  env (bwf↓ here-rvld (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
      (env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
           (⊢ƛ (wf-var here-abst) (⊢` here)))

⊢mergedo-old : Δo ∣ [] ⊢ Vo ⟪ Θold , ` 1 ⟫ ⦂ ` 0
⊢mergedo-old =
  env (bwf↑ wf-ℕ (bwf↓ here-rvld (wf-⇒ (wf-var here-abst) (wf-var here-abst))
                        bwf[]))
      (sc-var (thereᵒ hereᵒ))
      (⊢ƛ (wf-var here-abst) (⊢` here))

¬⊢mergedo : ¬ (Δo ∣ [] ⊢′ Vo ⟪ Θold , ` 1 ⟫ ⦂ ` 0)
¬⊢mergedo (env′ (bwf↑′ _ (bwf↓′ () _ _)) _ _)

------------------------------------------------------------------------
-- §4d.  An Example-3-shaped tower (notes.md Example 3, last line), merged
-- twice.  Δ3 = [X:=𝔹];  Θ₃ = ↑Z₁:=X , ↓X:=𝔹 ;  Θ₂ = ↑Z₂:=Z₁ , ↑Y:=ℕ ;
-- Θ₁ = ↑Z₃:=Z₂ ;  V = λz:Z₃. z.  Here everything works: both merges keep
-- both faces, and (because every rep is ℕ or a slot that pushes out to
-- itself) even intOf′ composes.
------------------------------------------------------------------------

Δ3 : TCtx
Δ3 = rvld `𝔹 ∷ []

Θ3₃ Θ3₂ Θ3₁ : BCtx
Θ3₃ = rvl (` 0) ∷ cnc 0 `𝔹 ∷ []
Θ3₂ = rvl (` 0) ∷ rvl `ℕ ∷ []
Θ3₁ = rvl (` 0) ∷ []

_ : Θ3₁ ⊕ Θ3₂ ≡ rvl (` 0) ∷ rvl (` 0) ∷ rvl `ℕ ∷ []
_ = refl

Θ3⊕ : BCtx
Θ3⊕ = (Θ3₁ ⊕ Θ3₂) ⊕ Θ3₃

_ : Θ3⊕ ≡ rvl (` 0) ∷ rvl (` 0) ∷ rvl `ℕ ∷ rvl (` 0) ∷ cnc 0 `𝔹 ∷ []
_ = refl

_ : intOf′ Δ3 Θ3⊕
    ≡ intOf′ (intOf′ (intOf′ Δ3 Θ3₃) Θ3₂) Θ3₁
_ = refl

-- both merges preserve both faces
_ : substᵗ (γᵇ (Θ3₁ ⊕ Θ3₂)) (substᵗ (mrg₁ Θ3₁ Θ3₂) (` 0 ⇒ ` 0))
    ≡ substᵗ (γᵇ Θ3₁) (` 0 ⇒ ` 0)
_ = refl

_ : substᵗ (ρᵇ (Θ3₁ ⊕ Θ3₂)) (substᵗ (mrg₁ Θ3₁ Θ3₂) (` 0 ⇒ ` 0))
    ≡ substᵗ (ρᵇ Θ3₂) (` 0 ⇒ ` 0)
_ = refl

_ : substᵗ (γᵇ Θ3⊕) (substᵗ (mrg₁ (Θ3₁ ⊕ Θ3₂) Θ3₃) (` 0 ⇒ ` 0))
    ≡ substᵗ (γᵇ Θ3₁) (` 0 ⇒ ` 0)
_ = refl

_ : substᵗ (ρᵇ Θ3⊕) (substᵗ (mrg₁ (Θ3₁ ⊕ Θ3₂) Θ3₃) (` 0 ⇒ ` 0))
    ≡ substᵗ (ρᵇ Θ3₃) (` 0 ⇒ ` 0)
_ = refl

tower3 : Term
tower3 = (((ƛ ` 0 ∙ ` 0) ⟪ Θ3₁ , ` 0 ⇒ ` 0 ⟫) ⟪ Θ3₂ , ` 0 ⇒ ` 0 ⟫)
           ⟪ Θ3₃ , ` 0 ⇒ ` 0 ⟫

⊢tower3 : Δ3 ∣ [] ⊢′ tower3 ⦂ (` 0 ⇒ ` 0)
⊢tower3 =
  env′ (bwf↑′ (wf-var here-rvld) (bwf↓′ here wf-𝔹 bwf[]′))
       (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       (env′ (bwf↑′ (wf-var here-rvld) (bwf↑′ wf-ℕ bwf[]′))
             (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
             (env′ (bwf↑′ (wf-var here-rvld) bwf[]′)
                   (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
                   (⊢ƛ′ (wf-var here-rvld) (⊢`′ here))))

⊢merged3 : Δ3 ∣ [] ⊢′ (ƛ ` 0 ∙ ` 0) ⟪ Θ3⊕ , ` 0 ⇒ ` 0 ⟫ ⦂ (` 0 ⇒ ` 0)
⊢merged3 =
  env′ (bwf↑′ (wf-var here-rvld)
        (bwf↑′ (wf-var here-rvld)
         (bwf↑′ wf-ℕ (bwf↑′ (wf-var here-rvld) (bwf↓′ here wf-𝔹 bwf[]′)))))
       (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       (⊢ƛ′ (wf-var here-rvld) (⊢`′ here))

------------------------------------------------------------------------
-- §5.  The internal face DOES compose, in general, whenever Θ₁ conceals only
-- slots that Θ₂ revealed (cmax Θ₁ ≤ revs Θ₂ — true of every example here and
-- of every boundary a Wrap/TyWrap contractum builds over a fresh reveal).
--
--   ⊕-γ : Scoped (baseS Θ₁ Ψ₂) B₁
--       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (substᵗ (mrg₁ Θ₁ Θ₂) B₁)
--         ≡ substᵗ (γᵇ Θ₁) B₁
--
-- It is the EXTERNAL face that has no general law: §4c.
------------------------------------------------------------------------

γcnc-hi : ∀ r m Θ i → cmax Θ ≤ i → γcnc r m Θ i ≡ ` (r + (i ∸ m))
γcnc-hi r m []            i le = refl
γcnc-hi r m (rvl A ∷ Θ)   i le = γcnc-hi r m Θ i le
γcnc-hi r m (cnc X A ∷ Θ) i le with X ≟ i
γcnc-hi r m (cnc X A ∷ Θ) i le | yes refl =
  ⊥-elim (1+n≰n (≤-trans (m≤m⊔n (suc X) (cmax Θ)) le))
  where
    1+n≰n : ∀ {n} → ¬ (suc n ≤ n)
    1+n≰n (s≤s p) = 1+n≰n p
γcnc-hi r m (cnc X A ∷ Θ) i le | no _ =
  γcnc-hi r m Θ i (≤-trans (m≤n⊔m (suc X) (cmax Θ)) le)

γcnc-conc : ∀ r m Θ i → isConc i Θ ≡ true → γcnc r m Θ i ≡ repOf i Θ
γcnc-conc r m []            i ()
γcnc-conc r m (rvl A ∷ Θ)   i c = γcnc-conc r m Θ i c
γcnc-conc r m (cnc X A ∷ Θ) i c with X ≟ i | i ≟ X
γcnc-conc r m (cnc X A ∷ Θ) i c | yes _ | yes _ = refl
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | no ¬q = ⊥-elim (¬q (sym p))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | yes q = ⊥-elim (¬p (sym q))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | no ¬q = γcnc-conc r m Θ i c

-- Ψ₁ embeds into ⊕'s frame, and γᵇ of the composite undoes the embedding.
γ-generic : ∀ Θ R C j → revs Θ ≡ R → cmax Θ ≡ C → R ≤ j
          → γᵇ Θ (R + (C + (j ∸ R))) ≡ ` j
γ-generic Θ R C j refl refl le =
  trans (γᵇ-hi Θ (cmax Θ + (j ∸ revs Θ)))
        (trans (γcnc-hi (revs Θ) (cmax Θ) Θ (cmax Θ + (j ∸ revs Θ))
                        (m≤m+n (cmax Θ) (j ∸ revs Θ)))
               (cong `_ (trans (cong (revs Θ +_)
                                     (m+n∸m≡n (cmax Θ) (j ∸ revs Θ)))
                               (m+[n∸m]≡n le))))

γ⊕-up : ∀ Θ₁ Θ₂ j → γᵇ (Θ₁ ⊕ Θ₂) (up⊕ Θ₁ Θ₂ j) ≡ ` j
γ⊕-up Θ₁ Θ₂ j with j <? R⊕ Θ₁ Θ₂
γ⊕-up Θ₁ Θ₂ j | yes lt =
  γᵇ-lo (Θ₁ ⊕ Θ₂) j (subst (j <_) (sym (revs-⊕ Θ₁ Θ₂)) lt)
γ⊕-up Θ₁ Θ₂ j | no ge =
  γ-generic (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂) (C⊕ Θ₁ Θ₂) j
            (revs-⊕ Θ₁ Θ₂) (cmax-⊕ Θ₁ Θ₂) (≮⇒≥ ge)

sub-ren : ∀ ρ σ A → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
sub-ren ρ σ A =
  trans (cong (substᵗ σ) (sym (substᵗ-renᵗ ρ A))) (sub-sub (renᵗ ρ) σ A)

γ⊕-rep : ∀ Θ₁ Θ₂ A
  → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (renameᵗ (up⊕ Θ₁ Θ₂) A) ≡ A
γ⊕-rep Θ₁ Θ₂ A =
  trans (sub-ren (up⊕ Θ₁ Θ₂) (γᵇ (Θ₁ ⊕ Θ₂)) A)
        (trans (subst-cong (γ⊕-up Θ₁ Θ₂) A) (subst-id A))

∸-chain : ∀ {a b c} → a ≤ b → b ≤ c → (b ∸ a) + (c ∸ b) ≡ c ∸ a
∸-chain {zero} z≤n      bc       = m+[n∸m]≡n bc
∸-chain (s≤s ab) (s≤s bc)        = ∸-chain ab bc

mrg₁-lo : ∀ Θ₁ Θ₂ j → j < revs Θ₁ → mrg₁ Θ₁ Θ₂ j ≡ ` j
mrg₁-lo Θ₁ Θ₂ j l with j <? revs Θ₁
mrg₁-lo Θ₁ Θ₂ j l | yes _  = refl
mrg₁-lo Θ₁ Θ₂ j l | no  ¬p = ⊥-elim (¬p l)

mrg₁-hi : ∀ Θ₁ Θ₂ X → mrg₁ Θ₁ Θ₂ (revs Θ₁ + X) ≡ mrgΨ Θ₁ Θ₂ X
mrg₁-hi Θ₁ Θ₂ X with (revs Θ₁ + X) <? revs Θ₁
mrg₁-hi Θ₁ Θ₂ X | yes lt = ⊥-elim (m+n≮m (revs Θ₁) X lt)
mrg₁-hi Θ₁ Θ₂ X | no  _  = cong (mrgΨ Θ₁ Θ₂) (m+n∸m≡n (revs Θ₁) X)

mrgΨ-c : ∀ Θ₁ Θ₂ X → X < revs Θ₂ → X < cmax Θ₁
       → mrgΨ Θ₁ Θ₂ X ≡ renameᵗ (up⊕ Θ₁ Θ₂) (repOf X Θ₁)
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ with X <? revs Θ₂
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | yes _ with X <? cmax Θ₁
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | yes _ | yes _ = refl
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | yes _ | no ¬p = ⊥-elim (¬p l₁)
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | no ¬p = ⊥-elim (¬p l₂)

mrgΨ-r : ∀ Θ₁ Θ₂ X → X < revs Θ₂ → cmax Θ₁ ≤ X
       → mrgΨ Θ₁ Θ₂ X ≡ ` (revs Θ₁ + (X ∸ cmax Θ₁))
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ with X <? revs Θ₂
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | yes _ with X <? cmax Θ₁
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | yes _ | yes p = ⊥-elim (≤⇒≯ g₁ p)
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | yes _ | no  _ = refl
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | no ¬p = ⊥-elim (¬p l₂)

mrgΨ-d : ∀ Θ₁ Θ₂ X → revs Θ₂ ≤ X
       → mrgΨ Θ₁ Θ₂ X ≡ ` (R⊕ Θ₁ Θ₂ + (cmax Θ₂ + (X ∸ revs Θ₂)))
mrgΨ-d Θ₁ Θ₂ X g₂ with X <? revs Θ₂
mrgΨ-d Θ₁ Θ₂ X g₂ | yes p = ⊥-elim (≤⇒≯ g₂ p)
mrgΨ-d Θ₁ Θ₂ X g₂ | no  _ = refl

-- the pointwise internal-face law, at an ACCESSIBLE slot of Θ₁'s frame
⊕-γ-pt : ∀ Θ₁ Θ₂ → cmax Θ₁ ≤ revs Θ₂ → ∀ X
       → (cmax Θ₁ ≤ X) ⊎ (isConc X Θ₁ ≡ true)
       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrg₁ Θ₁ Θ₂ (revs Θ₁ + X))
         ≡ γᵇ Θ₁ (revs Θ₁ + X)
⊕-γ-pt Θ₁ Θ₂ sc X acc with X <? revs Θ₂
⊕-γ-pt Θ₁ Θ₂ sc X (inj₁ g₁) | yes l₂ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂))) (trans (mrg₁-hi Θ₁ Θ₂ X)
                                             (mrgΨ-r Θ₁ Θ₂ X l₂ g₁)))
        (trans (γᵇ-lo (Θ₁ ⊕ Θ₂) (revs Θ₁ + (X ∸ cmax Θ₁)) lt⊕)
               (sym (trans (γᵇ-hi Θ₁ X)
                           (γcnc-hi (revs Θ₁) (cmax Θ₁) Θ₁ X g₁))))
  where
    lt⊕ : revs Θ₁ + (X ∸ cmax Θ₁) < revs (Θ₁ ⊕ Θ₂)
    lt⊕ = subst (revs Θ₁ + (X ∸ cmax Θ₁) <_) (sym (revs-⊕ Θ₁ Θ₂))
                (+-monoʳ-< (revs Θ₁) (∸-monoˡ-< l₂ g₁))
⊕-γ-pt Θ₁ Θ₂ sc X (inj₂ c) | yes l₂ with cmax Θ₁ ≤? X
⊕-γ-pt Θ₁ Θ₂ sc X (inj₂ c) | yes l₂ | yes g₁ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂))) (trans (mrg₁-hi Θ₁ Θ₂ X)
                                             (mrgΨ-r Θ₁ Θ₂ X l₂ g₁)))
        (trans (γᵇ-lo (Θ₁ ⊕ Θ₂) (revs Θ₁ + (X ∸ cmax Θ₁)) lt⊕)
               (sym (trans (γᵇ-hi Θ₁ X)
                           (γcnc-hi (revs Θ₁) (cmax Θ₁) Θ₁ X g₁))))
  where
    lt⊕ : revs Θ₁ + (X ∸ cmax Θ₁) < revs (Θ₁ ⊕ Θ₂)
    lt⊕ = subst (revs Θ₁ + (X ∸ cmax Θ₁) <_) (sym (revs-⊕ Θ₁ Θ₂))
                (+-monoʳ-< (revs Θ₁) (∸-monoˡ-< l₂ g₁))
⊕-γ-pt Θ₁ Θ₂ sc X (inj₂ c) | yes l₂ | no l₁ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)))
              (trans (mrg₁-hi Θ₁ Θ₂ X) (mrgΨ-c Θ₁ Θ₂ X l₂ (≰⇒> l₁))))
        (trans (γ⊕-rep Θ₁ Θ₂ (repOf X Θ₁))
               (sym (trans (γᵇ-hi Θ₁ X)
                           (γcnc-conc (revs Θ₁) (cmax Θ₁) Θ₁ X c))))
⊕-γ-pt Θ₁ Θ₂ sc X acc | no g₂ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)))
              (trans (mrg₁-hi Θ₁ Θ₂ X) (mrgΨ-d Θ₁ Θ₂ X (≮⇒≥ g₂))))
        (trans lhs (sym rhs))
  where
    g₂' : revs Θ₂ ≤ X
    g₂' = ≮⇒≥ g₂
    g₁ : cmax Θ₁ ≤ X
    g₁ = ≤-trans sc g₂'
    cC : C⊕ Θ₁ Θ₂ ≡ cmax Θ₂
    cC = trans (cong (cmax Θ₂ +_) (m≤n⇒m∸n≡0 sc)) (+-identityʳ (cmax Θ₂))
    lhs : γᵇ (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂ + (cmax Θ₂ + (X ∸ revs Θ₂)))
        ≡ ` (revs Θ₁ + (X ∸ cmax Θ₁))
    lhs = trans (cong (λ u → γᵇ (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂ + u)) (sym shape))
                (trans (γ-generic (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂) (C⊕ Θ₁ Θ₂)
                                  (R⊕ Θ₁ Θ₂ + (X ∸ revs Θ₂))
                                  (revs-⊕ Θ₁ Θ₂) (cmax-⊕ Θ₁ Θ₂)
                                  (m≤m+n (R⊕ Θ₁ Θ₂) (X ∸ revs Θ₂)))
                       (cong `_ (trans (+-assoc (revs Θ₁) (revs Θ₂ ∸ cmax Θ₁)
                                                (X ∸ revs Θ₂))
                                       (cong (revs Θ₁ +_)
                                             (∸-chain sc g₂')))))
      where
        shape : C⊕ Θ₁ Θ₂ + ((R⊕ Θ₁ Θ₂ + (X ∸ revs Θ₂)) ∸ R⊕ Θ₁ Θ₂)
              ≡ cmax Θ₂ + (X ∸ revs Θ₂)
        shape = cong₂ _+_ cC (m+n∸m≡n (R⊕ Θ₁ Θ₂) (X ∸ revs Θ₂))
    rhs : γᵇ Θ₁ (revs Θ₁ + X) ≡ ` (revs Θ₁ + (X ∸ cmax Θ₁))
    rhs = trans (γᵇ-hi Θ₁ X) (γcnc-hi (revs Θ₁) (cmax Θ₁) Θ₁ X g₁)

-- ⊕-γ : the internal face composes (given cmax Θ₁ ≤ revs Θ₂).
⊕-γ : ∀ {Ψ₂ : TCtx} {B₁} Θ₁ Θ₂ → cmax Θ₁ ≤ revs Θ₂
    → Scoped (baseS Θ₁ Ψ₂) B₁
    → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (substᵗ (mrg₁ Θ₁ Θ₂) B₁)
      ≡ substᵗ (γᵇ Θ₁) B₁
⊕-γ {Ψ₂} {B₁} Θ₁ Θ₂ sc scB =
  trans (sub-sub (mrg₁ Θ₁ Θ₂) (γᵇ (Θ₁ ⊕ Θ₂)) B₁)
        (subst-cong-sc scB pt)
  where
    pt : ∀ j → baseS Θ₁ Ψ₂ ∋ok j
       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrg₁ Θ₁ Θ₂ j) ≡ γᵇ Θ₁ j
    pt j p with split (revs Θ₁) j
    pt j p | inj₁ lt
      rewrite mrg₁-lo Θ₁ Θ₂ j lt =
        trans (γᵇ-lo (Θ₁ ⊕ Θ₂) j
                     (subst (j <_) (sym (revs-⊕ Θ₁ Θ₂))
                            (≤-trans lt
                                     (m≤m+n (revs Θ₁) (revs Θ₂ ∸ cmax Θ₁)))))
              (sym (γᵇ-lo Θ₁ j lt))
    pt j p | inj₂ (X , refl) =
      ⊕-γ-pt Θ₁ Θ₂ sc X (baseS-acc Θ₁ X p)

-- ⊕-γ on the examples (the side condition cmax Θ₁ ≤ revs Θ₂ holds in each)
_ : substᵗ (γᵇ (Θi ⊕ Θn)) (substᵗ (mrg₁ Θi Θn) (` 0 ⇒ ` 0))
    ≡ substᵗ (γᵇ Θi) (` 0 ⇒ ` 0)
_ = ⊕-γ {Ψ₂ = abst ∷ []} Θi Θn z≤n (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))

_ : substᵗ (γᵇ (Θ1c ⊕ Θ2c)) (substᵗ (mrg₁ Θ1c Θ2c) (` 0))
    ≡ substᵗ (γᵇ Θ1c) (` 0)
_ = ⊕-γ {Ψ₂ = abst ∷ []} Θ1c Θ2c (s≤s z≤n) (sc-var hereᵒ)

_ : substᵗ (γᵇ Θ3⊕) (substᵗ (mrg₁ (Θ3₁ ⊕ Θ3₂) Θ3₃) (` 0 ⇒ ` 0))
    ≡ substᵗ (γᵇ (Θ3₁ ⊕ Θ3₂)) (` 0 ⇒ ` 0)
_ = ⊕-γ {Ψ₂ = abst ∷ []} (Θ3₁ ⊕ Θ3₂) Θ3₃ z≤n
        (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))

------------------------------------------------------------------------
-- §6.  The external face.  ρᵇ of the composite reads off as expected at
-- Θ₁'s reveals (their reps PUSHED OUT), at Θ₂'s surviving reveals, and at
-- the exterior — so ⊕-ρ holds pointwise everywhere EXCEPT at a cancelled
-- slot, where the composite has no slot left and mrg₂ substitutes Θ₁'s rep:
-- there the law needs the rep to survive the round trip Ψ₁ ↪ frame → Δ
-- (automatic for a closed rep; in general this is the same two-readings gap
-- as §2's ¬⊕-int′, and DECISIONS.md §5c's transported premise is what would
-- close it).
------------------------------------------------------------------------

ρᵇ-mapL-lo : ∀ Θ₂ Θ₁ Ξ j → j < revs Θ₁
  → ρᵇ (mapL Θ₂ Θ₁ ++ Ξ) j ≡ substᵗ (outSub Θ₂) (ρᵇ Θ₁ j)
ρᵇ-mapL-lo Θ₂ []            Ξ j       ()
ρᵇ-mapL-lo Θ₂ (rvl A ∷ Θ)   Ξ zero    lt       = refl
ρᵇ-mapL-lo Θ₂ (rvl A ∷ Θ)   Ξ (suc j) (s≤s lt) =
  ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (cnc X A ∷ Θ) Ξ j lt with X <? revs Θ₂
ρᵇ-mapL-lo Θ₂ (cnc X A ∷ Θ) Ξ j lt | yes _ = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (cnc X A ∷ Θ) Ξ j lt | no  _ = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt

ρᵇ-mapL-hi : ∀ Θ₂ Θ₁ Ξ t → ρᵇ (mapL Θ₂ Θ₁ ++ Ξ) (revs Θ₁ + t) ≡ ρᵇ Ξ t
ρᵇ-mapL-hi Θ₂ []            Ξ t = refl
ρᵇ-mapL-hi Θ₂ (rvl A ∷ Θ)   Ξ t = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (cnc X A ∷ Θ) Ξ t with X <? revs Θ₂
ρᵇ-mapL-hi Θ₂ (cnc X A ∷ Θ) Ξ t | yes _ = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (cnc X A ∷ Θ) Ξ t | no  _ = ρᵇ-mapL-hi Θ₂ Θ Ξ t

-- NOTE (first failed attempt, kept per the probe convention): the law was
-- first stated WITHOUT the side condition `(cmax Θ₁ ∸ j) ≤ revs Θ₂`, and the
-- empty case does not hold —
--   ρᵇ (mapR Θ₁ j []) t ≡ ρᵇ [] (cmax Θ₁ ∸ j + t)
--   error: [UnequalTerms] t != cmax Θ₁ ∸ j + t of type ℕ
-- (mapR can only DROP reveals that Θ₂ actually has).
ρᵇ-mapR : ∀ Θ₁ j Θ₂ t → (cmax Θ₁ ∸ j) ≤ revs Θ₂
  → ρᵇ (mapR Θ₁ j Θ₂) t ≡ ρᵇ Θ₂ ((cmax Θ₁ ∸ j) + t)
ρᵇ-mapR Θ₁ j []            t le = cong (λ n → ` (n + t)) (sym (n≤0⇒n≡0 le))
ρᵇ-mapR Θ₁ j (rvl A ∷ Θ)   t le with j <? cmax Θ₁
ρᵇ-mapR Θ₁ j (rvl A ∷ Θ)   t le | yes lt =
  trans (ρᵇ-mapR Θ₁ (suc j) Θ t le′)
        (cong (λ n → ρᵇ (rvl A ∷ Θ) (n + t)) (sym dd))
  where
    dd : cmax Θ₁ ∸ j ≡ suc (cmax Θ₁ ∸ suc j)
    dd = drop-lo (cmax Θ₁) j lt
    le′ : (cmax Θ₁ ∸ suc j) ≤ revs Θ
    le′ = ≤-pred (subst (_≤ suc (revs Θ)) dd le)
ρᵇ-mapR Θ₁ j (rvl A ∷ Θ)   t le | no ge =
  trans (body t) (cong (λ n → ρᵇ (rvl A ∷ Θ) (n + t)) (sym z))
  where
    z : cmax Θ₁ ∸ j ≡ 0
    z = m≤n⇒m∸n≡0 (≮⇒≥ ge)
    z′ : cmax Θ₁ ∸ suc j ≡ 0
    z′ = m≤n⇒m∸n≡0 (≤-trans (≮⇒≥ ge) (n≤1+n j))
    body : ∀ u → ρᵇ (rvl A ∷ mapR Θ₁ (suc j) Θ) u ≡ ρᵇ (rvl A ∷ Θ) u
    body zero    = refl
    body (suc u) =
      trans (ρᵇ-mapR Θ₁ (suc j) Θ u (subst (_≤ revs Θ) (sym z′) z≤n))
            (cong (λ n → ρᵇ Θ (n + u)) z′)
ρᵇ-mapR Θ₁ j (cnc X A ∷ Θ) t le = ρᵇ-mapR Θ₁ j Θ t le

ρ⊕-mid : ∀ Θ₁ Θ₂ t → cmax Θ₁ ≤ revs Θ₂
  → ρᵇ (Θ₁ ⊕ Θ₂) (revs Θ₁ + t) ≡ ρᵇ Θ₂ (cmax Θ₁ + t)
ρ⊕-mid Θ₁ Θ₂ t sc =
  trans (ρᵇ-mapL-hi Θ₂ Θ₁ (mapR Θ₁ 0 Θ₂) t) (ρᵇ-mapR Θ₁ 0 Θ₂ t sc)

-- the pointwise external-face law, away from the cancelled slots
⊕-ρ-pt : ∀ Θ₁ Θ₂ j → cmax Θ₁ ≤ revs Θ₂ → ¬ (j < cmax Θ₁)
       → substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrg₂ Θ₁ Θ₂ j) ≡ ρᵇ Θ₂ j
⊕-ρ-pt Θ₁ Θ₂ j sc nc with j <? revs Θ₂
⊕-ρ-pt Θ₁ Θ₂ j sc nc | yes l₂ with j <? cmax Θ₁
⊕-ρ-pt Θ₁ Θ₂ j sc nc | yes l₂ | yes p = ⊥-elim (nc p)
⊕-ρ-pt Θ₁ Θ₂ j sc nc | yes l₂ | no  _ =
  trans (ρ⊕-mid Θ₁ Θ₂ (j ∸ cmax Θ₁) sc)
        (cong (ρᵇ Θ₂) (m+[n∸m]≡n (≮⇒≥ nc)))
⊕-ρ-pt Θ₁ Θ₂ j sc nc | no g₂ = trans lhs (sym rhs)
  where
    ii : ℕ
    ii = j ∸ revs Θ₂
    lhs : ρᵇ (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂ + ii) ≡ ` ii
    lhs = subst (λ n → ρᵇ (Θ₁ ⊕ Θ₂) (n + ii) ≡ ` ii)
                (revs-⊕ Θ₁ Θ₂) (ρᵇ-hi (Θ₁ ⊕ Θ₂) ii)
    rhs : ρᵇ Θ₂ j ≡ ` ii
    rhs = trans (cong (ρᵇ Θ₂) (sym (m+[n∸m]≡n (≮⇒≥ g₂)))) (ρᵇ-hi Θ₂ ii)

------------------------------------------------------------------------
-- §7.  ⊕-ρ : the external face, in general.
--
-- Away from the cancelled slots this is ⊕-ρ-pt.  AT a cancelled slot the
-- composite has no slot left and mrg₂ puts Θ₁'s conceal rep there, so the
-- law needs that rep to survive the round trip Ψ₁ ↪ ⊕-frame → Δ.  We keep
-- that as an explicit premise and then discharge it (§7b) for GROUND reps,
-- which is every rep occurring in Example 8, the cancel pair and Example 3.
------------------------------------------------------------------------

⊕-ρ : ∀ Θ₁ Θ₂ {B₂ : Ty} → cmax Θ₁ ≤ revs Θ₂
    → (∀ j → j < cmax Θ₁
           → substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrg₂ Θ₁ Θ₂ j) ≡ ρᵇ Θ₂ j)
    → substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (substᵗ (mrg₂ Θ₁ Θ₂) B₂)
      ≡ substᵗ (ρᵇ Θ₂) B₂
⊕-ρ Θ₁ Θ₂ {B₂} sc cn =
  trans (sub-sub (mrg₂ Θ₁ Θ₂) (ρᵇ (Θ₁ ⊕ Θ₂)) B₂) (subst-cong pt B₂)
  where
    pt : ∀ j → substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrg₂ Θ₁ Θ₂ j) ≡ ρᵇ Θ₂ j
    pt j with j <? cmax Θ₁
    pt j | yes lt = cn j lt
    pt j | no  ge = ⊕-ρ-pt Θ₁ Θ₂ j sc ge

------------------------------------------------------------------------
-- §7b.  Discharging the cancel premise for ground reps.
------------------------------------------------------------------------

data Ground : Ty → Set where
  gr-ℕ : Ground `ℕ
  gr-𝔹 : Ground `𝔹
  gr-⇒ : ∀ {A B} → Ground A → Ground B → Ground (A ⇒ B)

ground-ren : ∀ {A} ρ → Ground A → renameᵗ ρ A ≡ A
ground-ren ρ gr-ℕ         = refl
ground-ren ρ gr-𝔹         = refl
ground-ren ρ (gr-⇒ gA gB) = cong₂ _⇒_ (ground-ren ρ gA) (ground-ren ρ gB)

ground-sub : ∀ {A} σ → Ground A → substᵗ σ A ≡ A
ground-sub σ gr-ℕ         = refl
ground-sub σ gr-𝔹         = refl
ground-sub σ (gr-⇒ gA gB) = cong₂ _⇒_ (ground-sub σ gA) (ground-sub σ gB)

mrg₂-c : ∀ Θ₁ Θ₂ j → j < revs Θ₂ → j < cmax Θ₁
       → mrg₂ Θ₁ Θ₂ j ≡ renameᵗ (up⊕ Θ₁ Θ₂) (repOf j Θ₁)
mrg₂-c Θ₁ Θ₂ j l₂ l₁ with j <? revs Θ₂
mrg₂-c Θ₁ Θ₂ j l₂ l₁ | yes _ with j <? cmax Θ₁
mrg₂-c Θ₁ Θ₂ j l₂ l₁ | yes _ | yes _ = refl
mrg₂-c Θ₁ Θ₂ j l₂ l₁ | yes _ | no ¬p = ⊥-elim (¬p l₁)
mrg₂-c Θ₁ Θ₂ j l₂ l₁ | no ¬p = ⊥-elim (¬p l₂)

-- Θ₁ has no BLOCKED slot: every slot it drops, it conceals.  (A blocked slot
-- of Θ₁ that is one of Θ₂'s reveals is the future `↑Y:⋆` of DECISIONS.md —
-- the composite has no slot for it and mrg₂ would read repOf's `ℕ dummy.)
NoBlk : BCtx → Set
NoBlk Θ = ∀ j → j < cmax Θ → isConc j Θ ≡ true

cancel-rt : ∀ {Δ Ψ} Θ₁ Θ₂ → intOf′ Δ Θ₂ ∣ Ψ ⊢ᵇ′ Θ₁
          → cmax Θ₁ ≤ revs Θ₂ → NoBlk Θ₁
          → (∀ j → j < cmax Θ₁ → Ground (repOf j Θ₁))
          → ∀ j → j < cmax Θ₁
          → substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrg₂ Θ₁ Θ₂ j) ≡ ρᵇ Θ₂ j
cancel-rt {Δ} Θ₁ Θ₂ b sc nb gr j lt =
  trans (cong (substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)))
              (trans (mrg₂-c Θ₁ Θ₂ j (≤-trans lt sc) lt)
                     (ground-ren (up⊕ Θ₁ Θ₂) (gr j lt))))
        (trans (ground-sub (ρᵇ (Θ₁ ⊕ Θ₂)) (gr j lt))
               (sym (cancel-agree Θ₂ Δ j (repOf j Θ₁) (≤-trans lt sc)
                                  (bwf-repOf Θ₁ b j (nb j lt)))))

-- the cancel pair, through the GENERAL lemmas (not by refl)
nb-c : NoBlk Θ1c
nb-c zero    (s≤s z≤n) = refl
nb-c (suc j) (s≤s ())

gr-c : ∀ j → j < cmax Θ1c → Ground (repOf j Θ1c)
gr-c zero    (s≤s z≤n) = gr-ℕ
gr-c (suc j) (s≤s ())

rt-c : ∀ j → j < cmax Θ1c
     → substᵗ (ρᵇ (Θ1c ⊕ Θ2c)) (mrg₂ Θ1c Θ2c j) ≡ ρᵇ Θ2c j
rt-c = cancel-rt {Δ = []} {Ψ = []} Θ1c Θ2c
         (bwf↓′ here wf-ℕ bwf[]′) (s≤s z≤n) nb-c gr-c

_ : substᵗ (ρᵇ (Θ1c ⊕ Θ2c)) (substᵗ (mrg₂ Θ1c Θ2c) (` 0))
    ≡ substᵗ (ρᵇ Θ2c) (` 0)
_ = ⊕-ρ Θ1c Θ2c {B₂ = ` 0} (s≤s z≤n) rt-c

------------------------------------------------------------------------
-- §8.  The Merge rule, and what B₂′ has to be.
--
--   Merge : Value V
--     → (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫  -→  V ⟪ Θ₁ ⊕ Θ₂ , B₂′ ⟫
--
-- There are exactly two candidates for B₂′, and they are the two transports
-- of §3:
--
--   B₂′ = substᵗ (mrg₁ Θ₁ Θ₂) B₁      -- the INTERNAL face is then free (⊕-γ)
--   B₂′ = substᵗ (mrg₂ Θ₁ Θ₂) B₂      -- the EXTERNAL face is then free (⊕-ρ)
--
-- On the cancel pair (§4b) the two agree and both give the expected `ℕ, i.e.
-- "B₂ with the cancelled reveal variable replaced by its rep".  In general
-- they do NOT agree — not even under the middle-type equation (¬Aligned-o
-- below) — and §4c shows a redex for which NEITHER (indeed no boundary type
-- whatsoever) works.  So Merge is sound exactly on the redexes satisfying
------------------------------------------------------------------------

Aligned : BCtx → BCtx → Ty → Ty → Set
Aligned Θ₁ Θ₂ B₁ B₂ =
  substᵗ (mrg₁ Θ₁ Θ₂) B₁ ≡ substᵗ (mrg₂ Θ₁ Θ₂) B₂

-- … or, weaker and all that Merge actually needs, on those satisfying
MergeOK : BCtx → BCtx → Ty → Ty → Set
MergeOK Θ₁ Θ₂ B₁ B₂ =
  substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (substᵗ (mrg₁ Θ₁ Θ₂) B₁) ≡ substᵗ (ρᵇ Θ₂) B₂

aligned⇒ok : ∀ Θ₁ Θ₂ {B₁ B₂} → cmax Θ₁ ≤ revs Θ₂
  → (∀ j → j < cmax Θ₁
         → substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrg₂ Θ₁ Θ₂ j) ≡ ρᵇ Θ₂ j)
  → Aligned Θ₁ Θ₂ B₁ B₂ → MergeOK Θ₁ Θ₂ B₁ B₂
aligned⇒ok Θ₁ Θ₂ {B₁} {B₂} sc cn al =
  trans (cong (substᵗ (ρᵇ (Θ₁ ⊕ Θ₂))) al) (⊕-ρ Θ₁ Θ₂ {B₂} sc cn)

-- THE PRESERVATION STATEMENT for Merge, with B₂′ = substᵗ (mrg₁ Θ₁ Θ₂) B₁:
-- both faces of the composite are the faces the redex had.
merge-faces : ∀ {Ψ₂ : TCtx} {B₁ B₂} Θ₁ Θ₂ → cmax Θ₁ ≤ revs Θ₂
  → Scoped (baseS Θ₁ Ψ₂) B₁ → MergeOK Θ₁ Θ₂ B₁ B₂
  → (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (substᵗ (mrg₁ Θ₁ Θ₂) B₁) ≡ substᵗ (γᵇ Θ₁) B₁)
  × (substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (substᵗ (mrg₁ Θ₁ Θ₂) B₁) ≡ substᵗ (ρᵇ Θ₂) B₂)
merge-faces {Ψ₂} {B₁} Θ₁ Θ₂ sc scB mok = ⊕-γ {Ψ₂} {B₁} Θ₁ Θ₂ sc scB , mok

-- the middle-type equation does NOT lift to Aligned: §4c's redex satisfies
-- it, yet the two transports differ (and by no-merge nothing repairs it).
_ : substᵗ (ρᵇ Θ1o) (` 0 ⇒ ` 0) ≡ substᵗ (γᵇ Θ2o) (` 0)
_ = refl

_ : substᵗ (mrg₁ Θ1o Θ2o) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)
_ = refl

-- (Θ2o has no reveal, so mrg₂ just re-indexes X past Θ1o's reveal)
_ : substᵗ (mrg₂ Θ1o Θ2o) (` 0) ≡ ` 1
_ = refl

¬Aligned-o : ¬ (Aligned Θ1o Θ2o (` 0 ⇒ ` 0) (` 0))
¬Aligned-o ()

¬MergeOK-o : ¬ (MergeOK Θ1o Θ2o (` 0 ⇒ ` 0) (` 0))
¬MergeOK-o ()

-- MergeOK on the three positive examples (T5, the cancel pair, the tower)
okT5 : MergeOK Θi Θn (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
okT5 = refl

ok-c : MergeOK Θ1c Θ2c (` 0) (` 0)
ok-c = refl

ok-3a : MergeOK Θ3₁ Θ3₂ (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
ok-3a = refl

ok-3b : MergeOK (Θ3₁ ⊕ Θ3₂) Θ3₃ (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
ok-3b = refl

-- T5 shows Aligned is strictly stronger than MergeOK
¬Aligned-T5 : ¬ (Aligned Θi Θn (` 0 ⇒ ` 0) (` 0 ⇒ ` 0))
¬Aligned-T5 ()

------------------------------------------------------------------------
-- §9.  bwf and scope for the composite.
--
-- ⊕-bwf does NOT hold for GroundedProbe's (untransported) bwf↓′: the
-- composite must read Θ₂'s conceal reps in Ψ₁ (mapR pushes them in through
-- inSub Θ₁), while bwf↓′ compares them SYNTACTICALLY with the knowledge Δ
-- holds.  Counterexample: Δ = [X:=P , P] , Θ₂ = ↓X:=P , Θ₁ = ↑W:=𝔹.
-- Under DECISIONS.md §5c's TRANSPORTED premise (grounded Θ X A A₀, i.e.
-- A = (↑A₀)[γΘ]) the composite's rep is by construction the γᵇ-image of the
-- same A₀ through the whole composite, and this mismatch disappears — so
-- ⊕-bwf is a reason to land the transported premise, not a counterexample
-- to Merge.
------------------------------------------------------------------------

Δbw : TCtx
Δbw = rvld (` 0) ∷ abst ∷ []

Θ2bw Θ1bw : BCtx
Θ2bw = cnc 0 (` 0) ∷ []
Θ1bw = rvl `𝔹 ∷ []

_ : intOf′ Δbw Θ2bw ≡ abst ∷ []
_ = refl

_ : Θ1bw ⊕ Θ2bw ≡ rvl `𝔹 ∷ cnc 0 (` 1) ∷ []
_ = refl

⊢Θ2bw : Δbw ∣ intOf′ Δbw Θ2bw ⊢ᵇ′ Θ2bw
⊢Θ2bw = bwf↓′ here (wf-var here-abst) bwf[]′

⊢Θ1bw : intOf′ Δbw Θ2bw ∣ intOf′ (intOf′ Δbw Θ2bw) Θ1bw ⊢ᵇ′ Θ1bw
⊢Θ1bw = bwf↑′ wf-𝔹 bwf[]′

¬⊕-bwf : ¬ (Δbw ∣ intOf′ (intOf′ Δbw Θ2bw) Θ1bw ⊢ᵇ′ (Θ1bw ⊕ Θ2bw))
¬⊕-bwf (bwf↑′ _ (bwf↓′ () _ _))

-- … whereas the composite IS well formed on every example whose reps are
-- ground (the derivations are the ones already given: ⊢mergedT5,
-- ⊢contractum-c, ⊢merged3), e.g.
⊢Θ⊕8 : Δ8′ ∣ intOf′ Δ8′ Θ⊕8 ⊢ᵇ′ Θ⊕8
⊢Θ⊕8 = bwf↑′ (wf-var here-abst)
        (bwf↑′ (wf-var here-abst) (bwf↓′ (skip-abst here) wf-ℕ bwf[]′))

-- Scope: on the examples, B₂′ is Scoped over the composite's stack.
_ : baseS Θ⊕8 Δ8 ≡ ok ∷ ok ∷ blk ∷ ok ∷ []
_ = refl

scB⊕8 : Scoped (baseS Θ⊕8 Δ8) (substᵗ (mrg₁ Θi Θn) (` 0 ⇒ ` 0))
scB⊕8 = sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)

scB⊕c : Scoped (baseS (Θ1c ⊕ Θ2c) []) (substᵗ (mrg₁ Θ1c Θ2c) (` 0))
scB⊕c = sc-ℕ

scB⊕3 : Scoped (baseS Θ3⊕ Δ3) (substᵗ (mrg₁ (Θ3₁ ⊕ Θ3₂) Θ3₃) (` 0 ⇒ ` 0))
scB⊕3 = sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)

------------------------------------------------------------------------
-- §10.  Depth-1 values (Decision 3a, Zdancewic Fig. 11): a wrapper's body
-- is a PRIMVAL (constant, λ or Λ), never another wrapper.
------------------------------------------------------------------------

data GVal₁ : Term → Set
data Val₁  : Term → Set
data PVal  : Term → Set

data GVal₁ where
  G₁-ƛ : GVal₁ (ƛ A ∙ M)
  G₁-Λ : Val₁ M → GVal₁ (Λ M)

data PVal where
  P-$ : ∀ {n} → PVal ($ n)
  P-G : GVal₁ M → PVal M

data Val₁ where
  V₁-P  : PVal M → Val₁ M
  V₁-⟪⟫ : PVal M → Val₁ (M ⟪ Θ , B₀ ⟫)

-- the merged forms of the three examples are depth-1 values …
_ : Val₁ mergedT5
_ = V₁-⟪⟫ (P-G G₁-ƛ)

_ : Val₁ (($ 7) ⟪ [] , `ℕ ⟫)
_ = V₁-⟪⟫ P-$

_ : Val₁ ((ƛ ` 0 ∙ ` 0) ⟪ Θ3⊕ , ` 0 ⇒ ` 0 ⟫)
_ = V₁-⟪⟫ (P-G G₁-ƛ)

-- … and §4c's redex is NOT (its body is a wrapper), yet no Merge applies:
-- with depth-1 values, `redexo` is a CLOSED WELL-TYPED STUCK TERM.  This is
-- the price of Decision 3a as stated; ⊢redexo / no-merge above are the proof.
¬Val₁-redexo : ¬ (Val₁ redexo)
¬Val₁-redexo (V₁-P (P-G ()))
¬Val₁-redexo (V₁-⟪⟫ (P-G ()))

-- Where the depth-2 towers come from: TyWrap's contractum wraps a type
-- application, and TyBeta turns that into a wrapper (Example 8, T4 -→ T5);
-- Wrap's contractum wraps an application, and Beta can turn that into a
-- wrapper too.  Merge is what returns them to depth 1.
_ : Value ((ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫)
_ = V-⟪⟫ (V-G G-ƛ)

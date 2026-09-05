module strong.notes.probes.ConvBoundaryProbe where

-- THE CONVERSION-BOUNDARY REDESIGN PROBE — part 3: the RULES and the CORPUS.
--
-- §1  ACTIVE/INERT, classified by the CONVERSION constructor (Jeremy's list).
-- §2  the rules: TyBeta, Beta, Peel, TyPeel, Cancel, Drop$, ξ.
-- §3  Q3 THE SOUNDNESS GATE — `seal-cites-a-live-owner`, and the ⊢3n-adv
--     analogue refuted; `ali` claims nothing.
-- §4  Q2 THE THREE BREAKS (c10/c11 §9n, n1b, n4) and E★′, in the mini-core:
--     all four type, all four CROSS, and the crossing value's licence
--     SURVIVES the crossing — the contractum is typed, where the current
--     design has `¬⊢contractum`, `n1b-¬contractum`, `n4-¬contractum`.
-- §5  Q4 the safe corpus: the cancel pair and the §9m ≡/≈ gap.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.notes.probes.ConvBoundaryCore
open import strong.notes.probes.ConvBoundaryTerms

------------------------------------------------------------------------
-- §1  ACTIVE / INERT — a one-level match on the CONVERSION constructor
------------------------------------------------------------------------

-- Inert  = { s ↦ t , ∀ s , seal α , id-at-a-variable }
-- Active = { unseal α , id-at-base }
-- No face type is inspected and no slot arithmetic occurs: the current
-- core's `I-var : revs Θ ≤ X → …` has no analogue.
data Inert : Conv → Set where
  I-idv  : ∀ {X}   → Inert (id (` X))
  I-seal : ∀ {X}   → Inert (seal X)
  I-fun  : ∀ {s t} → Inert (s ↦ t)
  I-all  : ∀ {s}   → Inert (`∀ s)

data Active : Conv → Set where
  A-idb    : ∀ {A} → Base A → Active (id A)
  A-unseal : ∀ {X} → Active (unseal X)

-- (i) ActiveOrInert is CONSTRUCTOR TOTALITY.
-- totality over TYPED conversions: the payload restriction on `id` makes
-- classification a match on the TYPING derivation (Jeremy's ruling — the
-- untypeable compound identities are never classified at all)
act-or-inert : ∀ {Δ c A B p} → Δ ⊢ c ∶ A ⇝ B ∙ p → Active c ⊎ Inert c
act-or-inert (conv-id b)       = inj₁ (A-idb b)
act-or-inert (conv-idv tv)     = inj₂ I-idv
act-or-inert (conv-seal o)     = inj₂ I-seal
act-or-inert (conv-unseal o)   = inj₁ A-unseal
act-or-inert (conv-fun s t)    = inj₂ I-fun
act-or-inert (conv-all s)      = inj₂ I-all

act-not-inert : ∀ {c} → Active c → Inert c → ⊥
act-not-inert (A-idb ()) I-idv
act-not-inert A-unseal ()

data Value : Term → Set where
  V-$  : ∀ {n} → Value ($ n)
  V-ƛ  : ∀ {A N} → Value (ƛ A ∙ N)
  V-Λ  : ∀ {N} → Value (Λ N)
  V-⟪⟫ : ∀ {M Θ c} → Value M → Inert c → Value (M ⟪ Θ , c ⟫)

------------------------------------------------------------------------
-- §2  The rules
------------------------------------------------------------------------

-- Term substitution (ordinary; boundaries are term-closed, so a wrapper is
-- never descended into).
extᵐ : (ℕ → Term) → (ℕ → Term)
extᵐ σ zero    = ` zero
extᵐ σ (suc x) = shiftᵐ (σ x)
  where
  shiftᵐ : Term → Term
  shiftᵐ (` x)          = ` suc x
  shiftᵐ ($ n)          = $ n
  shiftᵐ (ƛ A ∙ N)      = ƛ A ∙ shiftᵐ N
  shiftᵐ (L · M)        = shiftᵐ L · shiftᵐ M
  shiftᵐ (Λ N)          = Λ (shiftᵐ N)
  shiftᵐ (L ·[ B , A ]) = shiftᵐ L ·[ B , A ]
  shiftᵐ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

substᵐ : (ℕ → Term) → Term → Term
substᵐ σ (` x)          = σ x
substᵐ σ ($ n)          = $ n
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᵐ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ σ N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵐ (λ { zero → W ; (suc x) → ` x }) N

-- The CANONICAL conversion at a slot: unseal every occurrence of X (read in
-- the ↑ polarity) / seal it back (read in the ↓ polarity).  These are what
-- the reveal rules mint; they are DERIVED from the face type, not stored
-- knowledge, and they carry only the NAME X.
mutual
  unsealAt : ℕ → Ty → Conv
  unsealAt X (` Y) with X ≟ℕ Y
  ... | yes _ = unseal X
  ... | no  _ = id (` Y)
  unsealAt X `ℕ      = id `ℕ
  unsealAt X `𝔹      = id `𝔹
  unsealAt X (A ⇒ B) = sealAt X A ↦ unsealAt X B
  unsealAt X (`∀ A)  = `∀ (unsealAt (suc X) A)

  sealAt : ℕ → Ty → Conv
  sealAt X (` Y) with X ≟ℕ Y
  ... | yes _ = seal X
  ... | no  _ = id (` Y)
  sealAt X `ℕ      = id `ℕ
  sealAt X `𝔹      = id `𝔹
  sealAt X (A ⇒ B) = unsealAt X A ↦ sealAt X B
  sealAt X (`∀ A)  = `∀ (sealAt (suc X) A)

-- THE DUAL, in full.  It mints ONLY name-carrying entries: a `cnc` for each
-- of the crossed boundary's owners (the argument may not see them) and an
-- `ali` for each of its conceals (the argument came from outside, where they
-- were nameable).  Nothing is copied, nothing is guarded, nothing is
-- demoted; `entᴳ` has no analogue.
maskOwns : ℕ → BCtx
maskOwns zero    = []
maskOwns (suc k) = cnc k ∷ maskOwns k

dualS : ℕ → BCtx → BCtx
dualS n []            = []
dualS n (own A ∷ Θ)   = dualS n Θ
dualS n (ali X ∷ Θ)   = cnc (n + X) ∷ dualS n Θ
dualS n (cnc X ∷ Θ)   = ali (n + X) ∷ dualS n Θ

dual : BCtx → BCtx
dual Θ = maskOwns (nrev Θ) ++ dualS (nrev Θ) Θ

-- The weakening a crossing argument undergoes: the boundary's frame grew by
-- `nrev Θ` binders, so the argument's ANNOTATIONS shift.  This is ordinary
-- de Bruijn weakening (`⊢rename` at `wkN`), not a re-spelling.
wkN : ℕ → Renameᵗ
wkN n X = n + X

reps→own : List Ty → BCtx
reps→own []       = []
reps→own (A ∷ As) = own A ∷ reps→own As

wkᴹ : ℕ → Term → Term
wkᴹ n = renᴹ (wkN n)

infix 2 _⊢_-→_
data _⊢_-→_ : Ctxᵗ → Term → Term → Set where

  -- a boundary is BORN: the ∀-elimination mints THE OWNER of the event.
  TyBeta : ∀ {Δ B A N}
    → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ own A ∷ [] , unsealAt 0 B ⟫

  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- PEEL — the crossing.  The application is pushed in one layer and the
  -- argument acquires the DUAL.  `s`/`t` are literally ↦'s components:
  -- the crossing argument's conversion is RE-BASED by the repointing.
  Peel : ∀ {Δ V W Θ s t} → Value V → Value W
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (wkᴹ (nrev Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫

  -- TYPEEL — the ∀-face analogue; the new owner is prepended (direct
  -- combine), and the elimination instantiates at the new owner's own name.
  TyPeel : ∀ {Δ V Θ s B A} → Value V
    → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ (wkᴹ 1 V ·[ B , ` 0 ]) ⟪ own A ∷ renᴮ suc Θ , s ⟫

  -- CANCEL — a conceal directly under the owner it names.  The face match
  -- is DEFINITIONAL: `seal X` and `unseal X` cite the SAME entry, so there is
  -- no second spelling to disagree with the first.  The residue masks the
  -- boundary's own owners, which is exactly "the composite is empty".
  Cancel : ∀ {Δ V Θ₁ Θ₂ X B} → Value V
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal X ⟫
        -→ V ⟪ reps→own (reps Θ₂) ++ maskOwns (nrev Θ₂) , idc B ⟫

  -- DROP$ — a base-faced boundary over a numeral (`⊢$` types it anywhere).
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n

  ξ-·-l : ∀ {Δ L L′ M} → Δ ⊢ L -→ L′ → Δ ⊢ L · M -→ L′ · M
  ξ-·-r : ∀ {Δ V M M′} → Value V → Δ ⊢ M -→ M′ → Δ ⊢ V · M -→ V · M′
  ξ-·[] : ∀ {Δ L L′ B A} → Δ ⊢ L -→ L′ → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]
  ξ-Λ   : ∀ {Δ N N′} → (abst ∷ Δ) ⊢ N -→ N′ → Δ ⊢ Λ N -→ Λ N′
  ξ-⟪⟫  : ∀ {Δ M M′ Θ c} → intC Θ Δ ⊢ M -→ M′
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ Θ , c ⟫

------------------------------------------------------------------------
-- §3  Q3 — THE SOUNDNESS GATE
------------------------------------------------------------------------

-- A CONCEAL MUST CITE A LIVE OWNER.  This is the whole gate, and it is a
-- one-line inversion: `conv-seal` has no other premise.  Under the old design the
-- same fact needed `bwf↓`+`Reversal≈` OR `bwf↓x`+`starOnly`+`SkelEq`, and
-- the adversary passed ≡, ≈Δ̄ and SkelEq (only `starOnly` refused it).
seal-cites-owner : ∀ {Δ X A B p c}
  → Δ ⊢ c ∶ A ⇝ B ∙ p → c ≡ seal X → Δ ∋ X := A
seal-cites-owner (conv-seal d) refl = d

-- `ali` claims nothing: it is a NAME with no rep, so it cannot assert
-- knowledge.  Formally: the boundary skeleton carries no type at an alias,
-- and `Bwf`'s alias premise is `Δ ∋e X , E` — pure existence.
ali-claims-nothing : ∀ {Δ X E Θ} → Δ ∋e X , E → Bwf Δ Θ → Bwf Δ (ali X ∷ Θ)
ali-claims-nothing = bw-a

-- THE ADVERSARY (⊢3n-adv / `adv`).  Its harm was a conceal ASSERTING false
-- knowledge: at a spine where slot 0 is ABSTRACT (Λ-bound — no owner), it
-- exported `7 : ℕ` at the abstract type.  In the mini-core the boundary is
-- unmintable, because `seal 0` demands `Δ ∋ 0 := `ℕ` and an `abst` slot has
-- no rep to cite.  Unmasking cannot manufacture one either (§ali above).
Δadv : Ctxᵗ
Δadv = abst ∷ []

-- there is NO knowledge at the abstract slot …
¬know-adv : ∀ {A} → Δadv ∋ 0 := A → ⊥
¬know-adv ()

-- … hence no seal at it, in either polarity …
¬seal-adv : ∀ {A B p} → Δadv ⊢ seal 0 ∶ A ⇝ B ∙ p → ⊥
¬seal-adv (conv-seal d) = ¬know-adv d

-- … hence the adversary's boundary has no face at all, and the term
-- `7 ⟪ cnc 0 ∷ [] , seal 0 ⟫ : ` 0` is UNTYPABLE.
¬⊢adv : ∀ {Γ} → Δadv ∣ Γ ⊢ ($ 7) ⟪ cnc 0 ∷ [] , seal 0 ⟫ ⦂ ` 0 → ⊥
¬⊢adv (env bw ⊢M ⊢c wE) = ¬seal-adv ⊢c

-- `bad`: an inner conceal at rep ℕ under an owner whose rep is ∀Z.Z→Z.
-- The two spellings cannot disagree, because there is only ONE: `seal 0`
-- reads the owner, so the interior face IS the owner's rep.  The
-- ill-typed configuration is not expressible.
∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

Δbad : Ctxᵗ
Δbad = own ∀ZZ ∷ []

-- the ONLY interior face a `seal 0` can have here is the owner's rep …
seal-bad-face : ∀ {A B p} → Δbad ⊢ seal 0 ∶ A ⇝ B ∙ p → A ≡ ⇑ᵗ ∀ZZ
seal-bad-face (conv-seal ez) = refl

-- … so `7 : ℕ` can never acquire the abstract type there.
¬⊢bad : ∀ {Γ} → Δbad ∣ Γ ⊢ ($ 7) ⟪ cnc 0 ∷ [] , seal 0 ⟫ ⦂ ` 0 → ⊥
¬⊢bad (env bw ⊢$ ⊢c wE) with seal-bad-face ⊢c
... | ()

------------------------------------------------------------------------
-- §4  Q2 — THE THREE BREAKS, and the shape-IV survivor
------------------------------------------------------------------------

-- ── c10 / c11 (the §9n preservation break) ──────────────────────────────
--
--   old:  Δd = rvld (` 0) ∷ abst ∷ rvld `ℕ ∷ []      W:=X , X , V:=ℕ
--         Θ2 = rvl (` 0) ∷ cnc 2 `ℕ ∷ []            ↑?:=W , ↓V:=ℕ
--         Wtm = (ƛ ` 0 ∙ ` 0) ⟪ cnc 0 (` 0) ∷ [] , ` 0 ⇒ ` 0 ⟫
--   The reveal's rep NAMES the chained slot W, whose own knowledge is the
--   Λ-bound X; the old dual demoted W and `Wtm`'s licence died.

Δd : Ctxᵗ                       -- W:=X , X abstract , V:=ℕ
Δd = own (` 0) ∷ abst ∷ own `ℕ ∷ []

-- W's rep, read on Δd, is the Λ-bound X — the chained spelling that broke.
_ : Δd ∋ 0 := ` 1
_ = ez

Θ2 : BCtx                       -- own(W) , conceal V
Θ2 = own (` 0) ∷ cnc 2 ∷ []

-- ONE frame change: the owner is pushed on, V is MASKED in place (the entry
-- `own `ℕ` survives as `blk (own `ℕ)`), nothing is dropped.
_ : intC Θ2 Δd ≡ own (` 0) ∷ own (` 0) ∷ abst ∷ blk (own `ℕ) ∷ []
_ = refl

-- the FACE spine keeps every slot live, so a conceal's licence resolves.
_ : fceC Θ2 Δd ≡ own (` 0) ∷ own (` 0) ∷ abst ∷ own `ℕ ∷ []
_ = refl

cΘ2 : Conv                      -- (X⇒X)⇒ℕ  ⇝  (W⇒W)⇒ℕ
cΘ2 = (unseal 0 ↦ seal 0) ↦ id `ℕ

Vd : Term
Vd = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)

⊢cΘ2 : fceC Θ2 Δd ⊢ cΘ2 ∶ ((` 0 ⇒ ` 0) ⇒ `ℕ) ⇝ ((` 1 ⇒ ` 1) ⇒ `ℕ) ∙ ↑ˢ
⊢cΘ2 = conv-fun (conv-fun (conv-unseal ez) (conv-seal ez)) (conv-id base-ℕ)

⊢Fnd : Δd ∣ [] ⊢ Vd ⟪ Θ2 , cΘ2 ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fnd = env (bw-o (wf-var (_ , ez , vis-o)) (bw-c (_ , es (es ez) , vis-o) bw[]))
           (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                     (wf-var (_ , ez , vis-o))) ⊢$)
           ⊢cΘ2
           (wf-⇒ (wf-⇒ (wf-var (_ , ez , vis-o))
                       (wf-var (_ , ez , vis-o))) wf-ℕ)

-- THE CROSSING VALUE.  Its own boundary masks W and seals at it: the licence
-- `seal 0` cites the owner at slot 0 of Δd, whose rep is X = ` 1.
Θw : BCtx
Θw = cnc 0 ∷ []

Wd : Term
Wd = (ƛ (` 1) ∙ (` 0)) ⟪ Θw , unseal 0 ↦ seal 0 ⟫

_ : intC Θw Δd ≡ blk (own (` 0)) ∷ abst ∷ own `ℕ ∷ []
_ = refl

⊢Wd : Δd ∣ [] ⊢ Wd ⦂ (` 0 ⇒ ` 0)
⊢Wd = env (bw-c (_ , ez , vis-o) bw[])
          (⊢ƛ (wf-var (_ , es ez , vis-a)) (⊢` here))
          (conv-fun (conv-unseal ez) (conv-seal ez))
          (wf-⇒ (wf-var (_ , ez , vis-o))
                (wf-var (_ , ez , vis-o)))

Wd-value : Value Wd
Wd-value = V-⟪⟫ V-ƛ I-fun

⊢Redexd : Δd ∣ [] ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd ⦂ `ℕ
⊢Redexd = ⊢· ⊢Fnd ⊢Wd

-- THE PEEL STEP.
peel-d : Δd ⊢ (Vd ⟪ Θ2 , cΘ2 ⟫) · Wd
           -→ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫)) ⟪ Θ2 , id `ℕ ⟫
peel-d = Peel V-ƛ Wd-value

-- THE DUAL is two names and nothing else: mask the owner, re-expose V.
_ : dual Θ2 ≡ cnc 0 ∷ ali 3 ∷ []
_ = refl

-- THE REPOINTING.  The dual's interior is Δd with ONE masked slot in front:
-- every entry of Δd is still there, in the same order, with the same rep.
-- W's entry — the one the old design demoted to `abst` — is untouched.
_ : intC (dual Θ2) (intC Θ2 Δd) ≡ blk (own (` 0)) ∷ Δd
_ = refl

-- and the dual's FACE spine is IDENTICAL to the crossed boundary's, so `s`
-- transplants verbatim (no `swapᵇ`, no re-derivation).
_ : fceC (dual Θ2) (intC Θ2 Δd) ≡ fceC Θ2 Δd
_ = refl

-- THE CONTRACTUM IS TYPED.  Compare `DI.¬⊢contractum` / `¬⊢qP₈`.
⊢contractumd :
  Δd ∣ [] ⊢ (Vd · (wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫)) ⟪ Θ2 , id `ℕ ⟫ ⦂ `ℕ
⊢contractumd =
  env {p = ↑ˢ}
      (bw-o (wf-var (_ , ez , vis-o))
            (bw-c (_ , es (es ez) , vis-o) bw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                    (wf-var (_ , ez , vis-o))) ⊢$)
          ⊢Wd-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  -- the crossing argument, re-typed INSIDE, by ⊢rename at the weakening.
  ⊢Wd-in : (blk (own (` 0)) ∷ Δd) ∣ [] ⊢ wkᴹ 1 Wd ⦂ (` 1 ⇒ ` 1)
  ⊢Wd-in = ⊢rename (mkRen (λ d → es d)) (λ eq → suc-inj eq) ⊢Wd
    where
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
  ⊢Wd-crossed : intC Θ2 Δd ∣ [] ⊢ wkᴹ 1 Wd ⟪ dual Θ2 , unseal 0 ↦ seal 0 ⟫
                                ⦂ (` 0 ⇒ ` 0)
  ⊢Wd-crossed =
    env (bw-c (_ , ez , vis-o)
              (bw-a (es (es (es ez))) bw[]))
        ⊢Wd-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , vis-o))
              (wf-var (_ , ez , vis-o)))

-- ── n1b (THE BREAK, MINIMIZED) ──────────────────────────────────────────
--   old: Δ1b = rvld (` 0) ∷ abst ∷ [] ;  Θ1b = rvl (` 0) ∷ cnc⋆ 1 ∷ []
-- The chain X:=Y over a Λ-bound Y, with the ambient's third slot and the
-- rep-carrying conceal both removed.

Δ1b : Ctxᵗ
Δ1b = own (` 0) ∷ abst ∷ []

Θ1b : BCtx
Θ1b = own (` 0) ∷ cnc 1 ∷ []

_ : intC Θ1b Δ1b ≡ own (` 0) ∷ own (` 0) ∷ blk abst ∷ []
_ = refl

W1b : Term
W1b = (ƛ (` 1) ∙ (` 0)) ⟪ cnc 0 ∷ [] , unseal 0 ↦ seal 0 ⟫

⊢W1b : Δ1b ∣ [] ⊢ W1b ⦂ (` 0 ⇒ ` 0)
⊢W1b = env (bw-c (_ , ez , vis-o) bw[])
           (⊢ƛ (wf-var (_ , es ez , vis-a)) (⊢` here))
           (conv-fun (conv-unseal ez) (conv-seal ez))
           (wf-⇒ (wf-var (_ , ez , vis-o))
                 (wf-var (_ , ez , vis-o)))

_ : dual Θ1b ≡ cnc 0 ∷ ali 2 ∷ []
_ = refl

-- the repointing again: nothing dropped, nothing demoted.
_ : intC (dual Θ1b) (intC Θ1b Δ1b) ≡ blk (own (` 0)) ∷ Δ1b
_ = refl

-- the crossing value's licence, re-based one slot out — STILL A LIVE OWNER.
_ : (blk (own (` 0)) ∷ Δ1b) ∋ 1 := ` 2
_ = es ez

-- THE MINIMIZED BREAK, TYPED THROUGH ITS CROSSING.

cΘ1b : Conv
cΘ1b = (unseal 0 ↦ seal 0) ↦ id `ℕ

V1b : Term
V1b = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)

⊢Fn1b : Δ1b ∣ [] ⊢ V1b ⟪ Θ1b , cΘ1b ⟫ ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢Fn1b = env (bw-o (wf-var (_ , ez , vis-o)) (bw-c (_ , es ez , vis-a) bw[]))
            (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                      (wf-var (_ , ez , vis-o))) ⊢$)
            (conv-fun (conv-fun (conv-unseal ez) (conv-seal ez)) (conv-id base-ℕ))
            (wf-⇒ (wf-⇒ (wf-var (_ , ez , vis-o))
                        (wf-var (_ , ez , vis-o))) wf-ℕ)

⊢Redex1b : Δ1b ∣ [] ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b ⦂ `ℕ
⊢Redex1b = ⊢· ⊢Fn1b ⊢W1b

peel-1b : Δ1b ⊢ (V1b ⟪ Θ1b , cΘ1b ⟫) · W1b
            -→ (V1b · (wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫)) ⟪ Θ1b , id `ℕ ⟫
peel-1b = Peel V-ƛ (V-⟪⟫ V-ƛ I-fun)

-- compare `n1b-¬W-rebuild` and `n1b-¬contractum`.
⊢contractum1b :
  Δ1b ∣ [] ⊢ (V1b · (wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫)) ⟪ Θ1b , id `ℕ ⟫
           ⦂ `ℕ
⊢contractum1b =
  env {p = ↑ˢ}
      (bw-o (wf-var (_ , ez , vis-o)) (bw-c (_ , es ez , vis-a) bw[]))
      (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , ez , vis-o))
                    (wf-var (_ , ez , vis-o))) ⊢$)
          ⊢W1b-crossed)
      (conv-id base-ℕ)
      wf-ℕ
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
  ⊢W1b-in : (blk (own (` 0)) ∷ Δ1b) ∣ [] ⊢ wkᴹ 1 W1b ⦂ (` 1 ⇒ ` 1)
  ⊢W1b-in = ⊢rename (mkRen (λ d → es d)) (λ eq → suc-inj eq) ⊢W1b
  ⊢W1b-crossed : intC Θ1b Δ1b ∣ [] ⊢ wkᴹ 1 W1b ⟪ dual Θ1b , unseal 0 ↦ seal 0 ⟫
                                   ⦂ (` 0 ⇒ ` 0)
  ⊢W1b-crossed =
    env (bw-c (_ , ez , vis-o) (bw-a (es (es ez)) bw[]))
        ⊢W1b-in
        (conv-fun (conv-unseal ez) (conv-seal ez))
        (wf-⇒ (wf-var (_ , ez , vis-o)) (wf-var (_ , ez , vis-o)))

-- THE GENERAL FACT BEHIND ALL THREE.  Masking RETAINS the owner's entry, and
-- an alias RECOVERS it — so no boundary operation can take an owner away.
-- In the current design this is exactly what fails: `entᴳ` writes `rvl⋆` at
-- the slot (`demote-x-always`, `demote-count-break/n1b/n4`), the rebuild has
-- `abst`, and the crossing value's licence dies (`¬⊢W-rebuild`).
mask-retains : ∀ {Δ X Y A} → Δ ∋ X := A
  → (mask Y Δ ∋ X := A) ⊎ (mask Y Δ ∋e X , blk (own A))
mask-retains {X = X} {Y = Y} d with Y ≟ℕ X
... | yes refl = inj₂ (upd-hit blk blk-comm d)
... | no ne    = inj₁ (upd-miss blk blk-comm ne d)

ali-recovers : ∀ {Δ X A} → Δ ∋e X , blk (own A) → unmask X Δ ∋ X := A
ali-recovers d = upd-hit unblk unblk-comm d

-- ── n4 (the x-alias break) ──────────────────────────────────────────────
--   old: Γz = xrvld (` 0) ∷ [] (an EXTERIOR-READ entry, the x-machinery),
--        Ξalias = rvl⋆ ∷ cnc 0 (` 0) ∷ [] — a conceal at a rep-less reveal.
-- In the mini-core there is no x-entry and no rep-less reveal to alias: a
-- conceal cites an owner, full stop.  The n4 CONFIGURATION becomes an
-- ordinary owner + alias, and its crossing repoints like the others.

Δ4 : Ctxᵗ
Δ4 = blk (own `ℕ) ∷ []          -- a slot masked by an enclosing boundary

Θ4 : BCtx                        -- re-expose it, then conceal it again
Θ4 = ali 0 ∷ []

_ : intC Θ4 Δ4 ≡ own `ℕ ∷ []
_ = refl

-- the alias RESTORES NAMEABILITY, and with it the owner's knowledge — which
-- is the fact `demote-x-always` denied.  It invents nothing: the rep `ℕ`
-- was already sitting in the masked entry.
_ : intC Θ4 Δ4 ∋ 0 := `ℕ
_ = ez

-- cnc-then-ali: a program that hides from itself and then looks again is
-- harmless and typeable — the round trip is the identity on the spine.
_ : intC (ali 0 ∷ []) (intC (cnc 0 ∷ []) (own `ℕ ∷ [])) ≡ own `ℕ ∷ []
_ = refl

-- ── E★′ (the shape-IV survivor) ─────────────────────────────────────────
--   old: Γ★ = abst ∷ rvld `ℕ ∷ [] , Θ★ = rvl (` 0) ∷ cnc 1 `ℕ ∷ []
-- The reveal's rep names the Λ-bound Y.  It survived only because the
-- ambient happened to hold `abst` there.  Here it is unremarkable.

Γ★ : Ctxᵗ
Γ★ = abst ∷ own `ℕ ∷ []

Θ★ : BCtx
Θ★ = own (` 0) ∷ cnc 1 ∷ []

_ : intC Θ★ Γ★ ≡ own (` 0) ∷ abst ∷ blk (own `ℕ) ∷ []
_ = refl

_ : dual Θ★ ≡ cnc 0 ∷ ali 2 ∷ []
_ = refl

_ : intC (dual Θ★) (intC Θ★ Γ★) ≡ blk (own (` 0)) ∷ Γ★
_ = refl

------------------------------------------------------------------------
-- §5  Q4 — the safe corpus
------------------------------------------------------------------------

-- THE CANCEL PAIR (c4 / gauntlet §9a):  (7 ⟪ ↓X , seal 0 ⟫) ⟪ ↑X:=ℕ , unseal 0 ⟫
-- Outer face ACTIVE (`unseal`), inner face INERT (`seal`) — exactly the old
-- Merge classification, now read off the conversion constructors.

Θ↑ : BCtx
Θ↑ = own `ℕ ∷ []

Θ↓ : BCtx
Θ↓ = cnc 0 ∷ []

cancelTm : Term
cancelTm = (($ 7) ⟪ Θ↓ , seal 0 ⟫) ⟪ Θ↑ , unseal 0 ⟫

⊢cancelTm : [] ∣ [] ⊢ cancelTm ⦂ `ℕ
⊢cancelTm =
  env (bw-o wf-ℕ bw[])
      (env (bw-c (_ , ez , vis-o) bw[]) ⊢$ (conv-seal ez) (wf-var (_ , ez , vis-o)))
      (conv-unseal ez)
      wf-ℕ

-- the pair is NOT a value (the outer face is active) and the cancel fires.
cancel-step : [] ⊢ cancelTm -→ ($ 7) ⟪ own `ℕ ∷ cnc 0 ∷ [] , idc `ℕ ⟫
cancel-step = Cancel {B = `ℕ} V-$

-- the residue is base-faced over a numeral, so `Drop$` finishes it.
drop-step : [] ⊢ ($ 7) ⟪ own `ℕ ∷ cnc 0 ∷ [] , id `ℕ ⟫ -→ $ 7
drop-step = Drop$ base-ℕ

_ : idc `ℕ ≡ id `ℕ
_ = refl

-- ── §9m (c9): the ≡/≈ gap CANNOT ARISE ──────────────────────────────────
--   old: Θq2 = rvl `ℕ ∷ [] (the reveal stores ℕ), Θq1 = cnc 0 (` 0) ∷ []
--   (the conceal stores the VARIABLE ` 0).  Two spellings of one fact; the
--   merge demanded ≡ and only ≈ held, so the term was STUCK (¬progress).
--
--   Here the conceal stores NO rep at all: `seal 0` names slot 0 and its
--   interior face is READ OFF the owner.  There is no second spelling, so
--   there is nothing for ≡ and ≈ to disagree about.  The theorem:

seal-face-is-the-owners-rep : ∀ {Δ X A B p}
  → Δ ⊢ seal X ∶ A ⇝ B ∙ p → Δ ∋ X := A
seal-face-is-the-owners-rep (conv-seal d) = d

unseal-face-is-the-owners-rep : ∀ {Δ X A B p}
  → Δ ⊢ unseal X ∶ A ⇝ B ∙ p → Δ ∋ X := B
unseal-face-is-the-owners-rep (conv-unseal d) = d

-- CANCEL'S FACE EQUATION, DEFINITIONAL (Q4).  At a cancel the inner
-- conceal's interior face and the outer reveal's exterior face are the
-- SAME lookup on the SAME spine, hence literally equal.  This one lemma
-- replaces cancel-agree + Reversal≈ + SkelEq + xrep-stored + MergeOK's two
-- face equations.
∋e-det : ∀ {Δ X E E′} → Δ ∋e X , E → Δ ∋e X , E′ → E ≡ E′
∋e-det ez     ez      = refl
∋e-det (es d) (es d′) = cong ⇑ᵉ (∋e-det d d′)

own-inj : ∀ {A B : Ty} → _≡_ {A = Ent} (own A) (own B) → A ≡ B
own-inj refl = refl

∋:=-det : ∀ {Δ X A B} → Δ ∋ X := A → Δ ∋ X := B → A ≡ B
∋:=-det d d′ = own-inj (∋e-det d d′)

cancel-faces-agree : ∀ {Δ X A B A′ B′ p q}
  → Δ ⊢ seal X ∶ A ⇝ B ∙ p     -- the inner conceal
  → Δ ⊢ unseal X ∶ A′ ⇝ B′ ∙ q   -- the owner it names
    ---------------------------
  → A ≡ B′
cancel-faces-agree cs cu =
  ∋:=-det (seal-face-is-the-owners-rep cs) (unseal-face-is-the-owners-rep cu)

module strong.proof.Canonicity where

-- THE CANONICITY INVARIANT — the OWNER-NAME reading.
--
-- Every conversion that reduction ever writes on a wrapper is a member of
-- the CANONICAL FAMILY: it is (a subtree of) `unsealAt X B`, `sealAt X B`,
-- or `idc A`.  This file states that family as an inductive predicate,
-- proves the three closure facts the rules need (MINT / DECOMPOSE /
-- RENAME), lifts it to terms, and proves it PRESERVED BY REDUCTION
-- (`canon-step`).
--
-- WHAT THE FAMILY SAYS, NOW THAT THE POLARITY INDEX IS GONE.  It used to
-- say two things at once: a POLARITY SHAPE (`unseal` leaves covariant,
-- `seal` leaves contravariant) and a NAME (every non-identity leaf cites
-- the SAME owner X, shifted under each `` `∀ `` exactly as
-- `unsealAt`/`sealAt` shift it).  The first half was a restatement of
-- what the indexed typing judgment already forced, and it went with the
-- index (Jeremy's ruling, strong.Conversion): a mixed tree like
-- `seal 0 ↦ seal 1` is now perfectly typeable, and TyPeelR's contractum
-- IS one (proof/PreserveObstruct §2).  The SECOND half is the content
-- that survives, and it is what `CanonAt X c` states below.
--
-- The term-level invariant (`CanonC`) quantifies the name existentially,
-- because a term's wrappers name different owners.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.Examples
  using (T₆; cancelTm; Δ₆; run-T₆; run-cancelTm)

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X : ℕ
    c s t : Conv
    L M M′ N W : Term
    σ : ℕ → Term

------------------------------------------------------------------------
-- 1.  The canonical family
------------------------------------------------------------------------

-- `CanonAt X c` — every non-identity leaf of c cites the owner X.  A
-- `` `∀ `` pushes a binder in front of the leaves, so the name it tracks
-- is `suc X`, which is precisely the shift `unsealAt`/`sealAt` perform on
-- the `` `∀ `` case.
data CanonAt : ℕ → Conv → Set where
  ca-id     : CanonAt X (id A)
  ca-unseal : CanonAt X (unseal X)
  ca-seal   : CanonAt X (seal X)
  ca-fun    : CanonAt X s → CanonAt X t → CanonAt X (s ↦ t)
  ca-all    : CanonAt (suc X) s → CanonAt X (`∀ s)

-- The term-level reading: a wrapper's conversion cites SOME single owner.
-- It has to be existential and it has to be single-name: TyPeelR's minted
-- face `unsealAtᶜ 0 s` reads TWO owners in one wrapper — the face's own,
-- and the one the instantiation just bound at slot 0 — which is exactly
-- what `¬CanonTyPeelR` (§8) records.
CanonC : Conv → Set
CanonC c = ∃[ X ] CanonAt X c

------------------------------------------------------------------------
-- 2.  MINT — the faces the rules write are canonical
------------------------------------------------------------------------

-- (a) TyBeta's face and its dual, by mutual induction on the face type —
-- the same recursion `unsealAt`/`sealAt` are defined by.
mutual
  canonAt-unsealAt : (X : ℕ) (B : Ty) → CanonAt X (unsealAt X B)
  canonAt-unsealAt X (` Y) with X ≟ℕ Y
  ... | yes refl = ca-unseal
  ... | no  _    = ca-id
  canonAt-unsealAt X `ℕ      = ca-id
  canonAt-unsealAt X `𝔹      = ca-id
  canonAt-unsealAt X (A ⇒ B) =
    ca-fun (canonAt-sealAt X A) (canonAt-unsealAt X B)
  canonAt-unsealAt X (`∀ A)  = ca-all (canonAt-unsealAt (suc X) A)

  canonAt-sealAt : (X : ℕ) (B : Ty) → CanonAt X (sealAt X B)
  canonAt-sealAt X (` Y) with X ≟ℕ Y
  ... | yes refl = ca-seal
  ... | no  _    = ca-id
  canonAt-sealAt X `ℕ      = ca-id
  canonAt-sealAt X `𝔹      = ca-id
  canonAt-sealAt X (A ⇒ B) =
    ca-fun (canonAt-unsealAt X A) (canonAt-sealAt X B)
  canonAt-sealAt X (`∀ A)  = ca-all (canonAt-sealAt (suc X) A)

-- (b) The identity at an arbitrary type — CancelR's and IdPush's residue.
-- It is canonical at EVERY name: the leaves of `idc` are all `id`, which
-- is the family's name-free leaf.
canonAt-idc : (X : ℕ) (A : Ty) → CanonAt X (idc A)
canonAt-idc X (` Y)   = ca-id
canonAt-idc X `ℕ      = ca-id
canonAt-idc X `𝔹      = ca-id
canonAt-idc X (A ⇒ B) = ca-fun (canonAt-idc X A) (canonAt-idc X B)
canonAt-idc X (`∀ A)  = ca-all (canonAt-idc (suc X) A)

canonC-unsealAt : (X : ℕ) (B : Ty) → CanonC (unsealAt X B)
canonC-unsealAt X B = X , canonAt-unsealAt X B

canonC-sealAt : (X : ℕ) (B : Ty) → CanonC (sealAt X B)
canonC-sealAt X B = X , canonAt-sealAt X B

canonC-idc : (A : Ty) → CanonC (idc A)
canonC-idc A = 0 , canonAt-idc 0 A

-- IdPush's other mint: the pushed `unseal` at the name the id-face wrote.
canonC-unseal : (X : ℕ) → CanonC (unseal X)
canonC-unseal X = X , ca-unseal

------------------------------------------------------------------------
-- 3.  DECOMPOSE — the subtree readings the crossing rules perform
------------------------------------------------------------------------

-- Peel reads `s ↦ t` apart; the DOMAIN comes back at the SAME owner,
-- which is exactly the crossing argument's face.
canonC-fun-dom : CanonC (s ↦ t) → CanonC s
canonC-fun-dom (X , ca-fun cs ct) = X , cs

canonC-fun-cod : CanonC (s ↦ t) → CanonC t
canonC-fun-cod (X , ca-fun cs ct) = X , ct

-- TyPeelR reads `∀ s` apart — and then MINTS on the body (`unsealAtᶜ 0`):
-- the slot the `` `∀ `` left abstract is now the owner the rule binds, so
-- the face's identity leaves at that slot become the instantiation.  The
-- decomposition itself only walks the name past the binder.
canonC-all : CanonC (`∀ s) → CanonC s
canonC-all (X , ca-all cs) = suc X , cs

------------------------------------------------------------------------
-- 4.  RENAME — canonicity survives a type-context renaming
------------------------------------------------------------------------

-- `renᴹ` (hence `wkᴹ`, used by Peel and TyPeelR on the term they move)
-- renames the conversions it passes.  The name moves with the renaming.
canonAt-ren : (ρ : Renameᵗ) → CanonAt X c → CanonAt (ρ X) (renᶜ ρ c)
canonAt-ren ρ ca-id          = ca-id
canonAt-ren ρ ca-unseal      = ca-unseal
canonAt-ren ρ ca-seal        = ca-seal
canonAt-ren ρ (ca-fun cs ct) =
  ca-fun (canonAt-ren ρ cs) (canonAt-ren ρ ct)
canonAt-ren ρ (ca-all cs)    = ca-all (canonAt-ren (extᵗ ρ) cs)

canonC-ren : (ρ : Renameᵗ) → CanonC c → CanonC (renᶜ ρ c)
canonC-ren ρ (X , cc) = ρ X , canonAt-ren ρ cc

------------------------------------------------------------------------
-- 6.  Lifting to terms
------------------------------------------------------------------------

-- `CanonTm M` — every wrapper in M carries a canonical conversion.
-- Structural, with no condition on the context morphisms: canonicity is a
-- property of FACES.
data CanonTm : Term → Set where
  ct-var : ∀ {x} → CanonTm (` x)
  ct-lit : ∀ {n} → CanonTm ($ n)
  ct-ƛ   : CanonTm N → CanonTm (ƛ A ∙ N)
  ct-·   : CanonTm L → CanonTm M → CanonTm (L · M)
  ct-Λ   : CanonTm N → CanonTm (Λ N)
  ct-·[] : CanonTm L → CanonTm (L ·[ B , A ])
  ct-⟪⟫  : ∀ {Θ} → CanonTm M → CanonC c → CanonTm (M ⟪ Θ , c ⟫)

-- Renaming a term renames its faces; §4 covers them.
canon-renᴹ : (ρ : Renameᵗ) → CanonTm M → CanonTm (renᴹ ρ M)
canon-renᴹ ρ ct-var           = ct-var
canon-renᴹ ρ ct-lit           = ct-lit
canon-renᴹ ρ (ct-ƛ cN)        = ct-ƛ (canon-renᴹ ρ cN)
canon-renᴹ ρ (ct-· cL cM)     = ct-· (canon-renᴹ ρ cL) (canon-renᴹ ρ cM)
canon-renᴹ ρ (ct-Λ cN)        = ct-Λ (canon-renᴹ (extᵗ ρ) cN)
canon-renᴹ ρ (ct-·[] cL)      = ct-·[] (canon-renᴹ ρ cL)
canon-renᴹ ρ (ct-⟪⟫ {Θ = Θ} cM cc) =
  ct-⟪⟫ (canon-renᴹ (extN (nbind Θ) ρ) cM)
        (canonC-ren (extN (nbind Θ) ρ) cc)

canon-wkᴹ : (n : ℕ) → CanonTm M → CanonTm (wkᴹ n M)
canon-wkᴹ n cM = canon-renᴹ (wkN n) cM

------------------------------------------------------------------------
-- 7.  Term substitution
------------------------------------------------------------------------

-- Boundaries are TERM-CLOSED: `shiftᵐ` and `substᵐ` return a wrapper
-- untouched (strong.TermSubst).  So no conversion is ever renamed by term
-- substitution, and canonicity is preserved for free — the only wrappers
-- in the result are those already in N or those carried in by σ.
CanonSub : (ℕ → Term) → Set
CanonSub σ = ∀ x → CanonTm (σ x)

-- Term-variable renaming touches no conversion (a wrapper is
-- term-closed), so canonicity passes through renⁿ unconditionally.
canon-renⁿ : (ρ : ℕ → ℕ) → CanonTm M → CanonTm (renⁿ ρ M)
canon-renⁿ ρ ct-var        = ct-var
canon-renⁿ ρ ct-lit        = ct-lit
canon-renⁿ ρ (ct-ƛ cN)     = ct-ƛ (canon-renⁿ (extⁿ ρ) cN)
canon-renⁿ ρ (ct-· cL cM)  = ct-· (canon-renⁿ ρ cL) (canon-renⁿ ρ cM)
canon-renⁿ ρ (ct-Λ cN)     = ct-Λ (canon-renⁿ ρ cN)
canon-renⁿ ρ (ct-·[] cL)   = ct-·[] (canon-renⁿ ρ cL)
canon-renⁿ ρ (ct-⟪⟫ cM cc) = ct-⟪⟫ cM cc

canon-shiftᵐ : CanonTm M → CanonTm (shiftᵐ M)
canon-shiftᵐ = canon-renⁿ suc

canon-extᵐ : CanonSub σ → CanonSub (extᵐ σ)
canon-extᵐ cσ zero    = ct-var
canon-extᵐ cσ (suc x) = canon-shiftᵐ (cσ x)

canon-substᵐ : CanonSub σ → CanonTm M → CanonTm (substᵐ σ M)
canon-substᵐ cσ (ct-var {x = x}) = cσ x
canon-substᵐ cσ ct-lit           = ct-lit
canon-substᵐ cσ (ct-ƛ cN)        = ct-ƛ (canon-substᵐ (canon-extᵐ cσ) cN)
canon-substᵐ cσ (ct-· cL cM)     =
  ct-· (canon-substᵐ cσ cL) (canon-substᵐ cσ cM)
canon-substᵐ cσ (ct-Λ cN)        =
  ct-Λ (canon-substᵐ (λ x → canon-renᴹ suc (cσ x)) cN)
canon-substᵐ cσ (ct-·[] cL)      = ct-·[] (canon-substᵐ cσ cL)
canon-substᵐ cσ (ct-⟪⟫ cM cc)    = ct-⟪⟫ cM cc

canon-subst : CanonTm N → CanonTm W → CanonTm (N [ W ]ᵐ)
canon-subst cN cW =
  canon-substᵐ (λ { zero → cW ; (suc x) → ct-var }) cN

------------------------------------------------------------------------
-- 8.  THE INVARIANT — canonicity is preserved by reduction
------------------------------------------------------------------------

-- One case per rule.  The story:
--
--   TyBeta   MINTS `unsealAt 0 B` at the owner it just bound (name 0).
--   Beta     substitutes — §7, wrappers are opaque to `substᵐ`.
--   Peel     DECOMPOSES `s ↦ t`; the argument is `wkᴹ`-renamed (§4) and
--            takes the domain `s` at the SAME owner.
--   TyPeelR  DECOMPOSES `∀ s`, RENAMES the moved value (`wkᴹ 1`), and
--            MINTS `unsealAtᶜ 0 s` on the body — the ONE case that is not
--            unconditional, because the mint puts leaves at slot 0
--            ALONGSIDE the face's own, so the result cites TWO owners;
--            hence the hypothesis `CanonTyPeelR` below, which is REFUTED.
--            (This is NOT a leftover of the polarity index: it survives
--            the index's retirement, for the two-owner reason.)
--   CancelR  MINTS `idc A` at the looked-up rep — a LEAF of the family
--            (`canonAt-idc`), canonical at every name.
--   IdPush   MINTS BOTH faces: the pushed `unseal X` (owner X) and the
--            residue `idc A`.  The old inner face was `id (` X)`, a leaf
--            that carries no owner, so the name comes from the face's own
--            payload — which typing shows is the right one
--            (proof/IdLayer.agda, `idpush-name`).
--   Drop$    contracts to `$ n`; no wrappers at all.
--   ξ-*      structural.
-- WHAT TYPEELR'S MINT OWES THE FAMILY, as a statement.
CanonTyPeelR : Set
CanonTyPeelR = ∀ {s : Conv} → CanonC (`∀ s) → CanonC (unsealAtᶜ 0 s)

-- IT FAILS on the ∀-face `∀ (id (` 0) ↦ seal 1)` — a polymorphic
-- ARGUMENT that crossed a Peel, `sealAt 0 (∀Y. Y ⇒ X)`.  That face cites
-- the ONE owner X (slot 1 under the `` `∀ ``), but its mint
-- `seal 0 ↦ seal 1` cites TWO: the owner TyPeelR just bound at slot 0 and
-- the crossed boundary's at slot 1.  The mint TYPES (proof/Preserve.
-- preserve-TyPeelR; the tree was untypeable only under the retired
-- polarity index) — it is the SINGLE-OWNER reading that it leaves.
canonC-∀face : CanonC (`∀ (id (` 0) ↦ seal 1))
canonC-∀face = 0 , ca-all (ca-fun ca-id ca-seal)

_ : unsealAtᶜ 0 (id (` 0) ↦ seal 1) ≡ seal 0 ↦ seal 1
_ = refl

¬canonC-seal↦seal : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-seal↦seal (X , ca-fun ca-seal ())

¬CanonTyPeelR : ¬ CanonTyPeelR
¬CanonTyPeelR tp = ¬canonC-seal↦seal (tp canonC-∀face)

canon-step : ∀ {Δ} → CanonTyPeelR → CanonTm M → Δ ⊢ M -→ M′ → CanonTm M′
canon-step tp (ct-·[] (ct-Λ cN)) (TyBeta {B = B} _) =
  ct-⟪⟫ cN (canonC-unsealAt 0 B)
canon-step tp (ct-· (ct-ƛ cN) cW) (Beta _) = canon-subst cN cW
canon-step tp (ct-· (ct-⟪⟫ cV cst) cW) (Peel {Θ = Θ} _ _) =
  ct-⟪⟫ (ct-· cV (ct-⟪⟫ (canon-wkᴹ (nbind Θ) cW) (canonC-fun-dom cst)))
        (canonC-fun-cod cst)
canon-step tp (ct-·[] (ct-⟪⟫ cV cs)) (TyPeelR _ _) =
  ct-⟪⟫ (ct-·[] (canon-wkᴹ 1 cV)) (tp cs)
canon-step tp (ct-⟪⟫ (ct-⟪⟫ cV _) _) (CancelR {Θ₁ = Θ₁} {A = A} _ _) =
  ct-⟪⟫ (ct-⟪⟫ cV (canonC-idc (liftN (nbind Θ₁) A))) (canonC-idc A)
canon-step tp (ct-⟪⟫ _ _) (Drop$ _) = ct-lit
canon-step tp (ct-⟪⟫ (ct-⟪⟫ cV _) _) (IdPush {X = X} {A = A} _ _) =
  ct-⟪⟫ (ct-⟪⟫ cV (canonC-unseal X)) (canonC-idc A)
canon-step tp (ct-· cL cM)  (ξ-·-l st)   = ct-· (canon-step tp cL st) cM
canon-step tp (ct-· cV cM)  (ξ-·-r _ st) = ct-· cV (canon-step tp cM st)
canon-step tp (ct-·[] cL)   (ξ-·[] st)   = ct-·[] (canon-step tp cL st)
canon-step tp (ct-Λ cN)     (ξ-Λ st)     = ct-Λ (canon-step tp cN st)
canon-step tp (ct-⟪⟫ cM cc) (ξ-⟪⟫ st)    = ct-⟪⟫ (canon-step tp cM st) cc

canon-steps : ∀ {Δ} → CanonTyPeelR → CanonTm M → Δ ⊢ M -→* M′ → CanonTm M′
canon-steps tp cM done          = cM
canon-steps tp cM (st then sts) = canon-steps tp (canon-step tp cM st) sts

------------------------------------------------------------------------
-- 9.  SOURCES — plain System F terms are canonical, vacuously
------------------------------------------------------------------------

-- Compilation from plain System F introduces no boundary at all: every
-- wrapper in a reachable term was minted by a reduction step, so §8 is
-- the whole story.  Stated for the record.
data Plain : Term → Set where
  pl-var : ∀ {x} → Plain (` x)
  pl-lit : ∀ {n} → Plain ($ n)
  pl-ƛ   : Plain N → Plain (ƛ A ∙ N)
  pl-·   : Plain L → Plain M → Plain (L · M)
  pl-Λ   : Plain N → Plain (Λ N)
  pl-·[] : Plain L → Plain (L ·[ B , A ])

canon-source : Plain M → CanonTm M
canon-source pl-var        = ct-var
canon-source pl-lit        = ct-lit
canon-source (pl-ƛ pN)     = ct-ƛ (canon-source pN)
canon-source (pl-· pL pM)  = ct-· (canon-source pL) (canon-source pM)
canon-source (pl-Λ pN)     = ct-Λ (canon-source pN)
canon-source (pl-·[] pL)   = ct-·[] (canon-source pL)

------------------------------------------------------------------------
-- 10.  Validation on the regression corpus
------------------------------------------------------------------------

-- T₆ = ((7 ⟪ [] , seal 1 ⟫) ⟪ bind ℕ , id (` 1) ⟫) ⟪ bind ℕ , unseal 0 ⟫
-- Three wrappers, three families: a conceal at owner 1, an ambipolar
-- id-layer, a reveal at owner 0.
canonTm-T₆ : CanonTm T₆
canonTm-T₆ =
  ct-⟪⟫ (ct-⟪⟫ (ct-⟪⟫ ct-lit (1 , ca-seal))
               (0 , ca-id))
        (canonC-unseal 0)

-- …and the invariant survives the whole IdPush ⨟ Cancel ⨟ Drop$ ⨟ Drop$
-- run, which is what `canon-step` is for.  (Neither run takes a TyPeelR
-- step, so the hypothesis is carried but never consumed.)
canonTm-T₆-run : CanonTyPeelR → CanonTm ($ 7)
canonTm-T₆-run tp = canon-steps tp canonTm-T₆ run-T₆

canonTm-cancelTm : CanonTm cancelTm
canonTm-cancelTm =
  ct-⟪⟫ (ct-⟪⟫ ct-lit (0 , ca-seal)) (canonC-unseal 0)

canonTm-cancelTm-run : CanonTyPeelR → CanonTm ($ 7)
canonTm-cancelTm-run tp = canon-steps tp canonTm-cancelTm run-cancelTm

-- The mint lemmas, on the ground: TyBeta's face at a function type is the
-- ↦-tree whose domain is the DUAL family.
_ : unsealAt 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

_ : CanonC (unsealAt 0 (` 0 ⇒ ` 0))
_ = canonC-unsealAt 0 (` 0 ⇒ ` 0)

-- A TWO-OWNER tree — `seal` leaves at two different names — is outside
-- the family, though (unlike under the retired polarity index) it is
-- perfectly TYPEABLE: it is what TyPeelR mints, and the frames, not a
-- global index, are what keep the two owners apart.
¬canonC-two-owners : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-two-owners = ¬canonC-seal↦seal

module strong-rep-store.proof.Canonicity where

-- THE CANONICITY INVARIANT — the BINDER-NAME reading.
--
-- Every conversion that reduction ever writes on a wrapper is a member of
-- the CANONICAL FAMILY: it is a subtree, a re-spelling, or a mint of
-- `reveal X B`, `conceal X B`, `mkId A`, or `unseal X`.  This file states
-- that family as an inductive predicate, proves the four closure facts the
-- rules need (MINT / DECOMPOSE / RENAME / RE-SPELL), lifts it to terms, and
-- proves it PRESERVED BY REDUCTION (`canon-step`).
--
-- WHAT THE FAMILY SAYS.  It used to say two things at once: a POLARITY
-- SHAPE (`unseal` leaves covariant, `seal` leaves contravariant) and a
-- NAME (every non-identity leaf cites the SAME binder X, shifted under each
-- `` `∀ `` exactly as `reveal`/`conceal` shift it).  The first half was a
-- restatement of what the indexed typing judgment already forced, and it
-- went with the index (Jeremy's ruling, strong-rep-store.Conversion): a mixed
-- tree
-- like `seal 0 ↦ seal 1` is now perfectly typeable, and TyPeelR's
-- contractum IS one.  The SECOND half is the content that survives, and it
-- is what `CanonAt X c` states below.
--
-- WHAT THE TWO UNIVERSES ADD (2026-09-19).  `Peel` no longer carries its
-- crossing argument's conversion `s` onto the dual: the dual's conversion
-- context is a DIFFERENT name map, so the rule carries the dual's own
-- spelling `s′` with a `SameConv` relating the two (strong-rep-store.Reduction).
-- Canonicity must therefore RE-SPELL, and that is §5.  The family is
-- stated a second time one universe up — `CanonAtᴿ`, on REPRESENTATION
-- variables — `SameConv` transports it down and back, and the way back
-- needs the target name map to be a FUNCTION.  So `canon-step` takes
-- `Unique (names Δ)`, for the same reason `det` takes a typing derivation
-- (notes/DECISIONS.md, 2026-09-18): uniqueness is a property of the
-- context, not a premise of a rule.  Every other rule's mint is a subtree,
-- a `mkId`, or an `unseal` at a name the rule already carries.
--
-- The re-spelling needs one more distinction the one-universe design did
-- not: a conversion all of whose leaves are identities (`AllId`) names no
-- binder at all, so it is canonical at EVERY name and its re-spelling has
-- no name to inherit.  Both transports therefore return a SUM.
--
-- The term-level invariant (`CanonC`) quantifies the name existentially,
-- because a term's wrappers name different binders.
--
-- The old §10 validated the invariant on the regression corpus.  It is
-- dropped while `strong-rep-store.Examples` is unported on this branch; the
-- ground-level mint checks it sat beside are kept as §10.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction

private
  variable
    Δ Δ′ : Ctxᵗ
    η η′ : TyCtx
    A B R : Ty
    X Y : ℕ
    α β : RVar
    c s t r u : Conv
    L M M′ N W : Term
    i : Img
    σ : Var → Img

------------------------------------------------------------------------
-- 1.  The canonical family
------------------------------------------------------------------------

-- `CanonAt X c` — every non-identity leaf of c cites the binder X.  A
-- `` `∀ `` pushes a binder in front of the leaves, so the name it tracks
-- is `suc X`, which is precisely the shift `reveal`/`conceal` perform on
-- the `` `∀ `` case.
data CanonAt : ℕ → Conv → Set where
  ca-id     : CanonAt X (id A)
  ca-unseal : CanonAt X (unseal X)
  ca-seal   : CanonAt X (seal X)
  ca-fun    : CanonAt X s → CanonAt X t → CanonAt X (s ↦ t)
  ca-all    : CanonAt (suc X) s → CanonAt X (`∀ s)

-- The term-level reading: a wrapper's conversion cites SOME single binder.
-- It has to be existential and it has to be single-name: TyPeelR's minted
-- conversion `instReveal 0 s` reads TWO binders in one wrapper — the
-- conversion's own, and the one the instantiation just bound at slot 0 —
-- which is exactly what `¬CanonTyPeelR` (§8) records.
CanonC : Conv → Set
CanonC c = ∃[ X ] CanonAt X c

-- The name-free members of the family: every leaf is an identity.  These
-- are canonical at every name, and they are the ones a re-spelling cannot
-- read a name off.
data AllId : Conv → Set where
  ai-id  : AllId (id A)
  ai-fun : AllId s → AllId t → AllId (s ↦ t)
  ai-all : AllId s → AllId (`∀ s)

allId-canon : AllId c → (X : ℕ) → CanonAt X c
allId-canon ai-id          X = ca-id
allId-canon (ai-fun as at) X = ca-fun (allId-canon as X) (allId-canon at X)
allId-canon (ai-all as)    X = ca-all (allId-canon as (suc X))

------------------------------------------------------------------------
-- 2.  MINT — the conversions the rules write are canonical
------------------------------------------------------------------------

-- (a) TyBeta's conversion and its dual, by mutual induction on the type
-- it is minted from — the same recursion `reveal`/`conceal` are defined
-- by.
mutual
  canonAt-reveal : (X : ℕ) (B : Ty) → CanonAt X (reveal X B)
  canonAt-reveal X (` Y) with X ≟ Y
  ... | yes refl = ca-unseal
  ... | no  _    = ca-id
  canonAt-reveal X `ℕ      = ca-id
  canonAt-reveal X `𝔹      = ca-id
  canonAt-reveal X (A ⇒ B) =
    ca-fun (canonAt-conceal X A) (canonAt-reveal X B)
  canonAt-reveal X (`∀ A)  = ca-all (canonAt-reveal (suc X) A)

  canonAt-conceal : (X : ℕ) (B : Ty) → CanonAt X (conceal X B)
  canonAt-conceal X (` Y) with X ≟ Y
  ... | yes refl = ca-seal
  ... | no  _    = ca-id
  canonAt-conceal X `ℕ      = ca-id
  canonAt-conceal X `𝔹      = ca-id
  canonAt-conceal X (A ⇒ B) =
    ca-fun (canonAt-reveal X A) (canonAt-conceal X B)
  canonAt-conceal X (`∀ A)  = ca-all (canonAt-conceal (suc X) A)

-- (b) The identity at an arbitrary type — CancelR's and IdPush's residue.
-- It is the name-free half of the family.
allId-mkId : (A : Ty) → AllId (mkId A)
allId-mkId (` Y)   = ai-id
allId-mkId `ℕ      = ai-id
allId-mkId `𝔹      = ai-id
allId-mkId (A ⇒ B) = ai-fun (allId-mkId A) (allId-mkId B)
allId-mkId (`∀ A)  = ai-all (allId-mkId A)

canonAt-mkId : (X : ℕ) (A : Ty) → CanonAt X (mkId A)
canonAt-mkId X A = allId-canon (allId-mkId A) X

canonC-reveal : (X : ℕ) (B : Ty) → CanonC (reveal X B)
canonC-reveal X B = X , canonAt-reveal X B

canonC-conceal : (X : ℕ) (B : Ty) → CanonC (conceal X B)
canonC-conceal X B = X , canonAt-conceal X B

canonC-mkId : (A : Ty) → CanonC (mkId A)
canonC-mkId A = 0 , canonAt-mkId 0 A

-- IdPush's other mint: the pushed `unseal` at the name the rule carries.
canonC-unseal : (X : ℕ) → CanonC (unseal X)
canonC-unseal X = X , ca-unseal

------------------------------------------------------------------------
-- 3.  DECOMPOSE — the subtree readings the crossing rules perform
------------------------------------------------------------------------

-- Peel reads `s ↦ t` apart; the DOMAIN comes back at the SAME binder,
-- and is then re-spelled onto the dual's name map (§5).
canonC-fun-dom : CanonC (s ↦ t) → CanonC s
canonC-fun-dom (X , ca-fun cs ct) = X , cs

canonC-fun-cod : CanonC (s ↦ t) → CanonC t
canonC-fun-cod (X , ca-fun cs ct) = X , ct

-- TyPeelR reads `∀ s` apart — and then MINTS on the body (`instReveal 0`):
-- the slot the `` `∀ `` left abstract is now the binder the rule
-- introduces, so the conversion's identity leaves at that slot become
-- the instantiation.  The decomposition itself only walks the name past
-- the binder.
canonC-all : CanonC (`∀ s) → CanonC s
canonC-all (X , ca-all cs) = suc X , cs

------------------------------------------------------------------------
-- 4.  RENAME — canonicity survives a type-context renaming
------------------------------------------------------------------------

-- `renᴹ²` (hence `wkᴹ`, `⇑ᴹ`, and the rep-only renamings Peel and
-- TyPeelR-⟪⟫ perform) renames the conversions it passes with its ORDINARY
-- component.  The name moves with that renaming.
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
-- 5.  RE-SPELL — canonicity crosses a `SameConv`
------------------------------------------------------------------------

-- THE FAMILY ONE UNIVERSE UP.  A representation-universe conversion is
-- canonical at a REPRESENTATION VARIABLE.  `_⊩_~_` shifts that variable
-- under a `` `∀ `` exactly as `CanonAt` shifts the ordinary name, because
-- its `` `∀ `` clause reads the body at `zero ∷ shiftNames η`.
data CanonAtᴿ : RVar → Conv → Set where
  car-id     : CanonAtᴿ α (id R)
  car-unseal : CanonAtᴿ α (unseal α)
  car-seal   : CanonAtᴿ α (seal α)
  car-fun    : CanonAtᴿ α r → CanonAtᴿ α u → CanonAtᴿ α (r ↦ u)
  car-all    : CanonAtᴿ (suc α) r → CanonAtᴿ α (`∀ r)

allIdᴿ-canon : AllId r → (α : RVar) → CanonAtᴿ α r
allIdᴿ-canon ai-id          α = car-id
allIdᴿ-canon (ai-fun as at) α =
  car-fun (allIdᴿ-canon as α) (allIdᴿ-canon at α)
allIdᴿ-canon (ai-all as)    α = car-all (allIdᴿ-canon as (suc α))

shiftNames-∋ : η ∋ˡ X := α → shiftNames η ∋ˡ X := suc α
shiftNames-∋ here      = here
shiftNames-∋ (there d) = there (shiftNames-∋ d)

shiftNames-∋⁻ : (η : TyCtx) → shiftNames η ∋ˡ X := β
  → ∃[ α ] ((β ≡ suc α) × (η ∋ˡ X := α))
shiftNames-∋⁻ (γ ∷ η) here      = γ , refl , here
shiftNames-∋⁻ (γ ∷ η) (there d) with shiftNames-∋⁻ η d
... | α , refl , d′ = α , refl , there d′

-- DOWN.  A conversion canonical at the ordinary name X denotes a
-- representation conversion canonical at the representation variable X
-- names — unless it names nothing at all.
canon-rep : η ⊩ s ~ r → CanonAt X s
  → AllId r ⊎ (∃[ α ] ((η ∋ˡ X := α) × CanonAtᴿ α r))
canon-rep (sameᶜ-id p)      ca-id          = inj₁ ai-id
canon-rep (sameᶜ-seal d)    ca-seal        = inj₂ (_ , d , car-seal)
canon-rep (sameᶜ-unseal d)  ca-unseal      = inj₂ (_ , d , car-unseal)
canon-rep (sameᶜ-fun a b)   (ca-fun cs ct)
  with canon-rep a cs | canon-rep b ct
... | inj₁ ar          | inj₁ au          = inj₁ (ai-fun ar au)
... | inj₁ ar          | inj₂ (α , d , c) =
  inj₂ (α , d , car-fun (allIdᴿ-canon ar α) c)
... | inj₂ (α , d , c) | inj₁ au          =
  inj₂ (α , d , car-fun c (allIdᴿ-canon au α))
... | inj₂ (α , d , c) | inj₂ (β , d′ , c′)
  with ∋ˡ-det d d′
...   | refl = inj₂ (α , d , car-fun c c′)
canon-rep {η = η} (sameᶜ-all a) (ca-all cs)
  with canon-rep a cs
... | inj₁ ar                    = inj₁ (ai-all ar)
... | inj₂ (α₀ , there d₀ , c)
  with shiftNames-∋⁻ η d₀
...   | α , refl , d = inj₂ (α , d , car-all c)

-- UP.  On a name map that is a FUNCTION, a representation conversion
-- canonical at α has only one ordinary reading, so its spelling cites one
-- name throughout.
canon-name : Unique η′ → η′ ⊩ s ~ r → CanonAtᴿ α r
  → AllId s ⊎ (∃[ Y ] ((η′ ∋ˡ Y := α) × CanonAt Y s))
canon-name uq (sameᶜ-id p)     car-id          = inj₁ ai-id
canon-name uq (sameᶜ-seal d)   car-seal        = inj₂ (_ , d , ca-seal)
canon-name uq (sameᶜ-unseal d) car-unseal      = inj₂ (_ , d , ca-unseal)
canon-name uq (sameᶜ-fun a b)  (car-fun cr cu)
  with canon-name uq a cr | canon-name uq b cu
... | inj₁ as          | inj₁ at          = inj₁ (ai-fun as at)
... | inj₁ as          | inj₂ (Y , d , c) =
  inj₂ (Y , d , ca-fun (allId-canon as Y) c)
... | inj₂ (Y , d , c) | inj₁ at          =
  inj₂ (Y , d , ca-fun c (allId-canon at Y))
... | inj₂ (Y , d , c) | inj₂ (Z , d′ , c′)
  with unique-lookup uq d d′
...   | refl = inj₂ (Y , d , ca-fun c c′)
canon-name {η′ = η′} uq (sameᶜ-all a) (car-all cr)
  with canon-name (unique∷ fresh-zero-shift (unique-shift uq)) a cr
... | inj₁ as                  = inj₁ (ai-all as)
... | inj₂ (suc Y₀ , there d₀ , c)
  with shiftNames-∋⁻ η′ d₀
...   | α , refl , d = inj₂ (Y₀ , d , ca-all c)

-- THE RE-SPELLING.  `Peel` carries `SameConv Δᵈ s′ Δᶜ s`; the `Unique` its
-- first context needs is `dual-unique` at the rule's own two readings.
canonC-respell : Unique η′
  → ∃[ r ] ((η′ ⊩ s ~ r) × (η ⊩ t ~ r))
  → CanonC t → CanonC s
canonC-respell uq (r , p , q) (X , ct)
  with canon-rep q ct
... | inj₁ ar with canon-name uq p (allIdᴿ-canon ar 0)
...   | inj₁ as        = 0 , allId-canon as 0
...   | inj₂ (Y , d , c) = Y , c
canonC-respell uq (r , p , q) (X , ct)
    | inj₂ (α , d , c) with canon-name uq p c
...   | inj₁ as          = 0 , allId-canon as 0
...   | inj₂ (Y , d′ , c′) = Y , c′

------------------------------------------------------------------------
-- 6.  Lifting to terms
------------------------------------------------------------------------

-- `CanonTm M` — every wrapper in M carries a canonical conversion.
-- Structural, with no condition on the boundary scopes: canonicity is a
-- property of CONVERSIONS.
data CanonTm : Term → Set where
  ct-var   : ∀ {x} → CanonTm (` x)
  ct-lit   : ∀ {n} → CanonTm ($ n)
  ct-true  : CanonTm `true
  ct-false : CanonTm `false
  ct-ƛ     : CanonTm N → CanonTm (ƛ A ∙ N)
  ct-·     : CanonTm L → CanonTm M → CanonTm (L · M)
  ct-Λ     : CanonTm N → CanonTm (Λ N)
  ct-·[]   : CanonTm L → CanonTm (L ·[ B , A ])
  ct-⟪⟫    : ∀ {Θ} → CanonTm M → CanonC c → CanonTm (M ⟪ Θ , c ⟫)

-- Renaming a term renames its conversions with the renaming's ORDINARY
-- component; §4 covers them.  A rep-only renaming — `ren² idᵗ _`, which
-- is what `Peel`, `TyPeelR-⟪⟫` and `crossΛᴹ` perform — leaves every
-- conversion name where it was.
canon-renᴹ² : (ρ : TyRename) → CanonTm M → CanonTm (renᴹ² ρ M)
canon-renᴹ² ρ ct-var           = ct-var
canon-renᴹ² ρ ct-lit           = ct-lit
canon-renᴹ² ρ ct-true          = ct-true
canon-renᴹ² ρ ct-false         = ct-false
canon-renᴹ² ρ (ct-ƛ cN)        = ct-ƛ (canon-renᴹ² ρ cN)
canon-renᴹ² ρ (ct-· cL cM)     =
  ct-· (canon-renᴹ² ρ cL) (canon-renᴹ² ρ cM)
canon-renᴹ² ρ (ct-Λ cN)        = ct-Λ (canon-renᴹ² (underΛ-ren ρ) cN)
canon-renᴹ² ρ (ct-·[] cL)      = ct-·[] (canon-renᴹ² ρ cL)
canon-renᴹ² ρ (ct-⟪⟫ {Θ = Θ} cM cc) =
  ct-⟪⟫ (canon-renᴹ² (underReps-ren (numBinds Θ) ρ) cM)
        (canonC-ren (ordinary ρ) cc)

canon-renᴹ : (ρ : Renameᵗ) → CanonTm M → CanonTm (renᴹ ρ M)
canon-renᴹ ρ cM = canon-renᴹ² (ren² ρ ρ) cM

canon-wkᴹ : (n : ℕ) → CanonTm M → CanonTm (wkᴹ n M)
canon-wkᴹ n cM = canon-renᴹ (wkN n) cM

------------------------------------------------------------------------
-- 7.  Term substitution
------------------------------------------------------------------------

-- Boundaries are TERM-CLOSED: `shiftᵐ` and `substᵐ` return a wrapper
-- untouched (strong-rep-store.TermSubst).  So no conversion is ever renamed by
-- term
-- substitution, and canonicity is preserved for free — the only wrappers
-- in the result are those already in N, those carried in by σ, and THE
-- DUAL WRAPPER FRAME-EXACT BETA MINTS AT EACH CROSSED Λ, whose conversion
-- is `mkId` — the name-free half of the family (`allId-mkId`).
CanonImg : Img → Set
CanonImg i = CanonTm (imgTm i)

CanonSub : (Var → Img) → Set
CanonSub σ = ∀ x → CanonImg (σ x)

-- Term-variable renaming touches no conversion (a wrapper is
-- term-closed), so canonicity passes through renⁿ unconditionally.
canon-renⁿ : (ρ : Var → Var) → CanonTm M → CanonTm (renⁿ ρ M)
canon-renⁿ ρ ct-var        = ct-var
canon-renⁿ ρ ct-lit        = ct-lit
canon-renⁿ ρ ct-true       = ct-true
canon-renⁿ ρ ct-false      = ct-false
canon-renⁿ ρ (ct-ƛ cN)     = ct-ƛ (canon-renⁿ (extⁿ ρ) cN)
canon-renⁿ ρ (ct-· cL cM)  = ct-· (canon-renⁿ ρ cL) (canon-renⁿ ρ cM)
canon-renⁿ ρ (ct-Λ cN)     = ct-Λ (canon-renⁿ ρ cN)
canon-renⁿ ρ (ct-·[] cL)   = ct-·[] (canon-renⁿ ρ cL)
canon-renⁿ ρ (ct-⟪⟫ cM cc) = ct-⟪⟫ cM cc

canon-shiftᵐ : CanonTm M → CanonTm (shiftᵐ M)
canon-shiftᵐ = canon-renⁿ suc

-- A variable image is canonical outright; a VALUE image is closed, so the
-- term-variable weakening leaves it alone.
canon-shiftᴵ : (i : Img) → CanonImg i → CanonImg (shiftᴵ i)
canon-shiftᴵ (ivar x)   ci = ct-var
canon-shiftᴵ (ival W A) ci = ci

-- THE Λ CROSSING.  A value image acquires the DUAL WRAPPER, whose
-- conversion is `mkId (⇑ᵗ A)` — name-free, hence canonical at every name —
-- over the value weakened in the REPRESENTATION universe only (§6).
canon-⇑ᴵ : (i : Img) → CanonImg i → CanonImg (⇑ᴵ i)
canon-⇑ᴵ (ivar x)   ci = ct-var
canon-⇑ᴵ (ival W A) ci =
  ct-⟪⟫ (canon-renᴹ² (ren² idᵗ suc) ci) (canonC-mkId (⇑ᵗ A))

canon-extᴵ : (σ : Var → Img) → CanonSub σ → CanonSub (extᴵ σ)
canon-extᴵ σ cσ zero    = ct-var
canon-extᴵ σ cσ (suc x) = canon-shiftᴵ (σ x) (cσ x)

canon-substᵐ : CanonSub σ → CanonTm M → CanonTm (substᵐ σ M)
canon-substᵐ cσ (ct-var {x = x})          = cσ x
canon-substᵐ cσ ct-lit                    = ct-lit
canon-substᵐ cσ ct-true                   = ct-true
canon-substᵐ cσ ct-false                  = ct-false
canon-substᵐ {σ = σ} cσ (ct-ƛ cN)         =
  ct-ƛ (canon-substᵐ (canon-extᴵ σ cσ) cN)
canon-substᵐ cσ (ct-· cL cM)              =
  ct-· (canon-substᵐ cσ cL) (canon-substᵐ cσ cM)
canon-substᵐ {σ = σ} cσ (ct-Λ cN)         =
  ct-Λ (canon-substᵐ (λ x → canon-⇑ᴵ (σ x) (cσ x)) cN)
canon-substᵐ cσ (ct-·[] cL)               = ct-·[] (canon-substᵐ cσ cL)
canon-substᵐ cσ (ct-⟪⟫ cM cc)             = ct-⟪⟫ cM cc

canon-subst : CanonTm N → CanonTm W → CanonTm (N [ W ∶ A ]ᵐ)
canon-subst cN cW =
  canon-substᵐ (λ { zero → cW ; (suc x) → ct-var }) cN

------------------------------------------------------------------------
-- 8.  THE INVARIANT — canonicity is preserved by reduction
------------------------------------------------------------------------

-- One case per rule.  The story:
--
--   TyBeta   MINTS `reveal 0 B` at the binder it just bound (name 0).
--   Beta     substitutes — §7, wrappers are opaque to `substᵐ`.
--   Peel     DECOMPOSES `s ↦ t` and RE-SPELLS the domain onto the dual's
--            name map (§5); the argument is rep-only renamed (§6), which
--            touches no conversion name.
--   TyPeelR-Λ / TyPeelR-⟪⟫
--            both DECOMPOSE `∀ s` and MINT `instReveal 0 s` on the body —
--            the ONE case that is not unconditional, because the mint
--            puts leaves at slot 0 ALONGSIDE the conversion's own, so the
--            result cites TWO binders; hence the hypothesis
--            `CanonTyPeelR` below, which is REFUTED.  (This is NOT a
--            leftover of the polarity index: it survives the index's
--            retirement, for the two-binder reason.)  The Λ clause moves
--            nothing; the wrapper clause renames the moved boundary and
--            appends a lock to its frame, which touches no conversion.
--   CancelR  MINTS `mkId A′` and `mkId A` — name-free leaves of the family.
--   IdPush   MINTS BOTH conversions: the pushed `unseal X′` (binder X′,
--            which the rule carries) and the residue `mkId A`.
--   Drop$ / Drop-true / Drop-false
--            contract to a literal; no wrappers at all.
--   ξ-*      structural; ξ-Λ and ξ-⟪⟫ transport `Unique` through
--            `unique-underΛ` and `interior-unique`.

-- WHAT TYPEELR'S MINT OWES THE FAMILY, as a statement.
CanonTyPeelR : Set
CanonTyPeelR = ∀ {s : Conv} → CanonC (`∀ s) → CanonC (instReveal 0 s)

-- IT FAILS on the ∀ conversion `∀ (id (` 0) ↦ seal 1)` — a polymorphic
-- ARGUMENT that crossed a Peel, `conceal 0 (∀Y. Y ⇒ X)`.  That
-- conversion cites the ONE binder X (slot 1 under the `` `∀ ``), but its
-- mint `seal 0 ↦ seal 1` cites TWO: the binder TyPeelR just bound at slot 0
-- and the crossed boundary's at slot 1.  The mint TYPES
-- (strong-rep-store.proof.Preserve, `preserve-TyPeelR-Λ`; the tree was
-- untypeable
-- only under the retired index) — it is the SINGLE-BINDER reading that it
-- leaves.
canonC-∀conv : CanonC (`∀ (id (` 0) ↦ seal 1))
canonC-∀conv = 0 , ca-all (ca-fun ca-id ca-seal)

_ : instReveal 0 (id (` 0) ↦ seal 1) ≡ seal 0 ↦ seal 1
_ = refl

¬canonC-seal↦seal : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-seal↦seal (X , ca-fun ca-seal ())

¬CanonTyPeelR : ¬ CanonTyPeelR
¬CanonTyPeelR tp = ¬canonC-seal↦seal (tp canonC-∀conv)

canon-step : ∀ {Δ} → Unique (names Δ) → CanonTyPeelR
  → CanonTm M → Δ ⊢ M -→ M′ → CanonTm M′
canon-step uq tp (ct-·[] (ct-Λ cN)) (TyBeta {B = B} _ _) =
  ct-⟪⟫ cN (canonC-reveal 0 B)
canon-step uq tp (ct-· (ct-ƛ cN) cW) (Beta _) = canon-subst cN cW
canon-step uq tp (ct-· (ct-⟪⟫ cV cst) cW) (Peel _ _ rc ri rd sc) =
  ct-⟪⟫ (ct-· cV (ct-⟪⟫ (canon-renᴹ² (ren² idᵗ (wkN _)) cW)
                        (canonC-respell (dual-unique uq ri rd) sc
                                        (canonC-fun-dom cst))))
        (canonC-fun-cod cst)
canon-step uq tp (ct-·[] (ct-⟪⟫ (ct-Λ cN) cs)) (TyPeelR-Λ _ _ _ _) =
  ct-⟪⟫ cN (tp cs)
canon-step uq tp (ct-·[] (ct-⟪⟫ (ct-⟪⟫ cW cs′) cs))
              (TyPeelR-⟪⟫ {Δ′ᶜ = Δ′ᶜ} {Δ″ᶜ = Δ″ᶜ} {Θ′ = Θ′}
                _ _ _ _ ri⁺ r″ sc _ _ _) =
  ct-⟪⟫ (ct-·[] (ct-⟪⟫ (canon-renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) cW)
                       (canonC-respell
                         (conversion-unique
                           (interior-unique uq ri⁺) r″)
                         (sameConv-∀ {Γ = Δ″ᶜ}
                           {Γ′ = renNameCtx
                             (extN (numBinds Θ′) suc) Δ″ᶜ Δ′ᶜ} sc)
                         cs′)))
        (tp cs)
canon-step uq tp (ct-⟪⟫ (ct-⟪⟫ cV _) _)
              (CancelR {A = A} {A′ = A′} _ _ _ _ _ _ _ _) =
  ct-⟪⟫ (ct-⟪⟫ cV (canonC-mkId A′)) (canonC-mkId A)
canon-step uq tp (ct-⟪⟫ _ _) (Drop$ _)     = ct-lit
canon-step uq tp (ct-⟪⟫ _ _) Drop-true     = ct-true
canon-step uq tp (ct-⟪⟫ _ _) Drop-false    = ct-false
canon-step uq tp (ct-⟪⟫ (ct-⟪⟫ cV _) _)
              (IdPush {X′ = X′} {A = A} _ _ _ _ _ _ _) =
  ct-⟪⟫ (ct-⟪⟫ cV (canonC-unseal X′)) (canonC-mkId A)
canon-step uq tp (ct-· cL cM)  (ξ-·-l st)   =
  ct-· (canon-step uq tp cL st) cM
canon-step uq tp (ct-· cV cM)  (ξ-·-r _ st) =
  ct-· cV (canon-step uq tp cM st)
canon-step uq tp (ct-·[] cL)   (ξ-·[] st)   =
  ct-·[] (canon-step uq tp cL st)
canon-step {Δ = Δ} uq tp (ct-Λ cN) (ξ-Λ st) =
  ct-Λ (canon-step (unique-underΛ {Γ = Δ} uq) tp cN st)
canon-step uq tp (ct-⟪⟫ cM cc) (ξ-⟪⟫ ri st) =
  ct-⟪⟫ (canon-step (interior-unique uq ri) tp cM st) cc

canon-steps : ∀ {Δ} → Unique (names Δ) → CanonTyPeelR
  → CanonTm M → Δ ⊢ M -→* M′ → CanonTm M′
canon-steps uq tp cM done          = cM
canon-steps uq tp cM (st then sts) =
  canon-steps uq tp (canon-step uq tp cM st) sts

------------------------------------------------------------------------
-- 9.  SOURCES — plain System F terms are canonical, vacuously
------------------------------------------------------------------------

-- Compilation from plain System F introduces no boundary at all: every
-- wrapper in a reachable term was minted by a reduction step, so §8 is
-- the whole story.  Stated for the record.
data Plain : Term → Set where
  pl-var   : ∀ {x} → Plain (` x)
  pl-lit   : ∀ {n} → Plain ($ n)
  pl-true  : Plain `true
  pl-false : Plain `false
  pl-ƛ     : Plain N → Plain (ƛ A ∙ N)
  pl-·     : Plain L → Plain M → Plain (L · M)
  pl-Λ     : Plain N → Plain (Λ N)
  pl-·[]   : Plain L → Plain (L ·[ B , A ])

canon-source : Plain M → CanonTm M
canon-source pl-var        = ct-var
canon-source pl-lit        = ct-lit
canon-source pl-true       = ct-true
canon-source pl-false      = ct-false
canon-source (pl-ƛ pN)     = ct-ƛ (canon-source pN)
canon-source (pl-· pL pM)  = ct-· (canon-source pL) (canon-source pM)
canon-source (pl-Λ pN)     = ct-Λ (canon-source pN)
canon-source (pl-·[] pL)   = ct-·[] (canon-source pL)

------------------------------------------------------------------------
-- 10.  The mint lemmas, on the ground
------------------------------------------------------------------------

-- TyBeta's conversion at a function type is the ↦-tree whose domain is
-- the DUAL family.
_ : reveal 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

_ : CanonC (reveal 0 (` 0 ⇒ ` 0))
_ = canonC-reveal 0 (` 0 ⇒ ` 0)

-- The wrapper frame-exact Beta mints at a crossed `Λ` is name-free.
_ : ∀ {W A} → CanonTm W → CanonTm (crossΛᴹ W A)
_ = λ cW → ct-⟪⟫ (canon-renᴹ² (ren² idᵗ suc) cW) (canonC-mkId _)

-- A TWO-BINDER tree — `seal` leaves at two different names — is outside
-- the family, though (unlike under the retired polarity index) it is
-- perfectly TYPEABLE: it is what TyPeelR mints, and the frames, not a
-- global index, are what keep the two binders apart.
¬canonC-two-binders : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-two-binders = ¬canonC-seal↦seal

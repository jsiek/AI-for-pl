module strong-rep-store.proof.Canonicity where

-- File Charter:
--   * THE CANONICITY INVARIANT — the BINDER-NAME reading.  Every
--     conversion reduction writes on a wrapper is a subtree, a
--     re-spelling, or a mint of `reveal X B`, `conceal X B`, `mkId A`
--     or `unseal X`.  §1 the family `CanonAt`/`CanonC`/`AllId`;
--     §2 MINT; §3 DECOMPOSE; §4 RENAME; §5 RE-SPELL (the family one
--     universe up, `CanonAtᴿ`); §6 lifting to terms; §7 substitution;
--     §8 `canon-step`, the invariant, with `CanonTyPeelR` REFUTED;
--     §9 sources; §10 the mint lemmas on the ground.
--   * WHAT THE FAMILY SAYS is the NAME, not a polarity shape: every
--     non-identity leaf cites the SAME binder, shifted under each
--     `` `∀ `` as `reveal`/`conceal` shift it.
--   * `canon-step` takes `Unique (names Δ)`, because the way back up
--     from a `SameConv` needs the target name map to be a FUNCTION.
-- Commentary: Commentary.md § proof/Canonicity.agda

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
open import strong-rep-store.proof.TermSubst
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

-- The term-level reading: a wrapper's conversion cites SOME single
-- binder — existential, and single-name (see §8's `¬CanonTyPeelR`).
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
  canonAt-reveal X (` Y) | yes refl = ca-unseal
  canonAt-reveal X (` Y) | no  _    = ca-id
  canonAt-reveal X `ℕ      = ca-id
  canonAt-reveal X `𝔹      = ca-id
  canonAt-reveal X (A ⇒ B) =
    ca-fun (canonAt-conceal X A) (canonAt-reveal X B)
  canonAt-reveal X (`∀ A)  = ca-all (canonAt-reveal (suc X) A)

  canonAt-conceal : (X : ℕ) (B : Ty) → CanonAt X (conceal X B)
  canonAt-conceal X (` Y) with X ≟ Y
  canonAt-conceal X (` Y) | yes refl = ca-seal
  canonAt-conceal X (` Y) | no  _    = ca-id
  canonAt-conceal X `ℕ      = ca-id
  canonAt-conceal X `𝔹      = ca-id
  canonAt-conceal X (A ⇒ B) =
    ca-fun (canonAt-reveal X A) (canonAt-conceal X B)
  canonAt-conceal X (`∀ A)  = ca-all (canonAt-conceal (suc X) A)

-- (b) The identity at an arbitrary type — the conversion `CancelR` mints.
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

-- IdPush's mint: the pushed `unseal` at the name the rule carries.
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

-- THE FAMILY ONE UNIVERSE UP: canonical at a REPRESENTATION VARIABLE,
-- which `_⊩_~_` shifts under a `` `∀ `` exactly as `CanonAt` shifts
-- the ordinary name.  Commentary.md § proof/Canonicity.agda / §5
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

shiftReps-∋ : η ∋ˡ X := α → shiftReps η ∋ˡ X := suc α
shiftReps-∋ here      = here
shiftReps-∋ (there d) = there (shiftReps-∋ d)

shiftReps-∋⁻ : (η : TyCtx) → shiftReps η ∋ˡ X := β
  → ∃[ α ] ((β ≡ suc α) × (η ∋ˡ X := α))
shiftReps-∋⁻ (γ ∷ η) here      = γ , refl , here
shiftReps-∋⁻ (γ ∷ η) (there d) with shiftReps-∋⁻ η d
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
canon-rep (sameᶜ-fun a b) (ca-fun cs ct)
  | inj₁ ar          | inj₁ au          = inj₁ (ai-fun ar au)
canon-rep (sameᶜ-fun a b) (ca-fun cs ct)
  | inj₁ ar          | inj₂ (α , d , c) =
  inj₂ (α , d , car-fun (allIdᴿ-canon ar α) c)
canon-rep (sameᶜ-fun a b) (ca-fun cs ct)
  | inj₂ (α , d , c) | inj₁ au          =
  inj₂ (α , d , car-fun c (allIdᴿ-canon au α))
canon-rep (sameᶜ-fun a b) (ca-fun cs ct)
  | inj₂ (α , d , c) | inj₂ (β , d′ , c′)
  with ∋ˡ-det d d′
canon-rep (sameᶜ-fun a b) (ca-fun cs ct)
  | inj₂ (α , d , c) | inj₂ (β , d′ , c′) | refl =
  inj₂ (α , d , car-fun c c′)
canon-rep {η = η} (sameᶜ-all a) (ca-all cs)
  with canon-rep a cs
canon-rep {η = η} (sameᶜ-all a) (ca-all cs)
  | inj₁ ar = inj₁ (ai-all ar)
canon-rep {η = η} (sameᶜ-all a) (ca-all cs)
  | inj₂ (α₀ , there d₀ , c)
  with shiftReps-∋⁻ η d₀
canon-rep {η = η} (sameᶜ-all a) (ca-all cs)
  | inj₂ (α₀ , there d₀ , c) | α , refl , d = inj₂ (α , d , car-all c)

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
canon-name uq (sameᶜ-fun a b) (car-fun cr cu)
  | inj₁ as          | inj₁ at          = inj₁ (ai-fun as at)
canon-name uq (sameᶜ-fun a b) (car-fun cr cu)
  | inj₁ as          | inj₂ (Y , d , c) =
  inj₂ (Y , d , ca-fun (allId-canon as Y) c)
canon-name uq (sameᶜ-fun a b) (car-fun cr cu)
  | inj₂ (Y , d , c) | inj₁ at          =
  inj₂ (Y , d , ca-fun c (allId-canon at Y))
canon-name uq (sameᶜ-fun a b) (car-fun cr cu)
  | inj₂ (Y , d , c) | inj₂ (Z , d′ , c′)
  with unique-lookup uq d d′
canon-name uq (sameᶜ-fun a b) (car-fun cr cu)
  | inj₂ (Y , d , c) | inj₂ (Z , d′ , c′) | refl =
  inj₂ (Y , d , ca-fun c c′)
canon-name {η′ = η′} uq (sameᶜ-all a) (car-all cr)
  with canon-name (unique∷ fresh-zero-shift (unique-shift uq)) a cr
canon-name {η′ = η′} uq (sameᶜ-all a) (car-all cr)
  | inj₁ as = inj₁ (ai-all as)
canon-name {η′ = η′} uq (sameᶜ-all a) (car-all cr)
  | inj₂ (suc Y₀ , there d₀ , c)
  with shiftReps-∋⁻ η′ d₀
canon-name {η′ = η′} uq (sameᶜ-all a) (car-all cr)
  | inj₂ (suc Y₀ , there d₀ , c) | α , refl , d = inj₂ (Y₀ , d , ca-all c)

-- THE RE-SPELLING.  `Peel` carries `SameConv Δᵈ s′ Δᶜ s`; the `Unique` its
-- first context needs is `dual-unique` at the rule's own two readings.
canonC-respell : Unique η′
  → ∃[ r ] ((η′ ⊩ s ~ r) × (η ⊩ t ~ r))
  → CanonC t → CanonC s
canonC-respell uq (r , p , q) (X , ct)
  with canon-rep q ct
canonC-respell uq (r , p , q) (X , ct) | inj₁ ar
  with canon-name uq p (allIdᴿ-canon ar 0)
canonC-respell uq (r , p , q) (X , ct) | inj₁ ar | inj₁ as =
  0 , allId-canon as 0
canonC-respell uq (r , p , q) (X , ct) | inj₁ ar | inj₂ (Y , d , c) = Y , c
canonC-respell uq (r , p , q) (X , ct) | inj₂ (α , d , c)
  with canon-name uq p c
canonC-respell uq (r , p , q) (X , ct) | inj₂ (α , d , c) | inj₁ as =
  0 , allId-canon as 0
canonC-respell uq (r , p , q) (X , ct)
  | inj₂ (α , d , c) | inj₂ (Y , d′ , c′) = Y , c′

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
-- component; §4 covers them.  A representation-only renaming leaves every
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
canon-renᴹ² ρ (ct-⟪⟫ cM cc) =
  ct-⟪⟫ (canon-renᴹ² ρ cM) (canonC-ren (ordinary ρ) cc)

canon-renᴹᴿ : (ρ : Renameᵗ) → CanonTm M → CanonTm (renᴹᴿ ρ M)
canon-renᴹᴿ ρ ct-var        = ct-var
canon-renᴹᴿ ρ ct-lit        = ct-lit
canon-renᴹᴿ ρ ct-true       = ct-true
canon-renᴹᴿ ρ ct-false      = ct-false
canon-renᴹᴿ ρ (ct-ƛ cN)     = ct-ƛ (canon-renᴹᴿ ρ cN)
canon-renᴹᴿ ρ (ct-· cL cM)  =
  ct-· (canon-renᴹᴿ ρ cL) (canon-renᴹᴿ ρ cM)
canon-renᴹᴿ ρ (ct-Λ cN)     = ct-Λ (canon-renᴹᴿ (extᵗ ρ) cN)
canon-renᴹᴿ ρ (ct-·[] cL)   = ct-·[] (canon-renᴹᴿ ρ cL)
canon-renᴹᴿ ρ (ct-⟪⟫ cM cc) = ct-⟪⟫ (canon-renᴹᴿ ρ cM) cc

canon-↑ : (δ : Alloc) → CanonTm M → CanonTm (↑ᴹ[ δ ] M)
canon-↑ none    cM = cM
canon-↑ (new R) cM = canon-renᴹᴿ suc cM

canon-renᴹ : (ρ : Renameᵗ) → CanonTm M → CanonTm (renᴹ ρ M)
canon-renᴹ ρ cM = canon-renᴹ² (ren² ρ ρ) cM

canon-wkᴹ : (n : ℕ) → CanonTm M → CanonTm (wkᴹ n M)
canon-wkᴹ n cM = canon-renᴹ (wkN n) cM

------------------------------------------------------------------------
-- 7.  Term substitution
------------------------------------------------------------------------

-- Boundaries are TERM-CLOSED, so no conversion is ever renamed by term
-- substitution.  The one new wrapper is the DUAL frame-exact Beta mints
-- at each crossed Λ, whose conversion is `mkId` — name-free.
-- Commentary.md § proof/Canonicity.agda / §7
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

-- One case per rule; the rule-by-rule story is
-- Commentary.md § proof/Canonicity.agda / §8.  The ONE case that is
-- not unconditional is TyPeelR's mint, which puts leaves at slot 0
-- ALONGSIDE the conversion's own, so the result cites TWO binders —
-- hence the hypothesis `CanonTyPeelR` below, which is REFUTED.

-- WHAT TYPEELR'S MINT OWES THE FAMILY, as a statement.
CanonTyPeelR : Set
CanonTyPeelR = ∀ {s : Conv} → CanonC (`∀ s) → CanonC (instReveal 0 s)

-- IT FAILS on `` `∀ (id (` 0) ↦ seal 1) `` — a polymorphic ARGUMENT
-- that crossed a Peel.  The mint TYPES; it is the SINGLE-BINDER
-- reading that it leaves.
-- Commentary.md § proof/Canonicity.agda / §8
canonC-∀conv : CanonC (`∀ (id (` 0) ↦ seal 1))
canonC-∀conv = 0 , ca-all (ca-fun ca-id ca-seal)

_ : instReveal 0 (id (` 0) ↦ seal 1) ≡ seal 0 ↦ seal 1
_ = refl

¬canonC-seal↦seal : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-seal↦seal (X , ca-fun ca-seal ())

¬CanonTyPeelR : ¬ CanonTyPeelR
¬CanonTyPeelR tp = ¬canonC-seal↦seal (tp canonC-∀conv)

canon-step : ∀ {Δ M M′ δ} → Unique (names Δ) → CanonTyPeelR
  → CanonTm M → Δ ⊢ M -→ M′ ∣ δ → CanonTm M′
canon-step uq tp (ct-·[] (ct-Λ cN)) (TyBeta {B = B} _ _) =
  ct-⟪⟫ cN (canonC-reveal 0 B)
canon-step uq tp (ct-· (ct-ƛ cN) cW) (Beta _) = canon-subst cN cW
canon-step uq tp (ct-· (ct-⟪⟫ cV cst) cW) (Peel _ _ rc ri rd sc) =
  ct-⟪⟫ (ct-· cV (ct-⟪⟫ cW
                        (canonC-respell (dual-unique uq ri rd) sc
                                        (canonC-fun-dom cst))))
        (canonC-fun-cod cst)
canon-step uq tp (ct-·[] (ct-⟪⟫ (ct-Λ cN) cs)) (TyPeelR-Λ _ _ _ _) =
  ct-⟪⟫ cN (tp cs)
canon-step uq tp (ct-·[] (ct-⟪⟫ (ct-⟪⟫ cW cs′) cs))
              (TyPeelR-⟪⟫ {Δ′ᶜ = Δ′ᶜ} {Δ″ᶜ = Δ″ᶜ} {Θ′ = Θ′}
                _ _ _ _ ri⁺ r″ sc _ _ _) =
  ct-⟪⟫ (ct-·[] (ct-⟪⟫ (canon-renᴹᴿ suc cW)
                       (canonC-respell
                         (conversion-unique
                           (interior-unique (unique-shift uq) ri⁺) r″)
                         (sameConv-∀ {Γ = Δ″ᶜ}
                           {Γ′ = renNameCtx suc Δ″ᶜ Δ′ᶜ} sc)
                         cs′)))
        (tp cs)
canon-step uq tp (ct-⟪⟫ (ct-⟪⟫ cV _) _)
              (CancelR {A′ = A′} _ _ _ _ _ _) =
  ct-⟪⟫ cV (canonC-mkId A′)
canon-step uq tp (ct-⟪⟫ _ _) (Drop$ _)     = ct-lit
canon-step uq tp (ct-⟪⟫ _ _) Drop-true     = ct-true
canon-step uq tp (ct-⟪⟫ _ _) Drop-false    = ct-false
canon-step uq tp (ct-⟪⟫ (ct-⟪⟫ cV _) _)
              (IdPush {X′ = X′} _ _ _ _ _) =
  ct-⟪⟫ cV (canonC-unseal X′)
canon-step uq tp (ct-· cL cM) (ξ-·-l {δ = δ} st) =
  ct-· (canon-step uq tp cL st) (canon-↑ δ cM)
canon-step uq tp (ct-· cV cM) (ξ-·-r {δ = δ} _ st) =
  ct-· (canon-↑ δ cV) (canon-step uq tp cM st)
canon-step uq tp (ct-·[] cL)   (ξ-·[] st)   =
  ct-·[] (canon-step uq tp cL st)
canon-step uq tp (ct-⟪⟫ cM cc) (ξ-⟪⟫ ri st) =
  ct-⟪⟫ (canon-step (interior-unique uq ri) tp cM st) cc

canon-steps : ∀ {Δ M M′} → Unique (names Δ) → CanonTyPeelR
  → CanonTm M → Δ ⊢ M -→* M′ → CanonTm M′
canon-steps uq tp cM done = cM
canon-steps uq tp cM (_then_ {δ = none} st sts) =
  canon-steps uq tp (canon-step uq tp cM st) sts
canon-steps uq tp cM (_then_ {δ = new R} st sts) =
  canon-steps (unique-shift uq) tp (canon-step uq tp cM st) sts

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
_ = λ cW →
  ct-⟪⟫ (canon-renᴹ² (ren² idᵗ suc) cW) (canonC-mkId _)

-- A TWO-BINDER tree is outside the family, though perfectly TYPEABLE:
-- the FRAMES, not a global index, keep the two binders apart.
¬canonC-two-binders : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-two-binders = ¬canonC-seal↦seal

module strong.proof.Canonicity where

-- THE CANONICITY INVARIANT — Decision "Option A" (the polarity ruling).
--
-- Every conversion that reduction ever writes on a wrapper is a member of
-- the CANONICAL FAMILY: it is (a subtree of) `unsealAt X B`, `sealAt X B`,
-- or `idc A`.  This file states that family as an inductive predicate,
-- proves the three closure facts the rules need (MINT / DECOMPOSE /
-- RENAME), lifts it to terms, and proves it PRESERVED BY REDUCTION
-- (`canon-step`).  The payoff is §5: a canonical conversion is
-- SINGLE-POLARITY — it types at exactly the polarity its family dictates,
-- unless it is the identity, which types at both.
--
-- TWO predicates, because two different things are true.
--
--   `Canon p c`      — the POLARITY SHAPE.  `unseal` leaves sit at ↑ˢ
--                      positions, `seal` leaves at ↓ˢ positions, where
--                      "position" flips at every ↦-domain.  This is the
--                      "no mixed tree" property, and it is exactly what
--                      the typing judgment already forces (`typed→canon`).
--
--   `CanonAt p X c`  — the same, but TRACKING THE NAME: every non-identity
--                      leaf names the SAME owner X, shifted under each `∀
--                      exactly as `unsealAt`/`sealAt` shift it.  This is
--                      the tight reading of "subtree of unsealAt X B", and
--                      it is what `canon-step` maintains.
--
-- `CanonAt` refines `Canon` (`canonAt→canon`); the term-level invariant
-- uses `CanonAt` with the name and polarity existentially quantified
-- (`CanonC`), because a term's wrappers name different owners.

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
    p q : Pol
    X : ℕ
    c s t : Conv
    L M M′ N W : Term
    σ : ℕ → Term

------------------------------------------------------------------------
-- 1.  The canonical family
------------------------------------------------------------------------

-- `Canon p c` — c read at polarity p: reveals at ↑ˢ, conceals at ↓ˢ, the
-- polarity flipping on ↦-domains exactly as `conv-fun` flips it.
data Canon : Pol → Conv → Set where
  can-id     : Canon p (id A)
  can-unseal : Canon ↑ˢ (unseal X)
  can-seal   : Canon ↓ˢ (seal X)
  can-fun    : Canon (flip p) s → Canon p t → Canon p (s ↦ t)
  can-all    : Canon p s → Canon p (`∀ s)

-- `CanonAt p X c` — the same, with the owner NAME tracked.  A `∀ pushes a
-- binder in front of the leaves, so the name it tracks is `suc X`, which
-- is precisely the shift `unsealAt`/`sealAt` perform on the `∀ case.
data CanonAt : Pol → ℕ → Conv → Set where
  ca-id     : CanonAt p X (id A)
  ca-unseal : CanonAt ↑ˢ X (unseal X)
  ca-seal   : CanonAt ↓ˢ X (seal X)
  ca-fun    : CanonAt (flip p) X s → CanonAt p X t
            → CanonAt p X (s ↦ t)
  ca-all    : CanonAt p (suc X) s → CanonAt p X (`∀ s)

canonAt→canon : CanonAt p X c → Canon p c
canonAt→canon ca-id          = can-id
canonAt→canon ca-unseal      = can-unseal
canonAt→canon ca-seal        = can-seal
canonAt→canon (ca-fun cs ct) =
  can-fun (canonAt→canon cs) (canonAt→canon ct)
canonAt→canon (ca-all cs)    = can-all (canonAt→canon cs)

-- The term-level reading: a wrapper's conversion is canonical for SOME
-- polarity.  It is the POLARITY shape alone, not the tight single-name
-- reading `CanonAt`, and it has to be: TyPeelR's minted face
-- `unsealAtᶜ 0 s` reads TWO owners in one wrapper — the face's own, and
-- the one the instantiation just bound at slot 0 — so no single name
-- tracks it.  (`CanonAt` is still what the MINT lemmas produce, and
-- `canonAt→canon` is how they land here.)
CanonC : Conv → Set
CanonC c = ∃[ p ] Canon p c

------------------------------------------------------------------------
-- 2.  MINT — the faces the rules write are canonical
------------------------------------------------------------------------

-- (a) TyBeta's face and its dual, by mutual induction on the face type —
-- the same recursion `unsealAt`/`sealAt` are defined by.
mutual
  canonAt-unsealAt : (X : ℕ) (B : Ty) → CanonAt ↑ˢ X (unsealAt X B)
  canonAt-unsealAt X (` Y) with X ≟ℕ Y
  ... | yes refl = ca-unseal
  ... | no  _    = ca-id
  canonAt-unsealAt X `ℕ      = ca-id
  canonAt-unsealAt X `𝔹      = ca-id
  canonAt-unsealAt X (A ⇒ B) =
    ca-fun (canonAt-sealAt X A) (canonAt-unsealAt X B)
  canonAt-unsealAt X (`∀ A)  = ca-all (canonAt-unsealAt (suc X) A)

  canonAt-sealAt : (X : ℕ) (B : Ty) → CanonAt ↓ˢ X (sealAt X B)
  canonAt-sealAt X (` Y) with X ≟ℕ Y
  ... | yes refl = ca-seal
  ... | no  _    = ca-id
  canonAt-sealAt X `ℕ      = ca-id
  canonAt-sealAt X `𝔹      = ca-id
  canonAt-sealAt X (A ⇒ B) =
    ca-fun (canonAt-unsealAt X A) (canonAt-sealAt X B)
  canonAt-sealAt X (`∀ A)  = ca-all (canonAt-sealAt (suc X) A)

-- (b) The identity at an arbitrary type — CancelR's and IdPush's residue.
-- It is canonical at EVERY polarity and EVERY name: the leaves of `idc`
-- are all `id`, which is the family's ambipolar leaf.
canonAt-idc : (p : Pol) (X : ℕ) (A : Ty) → CanonAt p X (idc A)
canonAt-idc p X (` Y)   = ca-id
canonAt-idc p X `ℕ      = ca-id
canonAt-idc p X `𝔹      = ca-id
canonAt-idc p X (A ⇒ B) =
  ca-fun (canonAt-idc (flip p) X A) (canonAt-idc p X B)
canonAt-idc p X (`∀ A)  = ca-all (canonAt-idc p (suc X) A)

canon-unsealAt : (X : ℕ) (B : Ty) → Canon ↑ˢ (unsealAt X B)
canon-unsealAt X B = canonAt→canon (canonAt-unsealAt X B)

canon-sealAt : (X : ℕ) (B : Ty) → Canon ↓ˢ (sealAt X B)
canon-sealAt X B = canonAt→canon (canonAt-sealAt X B)

canonC-unsealAt : (X : ℕ) (B : Ty) → CanonC (unsealAt X B)
canonC-unsealAt X B = ↑ˢ , canon-unsealAt X B

canonC-sealAt : (X : ℕ) (B : Ty) → CanonC (sealAt X B)
canonC-sealAt X B = ↓ˢ , canon-sealAt X B

canonC-idc : (A : Ty) → CanonC (idc A)
canonC-idc A = ↑ˢ , canonAt→canon (canonAt-idc ↑ˢ 0 A)

-- IdPush's other mint: the pushed `unseal` at the name the id-face wrote.
canonC-unseal : (X : ℕ) → CanonC (unseal X)
canonC-unseal X = ↑ˢ , can-unseal

-- (c) TYPEELR's mint — `unsealAtᶜ`, the leaf-wise instantiation of the
-- ∀-face at the owner the rule binds.  THE POLARITIES LINE UP ONLY ONE
-- WAY: an inserted `unseal 0` sits where the face runs COVARIANTLY and an
-- inserted `seal 0` where it runs CONTRAVARIANTLY, so the mint stays in
-- the family exactly when the ∀-face is a REVEAL (`↑ˢ`).  Under a
-- CONCEAL (`↓ˢ`) face the two are swapped and the result is a MIXED tree
-- — `¬CanonTyPeelR`, §8.
mutual
  canon-unsealAtᶜ : (n : ℕ) → Canon ↑ˢ c → Canon ↑ˢ (unsealAtᶜ n c)
  canon-unsealAtᶜ n (can-id {A = A})   = canon-unsealAt n A
  canon-unsealAtᶜ n can-unseal         = can-unseal
  canon-unsealAtᶜ n (can-fun cs ct)    =
    can-fun (canon-sealAtᶜ n cs) (canon-unsealAtᶜ n ct)
  canon-unsealAtᶜ n (can-all cs)       = can-all (canon-unsealAtᶜ (suc n) cs)

  canon-sealAtᶜ : (n : ℕ) → Canon ↓ˢ c → Canon ↓ˢ (sealAtᶜ n c)
  canon-sealAtᶜ n (can-id {A = A})     = canon-sealAt n A
  canon-sealAtᶜ n can-seal             = can-seal
  canon-sealAtᶜ n (can-fun cs ct)      =
    can-fun (canon-unsealAtᶜ n cs) (canon-sealAtᶜ n ct)
  canon-sealAtᶜ n (can-all cs)         = can-all (canon-sealAtᶜ (suc n) cs)

------------------------------------------------------------------------
-- 3.  DECOMPOSE — the subtree readings the crossing rules perform
------------------------------------------------------------------------

-- Peel reads `s ↦ t` apart; note the DOMAIN comes back at the FLIPPED
-- polarity and the SAME owner, which is exactly the crossing argument's
-- face.
canonC-fun-dom : CanonC (s ↦ t) → CanonC s
canonC-fun-dom (p , can-fun cs ct) = flip p , cs

canonC-fun-cod : CanonC (s ↦ t) → CanonC t
canonC-fun-cod (p , can-fun cs ct) = p , ct

-- TyPeelR reads `∀ s` apart — and then MINTS on the body (`unsealAtᶜ 0`,
-- §2c): the slot the `` `∀ `` left abstract is now the owner the rule
-- binds, so the face's identity leaves at that slot become the
-- instantiation.  The polarity is unchanged by the decomposition.
canonC-all : CanonC (`∀ s) → CanonC s
canonC-all (p , can-all cs) = p , cs

------------------------------------------------------------------------
-- 4.  RENAME — canonicity survives a type-context renaming
------------------------------------------------------------------------

-- `renᴹ` (hence `wkᴹ`, used by Peel and TyPeelR on the term they move)
-- renames the conversions it passes.  The name moves with the renaming.
canonAt-ren : (ρ : Renameᵗ) → CanonAt p X c → CanonAt p (ρ X) (renᶜ ρ c)
canonAt-ren ρ ca-id          = ca-id
canonAt-ren ρ ca-unseal      = ca-unseal
canonAt-ren ρ ca-seal        = ca-seal
canonAt-ren ρ (ca-fun cs ct) =
  ca-fun (canonAt-ren ρ cs) (canonAt-ren ρ ct)
canonAt-ren ρ (ca-all cs)    = ca-all (canonAt-ren (extᵗ ρ) cs)

canon-ren : (ρ : Renameᵗ) → Canon p c → Canon p (renᶜ ρ c)
canon-ren ρ can-id          = can-id
canon-ren ρ can-unseal      = can-unseal
canon-ren ρ can-seal        = can-seal
canon-ren ρ (can-fun cs ct) = can-fun (canon-ren ρ cs) (canon-ren ρ ct)
canon-ren ρ (can-all cs)    = can-all (canon-ren (extᵗ ρ) cs)

canonC-ren : (ρ : Renameᵗ) → CanonC c → CanonC (renᶜ ρ c)
canonC-ren ρ (p , cc) = p , canon-ren ρ cc

------------------------------------------------------------------------
-- 5.  THE POLARITY PAYOFF
------------------------------------------------------------------------

-- The identity-only conversions — the family's ambipolar members.  These
-- are exactly the `idc A` shapes plus the sub-identities the mint lemmas
-- produce at a non-matching variable.
data IdOnly : Conv → Set where
  io-id  : IdOnly (id A)
  io-fun : IdOnly s → IdOnly t → IdOnly (s ↦ t)
  io-all : IdOnly s → IdOnly (`∀ s)

idOnly-idc : (A : Ty) → IdOnly (idc A)
idOnly-idc (` X)   = io-id
idOnly-idc `ℕ      = io-id
idOnly-idc `𝔹      = io-id
idOnly-idc (A ⇒ B) = io-fun (idOnly-idc A) (idOnly-idc B)
idOnly-idc (`∀ A)  = io-all (idOnly-idc A)

flip-inj : flip p ≡ flip q → p ≡ q
flip-inj {↑ˢ} {↑ˢ} refl = refl
flip-inj {↓ˢ} {↓ˢ} refl = refl

-- THE SINGLE-POLARITY LAW.  If a canonical conversion is typeable at all,
-- it is typeable at the polarity of ITS OWN family — the only escape is
-- the identity, which really does type at both (conv-id/conv-idv are
-- polymorphic in p).  This is the honest form of "CanU types at ↑ˢ, CanS
-- at ↓ˢ, idc at both": the `IdOnly` disjunct is not slack, it is the
-- ambipolar case, and it cannot be dropped.
canon-pol : Canon p c → Δ ⊢ c ∶ A ⇝ B ∙ q → IdOnly c ⊎ p ≡ q
canon-pol can-id      ⊢c              = inj₁ io-id
canon-pol can-unseal  (conv-unseal _) = inj₂ refl
canon-pol can-seal    (conv-seal _)   = inj₂ refl
canon-pol (can-all cs) (conv-all ⊢s)  with canon-pol cs ⊢s
... | inj₁ io = inj₁ (io-all io)
... | inj₂ eq = inj₂ eq
canon-pol (can-fun cs ct) (conv-fun ⊢s ⊢t) with canon-pol ct ⊢t
... | inj₂ eq  = inj₂ eq
... | inj₁ iot with canon-pol cs ⊢s
...   | inj₂ eq  = inj₂ (flip-inj eq)
...   | inj₁ ios = inj₁ (io-fun ios iot)

canonAt-pol : CanonAt p X c → Δ ⊢ c ∶ A ⇝ B ∙ q → IdOnly c ⊎ p ≡ q
canonAt-pol cc ⊢c = canon-pol (canonAt→canon cc) ⊢c

-- THE CONVERSE, and the reason the invariant costs nothing: the typing
-- judgment ALREADY forces the polarity shape.  A mixed tree — a `seal` at
-- a ↑ˢ position, an `unseal` at a ↓ˢ one — is not merely non-canonical,
-- it is UNTYPEABLE.  So `Canon` is not an extra hypothesis on typed
-- terms; `CanonAt` is the part that carries real information (the owner).
typed→canon : Δ ⊢ c ∶ A ⇝ B ∙ p → Canon p c
typed→canon (conv-id _)      = can-id
typed→canon (conv-idv _)     = can-id
typed→canon (conv-unseal _)  = can-unseal
typed→canon (conv-seal _)    = can-seal
typed→canon (conv-fun ⊢s ⊢t) =
  can-fun (typed→canon ⊢s) (typed→canon ⊢t)
typed→canon (conv-all ⊢s)    = can-all (typed→canon ⊢s)

-- Consequence: a non-identity conversion has ONE polarity, on any two
-- type contexts and at any two face pairs.  Single-polarity is a property
-- of the conversion alone.
pol-unique : ∀ {A′ B′} → ¬ IdOnly c
  → Δ  ⊢ c ∶ A  ⇝ B  ∙ p
  → Δ′ ⊢ c ∶ A′ ⇝ B′ ∙ q
    ---------------------
  → p ≡ q
pol-unique ¬io ⊢c₁ ⊢c₂ with canon-pol (typed→canon ⊢c₁) ⊢c₂
... | inj₁ io = ⊥-elim (¬io io)
... | inj₂ eq = eq

-- The identity really is ambipolar, so `¬ IdOnly` above is necessary.
id-both-pols : Base A → (Δ ⊢ id A ∶ A ⇝ A ∙ ↑ˢ) × (Δ ⊢ id A ∶ A ⇝ A ∙ ↓ˢ)
id-both-pols b = conv-id b , conv-id b

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
--            takes the domain `s` at the FLIPPED polarity.
--   TyPeelR  DECOMPOSES `∀ s`, RENAMES the moved value (`wkᴹ 1`), and
--            MINTS `unsealAtᶜ 0 s` on the body — the ONE case that is not
--            unconditional, because the mint is in the family only at a
--            REVEAL face (`canon-unsealAtᶜ`); hence the hypothesis
--            `CanonTyPeelR` below, whose general form is REFUTED.
--   CancelR  MINTS `idc A` at the looked-up rep — a LEAF of the family
--            (`idOnly-idc`), canonical at every polarity and name.
--   IdPush   MINTS BOTH faces: the pushed `unseal X` (canonical at ↑ˢ,
--            owner X) and the residue `idc A`.  The old inner face was
--            `id (` X)`, an ambipolar leaf that carries no owner, so the
--            name comes from the face's own payload — which typing shows
--            is the right one (proof/IdLayer.agda, `idpush-name`).
--   Drop$    contracts to `$ n`; no wrappers at all.
--   ξ-*      structural.
-- WHAT TYPEELR'S MINT OWES THE FAMILY, as a statement.
CanonTyPeelR : Set
CanonTyPeelR = ∀ {s : Conv} → CanonC (`∀ s) → CanonC (unsealAtᶜ 0 s)

-- It HOLDS at a reveal face …
canonC-unsealAtᶜ-↑ : Canon ↑ˢ s → CanonC (unsealAtᶜ 0 s)
canonC-unsealAtᶜ-↑ cs = ↑ˢ , canon-unsealAtᶜ 0 cs

-- … and FAILS at a conceal face: the ∀-face `∀ (id (` 0) ↦ seal 1)` — a
-- polymorphic ARGUMENT that crossed a Peel, `sealAt 0 (∀Y. Y ⇒ X)` — is
-- canonical at ↓ˢ, and its mint `seal 0 ↦ seal 1` is a MIXED tree: the
-- inserted `seal 0` sits contravariantly (wanting ↑ˢ) under a `seal 1`
-- that sits covariantly (wanting ↓ˢ).  By `typed→canon` the mint is
-- therefore untypeable at either polarity — which is exactly
-- proof/PreserveObstruct §2, at the level of the family.
canonC-↓ˢ-∀face : CanonC (`∀ (id (` 0) ↦ seal 1))
canonC-↓ˢ-∀face = ↓ˢ , can-all (can-fun can-id can-seal)

_ : unsealAtᶜ 0 (id (` 0) ↦ seal 1) ≡ seal 0 ↦ seal 1
_ = refl

¬canonC-seal↦seal : ¬ CanonC (seal 0 ↦ seal 1)
¬canonC-seal↦seal (↑ˢ , can-fun cs ())
¬canonC-seal↦seal (↓ˢ , can-fun () ct)

¬CanonTyPeelR : ¬ CanonTyPeelR
¬CanonTyPeelR tp = ¬canonC-seal↦seal (tp canonC-↓ˢ-∀face)

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
  ct-⟪⟫ (ct-⟪⟫ (ct-⟪⟫ ct-lit (↓ˢ , can-seal))
               (↑ˢ , can-id))
        (canonC-unseal 0)

-- …and the invariant survives the whole IdPush ⨟ Cancel ⨟ Drop$ ⨟ Drop$
-- run, which is what `canon-step` is for.  (Neither run takes a TyPeelR
-- step, so the hypothesis is carried but never consumed.)
canonTm-T₆-run : CanonTyPeelR → CanonTm ($ 7)
canonTm-T₆-run tp = canon-steps tp canonTm-T₆ run-T₆

canonTm-cancelTm : CanonTm cancelTm
canonTm-cancelTm =
  ct-⟪⟫ (ct-⟪⟫ ct-lit (↓ˢ , can-seal)) (canonC-unseal 0)

canonTm-cancelTm-run : CanonTyPeelR → CanonTm ($ 7)
canonTm-cancelTm-run tp = canon-steps tp canonTm-cancelTm run-cancelTm

-- The mint lemmas, on the ground: TyBeta's face at a function type is the
-- ↦-tree whose domain is the DUAL family.
_ : unsealAt 0 (` 0 ⇒ ` 0) ≡ seal 0 ↦ unseal 0
_ = refl

_ : CanonC (unsealAt 0 (` 0 ⇒ ` 0))
_ = canonC-unsealAt 0 (` 0 ⇒ ` 0)

-- A MIXED tree — a `seal` in the codomain of a reveal face — is outside
-- the family, and (by `typed→canon`) untypeable at either polarity.
¬canon-mixed : ¬ Canon ↑ˢ (seal 0 ↦ seal 0)
¬canon-mixed (can-fun _ ())

¬typed-mixed : ∀ {A B} → ¬ (Δ ⊢ seal 0 ↦ seal 0 ∶ A ⇝ B ∙ ↑ˢ)
¬typed-mixed ⊢c = ¬canon-mixed (typed→canon ⊢c)

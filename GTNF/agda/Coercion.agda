module Coercion where

-- File Charter:
--   * THE COERCIONS OF GTNF (GTNF/design.md §3), the second sort of
--     run-time mediation, kept apart from νF's conversions
--     (Conversion.agda): a coercion never contains a conversion and a
--     conversion never contains a coercion.  §1 `Label` and the syntax;
--     §2 the consistency MODES and mode environments; §3 the side
--     predicates (`GroundNV`, `NonVar`, `NonStar`, `_∈ᵗ_`, `GenSafe`,
--     `InertC`); §4 `srcᵖ`/`trgᵖ`; §5 renaming `renᵖ` and closing at ★
--     `closeᵖ` (design.md's `p[★/X]`); §6 the typing judgement
--     `Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B`.
--   * DEFINITIONS ONLY.  The decision procedures (`coercionTy?`,
--     `inertC?`, ...) are TypeCheck.agda §11.
--   * DE BRUIJN.  `∀ᵖ`, `instᵖ` and `genᵖ` bind a type variable exactly
--     as a term-level `Λ` does: the body is read on `underΛ Δ` (index 0
--     is the bound name, over an abstract representation variable), and
--     the body's mode environment gets the binder's mode at its head.
--     A mode environment is a list PARALLEL TO `names Δ`.
--   * NAMES (design.md → Agda).  Coercion constructors carry a `ᵖ`
--     suffix where the design's spelling is already taken by a type
--     (`_⇒_`, `` `∀ ``), a conversion (`id`, `_↦_`, `` `∀ ``) or a
--     boundary operation (`inst`):
--       id(A)        idᵖ A          G!           G !
--       G?ℓ          G ？ ℓ         p → q        p ↦ᵖ q
--       ∀X. p        ∀ᵖ p           inst X. p    instᵖ p
--       gen X. p     genᵖ p         p ; G!       p ︔ G !
--       G?ℓ ; p      G ？ ℓ ︔ p
--       bot-elim     bot-elim       bot-intro ℓ  bot-intro ℓ
--     Modes are GTSFImp's `Var∼` constructors verbatim (`X∼X`, `X∼★`,
--     `★∼X`, `★∼X∼★`), with `flipᵐ` and the list-shaped `flipEnv`.
--   * TWO DE BRUIJN READINGS OF THE DESIGN.  (1) `instᵖ p : ∀A ⟹ B`
--     types `p : A ⟹ ⇑ᵗ B` (GTSFImp's `instᵐ μ ⊢ A ∼ ⇑ᵗ B`), and
--     `genᵖ p : A ⟹ ∀B` types `p : ⇑ᵗ A ⟹ B`; design.md's "Δ ⊢ B" with
--     X ∉ B is the shift.  (2) design.md's side condition `B ≠ ★` is
--     the constructor predicate `NonStar B` (GTSFImp's `NonStar`), so
--     that it is decidable without a negation.
--   * TAGS ON NAMES.  `(` X) !` and `(` X) ？ ℓ` are their own typing
--     rules, gated by the mode of X (design.md §3's table); every other
--     ground type is a `GroundNV`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Ctx

------------------------------------------------------------------------
-- 1. Syntax
------------------------------------------------------------------------

Label : Set
Label = ℕ

infixr 7 _↦ᵖ_
infix  6 _︔_! _？_︔_
infix  9 _!
infix  9 _？_
infix  8 ∀ᵖ_ instᵖ_ genᵖ_

data Coercion : Set where
  idᵖ       : Ty → Coercion                -- id(A)
  _!        : Ty → Coercion                -- G!      tag into ★
  _？_      : Ty → Label → Coercion        -- G?ℓ     check a tag
  _↦ᵖ_      : Coercion → Coercion → Coercion   -- p → q
  ∀ᵖ_       : Coercion → Coercion          -- ∀X. p
  instᵖ_    : Coercion → Coercion          -- inst X. p
  genᵖ_     : Coercion → Coercion          -- gen X. p
  -- EVIDENCE-SHAPED SEQUENCING (design.md D20): only the two forms that
  -- compilation produces, `⟦c !⟧ = ⟦c⟧ ; G!` and `⟦？ c⟧ = G?ℓ ; ⟦c⟧`
  _︔_!      : Coercion → Ty → Coercion     -- p ; G!
  _？_︔_     : Ty → Label → Coercion → Coercion   -- G?ℓ ; p
  bot-elim  : Coercion                     -- ∀X. X ⟹ ∀X. ★
  bot-intro : Label → Coercion             -- ∀X. ★ ⟹ ∀X. X

------------------------------------------------------------------------
-- 2. Modes and mode environments (GTSFImp `Var∼`, `Env∼`)
------------------------------------------------------------------------

data Mode : Set where
  X∼X   : Mode     -- strict: no tag, no check      (∀ᵖ's binder)
  X∼★   : Mode     -- may tag                       (instᵖ's binder)
  ★∼X   : Mode     -- may check                     (genᵖ's binder)
  ★∼X∼★ : Mode     -- cross: may tag and check      (source scope)

flipᵐ : Mode → Mode
flipᵐ X∼X   = X∼X
flipᵐ X∼★   = ★∼X
flipᵐ ★∼X   = X∼★
flipᵐ ★∼X∼★ = ★∼X∼★

-- One mode per ordinary name, parallel to `names Δ` (head = index 0).
ModeEnv : Set
ModeEnv = List Mode

flipEnv : ModeEnv → ModeEnv
flipEnv = map flipᵐ

-- every name in scope at the cross mode: the environment compilation
-- writes on its casts (GTSFImp `idᶜ`)
cross : TyCtx → ModeEnv
cross = map (λ _ → ★∼X∼★)

-- a fresh name at position k with mode m (GTSFImp's `renameEnv∼` at a
-- `skip`); a position past the end appends
insertAt : ℕ → Mode → ModeEnv → ModeEnv
insertAt zero    m μ       = m ∷ μ
insertAt (suc k) m []      = m ∷ []
insertAt (suc k) m (n ∷ μ) = n ∷ insertAt k m μ

-- the modes that permit a tag `X!` and a check `X?ℓ`
data TagOK : Mode → Set where
  tag-dyn   : TagOK X∼★
  tag-cross : TagOK ★∼X∼★

data CheckOK : Mode → Set where
  check-dyn   : CheckOK ★∼X
  check-cross : CheckOK ★∼X∼★

------------------------------------------------------------------------
-- 3. Side predicates
------------------------------------------------------------------------

-- The ground types other than a name (design.md §1: ι, ★ → ★, ∀X.★).
data GroundNV : Ty → Set where
  g-ℕ : GroundNV `ℕ
  g-𝔹 : GroundNV `𝔹
  g-⇒ : GroundNV (★ ⇒ ★)
  g-∀ : GroundNV (`∀ ★)

data NonVar : Ty → Set where
  nv-ℕ : NonVar `ℕ
  nv-𝔹 : NonVar `𝔹
  nv-★ : NonVar ★
  nv-⇒ : ∀ {A B} → NonVar (A ⇒ B)
  nv-∀ : ∀ {A} → NonVar (`∀ A)

data NonStar : Ty → Set where
  ns-var : ∀ {X} → NonStar (` X)
  ns-ℕ   : NonStar `ℕ
  ns-𝔹   : NonStar `𝔹
  ns-⇒   : ∀ {A B} → NonStar (A ⇒ B)
  ns-∀   : ∀ {A} → NonStar (`∀ A)

-- `X ∈ᵗ A`: the type variable X occurs free in A
infix 4 _∈ᵗ_
data _∈ᵗ_ : ℕ → Ty → Set where
  ∈-var : ∀ {X} → X ∈ᵗ ` X
  ∈-⇒ˡ  : ∀ {X A B} → X ∈ᵗ A → X ∈ᵗ A ⇒ B
  ∈-⇒ʳ  : ∀ {X A B} → X ∈ᵗ B → X ∈ᵗ A ⇒ B
  ∈-∀   : ∀ {X A} → suc X ∈ᵗ A → X ∈ᵗ `∀ A

-- The atoms: the only types at which an identity coercion is formed
-- (GTSFImp `Atom`; design.md D21).  Compound identities are written
-- structurally, `id(A) → id(B)` and `∀X. id(A)`.
data Atom : Ty → Set where
  atom-var : ∀ {X} → Atom (` X)
  atom-ℕ   : Atom `ℕ
  atom-𝔹   : Atom `𝔹
  atom-★   : Atom ★

-- GTSFImp `CastTerms.GenSafe`, on the syntax
data GenSafe : Coercion → Set where
  safe-↦    : ∀ {p q} → GenSafe (p ↦ᵖ q)
  safe-∀    : ∀ {p} → GenSafe (∀ᵖ p)
  safe-inst : ∀ {p} → GenSafe (instᵖ p)
  safe-gen  : ∀ {p} → GenSafe p → GenSafe (genᵖ p)

-- Inert coercions, design.md §3: P ::= G! | p → q | ∀X. p | gen X. p
data InertC : Coercion → Set where
  I-tag : ∀ {G} → InertC (G !)
  I-↦   : ∀ {p q} → InertC (p ↦ᵖ q)
  I-∀ᵖ  : ∀ {p} → InertC (∀ᵖ p)
  I-gen : ∀ {p} → InertC (genᵖ p)

------------------------------------------------------------------------
-- 4. Source and target, computed syntactically (design.md §3)
------------------------------------------------------------------------

-- `lowerᵗ` undoes `⇑ᵗ` on a type in which index 0 does not occur
-- (`A [ ★ ]ᵗ` then substitutes nothing): it is the de Bruijn reading of
-- design.md's `src(gen X. p) = src(p)` and `trg(inst X. p) = trg(p)`.
lowerᵗ : Ty → Ty
lowerᵗ A = A [ ★ ]ᵗ

mutual
  srcᵖ : Coercion → Ty
  srcᵖ (idᵖ A)       = A
  srcᵖ (G !)         = G
  srcᵖ (G ？ ℓ)      = ★
  srcᵖ (p ↦ᵖ q)      = trgᵖ p ⇒ srcᵖ q
  srcᵖ (∀ᵖ p)        = `∀ (srcᵖ p)
  srcᵖ (instᵖ p)     = `∀ (srcᵖ p)
  srcᵖ (genᵖ p)      = lowerᵗ (srcᵖ p)
  srcᵖ (p ︔ G !)     = srcᵖ p
  srcᵖ (G ？ ℓ ︔ p)   = ★
  srcᵖ bot-elim      = `∀ (` 0)
  srcᵖ (bot-intro ℓ) = `∀ ★

  trgᵖ : Coercion → Ty
  trgᵖ (idᵖ A)       = A
  trgᵖ (G !)         = ★
  trgᵖ (G ？ ℓ)      = G
  trgᵖ (p ↦ᵖ q)      = srcᵖ p ⇒ trgᵖ q
  trgᵖ (∀ᵖ p)        = `∀ (trgᵖ p)
  trgᵖ (instᵖ p)     = lowerᵗ (trgᵖ p)
  trgᵖ (genᵖ p)      = `∀ (trgᵖ p)
  trgᵖ (p ︔ G !)     = ★
  trgᵖ (G ？ ℓ ︔ p)   = trgᵖ p
  trgᵖ bot-elim      = `∀ ★
  trgᵖ (bot-intro ℓ) = `∀ (` 0)

------------------------------------------------------------------------
-- 5. Renaming, and closing a variable at ★
------------------------------------------------------------------------

-- ordinary renaming: types, tags and checks; binders extend
renᵖ : Renameᵗ → Coercion → Coercion
renᵖ ρ (idᵖ A)       = idᵖ (renameᵗ ρ A)
renᵖ ρ (G !)         = renameᵗ ρ G !
renᵖ ρ (G ？ ℓ)      = renameᵗ ρ G ？ ℓ
renᵖ ρ (p ↦ᵖ q)      = renᵖ ρ p ↦ᵖ renᵖ ρ q
renᵖ ρ (∀ᵖ p)        = ∀ᵖ renᵖ (extᵗ ρ) p
renᵖ ρ (instᵖ p)     = instᵖ renᵖ (extᵗ ρ) p
renᵖ ρ (genᵖ p)      = genᵖ renᵖ (extᵗ ρ) p
renᵖ ρ (p ︔ G !)     = renᵖ ρ p ︔ renameᵗ ρ G !
renᵖ ρ (G ？ ℓ ︔ p)   = renameᵗ ρ G ？ ℓ ︔ renᵖ ρ p
renᵖ ρ bot-elim      = bot-elim
renᵖ ρ (bot-intro ℓ) = bot-intro ℓ

-- `closeEnv k`: ★ for index k, the indices above k shifted down,
-- those below kept — `singleTyEnv ★` under k binders.
closeEnv : ℕ → Substᵗ
closeEnv zero    = singleTyEnv ★
closeEnv (suc k) = extsᵗ (closeEnv k)

closeTy : ℕ → Ty → Ty
closeTy k A = substᵗ (closeEnv k) A

-- a tag or check on the closed variable itself becomes `id(★)`
closeTag : ℕ → Ty → Coercion
closeTag k (` Y) with k ≟ Y
closeTag k (` Y) | yes _ = idᵖ ★
closeTag k (` Y) | no  _ = closeTy k (` Y) !
closeTag k `ℕ      = `ℕ !
closeTag k `𝔹      = `𝔹 !
closeTag k ★       = ★ !
closeTag k (A ⇒ B) = closeTy k (A ⇒ B) !
closeTag k (`∀ A)  = closeTy k (`∀ A) !

closeCheck : ℕ → Ty → Label → Coercion
closeCheck k (` Y) ℓ with k ≟ Y
closeCheck k (` Y) ℓ | yes _ = idᵖ ★
closeCheck k (` Y) ℓ | no  _ = closeTy k (` Y) ？ ℓ
closeCheck k `ℕ      ℓ = `ℕ ？ ℓ
closeCheck k `𝔹      ℓ = `𝔹 ？ ℓ
closeCheck k ★       ℓ = ★ ？ ℓ
closeCheck k (A ⇒ B) ℓ = closeTy k (A ⇒ B) ？ ℓ
closeCheck k (`∀ A)  ℓ = closeTy k (`∀ A) ？ ℓ

-- closing a sequence RE-NORMALIZES (GTSFImp's `subst-to-star-var`):
-- a tag or check on the closed variable itself disappears, leaving the
-- closed inner coercion, whose own end is now ★
closeSeqTag : ℕ → Coercion → Ty → Coercion
closeSeqTag k p′ (` Y) with k ≟ Y
closeSeqTag k p′ (` Y) | yes _ = p′
closeSeqTag k p′ (` Y) | no  _ = p′ ︔ closeTy k (` Y) !
closeSeqTag k p′ `ℕ      = p′ ︔ `ℕ !
closeSeqTag k p′ `𝔹      = p′ ︔ `𝔹 !
closeSeqTag k p′ ★       = p′ ︔ ★ !
closeSeqTag k p′ (A ⇒ B) = p′ ︔ closeTy k (A ⇒ B) !
closeSeqTag k p′ (`∀ A)  = p′ ︔ closeTy k (`∀ A) !

closeSeqCheck : ℕ → Ty → Label → Coercion → Coercion
closeSeqCheck k (` Y) ℓ p′ with k ≟ Y
closeSeqCheck k (` Y) ℓ p′ | yes _ = p′
closeSeqCheck k (` Y) ℓ p′ | no  _ = closeTy k (` Y) ？ ℓ ︔ p′
closeSeqCheck k `ℕ      ℓ p′ = `ℕ ？ ℓ ︔ p′
closeSeqCheck k `𝔹      ℓ p′ = `𝔹 ？ ℓ ︔ p′
closeSeqCheck k ★       ℓ p′ = ★ ？ ℓ ︔ p′
closeSeqCheck k (A ⇒ B) ℓ p′ = closeTy k (A ⇒ B) ？ ℓ ︔ p′
closeSeqCheck k (`∀ A)  ℓ p′ = closeTy k (`∀ A) ？ ℓ ︔ p′

-- closing an atom gives an atom
atom-ren : ∀ {ρ A} → Atom A → Atom (renameᵗ ρ A)
atom-ren atom-var = atom-var
atom-ren atom-ℕ   = atom-ℕ
atom-ren atom-𝔹   = atom-𝔹
atom-ren atom-★   = atom-★

atom-env : ∀ k X → Atom (closeEnv k X)
atom-env zero    zero    = atom-★
atom-env zero    (suc X) = atom-var
atom-env (suc k) zero    = atom-var
atom-env (suc k) (suc X) = atom-ren (atom-env k X)

atom-close : ∀ k {A} → Atom A → Atom (closeTy k A)
atom-close k (atom-var {X}) = atom-env k X
atom-close k atom-ℕ = atom-ℕ
atom-close k atom-𝔹 = atom-𝔹
atom-close k atom-★ = atom-★

-- `closeᵖ 0 p` is design.md's `p[★/X]` (GTSFImp `c [ ★/0 ]ᶜ`)
closeᵖ : ℕ → Coercion → Coercion
closeᵖ k (idᵖ A)       = idᵖ (closeTy k A)
closeᵖ k (G !)         = closeTag k G
closeᵖ k (G ？ ℓ)      = closeCheck k G ℓ
closeᵖ k (p ↦ᵖ q)      = closeᵖ k p ↦ᵖ closeᵖ k q
closeᵖ k (∀ᵖ p)        = ∀ᵖ closeᵖ (suc k) p
closeᵖ k (instᵖ p)     = instᵖ closeᵖ (suc k) p
closeᵖ k (genᵖ p)      = genᵖ closeᵖ (suc k) p
closeᵖ k (p ︔ G !)     = closeSeqTag k (closeᵖ k p) G
closeᵖ k (G ？ ℓ ︔ p)   = closeSeqCheck k G ℓ (closeᵖ k p)
closeᵖ k bot-elim      = bot-elim
closeᵖ k (bot-intro ℓ) = bot-intro ℓ

------------------------------------------------------------------------
-- 6. Typing  Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B   (design.md §3)
------------------------------------------------------------------------

private
  variable
    Δ : Ctxᵗ
    μ : ModeEnv
    m : Mode
    A A′ B B′ C G : Ty
    X : ℕ
    ℓ : Label
    p q : Coercion

-- a ground type that a tag (resp. check) may name under μ
data TagGround (Δ : Ctxᵗ) (μ : ModeEnv) : Ty → Set where
  tg-nv  : GroundNV G → TagGround Δ μ G
  tg-var : Δ ∋tv X → μ ∋ˡ X := m → TagOK m → TagGround Δ μ (` X)

data CheckGround (Δ : Ctxᵗ) (μ : ModeEnv) : Ty → Set where
  cg-nv  : GroundNV G → CheckGround Δ μ G
  cg-var : Δ ∋tv X → μ ∋ˡ X := m → CheckOK m → CheckGround Δ μ (` X)

infix 4 _∣_⊢ᵖ_∶_⟹_
data _∣_⊢ᵖ_∶_⟹_ : Ctxᵗ → ModeEnv → Coercion → Ty → Ty → Set where

  ⊢id : Atom A → Δ ⊢ᵗ A
      ------------------------------
    → Δ ∣ μ ⊢ᵖ idᵖ A ∶ A ⟹ A

  ⊢tag : GroundNV G
      ------------------------------
    → Δ ∣ μ ⊢ᵖ G ! ∶ G ⟹ ★

  ⊢tag-var : Δ ∋tv X → μ ∋ˡ X := m → TagOK m
      ------------------------------
    → Δ ∣ μ ⊢ᵖ (` X) ! ∶ ` X ⟹ ★

  ⊢check : GroundNV G
      ------------------------------
    → Δ ∣ μ ⊢ᵖ G ？ ℓ ∶ ★ ⟹ G

  ⊢check-var : Δ ∋tv X → μ ∋ˡ X := m → CheckOK m
      ------------------------------
    → Δ ∣ μ ⊢ᵖ (` X) ？ ℓ ∶ ★ ⟹ ` X

  -- the domain is typed under the FLIPPED environment
  ⊢fun : Δ ∣ flipEnv μ ⊢ᵖ p ∶ A′ ⟹ A → Δ ∣ μ ⊢ᵖ q ∶ B ⟹ B′
      ------------------------------------------------
    → Δ ∣ μ ⊢ᵖ p ↦ᵖ q ∶ A ⇒ B ⟹ A′ ⇒ B′

  ⊢all : underΛ Δ ∣ X∼X ∷ μ ⊢ᵖ p ∶ A ⟹ B
      ------------------------------------
    → Δ ∣ μ ⊢ᵖ ∀ᵖ p ∶ `∀ A ⟹ `∀ B

  ⊢inst : underΛ Δ ∣ X∼★ ∷ μ ⊢ᵖ p ∶ A ⟹ ⇑ᵗ B
    → Δ ⊢ᵗ B → NonVar A → 0 ∈ᵗ A → NonStar B
      ------------------------------------
    → Δ ∣ μ ⊢ᵖ instᵖ p ∶ `∀ A ⟹ B

  ⊢gen : underΛ Δ ∣ ★∼X ∷ μ ⊢ᵖ p ∶ ⇑ᵗ A ⟹ B
    → Δ ⊢ᵗ A → NonVar B → 0 ∈ᵗ B → NonStar A → GenSafe p
      ------------------------------------
    → Δ ∣ μ ⊢ᵖ genᵖ p ∶ A ⟹ `∀ B

  -- the two evidence-shaped sequences (GTSFImp `_!` and `？_`): the
  -- tag or check sits OUTSIDE, its ground is permitted by the modes, and
  -- the inner coercion's other end is not ★ (design.md D20)
  ⊢seq-tag : Δ ∣ μ ⊢ᵖ p ∶ A ⟹ G → TagGround Δ μ G → NonStar A
      ------------------------------------
    → Δ ∣ μ ⊢ᵖ p ︔ G ! ∶ A ⟹ ★

  ⊢seq-check : CheckGround Δ μ G → Δ ∣ μ ⊢ᵖ p ∶ G ⟹ B → NonStar B
      ------------------------------------
    → Δ ∣ μ ⊢ᵖ G ？ ℓ ︔ p ∶ ★ ⟹ B

  ⊢bot-elim :
      ------------------------------------
      Δ ∣ μ ⊢ᵖ bot-elim ∶ `∀ (` 0) ⟹ `∀ ★

  ⊢bot-intro :
      ------------------------------------
      Δ ∣ μ ⊢ᵖ bot-intro ℓ ∶ `∀ ★ ⟹ `∀ (` 0)

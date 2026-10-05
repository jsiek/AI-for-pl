module proof.DGG.notes.PermissionsR where

-- File Charter:
--   * THE DESIGN CHECKED HERE: Permissions.agda's world (`κʷ`, derived
--     marks, granting `⊑cast`) PLUS R1/R2 (PermissionsR.md), the repair
--     for Permissions' counterexample C5:
--       R1  `⟪⟫⊑` (the left's one-sided boundary) takes
--           `All (UnbindOK W) Θ`: every left UNBIND entry `unbind X α`
--           of Θ has `Unpermitted W α` (α has no permitted right
--           partner).  W and the interior world read the same
--           (`r1-interior`).
--       R2  the four ★ conversion clauses take `LeftUnpermitted W X`:
--           the left name's rep. var is `Unpermitted` in the conversion
--           world.
--     R1/R2 are RULE premises, not WfWorld fields (§19b: no world-level
--     invariant separates C5's hidden variant from P4).
--   * A COPY of Permissions.agda §1-§19 (module renamed; C5's derivation
--     and §20 C5InHEAD left out), with the two rule changes; every
--     corpus derivation re-checks (P2 and K's `⟪⟫⊑` get `ok-bind ∷ []`);
--     C1-C4g re-check.  New: §6a the condition, §19a C5 and its hidden
--     variant NOT derivable in any world at any κ, §19b rule-vs-WfWorld
--     and anti-monotonicity, §21 κ-weakening with the R12 side condition
--     and CastFun's grant case, §22 the pieces of the TagUntag drop.
--   * NOT a Def module, not imported by All.agda; nothing outside this
--     file and its .md is edited.  LEFT is the more precise side.

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; map; length; head; drop; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
  using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
  using (RepRel; _∋ᵨ_⇔_; here⇔; there⇔; sucᴸ; sucᴿ; suc²;
         shiftᴸ; shiftᴿ; shift²; _⊳_; OpenImp)
open import TermImprecision
  using (Lit; lit-$; lit-true; lit-false;
         CastTy; cast-ty; NuTy; nu-ty; BdyTy; bdy-ty;
         cast-inv; ν-inv; ⟪⟫-inv;
         CastClaim; cc-plain; cc-∀; cc-gen;
         ForallConv; fc-[]; fc-∷; BdyClaim; bc-plain; bc-∀;
         Carried; ca-[]; ca-∷; Push; push; push-none)
open import proof.ImprecisionWorld using (AtMostOneName; ≤1-[]; ≤1-∷[])

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Embeddings into a center of n names, and the derived marks
------------------------------------------------------------------------

infix 4 _↪_
data _↪_ : TyCtx → ℕ → Set where
  []↪  : [] ↪ 0
  keep : ∀ {α Δ n} → Δ ↪ n → (α ∷ Δ) ↪ suc n
  skip : ∀ {Δ n} → Δ ↪ n → Δ ↪ suc n

emb : ∀ {η n} → η ↪ n → Renameᵗ
emb []↪      X       = X
emb (keep ι) zero    = zero
emb (keep ι) (suc X) = suc (emb ι X)
emb (skip ι) X       = suc (emb ι X)

relabel : ∀ {η n} (f : RVar → RVar) → η ↪ n → map f η ↪ n
relabel f []↪      = []↪
relabel f (keep ι) = keep (relabel f ι)
relabel f (skip ι) = skip (relabel f ι)

-- THE PERMISSION of one right rep. var
permit : RVar → List RVar → VarImp
permit β []      = X⊑X
permit β (γ ∷ κ) = if β ≡ᵇ γ then X⊑★ else permit β κ

-- THE DERIVED MARKS: a center name the right sees is X⊑★ exactly when
-- its right rep. var is permitted; a center name the right does not see
-- (left-only) is X⊑★
dmarks : ∀ {ns n} → ns ↪ n → List RVar → ImpEnv
dmarks []↪              κ = []
dmarks (keep {α = β} ι) κ = permit β κ ∷ dmarks ι κ
dmarks (skip ι)         κ = X⊑★ ∷ dmarks ι κ

≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

permit-here : ∀ β κ → permit β (β ∷ κ) ≡ X⊑★
permit-here β κ rewrite ≡ᵇ-refl β = refl

-- a lookup at the head whose value is X⊑★ up to an equation
here★ : ∀ {m} {μ : ImpEnv} → m ≡ X⊑★ → (m ∷ μ) ∋ˡ 0 := X⊑★
here★ refl = here

------------------------------------------------------------------------
-- 2. Worlds
------------------------------------------------------------------------

record World (Δ Δ′ : Ctxᵗ) : Set where
  constructor world
  field
    Ωʷ  : ℕ                     -- the center: how many center names
    ηᴸʷ : names Δ ↪ Ωʷ
    ηᴿʷ : names Δ′ ↪ Ωʷ
    ϱᵍʷ : RepRel
    ϱˡʷ : RepRel
    κʷ  : List RVar             -- NEW: the permitted right rep. vars
    πʷ  : List ℕ
open World public

-- a world with no permission (every literal world of the corpus)
world⁰ : ∀ {Δ Δ′} (Ω : ℕ) → names Δ ↪ Ω → names Δ′ ↪ Ω
  → RepRel → RepRel → List ℕ → World Δ Δ′
world⁰ Ω η η′ ϱᵍ ϱˡ π = world Ω η η′ ϱᵍ ϱˡ [] π

marksʷ : World Δ Δ′ → ImpEnv
marksʷ W = dmarks (ηᴿʷ W) (κʷ W)

Paired : World Δ Δ′ → RVar → RVar → Set
Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

-- R1/R2's CONDITION: the LEFT rep. var α has no PERMITTED right partner.
-- Stated through `permit` (what the derived marks read); `unpermitted⇔`
-- below shows it is  ¬ ∃ β. Paired W α β × β ∈ κʷ W.
Unpermitted : World Δ Δ′ → RVar → Set
Unpermitted W α = ∀ {β} → Paired W α β → permit β (κʷ W) ≡ X⊑X

-- R2's form: every rep. var of the left name X (there is at most one)
LeftUnpermitted : World Δ Δ′ → ℕ → Set
LeftUnpermitted {Δ = Δ} W X = ∀ {α} → Δ ∋ᵗ X := α → Unpermitted W α

-- R1's form, per boundary entry: a left UNBIND of α needs α unpermitted;
-- a bind needs nothing
data UnbindOK (W : World Δ Δ′) : Change → Set where
  ok-bind   : ∀ {X α} → UnbindOK W (bind X α)
  ok-unbind : ∀ {X α} → Unpermitted W α → UnbindOK W (unbind X α)

Joins : World Δ Δ′ → ℕ → ℕ → Set
Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

∅ʷ : World empty empty
∅ʷ = world⁰ 0 []↪ []↪ [] [] []

embᴸ : World Δ Δ′ → Ty → Ty
embᴸ W = renameᵗ (emb (ηᴸʷ W))

embᴿ : World Δ Δ′ → Ty → Ty
embᴿ W = renameᵗ (emb (ηᴿʷ W))

-- THE INDEX: HEAD's, at the derived marks
infix 4 _⊑ᵂ⟨_⟩_
_⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᵂ⟨ W ⟩ A′ =
  OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

-- world operations: HEAD's, with no mark parameter (the marks are
-- derived); a right abstract rep. var shifts κ
infixl 6 _⊕² _⊕ᴸ _⊕⁺^_ _⊕ʳ^_
_⊕² : World Δ Δ′ → World (underΛ Δ) (underΛ Δ′)
world n η η′ ϱᵍ ϱˡ κ π ⊕² =
  world (suc n) (keep (relabel suc η)) (keep (relabel suc η′))
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc κ) (map suc π)

_⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
world n η η′ ϱᵍ ϱˡ κ π ⊕ᴸ =
  world (suc n) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ π

_⊕⁺^_ : World Δ Δ′ → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world n η η′ ϱᵍ ϱˡ κ π ⊕⁺^ β =
  world (suc n) (keep (relabel suc η)) (keep η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ (map suc π)

_⊕ʳ^_ : World Δ Δ′ → (β : RVar) → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
world n η η′ ϱᵍ ϱˡ κ π ⊕ʳ^ β =
  world (suc n) (skip η) (keep η′) ϱᵍ ϱˡ κ (map suc π)

data Join↪ {η : TyCtx}
    : ∀ {η′ n} → η ↪ n → η′ ↪ n → (zero ∷ map suc η) ↪ n → ℕ → Set where
  join-here : ∀ {β η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Join↪ (skip ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : ∀ {β η′ n k} {ι : η ↪ n} {ι′ : η′ ↪ n}
      {ι⁺ : (zero ∷ map suc η) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Join↪ (skip ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

-- the pop (D27): κ is unchanged (the right does not move)
data Open1 {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  open1 : ∀ {n ϱᵍ ϱˡ κ k π β} {ι : names Δ ↪ n} {ι′ : names Δ′ ↪ n}
      {ι⁺ : names (underΛ Δ) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Open1 (world n ι ι′ ϱᵍ ϱˡ κ (k ∷ π))
            (world n ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ π)

open-⊕ : ∀ {W : World Δ Δ′} {β}
  → Δ′ ∋rep β := ★
  → Open1 (record (W ⊕ʳ^ β) { πʷ = 0 ∷ map suc (πʷ W) }) (W ⊕⁺^ β)
open-⊕ hβ = open1 join-here here hβ

-- the ν-bound rep. vars: both sides allocate, κ shifts
underν² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
underν² R R′ (world n η η′ ϱᵍ ϱˡ κ π) =
  world n (relabel suc η) (relabel suc η′)
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc κ) π

------------------------------------------------------------------------
-- 3. The interior world and the conversion-context world: HEAD's,
-- with `same-κ` and WITHOUT marks (they are derived)
------------------------------------------------------------------------

record Interior (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
  constructor interior-world
  field
    int-left  : Δ ⊢ⁱ Θ ⇒ Δᵢ
    int-right : Δ′ ⊢ⁱ Θ′ ⇒ Δ′ᵢ
    same-ϱᵍ : ϱᵍʷ Wᵢ ≡ ϱᵍʷ W
    same-ϱˡ : ϱˡʷ Wᵢ ≡ ϱˡʷ W
    -- a boundary moves no rep. var: the permissions pass through
    same-κ  : κʷ Wᵢ ≡ κʷ W
    join-cont : ∀ {X X′ Xₑ X′ₑ}
      → Δᵢ ∋tv X → Δ′ᵢ ∋tv X′
      → toExt Θ X ≡ just Xₑ → toExt Θ′ X′ ≡ just X′ₑ
      → (Joins Wᵢ X X′ → Joins W Xₑ X′ₑ)
        × (Joins W Xₑ X′ₑ → Joins Wᵢ X X′)
    join-fresh : ∀ {X X′ α β}
      → Δᵢ ∋ᵗ X := α → Δ′ᵢ ∋ᵗ X′ := β
      → Fresh Θ X ⊎ Fresh Θ′ X′
      → (Joins Wᵢ X X′ → Paired W α β)
        × (Paired W α β → Joins Wᵢ X X′)
open Interior public

record ConversionInterior (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᶜ : World Δᶜ Δ′ᶜ) : Set where
  constructor conversion-interior-world
  field
    conv-left  : Δ ⊢ᶜ Θ ⇒ Δᶜ
    conv-right : Δ′ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
    conv-same-ϱᵍ : ϱᵍʷ Wᶜ ≡ ϱᵍʷ W
    conv-same-ϱˡ : ϱˡʷ Wᶜ ≡ ϱˡʷ W
    conv-same-κ  : κʷ Wᶜ ≡ κʷ W
    conv-join-cont : ∀ {X X′ Xₑ X′ₑ α β}
      → Δᶜ ∋ᵗ X := α → Δ′ᶜ ∋ᵗ X′ := β
      → Δ ∋ᵗ Xₑ := α → Δ′ ∋ᵗ X′ₑ := β
      → (Joins Wᶜ X X′ → Joins W Xₑ X′ₑ)
        × (Joins W Xₑ X′ₑ → Joins Wᶜ X X′)
    conv-join-fresh : ∀ {X X′ α β}
      → Δᶜ ∋ᵗ X := α → Δ′ᶜ ∋ᵗ X′ := β
      → (names Δ ∌ʳ α) ⊎ (names Δ′ ∌ʳ β)
      → (Joins Wᶜ X X′ → Paired W α β)
        × (Paired W α β → Joins Wᶜ X X′)
open ConversionInterior public

------------------------------------------------------------------------
-- 4. Term contexts and well-formedness
------------------------------------------------------------------------

-- an entry reads the marks, the center and the two embeddings; the
-- marks are a parameter of their own (they are derived from ηᴿ and κ)
record CtxImpEntry {ns ns′ : TyCtx} {n : ℕ} (μ : ImpEnv) (ηᴸ : ns ↪ n)
    (ηᴿ : ns′ ↪ n) : Set where
  constructor ctx-imp
  field
    tyᴸ  : Ty
    tyᴿ  : Ty
    impʷ : μ ⊢ renameᵗ (emb ηᴸ) tyᴸ ⊑ renameᵗ (emb ηᴿ) tyᴿ
open CtxImpEntry public

Entries : ∀ {ns ns′ n} (μ : ImpEnv) → ns ↪ n → ns′ ↪ n → Set
Entries μ ηᴸ ηᴿ = List (CtxImpEntry μ ηᴸ ηᴿ)

-- the entries are read at the derived marks: CtxImp depends on κʷ (not
-- on πʷ); a grant moves γ by `RaiseCtx`
CtxImp : World Δ Δ′ → Set
CtxImp W = Entries (marksʷ W) (ηᴸʷ W) (ηᴿʷ W)

lhs : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  → Entries μ ηᴸ ηᴿ → List Ty
lhs = map tyᴸ

rhs : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  → Entries μ ηᴸ ηᴿ → List Ty
rhs = map tyᴿ

infix 4 _∋ʷ_⦂_
data _∋ʷ_⦂_ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    : Entries μ ηᴸ ηᴿ → ℕ → CtxImpEntry μ ηᴸ ηᴿ → Set where
  Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
  Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

-- `⇑γ` for `Λ⊑Λ`: both types shifted, the proof any at the new world
data LiftCtx {ns ns′ n μ ns₁ ns′₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′₁ ↪ n₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  lift-[] : LiftCtx [] []
  lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx γ γ′
    → LiftCtx (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

-- `⇑ᴸγ` for `Λ⊑`: the right types cross unweakened
data LiftCtxᴸ {ns ns′ n μ ns₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′ ↪ n₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

-- NEW: a grant raises the marks; the entries keep their types (the
-- proofs are at the raised marks, which type imprecision is monotone in)
data RaiseCtx {ns ns′ n μ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ ηᴿ → Set where
  raise-[] : RaiseCtx [] []
  raise-∷  : ∀ {γ γ′ A A′ p p′} → RaiseCtx γ γ′
    → RaiseCtx (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p′ ∷ γ′)

raise-refl : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  (γ : Entries μ ηᴸ ηᴿ) → RaiseCtx γ γ
raise-refl []      = raise-[]
raise-refl (e ∷ γ) = raise-∷ (raise-refl γ)

-- the two embeddings jointly, WITHOUT marks
data Joint (P : RVar → RVar → Set)
    : ∀ {η η′ n} → η ↪ n → η′ ↪ n → Set where
  joint[]    : Joint P []↪ []↪
  both       : ∀ {α β η η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → P α β → Joint P ι ι′
    → Joint P (keep {α = α} ι) (keep {α = β} ι′)
  left-only  : ∀ {α η η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Joint P ι ι′
    → Joint P (keep {α = α} ι) (skip ι′)
  right-only : ∀ {β η η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Joint P ι ι′
    → Joint P (skip ι) (keep {α = β} ι′)

-- HEAD's payload imprecision (local marks only; unchanged)
data RepImp (W : World Δ Δ′) : ImpEnv → Ty → Ty → Set
infix 4 RepImp
syntax RepImp W μ R R′ = μ ⊢ R ⊑ᴿ⟨ W ⟩ R′

data RepImp W where
  ★⊑★ : ∀ {μ} → μ ⊢ ★ ⊑ᴿ⟨ W ⟩ ★
  ι⊑ι : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ι
  X⊑X : ∀ {μ X m} → μ ∋ˡ X := m → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ` X
  α⊑β : ∀ {μ α β} → Paired W α β
    → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ` (length μ + β)
  ⇒⊑⇒ : ∀ {μ R R′ S S′}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ S ⊑ᴿ⟨ W ⟩ S′
    → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ R′ ⇒ S′
  ∀⊑∀ : ∀ {μ R R′} → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ `∀ R′
  ⇒⊑★ : ∀ {μ R S}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ S ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ ★
  ι⊑★ : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ★
  X⊑★ : ∀ {μ X} → μ ∋ˡ X := X⊑★ → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ★
  α⊑★ : ∀ {μ α} → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ★
  ∀⊑  : ∀ {μ R R′} → NonVar R → 0 ∈ᵗ R
    → instᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ⇑ᵗ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ R′
  ∀★⊑★ : ∀ {μ} → μ ⊢ `∀ ★ ⊑ᴿ⟨ W ⟩ ★
  ∀⊑★ : ∀ {μ R} → NonStar R → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ★
    → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ ★
  bot-elim : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ `∀ ★
  bot⊑★ : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ ★

data Agree (W : World Δ Δ′) (α β : RVar) : Set where
  abst-abst : reps Δ ∋ʳ α := abstR → reps Δ′ ∋ʳ β := abstR
    → Agree W α β
  abst-★    : reps Δ ∋ʳ α := abstR → Δ′ ∋rep β := ★
    → Agree W α β
  rep-rep   : ∀ {R R′}
    → Δ ∋rep α := R → Δ′ ∋rep β := R′
    → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′
    → Agree W α β

NamedUniqueᴸ : World Δ Δ′ → Set
NamedUniqueᴸ {Δ} {Δ′} W = ∀ {α α′ β}
  → names Δ ∋ᵅ α → names Δ ∋ᵅ α′ → names Δ′ ∋ᵅ β
  → Paired W α β → Paired W α′ β → α ≡ α′

NamedUniqueᴿ : World Δ Δ′ → Set
NamedUniqueᴿ {Δ} {Δ′} W = ∀ {α β β′}
  → names Δ ∋ᵅ α → names Δ′ ∋ᵅ β → names Δ′ ∋ᵅ β′
  → Paired W α β → Paired W α β′ → β ≡ β′

NoNamedPartner : World Δ Δ′ → RVar → Set
NoNamedPartner {Δ} W β = ∀ {α} → names Δ ∋ᵅ α → ¬ Paired W α β

RightOnly : World Δ Δ′ → ℕ → Set
RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

-- a pending name: HEAD's, WITHOUT its fixed X⊑★ (its mark is derived:
-- X⊑★ exactly when its rep. var is permitted)
PendingOK : World Δ Δ′ → ℕ → Set
PendingOK {Δ′ = Δ′} W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
    × NoNamedPartner W β

record WfWorld (W : World Δ Δ′) : Set where
  constructor wf-world
  field
    wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wf-agree : ∀ {α β} → Paired W α β → Agree W α β
    wf-namedᴸ : NamedUniqueᴸ W
    wf-namedᴿ : NamedUniqueᴿ W
    wf-pending  : All (PendingOK W) (πʷ W)
    wf-distinct : AllPairs _≢_ (πʷ W)
    -- NEW: every permitted rep. var is a right rep. var (named or not:
    -- a right hide keeps it, P4 B4)
    wf-permits  : All (reps Δ′ ∋ʳ_) (κʷ W)
open WfWorld public

namedᴸ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ) → NamedUniqueᴸ W
namedᴸ-≤1 W h a a′ _ _ _ = h a a′

namedᴿ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ′) → NamedUniqueᴿ W
namedᴿ-≤1 W h _ b b′ _ _ = h b b′

------------------------------------------------------------------------
-- 5. Conversion imprecision: HEAD's, at the derived marks
------------------------------------------------------------------------

mutual
  data MidImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Mid → Mid → Set where
    conv-id⊑id : ∀ {A A′} → marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′
      → MidImp W (id A) (id A′)
    conv-↦⊑↦ : ∀ {s s′ c c′} → ConvImp W s s′ → ConvImp W c c′
      → MidImp W (s ↦ c) (s′ ↦ c′)
    conv-∀⊑∀ : ∀ {c c′} → ConvImp (W ⊕²) c c′
      → MidImp W (`∀ c) (`∀ c′)
    conv-∀⊑ : ∀ {c g′} → ConvImp (W ⊕ᴸ) c ⌞ g′ ⌟
      → MidImp W (`∀ c) g′

  data TailImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Tail → Tail → Set where
    conv-mid⊑mid : ∀ {g g′} → MidImp W g g′
      → TailImp W (mid g) (mid g′)
    conv-seal⊑seal : ∀ {X X′} → Joins W X X′
      → TailImp W (seal X) (seal X′)
    conv-⨾seal⊑⨾seal : ∀ {t t′ X X′} → TailImp W t t′ → Joins W X X′
      → TailImp W (t ⨾seal X) (t′ ⨾seal X′)
    -- R2: the four ★ clauses also need the left name's rep. var
    -- unpermitted (`LeftUnpermitted`)
    conv-seal⊑id★ : ∀ {X} → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftUnpermitted W X
      → TailImp W (seal X) (mid (id ★))
    conv-⨾seal⊑ : ∀ {t t′ X} → TailImp W t t′
      → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftUnpermitted W X
      → TailImp W (t ⨾seal X) t′

  data ConvImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Conv → Conv → Set where
    conv-tail⊑tail : ∀ {t t′} → TailImp W t t′
      → ConvImp W (tail t) (tail t′)
    conv-unseal⊑unseal : ∀ {X X′} → Joins W X X′
      → ConvImp W (unseal X) (unseal X′)
    conv-unseal⨾⊑unseal⨾ : ∀ {X X′ c c′} → Joins W X X′ → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) (unseal X′ ⨾ c′)
    conv-unseal⊑id★ : ∀ {X} → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftUnpermitted W X
      → ConvImp W (unseal X) ⌞ id ★ ⌟
    conv-unseal⨾⊑ : ∀ {X c c′} → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftUnpermitted W X
      → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) c′

NuConversionImp : ∀ {Δ Δ′ A A′ C C′ c c′ B B′}
  → (W : World Δ Δ′)
  → NuTy Δ A C c B → NuTy Δ′ A′ C′ c′ B′ → Set
NuConversionImp {c = c} {c′ = c′} W
  (nu-ty {R = R} {Δᶜ = Δᶜ} wA rA mw ⊢c eq wB)
  (nu-ty {R = R′} {Δᶜ = Δ′ᶜ} wA′ rA′ mw′ ⊢c′ eq′ wB′) =
  Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
    (ConversionInterior (underν² R R′ W) TyBetaBoundary TyBetaBoundary Wᶜ
    × ConvImp Wᶜ c c′)

BdyConversionImp : ∀ {Δ Δ′ Δᵢ Δ′ᵢ Θ Θ′}
    {Aᵢ A′ᵢ c c′ A A′}
  → (W : World Δ Δ′)
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → Set
BdyConversionImp {Θ = Θ} {Θ′ = Θ′} {c = c} {c′ = c′} W
  (bdy-ty {Δᶜ = Δᶜ} mw ⊢c eqᵢ eqₑ wB)
  (bdy-ty {Δᶜ = Δ′ᶜ} mw′ ⊢c′ eq′ᵢ eq′ₑ wB′) =
  Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
    (ConversionInterior W Θ Θ′ Wᶜ × ConvImp Wᶜ c c′)

------------------------------------------------------------------------
-- 6. Grants, and the relation: HEAD's 15 rules with a granting ⊑cast
------------------------------------------------------------------------

-- a coercion through which nothing flows OUT of the cast value
data FirstOrder : Coercion → Set where
  fo-id : ∀ {A} → FirstOrder (idᵖ A)
  fo-!  : ∀ {G} → FirstOrder (G !)
  fo-?  : ∀ {G ℓ} → FirstOrder (G ？ ℓ)

-- `Grants Δ′ β c′`: every value that leaves the right's cast value
-- through c′ is checked against the name of rep. var β.  A check of X
-- (bound to β); an arrow whose codomain grants and whose domain is
-- first order (a covariant X? covers the contravariant X!, e.g. the
-- gen wrapper `X! → X?`).  C2's `X! → id(★)` grants nothing.
data Grants (Δ′ : Ctxᵗ) (β : RVar) : Coercion → Set where
  gr-?  : ∀ {X ℓ} → Δ′ ∋ᵗ X := β → Grants Δ′ β ((` X) ？ ℓ)
  gr-?︔ : ∀ {X ℓ p} → Δ′ ∋ᵗ X := β → Grants Δ′ β ((` X) ？ ℓ ︔ p)
  gr-↦  : ∀ {p q} → FirstOrder p → Grants Δ′ β q → Grants Δ′ β (p ↦ᵖ q)

-- `⊑cast`'s permissions (conclusion κ, premise κₚ): unchanged, or one
-- more rep. var that the right coercion grants
data CastGrant (Δ′ : Ctxᵗ) (c′ : Coercion) (κ : List RVar)
    : List RVar → Set where
  no-grant : CastGrant Δ′ c′ κ κ
  grant    : ∀ {β} → Grants Δ′ β c′ → CastGrant Δ′ c′ κ (β ∷ κ)

data Claim : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  claim-fresh : ∀ {n ϱᵍ ϱˡ κ} {ηᴸ : names Δ ↪ n} {ηᴿ : names Δ′ ↪ n}
    → let W = world {Δ} {Δ′} n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in Claim W (W ⊕ᴸ)
  claim-pop   : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
    → Open1 W W₁ → Claim W W₁

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ}
    : (W : World Δ Δ′) → CtxImp W → Term → Term
    → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ k ι}
    → Lit k ι
    → (p : ι ⊑ᵂ⟨ W ⟩ ι)
    → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ L L′ M M′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {W : World Δ Δ′} {πₚ γ M M′ μ c B A A′}
      {p : B ⊑ᵂ⟨ record W { πʷ = πₚ } ⟩ A′}
    → CastClaim M c (πʷ W) πₚ
    → record W { πʷ = πₚ } ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  -- THE GRANTING RULE: a right coercion that grants β puts β into the
  -- premise's permissions (`CastGrant`); γ moves along (`RaiseCtx`)
  ⊑cast : ∀ {W : World Δ Δ′} {κₚ γ γ′ M M′ μ′ c′ A B′ A′}
      {p : A ⊑ᵂ⟨ record W { κʷ = κₚ } ⟩ B′}
    → CastGrant Δ′ c′ (κʷ W) κₚ
    → RaiseCtx γ γ′
    → record W { κʷ = κₚ } ∣ γ′ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕² ⟩ A′}
    → LiftCtx γ γ′
    → Value V
    → Value V′
    → W ⊕² ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {γ γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W₁ ⟩ B′}
    → Claim W W₁
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  ν⊑ν : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {Δᵢ Δ′ᵢ nᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ}
    → let Wᵢ = world {Δᵢ} {Δ′ᵢ} nᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ [] in
      ∀ {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  -- R1: every left UNBIND entry of Θ names an unpermitted rep. var (in
  -- W; equivalently in Wᵢ, `r1-interior`)
  ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ
    → All (UnbindOK W) Θ
    → BdyClaim M c (πʷ W) (πʷ Wᵢ)
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → Push Θ′ M (πʷ W) (πʷ Wᵢ)
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

infix 3 _∣_⊢_⊑_∶⟨_,_⟩_
_∣_⊢_⊑_∶⟨_,_⟩_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
  → (A A′ : Ty) → A ⊑ᵂ⟨ W ⟩ A′ → Set
W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p = _∣_⊢_⊑_∶_ W γ M M′ {A} {A′} p

-- HEAD's ⊑cast: no grant (the premise world is W itself, by record eta)
⊑cast₀ : ∀ {W : World Δ Δ′} {γ M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → CastTy Δ′ μ′ c′ B′ A′
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q
⊑cast₀ {γ = γ} d ct q = ⊑cast no-grant (raise-refl γ) d ct q

-- a grant at the empty term context (every grant of the corpus)
⊑cast! : ∀ {W : World Δ Δ′} {β M M′ μ′ c′ A B′ A′}
    {p : A ⊑ᵂ⟨ record W { κʷ = β ∷ κʷ W } ⟩ B′}
  → Grants Δ′ β c′
  → record W { κʷ = β ∷ κʷ W } ∣ [] ⊢ M ⊑ M′ ∶ p
  → CastTy Δ′ μ′ c′ B′ A′
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ [] ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q
⊑cast! g d ct q = ⊑cast (grant g) raise-[] d ct q

------------------------------------------------------------------------
-- 6a. R1/R2: the condition, its two readings, and which world.
------------------------------------------------------------------------

-- membership in a permission list
infix 4 _∈κ_
data _∈κ_ (β : RVar) : List RVar → Set where
  here∈  : ∀ {κ} → β ∈κ (β ∷ κ)
  there∈ : ∀ {γ κ} → β ∈κ κ → β ∈κ (γ ∷ κ)

T-≡ᵇ : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
T-≡ᵇ zero    zero    _  = refl
T-≡ᵇ zero    (suc n) ()
T-≡ᵇ (suc m) zero    ()
T-≡ᵇ (suc m) (suc n) e  = cong suc (T-≡ᵇ m n e)

permit-∈ : ∀ β κ → permit β κ ≡ X⊑★ → β ∈κ κ
permit-∈ β []      ()
permit-∈ β (γ ∷ κ) h with β ≡ᵇ γ in eq
... | true  rewrite T-≡ᵇ β γ eq = here∈
... | false = there∈ (permit-∈ β κ h)

∈-permit : ∀ {β κ} → β ∈κ κ → permit β κ ≡ X⊑★
∈-permit {β} {β ∷ κ} here∈ = permit-here β κ
∈-permit {β} {γ ∷ κ} (there∈ m) with β ≡ᵇ γ
... | true  = refl
... | false = ∈-permit m

permit-X⊑X : ∀ β κ → permit β κ ≢ X⊑★ → permit β κ ≡ X⊑X
permit-X⊑X β κ n with permit β κ
... | X⊑X = refl
... | X⊑★ = ⊥-elim (n refl)

-- `Unpermitted W α` is exactly  ¬ ∃ β. Paired W α β × β ∈ κʷ W
unpermitted→ : ∀ {W : World Δ Δ′} {α} → Unpermitted W α
  → ¬ (Σ[ β ∈ RVar ] Paired W α β × β ∈κ κʷ W)
unpermitted→ u (β , pr , m) with trans (sym (∈-permit m)) (u pr)
... | ()

→unpermitted : ∀ {W : World Δ Δ′} {α}
  → ¬ (Σ[ β ∈ RVar ] Paired W α β × β ∈κ κʷ W) → Unpermitted W α
→unpermitted {W = W} n {β} pr =
  permit-X⊑X β (κʷ W) (λ h → n (β , pr , permit-∈ β (κʷ W) h))

-- the negation, as the negative proofs use it
HasPermittedPartner : World Δ Δ′ → RVar → Set
HasPermittedPartner W α =
  Σ[ β ∈ RVar ] Paired W α β × (permit β (κʷ W) ≡ X⊑★)

r1-fails : ∀ {W : World Δ Δ′} {α} → HasPermittedPartner W α
  → ¬ Unpermitted W α
r1-fails (β , pr , pm) u with trans (sym pm) (u pr)
... | ()

-- WHICH WORLD: a boundary keeps ϱ and κ, so R1 reads the same in the
-- conclusion world W and the interior world Wᵢ (and R2 likewise in the
-- conversion world and the exterior)
Paired-int : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α β}
  → Interior W Θ Θ′ Wᵢ → Paired W α β → Paired Wᵢ α β
Paired-int I (inj₁ h) = inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (same-ϱᵍ I)) h)
Paired-int I (inj₂ h) = inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (same-ϱˡ I)) h)

Paired-int⁻ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α β}
  → Interior W Θ Θ′ Wᵢ → Paired Wᵢ α β → Paired W α β
Paired-int⁻ I (inj₁ h) = inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (same-ϱᵍ I) h)
Paired-int⁻ I (inj₂ h) = inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (same-ϱˡ I) h)

unpermitted-int : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α}
  → Interior W Θ Θ′ Wᵢ → Unpermitted W α → Unpermitted Wᵢ α
unpermitted-int I u {β} pr =
  subst (λ κ → permit β κ ≡ X⊑X) (sym (same-κ I)) (u (Paired-int⁻ I pr))

unpermitted-int⁻ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α}
  → Interior W Θ Θ′ Wᵢ → Unpermitted Wᵢ α → Unpermitted W α
unpermitted-int⁻ I u {β} pr =
  subst (λ κ → permit β κ ≡ X⊑X) (same-κ I) (u (Paired-int I pr))

r1-interior : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → (All (UnbindOK W) Θ → All (UnbindOK Wᵢ) Θ)
    × (All (UnbindOK Wᵢ) Θ → All (UnbindOK W) Θ)
r1-interior I = to , from
  where
  to : ∀ {Θ} → All (UnbindOK _) Θ → All (UnbindOK _) Θ
  to []                  = []
  to (ok-bind ∷ r)       = ok-bind ∷ to r
  to (ok-unbind u ∷ r)   = ok-unbind (unpermitted-int I u) ∷ to r
  from : ∀ {Θ} → All (UnbindOK _) Θ → All (UnbindOK _) Θ
  from []                = []
  from (ok-bind ∷ r)     = ok-bind ∷ from r
  from (ok-unbind u ∷ r) = ok-unbind (unpermitted-int⁻ I u) ∷ from r

hasPP-int : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α}
  → Interior W Θ Θ′ Wᵢ → HasPermittedPartner W α
  → HasPermittedPartner Wᵢ α
hasPP-int I (β , pr , pm) =
  β , Paired-int I pr , subst (λ κ → permit β κ ≡ X⊑★) (sym (same-κ I)) pm

hasPP-conv : ∀ {W : World Δ Δ′} {Wᶜ : World Δᶜ Δ′ᶜ} {Θ Θ′ α}
  → ConversionInterior W Θ Θ′ Wᶜ → HasPermittedPartner W α
  → HasPermittedPartner Wᶜ α
hasPP-conv ci (β , inj₁ h , pm) =
  β , inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (conv-same-ϱᵍ ci)) h)
    , subst (λ κ → permit β κ ≡ X⊑★) (sym (conv-same-κ ci)) pm
hasPP-conv ci (β , inj₂ h , pm) =
  β , inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (conv-same-ϱˡ ci)) h)
    , subst (λ κ → permit β κ ≡ X⊑★) (sym (conv-same-κ ci)) pm

------------------------------------------------------------------------
-- 7. HEAD's TermImprecisionExamples (P1, P2, P3, P6), ported: worlds
-- get κ = [] (`world⁰`), each `Interior` gets `same-κ` and loses its
-- mark fields
------------------------------------------------------------------------

module TIE where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples
    using (L1; R1; L1-⊢; R1-⊢; R2; L3-⊢; R3-⊢; L6; R6; L6-⊢; R6-⊢)

  ------------------------------------------------------------------------
  -- Shared pieces
  ------------------------------------------------------------------------

  idX : Term
  idX = ƛ (` 0) ∙ ` 0

  revX : Conv
  revX = reveal 0 (` 0 ⇒ ` 0)

  ℕ⊑★ : ∀ {μ} → μ ⊢ `ℕ ⊑ ★
  ℕ⊑★ = ι⊑★ base-ℕ

  5⟨ℕ!⟩ : Term
  5⟨ℕ!⟩ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  -- the argument `5 ⊑ 5⟨ℕ!⟩` at ℕ ⊑ ★, in any world whose right side has
  -- no names (the cast carries `[]`)
  five⊑ : ∀ {Δ Ξ′ Ω ϱᵍ ϱˡ κ} {ηᴸ : names Δ ↪ Ω} {ηᴿ : [] ↪ Ω}
    → let W = world {Δ} {Ξ′ ∣ []} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in ∀ {γ : CtxImp W}
    → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
  five⊑ = ⊑cast₀ (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

  ∀X⇒X : Ty
  ∀X⇒X = `∀ (` 0 ⇒ ` 0)

  ------------------------------------------------------------------------
  -- P1, initial pair
  ------------------------------------------------------------------------

  νL νR : Term
  νL = ν `ℕ · Λ idX ⟨ revX ⟩
  νR = ν ★ · Λ idX ⟨ revX ⟩

  νL-⊢ : empty ∣ [] ⊢ νL ⦂ `ℕ ⇒ `ℕ
  νL-⊢ = tc

  νR-⊢ : empty ∣ [] ⊢ νR ⦂ ★ ⇒ ★
  νR-⊢ = tc

  νL-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv νL-⊢))

  νR-ty : NuTy empty ★ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  νR-ty = proj₂ (proj₂ (ν-inv νR-⊢))

  ------------------------------------------------------------------------
  -- P1, after both TyBetas
  ------------------------------------------------------------------------

  Θ₀ : Boundary
  Θ₀ = bind 0 0 ∷ []

  L1′ R1′ : Term
  L1′ = (idX ⟪ Θ₀ , revX ⟫) · $ 5
  R1′ = (idX ⟪ Θ₀ , revX ⟫) · 5⟨ℕ!⟩

  L1′-state : head (drop 1 (evalTerms 10 L1-⊢)) ≡ just L1′
  L1′-state = refl

  R1′-state : head (drop 1 (evalTerms 11 R1-⊢)) ≡ just R1′
  R1′-state = refl

  ΔL ΔR ΔLᵢ ΔRᵢ : Ctxᵗ
  ΔL = allocate `ℕ empty
  ΔR = allocate ★ empty
  ΔLᵢ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])
  ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])

  ConvCtx₀ : Ty → Ctxᵗ
  ConvCtx₀ R = (bindR R ∷ []) ∣ (0 ∷ [])

  conv₀ : ∀ {R} → allocate R empty ⊢ᶜ Θ₀ ⇒ ConvCtx₀ R
  conv₀ = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

  -- The ν-conversion world has one both-sided name and the ν-bound pair
  -- in ϱˡ, not ϱᵍ.
  Wν : ∀ {R R′} → World (ConvCtx₀ R) (ConvCtx₀ R′)
  Wν = world⁰ 1 (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) []

  Wν-conv : ∀ {R R′}
    → ConversionInterior (underν² R R′ ∅ʷ) Θ₀ Θ₀ Wν
  Wν-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  revX⊑revX : ∀ {Δ Δ′} {W : World Δ Δ′}
    → Joins W 0 0 → ConvImp W revX revX
  revX⊑revX j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-unseal⊑unseal j)))

  νLR-conv : NuConversionImp ∅ʷ νL-ty νR-ty
  νLR-conv = Wν , Wν-conv , revX⊑revX refl

  p1-init : ∅ʷ ∣ [] ⊢ L1 ⊑ R1 ∶ ℕ⊑★
  p1-init =
    ·⊑· (ν⊑ν (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
                (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
             ℕ⊑★ νL-ty νR-ty νLR-conv (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  -- the exterior world: no names; the two store rep. vars paired (ϱᵍ)
  W₁ : World ΔL ΔR
  W₁ = world⁰ 0 []↪ []↪ ((0 , 0) ∷ []) [] []

  -- the interior world: X both-sided at X⊑X
  Wᵢ₁ : World ΔLᵢ ΔRᵢ
  Wᵢ₁ = world⁰ 1 (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  int₀ : ∀ {R} → allocate R empty ⊢ⁱ Θ₀ ⇒ ((bindR R ∷ []) ∣ (0 ∷ []))
  int₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  Wᵢ₁-int : Interior W₁ Θ₀ Θ₀ Wᵢ₁
  Wᵢ₁-int = record
    { int-left   = int₀
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  Wᵢ₁-conv : ConversionInterior W₁ Θ₀ Θ₀ Wᵢ₁
  Wᵢ₁-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  bL bR : Term
  bL = idX ⟪ Θ₀ , revX ⟫
  bR = bL

  bL-⊢ : ΔL ∣ [] ⊢ bL ⦂ `ℕ ⇒ `ℕ
  bL-⊢ = tc

  bR-⊢ : ΔR ∣ [] ⊢ bR ⦂ ★ ⇒ ★
  bR-⊢ = tc

  bL-ty : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bL-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv bL-⊢)))

  bR-ty : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bR-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv bR-⊢)))

  bLR-conv : BdyConversionImp W₁ bL-ty bR-ty
  bLR-conv = Wᵢ₁ , Wᵢ₁-conv , revX⊑revX refl

  Wᵢ₁-wf : WfWorld Wᵢ₁
  Wᵢ₁-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wᵢ₁ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₁ ≤1-∷[]) [] [] []
    where
    agree : ∀ {α β} → Paired Wᵢ₁ α β → Agree Wᵢ₁ α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  p1-tybeta : W₁ ∣ [] ⊢ L1′ ⊑ R1′ ∶ ℕ⊑★
  p1-tybeta =
    ·⊑· (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
                (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bL-ty bR-ty bLR-conv
                (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P2, after the left's TyBeta (a left-only boundary)
  ------------------------------------------------------------------------

  R2-state : R2 ≡ (ƛ ★ ∙ ` 0) · 5⟨ℕ!⟩
  R2-state = refl

  W₂ : World ΔL empty
  W₂ = world⁰ 0 []↪ []↪ [] [] []

  -- X is left-only, so its mark is X⊑★
  Wᵢ₂ : World ΔLᵢ empty
  Wᵢ₂ = world⁰ 1 (keep []↪) (skip []↪) [] [] []

  Wᵢ₂-int : Interior W₂ Θ₀ [] Wᵢ₂
  Wᵢ₂-int = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    }

  Wᵢ₂-wf : WfWorld Wᵢ₂
  Wᵢ₂-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 Wᵢ₂ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₂ ≤1-[]) [] [] []
    where
    agree : ∀ {α β} → Paired Wᵢ₂ α β → Agree Wᵢ₂ α β
    agree (inj₁ ())
    agree (inj₂ ())

  p2-tybeta : W₂ ∣ [] ⊢ L1′ ⊑ R2 ∶ ℕ⊑★
  p2-tybeta =
    ·⊑· (⟪⟫⊑ Wᵢ₂-int (ok-bind ∷ []) bc-plain (Wᵢ₂-wf)
                (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) bL-ty
                (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P3, after the right's Inst, TyBeta and Beta, before the left's
  -- TyBeta: ⊑⟪⟫ pushes the Inst boundary's name and Λ⊑ pops it (D27;
  -- before D26, ∀⊑⟪+⟫; D26: an opening) to relate the left Λ to the right's
  -- Inst boundary
  ------------------------------------------------------------------------

  R3′ : Term
  R3′ = ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ ★ ⟩) · 5⟨ℕ!⟩

  L3′-state : head (drop 1 (evalTerms 11 L3-⊢)) ≡ just L1
  L3′-state = refl

  R3′-state : head (drop 3 (evalTerms 16 R3-⊢)) ≡ just R3′
  R3′-state = refl

  W₃ : World empty ΔR
  W₃ = world⁰ 0 []↪ []↪ [] [] []

  -- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★)
  ∀id⊑★ : ∀X⇒X ⊑ᵂ⟨ W₃ ⟩ (★ ⇒ ★)
  ∀id⊑★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  ΛidX-⊢ : empty ∣ [] ⊢ Λ idX ⦂ ∀X⇒X
  ΛidX-⊢ = tc

  -- the Inst boundary `+X^α` (α:=★ at rep. var 0) alone: X is a
  -- right-only name (its mark is αᴿ's permission: none, X⊑X), and
  -- PUSHED: the interior world has the pending name 0 (D27)
  int-ro₃ : Interior W₃ [] Θ₀ (record (W₃ ⊕ʳ^ 0) { πʷ = 0 ∷ [] })
  int-ro₃ = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- inside the Inst boundary: X right-only, and PENDING (D27): it
  -- is bound to the ★ rep. var αᴿ and has no named left partner
  Wi₃-wf : WfWorld (record (W₃ ⊕ʳ^ 0) { πʷ = 0 ∷ [] })
  Wi₃-wf = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 (W₃ ⊕ʳ^ 0) ≤1-[]) (namedᴿ-≤1 (W₃ ⊕ʳ^ 0) ≤1-∷[])
    ((0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ [])
    ([] ∷ []) []

  vΛidX : Value (Λ idX)
  vΛidX = V-simple (S-Λ (V-simple S-ƛ))

  -- THE CORE: ⊑⟪⟫ PUSHES the boundary's name X (the left is a value);
  -- Λ⊑ POPS it: the left binder joins X, its abstract rep. var paired
  -- lexically with αᴿ:=★ (`open-⊕`: the popped world is `W₃ ⊕⁺^ 0`);
  -- then ƛ⊑ƛ at X ⊑ X
  core₃ : W₃ ∣ [] ⊢ Λ idX ⊑ idX ⟪ Θ₀ , revX ⟫ ∶ ∀id⊑★
  core₃ =
    ⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vΛidX)) Wi₃-wf
      (Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[]
        (V-simple S-ƛ) (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (⇒⊑⇒ X⊑X X⊑X))
      bR-ty ∀id⊑★

  p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  p3-inst =
    ·⊑· (ν⊑ (⊑cast₀ core₃
                   (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl)
                   ∀id⊑★)
            ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P6, the initial ν pair and the state after both TyBetas
  ------------------------------------------------------------------------

  ∀6L ∀6R : Ty
  ∀6L = `∀ (` 0 ⇒ `ℕ)
  ∀6R = `∀ (` 0 ⇒ ★)

  ∀6L⊑∀6R : ∀6L ⊑ᵂ⟨ ∅ʷ ⟩ ∀6R
  ∀6L⊑∀6R = ∀⊑∀ (⇒⊑⇒ X⊑X ℕ⊑★)

  c6L c6R : Conv
  c6L = reveal 0 (` 0 ⇒ `ℕ)
  c6R = reveal 0 (` 0 ⇒ ★)

  ν6L ν6R : Term
  ν6L = ν `𝔹 · ` 0 ⟨ c6L ⟩
  ν6R = ν `𝔹 · ` 0 ⟨ c6R ⟩

  ν6L-⊢ : empty ∣ ∀6L ∷ [] ⊢ ν6L ⦂ `𝔹 ⇒ `ℕ
  ν6L-⊢ = tc

  ν6R-⊢ : empty ∣ ∀6R ∷ [] ⊢ ν6R ⦂ `𝔹 ⇒ ★
  ν6R-⊢ = tc

  ν6L-ty : NuTy empty `𝔹 (` 0 ⇒ `ℕ) c6L (`𝔹 ⇒ `ℕ)
  ν6L-ty = proj₂ (proj₂ (ν-inv ν6L-⊢))

  ν6R-ty : NuTy empty `𝔹 (` 0 ⇒ ★) c6R (`𝔹 ⇒ ★)
  ν6R-ty = proj₂ (proj₂ (ν-inv ν6R-⊢))

  c6⊑ : ∀ {Δ Δ′} {W : World Δ Δ′}
    → Joins W 0 0 → ConvImp W c6L c6R
  c6⊑ j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-tail⊑tail
                     (conv-mid⊑mid (conv-id⊑id ℕ⊑★)))))

  ν6-conv : NuConversionImp ∅ʷ ν6L-ty ν6R-ty
  ν6-conv = Wν , Wν-conv , c6⊑ refl

  p6-init-ν : ∅ʷ ∣ ctx-imp ∀6L ∀6R ∀6L⊑∀6R ∷ []
    ⊢ ν6L ⊑ ν6R ∶ ⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★
  p6-init-ν =
    ν⊑ν (x⊑x Zʷ) (ι⊑ι base-𝔹) ν6L-ty ν6R-ty ν6-conv
         (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★)

  Δ6 Δ6ᵢ : Ctxᵗ
  Δ6 = allocate `𝔹 empty
  Δ6ᵢ = ConvCtx₀ `𝔹

  W₆ : World Δ6 Δ6
  W₆ = world⁰ 0 []↪ []↪ ((0 , 0) ∷ []) [] []

  Wᵢ₆ : World Δ6ᵢ Δ6ᵢ
  Wᵢ₆ = world⁰ 1 (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  int₆ : Δ6 ⊢ⁱ Θ₀ ⇒ Δ6ᵢ
  int₆ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  Wᵢ₆-int : Interior W₆ Θ₀ Θ₀ Wᵢ₆
  Wᵢ₆-int = record
    { int-left   = int₆
    ; int-right  = int₆
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  Wᵢ₆-wf : WfWorld Wᵢ₆
  Wᵢ₆-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wᵢ₆ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₆ ≤1-∷[]) [] [] []
    where
    agree : ∀ {α β} → Paired Wᵢ₆ α β → Agree Wᵢ₆ α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑ι base-𝔹)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wᵢ₆-conv : ConversionInterior W₆ Θ₀ Θ₀ Wᵢ₆
  Wᵢ₆-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  body6L body6R : Term
  body6L = ƛ (` 0) ∙ $ 7
  body6R = body6L ⟨ X∼X ∷ [] ∣ idᵖ (` 0) ↦ᵖ (`ℕ !) ⟩

  b6L b6R : Term
  b6L = body6L ⟪ Θ₀ , c6L ⟫
  b6R = body6R ⟪ Θ₀ , c6R ⟫

  L6′ R6′ : Term
  L6′ = b6L · `true
  R6′ = b6R · `true

  L6′-state : head (drop 2 (evalTerms 10 L6-⊢)) ≡ just L6′
  L6′-state = refl

  R6′-state : head (drop 2 (evalTerms 13 R6-⊢)) ≡ just R6′
  R6′-state = refl

  body6R-⊢ : Δ6ᵢ ∣ [] ⊢ body6R ⦂ ` 0 ⇒ ★
  body6R-⊢ = tc

  body6R-ty : CastTy Δ6ᵢ (X∼X ∷ []) (idᵖ (` 0) ↦ᵖ (`ℕ !))
                           (` 0 ⇒ `ℕ) (` 0 ⇒ ★)
  body6R-ty = proj₂ (proj₂ (cast-inv body6R-⊢))

  b6L-⊢ : Δ6 ∣ [] ⊢ b6L ⦂ `𝔹 ⇒ `ℕ
  b6L-⊢ = tc

  b6R-⊢ : Δ6 ∣ [] ⊢ b6R ⦂ `𝔹 ⇒ ★
  b6R-⊢ = tc

  b6L-ty : BdyTy Δ6 Θ₀ Δ6ᵢ (` 0 ⇒ `ℕ) c6L (`𝔹 ⇒ `ℕ)
  b6L-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv b6L-⊢)))

  b6R-ty : BdyTy Δ6 Θ₀ Δ6ᵢ (` 0 ⇒ ★) c6R (`𝔹 ⇒ ★)
  b6R-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv b6R-⊢)))

  b6-conv : BdyConversionImp W₆ b6L-ty b6R-ty
  b6-conv = Wᵢ₆ , Wᵢ₆-conv , c6⊑ refl

  p6-tybeta : W₆ ∣ [] ⊢ L6′ ⊑ R6′ ∶ ℕ⊑★
  p6-tybeta =
    ·⊑·
      (⟪⟫⊑⟪⟫ Wᵢ₆-int Wᵢ₆-wf
        (⊑cast₀
          (ƛ⊑ƛ {pA = X⊑X} {pB = ι⊑ι base-ℕ}
            tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
          body6R-ty (⇒⊑⇒ X⊑X ℕ⊑★))
        b6L-ty b6R-ty b6-conv (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★))
      (κ⊑κ lit-true (ι⊑ι base-𝔹))

------------------------------------------------------------------------
-- 8. HEAD's TermImprecisionRebaseExamples (C12, C13, C14, Cg, C2, Ch),
-- ported.  CHANGE: the worlds carry permissions; every gen wrapper
-- `X! → X?` GRANTS its rep. var (`tagX↦-grants`), which is what makes
-- the shared name X⊑★ inside it (`layer⊑`, `outer⊑`, `cg-body`,
-- `c2-body`); inside the right's own `−X` the name is left-only
------------------------------------------------------------------------

module Rebase where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples
  open import TermSubst using (crossΛᴹ)
  open import examples.ImprecisionExamples using (L1)
  open TIE
    using (idX; revX; ℕ⊑★; five⊑; Θ₀; L1′; ΔL; ΔR; ΔLᵢ; ΔRᵢ;
           W₁; Wᵢ₁; Wᵢ₁-int; Wᵢ₁-conv; Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv;
           revX⊑revX; νL-ty; Wν; Wν-conv; W₃; R3′; p3-inst; int-ro₃;
           core₃; Wi₃-wf; vΛidX)

  -- Pieces shared by the blocks
  ------------------------------------------------------------------------

  -- `id(★) → id(★)` as a coercion and as a conversion
  id★↦ : Coercion
  id★↦ = idᵖ ★ ↦ᵖ idᵖ ★

  id★→ : Conv
  id★→ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

  -- the gen wrapper's coercion `X! → X?ℓ0`
  tagX↦ : Coercion
  tagX↦ = (` 0) ! ↦ᵖ (` 0) ？ 0

  X⇒X⊑★⇒★ : ∀ {Δ Δ′} {W : World Δ Δ′} → marksʷ W ∋ˡ emb (ηᴸʷ W) 0 := X⊑★
    → marksʷ W ⊢ embᴸ W (` 0 ⇒ ` 0) ⊑ embᴿ W (★ ⇒ ★)
  X⇒X⊑★⇒★ m = ⇒⊑⇒ (X⊑★ m) (X⊑★ m)

  ℕ⇒ℕ : ∀ {Δ Δ′} (W : World Δ Δ′) → marksʷ W ⊢ embᴸ W (`ℕ ⇒ `ℕ) ⊑ embᴿ W (`ℕ ⇒ `ℕ)
  ℕ⇒ℕ W = ⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)

  ------------------------------------------------------------------------
  -- D25 worlds: one left name c against a chain of right boundaries
  ------------------------------------------------------------------------

  -- C12–C14 B1.  The left is `[+X^αᴸ] (λx:X. x) ⟨−X → +X⟩` at
  -- ΔL = αᴸ:=ℕ.  The right nests `[+Y^β] ([−Y^β] … ⟨…⟩)⟨Y! → Y?ℓ0⟩` around
  -- the Inst boundary `[+X^αᴿ] (λx:X. x)`.  Every right `+_^β` names a
  -- right rep. var paired with αᴸ (D25), so c rejoins at each one; every
  -- right `−_^β` leaves c left-only at c⊑★ (D15).  The store pairing ϱ is
  -- global and the same in every world of the derivation.

  module _ {Ξ′ : RepCtx} {ϱ : RepRel} where

    -- outside: no names, no permission
    Wc⁰ : World ΔL (Ξ′ ∣ [])
    Wc⁰ = world⁰ 0 []↪ []↪ ϱ [] []

    -- c both-sided, its right name at rep. var β, permissions κ
    Wc² : List RVar → (β : RVar) → World ΔLᵢ (Ξ′ ∣ (β ∷ []))
    Wc² κ β = world 1 (keep []↪) (keep []↪) ϱ [] κ []

    -- c left-only (inside a right −X), permissions κ
    Wcᴸ : List RVar → World ΔLᵢ (Ξ′ ∣ [])
    Wcᴸ κ = world 1 (keep []↪) (skip []↪) ϱ [] κ []

    -- the matched TyBeta boundaries [+X^αᴸ] ∥ [+Y^0]
    Wc-bind² : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0 → Interior Wc⁰ Θ₀ Θ₀ (Wc² [] 0)
    Wc-bind² v p = record
      { int-left   = interior (changes∷ changes[]
                       (step-bind (_ , here) fresh[] ins-here))
      ; int-right  = interior (changes∷ changes[]
                       (step-bind v fresh[] ins-here))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; same-κ     = refl
      ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
      ; join-fresh = λ { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
                       ; here (there ()) _ ; (there ()) _ _ }
      }

    Wc-bind²-conv : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0
      → ConversionInterior Wc⁰ Θ₀ Θ₀ (Wc² [] 0)
    Wc-bind²-conv v p = record
      { conv-left       =
          conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
      ; conv-right      = conversion (conv-bind v conv[] fresh[] ins-here)
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
      ; conv-same-κ     = refl
      ; conv-join-cont  = λ { _ _ () _ }
      ; conv-join-fresh = λ
          { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      }

    -- a right-only −Y^β: c goes left-only (so X⊑★); κ passes through
    Wc-unbindᴿ : ∀ {κ β} → Ξ′ ∋ʳ β
      → Interior (Wc² κ β) [] (unbind 0 β ∷ []) (Wcᴸ κ)
    Wc-unbindᴿ v = record
      { int-left   = interior changes[]
      ; int-right  = interior (changes∷ changes[]
                       (step-unbind v del-here fresh[]))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; same-κ     = refl
      ; join-cont  = λ { _ (_ , ()) _ _ }
      ; join-fresh = λ { _ () _ }
      }

    -- a right-only +X^β: c rejoins αᴸ (D25); its mark is β's permission
    Wc-bindᴿ : ∀ {κ β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
      → Interior (Wcᴸ κ) [] (bind 0 β ∷ []) (Wc² κ β)
    Wc-bindᴿ v p = record
      { int-left   = interior changes[]
      ; int-right  = interior (changes∷ changes[] (step-bind v fresh[] ins-here))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; same-κ     = refl
      ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
      ; join-fresh = λ
          { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      }

  -- the types at these worlds: left-only c is X⊑★ at any κ; both-sided
  -- c is X⊑★ exactly when its right rep. var β is permitted
  c⊑★ᴸ : ∀ Ξ′ ϱ κ → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wcᴸ {Ξ′} {ϱ} κ ⟩ (★ ⇒ ★)
  c⊑★ᴸ Ξ′ ϱ κ = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

  c⊑★² : ∀ Ξ′ ϱ κ β → permit β κ ≡ X⊑★
    → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} κ β ⟩ (★ ⇒ ★)
  c⊑★² Ξ′ ϱ κ β pβ = ⇒⊑⇒ (X⊑★ (here★ pβ)) (X⊑★ (here★ pβ))

  c⊑c² : ∀ Ξ′ ϱ κ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} κ β ⟩ (` 0 ⇒ ` 0)
  c⊑c² Ξ′ ϱ κ β = ⇒⊑⇒ (X⊑X {X = 0}) (X⊑X {X = 0})

  -- THE GRANT of the gen wrapper `X! → X?ℓ0` (X bound to β): the
  -- covariant check covers the contravariant tag
  tagX↦-grants : ∀ {Ξ β} → Grants (Ξ ∣ (β ∷ [])) β tagX↦
  tagX↦-grants = gr-↦ fo-! (gr-? here)

  -- the core `[+X^αᴿ] (λx:X. x) ⟨−X → +X⟩` against λx:X. x (no
  -- permission needed: X ⊑ X), at any κ
  core⊑ : ∀ {Ξ′ ϱ κ β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} κ β)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → (Wcᴸ {Ξ′} {ϱ} κ) ∣ [] ⊢ idX ⊑ idX ⟪ bind 0 β ∷ [] , revX ⟫
        ∶ c⊑★ᴸ Ξ′ ϱ κ
  core⊑ {Ξ′} {ϱ} {κ} v p W²-wf b =
    ⊑⟪⟫ (Wc-bindᴿ v p) push-none (W²-wf)
      (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
      b (c⊑★ᴸ Ξ′ ϱ κ)

  -- permits: rep. var 0, and rep. vars 1 and 0, in a store of size ≥ 2
  p0 : ∀ {b Ξ} → All ((b ∷ Ξ) ∋ʳ_) (0 ∷ [])
  p0 = (_ , here) ∷ []

  p10 : ∀ {b b′ Ξ} → All ((b ∷ b′ ∷ Ξ) ∋ʳ_) (1 ∷ 0 ∷ [])
  p10 = (_ , there here) ∷ (_ , here) ∷ []

  -- the gen layer's right term, around M
  genLayer : RVar → Term → Term
  genLayer β M =
    (((M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩)
      ⟪ bind 0 β ∷ [] , revX ⟫

  -- one gen layer: its wrapper GRANTS β, so inside it the rejoined c is
  -- X⊑★ (the `−X^β` then makes c left-only; the inner term M is read at
  -- the larger permissions β ∷ κ)
  layer⊑ : ∀ {Ξ′ ϱ κ β M}
    → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} κ β)
    → WfWorld (Wcᴸ {Ξ′} {ϱ} (β ∷ κ))
    → (Wcᴸ {Ξ′} {ϱ} (β ∷ κ)) ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ (β ∷ κ)
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (β ∷ [])) (unbind 0 β ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (β ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → (Wcᴸ {Ξ′} {ϱ} κ) ∣ [] ⊢ idX ⊑ genLayer β M
        ∶ c⊑★ᴸ Ξ′ ϱ κ
  layer⊑ {Ξ′} {ϱ} {κ} {β} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b =
    ⊑⟪⟫ (Wc-bindᴿ v p) push-none (W²-wf)
      (⊑cast! {A = ` 0 ⇒ ` 0} tagX↦-grants
        (⊑⟪⟫ (Wc-unbindᴿ v) push-none (Wᴸ-wf)
          (⊑cast₀ M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ (β ∷ κ))) bᵤ
          (c⊑★² Ξ′ ϱ (β ∷ κ) β (permit-here β κ)))
        cₜ (c⊑c² Ξ′ ϱ κ β))
      b (c⊑★ᴸ Ξ′ ϱ κ)

  -- the outermost gen layer, matched with the left's TyBeta boundary
  outer⊑ : ∀ {Ξ′ ϱ M B′}
    → (v : Ξ′ ∋ʳ 0) → (p : ϱ ∋ᵨ 0 ⇔ 0)
    → WfWorld (Wc² {Ξ′} {ϱ} [] 0)
    → WfWorld (Wcᴸ {Ξ′} {ϱ} (0 ∷ []))
    → (Wcᴸ {Ξ′} {ϱ} (0 ∷ [])) ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ (0 ∷ [])
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → (b : BdyTy (Ξ′ ∣ []) Θ₀ (Ξ′ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX B′)
    → BdyConversionImp (Wc⁰ {Ξ′} {ϱ}) bL-ty b
    → (q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ Wc⁰ {Ξ′} {ϱ} ⟩ B′)
    → (Wc⁰ {Ξ′} {ϱ}) ∣ [] ⊢ idX ⟪ Θ₀ , revX ⟫ ⊑ genLayer 0 M ∶ q
  outer⊑ {Ξ′} {ϱ} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b bc q =
    ⟪⟫⊑⟪⟫ (Wc-bind² v p) W²-wf
      (⊑cast! {A = ` 0 ⇒ ` 0} tagX↦-grants
        (⊑⟪⟫ (Wc-unbindᴿ v) push-none (Wᴸ-wf)
          (⊑cast₀ M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ (0 ∷ []))) bᵤ
          (c⊑★² Ξ′ ϱ (0 ∷ []) 0 refl))
        cₜ (c⊑c² Ξ′ ϱ [] 0))
      bL-ty b bc q

  ------------------------------------------------------------------------
  -- C12 B1: one left rep. var, two right partners (D25)
  ------------------------------------------------------------------------

  -- C12's state 3: the right has run Inst, TyBeta (αᴿ:=★) and the source
  -- TyBeta (βᴿ:=ℕ); βᴿ is rep. var 0, αᴿ is rep. var 1
  Ξ₁₂ : RepCtx
  Ξ₁₂ = bindR `ℕ ∷ bindR ★ ∷ []

  -- αᴸ (0) is paired with both βᴿ (0) and αᴿ (1)
  ϱ₁₂ : RepRel
  ϱ₁₂ = (0 , 0) ∷ (0 , 1) ∷ []

  B12x B12 : Term
  B12x = idX ⟪ bind 0 1 ∷ [] , revX ⟫
  B12  = genLayer 0 B12x

  C12-R₃ : Term
  C12-R₃ = B12 · $ 5

  C12-L₁-state : head (drop 1 (evalTerms 10 C12-L-⊢)) ≡ just L1′
  C12-L₁-state = refl

  C12-R₃-state : head (drop 3 (evalTerms 24 C12-R-⊢)) ≡ just C12-R₃
  C12-R₃-state = refl

  -- the right contexts: outside, and with the one name at rep. var β
  ΔR₁₂ : Ctxᵗ
  ΔR₁₂ = Ξ₁₂ ∣ []

  ΔR₁₂^ : RVar → Ctxᵗ
  ΔR₁₂^ β = Ξ₁₂ ∣ (β ∷ [])

  -- typing side premises, read off `tc`
  B12-ty : BdyTy ΔR₁₂ Θ₀ (ΔR₁₂^ 0) (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  B12-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂} {M = B12}))))

  B12x-ty : BdyTy ΔR₁₂ (bind 0 1 ∷ []) (ΔR₁₂^ 1) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  B12x-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂} {M = B12x}))))

  id★↦-ty : ∀ {Ξ} → CastTy (Ξ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  -- one gen layer's two inner pieces
  unbTerm tagTerm : RVar → Term → Term
  unbTerm β M = (M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫
  tagTerm β M = unbTerm β M ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

  B12ᵤ-ty : BdyTy (ΔR₁₂^ 0) (unbind 0 0 ∷ []) ΔR₁₂ (★ ⇒ ★) id★→ (★ ⇒ ★)
  B12ᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂^ 0} {M = unbTerm 0 B12x}))))

  B12ₜ-ty : CastTy (ΔR₁₂^ 0) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B12ₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = ΔR₁₂^ 0} {M = tagTerm 0 B12x})))

  -- the worlds of the derivation
  W₁₂ : World ΔL ΔR₁₂
  W₁₂ = Wc⁰ {Ξ₁₂} {ϱ₁₂}

  -- WfWorld for the four worlds of c12-b1: outside; c both-sided naming
  -- (αᴸ, βᴿ); c left-only; c both-sided naming (αᴸ, αᴿ).  Each has
  -- ϱᵍ = ϱ₁₂ and ϱˡ = ∅.
  module Wf₁₂ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₂ ∣ nsR)
    W = world n η η′ ϱ₁₂ [] κ []

    -- both pairs agree: ℕ ⊑ ℕ and ℕ ⊑ ★
    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())

  W₁₂-wf : WfWorld W₁₂
  W₁₂-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[]) [] [] []
    where open Wf₁₂ 0 []↪ []↪ []

  W₁₂²-wf : ∀ {κ} → All (Ξ₁₂ ∋ʳ_) κ → WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} κ 0)
  W₁₂²-wf {κ} ps = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] ps
    where open Wf₁₂ 1 (keep []↪) (keep []↪) κ

  W₁₂ᴸ-wf : ∀ {κ} → All (Ξ₁₂ ∋ʳ_) κ → WfWorld (Wcᴸ {Ξ₁₂} {ϱ₁₂} κ)
  W₁₂ᴸ-wf {κ} ps = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] ps
    where open Wf₁₂ 1 (keep []↪) (skip []↪) κ

  W₁₂ˣ-wf : ∀ {κ} → All (Ξ₁₂ ∋ʳ_) κ → WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} κ 1)
  W₁₂ˣ-wf {κ} ps = wf-world (both (inj₁ (there⇔ here⇔)) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] ps
    where open Wf₁₂ 1 (keep []↪) (keep []↪) κ

  c12-b1 : W₁₂ ∣ [] ⊢ L1′ ⊑ C12-R₃ ∶ ι⊑ι base-ℕ
  c12-b1 =
    ·⊑·
      (outer⊑ (_ , here) here⇔ (W₁₂²-wf []) (W₁₂ᴸ-wf p0)
        (core⊑ (_ , there here) (there⇔ here⇔) (W₁₂ˣ-wf p0) B12x-ty)
        id★↦-ty B12ᵤ-ty B12ₜ-ty B12-ty
        (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₁₂))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- Shared pieces for the right-led blocks
  ------------------------------------------------------------------------

  -- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★), in any world (the plain
  -- index, which is `_⊑ᵂ⟨_⟩_` at a world with no pending name)
  ∀id⊑★ : ∀ {Δ Δ′} (W : World Δ Δ′)
    → marksʷ W ⊢ embᴸ W (`∀ (` 0 ⇒ ` 0)) ⊑ embᴿ W (★ ⇒ ★)
  ∀id⊑★ W = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  ∀id⊑∀id : ∀ {Δ Δ′} (W : World Δ Δ′)
    → marksʷ W ⊢ embᴸ W (`∀ (` 0 ⇒ ` 0)) ⊑ embᴿ W (`∀ (` 0 ⇒ ` 0))
  ∀id⊑∀id W = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

  ★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → marksʷ W ⊢ embᴸ W (★ ⇒ ★) ⊑ embᴿ W (★ ⇒ ★)
  ★⇒★ W = ⇒⊑⇒ ★⊑★ ★⊑★

  ℕ⇒ℕ⊑★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → marksʷ W ⊢ embᴸ W (`ℕ ⇒ `ℕ) ⊑ embᴿ W (★ ⇒ ★)
  ℕ⇒ℕ⊑★⇒★ W = ⇒⊑⇒ ℕ⊑★ ℕ⊑★

  id★→⊑id★→ : ∀ {Δ Δ′} {W : World Δ Δ′} → ConvImp W id★→ id★→
  id★→⊑id★→ =
    conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where
    i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★))

  -- `[−X^α] (λx:★. x) ⟨id(★) → id(★)⟩`: the gen value's crossed body, and
  -- the gen wrapper `(…)⟨X! → X?ℓ0⟩^[X:★∼X]` over it (on the left this is
  -- `inst_X` of the gen value, `inst-gen`; on the right it is what the
  -- right's TyBeta left inside its boundary)
  I★⁻ I★gen : Term
  I★⁻ = I★ ⟪ unbind 0 0 ∷ [] , id★→ ⟫
  I★gen = I★⁻ ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

  I★⁻-crossed : crossΛᴹ I★ (srcᵖ genI) ≡ I★⁻
  I★⁻-crossed = refl

  -- the right's state after Inst and TyBeta (αᴿ:=★), Cg-R = C2-R state 2
  Bg Cg-R₂ : Term
  Bg = I★gen ⟪ Θ₀ , revX ⟫
  Cg-R₂ = (Bg ⟨ [] ∣ id★↦ ⟩) · dyn 5

  Cg-R₂-state : head (drop 2 (evalTerms 21 Cg-R-⊢)) ≡ just Cg-R₂
  Cg-R₂-state = refl

  -- the right contexts: the exterior (αᴿ:=★ at rep. var 0), inside the
  -- Inst boundary `+X^αᴿ`, inside the gen value's `−X^αᴿ`
  ΔRₓ : Ctxᵗ
  ΔRₓ = reps ΔR ∣ (0 ∷ [])

  Bg-ty : BdyTy ΔR (bind 0 0 ∷ []) ΔRₓ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  Bg-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Bg}))))

  I★⁻ᴿ-ty : BdyTy ΔRₓ (unbind 0 0 ∷ []) ΔR (★ ⇒ ★) id★→ (★ ⇒ ★)
  I★⁻ᴿ-ty =
    proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★⁻}))))

  tagᴿ-ty : CastTy ΔRₓ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᴿ-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★gen})))

  id★↦ᴿ-ty : CastTy ΔR [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦ᴿ-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  ΛidX-⊢ : empty ∣ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  ΛidX-⊢ = tc

  ------------------------------------------------------------------------
  -- Cg's right-led block X0 (D27: ⊑⟪⟫ pushes X, Λ⊑ pops it; the gen
  -- wrapper's grant makes the popped X X⊑★)
  ------------------------------------------------------------------------

  -- the popped world: the left Λ's abstract rep. var paired
  -- LEXICALLY with αᴿ:=★; the shared name's mark is αᴿ's permission
  Wg⁺ : World (underΛ empty) ΔRₓ
  Wg⁺ = W₃ ⊕⁺^ 0

  -- the popped world with αᴿ permitted (inside the gen wrapper's grant)
  Wg⁺¹ : World (underΛ empty) ΔRₓ
  Wg⁺¹ = record Wg⁺ { κʷ = 0 ∷ [] }

  -- inside the right's −X^αᴿ: X is left-only, X⊑★
  Wg⁻ : List RVar → World (underΛ empty) ΔR
  Wg⁻ κ = world 1 (keep []↪) (skip []↪) [] ((0 , 0) ∷ []) κ []

  Wg⁻-int : ∀ {κ} → Interior (record Wg⁺ { κʷ = κ }) [] (unbind 0 0 ∷ [])
    (Wg⁻ κ)
  Wg⁻-int = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    }

  -- WfWorld for the worlds of the lexical pair (aᴸ_ΛY, αᴿ:=★): the left
  -- member abstract, the right member at ★ (`abst-★`)
  module WfΛ★ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((abstR ∷ []) ∣ nsL) ((bindR ★ ∷ []) ∣ nsR)
    W = world n η η′ [] ((0 , 0) ∷ []) κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-★ r-here r-here
    agree (inj₂ (there⇔ ()))


  Wg⁺-wf : WfWorld Wg⁺
  Wg⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] []
    where open WfΛ★ 1 (keep []↪) (keep []↪) []

  Wg⁻-wf : ∀ {κ} → All ((bindR ★ ∷ []) ∋ʳ_) κ → WfWorld (Wg⁻ κ)
  Wg⁻-wf {κ} ps = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] ps
    where open WfΛ★ 1 (keep []↪) (skip []↪) κ

  -- the pop's premise: the left's λx:X.x against the right's gen value,
  -- at the popped world Wg⁺ (the right's tag cast, then its −X^αᴿ)
  cg-body : record (W₃ ⊕ʳ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ I ⊑ I★gen
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  cg-body =
    Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (⊑cast! tagX↦-grants
        (⊑⟪⟫ Wg⁻-int push-none (Wg⁻-wf p0)
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
          I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺¹} here))
        tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
      (⇒⊑⇒ X⊑X X⊑X)

  -- ⊑⟪⟫ pushes X, Λ⊑ pops it first; then the right's tag cast and −X
  cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
  cg-x0 =
    ·⊑·
      (ν⊑
        (⊑cast₀
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vΛidX)) Wi₃-wf cg-body
            Bg-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
      five⊑

  ------------------------------------------------------------------------
  -- C2's right-led block X0 (D27: ⊑⟪⟫ pushes X, the left gen cast pops
  -- it, `cc-gen`)
  ------------------------------------------------------------------------

  I★genI : Term
  I★genI = I★ ⟨ [] ∣ genI ⟩

  I★genI-⊢ : empty ∣ [] ⊢ I★genI ⦂ `∀ (` 0 ⇒ ` 0)
  I★genI-⊢ = tc

  C2-L-ν : Term
  C2-L-ν = ν `ℕ · I★genI ⟨ revX ⟩

  C2-L-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C2-L-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C2-L-ν})))

  C2-L₀-is : C2-L ≡ C2-L-ν · $ 5
  C2-L₀-is = refl

  unbind₀-int : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ (unbind 0 0 ∷ [])
    ⇒ ((b ∷ Ξ) ∣ [])
  unbind₀-int = interior (changes∷ changes[]
    (step-unbind (_ , here) del-here fresh[]))

  unbind₀-conv : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ (unbind 0 0 ∷ [])
    ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  unbind₀-conv = conversion (conv-unbind (_ , here) conv[])

  -- the right's `−X^αᴿ` alone: X goes away (the left has no name here)
  IntN : ∀ {κ} → Interior (record (W₃ ⊕ʳ^ 0) { κʷ = κ }) []
    (unbind 0 0 ∷ []) (record W₃ { κʷ = κ })
  IntN = record
    { int-left   = interior changes[]
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- the conversion contexts skip the unbinds: they are the exterior
  unbind₀-conv-self : ∀ {b b′ Ξ Ξ′}
      {W : World ((b ∷ Ξ) ∣ (0 ∷ [])) ((b′ ∷ Ξ′) ∣ (0 ∷ []))}
    → ConversionInterior W (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W
  unbind₀-conv-self {W = W} = record
    { conv-left       = unbind₀-conv
    ; conv-right      = unbind₀-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  W₃-wf : ∀ {κ} → All (reps ΔR ∋ʳ_) κ → WfWorld (record W₃ { κʷ = κ })
  W₃-wf ps = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) }) (λ { _ (_ , ()) }) [] [] ps

  vI★genI : Value I★genI
  vI★genI = V-simple (S-cast (V-simple S-ƛ) I-gen)

  genIᴸ-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genIᴸ-ty = proj₂ (proj₂ (cast-inv {Γ = []} I★genI-⊢))

  -- the left gen cast against the right's tag cast: ⊑cast₀ first (Y ⊑ ★
  -- by the pending name's X⊑★), then cast⊑ POPS at the gen (`cc-gen`):
  -- the left's λx:★.x is related at the UNOPENED world W₃, against the
  -- right's `[−X^αᴿ] λx:★.x`
  c2-body : record (W₃ ⊕ʳ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ I★genI ⊑ I★gen
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  c2-body =
    ⊑cast! tagX↦-grants
      (cast⊑ (cc-gen (V-simple S-ƛ))
        (⊑⟪⟫ IntN push-none (W₃-wf p0)
          (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ)) I★⁻ᴿ-ty (⇒⊑⇒ ★⊑★ ★⊑★))
        genIᴸ-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X)

  c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
  c2-x0 =
    ·⊑·
      (ν⊑
        (⊑cast₀
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vI★genI)) Wi₃-wf c2-body
            Bg-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
      five⊑

  ------------------------------------------------------------------------
  -- C2 B6 and B7 (D15: a multi-entry boundary, with its conversion
  -- premise)
  ------------------------------------------------------------------------

  -- the multi-entry scope (−X, +X): head last, so `unbind` acts first
  Θ⁻⁺ : Boundary
  Θ⁻⁺ = bind 0 0 ∷ unbind 0 0 ∷ []

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  -- `[−X^α] m ⟨−X⟩`, for the leaf m = 5 (left) or 5⟨ℕ!⟩ (right)
  seal-leaf : Term → Term
  seal-leaf m = m ⟪ unb₀ , tail (seal 0) ⟫

  tagX untagX : Coercion
  tagX   = (` 0) !
  untagX = (` 0) ？ 0

  C2-B6 C2-B7 : Term → Term
  C2-B6 m =
    (((seal-leaf m ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , tail (mid (id ★)) ⟫)
      ⟨ ★∼X ∷ [] ∣ untagX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  C2-B7 m =
    (((seal-leaf m ⟪ Θ⁻⁺ , tail (mid (id (` 0))) ⟫) ⟨ X∼★ ∷ [] ∣ tagX ⟩)
      ⟨ ★∼X ∷ [] ∣ untagX ⟩) ⟪ Θ₀ , unseal 0 ⟫

  C2-L₆-state : head (drop 6 (evalTerms 16 C2-L-⊢)) ≡ just (C2-B6 ($ 5))
  C2-L₆-state = refl

  C2-R₉-state : head (drop 9 (evalTerms 21 C2-R-⊢))
    ≡ just (C2-B6 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩)
  C2-R₉-state = refl

  C2-L₇-state : head (drop 7 (evalTerms 16 C2-L-⊢)) ≡ just (C2-B7 ($ 5))
  C2-L₇-state = refl

  C2-R₁₀-state : head (drop 10 (evalTerms 21 C2-R-⊢))
    ≡ just (C2-B7 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩)
  C2-R₁₀-state = refl

  -- the worlds: W₁ outside (ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}), Wᵢ₁ inside the outer
  -- boundaries (X both-sided, X⊑X: no permission); the final interior
  -- world of (−X, +X) ∥ (−X, +X) is Wᵢ₁ again (X continues, keeps X⊑X);
  -- inside the two −X, W₁ again (no names)
  Wᵢ₁-unb : Interior Wᵢ₁ unb₀ unb₀ W₁
  Wᵢ₁-unb = record
    { int-left   = unbind₀-int
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  W₁-wf : WfWorld W₁
  W₁-wf = wf-world joint[] agree (namedᴸ-≤1 W₁ ≤1-[]) (namedᴿ-≤1 W₁ ≤1-[]) [] [] []
    where
    agree : ∀ {α β} → Paired W₁ α β → Agree W₁ α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Θ⁻⁺-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ Θ⁻⁺ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ⁻⁺-int = interior (changes∷
    (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
    (step-bind (_ , here) fresh[] ins-here))

  Θ⁻⁺-conv : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ Θ⁻⁺ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ⁻⁺-conv = conversion (conv-bind-live (_ , here)
    (conv-unbind (_ , here) conv[]) here)

  -- D15: X goes away and comes back within the entries; only the final
  -- interior world is given, and X keeps its mark
  Wᵢ₁-Θ⁻⁺ : Interior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
  Wᵢ₁-Θ⁻⁺ = record
    { int-left   = Θ⁻⁺-int
    ; int-right  = Θ⁻⁺-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
        ; (_ , here) (_ , there ()) _ _
        ; (_ , there ()) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there ()) _ ; (there ()) _ _ }
    }

  Wᵢ₁-Θ⁻⁺-conv : ConversionInterior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
  Wᵢ₁-Θ⁻⁺-conv = record
    { conv-left       = Θ⁻⁺-conv
    ; conv-right      = Θ⁻⁺-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  -- typing side premises
  leafᴸ-ty : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  leafᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = seal-leaf ($ 5)}))))

  leafᴿ-ty : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
  leafᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = seal-leaf (dyn 5)}))))

  tag-ty : ∀ {R} → CastTy ((bindR R ∷ []) ∣ (0 ∷ [])) (X∼★ ∷ []) tagX (` 0) ★
  tag-ty = cast-ty (⊢tag-var (_ , here) here tag-dyn) refl

  untag-ty : ∀ {R} → CastTy ((bindR R ∷ []) ∣ (0 ∷ [])) (★∼X ∷ []) untagX ★ (` 0)
  untag-ty = cast-ty (⊢check-var (_ , here) here check-dyn) refl

  -- B6's middle boundary `[−X, +X] (…)⟨X!⟩ ⟨id(★)⟩`
  mid6 : Term → Term
  mid6 m = (seal-leaf m ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , tail (mid (id ★)) ⟫

  mid6ᴸ-ty : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ ★ (tail (mid (id ★))) ★
  mid6ᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = mid6 ($ 5)}))))

  mid6ᴿ-ty : BdyTy ΔRᵢ Θ⁻⁺ ΔRᵢ ★ (tail (mid (id ★))) ★
  mid6ᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = mid6 (dyn 5)}))))

  -- B7's middle boundary `[−X, +X] (…) ⟨id(X)⟩`
  mid7 : Term → Term
  mid7 m = seal-leaf m ⟪ Θ⁻⁺ , tail (mid (id (` 0))) ⟫

  mid7ᴸ-ty : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0) (tail (mid (id (` 0)))) (` 0)
  mid7ᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = mid7 ($ 5)}))))

  mid7ᴿ-ty : BdyTy ΔRᵢ Θ⁻⁺ ΔRᵢ (` 0) (tail (mid (id (` 0)))) (` 0)
  mid7ᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = mid7 (dyn 5)}))))

  -- the outer boundary `[+X] (…) ⟨+X⟩`
  outᴸ-ty : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  outᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C2-B6 ($ 5)}))))

  outᴿ-ty : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
  outᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = C2-B6 (dyn 5)}))))

  id★ᴿ-ty : CastTy ΔR [] (idᵖ ★) ★ ★
  id★ᴿ-ty = cast-ty (⊢id atom-★ wf-★) refl

  X⊑X₀ : ` 0 ⊑ᵂ⟨ Wᵢ₁ ⟩ ` 0
  X⊑X₀ = X⊑X

  -- the leaf `[−X] 5 ⟨−X⟩ ⊑ [−X] 5⟨ℕ!⟩ ⟨−X⟩`, with `−X ⊑ −X`
  leaf⊑ : Wᵢ₁ ∣ [] ⊢ seal-leaf ($ 5) ⊑ seal-leaf (dyn 5) ∶ X⊑X₀
  leaf⊑ =
    ⟪⟫⊑⟪⟫ Wᵢ₁-unb W₁-wf five⊑ leafᴸ-ty leafᴿ-ty
      (Wᵢ₁ , unbind₀-conv-self , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  c2-b6 : W₁ ∣ [] ⊢ C2-B6 ($ 5) ⊑ C2-B6 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩ ∶ ℕ⊑★
  c2-b6 =
    ⊑cast₀
      (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
        (cast⊑cast
          (⟪⟫⊑⟪⟫ Wᵢ₁-Θ⁻⁺ Wᵢ₁-wf
            (cast⊑cast leaf⊑ tag-ty tag-ty ★⊑★)
            mid6ᴸ-ty mid6ᴿ-ty
            (Wᵢ₁ , Wᵢ₁-Θ⁻⁺-conv , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★)))
            ★⊑★)
          untag-ty untag-ty X⊑X)
        outᴸ-ty outᴿ-ty
        (Wᵢ₁ , Wᵢ₁-conv , conv-unseal⊑unseal refl) ℕ⊑★)
      id★ᴿ-ty ℕ⊑★

  c2-b7 : W₁ ∣ [] ⊢ C2-B7 ($ 5) ⊑ C2-B7 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩ ∶ ℕ⊑★
  c2-b7 =
    ⊑cast₀
      (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
        (cast⊑cast
          (cast⊑cast
            (⟪⟫⊑⟪⟫ Wᵢ₁-Θ⁻⁺ Wᵢ₁-wf
              leaf⊑ mid7ᴸ-ty mid7ᴿ-ty
              (Wᵢ₁ , Wᵢ₁-Θ⁻⁺-conv ,
               conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id X⊑X)))
              X⊑X)
            tag-ty tag-ty ★⊑★)
          untag-ty untag-ty X⊑X)
        outᴸ-ty′ outᴿ-ty′
        (Wᵢ₁ , Wᵢ₁-conv , conv-unseal⊑unseal refl) ℕ⊑★)
      id★ᴿ-ty ℕ⊑★
    where
    outᴸ-ty′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
    outᴸ-ty′ = proj₂ (proj₂ (proj₂
      (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C2-B7 ($ 5)}))))
    outᴿ-ty′ : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
    outᴿ-ty′ = proj₂ (proj₂ (proj₂
      (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = C2-B7 (dyn 5)}))))

  ------------------------------------------------------------------------
  -- C13 B1 and C14 B1: two and three right partners (D25)
  ------------------------------------------------------------------------

  -- C13's state 4: two Inst/TyBeta pairs on the right, βᴿ:=★ (0) and
  -- αᴿ:=★ (1); the store pairing is ϱ₁₂ again, now ℕ ⊑ ★ twice
  Ξ₁₃ : RepCtx
  Ξ₁₃ = bindR ★ ∷ bindR ★ ∷ []

  C13-R₄ : Term
  C13-R₄ = (B12 ⟨ [] ∣ id★↦ ⟩) · dyn 5

  C13-R₄-state : head (drop 4 (evalTerms 29 C13-R-⊢)) ≡ just C13-R₄
  C13-R₄-state = refl

  B13-ty : BdyTy (Ξ₁₃ ∣ []) Θ₀ (Ξ₁₃ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  B13-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ []} {M = B12}))))

  B13x-ty : BdyTy (Ξ₁₃ ∣ []) (bind 0 1 ∷ []) (Ξ₁₃ ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX
    (★ ⇒ ★)
  B13x-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ []} {M = B12x}))))

  B13ᵤ-ty : BdyTy (Ξ₁₃ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ₁₃ ∣ []) (★ ⇒ ★) id★→
    (★ ⇒ ★)
  B13ᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ (0 ∷ [])} {M = unbTerm 0 B12x}))))

  B13ₜ-ty : CastTy (Ξ₁₃ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B13ₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ (0 ∷ [])} {M = tagTerm 0 B12x})))

  W₁₃ : World ΔL (Ξ₁₃ ∣ [])
  W₁₃ = Wc⁰ {Ξ₁₃} {ϱ₁₂}

  module Wf₁₃ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₃ ∣ nsR)
    W = world n η η′ ϱ₁₂ [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())


  W₁₃²-wf : ∀ {β κ}
    → ϱ₁₂ ∋ᵨ 0 ⇔ β → All (Ξ₁₃ ∋ʳ_) κ
    → WfWorld (Wc² {Ξ₁₃} {ϱ₁₂} κ β)
  W₁₃²-wf {κ = κ} p ps = wf-world (both (inj₁ p) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] ps
    where open Wf₁₃ 1 (keep []↪) (keep []↪) κ

  W₁₃ᴸ-wf : ∀ {κ} → All (Ξ₁₃ ∋ʳ_) κ → WfWorld (Wcᴸ {Ξ₁₃} {ϱ₁₂} κ)
  W₁₃ᴸ-wf {κ} ps = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] ps
    where open Wf₁₃ 1 (keep []↪) (skip []↪) κ

  c13-b1 : W₁₃ ∣ [] ⊢ L1′ ⊑ C13-R₄ ∶ ℕ⊑★
  c13-b1 =
    ·⊑·
      (⊑cast₀
        (outer⊑ (_ , here) here⇔ (W₁₃²-wf here⇔ []) (W₁₃ᴸ-wf p0)
          (core⊑ (_ , there here) (there⇔ here⇔)
            (W₁₃²-wf (there⇔ here⇔) p0) B13x-ty)
          id★↦-ty B13ᵤ-ty B13ₜ-ty B13-ty
          (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ W₁₃))
        id★↦-ty (ℕ⇒ℕ⊑★⇒★ W₁₃))
      five⊑

  -- C14's state 5: γᴿ:=ℕ (0) from the source ν, βᴿ:=★ (1) and αᴿ:=★ (2)
  -- from the two Inst/TyBeta pairs; αᴸ has three right partners
  Ξ₁₄ : RepCtx
  Ξ₁₄ = bindR `ℕ ∷ bindR ★ ∷ bindR ★ ∷ []

  ϱ₁₄ : RepRel
  ϱ₁₄ = (0 , 0) ∷ (0 , 1) ∷ (0 , 2) ∷ []

  B14x B14y B14 : Term
  B14x = idX ⟪ bind 0 2 ∷ [] , revX ⟫
  B14y = genLayer 1 B14x
  B14  = genLayer 0 B14y

  C14-R₅ : Term
  C14-R₅ = B14 · $ 5

  C14-R₅-state : head (drop 5 (evalTerms 38 C14-R-⊢)) ≡ just C14-R₅
  C14-R₅-state = refl

  B14-ty : BdyTy (Ξ₁₄ ∣ []) Θ₀ (Ξ₁₄ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  B14-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14}))))

  B14ᵤ-ty : BdyTy (Ξ₁₄ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ₁₄ ∣ []) (★ ⇒ ★) id★→
    (★ ⇒ ★)
  B14ᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (0 ∷ [])} {M = unbTerm 0 B14y}))))

  B14ₜ-ty : CastTy (Ξ₁₄ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B14ₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (0 ∷ [])} {M = tagTerm 0 B14y})))

  B14y-ty : BdyTy (Ξ₁₄ ∣ []) (bind 0 1 ∷ []) (Ξ₁₄ ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX
    (★ ⇒ ★)
  B14y-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14y}))))

  B14yᵤ-ty : BdyTy (Ξ₁₄ ∣ (1 ∷ [])) (unbind 0 1 ∷ []) (Ξ₁₄ ∣ []) (★ ⇒ ★) id★→
    (★ ⇒ ★)
  B14yᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (1 ∷ [])} {M = unbTerm 1 B14x}))))

  B14yₜ-ty : CastTy (Ξ₁₄ ∣ (1 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B14yₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (1 ∷ [])} {M = tagTerm 1 B14x})))

  B14x-ty : BdyTy (Ξ₁₄ ∣ []) (bind 0 2 ∷ []) (Ξ₁₄ ∣ (2 ∷ [])) (` 0 ⇒ ` 0) revX
    (★ ⇒ ★)
  B14x-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14x}))))

  W₁₄ : World ΔL (Ξ₁₄ ∣ [])
  W₁₄ = Wc⁰ {Ξ₁₄} {ϱ₁₄}

  -- WfWorld for the outer world and the three both-sided worlds of
  -- c14-b1: αᴸ is paired with γᴿ:=ℕ, βᴿ:=★ and αᴿ:=★
  module Wf₁₄ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₄ ∣ nsR)
    W = world n η η′ ϱ₁₄ [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ here⇔))) =
      rep-rep r-here (r-there (r-there r-here)) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ (there⇔ ()))))
    agree (inj₂ ())


  W₁₄-wf : WfWorld W₁₄
  W₁₄-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[]) [] [] []
    where open Wf₁₄ 0 []↪ []↪ []

  W₁₄²-wf : ∀ {β κ} → ϱ₁₄ ∋ᵨ 0 ⇔ β → All (Ξ₁₄ ∋ʳ_) κ
    → WfWorld (Wc² {Ξ₁₄} {ϱ₁₄} κ β)
  W₁₄²-wf {κ = κ} p ps = wf-world (both (inj₁ p) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] ps
    where open Wf₁₄ 1 (keep []↪) (keep []↪) κ

  W₁₄ᴸ-wf : ∀ {κ} → All (Ξ₁₄ ∋ʳ_) κ → WfWorld (Wcᴸ {Ξ₁₄} {ϱ₁₄} κ)
  W₁₄ᴸ-wf {κ} ps = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] ps
    where open Wf₁₄ 1 (keep []↪) (skip []↪) κ

  c14-b1 : W₁₄ ∣ [] ⊢ L1′ ⊑ C14-R₅ ∶ ι⊑ι base-ℕ
  c14-b1 =
    ·⊑·
      (outer⊑ (_ , here) here⇔ (W₁₄²-wf here⇔ []) (W₁₄ᴸ-wf p0)
        (layer⊑ (_ , there here) (there⇔ here⇔)
          (W₁₄²-wf (there⇔ here⇔) p0) (W₁₄ᴸ-wf p10)
          (core⊑ (_ , there (there here)) (there⇔ (there⇔ here⇔))
            (W₁₄²-wf (there⇔ (there⇔ here⇔)) p10) B14x-ty)
          id★↦-ty B14yᵤ-ty B14yₜ-ty B14y-ty)
        id★↦-ty B14ᵤ-ty B14ₜ-ty B14-ty
        (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₁₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- The initial blocks B0
  ------------------------------------------------------------------------

  instI-ty : CastTy empty [] instI (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instI-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩})))

  genI-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = I★genI})))

  instI∘genI-ty : CastTy empty [] instI (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instI∘genI-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = empty} {M = I★genI ⟨ [] ∣ instI ⟩})))

  genI∘instI-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genI∘instI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩})))

  -- the left core Λ against the right core Λ: Λ⊑Λ pairs their abstract
  -- rep. vars lexically
  ΛI⊑ΛI : ∅ʷ ∣ [] ⊢ I ⊑ I ∶ (∀id⊑∀id ∅ʷ)
  ΛI⊑ΛI = Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
    (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ)) (∀id⊑∀id ∅ʷ)

  -- the premise world of Λ⊑Λ: (aᴸ_ΛY, aᴿ_ΛX) ∈ ϱˡ, both abstract
  ΛΛ-wf : WfWorld (∅ʷ ⊕²)
  ΛΛ-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 (∅ʷ ⊕²) ≤1-∷[]) (namedᴿ-≤1 (∅ʷ ⊕²) ≤1-∷[]) [] [] []
    where
    agree : ∀ {α β} → Paired (∅ʷ ⊕²) α β → Agree (∅ʷ ⊕²) α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-abst r-here r-here
    agree (inj₂ (there⇔ ()))

  -- Ch B0: Λ⊑Λ under the right's inst cast; the left ν is one-sided
  ch-b0 : ∅ʷ ∣ [] ⊢ Ch-L ⊑ Ch-R ∶ ℕ⊑★
  ch-b0 =
    ·⊑· (ν⊑ (⊑cast₀ ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ)) five⊑

  -- Cg B0: Λ⊑ (Y left-only at X⊑★) under the right's gen and inst casts
  cg-b0 : ∅ʷ ∣ [] ⊢ Cg-L ⊑ Cg-R ∶ ℕ⊑★
  cg-b0 =
    ·⊑·
      (ν⊑
        (⊑cast₀
          (⊑cast₀
            (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
            genI-ty (∀id⊑∀id ∅ʷ))
          instI∘genI-ty (∀id⊑★ ∅ʷ))
        ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ))
      five⊑

  -- C2 B0: the two gen casts matched by cast⊑cast; the right's inst
  -- cast by ⊑cast; the left ν is one-sided
  c2-b0 : ∅ʷ ∣ [] ⊢ C2-L ⊑ C2-R ∶ ℕ⊑★
  c2-b0 =
    ·⊑·
      (ν⊑
        (⊑cast₀
          (cast⊑cast (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ)) genI-ty genI-ty (∀id⊑∀id ∅ʷ))
          instI∘genI-ty (∀id⊑★ ∅ʷ))
        ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ))
      five⊑

  -- C12 B0: ν⊑ν (its two rep. vars paired lexically in the conversion
  -- world), the right's gen and inst casts by ⊑cast, Λ⊑Λ
  C12-ν : Term
  C12-ν = ν `ℕ · (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩

  C12-R-is : C12-R ≡ C12-ν · $ 5
  C12-R-is = refl

  C12-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C12-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C12-ν})))

  c12-b0 : ∅ʷ ∣ [] ⊢ C12-L ⊑ C12-R ∶ ι⊑ι base-ℕ
  c12-b0 =
    ·⊑·
      (ν⊑ν (⊑cast₀ (⊑cast₀ ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) genI∘instI-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty C12-ν-ty (Wν , Wν-conv , revX⊑revX refl) (ℕ⇒ℕ ∅ʷ))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- Ch's right-led block X0 (= P3's block, push and pop) and Ch B1
  ------------------------------------------------------------------------

  Ch-R₂-state : head (drop 2 (evalTerms 15 Ch-R-⊢)) ≡ just R3′
  Ch-R₂-state = refl

  -- a push and a pop (X⊑X): (aᴸ_ΛY, αᴿ:=★) ∈ ϱˡ in the popped world
  -- W₃ ⊕⁺^ 0
  ch-x0 : W₃ ∣ [] ⊢ Ch-L ⊑ R3′ ∶ ℕ⊑★
  ch-x0 = p3-inst

  -- ch-x0's popped world is Wg⁺ (the same world as Cg's X0)
  ch-x0-world : W₃ ⊕⁺^ 0 ≡ Wg⁺
  ch-x0-world = refl

  -- Ch B1: after the left's TyBeta the lexical pair is global,
  -- ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}
  Ch-L₁-state : head (drop 1 (evalTerms 10 Ch-L-⊢)) ≡ just L1′
  Ch-L₁-state = refl

  ch-b1 : W₁ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
  ch-b1 =
    ·⊑·
      (⊑cast₀
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
          (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
          bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
      five⊑

  ------------------------------------------------------------------------
  -- C12's right-led block X0: ν⊑ν around P3's core (push X, pop X; D27)
  ------------------------------------------------------------------------

  -- C12's state 2: the right's Inst and TyBeta (αᴿ:=★) have run inside
  -- the source ν, which has not
  C12-ν₂ C12-R₂ : Term
  C12-ν₂ = ν `ℕ · ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩
  C12-R₂ = C12-ν₂ · $ 5

  C12-R₂-state : head (drop 2 (evalTerms 24 C12-R-⊢)) ≡ just C12-R₂
  C12-R₂-state = refl

  C12-ν₂-ty : NuTy ΔR `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C12-ν₂-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔR} {M = C12-ν₂})))

  genIᴿ-ty : CastTy ΔR [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genIᴿ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔR} {M = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ⟨ [] ∣ genI ⟩})))

  -- the ν conversion world: the two ν-bound rep. vars paired lexically
  Wν₂ : World ((bindR `ℕ ∷ []) ∣ (0 ∷ [])) ((bindR `ℕ ∷ reps ΔR) ∣ (0 ∷ []))
  Wν₂ = world⁰ 1 (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) []

  Wν₂-conv : ConversionInterior (underν² `ℕ `ℕ W₃) Θ₀ Θ₀ Wν₂
  Wν₂-conv = record
    { conv-left       = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-right      = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
  c12-x0 =
    ·⊑·
      (ν⊑ν
        (⊑cast₀
          (⊑cast₀
            core₃
            id★↦ᴿ-ty (∀id⊑★ W₃))
          genIᴿ-ty (∀id⊑∀id W₃))
        (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl) (ℕ⇒ℕ W₃))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

------------------------------------------------------------------------
-- 9. HEAD's TermImprecisionRegressionExamples (K), §1-§4 ported (the
-- Evolve-based obligations of its §5 are not: they read HEAD's world).
-- No permission anywhere: the pending Y and the shared X are X⊑X,
-- and every index of K uses only X ⊑ X at them
------------------------------------------------------------------------

module K where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I; instI)
  open TIE using (idX; revX; Θ₀; ΔL; ΔLᵢ; ∀X⇒X; int₀; conv₀; Wν; Wν-conv)
  open Rebase using (id★↦; ∀id⊑★; ∀id⊑∀id)

  ------------------------------------------------------------------------
  -- 1. The programs and their runs
  ------------------------------------------------------------------------

  --   L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
  --   R  (λf:★→★.    f) (K[ℕ]⟨inst⟩)

  KK : Term
  KK = Λ I

  cId cK : Conv
  cId = ⌞ ⌞ id (` 0) ⌟ ↦ ⌞ id (` 0) ⌟ ⌟
  cK  = ⌞ `∀ cId ⌟

  -- VL: the left's ∀-boundary value; Nk = inst_Y(VL); Bm: the merged
  -- boundary `[+Y^β, +X^αᴿ] λx:Y.x`
  VL Nk Rarg₃ Bm RF : Term
  VL    = I ⟪ Θ₀ , cK ⟫
  Nk    = idX ⟪ bind 1 1 ∷ [] , cId ⟫
  Rarg₃ = (Nk ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩
  Bm    = idX ⟪ bind 1 1 ∷ bind 0 0 ∷ [] , revX ⟫
  RF    = Bm ⟨ [] ∣ id★↦ ⟩

  LK LK₁ RK RK₁ RK₂ RK₃ RK₄ : Term
  LK  = (ƛ ∀X⇒X ∙ ` 0) · (ν `ℕ · KK ⟨ cK ⟩)
  LK₁ = (ƛ ∀X⇒X ∙ ` 0) · VL
  RK  = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩)
  RK₁ = (ƛ (★ ⇒ ★) ∙ ` 0) · (VL ⟨ [] ∣ instI ⟩)
  RK₂ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν ★ · VL ⟨ revX ⟩) ⟨ [] ∣ id★↦ ⟩)
  RK₃ = (ƛ (★ ⇒ ★) ∙ ` 0) · Rarg₃
  RK₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · RF

  LK-⊢ : empty ∣ [] ⊢ LK ⦂ ∀X⇒X
  LK-⊢ = tc

  RK-⊢ : empty ∣ [] ⊢ RK ⦂ ★ ⇒ ★
  RK-⊢ = tc

  LK-states : evalTerms 20 LK-⊢ ≡ LK ∷ LK₁ ∷ VL ∷ []
  LK-states = refl

  RK-states : evalTerms 20 RK-⊢ ≡ RK ∷ RK₁ ∷ RK₂ ∷ RK₃ ∷ RK₄ ∷ RF ∷ []
  RK-states = refl

  -- the right's context after its Inst TyBeta (β:=★)
  ΔRk : Ctxᵗ
  ΔRk = allocate ★ ΔL

  vVL : Value VL
  vVL = V-⟪⟫ (S-Λ (V-simple S-ƛ)) I-all

  vRF : Value RF
  vRF = V-simple (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦)

  ------------------------------------------------------------------------
  -- 2. The initial pairs (no pending name)
  ------------------------------------------------------------------------

  cId⊑cId : ∀ {Δ Δ′} {W : World Δ Δ′} → marksʷ W ⊢ embᴸ W (` 0) ⊑ embᴿ W (` 0)
    → ConvImp W cId cId
  cId⊑cId x = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where
    i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id x))

  νK-ty : NuTy empty `ℕ ∀X⇒X cK ∀X⇒X
  νK-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = ν `ℕ · KK ⟨ cK ⟩})))

  instI₀-ty : CastTy empty [] instI ∀X⇒X (★ ⇒ ★)
  instI₀-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = (ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩})))

  νK-conv : NuConversionImp ∅ʷ νK-ty νK-ty
  νK-conv =
    Wν , Wν-conv , conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

  lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
  lk⊑rk =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ ∅ʷ} tf tf (x⊑x Zʷ))
      (⊑cast₀
        (ν⊑ν
          (Λ⊑Λ lift-[] (V-simple (S-Λ (V-simple S-ƛ)))
            (V-simple (S-Λ (V-simple S-ƛ)))
            (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
            (∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
          (ι⊑ι base-ℕ) νK-ty νK-ty νK-conv (∀id⊑∀id ∅ʷ))
        instI₀-ty (∀id⊑★ ∅ʷ))

  -- after both source TyBetas (α:=ℕ on each side, matched)
  Wk1 : World ΔL ΔL
  Wk1 = world⁰ 0 []↪ []↪ ((0 , 0) ∷ []) [] []

  Wk1ᵢ : World ΔLᵢ ΔLᵢ
  Wk1ᵢ = world⁰ 1 (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  Wk1-wf : WfWorld Wk1
  Wk1-wf = wf-world joint[] agree (namedᴸ-≤1 Wk1 ≤1-[]) (namedᴿ-≤1 Wk1 ≤1-[])
    [] [] []
    where
    agree : ∀ {α β} → Paired Wk1 α β → Agree Wk1 α β
    agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wk1ᵢ-wf : WfWorld Wk1ᵢ
  Wk1ᵢ-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wk1ᵢ ≤1-∷[]) (namedᴿ-≤1 Wk1ᵢ ≤1-∷[]) [] [] []
    where
    agree : ∀ {α β} → Paired Wk1ᵢ α β → Agree Wk1ᵢ α β
    agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wk1ᵢ-int : Interior Wk1 Θ₀ Θ₀ Wk1ᵢ
  Wk1ᵢ-int = record
    { int-left   = int₀
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  Wk1ᵢ-conv : ConversionInterior Wk1 Θ₀ Θ₀ Wk1ᵢ
  Wk1ᵢ-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  cK⊑cK : ConvImp Wk1ᵢ cK cK
  cK⊑cK = conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

  bVL : BdyTy ΔL Θ₀ ΔLᵢ ∀X⇒X cK ∀X⇒X
  bVL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = VL}))))

  instI-ty : CastTy ΔL [] instI ∀X⇒X (★ ⇒ ★)
  instI-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔL} {M = VL ⟨ [] ∣ instI ⟩})))

  lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
  lk₁⊑rk₁ =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk1} tf tf (x⊑x Zʷ))
      (⊑cast₀
        (⟪⟫⊑⟪⟫ Wk1ᵢ-int Wk1ᵢ-wf
          (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
          bVL bVL (Wk1ᵢ , Wk1ᵢ-conv , cK⊑cK) (∀id⊑∀id Wk1))
        instI-ty (∀id⊑★ Wk1))

  ------------------------------------------------------------------------
  -- 3. The worlds and boundaries after the right's Inst TyBeta
  ------------------------------------------------------------------------

  -- the world after the right's Inst TyBeta: (αᴸ, αᴿ) global, β unpaired
  Wk : World ΔL ΔRk
  Wk = world⁰ 0 []↪ []↪ ((0 , 1) ∷ []) [] []

  Wk-wf : WfWorld Wk
  Wk-wf = wf-world joint[] agree (namedᴸ-≤1 Wk ≤1-[]) (namedᴿ-≤1 Wk ≤1-[]) [] [] []
    where
    agree : ∀ {α β} → Paired Wk α β → Agree Wk α β
    agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Θ₀-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ₀-int = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  -- the Inst boundary `+Y^β` alone: Y is introduced right-only, at X⊑★,
  -- and pushed (pending, D27)
  IntK-ro : Interior Wk [] Θ₀ (record (Wk ⊕ʳ^ 0) { πʷ = 0 ∷ [] })
  IntK-ro = record
    { int-left   = interior changes[]
    ; int-right  = Θ₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- inside the inner boundary `+X^α`: Y at 0, X at 1
  ΘX : Boundary
  ΘX = bind 1 1 ∷ []

  ΔLX ΔRX : Ctxᵗ
  ΔLX = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
  ΔRX = (bindR ★ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

  bindX-int : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  bindX-int = interior (changes∷ changes[]
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  -- the merged boundary `+Y^β, +X^αᴿ`
  Θ₂ : Boundary
  Θ₂ = bind 1 1 ∷ bind 0 0 ∷ []

  int-Θ₂ : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  int-Θ₂ = interior
    (changes∷ (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
      (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  bNR : BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
  bNR = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = reps ΔRk ∣ (0 ∷ [])} {M = Nk}))))

  bOutK : BdyTy ΔRk Θ₀ (reps ΔRk ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOutK = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Nk ⟪ Θ₀ , revX ⟫}))))

  bBm : BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBm = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Bm}))))

  id★↦ᴿk-ty : CastTy ΔRk [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦ᴿk-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  -- The worlds of the pending name Y (design.md D27).  Right names inside
  -- the merged `+Y^β, +X^αᴿ`: Y at 0 (β:=★, PENDING, X⊑★: `πʷ = 0 ∷ []`),
  -- X at 1 (αᴿ:=ℕ).

  -- inside Θ₂ (and inside the Inst boundary's inner `+X^αᴿ`): no left
  -- name, Y pending
  WiR★ : World ΔL ΔRX
  WiR★ = world⁰ 2 (skip (skip []↪)) (keep (keep []↪))
           ((0 , 1) ∷ []) [] (0 ∷ [])

  -- inside the left's `+X^αᴸ` as well: X joined through (αᴸ, αᴿ)
  Wx★ : World ΔLᵢ ΔRX
  Wx★ = world⁰ 2 (skip (keep []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) [] (0 ∷ [])

  -- after the pop of Y: the left binder Y joins the right's Y, its
  -- abstract rep. var paired lexically with β
  WX★ : World ΔLX ΔRX
  WX★ = world⁰ 2 (keep (keep []↪)) (keep (keep []↪))
          ((1 , 1) ∷ []) ((0 , 0) ∷ []) []

  openX★ : Open1 Wx★ WX★
  openX★ = open1 join-here here r-here

  IntΘ₂★ : Interior Wk [] Θ₂ WiR★
  IntΘ₂★ = record
    { int-left   = interior changes[]
    ; int-right  = int-Θ₂
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  Wx-fresh : ∀ {X X′ α β}
    → ΔLᵢ ∋ᵗ X := α → ΔRX ∋ᵗ X′ := β
    → (Joins Wx★ X X′ → Paired WiR★ α β) × (Paired WiR★ α β → Joins Wx★ X X′)
  Wx-fresh here here = (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
  Wx-fresh here (there here) = (λ _ → inj₁ here⇔) , (λ _ → refl)
  Wx-fresh here (there (there ()))
  Wx-fresh (there ()) _

  IntX★ : Interior WiR★ Θ₀ [] Wx★
  IntX★ = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ a b _ → Wx-fresh a b
    }

  -- the Inst boundary `+Y^β` alone (before the Merge), Y pending
  WiY★ : World ΔL (reps ΔRk ∣ (0 ∷ []))
  WiY★ = record (Wk ⊕ʳ^ 0) { πʷ = 0 ∷ [] }

  -- the right's inner `+X^αᴿ` carries Y (toExt ΘX 0 = just 0)
  IntXc★ : Interior WiY★ [] ΘX WiR★
  IntXc★ = record
    { int-left   = interior changes[]
    ; int-right  = bindX-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  agreeₖ : ∀ {Δ₀ Δ₀′} {W : World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := `ℕ
    → Δ₀′ ∋rep 1 := `ℕ → ϱᵍʷ W ≡ (0 , 1) ∷ [] → ϱˡʷ W ≡ []
    → ∀ {α β} → Paired W α β → Agree W α β
  agreeₖ l r refl refl (inj₁ here⇔) = rep-rep l r (ι⊑ι base-ℕ)
  agreeₖ l r refl refl (inj₁ (there⇔ ()))
  agreeₖ l r refl refl (inj₂ ())

  WiR★-wf : WfWorld WiR★
  WiR★-wf = wf-world (right-only (right-only joint[]))
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 WiR★ ≤1-[]) (λ { (_ , ()) _ _ _ _ })
    ((0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ [])
    ([] ∷ []) []

  uniqᴿx : NamedUniqueᴿ Wx★
  uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴿx _ _ _ (inj₁ (there⇔ ())) _
  uniqᴿx _ _ _ (inj₂ ()) _
  uniqᴿx _ _ _ _ (inj₂ ())

  Wx★-wf : WfWorld Wx★
  Wx★-wf = wf-world (right-only (both (inj₁ here⇔) joint[]))
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 Wx★ ≤1-∷[]) uniqᴿx
    ((0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) _ }) ,
      (λ { (_ , here) (inj₁ (there⇔ ())) ; (_ , here) (inj₂ ())
         ; (_ , there ()) _ })) ∷ [])
    ([] ∷ []) []

  WiY★-wf : WfWorld WiY★
  WiY★-wf = wf-world (right-only joint[])
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 WiY★ ≤1-[]) (namedᴿ-≤1 WiY★ ≤1-∷[])
    ((0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ [])
    ([] ∷ []) []

  ------------------------------------------------------------------------
  -- 4. The pairs with Y pending: push, pass, pop (design.md D27)
  ------------------------------------------------------------------------

  -- THE COMMON PREMISE: inside the right boundary, Y pending.  ⟪⟫⊑ passes
  -- Y into VL's boundary (cK = ∀Y.cId), Λ⊑ pops it, ƛ⊑ƛ at Y ⊑ Y
  VL⊑idX : WiR★ ∣ [] ⊢ VL ⊑ idX
    ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  VL⊑idX =
    ⟪⟫⊑ IntX★ (ok-bind ∷ []) (bc-∀ (S-Λ (V-simple S-ƛ)) (fc-∷ fc-[])) Wx★-wf
      (Λ⊑ (claim-pop openX★) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (⇒⊑⇒ X⊑X X⊑X))
      bVL (⇒⊑⇒ X⊑X X⊑X)

  -- after the right's Merge (RK₄, RF): ⊑⟪⟫ at the merged Θ₂ PUSHES Y.
  -- THE FINAL ARGUMENT PAIR (unrelated before D26)
  VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
  VL⊑Bm =
    ⊑⟪⟫ IntΘ₂★ (push ca-[] (refl ∷ []) (inj₂ vVL)) WiR★-wf VL⊑idX bBm
      (∀id⊑★ Wk)

  VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
  VL⊑RF = ⊑cast₀ VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
  lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

  -- before the Merge (RK₃), RIGHT-FIRST: ⊑⟪⟫ at Θ₀ pushes Y, the inner
  -- ⊑⟪⟫ at ΘX CARRIES it; the premise is VL⊑idX again
  VL⊑Nk : WiY★ ∣ [] ⊢ VL ⊑ Nk
    ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  VL⊑Nk =
    ⊑⟪⟫ IntXc★ (push (ca-∷ refl ca-[]) [] (inj₁ refl)) WiR★-wf VL⊑idX bNR
      (⇒⊑⇒ X⊑X X⊑X)

  VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
  VL⊑Rarg₃ =
    ⊑cast₀
      (⊑⟪⟫ IntK-ro (push ca-[] (refl ∷ []) (inj₂ vVL)) WiY★-wf VL⊑Nk bOutK
        (∀id⊑★ Wk))
      id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
  lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

  -- K NEEDS its push: with no pending name, the premise index of
  -- `VL ⊑ Bm` inside Θ₂ is empty (Y is right-only)
  no-push-K : ¬ (∀X⇒X ⊑ᵂ⟨ record WiR★ { πʷ = [] } ⟩ (` 0 ⇒ ` 0))
  no-push-K (∀⊑ _ _ (⇒⊑⇒ () _))

------------------------------------------------------------------------
-- 10. Example P4 (= cambridge Cf from its second block), every block.
-- The shared X is X⊑X (`W₄²`) until a right coercion grants αᴿ: the gen
-- wrapper `X! → X?` before CastFun (B2), the check `X?` after it (B3,
-- B4).  Under the grant X is X⊑★ (`W₄²¹`); inside the right's own `−X`
-- it is left-only (`W₄ᴸ`), and the right's `+X` rejoins it at αᴿ, which
-- is still permitted (κ passes through every boundary)
------------------------------------------------------------------------

module P4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples using (L4; R4; L4-⊢; R4-⊢)

  nth : List Term → ℕ → Term
  nth []       _       = $ 0
  nth (x ∷ xs) zero    = x
  nth (x ∷ xs) (suc n) = nth xs n

  Ls Rs : List Term
  Ls = evalTerms 11 L4-⊢
  Rs = evalTerms 17 R4-⊢
  open TIE using (idX; revX; Θ₀; L1′; ΔL; ΔLᵢ; bL-ty; revX⊑revX; νL-ty;
                  Wν; Wν-conv)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; Wc-bindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; ℕ⇒ℕ; ∀id⊑★; ∀id⊑∀id; I★⁻; I★gen; Bg; tagX↦;
           id★→; tagX↦-grants)
  open import examples.CambridgeExamples using (I★)

  νbody : Term
  νbody = ν `ℕ · ` 0 ⟨ revX ⟩

  νbody-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νbody-ty = proj₂ (proj₂ (ν-inv {Γ = TIE.∀X⇒X ∷ []}
    (tc {Δ = empty} {Γ = TIE.∀X⇒X ∷ []} {M = νbody})))

  genArg : Term
  genArg = (ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩

  genArg-ty : CastTy empty [] (genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)))
    (★ ⇒ ★) TIE.∀X⇒X
  genArg-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = genArg})))

  ---------------------------------------------------------------------
  -- The worlds.  Both sides allocate αᴸ:=ℕ, αᴿ:=ℕ (rep. var 0); the
  -- matched TyBetas pair them globally.  The boundary name X is
  -- both-sided, X⊑X without permission (`W₄²`) and X⊑★ under the grant
  -- of αᴿ (`W₄²¹`), left-only after a right `−X` (`W₄ᴸ`), and rejoined
  -- at the right's `+X` with αᴿ still permitted.

  Ξ₄ : RepCtx
  Ξ₄ = bindR `ℕ ∷ []

  ϱ₄ : RepRel
  ϱ₄ = (0 , 0) ∷ []

  W₄ : World ΔL ΔL
  W₄ = Wc⁰ {Ξ₄} {ϱ₄}

  -- X both-sided, NOT permitted: X⊑X
  W₄² : World ΔLᵢ ΔLᵢ
  W₄² = Wc² {Ξ₄} {ϱ₄} [] 0

  -- X both-sided, αᴿ PERMITTED (under a grant): X⊑★
  W₄²¹ : World ΔLᵢ ΔLᵢ
  W₄²¹ = Wc² {Ξ₄} {ϱ₄} (0 ∷ []) 0

  -- X left-only (inside the right's −X), αᴿ permitted
  W₄ᴸ : World ΔLᵢ ΔL
  W₄ᴸ = Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ [])

  -- no name, permissions κ
  W₄⁰ : List RVar → World ΔL ΔL
  W₄⁰ κ = world 0 []↪ []↪ ϱ₄ [] κ []

  -- without a grant the shared X is X⊑X: B3's premise index is empty
  no-X⊑★-W₄² : ¬ (marksʷ W₄² ∋ˡ 0 := X⊑★)
  no-X⊑★-W₄² ()

  module Wf₄ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World (Ξ₄ ∣ nsL) (Ξ₄ ∣ nsR)
    W = world n η η′ ϱ₄ [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  p0 : All (Ξ₄ ∋ʳ_) (0 ∷ [])
  p0 = (_ , here) ∷ []

  W₄⁰-wf : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → WfWorld (W₄⁰ κ)
  W₄⁰-wf {κ} ps = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[])
    (namedᴿ-≤1 W ≤1-[]) [] [] ps
    where open Wf₄ 0 []↪ []↪ κ

  W₄-wf : WfWorld W₄
  W₄-wf = W₄⁰-wf []

  W₄²κ-wf : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → WfWorld (Wc² {Ξ₄} {ϱ₄} κ 0)
  W₄²κ-wf {κ} ps = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] ps
    where open Wf₄ 1 (keep []↪) (keep []↪) κ

  W₄²-wf : WfWorld W₄²
  W₄²-wf = W₄²κ-wf []

  W₄²¹-wf : WfWorld W₄²¹
  W₄²¹-wf = W₄²κ-wf p0

  W₄ᴸ-wf : WfWorld W₄ᴸ
  W₄ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] p0
    where open Wf₄ 1 (keep []↪) (skip []↪) (0 ∷ [])

  v₀ : Ξ₄ ∋ʳ 0
  v₀ = _ , here

  ---------------------------------------------------------------------
  -- Shared pieces: the sealed argument S = [−X^α] 5 ⟨−X⟩ on both sides

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  S : Term
  S = $ 5 ⟪ unb₀ , tail (seal 0) ⟫

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  unb-int : ∀ {κ} → Interior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ unb₀ (W₄⁰ κ)
  unb-int = record
    { int-left   = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  unb-conv : ∀ {κ} → ConversionInterior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ unb₀
    (Wc² {Ξ₄} {ϱ₄} κ 0)
  unb-conv = record
    { conv-left       = conversion (conv-unbind (_ , here) conv[])
    ; conv-right      = conversion (conv-unbind (_ , here) conv[])
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  bS : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S}))))

  -- the sealed literals, at any permissions
  S⊑Sκ : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → Wc² {Ξ₄} {ϱ₄} κ 0 ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑Sκ ps = ⟪⟫⊑⟪⟫ unb-int (W₄⁰-wf ps) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (_ , unb-conv , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  S⊑S : W₄²¹ ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S = S⊑Sκ p0

  -- the left's λx:X. x against the right's λx:★. x (X left-only)
  idX⊑I★ : W₄ᴸ ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξ₄ ϱ₄ (0 ∷ [])
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  bI★⁻ : BdyTy ΔLᵢ unb₀ ΔL (★ ⇒ ★) id★→ (★ ⇒ ★)
  bI★⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★⁻}))))

  -- idX ⊑ [−X^α] (λx:★. x) ⟨id(★) → id(★)⟩ at X→X ⊑ ★→★ (X both-sided
  -- and PERMITTED: this index needs the grant)
  idX⊑I★⁻ : W₄²¹ ∣ [] ⊢ idX ⊑ I★⁻ ∶ c⊑★² Ξ₄ ϱ₄ (0 ∷ []) 0 refl
  idX⊑I★⁻ = ⊑⟪⟫ (Wc-unbindᴿ v₀) push-none W₄ᴸ-wf idX⊑I★ bI★⁻
    (c⊑★² Ξ₄ ϱ₄ (0 ∷ []) 0 refl)

  tagᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★gen})))

  ---------------------------------------------------------------------
  -- B1 (0, 0): the initial pair

  p4-B1 : ∅ʷ ∣ [] ⊢ L4 ⊑ R4 ∶ ι⊑ι base-ℕ
  p4-B1 =
    ·⊑·
      (ƛ⊑ƛ {pA = ∀id⊑∀id ∅ʷ} tf tf
        (·⊑·
          (ν⊑ν (x⊑x Zʷ) (ι⊑ι base-ℕ) νbody-ty νbody-ty
            (Wν , Wν-conv , revX⊑revX refl)
            (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
          (κ⊑κ lit-$ (ι⊑ι base-ℕ))))
      (⊑cast₀
        (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
        genArg-ty (∀id⊑∀id ∅ʷ))

  ---------------------------------------------------------------------
  -- (1, 1): after both Betas (cambridge Cf B0)

  νR₁ : Term
  νR₁ = ν `ℕ · genArg ⟨ revX ⟩

  νR₁-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νR₁-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = νR₁})))

  p4-B1′ : ∅ʷ ∣ [] ⊢ nth Ls 1 ⊑ nth Rs 1 ∶ ι⊑ι base-ℕ
  p4-B1′ =
    ·⊑·
      (ν⊑ν
        (⊑cast₀
          (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
          genArg-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty νR₁-ty
        (Wν , Wν-conv , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B2 (2, 2): after both TyBetas, BEFORE CastFun.  The right's gen
  -- wrapper `X! → X?` at `^[X:★∼X]` is ONE arrow coercion; its
  -- covariant `X?` GRANTS αᴿ (`tagX↦-grants`), so its premise reads
  -- X→X ⊑ ★→★ at X⊑★

  bBg : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bBg = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = Bg}))))

  p4-B2 : W₄ ∣ [] ⊢ nth Ls 2 ⊑ nth Rs 2 ∶ ι⊑ι base-ℕ
  p4-B2 =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
        (⊑cast! tagX↦-grants idX⊑I★⁻ tagᵍ-ty (c⊑c² Ξ₄ ϱ₄ [] 0))
        bL-ty bBg (W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B3 (3, 4): after the left's Wrap and the right's Wrap, CastFun.
  -- The right's X? at `^[X:★∼X]` and its argument's X! at `^[X:X∼★]`
  -- (CastFun flipped the environment).  The check GRANTS αᴿ (`gr-?`);
  -- the tag below it reads X ⊑ ★ at the permitted X

  tagX : Coercion
  tagX = (` 0) !

  chkX : Coercion
  chkX = (` 0) ？ 0

  tagˣ-ty : CastTy ΔLᵢ (X∼★ ∷ []) tagX (` 0) ★
  tagˣ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = S ⟨ X∼★ ∷ [] ∣ tagX ⟩})))

  chkᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) chkX ★ (` 0)
  chkᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩})))

  -- the left's and the right's +X boundaries (conversion `unseal 0`)
  bUnsealL : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 4}))))

  bUnsealR : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealR = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 6}))))

  bUnsealL₃ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealL₃ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 3}))))

  bUnsealR₄ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealR₄ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 4}))))

  S⊑S! : W₄²¹ ∣ [] ⊢ S ⊑ S ⟨ X∼★ ∷ [] ∣ tagX ⟩ ∶ X⊑★ here
  S⊑S! = ⊑cast₀ S⊑S tagˣ-ty (X⊑★ here)

  p4-B3 : W₄ ∣ [] ⊢ nth Ls 3 ⊑ nth Rs 4 ∶ ι⊑ι base-ℕ
  p4-B3 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast! {p = X⊑★ here} (gr-? here) (·⊑· idX⊑I★⁻ S⊑S!) chkᵍ-ty X⊑X)
      bUnsealL₃ bUnsealR₄
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B4 (4, 6): after the left's Beta and the right's Wrap, Beta.  THE
  -- "J" PAIR (SidedMarks.md §4) is the premise `S ⊑ J`: X left-only
  -- after the right's −X, rejoined at the right's +X; αᴿ is still
  -- permitted (the check above granted it; κ passes both boundaries)

  J : Term
  J = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ₀ , id★ᶜ ⟫

  bJ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bJ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = J}))))

  bJ⁻ : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bJ⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = J ⟪ unb₀ , id★ᶜ ⟫}))))

  -- the J pair (index X ⊑ ★, X left-only)
  S⊑J : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here
  S⊑J = ⊑⟪⟫ (Wc-bindᴿ v₀ here⇔) push-none W₄²¹-wf S⊑S! bJ (X⊑★ here)

  p4-B4 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ nth Rs 6 ∶ ι⊑ι base-ℕ
  p4-B4 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast! {p = X⊑★ here} (gr-? here)
        (⊑⟪⟫ (Wc-unbindᴿ v₀) push-none W₄ᴸ-wf S⊑J bJ⁻ (X⊑★ here))
        chkᵍ-ty X⊑X)
      bUnsealL bUnsealR
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B5 (5, 11): after the Merges; the interiors have no name, the two
  -- conversions are id(ℕ)

  b5L : BdyTy ΔL (unbind 0 0 ∷ bind 0 0 ∷ []) ΔL `ℕ ⌞ id `ℕ ⌟ `ℕ
  b5L = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 5}))))

  b5R : BdyTy ΔL (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ [])
    ΔL `ℕ ⌞ id `ℕ ⌟ `ℕ
  b5R = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 11}))))

  bdy-wf : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ
    → Σ[ Δᶜ ∈ Ctxᵗ ] BoundaryWf Δ Θ Δᵢ Δᶜ
  bdy-wf (bdy-ty mw _ _ _ _) = _ , mw

  int5 : Interior W₄ (unbind 0 0 ∷ bind 0 0 ∷ [])
    (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ []) W₄
  int5 = record
    { int-left   = bw-interior (proj₂ (bdy-wf b5L))
    ; int-right  = bw-interior (proj₂ (bdy-wf b5R))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  p4-B5 : W₄ ∣ [] ⊢ nth Ls 5 ⊑ nth Rs 11 ∶ ι⊑ι base-ℕ
  p4-B5 = ⟪⟫⊑⟪⟫ int5 W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b5L b5R
    (W₄² , conv5 , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))
    (ι⊑ι base-ℕ)
    where
    conv5 : ConversionInterior W₄ (unbind 0 0 ∷ bind 0 0 ∷ [])
      (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ []) W₄²
    conv5 = record
      { conv-left       = bw-conversion (proj₂ (bdy-wf b5L))
      ; conv-right      = bw-conversion (proj₂ (bdy-wf b5R))
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
      ; conv-same-κ     = refl
      ; conv-join-cont  = λ { _ _ () _ }
      ; conv-join-fresh = λ
          { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      }

  -- B6 (6, 12): 5 ⊑ 5
  p4-B6 : W₄ ∣ [] ⊢ nth Ls 6 ⊑ nth Rs 12 ∶ ι⊑ι base-ℕ
  p4-B6 = κ⊑κ lit-$ (ι⊑ι base-ℕ)


------------------------------------------------------------------------
-- 10a. Cg B1 (cambridge Ex 1/20 after the left's catch-up TyBeta):
-- matched `+X` boundaries (αᴸ:=ℕ against the right's Inst αᴿ:=★, paired
-- globally), X both-sided at X⊑X; the right's gen wrapper `X! → X?`
-- GRANTS αᴿ; inside its own `−X` X is left-only, where λx:X.x ⊑ λx:★.x
-- reads X ⊑ ★
------------------------------------------------------------------------

module CgB1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (Cg-L; Cg-L-⊢; I★)
  open TIE using (idX; revX; L1′; ΔL; ΔR; ΔLᵢ; bL-ty; revX⊑revX; five⊑)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; Cg-R₂; Cg-R₂-state; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty;
           id★↦ᴿ-ty; ℕ⇒ℕ⊑★⇒★; tagX↦-grants; p0)

  Ξg : RepCtx
  Ξg = bindR ★ ∷ []

  ϱg : RepRel
  ϱg = (0 , 0) ∷ []

  Cg-L₁-state : head (drop 1 (evalTerms 10 Cg-L-⊢)) ≡ just L1′
  Cg-L₁-state = refl

  module Wfg {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξg ∣ nsR)
    W = world n η η′ ϱg [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wg²-wf : WfWorld (Wc² {Ξg} {ϱg} [] 0)
  Wg²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] []
    where open Wfg 1 (keep []↪) (keep []↪) []

  Wgᴴ-wf : WfWorld (Wcᴸ {Ξg} {ϱg} (0 ∷ []))
  Wgᴴ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] p0
    where open Wfg 1 (keep []↪) (skip []↪) (0 ∷ [])

  idX⊑I★ : Wcᴸ {Ξg} {ϱg} (0 ∷ []) ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξg ϱg (0 ∷ [])
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  cg-b1 : Wc⁰ {Ξg} {ϱg} ∣ [] ⊢ L1′ ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
  cg-b1 =
    ·⊑·
      (⊑cast₀
        (⟪⟫⊑⟪⟫ (Wc-bind² (_ , here) here⇔) Wg²-wf
          (⊑cast! {A = ` 0 ⇒ ` 0} tagX↦-grants
            (⊑⟪⟫ (Wc-unbindᴿ (_ , here)) push-none Wgᴴ-wf idX⊑I★ I★⁻ᴿ-ty
              (c⊑★² Ξg ϱg (0 ∷ []) 0 refl))
            tagᴿ-ty (c⊑c² Ξg ϱg [] 0))
          bL-ty Bg-ty
          (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
      five⊑

------------------------------------------------------------------------
-- 10b. C18b B7 (cambridge Ex 18b, block (7,12)): TWO names at once.
-- Matched outer `(+Y,+X)`, both both-sided at X⊑X; the right's `X?`
-- GRANTS X's rep. var 1; the right's `(−Y,−X)` makes both left-only;
-- its `(+X,+Y)` rejoins both, X still permitted (κ = [1] passes both
-- boundaries); the right's `X!` reads X ⊑ ★.  Center 0 is Y (rep. var
-- 0 = β), center 1 is X (rep. var 1 = α).
------------------------------------------------------------------------

module C18bB7 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.Examples using (ℓ)
  open import examples.CambridgeExamples using (C18b-L-⊢; C18b-R-⊢)
  open P4 using (nth)

  Δ₀ Δ₂ : Ctxᵗ
  Δ₀ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ []
  Δ₂ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

  Θo Θh Θj ΘS : Boundary
  Θo = bind 1 1 ∷ bind 0 0 ∷ []
  Θh = unbind 0 1 ∷ unbind 0 0 ∷ []
  Θj = bind 0 0 ∷ bind 0 1 ∷ []
  ΘS = unbind 0 0 ∷ unbind 1 1 ∷ []

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S2 J2 RH L7 R12 : Term
  S2  = $ 42 ⟪ ΘS , tail (seal 1) ⟫
  J2  = (S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩) ⟪ Θj , id★ᶜ ⟫
  RH  = J2 ⟪ Θh , id★ᶜ ⟫
  L7  = S2 ⟪ Θo , unseal 1 ⟫
  R12 = (RH ⟨ ★∼X ∷ ★∼X ∷ [] ∣ (` 1) ？ ℓ ⟩) ⟪ Θo , unseal 1 ⟫

  L7-state : nth (evalTerms 30 C18b-L-⊢) 7 ≡ L7
  L7-state = refl

  R12-state : nth (evalTerms 30 C18b-R-⊢) 12 ≡ R12
  R12-state = refl

  ϱ : RepRel
  ϱ = (0 , 0) ∷ (1 , 1) ∷ []

  W₀ : List RVar → World Δ₀ Δ₀
  W₀ κ = world 0 []↪ []↪ ϱ [] κ []

  -- both both-sided, X⊑★
  Wb : List RVar → World Δ₂ Δ₂
  Wb κ = world 2 (keep (keep []↪)) (keep (keep []↪)) ϱ [] κ []

  -- both left-only (inside the right's (−Y,−X))
  Wh : List RVar → World Δ₂ Δ₀
  Wh κ = world 2 (keep (keep []↪)) (skip (skip []↪)) ϱ [] κ []

  module Wf {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsL)
              ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsR)
    W = world n η η′ ϱ [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep (r-there r-here) (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())

    diag : ∀ {α β} → Paired W α β → α ≡ β
    diag (inj₁ here⇔) = refl
    diag (inj₁ (there⇔ here⇔)) = refl
    diag (inj₁ (there⇔ (there⇔ ())))
    diag (inj₂ ())

    uniqᴸ : NamedUniqueᴸ W
    uniqᴸ _ _ _ p p′ = trans (diag p) (sym (diag p′))

    uniqᴿ : NamedUniqueᴿ W
    uniqᴿ _ _ _ p p′ = trans (sym (diag p)) (diag p′)

  Rs₂ : RepCtx
  Rs₂ = bindR `ℕ ∷ bindR `ℕ ∷ []

  p1 : All (Rs₂ ∋ʳ_) (1 ∷ [])
  p1 = (_ , there here) ∷ []

  W₀-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (W₀ κ)
  W₀-wf {κ} ps = wf-world joint[] agree uniqᴸ uniqᴿ [] [] ps
    where open Wf 0 []↪ []↪ κ

  Wb-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (Wb κ)
  Wb-wf {κ} ps =
    wf-world (both (inj₁ here⇔) (both (inj₁ (there⇔ here⇔)) joint[]))
      agree uniqᴸ uniqᴿ [] [] ps
    where open Wf 2 (keep (keep []↪)) (keep (keep []↪)) κ

  Wh-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (Wh κ)
  Wh-wf {κ} ps =
    wf-world (left-only (left-only joint[])) agree uniqᴸ uniqᴿ [] [] ps
    where open Wf 2 (keep (keep []↪)) (skip (skip []↪)) κ

  -- the boundaries' interior contexts
  int-o : Δ₀ ⊢ⁱ Θo ⇒ Δ₂
  int-o = interior (changes∷ (changes∷ changes[]
    (step-bind (_ , here) fresh[] ins-here))
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  int-h : Δ₂ ⊢ⁱ Θh ⇒ Δ₀
  int-h = interior (changes∷ (changes∷ changes[]
    (step-unbind (_ , here) del-here (fresh∷ (λ ()) fresh[])))
    (step-unbind (_ , there here) del-here fresh[]))

  int-j : Δ₀ ⊢ⁱ Θj ⇒ Δ₂
  int-j = interior (changes∷ (changes∷ changes[]
    (step-bind (_ , there here) fresh[] ins-here))
    (step-bind (_ , here) (fresh∷ (λ ()) fresh[]) ins-here))

  int-S : Δ₂ ⊢ⁱ ΘS ⇒ Δ₀
  int-S = interior (changes∷ (changes∷ changes[]
    (step-unbind (_ , there here) (del-there del-here) (fresh∷ (λ ()) fresh[])))
    (step-unbind (_ , here) del-here fresh[]))

  -- the joins of the two fresh pairs: name i on each side, rep. var i
  pairs : ∀ {κ κ′ X X′ α β} → Δ₂ ∋ᵗ X := α → Δ₂ ∋ᵗ X′ := β
    → (Joins (Wb κ) X X′ → Paired (W₀ κ′) α β)
      × (Paired (W₀ κ′) α β → Joins (Wb κ) X X′)
  pairs here here = (λ _ → inj₁ here⇔) , (λ _ → refl)
  pairs here (there here) =
    (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
  pairs (there here) here =
    (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
  pairs (there here) (there here) = (λ _ → inj₁ (there⇔ here⇔)) , (λ _ → refl)

  -- the matched outer (+Y,+X): both fresh, both joined
  IntO : Interior (W₀ []) Θo Θo (Wb [])
  IntO = record
    { int-left   = int-o
    ; int-right  = int-o
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there here) _ () _ }
    ; join-fresh = λ a b _ → pairs {[]} {[]} a b
    }

  -- the right's (−Y,−X): both continuing left names become left-only
  IntH : ∀ {κ} → Interior (Wb κ) [] Θh (Wh κ)
  IntH = record
    { int-left   = interior changes[]
    ; int-right  = int-h
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    }

  -- the right's (+X,+Y): both names REJOIN; κ is unchanged
  IntJ : ∀ {κ} → Interior (Wh κ) [] Θj (Wb κ)
  IntJ {κ} = record
    { int-left   = interior changes[]
    ; int-right  = int-j
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there here) _ () }
    ; join-fresh = λ a b _ → pairs {κ} {κ} a b
    }

  -- the matched (−X,−Y) of the sealed literal: no names inside
  IntS : ∀ {κ} → Interior (Wb κ) ΘS ΘS (W₀ κ)
  IntS = record
    { int-left   = int-S
    ; int-right  = int-S
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  conv-o : Δ₀ ⊢ᶜ Θo ⇒ Δ₂
  conv-o = conversion (conv-bind (_ , there here)
    (conv-bind (_ , here) conv[] fresh[] ins-here)
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

  conv-S : Δ₂ ⊢ᶜ ΘS ⇒ Δ₂
  conv-S = conversion (conv-unbind (_ , here)
    (conv-unbind (_ , there here) conv[]))

  ConvO : ConversionInterior (W₀ []) Θo Θo (Wb [])
  ConvO = record
    { conv-left       = conv-o
    ; conv-right      = conv-o
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ a b _ → pairs {[]} {[]} a b
    }

  named₂ : ∀ {X α} → Δ₂ ∋ᵗ X := α → names Δ₂ ∌ʳ α → ⊥
  named₂ here         (fresh∷ n _)          = n refl
  named₂ (there here) (fresh∷ _ (fresh∷ n _)) = n refl

  ConvS : ∀ {κ} → ConversionInterior (Wb κ) ΘS ΘS (Wb κ)
  ConvS = record
    { conv-left       = conv-S
    ; conv-right      = conv-S
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here (there here) here (there here) → (λ j → j) , (λ j → j)
        ; (there here) here (there here) here → (λ j → j) , (λ j → j)
        ; (there here) (there here) (there here) (there here) →
            (λ j → j) , (λ j → j)
        ; (there (there ())) _ _ _
        ; _ (there (there ())) _ _
        ; _ _ (there (there ())) _
        ; _ _ _ (there (there ()))
        }
    ; conv-join-fresh = λ
        { a _ (inj₁ f) → ⊥-elim (named₂ a f)
        ; _ b (inj₂ f) → ⊥-elim (named₂ b f)
        }
    }

  bS : BdyTy Δ₂ ΘS Δ₀ `ℕ (tail (seal 1)) (` 1)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₂} {M = S2}))))

  bJ2 : BdyTy Δ₀ Θj Δ₂ ★ id★ᶜ ★
  bJ2 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = J2}))))

  bRH : BdyTy Δ₂ Θh Δ₀ ★ id★ᶜ ★
  bRH = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₂} {M = RH}))))

  bL7 : BdyTy Δ₀ Θo Δ₂ (` 1) (unseal 1) `ℕ
  bL7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = L7}))))

  bR12 : BdyTy Δ₀ Θo Δ₂ (` 1) (unseal 1) `ℕ
  bR12 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = R12}))))

  tag-ty : CastTy Δ₂ (flipᵐ ★∼X ∷ X∼★ ∷ []) ((` 1) !) (` 1) ★
  tag-ty = cast-ty (⊢tag-var (_ , there here) (there here) tag-dyn) refl

  chk-ty : CastTy Δ₂ (★∼X ∷ ★∼X ∷ []) ((` 1) ？ ℓ) ★ (` 1)
  chk-ty = cast-ty (⊢check-var (_ , there here) (there here) check-dyn) refl

  -- X (center 1) at X⊑★ under X's permission (Y stays X⊑X)
  X★ : marksʷ (Wb (1 ∷ [])) ∋ˡ 1 := X⊑★
  X★ = there here

  S2⊑S2 : Wb (1 ∷ []) ∣ [] ⊢ S2 ⊑ S2 ∶ X⊑X
  S2⊑S2 = ⟪⟫⊑⟪⟫ IntS (W₀-wf p1) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (Wb (1 ∷ []) , ConvS , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- inside the rejoin: the right's X! at the rejoined, permitted X
  inner : Wb (1 ∷ []) ∣ [] ⊢ S2 ⊑ S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩
    ∶ X⊑★ X★
  inner = ⊑cast₀ S2⊑S2 tag-ty (X⊑★ X★)

  c18b-b7 : W₀ [] ∣ [] ⊢ L7 ⊑ R12 ∶ ι⊑ι base-ℕ
  c18b-b7 =
    ⟪⟫⊑⟪⟫ IntO (Wb-wf [])
      (⊑cast! {p = X⊑★ X★} (gr-? (there here))
        (⊑⟪⟫ IntH push-none (Wh-wf p1)
          (⊑⟪⟫ IntJ push-none (Wb-wf p1) inner bJ2 (X⊑★ (there here)))
          bRH (X⊑★ X★))
        chk-ty X⊑X)
      bL7 bR12 (Wb [] , ConvO , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- 10c. Reduction closure on P4's run (SimBack evidence): the left at B4
-- (`[+X^α] S ⟨+X⟩`) is related to EVERY right state its Merge, IdDyn,
-- Merge, TagUntag steps produce (right states 7-10).  The merged
-- `[−X, +X]` is an unbind then a bind of X in ONE boundary: `toExt`
-- makes X continuing on both sides, so X stays joined, and αᴿ stays
-- permitted (the check above it); after IdDyn the tag `X!` is outside,
-- still under the check.  (State 11, the final Merge, needs the left's own Merge:
-- B5.)
------------------------------------------------------------------------

module P4c where
  open import examples.TypeCheck using (tc; tf)
  open P4 using (nth; Ls; Rs; S; unb₀; id★ᶜ; tagX; chkX; tagˣ-ty; chkᵍ-ty;
                 bUnsealL; W₄; W₄²; W₄-wf; W₄²-wf; v₀; S⊑S; bS; bdy-wf;
                 Ξ₄; ϱ₄; W₄²¹; W₄²¹-wf; W₄⁰; W₄⁰-wf; p0)
  open Rebase using (Wc²)
  open TIE using (ΔL; ΔLᵢ; Θ₀)
  open Rebase using (Θ⁻⁺; Θ⁻⁺-int; Wc-bind²; Wc-bind²-conv; unbind₀-int;
                     unbind₀-conv)

  Θ³ : Boundary
  Θ³ = unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ []

  Bm7 Bi8 S3 R7 R8 R9 R10 : Term
  Bm7 = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , id★ᶜ ⟫
  Bi8 = S ⟪ Θ⁻⁺ , ⌞ id (` 0) ⌟ ⟫
  S3  = $ 5 ⟪ Θ³ , tail (seal 0) ⟫
  R7  = (Bm7 ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R8  = ((Bi8 ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R9  = ((S3 ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R10 = S3 ⟪ Θ₀ , unseal 0 ⟫

  R7-state : nth Rs 7 ≡ R7
  R7-state = refl

  R8-state : nth Rs 8 ≡ R8
  R8-state = refl

  R9-state : nth Rs 9 ≡ R9
  R9-state = refl

  R10-state : nth Rs 10 ≡ R10
  R10-state = refl

  -- the right's [−X, +X] alone: X continuing on both sides, joined
  IntRR : Interior W₄²¹ [] Θ⁻⁺ W₄²¹
  IntRR = record
    { int-left   = interior changes[]
    ; int-right  = Θ⁻⁺-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
        ; (_ , here) (_ , there ()) _ _
        ; (_ , there ()) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there ()) _ ; (there ()) _ _ }
    }

  bBm7 : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ ★ id★ᶜ ★
  bBm7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Bm7}))))

  bBi8 : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0) ⌞ id (` 0) ⌟ (` 0)
  bBi8 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Bi8}))))

  bS3 : BdyTy ΔLᵢ Θ³ ΔL `ℕ (tail (seal 0)) (` 0)
  bS3 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S3}))))

  bR7 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R7}))))

  bR8 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR8 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R8}))))

  bR9 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR9 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R9}))))

  bR10 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR10 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R10}))))

  -- the left's sealed 5 against the right's merged [−X, +X, −X] 5 ⟨−X⟩
  Int3 : ∀ {κ} → Interior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ Θ³ (W₄⁰ κ)
  Int3 = record
    { int-left   = unbind₀-int
    ; int-right  = bw-interior (proj₂ (bdy-wf bS3))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  Conv3 : ∀ {κ} → ConversionInterior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ Θ³
    (Wc² {Ξ₄} {ϱ₄} κ 0)
  Conv3 = record
    { conv-left       = unbind₀-conv
    ; conv-right      = bw-conversion (proj₂ (bdy-wf bS3))
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  S⊑S3 : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ
    → Wc² {Ξ₄} {ϱ₄} κ 0 ∣ [] ⊢ S ⊑ S3 ∶ X⊑X
  S⊑S3 ps = ⟪⟫⊑⟪⟫ Int3 (W₄⁰-wf ps) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS3
    (_ , Conv3 , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  outer : ∀ {M′} → (b′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ)
    → BdyConversionImp W₄ bUnsealL b′
    → W₄² ∣ [] ⊢ S ⊑ M′ ∶ X⊑X
    → W₄ ∣ [] ⊢ nth Ls 4 ⊑ M′ ⟪ Θ₀ , unseal 0 ⟫ ∶ ι⊑ι base-ℕ
  outer b′ bc d =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf d bUnsealL b′ bc (ι⊑ι base-ℕ)


  p4-R7 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R7 ∶ ι⊑ι base-ℕ
  p4-R7 = outer bR7
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast! {p = X⊑★ here} (gr-? here)
      (⊑⟪⟫ IntRR push-none W₄²¹-wf (⊑cast₀ S⊑S tagˣ-ty (X⊑★ here)) bBm7
        (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R8 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R8 ∶ ι⊑ι base-ℕ
  p4-R8 = outer bR8
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast! {p = X⊑★ here} (gr-? here)
      (⊑cast₀ {p = X⊑X} (⊑⟪⟫ IntRR push-none W₄²¹-wf S⊑S bBi8 X⊑X)
        tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R9 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R9 ∶ ι⊑ι base-ℕ
  p4-R9 = outer bR9
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast! {p = X⊑★ here} (gr-? here)
      (⊑cast₀ {p = X⊑X} (S⊑S3 p0) tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R10 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R10 ∶ ι⊑ι base-ℕ
  p4-R10 = outer bR10
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl) (S⊑S3 [])


------------------------------------------------------------------------
-- 11. Facts for the non-derivability proofs.  THE INVARIANT IS κʷ ≡ []:
-- a top-level world has no permission (like `πʷ ≡ []`); a permission
-- enters only at a granting right cast; a boundary passes κ unchanged.
-- Under κʷ ≡ [] a center name the right sees is X⊑X (`no★-right`), so a
-- right tag `X!` can face no untagged left value (`no-tag★`).
------------------------------------------------------------------------

lookup-unique : ∀ {A : Set} {xs : List A} {k a b}
  → xs ∋ˡ k := a → xs ∋ˡ k := b → a ≡ b
lookup-unique here      here       = refl
lookup-unique (there h) (there h′) = lookup-unique h h′

-- the derived mark of a right name is its permission
dmarks-emb : ∀ {ns n X β} (ι : ns ↪ n) (κ : List RVar) → ns ∋ˡ X := β
  → dmarks ι κ ∋ˡ emb ι X := permit β κ
dmarks-emb (keep ι) κ here      = here
dmarks-emb (keep ι) κ (there h) = there (dmarks-emb ι κ h)
dmarks-emb (skip ι) κ h         = there (dmarks-emb ι κ h)

-- NO PERMISSION, NO X⊑★ AT A NAME THE RIGHT SEES
no★-right : ∀ {V : World Δ Δ′} {X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ¬ (marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := X⊑★)
no★-right {V = V} {β = β} eκ rh h
  with trans (lookup-unique h (dmarks-emb (ηᴿʷ V) (κʷ V) rh))
             (cong (permit β) eκ)
... | ()

-- ... so a left name joined to a right name is not X⊑★
no-tag★ : ∀ {V : World Δ Δ′} {X X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → Joins V X X′ → ¬ (marksʷ V ∋ˡ emb (ηᴸʷ V) X := X⊑★)
no-tag★ {V = V} eκ rh j h =
  no★-right {V = V} eκ rh (subst (λ c → marksʷ V ∋ˡ c := X⊑★) j h)

-- the index of a non-∀ left type has no pending name
data NonForall : Ty → Set where
  nf-var : ∀ {X} → NonForall (` X)
  nf-ℕ   : NonForall `ℕ
  nf-𝔹   : NonForall `𝔹
  nf-★   : NonForall ★
  nf-⇒   : ∀ {A B} → NonForall (A ⇒ B)

openImp-[] : ∀ {μ cs ρ A B} → NonForall A → OpenImp μ cs ρ A B → cs ≡ []
openImp-[] {cs = []}    _      _  = refl
openImp-[] {cs = c ∷ cs} nf-var ()
openImp-[] {cs = c ∷ cs} nf-ℕ   ()
openImp-[] {cs = c ∷ cs} nf-𝔹   ()
openImp-[] {cs = c ∷ cs} nf-★   ()
openImp-[] {cs = c ∷ cs} nf-⇒   ()

map-[] : ∀ {A B : Set} {f : A → B} (xs : List A) → map f xs ≡ [] → xs ≡ []
map-[] []       _  = refl
map-[] (x ∷ xs) ()

π[] : ∀ {V : World Δ Δ′} {A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩ A′ → πʷ V ≡ []
π[] {V = V} {A} {A′} nf q =
  map-[] (πʷ V)
    (openImp-[] {μ = marksʷ V} {ρ = emb (ηᴸʷ V)} {A = A} {B = embᴿ V A′} nf q)

plain-idx : ∀ {V : World Δ Δ′} {A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩ A′
  → marksʷ V ⊢ embᴸ V A ⊑ embᴿ V A′
plain-idx {V = V} {A} {A′} nf q =
  subst (λ π → OpenImp (marksʷ V) (map (emb (ηᴿʷ V)) π) (emb (ηᴸʷ V)) A
                 (embᴿ V A′))
        (π[] {V = V} {A′ = A′} nf q) q

var⊑var : ∀ {μ a b} → μ ⊢ ` a ⊑ ` b → a ≡ b
var⊑var X⊑X = refl

var⊑★ : ∀ {μ a} → μ ⊢ ` a ⊑ ★ → μ ∋ˡ a := X⊑★
var⊑★ (X⊑★ h) = h

no-ℕ⊑var : ∀ {V : World Δ Δ′} {X} → ¬ (`ℕ ⊑ᵂ⟨ V ⟩ ` X)
no-ℕ⊑var {V = V} {X} q with plain-idx {V = V} {A′ = ` X} nf-ℕ q
... | ()

no-★⊑var : ∀ {V : World Δ Δ′} {X} → ¬ (★ ⊑ᵂ⟨ V ⟩ ` X)
no-★⊑var {V = V} {X} q with plain-idx {V = V} {A′ = ` X} nf-★ q
... | ()

no-var⊑ℕ : ∀ {V : World Δ Δ′} {X} → ¬ (` X ⊑ᵂ⟨ V ⟩ `ℕ)
no-var⊑ℕ {V = V} {X} q with plain-idx {V = V} {A′ = `ℕ} nf-var q
... | ()

no-plain-ℕ⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ `ℕ ⊑ ` a)
no-plain-ℕ⊑var ()

no-plain-★⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ ★ ⊑ ` a)
no-plain-★⊑var ()

-- THE DECISIVE INDEX: a left name against a right name in one world,
-- against ★ in another with the same embeddings and no permission
no-tag-at : ∀ {V : World Δ Δ′} {κₚ a X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ` a ⊑ᵂ⟨ record V { κʷ = κₚ } ⟩ ` X′ → ` a ⊑ᵂ⟨ V ⟩ ★ → ⊥
no-tag-at {V = V} {κₚ} {X′ = X′} eκ rh p q =
  no-tag★ {V = V} eκ rh
    (var⊑var (plain-idx {V = record V { κʷ = κₚ }} {A′ = ` X′} nf-var p))
    (var⊑★ (plain-idx {V = V} {A′ = ★} nf-var q))

-- the left type of a cast, a boundary, a literal (right rules keep it)
lty-cast : ∀ {V : World Δ Δ′} {γ M M′ μ c A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q → Σ[ B ∈ Ty ] CastTy Δ μ c B A
lty-cast (cast⊑cast _ ct _ _) = _ , ct
lty-cast (cast⊑ _ _ ct _)     = _ , ct
lty-cast (⊑cast _ _ d _ _)    = lty-cast d
lty-cast (⊑⟪⟫ _ _ _ d _ _)    = lty-cast d

lty-bdy : ∀ {V : World Δ Δ′} {γ M M′ Θ c A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Aᵢ ∈ Ty ] BdyTy Δ Θ Δᵢ Aᵢ c A
lty-bdy (⟪⟫⊑⟪⟫ _ _ _ b _ _ _) = _ , _ , b
lty-bdy (⟪⟫⊑ _ _ _ _ _ b _)   = _ , _ , b
lty-bdy (⊑cast _ _ d _ _)     = lty-bdy d
lty-bdy (⊑⟪⟫ _ _ _ d _ _)     = lty-bdy d

lty-$ : ∀ {V : World Δ Δ′} {γ n M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ $ n ⊑ M′ ∶ q → A ≡ `ℕ
lty-$ (κ⊑κ lit-$ _)       = refl
lty-$ (⊑cast _ _ d _ _)   = lty-$ d
lty-$ (⊑⟪⟫ _ _ _ d _ _)   = lty-$ d

-- a variable at the empty term context is related to nothing
no-var-[] : ∀ {V : World Δ Δ′} {x M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → ¬ (V ∣ [] ⊢ ` x ⊑ M′ ∶ q)
no-var-[] (x⊑x ())
no-var-[] (⊑cast _ raise-[] d _ _) = no-var-[] d
no-var-[] (⊑⟪⟫ _ _ _ d _ _) = no-var-[] d

-- the left type of the variable 0 is its entry's
lty-x : ∀ {V : World Δ Δ′} {A₀ A₀′ p₀ γ M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ ctx-imp A₀ A₀′ p₀ ∷ γ ⊢ ` 0 ⊑ M′ ∶ q → A ≡ A₀
lty-x (x⊑x Zʷ) = refl
lty-x (⊑cast _ (raise-∷ _) d _ _) = lty-x d
lty-x (⊑⟪⟫ _ _ _ d _ _) = ⊥-elim (no-var-[] d)

-- the left types of λx:X. x and of ΛX. λx:X. x
idX′ : Term
idX′ = ƛ (` 0) ∙ ` 0

lty-idX : ∀ {V : World Δ Δ′} {γ M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ idX′ ⊑ M′ ∶ q → A ≡ ` 0 ⇒ ` 0
lty-idX (ƛ⊑ƛ _ _ d) rewrite lty-x d = refl
lty-idX (⊑cast _ _ d _ _) = lty-idX d
lty-idX (⊑⟪⟫ _ _ _ d _ _) = lty-idX d

lty-ΛidX : ∀ {V : World Δ Δ′} {γ M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ Λ idX′ ⊑ M′ ∶ q → A ≡ `∀ (` 0 ⇒ ` 0)
lty-ΛidX (Λ⊑Λ _ _ _ d _) rewrite lty-idX d = refl
lty-ΛidX (Λ⊑ _ _ _ _ _ d _) rewrite lty-idX d = refl
lty-ΛidX (⊑cast _ _ d _ _) = lty-ΛidX d
lty-ΛidX (⊑⟪⟫ _ _ _ d _ _) = lty-ΛidX d

-- coercion typings of the casts that occur
ct-id★ : ∀ {μ B A} → CastTy Δ μ (idᵖ ★) B A → (B ≡ ★) × (A ≡ ★)
ct-id★ (cast-ty (⊢id _ _) _) = refl , refl

ct-ℕ! : ∀ {μ B A} → CastTy Δ μ (`ℕ !) B A → (B ≡ `ℕ) × (A ≡ ★)
ct-ℕ! (cast-ty (⊢tag g-ℕ) _) = refl , refl

ct-ℕ? : ∀ {μ ℓ B A} → CastTy Δ μ (`ℕ ？ ℓ) B A → (B ≡ ★) × (A ≡ `ℕ)
ct-ℕ? (cast-ty (⊢check g-ℕ) _) = refl , refl

ct-X! : ∀ {μ X B A} → CastTy Δ μ ((` X) !) B A
  → (Δ ∋tv X) × (B ≡ ` X) × (A ≡ ★)
ct-X! (cast-ty (⊢tag ()) _)
ct-X! (cast-ty (⊢tag-var tv _ _) _) = tv , refl , refl

-- coercions that grant nothing
NoGrant : Coercion → Set
NoGrant c = ∀ {Δ′ β} → ¬ Grants Δ′ β c

ng-ℕ? : ∀ {ℓ} → NoGrant (`ℕ ？ ℓ)
ng-ℕ? ()

ng-id : ∀ {A} → NoGrant (idᵖ A)
ng-id ()

ng-id★↦ : NoGrant (idᵖ ★ ↦ᵖ idᵖ ★)
ng-id★↦ (gr-↦ _ ())

ng-tag↦id★ : ∀ {X} → NoGrant (((` X) !) ↦ᵖ idᵖ ★)
ng-tag↦id★ (gr-↦ _ ())

cg-none : ∀ {Δ′ c κ κₚ} → NoGrant c → CastGrant Δ′ c κ κₚ → κₚ ≡ κ
cg-none ng no-grant  = refl
cg-none ng (grant g) = ⊥-elim (ng g)

-- the bind entry `+X^0` from a context with no name
Θ₀ : Boundary
Θ₀ = bind 0 0 ∷ []

-- runs (HiddenNames.Runs, copied): every reachable state is a state of
-- the evalTerms run (determinism)
module Runs where
  open import examples.Eval
    using (eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed;
           no-redex; out-of-fuel; evalTerms; traceTerms; step; StepResult)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  import Data.List.Relation.Unary.All as All

  justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
    → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
  justStep {r = r} _ = proj₂ (proj₂ r)

  EndsVB : ∀ {Δ A M} → Trace Δ A M → Set
  EndsVB (stop (value _))   = ⊤
  EndsVB (stop (blamed _))  = ⊤
  EndsVB (stop no-redex)    = ⊥
  EndsVB (stop out-of-fuel) = ⊥
  EndsVB (illtyped _)       = ⊥
  EndsVB (_ ◅⟨ _ ⟩ tr)      = EndsVB tr

  in-trace : ∀ {Δ A M N} (tr : Trace Δ A M) → Δ ∣ [] ⊢ M ⦂ A
    → EndsVB tr → Δ ⊢ M -→* N → N ∈ traceTerms tr
  in-trace (stop f) ⊢M e done = here refl
  in-trace (illtyped _) ⊢M e done = here refl
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e done = here refl
  in-trace (stop (value v)) ⊢M e (st then r) =
    ⊥-elim (proj₁ irreducible v st)
  in-trace (stop (blamed refl)) ⊢M e (st then r) =
    ⊥-elim (proj₂ irreducible st)
  in-trace (stop no-redex) ⊢M () (st then r)
  in-trace (stop out-of-fuel) ⊢M () (st then r)
  in-trace (illtyped _) ⊢M () (st then r)
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) with det ⊢M st st′
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) | refl , refl =
    there (in-trace tr ⊢M′ e r)

  all-reach : ∀ {Δ A M N} {P : Term → Set} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
    → EndsVB (eval k M ⊢M) → All P (evalTerms k ⊢M)
    → Δ ⊢ M -→* N → P N
  all-reach k ⊢M e a r = All.lookup a (in-trace (eval k _ ⊢M) ⊢M e r)

  NotBlame : Term → Set
  NotBlame N = ∀ {ℓ} → N ≡ blame ℓ → ⊥

  last : List Term → Term
  last []           = $ 0
  last (x ∷ [])     = x
  last (x ∷ y ∷ xs) = last (y ∷ xs)

------------------------------------------------------------------------
-- 12. The spine argument for C1 and C2.  A RIGHT spine (casts,
-- boundaries) that reaches a name tag `X!` through casts that grant
-- nothing (`Reach`); a LEFT term outside its own `[+X^α] (sealed m)
-- ⟨+X⟩` boundary under ground casts (`LO`).  Under κʷ ≡ [] they are
-- never related: inside the left boundary the decisive step `⊑cast` of
-- the tag needs X⊑★ at a name the right sees (`no-tag-at`).
------------------------------------------------------------------------

data Reach : Term → Set where
  r-tag  : ∀ {U μ k} → Reach (U ⟨ μ ∣ (` k) ! ⟩)
  r-cast : ∀ {R μ c} → NoGrant c → Reach R → Reach (R ⟨ μ ∣ c ⟩)
  r-⟪⟫   : ∀ {R Θ d} → Reach R → Reach (R ⟪ Θ , d ⟫)

-- left literals against a Reach spine (by types alone)
no-$ : ∀ {V : World Δ Δ′} {γ n R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⊑ R ∶ q)
no-$ {V = V} r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
  with ct-X! ct | lty-$ d
... | _ , refl , refl | refl = no-ℕ⊑var {V = record V { κʷ = κₚ }} p
no-$ (r-cast _ r) (⊑cast _ _ d _ _) = no-$ r d
no-$ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ d _ _) = no-$ r d

no-n★ : ∀ {V : World Δ Δ′} {γ n μ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⟨ μ ∣ `ℕ ! ⟩ ⊑ R ∶ q)
no-n★ {V = V} r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
  with ct-X! ct | lty-cast d
... | _ , refl , refl | _ , ct₀ with ct-ℕ! ct₀
... | refl , refl = no-★⊑var {V = record V { κʷ = κₚ }} p
no-n★ r-tag (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ! ct | ct-X! ct′
... | refl , refl | _ , refl , refl = no-plain-ℕ⊑var p
no-n★ (r-cast _ r) (cast⊑cast d _ _ _) = no-$ r d
no-n★ (r-cast _ r) (⊑cast _ _ d _ _) = no-n★ r d
no-n★ r (cast⊑ _ d _ _) = no-$ r d
no-n★ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ d _ _) = no-n★ r d

data G : Ty → Set where
  gℕ : G `ℕ
  g★ : G ★

no-G⊑var : ∀ {V : World Δ Δ′} {A X} → G A → ¬ (A ⊑ᵂ⟨ V ⟩ ` X)
no-G⊑var {V = V} gℕ = no-ℕ⊑var {V = V}
no-G⊑var {V = V} g★ = no-★⊑var {V = V}

no-G⊑varᵖ : ∀ {μ : ImpEnv} {ρ A a} → G A → ¬ (μ ⊢ renameᵗ ρ A ⊑ ` a)
no-G⊑varᵖ gℕ = no-plain-ℕ⊑var
no-G⊑varᵖ g★ = no-plain-★⊑var

data GCast : Coercion → Set where
  gc-ℕ!  : GCast (`ℕ !)
  gc-ℕ?  : GCast (`ℕ ？ 0)
  gc-id★ : GCast (idᵖ ★)

gsrc : ∀ {c μ B A} → GCast c → CastTy Δ μ c B A → G B
gsrc gc-ℕ!  ct with ct-ℕ! ct
... | refl , _ = gℕ
gsrc gc-ℕ?  ct with ct-ℕ? ct
... | refl , _ = g★
gsrc gc-id★ ct with ct-id★ ct
... | refl , _ = g★

gtrg : ∀ {c μ B A} → GCast c → CastTy Δ μ c B A → G A
gtrg gc-ℕ!  ct with ct-ℕ! ct
... | _ , refl = g★
gtrg gc-ℕ?  ct with ct-ℕ? ct
... | _ , refl = gℕ
gtrg gc-id★ ct with ct-id★ ct
... | _ , refl = g★

sealed : Term → Term
sealed m = m ⟪ unbind 0 0 ∷ [] , tail (seal 0) ⟫

module Spine (m : Term)
  (no-leaf : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Reach R → ¬ (V ∣ γ ⊢ m ⊑ R ∶ q))
  (Δ₀ : Ctxᵗ)
  (bdy : ∀ {Δᵢ Aᵢ A} → BdyTy Δ₀ Θ₀ Δᵢ Aᵢ (unseal 0) A → (Aᵢ ≡ ` 0) × G A)
  where

  -- THE INSIDE LEMMA: the left's sealed leaf (type X) against a spine
  -- reaching a tag, with no permission
  no-S : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → A ≡ ` 0 → Reach R → ¬ (V ∣ γ ⊢ sealed m ⊑ R ∶ q)
  no-S {V = V} eκ refl r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct q)
    with ct-X! ct
  ... | (_ , rh) , refl , refl = no-tag-at {V = V} {κₚ = κₚ} eκ rh p q
  no-S eκ eA (r-cast ng r) (⊑cast g _ d _ _) =
    no-S (trans (cg-none ng g) eκ) eA r d
  no-S eκ eA (r-⟪⟫ r) (⊑⟪⟫ I _ _ d _ _) = no-S (trans (same-κ I) eκ) eA r d
  no-S eκ eA (r-⟪⟫ r) (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-leaf r d
  no-S eκ eA r (⟪⟫⊑ _ _ _ _ d _ _) = no-leaf r d

  B : Term
  B = sealed m ⟪ Θ₀ , unseal 0 ⟫

  data LO : Term → Set where
    lo-B : LO B
    lo-c : ∀ {M c} → GCast c → LO M → LO (M ⟨ [] ∣ c ⟩)

  lo-ty : ∀ {Δ₂} {V : World Δ₀ Δ₂} {γ M R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → V ∣ γ ⊢ M ⊑ R ∶ q → G A
  lo-ty lo-B d with lty-bdy d
  ... | _ , _ , b = proj₂ (bdy b)
  lo-ty (lo-c gc _) d with lty-cast d
  ... | _ , ct = gtrg gc ct

  -- THE OUTSIDE LEMMA: the left outside its boundary
  no-LO : ∀ {Δ₂} {V : World Δ₀ Δ₂} {γ M R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → LO M → Reach R → ¬ (V ∣ γ ⊢ M ⊑ R ∶ q)
  no-LO {V = V} eκ lo r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
    with ct-X! ct
  ... | _ , refl , refl = no-G⊑var {V = record V { κʷ = κₚ }} (lo-ty lo d) p
  no-LO eκ lo (r-cast ng r) (⊑cast g _ d _ _) =
    no-LO (trans (cg-none ng g) eκ) lo r d
  no-LO eκ (lo-c gc lo) r-tag (cast⊑cast {p = p} d ct ct′ _)
    with ct-X! ct′
  ... | _ , refl , refl = no-G⊑varᵖ (gsrc gc ct) p
  no-LO eκ (lo-c gc lo) (r-cast _ r) (cast⊑cast d _ _ _) = no-LO eκ lo r d
  no-LO eκ (lo-c gc lo) r (cast⊑ _ d _ _) = no-LO eκ lo r d
  no-LO eκ lo (r-⟪⟫ r) (⊑⟪⟫ I _ _ d _ _) = no-LO (trans (same-κ I) eκ) lo r d
  no-LO eκ lo-B r (⟪⟫⊑ I _ _ _ d b _) =
    no-S (trans (same-κ I) eκ) (proj₁ (bdy b)) r d
  no-LO eκ lo-B (r-⟪⟫ r) (⟪⟫⊑⟪⟫ I _ d b _ _ _) =
    no-S (trans (same-κ I) eκ) (proj₁ (bdy b)) r d

------------------------------------------------------------------------
-- 13. C1 = the SimBackBlame counterexample L₆ ⊑ R₇ (PendingOpenings
-- §5d): NOT DERIVABLE in any world over its contexts with no
-- permission, at any index.  All three routes of HiddenNames §2
-- (matched, left-first, right-first) end at the right's tag against
-- the left's sealed value with no right check above it: `no-tag-at`.
------------------------------------------------------------------------

module C1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)
  open Runs
  open P4 using (nth)

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? : Coercion
  ℕ? = `ℕ ？ 0

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  S : Term
  S = 5★ ⟪ unb₀ , tail (seal 0) ⟫

  LB Lid L₆ RX RB R₇ : Term
  LB  = S ⟪ Θ₀ , unseal 0 ⟫
  Lid = LB ⟨ [] ∣ idᵖ ★ ⟩
  L₆  = Lid ⟨ [] ∣ ℕ? ⟩
  RX  = S ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩
  RB  = RX ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫
  R₇  = RB ⟨ [] ∣ ℕ? ⟩

  --   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  --   R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  L₀ R₀ : Term
  L₀ = ((Λ (ƛ (` 0) ∙ ` 0) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩)
          · 5★) ⟨ [] ∣ ℕ? ⟩
  R₀ = ((Λ (ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩))
          ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
  L₀-⊢ = tc

  R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
  R₀-⊢ = tc

  L₆-state : nth (evalTerms 30 L₀-⊢) 6 ≡ L₆
  L₆-state = refl

  R₇-state : nth (evalTerms 30 R₀-⊢) 7 ≡ R₇
  R₇-state = refl

  ΔR ΔRᵢ : Ctxᵗ
  ΔR  = allocate ★ empty
  ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])

  L₆-⊢ : ΔR ∣ [] ⊢ L₆ ⦂ `ℕ
  L₆-⊢ = tc

  R₇-⊢ : ΔR ∣ [] ⊢ R₇ ⦂ `ℕ
  R₇-⊢ = tc

  R₇-blames : ΔR ⊢ R₇ -→ blame 0 ∣ none
  R₇-blames = justStep refl

  L₆-never-blames : ∀ {ℓ} → ¬ (ΔR ⊢ L₆ -→* blame ℓ)
  L₆-never-blames r = all-reach {P = NotBlame} 20 L₆-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bdy-LB : ∀ {Δᵢ Aᵢ A} → BdyTy ΔR Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Aᵢ ≡ ` 0) × G A
  bdy-LB (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-★))
                 (_ , same-var here , same-var here)
                 (_ , same-★ , same-★) _) | refl | refl =
    refl , g★

  open Spine 5★ no-n★ ΔR bdy-LB

  -- C1 IS UNRELATED: every world over (ΔR, ΔR) with no permission
  c1-unrelated : ∀ {W : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₆ ⊑ R₇ ∶ q)
  c1-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-id★ lo-B)) (r-cast ng-ℕ? (r-⟪⟫ r-tag))

------------------------------------------------------------------------
-- 14. C3 = ModeCondition's `Esc.esc-cex-early` (both after TyBeta):
-- NOT DERIVABLE.  Matched boundaries compare `−X → +X` with
-- `−X → id(★)`: the seal joins X, so the ★ clause `+X ⊑ id(★)` needs X
-- permitted; each one-sided order meets `X ⊑ ℕ` or `ℕ ⊑ X`.
------------------------------------------------------------------------

module C3 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open TIE using (idX; revX; ΔL)
  open Rebase using (I★⁻)

  genE genE-body : Coercion
  genE-body = ((` 0) !) ↦ᵖ idᵖ ★
  genE      = genᵖ genE-body

  cE : Conv
  cE = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))

  --  LE = ((ν X:=ℕ. ((ΛY. λx:Y. x) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩⟨ℕ?ℓ0⟩
  --  RE = ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩ X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
  LE RE : Term
  LE = (((ν `ℕ · Λ idX ⟨ revX ⟩) · $ 5) ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE = ((ν `ℕ · (I★ ⟨ [] ∣ genE ⟩) ⟨ cE ⟩) · $ 5) ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE-⊢ : empty ∣ [] ⊢ LE ⦂ `ℕ
  LE-⊢ = tc

  RE-⊢ : empty ∣ [] ⊢ RE ⦂ `ℕ
  RE-⊢ = tc

  LB₁ RB₁ LA RA LE₁ RE₁ : Term
  LB₁ = idX ⟪ Θ₀ , revX ⟫
  RB₁ = (I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩) ⟪ Θ₀ , cE ⟫
  LA  = LB₁ · $ 5
  RA  = RB₁ · $ 5
  LE₁ = (LA ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE₁ = RA ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₁-state : nth (evalTerms 20 LE-⊢) 1 ≡ LE₁
  LE₁-state = refl

  RE₁-state : nth (evalTerms 30 RE-⊢) 1 ≡ RE₁
  RE₁-state = refl

  LE₁-⊢ : ΔL ∣ [] ⊢ LE₁ ⦂ `ℕ
  LE₁-⊢ = tc

  RE₁-⊢ : ΔL ∣ [] ⊢ RE₁ ⦂ `ℕ
  RE₁-⊢ = tc

  RE₁-blames : last (evalTerms 20 RE₁-⊢) ≡ blame 0
  RE₁-blames = refl

  LE₁-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₁ -→* blame ℓ)
  LE₁-never-blames r = all-reach {P = NotBlame} 20 LE₁-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  -- the matched conversions `−X → +X` ⊑ `−X → id(★)`: the seal joins X;
  -- with no permission a joined X is X⊑X, so `+X ⊑ id(★)` fails
  matched-conv : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂} {Δᵢ Δ′ᵢ Aᵢ A′ᵢ A A′ Θ Θ′}
    → κʷ W ≡ []
    → (b : BdyTy Δ₁ Θ Δᵢ Aᵢ revX A) (b′ : BdyTy Δ₂ Θ′ Δ′ᵢ A′ᵢ cE A′)
    → ¬ BdyConversionImp W b b′
  matched-conv eκ (bdy-ty _ _ _ _ _)
    (bdy-ty _ (conv-tail (conv-mid (conv-fun
       (conv-tail (conv-seal (_ , _ , l , _))) _))) _ _ _)
    (Wᶜ , ci , conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
       (conv-tail⊑tail (conv-seal⊑seal j)) (conv-unseal⊑id★ h _)))) =
    no-tag★ {V = Wᶜ} (trans (conv-same-κ ci) eκ) l j h

  ct-genE-body : ∀ {Δ₀ μ B A} → CastTy Δ₀ μ genE-body B A → A ≡ ` 0 ⇒ ★
  ct-genE-body (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-genE-body (cast-ty (⊢fun (⊢tag-var _ _ _) (⊢id _ _)) _) = refl

  lty-ƛ : ∀ {V : World Δ Δ′} {γ A₀ N M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → V ∣ γ ⊢ ƛ A₀ ∙ N ⊑ M′ ∶ q → Σ[ B ∈ Ty ] A ≡ A₀ ⇒ B
  lty-ƛ (ƛ⊑ƛ _ _ _)       = _ , refl
  lty-ƛ (⊑cast _ _ d _ _) = lty-ƛ d
  lty-ƛ (⊑⟪⟫ _ _ _ d _ _) = lty-ƛ d

  rty-cast : ∀ {V : World Δ Δ′} {γ M M′ μ′ c′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → V ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q → Σ[ B′ ∈ Ty ] CastTy Δ′ μ′ c′ B′ A′
  rty-cast (cast⊑cast _ _ ct′ _) = _ , ct′
  rty-cast (⊑cast _ _ _ ct _)    = _ , ct
  rty-cast (cast⊑ _ d _ _)       = rty-cast d
  rty-cast (⟪⟫⊑ _ _ _ _ d _ _)   = rty-cast d
  rty-cast (Λ⊑ _ _ _ _ _ d _)    = rty-cast d
  rty-cast (ν⊑ d _ _ _)          = rty-cast d
  rty-cast (blame⊑ _ ⊢M′ _) with cast-inv ⊢M′
  ... | _ , _ , ct = _ , ct

  no-var⇒⊑ℕ⇒ : ∀ {V : World Δ Δ′} {X B B′} → ¬ ((` X ⇒ B) ⊑ᵂ⟨ V ⟩ (`ℕ ⇒ B′))
  no-var⇒⊑ℕ⇒ {V = V} {X} {B} {B′} q
    with plain-idx {V = V} {A′ = `ℕ ⇒ B′} (nf-⇒ {A = ` X} {B = B}) q
  ... | ⇒⊑⇒ () _

  no-ℕ⇒⊑var⇒ : ∀ {V : World Δ Δ′} {X B B′} → ¬ ((`ℕ ⇒ B) ⊑ᵂ⟨ V ⟩ (` X ⇒ B′))
  no-ℕ⇒⊑var⇒ {V = V} {X} {B} {B′} q
    with plain-idx {V = V} {A′ = ` X ⇒ B′} (nf-⇒ {A = `ℕ} {B = B}) q
  ... | ⇒⊑⇒ () _

  idx : ∀ {Δ₁ Δ₂} {V′ : World Δ₁ Δ₂} {γ M M′ A₁ A₂} {r : A₁ ⊑ᵂ⟨ V′ ⟩ A₂}
    → V′ ∣ γ ⊢ M ⊑ M′ ∶ r → A₁ ⊑ᵂ⟨ V′ ⟩ A₂
  idx {r = r} _ = r

  no-fun : ∀ {V : World ΔL ΔL} {γ A A′ B B′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → A ≡ `ℕ ⇒ B → A′ ≡ `ℕ ⇒ B′ → ¬ (V ∣ γ ⊢ LB₁ ⊑ RB₁ ∶ q)
  no-fun eκ _ _ (⟪⟫⊑⟪⟫ _ _ _ b b′ bc _) = matched-conv eκ b b′ bc
  no-fun eκ eA refl (⟪⟫⊑ {Wᵢ = Vi} _ _ _ _ d _ _) with lty-ƛ d
  ... | _ , refl = no-var⇒⊑ℕ⇒ {V = Vi} (idx d)
  no-fun eκ refl _ (⊑⟪⟫ {Wᵢ = Vi} _ _ _ d _ _) with rty-cast d
  ... | _ , ct with ct-genE-body ct
  ... | refl = no-ℕ⇒⊑var⇒ {V = Vi} (idx d)

  no-app : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ RA ∶ q)
  no-app eκ (·⊑· f (κ⊑κ lit-$ _)) = no-fun eκ refl refl f

  no-LAℕ!-RA : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RA ∶ q)
  no-LAℕ!-RA eκ (cast⊑ _ d _ _) = no-app eκ d

  no-LE₁-RA : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LE₁ ⊑ RA ∶ q)
  no-LE₁-RA eκ (cast⊑ _ d _ _) = no-LAℕ!-RA eκ d

  no-LA-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ RE₁ ∶ q)
  no-LA-RE₁ eκ (⊑cast g _ d _ _) = no-app (trans (cg-none ng-ℕ? g) eκ) d

  no-LAℕ!-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RE₁ ∶ q)
  no-LAℕ!-RE₁ eκ (cast⊑cast d _ _ _) = no-app eκ d
  no-LAℕ!-RE₁ eκ (⊑cast g _ d _ _) =
    no-LAℕ!-RA (trans (cg-none ng-ℕ? g) eκ) d
  no-LAℕ!-RE₁ eκ (cast⊑ _ d _ _) = no-LA-RE₁ eκ d

  -- C3 IS UNRELATED: every world over (ΔL, ΔL) with no permission
  c3-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₁ ⊑ RE₁ ∶ q)
  c3-unrelated eκ (cast⊑cast d _ _ _) = no-LAℕ!-RA eκ d
  c3-unrelated eκ (⊑cast g _ d _ _) = no-LE₁-RA (trans (cg-none ng-ℕ? g) eκ) d
  c3-unrelated eκ (cast⊑ _ d _ _) = no-LAℕ!-RE₁ eκ d

------------------------------------------------------------------------
-- 15. C2 = ModeCondition's `Esc.esc-cex` (the late pair, P4 B4's own
-- inner pair `S ⊑ J`): NOT DERIVABLE.  Its right spine reaches the tag
-- `X!` through `ℕ?`, `id(★)` and three boundaries, none of which grants.
------------------------------------------------------------------------

module C2 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open TIE using (ΔL; ΔLᵢ)
  open C3 using (LE; RE; LE-⊢; RE-⊢)

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S₄ LB₄ Lℕ LE₃ RX J RU RI RB₅ RE₅ : Term
  S₄  = sealed ($ 5)
  LB₄ = S₄ ⟪ Θ₀ , unseal 0 ⟫
  Lℕ  = LB₄ ⟨ [] ∣ `ℕ ! ⟩
  LE₃ = Lℕ ⟨ [] ∣ `ℕ ？ 0 ⟩
  RX  = S₄ ⟨ X∼★ ∷ [] ∣ (` 0) ! ⟩
  J   = RX ⟪ Θ₀ , id★ᶜ ⟫
  RU  = J ⟪ unb₀ , id★ᶜ ⟫
  RI  = RU ⟨ ★∼X ∷ [] ∣ idᵖ ★ ⟩
  RB₅ = RI ⟪ Θ₀ , id★ᶜ ⟫
  RE₅ = RB₅ ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₃-state : nth (evalTerms 20 LE-⊢) 3 ≡ LE₃
  LE₃-state = refl

  RE₅-state : nth (evalTerms 30 RE-⊢) 5 ≡ RE₅
  RE₅-state = refl

  -- J is P4 B4's J verbatim
  J-is-P4 : J ≡ P4.J
  J-is-P4 = refl

  LE₃-⊢ : ΔL ∣ [] ⊢ LE₃ ⦂ `ℕ
  LE₃-⊢ = tc

  RE₅-⊢ : ΔL ∣ [] ⊢ RE₅ ⦂ `ℕ
  RE₅-⊢ = tc

  RE₅-blames : last (evalTerms 20 RE₅-⊢) ≡ blame 0
  RE₅-blames = refl

  LE₃-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₃ -→* blame ℓ)
  LE₃-never-blames r = all-reach {P = NotBlame} 20 LE₃-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bdy-LB₄ : ∀ {Δᵢ Aᵢ A} → BdyTy ΔL Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Aᵢ ≡ ` 0) × G A
  bdy-LB₄ (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB₄ (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-ℕ))
                  (_ , same-var here , same-var here)
                  (_ , same-ℕ , same-ℕ) _) | refl | refl =
    refl , gℕ

  open Spine ($ 5) no-$ ΔL bdy-LB₄

  -- C2 IS UNRELATED: every world over (ΔL, ΔL) with no permission
  c2-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₃ ⊑ RE₅ ∶ q)
  c2-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-ℕ! lo-B))
      (r-cast ng-ℕ? (r-⟪⟫ (r-cast ng-id (r-⟪⟫ (r-⟪⟫ r-tag)))))

------------------------------------------------------------------------
-- 16. The pop walk for C4 and C4g.  The left has not instantiated; the
-- right has (Inst, TyBeta): `[+X^α] Bd ⟨−X → id(★)⟩` under `id(★) →
-- id(★)`, applied, under `ℕ?`.  No right cast on the way grants, so
-- every world of a derivation has no permission; the walk reaches the
-- left's Λ or λ against Bd, whatever was pushed or popped, and the
-- instance's lemmas refute that.
------------------------------------------------------------------------

open import proof.TypeSafety.CoercionTyping using (coercion-trg)

instL : Coercion
instL = instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !))

ct-instL : ∀ {μ B A} → CastTy Δ μ instL B A → A ≡ ★ ⇒ ★
ct-instL (cast-ty d _) = sym (coercion-trg d)

module PopWalk (Bd : Term)
  (no-idXBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ idX′ ⊑ Bd ∶ q))
  (no-ΛBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⊑ Bd ∶ q))
  (no-FBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⟨ [] ∣ instL ⟩ ⊑ Bd ∶ q))
  where

  RBd GR F : Term
  RBd = Bd ⟪ Θ₀ , C3.cE ⟫
  GR  = RBd ⟨ [] ∣ Rebase.id★↦ ⟩
  F   = Λ idX′ ⟨ [] ∣ instL ⟩

  w-idX-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ idX′ ⊑ RBd ∶ q)
  w-idX-RB eκ (⊑⟪⟫ I _ _ d _ _) = no-idXBd (trans (same-κ I) eκ) d

  w-idX-GR : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ idX′ ⊑ GR ∶ q)
  w-idX-GR eκ (⊑cast g _ d _ _) = w-idX-RB (trans (cg-none ng-id★↦ g) eκ) d

  w-Λ-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⊑ RBd ∶ q)
  w-Λ-RB eκ (Λ⊑ claim-fresh _ _ _ _ d _) = w-idX-RB eκ d
  w-Λ-RB eκ (Λ⊑ (claim-pop (open1 _ _ _)) _ _ _ _ d _) = w-idX-RB eκ d
  w-Λ-RB eκ (⊑⟪⟫ I _ _ d _ _) = no-ΛBd (trans (same-κ I) eκ) d

  w-Λ-GR : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⊑ GR ∶ q)
  w-Λ-GR eκ (Λ⊑ claim-fresh _ _ _ _ d _) = w-idX-GR eκ d
  w-Λ-GR eκ (Λ⊑ (claim-pop (open1 _ _ _)) _ _ _ _ d _) = w-idX-GR eκ d
  w-Λ-GR eκ (⊑cast g _ d _ _) = w-Λ-RB (trans (cg-none ng-id★↦ g) eκ) d

  w-F-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ F ⊑ RBd ∶ q)
  w-F-RB eκ (cast⊑ cc-plain d _ _) = w-Λ-RB eκ d
  w-F-RB eκ (⊑⟪⟫ I _ _ d _ _) = no-FBd (trans (same-κ I) eκ) d

  w-F-GR : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ F ⊑ GR ∶ q)
  w-F-GR eκ (cast⊑cast d _ _ _) = w-Λ-RB eκ d
  w-F-GR eκ (cast⊑ cc-plain d _ _) = w-Λ-GR eκ d
  w-F-GR eκ (⊑cast g _ d _ _) = w-F-RB (trans (cg-none ng-id★↦ g) eκ) d

  w-app : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ F · C1.5★ ⊑ GR · C1.5★ ∶ q)
  w-app eκ (·⊑· f _) = w-F-GR eκ f

  w-L-app : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ (F · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩ ⊑ GR · C1.5★ ∶ q)
  w-L-app eκ (cast⊑ cc-plain d _ _) = w-app eκ d

  w-app-R : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ F · C1.5★ ⊑ (GR · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩ ∶ q)
  w-app-R eκ (⊑cast g _ d _ _) = w-app (trans (cg-none ng-ℕ? g) eκ) d

  -- THE WALK: the initial-shaped pair is unrelated with no permission
  walk : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ []
    → ¬ (V ∣ γ ⊢ (F · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩
                 ⊑ (GR · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩ ∶ q)
  walk eκ (cast⊑cast d _ _ _) = w-app eκ d
  walk eκ (⊑cast g _ d _ _) = w-L-app (trans (cg-none ng-ℕ? g) eκ) d
  walk eκ (cast⊑ cc-plain d _ _) = w-app-R eκ d

------------------------------------------------------------------------
-- 17. C4 (HiddenNames §5, a POP at X⊑★ in HEAD): NOT DERIVABLE.  The
-- popped X is joined; nothing grants its rep. var, so the right's
-- source-scope tag `x⟨X!⟩` cannot face the left's x.
------------------------------------------------------------------------

module C4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open C1 using (5★; ℕ?; L₀; R₀; L₀-⊢; R₀-⊢; ΔR; ΔRᵢ)
  open Rebase using (id★↦)

  bodyR : Term
  bodyR = ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)

  RBp R₂ : Term
  RBp = bodyR ⟪ Θ₀ , C3.cE ⟫
  R₂  = ((RBp ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  R₂-state : nth (evalTerms 30 R₀-⊢) 2 ≡ R₂
  R₂-state = refl

  R₂-⊢ : ΔR ∣ [] ⊢ R₂ ⦂ `ℕ
  R₂-⊢ = tc

  R₂-blames : last (evalTerms 20 R₂-⊢) ≡ blame 0
  R₂-blames = refl

  L₀-never-blames : ∀ {ℓ} → ¬ (empty ⊢ L₀ -→* blame ℓ)
  L₀-never-blames r = all-reach {P = NotBlame} 30 L₀-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  -- the body: x against x⟨X!⟩, no permission
  no-xtag : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {A₀′ p₀ γ μ k A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ []
    → ¬ (V ∣ ctx-imp (` 0) A₀′ p₀ ∷ γ ⊢ ` 0 ⊑ (` 0) ⟨ μ ∣ (` k) ! ⟩ ∶ q)
  no-xtag {V = V} eκ (⊑cast {κₚ = κₚ} {p = p} _ (raise-∷ _) d ct q)
    with ct-X! ct | lty-x d
  ... | (_ , rh) , refl , refl | refl = no-tag-at {V = V} {κₚ = κₚ} eκ rh p q

  no-idXBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ idX′ ⊑ bodyR ∶ q)
  no-idXBd eκ (ƛ⊑ƛ _ _ d) = no-xtag eκ d

  no-ΛBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⊑ bodyR ∶ q)
  no-ΛBd eκ (Λ⊑ claim-fresh _ _ _ _ d _) = no-idXBd eκ d
  no-ΛBd eκ (Λ⊑ (claim-pop (open1 _ _ _)) _ _ _ _ d _) = no-idXBd eκ d

  no-FBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⟨ [] ∣ instL ⟩ ⊑ bodyR ∶ q)
  no-FBd eκ (cast⊑ cc-plain d _ _) = no-ΛBd eκ d

  open PopWalk bodyR no-idXBd no-ΛBd no-FBd

  -- C4 IS UNRELATED: every world over (empty, ΔR) with no permission
  c4-unrelated : ∀ {W : World empty ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₀ ⊑ R₂ ∶ q)
  c4-unrelated = walk

------------------------------------------------------------------------
-- 18. C4g (HiddenNames §19, C4 with a gen-mode tag): NOT DERIVABLE.  The
-- right's body is the gen wrapper `(…)⟨X! → id(★)⟩^[X:★∼X]`, which
-- grants nothing (its codomain does not check), so the index
-- `X→X ⊑ X→★` of the left's λx:X.x against it needs X⊑★ at a joined,
-- unpermitted X.
------------------------------------------------------------------------

module C4g where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open C1 using (5★; ℕ?; L₀; L₀-⊢; ΔR)
  open C3 using (genE; genE-body; cE; RB₁)
  open C4 using (L₀-never-blames)
  open Rebase using (id★↦; I★⁻)

  R0g R2g Bdg : Term
  R0g = (((I★ ⟨ [] ∣ genE ⟩) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩)
          · 5★) ⟨ [] ∣ ℕ? ⟩
  R2g = ((RB₁ ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  Bdg = I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩

  R0g-⊢ : empty ∣ [] ⊢ R0g ⦂ `ℕ
  R0g-⊢ = tc

  R2g-state : nth (evalTerms 30 R0g-⊢) 2 ≡ R2g
  R2g-state = refl

  R2g-⊢ : ΔR ∣ [] ⊢ R2g ⦂ `ℕ
  R2g-⊢ = tc

  R2g-blames : last (evalTerms 30 R2g-⊢) ≡ blame 0
  R2g-blames = refl

  ct-genE′ : ∀ {Δ₀ μ B A} → CastTy Δ₀ μ genE-body B A
    → (Δ₀ ∋tv 0) × (A ≡ ` 0 ⇒ ★)
  ct-genE′ (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-genE′ (cast-ty (⊢fun (⊢tag-var tv _ _) (⊢id _ _)) _) = tv , refl

  -- X→X ⊑ X′→★ with no permission (X′ a right name)
  no-idx-X→★ : ∀ {V : World Δ Δ′} {X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
    → ¬ ((` 0 ⇒ ` 0) ⊑ᵂ⟨ V ⟩ (` X′ ⇒ ★))
  no-idx-X→★ {V = V} {X′} eκ rh q
    with plain-idx {V = V} {A′ = ` X′ ⇒ ★} nf-⇒ q
  ... | ⇒⊑⇒ p₁ (X⊑★ h) = no-tag★ {V = V} eκ rh (var⊑var p₁) h

  -- ∀X.X→X ⊑ X′→★ with no permission, at any pending names
  open-∀id : ∀ {μ} cs {ρ b}
    → OpenImp μ cs ρ (`∀ (` 0 ⇒ ` 0)) (` b ⇒ ★) → μ ∋ˡ b := X⊑★
  open-∀id [] (∀⊑ _ _ (⇒⊑⇒ () _))
  open-∀id (c ∷ []) (⇒⊑⇒ X⊑X (X⊑★ h)) = h
  open-∀id (c ∷ c′ ∷ cs) ()

  no-idx-∀ : ∀ {V : World Δ Δ′} {X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
    → ¬ (`∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ V ⟩ (` X′ ⇒ ★))
  no-idx-∀ {V = V} eκ rh q =
    no★-right {V = V} eκ rh (open-∀id (map (emb (ηᴿʷ V)) (πʷ V)) q)

  no-idXBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ idX′ ⊑ Bdg ∶ q)
  no-idXBd {V = V} eκ (⊑cast _ _ d ct q) with lty-idX d | ct-genE′ ct
  ... | refl | (_ , rh) , refl = no-idx-X→★ {V = V} eκ rh q

  no-ΛBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⊑ Bdg ∶ q)
  no-ΛBd eκ (Λ⊑ claim-fresh _ _ _ _ d _) = no-idXBd eκ d
  no-ΛBd eκ (Λ⊑ (claim-pop (open1 _ _ _)) _ _ _ _ d _) = no-idXBd eκ d
  no-ΛBd {V = V} eκ (⊑cast _ _ d ct q) with lty-ΛidX d | ct-genE′ ct
  ... | refl | (_ , rh) , refl = no-idx-∀ {V = V} eκ rh q

  no-FBd : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ Λ idX′ ⟨ [] ∣ instL ⟩ ⊑ Bdg ∶ q)
  no-FBd eκ (cast⊑ cc-plain d _ _) = no-ΛBd eκ d
  no-FBd {V = V} eκ (⊑cast _ _ d ct q) with lty-cast d | ct-genE′ ct
  ... | _ , ct₀ | _ , refl with ct-instL ct₀
  ... | refl with plain-idx {V = V} {A′ = ` 0 ⇒ ★} nf-⇒ q
  ... | ⇒⊑⇒ () _
  no-FBd eκ (cast⊑cast d ct ct′ q) with ct-instL ct | ct-genE′ ct′
  ... | refl | _ , refl with q
  ... | ⇒⊑⇒ () _

  open PopWalk Bdg no-idXBd no-ΛBd no-FBd

  -- C4g IS UNRELATED: every world over (empty, ΔR) with no permission
  c4g-unrelated : ∀ {W : World empty ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₀ ⊑ R2g ∶ q)
  c4g-unrelated = walk

  -- the gen wrapper `X! → id(★)` grants nothing (C2's), unlike P4's
  -- `X! → X?`
  c2-wrapper-no-grant : NoGrant genE-body
  c2-wrapper-no-grant = ng-tag↦id★

------------------------------------------------------------------------
-- 19. C5 (Permissions.md §5), its programs and runs.  In Permissions'
-- relation the pair (L state 3, R state 5) is related through the
-- left's payload view `⟪⟫⊑` under the grant of the right's `X?`
-- (`Permissions.C5.c5`).  HERE R1 rejects that step (`r1-rejects-c5`)
-- and §19a proves the pair unrelated in every world.
--
-- Source programs (unrelated: ∀Y.Y→Y ⋢ ∀Y.★→Y, the shared Y is X⊑X):
--   L  (ΛY. λx:Y. x) [ℕ] 5
--   R  (ΛY. λx:★. (x : Y)) [ℕ] (5 : ★)
------------------------------------------------------------------------

module C5 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth; W₄; W₄²; W₄²-wf; W₄²¹; v₀; S; unb₀; bS; bUnsealL;
                 Ξ₄; ϱ₄; p0; module Wf₄)
  open TIE using (ΔL; ΔLᵢ)
  open Rebase using (Wc-bind²; Wc-bind²-conv; unbind₀-int)
  open C1 using (5★)

  -- the initial programs (cast terms); the left is P1's left
  L5 R5 : Term
  L5 = (ν `ℕ · Λ (ƛ (` 0) ∙ ` 0) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5
  R5 = (ν `ℕ · Λ (ƛ ★ ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩))
          ⟨ reveal 0 (★ ⇒ ` 0) ⟩) · 5★

  L5-⊢ : empty ∣ [] ⊢ L5 ⦂ `ℕ
  L5-⊢ = tc

  R5-⊢ : empty ∣ [] ⊢ R5 ⦂ `ℕ
  R5-⊢ = tc

  -- the related pair: left state 3, right state 5
  5★ˣ C5L C5R : Term
  5★ˣ = $ 5 ⟨ X∼X ∷ [] ∣ `ℕ ! ⟩
  C5L = S ⟪ Θ₀ , unseal 0 ⟫
  C5R = (5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩) ⟪ Θ₀ , unseal 0 ⟫

  C5L-state : nth (evalTerms 10 L5-⊢) 3 ≡ C5L
  C5L-state = refl

  C5R-state : nth (evalTerms 20 R5-⊢) 5 ≡ C5R
  C5R-state = refl

  C5L-⊢ : ΔL ∣ [] ⊢ C5L ⦂ `ℕ
  C5L-⊢ = tc

  C5R-⊢ : ΔL ∣ [] ⊢ C5R ⦂ `ℕ
  C5R-⊢ = tc

  C5R-blames : last (evalTerms 10 C5R-⊢) ≡ blame 0
  C5R-blames = refl

  C5L-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ C5L -→* blame ℓ)
  C5L-never-blames r = all-reach {P = NotBlame} 10 C5L-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  -- the left's `−X` alone, under the grant: X right-only, αᴿ permitted
  WU : World ΔL ΔLᵢ
  WU = world 1 (skip []↪) (keep []↪) ϱ₄ [] (0 ∷ []) []

  IntU : Interior W₄²¹ unb₀ [] WU
  IntU = record
    { int-left   = unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  WU-wf : WfWorld WU
  WU-wf = wf-world (right-only joint[]) agree
    (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] p0
    where open Wf₄ 1 (skip []↪) (keep []↪) (0 ∷ [])

  ℕ!ˣ-ty : CastTy ΔLᵢ (X∼X ∷ []) (`ℕ !) `ℕ ★
  ℕ!ˣ-ty = cast-ty (⊢tag g-ℕ) refl

  chk-ty : CastTy ΔLᵢ (★∼X∼★ ∷ []) ((` 0) ？ 0) ★ (` 0)
  chk-ty = cast-ty (⊢check-var (_ , here) here check-cross) refl

  bC5R : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bC5R = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C5R}))))

  -- the earlier pairs of the same runs are unrelated: before the Beta,
  -- λx:X. x faces λx:★. x⟨X?⟩ at X→X ⊑ ★→X, whose domain needs X⊑★ at
  -- the joined, unpermitted X (no check is around the λ)
  no-early-idx : ¬ ((` 0 ⇒ ` 0) ⊑ᵂ⟨ W₄² ⟩ (★ ⇒ ` 0))
  no-early-idx (⇒⊑⇒ (X⊑★ ()) _)


  -- R1 REJECTS the step Permissions.C5.c5 used: the left's `−X^0` under
  -- the grant of αᴿ = 0, which is paired with αᴸ = 0
  r1-rejects-c5 : ¬ All (UnbindOK W₄²¹) unb₀
  r1-rejects-c5 (ok-unbind u ∷ []) with u (inj₁ here⇔)
  ... | ()

------------------------------------------------------------------------
-- 19a. C5 IS DEAD under R1/R2: not derivable in ANY world over its
-- contexts, at any κ (no `κʷ ≡ []`, no WfWorld hypothesis at the top).
-- Also its hidden variant (the left's payload view inside the right's own
-- hide `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`), which needs R1 after the right hide or
-- R2 at the matched hides.
--
-- The argument: the only way to put the left's sealed `S : X` against a
-- right ★ value that is not X-tagged is the payload view (`⟪⟫⊑` with
-- the left's `−X^0`) or the ★ clause `−X ⊑ id(★)`.  Both sit below the
-- right check `X?`, whose conclusion index `X ⊑ X` joins the left X to
-- the right X (so, by `wf-joint`, rep. var 0 is paired with the right X's
-- rep. var β) and whose premise index `X ⊑ ★` reads X⊑★ at that joined
-- name (so β is permitted).  `HasPermittedPartner _ 0` then refutes R1
-- or R2.  The routes that avoid the check meet `ℕ ⊑ X` or `X ⊑ ℕ`.
------------------------------------------------------------------------

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

-- a joined pair of names has paired rep. vars (`wf-joint`)
joint-pair : ∀ {P : RVar → RVar → Set} {ns ns′ n} {ι : ns ↪ n}
    {ι′ : ns′ ↪ n} {X X′ α β}
  → Joint P ι ι′ → ns ∋ˡ X := α → ns′ ∋ˡ X′ := β
  → emb ι X ≡ emb ι′ X′ → P α β
joint-pair joint[]         ()       _          _
joint-pair (both p j)      here     here       e  = p
joint-pair (both p j)      here     (there h′) ()
joint-pair (both p j)      (there h) here      ()
joint-pair (both p j)      (there h) (there h′) e =
  joint-pair j h h′ (suc-inj e)
joint-pair (left-only j)   here     h′         ()
joint-pair (left-only j)   (there h) h′        e  =
  joint-pair j h h′ (suc-inj e)
joint-pair (right-only j)  h        here       ()
joint-pair (right-only j)  h        (there h′) e  =
  joint-pair j h h′ (suc-inj e)

-- THE CHECK FACT: under a right check of X′ (rep. var β), a left name a
-- (rep. var α) whose conclusion index is `a ⊑ X′` and whose premise
-- index is `a ⊑ ★` has α paired with β, and β permitted in the premise
HasPP-chk : ∀ {V : World Δ Δ′} {κₚ a X′ α β}
  → WfWorld V → Δ ∋ᵗ a := α → Δ′ ∋ᵗ X′ := β
  → ` a ⊑ᵂ⟨ V ⟩ ` X′ → ` a ⊑ᵂ⟨ record V { κʷ = κₚ } ⟩ ★
  → HasPermittedPartner (record V { κʷ = κₚ }) α
HasPP-chk {V = V} {κₚ} {a} {X′} {β = β} wf lh rh q p =
  β , joint-pair (wf-joint wf) lh rh j , sym (lookup-unique h′ hβ)
  where
  j : Joins V a X′
  j = var⊑var (plain-idx {V = V} {A′ = ` X′} nf-var q)
  h : marksʷ (record V { κʷ = κₚ }) ∋ˡ emb (ηᴸʷ V) a := X⊑★
  h = var⊑★ (plain-idx {V = record V { κʷ = κₚ }} {A′ = ★} nf-var p)
  h′ : dmarks (ηᴿʷ V) κₚ ∋ˡ emb (ηᴿʷ V) X′ := X⊑★
  h′ = subst (λ c → dmarks (ηᴿʷ V) κₚ ∋ˡ c := X⊑★) j h
  hβ : dmarks (ηᴿʷ V) κₚ ∋ˡ emb (ηᴿʷ V) X′ := permit β κₚ
  hβ = dmarks-emb (ηᴿʷ V) κₚ rh

-- the name and rep. var of a one-entry unbind, read off its interior or
-- its conversion context
del-lookup : ∀ {α Δ₀ X Δ₁} → α ⊢- Δ₀ at X ⇒ Δ₁ → Δ₀ ∋ˡ X := α
del-lookup del-here      = here
del-lookup (del-there d) = there (del-lookup d)

unb1-lookup : ∀ {Γ Γᵢ X α} → Γ ⊢ⁱ (unbind X α ∷ []) ⇒ Γᵢ → Γ ∋ᵗ X := α
unb1-lookup (interior (changes∷ changes[] (step-unbind _ d _))) =
  del-lookup d

unb1-conv : ∀ {Γ Γᶜ Y X α β} → Γ ⊢ᶜ (unbind X α ∷ []) ⇒ Γᶜ
  → Γ ∋ᵗ Y := β → Γᶜ ∋ᵗ Y := β
unb1-conv (conversion (conv-unbind _ conv[])) h = h

ct-X? : ∀ {μ X ℓ B A} → CastTy Δ μ ((` X) ？ ℓ) B A
  → (Δ ∋tv X) × (B ≡ ★) × (A ≡ ` X)
ct-X? (cast-ty (⊢check ()) _)
ct-X? (cast-ty (⊢check-var tv _ _) _) = tv , refl , refl

-- the outer +X boundary of C5's two sides (and of the hidden variant)
bdy-C5 : ∀ {Δᵢ Aᵢ A} → BdyTy TIE.ΔL Θ₀ Δᵢ Aᵢ (unseal 0) A
  → (Aᵢ ≡ ` 0) × (A ≡ `ℕ)
bdy-C5 (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
  with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
bdy-C5 (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-ℕ))
               (_ , same-var here , same-var here)
               (_ , same-ℕ , same-ℕ) _) | refl | refl =
  refl , refl

module C5Dead where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open TIE using (ΔL; ΔLᵢ)
  open P4 using (S; unb₀; id★ᶜ)
  open C5 using (5★ˣ; C5L; C5R; C5L-⊢; C5L-never-blames)
  open C1 using (5★)

  -- a literal against a right check of a name: `ℕ ⊑ X`
  no-$-chk : ∀ {V : World Δ Δ′} {γ n M′ μ′ X ℓ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ $ n ⊑ M′ ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶ q)
  no-$-chk {V = V} (⊑cast _ _ d ct q) with ct-X? ct | lty-$ d
  ... | _ , refl , refl | refl = no-ℕ⊑var {V = V} q

  -- the right cores under the check: C5's `5⟨ℕ!⟩` and the hidden
  -- variant's `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`
  data Core : Term → Set where
    c-5   : ∀ {n μ} → Core ($ n ⟨ μ ∣ `ℕ ! ⟩)
    c-hid : Core (5★ ⟪ unb₀ , id★ᶜ ⟫)

  -- "the left name 0's rep. var has a permitted partner"
  HP0 : World Δ Δ′ → Set
  HP0 {Δ = Δ} U = ∀ {α} → Δ ∋ᵗ 0 := α → HasPermittedPartner U α

  hp0-int : ∀ {U : World Δ Δ′} {Uᵢ : World Δ Δ′ᵢ} {Θ′}
    → Interior U [] Θ′ Uᵢ → HP0 U → HP0 Uᵢ
  hp0-int I hp lh = hasPP-int I (hp lh)

  -- S against an ℕ-tagged literal: X ⊑ ℕ, or the payload view (R1)
  no-S-5 : ∀ {U : World Δ Δ′} {γ n μ A A′} {q : A ⊑ᵂ⟨ U ⟩ A′}
    → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ $ n ⟨ μ ∣ `ℕ ! ⟩ ∶ q)
  no-S-5 {U = U} refl hp (⊑cast {κₚ = κₚ} _ _ d ct _) with ct-ℕ! ct
  ... | refl , refl = no-var⊑ℕ {V = record U { κʷ = κₚ }} (C3.idx d)
  no-S-5 {U = U} eA hp (⟪⟫⊑ I (ok-unbind u ∷ []) _ _ _ _ _) =
    r1-fails {W = U} (hp (unb1-lookup (int-left I))) u

  -- S against the hidden core: the right hide keeps HP0 (then no-S-5),
  -- the payload view fails R1, the matched hides fail R2
  no-S-core : ∀ {U : World Δ Δ′} {γ Q A A′} {q : A ⊑ᵂ⟨ U ⟩ A′}
    → Core Q → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ Q ∶ q)
  no-S-core c-5 eA hp d = no-S-5 eA hp d
  no-S-core c-hid eA hp (⊑⟪⟫ I _ _ d _ _) = no-S-5 eA (hp0-int I hp) d
  no-S-core {U = U} c-hid eA hp (⟪⟫⊑ I (ok-unbind u ∷ []) _ _ _ _ _) =
    r1-fails {W = U} (hp (unb1-lookup (int-left I))) u
  no-S-core c-hid eA hp
    (⟪⟫⊑⟪⟫ I _ _ (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _)
      (Wᶜ , ci , conv-tail⊑tail (conv-seal⊑id★ _ lu)) _) =
    r1-fails {W = Wᶜ} (hasPP-conv ci (hp lh)) (lu (unb1-conv (conv-left ci) lh))
    where lh = unb1-lookup (int-left I)

  -- S against a core under the right check `X?`: THE CHECK FACT gives
  -- HP0 in the premise world
  no-S-chk : ∀ {V : World Δ Δ′} {γ Q μ′ X ℓ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Core Q → WfWorld V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ Q ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶ q)
  no-S-chk {V = V} core wf refl (⊑cast {κₚ = κₚ} {p = p} _ _ d ct q)
    with ct-X? ct
  ... | (_ , rh) , refl , refl =
    no-S-core core refl
      (λ lh → HasPP-chk {V = V} {κₚ = κₚ} wf lh rh q p) d
  no-S-chk core wf eA (⟪⟫⊑ _ _ _ _ d _ _) = no-$-chk d

  module Outer (Q : Term) (core : Core Q) where
    RinQ RQ : Term
    RinQ = Q ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩
    RQ   = RinQ ⟪ Θ₀ , unseal 0 ⟫

    -- a literal against RQ: its right type is ℕ
    rty-$RQ : ∀ {Δ₁} {V : World Δ₁ ΔL} {γ n A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
      → V ∣ γ ⊢ $ n ⊑ RQ ∶ q → A′ ≡ `ℕ
    rty-$RQ (⊑⟪⟫ _ _ _ _ b _) = proj₂ (bdy-C5 b)

    no-S-RQ : ∀ {Δ₁} {V : World Δ₁ ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
      → A ≡ ` 0 → ¬ (V ∣ γ ⊢ S ⊑ RQ ∶ q)
    no-S-RQ eA (⊑⟪⟫ _ _ wf d _ _) = no-S-chk core wf eA d
    no-S-RQ {V = V} refl (⟪⟫⊑ _ _ _ _ d _ q) with rty-$RQ d
    ... | refl = no-var⊑ℕ {V = V} q
    no-S-RQ eA (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-$-chk d

    no-L-RinQ : ∀ {Δ₂} {V : World ΔL Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
      → ¬ (V ∣ γ ⊢ C5L ⊑ RinQ ∶ q)
    no-L-RinQ {V = V} (⊑cast _ _ d ct q) with ct-X? ct | lty-bdy d
    ... | _ , refl , refl | _ , _ , b with bdy-C5 b
    ...   | _ , refl = no-ℕ⊑var {V = V} q
    no-L-RinQ (⟪⟫⊑ _ _ _ wf d b _) = no-S-chk core wf (proj₁ (bdy-C5 b)) d

    -- THE TOP: every world over (ΔL, ΔL), any κ
    no-top : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ C5L ⊑ RQ ∶ q)
    no-top (⟪⟫⊑⟪⟫ _ wf d b _ _ _) = no-S-chk core wf (proj₁ (bdy-C5 b)) d
    no-top (⟪⟫⊑ _ _ _ _ d b _)    = no-S-RQ (proj₁ (bdy-C5 b)) d
    no-top (⊑⟪⟫ _ _ _ d _ _)      = no-L-RinQ d

  -- C5 IS UNRELATED (L state 3, R state 5), in every world, at any κ
  C5R-is : C5R ≡ Outer.RQ (5★ˣ) c-5
  C5R-is = refl

  c5-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ C5R ∶ q)
  c5-unrelated = Outer.no-top 5★ˣ c-5

  -- the failing redex `5⟨ℕ!⟩⟨X?⟩` against the left VALUE S (M26's shape)
  -- is unrelated in every well-formed world, at any κ
  c5-redex-unrelated : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → WfWorld V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ 5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩ ∶ q)
  c5-redex-unrelated = no-S-chk c-5

  -- THE HIDDEN VARIANT: right `[+X^α] (([−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩)⟨X?ℓ0⟩) ⟨+X⟩`
  -- against C5L = `[+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩`
  Hid RH : Term
  Hid = 5★ ⟪ unb₀ , id★ᶜ ⟫
  RH  = Outer.RQ Hid c-hid

  RH-⊢ : ΔL ∣ [] ⊢ RH ⦂ `ℕ
  RH-⊢ = tc

  RH-blames : last (evalTerms 10 RH-⊢) ≡ blame 0
  RH-blames = refl

  hidden-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ RH ∶ q)
  hidden-unrelated = Outer.no-top Hid c-hid

------------------------------------------------------------------------
-- 19b. RULE, NOT WfWorld.  (1) The strong world invariant ("a permitted
-- right rep. var's partners are named on the left") kills P4: the
-- interior world of P4's own `S ⊑ S` (B3, B4) violates it.  (2) The weak
-- one ("... when the right rep. var is itself named") kills C5 (its
-- payload-view world `C5.WU` violates it) but not the hidden variant:
-- in the relation WITHOUT R1/R2 (Permissions.agda) the hidden variant is
-- derived using only P4's worlds W₄, W₄², W₄²¹, W₄ᴸ, W₄⁰ [αᴿ], so ANY
-- world-level condition that keeps P4 B3 and B4 keeps it.  The
-- difference is which rule meets those worlds (a payload view under the
-- grant, against P4's matched S ⊑ S), so the condition must be on the
-- rule.  (3) Anti-monotonicity: the payload view `S ⊑ 5⟨ℕ!⟩` at a
-- left-only X is derivable at κ = [] and not at κ = [αᴿ].
------------------------------------------------------------------------

StrongInv : World Δ Δ′ → Set
StrongInv {Δ = Δ} W = ∀ {α β} → Paired W α β → permit β (κʷ W) ≡ X⊑★
  → names Δ ∋ᵅ α

WeakInv : World Δ Δ′ → Set
WeakInv {Δ = Δ} {Δ′ = Δ′} W = ∀ {α β} → Paired W α β
  → permit β (κʷ W) ≡ X⊑★ → names Δ′ ∋ᵅ β → names Δ ∋ᵅ α

module WorldLevel where
  open import examples.TypeCheck using (tc; tf)
  import proof.DGG.notes.Permissions as P0
  open TIE using (ΔL; ΔLᵢ)
  open P4 using (W₄⁰; W₄ᴸ; W₄²; W₄²¹; S; unb₀; id★ᶜ; bS; v₀; ϱ₄; Ξ₄;
                 W₄⁰-wf)
  open Rebase using (Wcᴸ; unbind₀-int)
  open C5 using (WU; C5L; chk-ty)
  open C1 using (5★)
  open C5Dead using (Hid; RH; no-S-5)

  -- (1) P4's S ⊑ S interior (`P4.unb-int`, `P4.S⊑S`) violates StrongInv
  strong-kills-P4 : ¬ StrongInv (W₄⁰ (0 ∷ []))
  strong-kills-P4 s with s (inj₁ here⇔) refl
  ... | _ , ()

  -- (2a) C5's payload-view world violates WeakInv
  weak-kills-C5 : ¬ WeakInv WU
  weak-kills-C5 w with w (inj₁ here⇔) refl (0 , here)
  ... | _ , ()

  -- (2b) ... and P4's worlds satisfy it
  weak-W₄²¹ : WeakInv W₄²¹
  weak-W₄²¹ (inj₁ here⇔) _ _ = 0 , here
  weak-W₄²¹ (inj₁ (there⇔ ())) _ _
  weak-W₄²¹ (inj₂ ()) _ _

  weak-W₄² : WeakInv W₄²
  weak-W₄² (inj₁ here⇔) () _
  weak-W₄² (inj₁ (there⇔ ())) _ _
  weak-W₄² (inj₂ ()) _ _

  weak-W₄ᴸ : WeakInv W₄ᴸ
  weak-W₄ᴸ _ _ (_ , ())

  weak-W₄⁰ : ∀ {κ} → WeakInv (W₄⁰ κ)
  weak-W₄⁰ _ _ (_ , ())

  -- (2c) the hidden variant in the relation WITHOUT R1/R2, through P4's
  -- worlds only: matched +X (W₄²), the check grants (W₄²¹), the right's
  -- hide (W₄ᴸ, P4's `Wc-unbindᴿ`), the left's payload view (W₄⁰ [αᴿ],
  -- P4's `S ⊑ S` interior)
  IntL0 : P0.Interior P0.P4.W₄ᴸ unb₀ [] (P0.P4.W₄⁰ (0 ∷ []))
  IntL0 = record
    { int-left   = unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  ℕ!-ty : CastTy ΔL [] (`ℕ !) `ℕ ★
  ℕ!-ty = cast-ty (⊢tag g-ℕ) refl

  bHid : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bHid = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Hid}))))

  bRH : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bRH = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = RH}))))

  hidden-without-R : P0.P4.W₄ P0.∣ [] ⊢ C5L ⊑ RH ∶ ι⊑ι base-ℕ
  hidden-without-R =
    P0.⟪⟫⊑⟪⟫ (P0.Rebase.Wc-bind² P0.P4.v₀ here⇔) P0.P4.W₄²-wf
      (P0.⊑cast! {p = X⊑★ here} (P0.gr-? here)
        (P0.⊑⟪⟫ (P0.Rebase.Wc-unbindᴿ P0.P4.v₀) push-none P0.P4.W₄ᴸ-wf
          (P0.⟪⟫⊑ IntL0 bc-plain (P0.P4.W₄⁰-wf P0.P4.p0)
            (P0.⊑cast₀ (P0.κ⊑κ lit-$ (ι⊑ι base-ℕ)) ℕ!-ty (ι⊑★ base-ℕ))
            P0.P4.bS (X⊑★ here))
          bHid (X⊑★ here))
        chk-ty X⊑X)
      P0.P4.bUnsealL bRH
      (P0.P4.W₄² , P0.Rebase.Wc-bind²-conv P0.P4.v₀ here⇔
                 , P0.conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  -- (3) ANTI-MONOTONICITY: the payload view at a left-only X (P2's shape)
  IntLκ : ∀ {κ} → Interior (Wcᴸ {Ξ₄} {ϱ₄} κ) unb₀ [] (W₄⁰ κ)
  IntLκ = record
    { int-left   = unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  pv-at-[] : Wcᴸ {Ξ₄} {ϱ₄} [] ∣ [] ⊢ S ⊑ 5★ ∶ X⊑★ here
  pv-at-[] =
    ⟪⟫⊑ IntLκ (ok-unbind (λ _ → refl) ∷ []) bc-plain (W₄⁰-wf [])
      (⊑cast₀ (κ⊑κ lit-$ (ι⊑ι base-ℕ)) ℕ!-ty (ι⊑★ base-ℕ)) bS (X⊑★ here)

  pv-not-at-[αᴿ] : ∀ {γ A′} {q : ` 0 ⊑ᵂ⟨ W₄ᴸ ⟩ A′}
    → ¬ (W₄ᴸ ∣ γ ⊢ S ⊑ 5★ ∶ q)
  pv-not-at-[αᴿ] = no-S-5 refl hp
    where
    hp : C5Dead.HP0 W₄ᴸ
    hp here = 0 , inj₁ here⇔ , refl

  W₄ᴸ-is : W₄ᴸ ≡ Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ [])
  W₄ᴸ-is = refl

------------------------------------------------------------------------
-- 21. κ-WEAKENING: CastFun's obligation (previously MarkMono), WITH the
-- side condition that R1/R2 make necessary.  A derivation at κ is a
-- derivation at any κ′ ⊇ κ (as permissions: `Up κ κ′`) PROVIDED every
-- payload view and every ★ conversion clause in it still passes R1/R2 at
-- the raised permissions (`R12 κ′ d`), and the new permissions are rep.
-- vars of the store (for the interiors' `wf-permits`).  The indices and
-- the term context are raised pointwise (`raise`, `raiseE`): type
-- imprecision is monotone in the marks and `dmarks` is monotone in κ.
-- §19b(3) shows the side condition cannot be dropped.
------------------------------------------------------------------------

record Up (κ κ′ : List RVar) : Set where
  constructor mk-up
  field upAt : ∀ β → permit β κ ≡ X⊑★ → permit β κ′ ≡ X⊑★
open Up public

Lift : ImpEnv → ImpEnv → Set
Lift μ μ′ = ∀ {X} → μ ∋ˡ X := X⊑★ → μ′ ∋ˡ X := X⊑★

liftᵐ-∷ : ∀ {μ μ′ m} → Lift μ μ′ → Lift (m ∷ μ) (m ∷ μ′)
liftᵐ-∷ L here      = here
liftᵐ-∷ L (there h) = there (L h)

raise : ∀ {μ μ′ A B} → Lift μ μ′ → μ ⊢ A ⊑ B → μ′ ⊢ A ⊑ B
raise L ★⊑★          = ★⊑★
raise L (ι⊑ι b)      = ι⊑ι b
raise L X⊑X          = X⊑X
raise L (⇒⊑⇒ a b)    = ⇒⊑⇒ (raise L a) (raise L b)
raise L (∀⊑∀ a)      = ∀⊑∀ (raise (liftᵐ-∷ L) a)
raise L (⇒⊑★ a b)    = ⇒⊑★ (raise L a) (raise L b)
raise L (ι⊑★ b)      = ι⊑★ b
raise L (X⊑★ h)      = X⊑★ (L h)
raise L (∀⊑ nv i a)  = ∀⊑ nv i (raise (liftᵐ-∷ L) a)
raise L ∀★⊑★         = ∀★⊑★
raise L (∀⊑★ ns a)   = ∀⊑★ ns (raise (liftᵐ-∷ L) a)
raise L bot-elim     = bot-elim
raise L bot⊑★        = bot⊑★

raiseO : ∀ {μ μ′} cs {ρ A B} → Lift μ μ′
  → OpenImp μ cs ρ A B → OpenImp μ′ cs ρ A B
raiseO []       L p = raise L p
raiseO (c ∷ cs) {A = `∀ A}   L p = raiseO cs L p
raiseO (c ∷ cs) {A = ` X}    L ()
raiseO (c ∷ cs) {A = `ℕ}     L ()
raiseO (c ∷ cs) {A = `𝔹}     L ()
raiseO (c ∷ cs) {A = ★}      L ()
raiseO (c ∷ cs) {A = A ⇒ B}  L ()

∋-head : ∀ {A : Set} {m v : A} {μ : List A} → (m ∷ μ) ∋ˡ 0 := v → m ≡ v
∋-head here = refl

dmarks-lift : ∀ {κ κ′ ns n} → Up κ κ′ → (ι : ns ↪ n)
  → Lift (dmarks ι κ) (dmarks ι κ′)
dmarks-lift up []↪ ()
dmarks-lift up (keep {α = β} ι) {zero} h = here★ (upAt up β (∋-head h))
dmarks-lift up (keep ι) {suc X} (there h) = there (dmarks-lift up ι h)
dmarks-lift up (skip ι) {zero} here = here
dmarks-lift up (skip ι) {suc X} (there h) = there (dmarks-lift up ι h)

up-∷ : ∀ {κ κ′} γ → Up κ κ′ → Up (γ ∷ κ) (γ ∷ κ′)
up-∷ {κ} {κ′} γ up = mk-up go
  where
  go : ∀ β → permit β (γ ∷ κ) ≡ X⊑★ → permit β (γ ∷ κ′) ≡ X⊑★
  go β h with β ≡ᵇ γ
  ... | true  = refl
  ... | false = upAt up β h

permit-suc : ∀ β κ → permit (suc β) (map suc κ) ≡ permit β κ
permit-suc β []      = refl
permit-suc β (γ ∷ κ) with β ≡ᵇ γ
... | true  = refl
... | false = permit-suc β κ

permit-zero : ∀ κ → permit 0 (map suc κ) ≡ X⊑X
permit-zero []      = refl
permit-zero (γ ∷ κ) = permit-zero κ

up-suc : ∀ {κ κ′} → Up κ κ′ → Up (map suc κ) (map suc κ′)
up-suc {κ} {κ′} up = mk-up go
  where
  go : ∀ β → permit β (map suc κ) ≡ X⊑★ → permit β (map suc κ′) ≡ X⊑★
  go zero h with trans (sym (permit-zero κ)) h
  ... | ()
  go (suc β) h =
    trans (permit-suc β κ′) (upAt up β (trans (sym (permit-suc β κ)) h))

up-≡ : ∀ {κ₀ κ κ′} → κ₀ ≡ κ → Up κ κ′ → Up κ₀ κ′
up-≡ refl up = up

-- the raised world
infixl 7 _↑_
_↑_ : World Δ Δ′ → List RVar → World Δ Δ′
W ↑ κ′ = record W { κʷ = κ′ }

raiseI : ∀ {W : World Δ Δ′} {κ′ A A′} → Up (κʷ W) κ′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ↑ κ′ ⟩ A′
raiseI {W = W} up p =
  raiseO (map (emb (ηᴿʷ W)) (πʷ W)) (dmarks-lift up (ηᴿʷ W)) p

raiseE : ∀ {ns ns′ n μ μ′} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  → Lift μ μ′ → Entries μ ηᴸ ηᴿ → Entries μ′ ηᴸ ηᴿ
raiseE L []                   = []
raiseE L (ctx-imp A A′ p ∷ γ) = ctx-imp A A′ (raise L p) ∷ raiseE L γ

raiseγ : ∀ {W : World Δ Δ′} {κ′} → Up (κʷ W) κ′ → CtxImp W
  → CtxImp (W ↑ κ′)
raiseγ {W = W} up = raiseE (dmarks-lift up (ηᴿʷ W))

raise-∋ : ∀ {ns ns′ n μ μ′} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n} {L : Lift μ μ′}
    {γ : Entries μ ηᴸ ηᴿ} {x A A′ p}
  → γ ∋ʷ x ⦂ ctx-imp A A′ p → raiseE L γ ∋ʷ x ⦂ ctx-imp A A′ (raise L p)
raise-∋ Zʷ     = Zʷ
raise-∋ (Sʷ h) = Sʷ (raise-∋ h)

raise-rhs : ∀ {ns ns′ n μ μ′} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n} (L : Lift μ μ′)
  (γ : Entries μ ηᴸ ηᴿ) → rhs (raiseE L γ) ≡ rhs γ
raise-rhs L []      = refl
raise-rhs L (e ∷ γ) = cong (tyᴿ e ∷_) (raise-rhs L γ)

raise-RaiseCtx : ∀ {ns ns′ n μ μ₁ μ′ μ₁′} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ ηᴿ}
    (L : Lift μ μ′) (L₁ : Lift μ₁ μ₁′)
  → RaiseCtx γ γ′ → RaiseCtx (raiseE L γ) (raiseE L₁ γ′)
raise-RaiseCtx L L₁ raise-[]     = raise-[]
raise-RaiseCtx L L₁ (raise-∷ rc) = raise-∷ (raise-RaiseCtx L L₁ rc)

raise-LiftCtx : ∀ {ns ns′ n μ ns₁ ns′₁ n₁ μ₁ μ′ μ₁′} {ηᴸ : ns ↪ n}
    {ηᴿ : ns′ ↪ n} {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′₁ ↪ n₁}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ₁ ηᴿ₁}
    (L : Lift μ μ′) (L₁ : Lift μ₁ μ₁′)
  → LiftCtx γ γ′ → LiftCtx (raiseE L γ) (raiseE L₁ γ′)
raise-LiftCtx L L₁ lift-[]     = lift-[]
raise-LiftCtx L L₁ (lift-∷ lc) = lift-∷ (raise-LiftCtx L L₁ lc)

raise-LiftCtxᴸ : ∀ {ns ns′ n μ ns₁ n₁ μ₁ μ′ μ₁′} {ηᴸ : ns ↪ n}
    {ηᴿ : ns′ ↪ n} {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′ ↪ n₁}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ₁ ηᴿ₁}
    (L : Lift μ μ′) (L₁ : Lift μ₁ μ₁′)
  → LiftCtxᴸ γ γ′ → LiftCtxᴸ (raiseE L γ) (raiseE L₁ γ′)
raise-LiftCtxᴸ L L₁ liftᴸ-[]     = liftᴸ-[]
raise-LiftCtxᴸ L L₁ (liftᴸ-∷ lc) = liftᴸ-∷ (raise-LiftCtxᴸ L L₁ lc)

-- the interior, conversion-interior and well-formedness of raised worlds
int-↑ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′} κ′
  → Interior W Θ Θ′ Wᵢ → Interior (W ↑ κ′) Θ Θ′ (Wᵢ ↑ κ′)
int-↑ κ′ I = record
  { int-left   = int-left I
  ; int-right  = int-right I
  ; same-ϱᵍ    = same-ϱᵍ I
  ; same-ϱˡ    = same-ϱˡ I
  ; same-κ     = refl
  ; join-cont  = join-cont I
  ; join-fresh = join-fresh I
  }

conv-↑ : ∀ {W : World Δ Δ′} {Wᶜ : World Δᶜ Δ′ᶜ} {Θ Θ′} κ′
  → ConversionInterior W Θ Θ′ Wᶜ
  → ConversionInterior (W ↑ κ′) Θ Θ′ (Wᶜ ↑ κ′)
conv-↑ κ′ ci = record
  { conv-left       = conv-left ci
  ; conv-right      = conv-right ci
  ; conv-same-ϱᵍ    = conv-same-ϱᵍ ci
  ; conv-same-ϱˡ    = conv-same-ϱˡ ci
  ; conv-same-κ     = refl
  ; conv-join-cont  = conv-join-cont ci
  ; conv-join-fresh = conv-join-fresh ci
  }

rep-↑ : ∀ {W : World Δ Δ′} {κ′ μ R R′}
  → μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ R ⊑ᴿ⟨ W ↑ κ′ ⟩ R′
rep-↑ ★⊑★          = ★⊑★
rep-↑ (ι⊑ι b)      = ι⊑ι b
rep-↑ (X⊑X h)      = X⊑X h
rep-↑ (α⊑β pr)     = α⊑β pr
rep-↑ (⇒⊑⇒ a b)    = ⇒⊑⇒ (rep-↑ a) (rep-↑ b)
rep-↑ (∀⊑∀ a)      = ∀⊑∀ (rep-↑ a)
rep-↑ (⇒⊑★ a b)    = ⇒⊑★ (rep-↑ a) (rep-↑ b)
rep-↑ (ι⊑★ b)      = ι⊑★ b
rep-↑ (X⊑★ h)      = X⊑★ h
rep-↑ α⊑★          = α⊑★
rep-↑ (∀⊑ nv i a)  = ∀⊑ nv i (rep-↑ a)
rep-↑ ∀★⊑★         = ∀★⊑★
rep-↑ (∀⊑★ ns a)   = ∀⊑★ ns (rep-↑ a)
rep-↑ bot-elim     = bot-elim
rep-↑ bot⊑★        = bot⊑★

agree-↑ : ∀ {W : World Δ Δ′} {κ′ α β} → Agree W α β → Agree (W ↑ κ′) α β
agree-↑ (abst-abst a b) = abst-abst a b
agree-↑ (abst-★ a b)    = abst-★ a b
agree-↑ (rep-rep l r i) = rep-rep l r (rep-↑ i)

wf-↑ : ∀ {W : World Δ Δ′} {κ′} → WfWorld W → All (reps Δ′ ∋ʳ_) κ′
  → WfWorld (W ↑ κ′)
wf-↑ wf ps = record
  { wf-joint    = wf-joint wf
  ; wf-agree    = λ pr → agree-↑ (wf-agree wf pr)
  ; wf-namedᴸ   = wf-namedᴸ wf
  ; wf-namedᴿ   = wf-namedᴿ wf
  ; wf-pending  = wf-pending wf
  ; wf-distinct = wf-distinct wf
  ; wf-permits  = ps
  }

reps-int : ∀ {Γ Θ Γᵢ} → Γ ⊢ⁱ Θ ⇒ Γᵢ → reps Γᵢ ≡ reps Γ
reps-int (interior _) = refl

all-suc : ∀ {b Ξ κ} → All (Ξ ∋ʳ_) κ → All ((b ∷ Ξ) ∋ʳ_) (map suc κ)
all-suc []             = []
all-suc ((b , h) ∷ ps) = (b , there h) ∷ all-suc ps

-- R2 at the raised permissions, along a conversion-imprecision proof
mutual
  R2M : ∀ {W : World Δ Δ′} {g g′} → List RVar → MidImp W g g′ → Set
  R2M κ′ (conv-id⊑id _)  = ⊤
  R2M κ′ (conv-↦⊑↦ s c)  = R2C κ′ s × R2C κ′ c
  R2M κ′ (conv-∀⊑∀ c)    = R2C (map suc κ′) c
  R2M κ′ (conv-∀⊑ c)     = R2C κ′ c

  R2T : ∀ {W : World Δ Δ′} {t t′} → List RVar → TailImp W t t′ → Set
  R2T κ′ (conv-mid⊑mid g)          = R2M κ′ g
  R2T κ′ (conv-seal⊑seal _)        = ⊤
  R2T κ′ (conv-⨾seal⊑⨾seal t _)    = R2T κ′ t
  R2T {W = W} κ′ (conv-seal⊑id★ {X = X} _ _) = LeftUnpermitted (W ↑ κ′) X
  R2T {W = W} κ′ (conv-⨾seal⊑ {X = X} t _ _) =
    R2T κ′ t × LeftUnpermitted (W ↑ κ′) X

  R2C : ∀ {W : World Δ Δ′} {c c′} → List RVar → ConvImp W c c′ → Set
  R2C κ′ (conv-tail⊑tail t)           = R2T κ′ t
  R2C κ′ (conv-unseal⊑unseal _)       = ⊤
  R2C κ′ (conv-unseal⨾⊑unseal⨾ _ c)   = R2C κ′ c
  R2C {W = W} κ′ (conv-unseal⊑id★ {X = X} _ _) = LeftUnpermitted (W ↑ κ′) X
  R2C {W = W} κ′ (conv-unseal⨾⊑ {X = X} _ _ c) =
    LeftUnpermitted (W ↑ κ′) X × R2C κ′ c

mutual
  mid-↑ : ∀ {W : World Δ Δ′} {κ′ g g′} → Up (κʷ W) κ′
    → (m : MidImp W g g′) → R2M κ′ m → MidImp (W ↑ κ′) g g′
  mid-↑ {W = W} up (conv-id⊑id p) _ =
    conv-id⊑id (raise (dmarks-lift up (ηᴿʷ W)) p)
  mid-↑ up (conv-↦⊑↦ s c) (rs , rc) =
    conv-↦⊑↦ (conv-imp-↑ up s rs) (conv-imp-↑ up c rc)
  mid-↑ up (conv-∀⊑∀ c) r = conv-∀⊑∀ (conv-imp-↑ (up-suc up) c r)
  mid-↑ up (conv-∀⊑ c) r  = conv-∀⊑ (conv-imp-↑ up c r)

  tail-↑ : ∀ {W : World Δ Δ′} {κ′ t t′} → Up (κʷ W) κ′
    → (m : TailImp W t t′) → R2T κ′ m → TailImp (W ↑ κ′) t t′
  tail-↑ up (conv-mid⊑mid g) r = conv-mid⊑mid (mid-↑ up g r)
  tail-↑ up (conv-seal⊑seal j) _ = conv-seal⊑seal j
  tail-↑ up (conv-⨾seal⊑⨾seal t j) r = conv-⨾seal⊑⨾seal (tail-↑ up t r) j
  tail-↑ {W = W} up (conv-seal⊑id★ h _) r =
    conv-seal⊑id★ (dmarks-lift up (ηᴿʷ W) h) r
  tail-↑ {W = W} up (conv-⨾seal⊑ t h _) (rt , r) =
    conv-⨾seal⊑ (tail-↑ up t rt) (dmarks-lift up (ηᴿʷ W) h) r

  conv-imp-↑ : ∀ {W : World Δ Δ′} {κ′ c c′} → Up (κʷ W) κ′
    → (m : ConvImp W c c′) → R2C κ′ m → ConvImp (W ↑ κ′) c c′
  conv-imp-↑ up (conv-tail⊑tail t) r = conv-tail⊑tail (tail-↑ up t r)
  conv-imp-↑ up (conv-unseal⊑unseal j) _ = conv-unseal⊑unseal j
  conv-imp-↑ up (conv-unseal⨾⊑unseal⨾ j c) r =
    conv-unseal⨾⊑unseal⨾ j (conv-imp-↑ up c r)
  conv-imp-↑ {W = W} up (conv-unseal⊑id★ h _) r =
    conv-unseal⊑id★ (dmarks-lift up (ηᴿʷ W) h) r
  conv-imp-↑ {W = W} up (conv-unseal⨾⊑ h _ c) (r , rc) =
    conv-unseal⨾⊑ (dmarks-lift up (ηᴿʷ W) h) r (conv-imp-↑ up c rc)

-- THE SIDE CONDITION: R1/R2 at the raised permissions, at every payload
-- view and every ★ clause; at a grant of β, β is a store rep. var
R12 : ∀ {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → List RVar → W ∣ γ ⊢ M ⊑ M′ ∶ p → Set
R12 κ′ (x⊑x _)                 = ⊤
R12 κ′ (κ⊑κ _ _)               = ⊤
R12 κ′ (ƛ⊑ƛ _ _ d)             = R12 κ′ d
R12 κ′ (·⊑· d e)               = R12 κ′ d × R12 κ′ e
R12 κ′ (blame⊑ _ _ _)          = ⊤
R12 κ′ (cast⊑cast d _ _ _)     = R12 κ′ d
R12 κ′ (cast⊑ _ d _ _)         = R12 κ′ d
R12 κ′ (⊑cast no-grant _ d _ _) = R12 κ′ d
R12 {Δ′ = Δ′} κ′ (⊑cast (grant {β = β} _) _ d _ _) =
  (reps Δ′ ∋ʳ β) × R12 (β ∷ κ′) d
R12 κ′ (Λ⊑Λ _ _ _ d _)         = R12 (map suc κ′) d
R12 κ′ (Λ⊑ _ _ _ _ _ d _)      = R12 κ′ d
R12 κ′ (ν⊑ν d _ (nu-ty _ _ _ _ _ _) (nu-ty _ _ _ _ _ _) (_ , _ , cv) _) =
  R12 κ′ d × R2C (map suc κ′) cv
R12 κ′ (ν⊑ d _ _ _)            = R12 κ′ d
R12 κ′ (⟪⟫⊑⟪⟫ _ _ d (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _) (_ , _ , cv) _) =
  R12 κ′ d × R2C κ′ cv
R12 {W = W} κ′ (⟪⟫⊑ {Θ = Θ} _ _ _ _ d _ _) =
  All (UnbindOK (W ↑ κ′)) Θ × R12 κ′ d
R12 κ′ (⊑⟪⟫ _ _ _ d _ _)       = R12 κ′ d

-- THE WEAKENING LEMMA
κ-weaken : ∀ {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′} {κ′}
  → (up : Up (κʷ W) κ′) → All (reps Δ′ ∋ʳ_) κ′
  → (d : W ∣ γ ⊢ M ⊑ M′ ∶ p) → R12 κ′ d
  → W ↑ κ′ ∣ raiseγ {W = W} up γ ⊢ M ⊑ M′ ∶ raiseI {W = W} up p
κ-weaken up ps (x⊑x h) _ = x⊑x (raise-∋ h)
κ-weaken up ps (κ⊑κ l p) _ = κ⊑κ l _
κ-weaken up ps (ƛ⊑ƛ a a′ d) r = ƛ⊑ƛ a a′ (κ-weaken up ps d r)
κ-weaken up ps (·⊑· d e) (rd , re) = ·⊑· (κ-weaken up ps d rd) (κ-weaken up ps e re)
κ-weaken {W = W} {γ = γ} up ps (blame⊑ a t p) _ =
  blame⊑ a (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
                  (sym (raise-rhs (dmarks-lift up (ηᴿʷ W)) γ)) t) _
κ-weaken up ps (cast⊑cast d ct ct′ q) r =
  cast⊑cast (κ-weaken up ps d r) ct ct′ _
κ-weaken up ps (cast⊑ cc d ct q) r = cast⊑ cc (κ-weaken up ps d r) ct _
κ-weaken {W = W} up ps (⊑cast no-grant rc d ct q) r =
  ⊑cast no-grant
    (raise-RaiseCtx (dmarks-lift up (ηᴿʷ W)) (dmarks-lift up (ηᴿʷ W)) rc)
    (κ-weaken up ps d r) ct _
κ-weaken {W = W} up ps (⊑cast (grant {β = β} g) rc d ct q) (pβ , r) =
  ⊑cast (grant g)
    (raise-RaiseCtx (dmarks-lift up (ηᴿʷ W))
                    (dmarks-lift (up-∷ β up) (ηᴿʷ W)) rc)
    (κ-weaken (up-∷ β up) (pβ ∷ ps) d r) ct _
κ-weaken {W = W} up ps (Λ⊑Λ lc v v′ d q) r =
  Λ⊑Λ (raise-LiftCtx (dmarks-lift up (ηᴿʷ W))
                     (dmarks-lift (up-suc up) (ηᴿʷ (W ⊕²))) lc)
      v v′ (κ-weaken (up-suc up) (all-suc ps) d r) _
κ-weaken {W = W} up ps (Λ⊑ claim-fresh nv i lc v d q) r =
  Λ⊑ claim-fresh nv i
    (raise-LiftCtxᴸ (dmarks-lift up (ηᴿʷ W))
                    (dmarks-lift up (ηᴿʷ (W ⊕ᴸ))) lc)
    v (κ-weaken up ps d r) _
κ-weaken {W = W} up ps (Λ⊑ {W₁ = W₁} (claim-pop (open1 j h hr)) nv i lc v d q) r =
  Λ⊑ (claim-pop (open1 j h hr)) nv i
    (raise-LiftCtxᴸ (dmarks-lift up (ηᴿʷ W))
                    (dmarks-lift up (ηᴿʷ W₁)) lc)
    v (κ-weaken up ps d r) _
κ-weaken {W = W} up ps (ν⊑ν d a n@(nu-ty _ _ _ _ _ _) n′@(nu-ty _ _ _ _ _ _)
               (Wᶜ , ci , cv) q) (rd , rc) =
  ν⊑ν (κ-weaken up ps d rd) (raiseI {W = W} up a) n n′
    (Wᶜ ↑ _ , conv-↑ _ ci
            , conv-imp-↑ (up-≡ (conv-same-κ ci) (up-suc up)) cv rc)
    _
κ-weaken {W = W} up ps (ν⊑ d a n q) r =
  ν⊑ (κ-weaken up ps d r) (raiseI {W = W} up a) n _
κ-weaken {κ′ = κ′} up ps
  (⟪⟫⊑⟪⟫ I wf d b@(bdy-ty _ _ _ _ _) b′@(bdy-ty _ _ _ _ _) (Wᶜ , ci , cv) q)
  (rd , rc) =
  ⟪⟫⊑⟪⟫ (int-↑ κ′ I)
    (wf-↑ wf (subst (λ Ξ → All (Ξ ∋ʳ_) κ′) (sym (reps-int (int-right I))) ps))
    (κ-weaken (up-≡ (same-κ I) up)
      (subst (λ Ξ → All (Ξ ∋ʳ_) κ′) (sym (reps-int (int-right I))) ps) d rd)
    b b′
    (Wᶜ ↑ κ′ , conv-↑ κ′ ci , conv-imp-↑ (up-≡ (conv-same-κ ci) up) cv rc)
    _
κ-weaken {κ′ = κ′} up ps (⟪⟫⊑ I _ bc wf d b q) (r1 , rd) =
  ⟪⟫⊑ (int-↑ κ′ I) r1 bc (wf-↑ wf ps)
    (κ-weaken (up-≡ (same-κ I) up) ps d rd) b _
κ-weaken {κ′ = κ′} up ps (⊑⟪⟫ I pu wf d b q) r =
  ⊑⟪⟫ (int-↑ κ′ I) pu
    (wf-↑ wf (subst (λ Ξ → All (Ξ ∋ʳ_) κ′) (sym (reps-int (int-right I))) ps))
    (κ-weaken (up-≡ (same-κ I) up)
      (subst (λ Ξ → All (Ξ ∋ʳ_) κ′) (sym (reps-int (int-right I))) ps) d r)
    b _

-- CASTFUN, the grant case: before the step the right's arrow cast
-- `p′ ↦ q′` grants β (first-order p′, granting q′) to the function only;
-- after `(V′⟨p′ ↦ q′⟩) W′ ⟶ (V′ (W′⟨p′⟩))⟨q′⟩` the argument sits under
-- the grant of q′.  The function's derivation is reused at β ∷ κ; the
-- argument's is RAISED by `κ-weaken`, which needs R12 (β ∷ κ) of it.
up-cons : ∀ β κ → Up κ (β ∷ κ)
up-cons β κ = mk-up go
  where
  go : ∀ γ → permit γ κ ≡ X⊑★ → permit γ (β ∷ κ) ≡ X⊑★
  go γ h with γ ≡ᵇ β
  ... | true  = refl
  ... | false = h

length-map : ∀ {A B : Set} (f : A → B) (xs : List A)
  → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

castfun-grant : ∀ {n ηᴸ ηᴿ ϱᵍ ϱˡ κ}
  → let W = world {Δ} {Δ′} n ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
    ∀ {β L N V′ W′ μ′ p′ q′ A B A₀′ B₀′ A₁′ B₁′}
      {pA₀ : A ⊑ᵂ⟨ W ↑ (β ∷ κ) ⟩ A₀′} {pB₀ : B ⊑ᵂ⟨ W ↑ (β ∷ κ) ⟩ B₀′}
      {pA : A ⊑ᵂ⟨ W ⟩ A₁′} {pB : B ⊑ᵂ⟨ W ⟩ B₁′}
  → FirstOrder p′ → Grants Δ′ β q′
  → W ↑ (β ∷ κ) ∣ [] ⊢ L ⊑ V′ ∶ ⇒⊑⇒ pA₀ pB₀
  → CastTy Δ′ μ′ (p′ ↦ᵖ q′) (A₀′ ⇒ B₀′) (A₁′ ⇒ B₁′)
  → (dN : W ∣ [] ⊢ N ⊑ W′ ∶ pA)
  → All (reps Δ′ ∋ʳ_) (β ∷ κ)
  → R12 (β ∷ κ) dN
    -- the pair before the step ...
  → (W ∣ [] ⊢ L · N ⊑ (V′ ⟨ μ′ ∣ p′ ↦ᵖ q′ ⟩) · W′ ∶ pB)
    -- ... and after it
    × (W ∣ [] ⊢ L · N ⊑ (V′ · (W′ ⟨ flipEnv μ′ ∣ p′ ⟩)) ⟨ μ′ ∣ q′ ⟩ ∶ pB)
castfun-grant {κ = κ} {β = β} {μ′ = μ′} {pA₀ = pA₀} {pA = pA} {pB = pB}
  fo gq dV ct@(cast-ty (⊢fun dp dq) len) dN ps r =
  ·⊑· (⊑cast (grant (gr-↦ fo gq)) raise-[] dV ct (⇒⊑⇒ pA pB)) dN ,
  ⊑cast (grant gq) raise-[]
    (·⊑· dV
      (⊑cast₀ (κ-weaken (up-cons β κ) ps dN r)
        (cast-ty dp (trans (length-map flipᵐ μ′) len)) pA₀))
    (cast-ty dq len) pB

------------------------------------------------------------------------
-- 22. The TagUntag DROP lemma: the pieces that hold in general.  The
-- step `V′⟨X!⟩⟨X?⟩ ⟶ V′` removes the check that granted β.  An X-typed
-- right value V′ is related under β ∷ κ; we need it under κ.
--   (a) R1/R2 only get easier when a permission is dropped
--       (`unpermitted-drop`);
--   (b) an index whose right type is a name reads no mark
--       (`var-right`), so the indices ABOVE V′'s hide `[−X^β]` survive;
--   (c) where no right name is bound to β, the marks do not see β at
--       all (`dmarks-drop`), so BELOW the hide (where the unbind made β
--       nameless, `step-unbind`'s freshness) every index is unchanged
--       until a right rebinding of β.
-- What is missing for the general lemma is the walk that puts V′'s
-- hide above every left rule that reads β's permission (Permissions.md
-- §6(b), PermissionsR.md §4.3).  On P4's run the drop holds
-- (`P4c.p4-R10`: S ⊑ [−X,+X,−X] 5 ⟨−X⟩ at κ = []).
------------------------------------------------------------------------

permit-other : ∀ {γ β} κ → γ ≢ β → permit γ (β ∷ κ) ≡ permit γ κ
permit-other {γ} {β} κ n with γ ≡ᵇ β in eq
... | true  = ⊥-elim (n (T-≡ᵇ γ β eq))
... | false = refl

unpermitted-drop : ∀ {W : World Δ Δ′} {β α}
  → Unpermitted (W ↑ (β ∷ κʷ W)) α → Unpermitted W α
unpermitted-drop {W = W} {β} u {γ} pr with γ ≡ᵇ β | u pr
... | true  | ()
... | false | e = e

var-right : ∀ {μ μ′ A b} → μ ⊢ A ⊑ ` b → μ′ ⊢ A ⊑ ` b
var-right X⊑X          = X⊑X
var-right (∀⊑ nv i a)  = ∀⊑ nv i (var-right a)

var-rightO : ∀ {μ μ′} cs {ρ A b}
  → OpenImp μ cs ρ A (` b) → OpenImp μ′ cs ρ A (` b)
var-rightO []       p = var-right p
var-rightO (c ∷ cs) {A = `∀ A}  p = var-rightO cs p
var-rightO (c ∷ cs) {A = ` X}   ()
var-rightO (c ∷ cs) {A = `ℕ}    ()
var-rightO (c ∷ cs) {A = `𝔹}    ()
var-rightO (c ∷ cs) {A = ★}     ()
var-rightO (c ∷ cs) {A = A ⇒ B} ()

-- (b) at the raised/dropped world: the same index
idx-name-free : ∀ {W : World Δ Δ′} {κ′ A X′}
  → A ⊑ᵂ⟨ W ⟩ ` X′ → A ⊑ᵂ⟨ W ↑ κ′ ⟩ ` X′
idx-name-free {W = W} {X′ = X′} p =
  var-rightO (map (emb (ηᴿʷ W)) (πʷ W)) p

-- (c)
dmarks-drop : ∀ {ns n β} κ (ι : ns ↪ n) → (∀ {X} → ¬ (ns ∋ˡ X := β))
  → dmarks ι (β ∷ κ) ≡ dmarks ι κ
dmarks-drop κ []↪ nn = refl
dmarks-drop {β = β} κ (keep {α = γ} ι) nn =
  cong₂′ (permit-other κ (λ e → nn (subst (λ b → (γ ∷ _) ∋ˡ 0 := b) e here)))
         (dmarks-drop κ ι (λ h → nn (there h)))
  where
  cong₂′ : ∀ {a b : VarImp} {xs ys : ImpEnv} → a ≡ b → xs ≡ ys
    → (a ∷ xs) ≡ (b ∷ ys)
  cong₂′ refl refl = refl
dmarks-drop κ (skip ι) nn = cong (X⊑★ ∷_) (dmarks-drop κ ι nn)

module proof.DGG.notes.PushOrder where

-- File Charter:
--   * D27's PUSH-ORDER DEFECT H1 MADE CONCRETE (PushOrder.md).  A left
--     ∀X.∀Y-value against a right that instantiates it TWICE by two
--     casts, `∀X.∀Y.X→Y→X ⇒ ∀Y.★→Y→★ ⇒ ★→★→★`.  The right's FINAL
--     value is the nested `[+Y^β](([+X^α] N ⟨…⟩)⟨…⟩)⟨…⟩` (a cast sits
--     between the boundaries, so no Merge), and D27 relates it to the
--     left value in NO world: a counterexample to the DGG's part 1.
--   * §0 a snapshot of git 888407ff (ImprecisionWorld, ConversionImp-
--     recision, TermImprecision's side relations), because the real
--     files are being edited for D28; §1 HEAD's relation with `Claim`
--     and `Push` as parameters (`Rel`); §2 the fixes as instances:
--     (a) `PushA` new-first, (c1) `PushS` any interleaving, (b)
--     `ClaimAny` pop any pending name, (c2) `ClaimRep` claim a rep.
--     var; §3 the example from its sources, runs pinned to `evalTerms`;
--     §4 the initial pair and state 2, related in all instances; §5
--     the final pair, related in (c2); §6 the final pair, NOT related
--     in HEAD, (a), (b), (c1) (`NoRel`, generic in the push relation);
--     §7 (c2) alone revives C4 at HEAD's marks; §8 carry-over of
--     derivations between instances.
--   * Not a Def module, not imported by All.agda.  No holes, no
--     postulates.  LEFT is the more precise side.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List
  using (List; []; _∷_; map; _++_; head; drop; length; last)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision

------------------------------------------------------------------------
-- 0. Snapshot of git 888407ff: ImprecisionWorld (IW),
--    ConversionImprecision (CI), TermImprecision §1-§2 side relations
--    (TI), verbatim (charters dropped).  The real files are being
--    edited for D28; this note does not depend on them.
------------------------------------------------------------------------

module IW where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.List using (List; []; _∷_; map; length)
  open import Data.Nat using (_+_)
  open import Data.Maybe using (just)
  open import Data.Product using (Σ-syntax; _×_; _,_)
  open import Data.Sum using (_⊎_)
  open import Data.Empty using (⊥)
  open import Data.List.Relation.Unary.All using (All; [])
  open import Data.List.Relation.Unary.AllPairs using (AllPairs; [])
  open import Relation.Nullary using (¬_)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

  open import Types
    using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Base; Renameᵗ; renameᵗ; ⇑ᵗ)
  open import Ctx
  open import Boundary using (Boundary; _⊢ⁱ_⇒_; _⊢ᶜ_⇒_; toExt; Fresh)
  open import Imprecision
    using (VarImp; X⊑X; X⊑★; ImpEnv; extᵐ; instᵐ; _⊢_⊑_)
  open import Coercion using (NonVar; NonStar; _∈ᵗ_)

  private
    variable
      Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

  ------------------------------------------------------------------------
  -- 1. Embeddings of name positions into the center
  ------------------------------------------------------------------------

  -- `η : names Δ ↪ Ω`: an order-preserving embedding of Δ's name
  -- positions into the center Ω (GTSFImp `_↪ᵗ_`).  `keep` sends the
  -- next name to the next center name; `skip` passes a center name this
  -- side does not see.
  infix 4 _↪_
  data _↪_ : TyCtx → ImpEnv → Set where
    []↪  : [] ↪ []
    keep : ∀ {α m Δ Ω} → Δ ↪ Ω → (α ∷ Δ) ↪ (m ∷ Ω)
    skip : ∀ {m Δ Ω} → Δ ↪ Ω → Δ ↪ (m ∷ Ω)

  -- its renaming (GTSFImp `toRenameᵗ`)
  emb : ∀ {η Ω} → η ↪ Ω → Renameᵗ
  emb []↪      X       = X
  emb (keep ι) zero    = zero
  emb (keep ι) (suc X) = suc (emb ι X)
  emb (skip ι) X       = suc (emb ι X)

  -- a renumbering of the rep. vars the names denote moves no position
  relabel : ∀ {η Ω} (f : RVar → RVar) → η ↪ Ω → map f η ↪ Ω
  relabel f []↪      = []↪
  relabel f (keep ι) = keep (relabel f ι)
  relabel f (skip ι) = skip (relabel f ι)

  ------------------------------------------------------------------------
  -- 2. The rep. var correspondence
  ------------------------------------------------------------------------

  -- pairs (left rep. var, right rep. var)
  RepRel : Set
  RepRel = List (RVar × RVar)

  infix 4 _∋ᵨ_⇔_
  data _∋ᵨ_⇔_ : RepRel → RVar → RVar → Set where
    here⇔  : ∀ {ϱ α β} → ((α , β) ∷ ϱ) ∋ᵨ α ⇔ β
    there⇔ : ∀ {ϱ α β π} → ϱ ∋ᵨ α ⇔ β → (π ∷ ϱ) ∋ᵨ α ⇔ β

  sucᴸ sucᴿ suc² : RVar × RVar → RVar × RVar
  sucᴸ (α , β) = suc α , β
  sucᴿ (α , β) = α , suc β
  suc² (α , β) = suc α , suc β

  -- one new rep. var on the left, on the right, on both sides
  shiftᴸ shiftᴿ shift² : RepRel → RepRel
  shiftᴸ = map sucᴸ
  shiftᴿ = map sucᴿ
  shift² = map suc²

  ------------------------------------------------------------------------
  -- 3. Worlds
  ------------------------------------------------------------------------

  record World (Δ Δ′ : Ctxᵗ) : Set where
    constructor world
    field
      μʷ  : ImpEnv                -- the center Ω, each name with its mark
      ηᴸʷ : names Δ ↪ μʷ          -- the left names
      ηᴿʷ : names Δ′ ↪ μʷ         -- the right names
      ϱᵍʷ : RepRel                -- global: store rep. vars (D16)
      ϱˡʷ : RepRel                -- lexical: Λ- and boundary-bound (D16)
      πʷ  : List ℕ                -- pending right names, next pop first (D27)
  open World public

  -- ϱ = ϱᵍ ∪ ϱˡ
  Paired : World Δ Δ′ → RVar → RVar → Set
  Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

  -- a left and a right position name the same center name
  Joins : World Δ Δ′ → ℕ → ℕ → Set
  Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

  -- the closed world: no names, no rep. vars paired
  ∅ʷ : World empty empty
  ∅ʷ = world [] []↪ []↪ [] [] []

  ------------------------------------------------------------------------
  -- 4. Type imprecision at a world (GTSFImp `_⊑ᵂ⟨_⟩_`)
  ------------------------------------------------------------------------

  embᴸ : World Δ Δ′ → Ty → Ty
  embᴸ W = renameᵗ (emb (ηᴸʷ W))

  embᴿ : World Δ Δ′ → Ty → Ty
  embᴿ W = renameᵗ (emb (ηᴿʷ W))

  -- one opened binder in front of a renaming: the bound variable 0 goes
  -- to the center name c
  infixr 5 _⊳_
  _⊳_ : ℕ → Renameᵗ → Renameᵗ
  (c ⊳ ρ) zero    = c
  (c ⊳ ρ) (suc X) = ρ X

  -- `OpenImp μ cs ρ A B`: A with its outer binders opened at the center
  -- names cs (outermost first), renamed by ρ, is below B.  A non-∀ type
  -- under a pending name has no index.
  OpenImp : ImpEnv → List ℕ → Renameᵗ → Ty → Ty → Set
  OpenImp μ []       ρ A        B = μ ⊢ renameᵗ ρ A ⊑ B
  OpenImp μ (c ∷ cs) ρ (`∀ A)   B = OpenImp μ cs (c ⊳ ρ) A B
  OpenImp μ (c ∷ cs) ρ (` X)    B = ⊥
  OpenImp μ (c ∷ cs) ρ `ℕ       B = ⊥
  OpenImp μ (c ∷ cs) ρ `𝔹       B = ⊥
  OpenImp μ (c ∷ cs) ρ ★        B = ⊥
  OpenImp μ (c ∷ cs) ρ (A ⇒ A′) B = ⊥

  -- THE INDEX of the term relation: the actual left type, opened at the
  -- center names of the pending names (design.md D27).  With no pending
  -- name (`πʷ W = []`) it is `μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′`
  -- (definitionally).
  infix 4 _⊑ᵂ⟨_⟩_
  _⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
  A ⊑ᵂ⟨ W ⟩ A′ =
    OpenImp (μʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

  ------------------------------------------------------------------------
  -- 5. World operations (design.md §12.2)
  ------------------------------------------------------------------------

  -- A new right name 0 moves every pending name one position up; a new
  -- left name, or an allocation, moves none.

  -- W ⊕ X:m — both sides bind X by a Λ: a new center name in both
  -- images with mark m, and the two abstract rep. vars paired lexically
  infixl 6 _⊕_ _⊕ᴿ_
  _⊕_ : World Δ Δ′ → VarImp → World (underΛ Δ) (underΛ Δ′)
  world μ η η′ ϱᵍ ϱˡ π ⊕ m =
    world (m ∷ μ) (keep (relabel suc η)) (keep (relabel suc η′))
          (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc π)

  -- W ⊕ᴸ X — the left side alone binds X: in η's image only, at X⊑★;
  -- its abstract rep. var is unpaired
  infixl 6 _⊕ᴸ
  _⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
  world μ η η′ ϱᵍ ϱˡ π ⊕ᴸ =
    world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip η′)
          (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) π

  -- W ⊕ᴿ X — the right side alone binds X: in η′'s image only (used by
  -- no rule of §12.3; recorded for completeness)
  _⊕ᴿ_ : World Δ Δ′ → VarImp → World Δ (underΛ Δ′)
  world μ η η′ ϱᵍ ϱˡ π ⊕ᴿ m =
    world (m ∷ μ) (skip η) (keep (relabel suc η′))
          (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) (map suc π)

  -- the premise world of the pop of the pending name of `bind 0 β`
  -- (`open-⊕`, design.md D27; before D26, of `∀⊑⟪+⟫`): the left goes
  -- under its binder, a Λ-like binder (an abstract rep. var at 0), the
  -- right is inside its boundary `bind 0 β`; one new center name with mark m, and the left
  -- abstract rep. var is paired lexically with β (design.md §12.2, D16)
  infixl 6 _⊕⁺_^_
  _⊕⁺_^_ : World Δ Δ′ → VarImp → (β : RVar)
    → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
  world μ η η′ ϱᵍ ϱˡ π ⊕⁺ m ^ β =
    world (m ∷ μ) (keep (relabel suc η)) (keep η′)
          (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) (map suc π)

  -- the interior world of `⊑⟪⟫` at a single right entry `bind 0 β`
  -- (`+X^β`): X is a right-only name with mark m (FixB's `_⊕ʳ_^_`)
  infixl 6 _⊕ʳ_^_
  _⊕ʳ_^_ : World Δ Δ′ → VarImp → (β : RVar)
    → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
  world μ η η′ ϱᵍ ϱˡ π ⊕ʳ m ^ β =
    world (m ∷ μ) (skip η) (keep η′) ϱᵍ ϱˡ (map suc π)

  -- POPS (design.md D27; D26's openings).  A left binder (`Λ⊑`, or the
  -- gen layer of `cast⊑`) may join the pending right-only name k that a
  -- `⊑⟪⟫` pushed: the binder (a Λ-like abstract rep. var at 0, as
  -- `underΛ`) joins k's center name.  `Join↪ ι ι′ ι⁺ k`: the left's NEW
  -- name 0 is kept into the center name of the right's name k, which is
  -- RIGHT-ONLY; the center names before it are right-only too (the left
  -- skips them), so the left's order is preserved.  `ι⁺` is the left embedding after the
  -- pop (FixB's `JoinΛ`, at any position k).
  data Join↪ {η : TyCtx}
      : ∀ {η′ μ} → η ↪ μ → η′ ↪ μ → (zero ∷ map suc η) ↪ μ → ℕ → Set where
    join-here : ∀ {β η′ μ m} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
      → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
    join-there : ∀ {β η′ μ m k} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
        {ι⁺ : (zero ∷ map suc η) ↪ μ}
      → Join↪ ι ι′ ι⁺ k
      → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

  -- The pop of the head pending name k, whose rep. var β is bound to ★;
  -- the left abstract rep. var is paired with β LEXICALLY (D16).
  -- `W ⊕⁺ m ^ β` is the pop of name 0 of `W ⊕ʳ m ^ β` with 0 pushed
  -- (`open-⊕`).
  data Open1 {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
    open1 : ∀ {μ ϱᵍ ϱˡ k π β} {ι : names Δ ↪ μ} {ι′ : names Δ′ ↪ μ}
        {ι⁺ : names (underΛ Δ) ↪ μ}
      → Join↪ ι ι′ ι⁺ k
      → Δ′ ∋ᵗ k := β
      → Δ′ ∋rep β := ★
      → Open1 (world μ ι ι′ ϱᵍ ϱˡ (k ∷ π))
              (world μ ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) π)

  open-⊕ : ∀ {W : World Δ Δ′} {m β}
    → Δ′ ∋rep β := ★
    → Open1 (record (W ⊕ʳ m ^ β) { πʷ = 0 ∷ map suc (πʷ W) }) (W ⊕⁺ m ^ β)
  open-⊕ hβ = open1 join-here here hβ

  -- Renumbering on allocation (for the metatheory; no rule of §12.3
  -- reads a world under an allocation).  An unmatched allocation only
  -- renumbers its own side; a matched pair of TyBetas adds (0, 0) to
  -- ϱᵍ; a left TyBeta catching up with a right boundary `bind 0 β`
  -- whose name a left binder popped adds (0, β) (design.md §12.2, D16,
  -- D27).
  allocᴸ : (R : Ty) → World Δ Δ′ → World (allocate R Δ) Δ′
  allocᴸ R (world μ η η′ ϱᵍ ϱˡ π) =
    world μ (relabel suc η) η′ (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) π

  allocᴿ : (R′ : Ty) → World Δ Δ′ → World Δ (allocate R′ Δ′)
  allocᴿ R′ (world μ η η′ ϱᵍ ϱˡ π) =
    world μ η (relabel suc η′) (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) π

  alloc² : (R R′ : Ty) → World Δ Δ′
    → World (allocate R Δ) (allocate R′ Δ′)
  alloc² R R′ (world μ η η′ ϱᵍ ϱˡ π) =
    world μ (relabel suc η) (relabel suc η′)
          ((zero , zero) ∷ shift² ϱᵍ) (shift² ϱˡ) π

  -- The two ν-bound rep. vars are in scope only while their conversions
  -- are compared.  Unlike `alloc²`, which records matched runtime
  -- allocations globally, this operation records (0, 0) lexically.
  underν² : (R R′ : Ty) → World Δ Δ′
    → World (allocate R Δ) (allocate R′ Δ′)
  underν² R R′ (world μ η η′ ϱᵍ ϱˡ π) =
    world μ (relabel suc η) (relabel suc η′)
          (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) π

  allocᴸ⇔ : (R : Ty) (β : RVar) → World Δ Δ′ → World (allocate R Δ) Δ′
  allocᴸ⇔ R β (world μ η η′ ϱᵍ ϱˡ π) =
    world μ (relabel suc η) η′ ((zero , β) ∷ shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) π

  ------------------------------------------------------------------------
  -- 6. The interior world W[δ ∥ δ′] (a relation; design.md §12.2)
  ------------------------------------------------------------------------

  -- `Interior W Θ Θ′ Wᵢ`: Wᵢ is an interior world of the boundary pair
  -- `[Θ] ⊑ [Θ′]` in W.  A one-sided boundary is the case Θ = [] or
  -- Θ′ = [] (W[δ ∥ ·], W[· ∥ δ′]); `toExt [] X = just X`, so every name
  -- of the side without a boundary continues.
  record Interior (W : World Δ Δ′) (Θ Θ′ : Boundary)
      (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
    constructor interior-world
    field
      -- each side's changes act on that side's names
      int-left  : Δ ⊢ⁱ Θ ⇒ Δᵢ
      int-right : Δ′ ⊢ⁱ Θ′ ⇒ Δ′ᵢ
      -- a boundary relates no new rep. vars
      same-ϱᵍ : ϱᵍʷ Wᵢ ≡ ϱᵍʷ W
      same-ϱˡ : ϱˡʷ Wᵢ ≡ ϱˡʷ W
      -- two continuing names share a center name inside iff outside
      join-cont : ∀ {X X′ Xₑ X′ₑ}
        → Δᵢ ∋tv X → Δ′ᵢ ∋tv X′
        → toExt Θ X ≡ just Xₑ → toExt Θ′ X′ ≡ just X′ₑ
        → (Joins Wᵢ X X′ → Joins W Xₑ X′ₑ)
          × (Joins W Xₑ X′ₑ → Joins Wᵢ X X′)
      -- a name the boundary introduces joins exactly the other side's
      -- name of a paired rep. var (D25: a right `+X^β` rejoins the left
      -- partner of β whose name is in scope; `wf-namedᴸ` of Wᵢ makes it
      -- unique); otherwise it is one-sided
      join-fresh : ∀ {X X′ α β}
        → Δᵢ ∋ᵗ X := α → Δ′ᵢ ∋ᵗ X′ := β
        → Fresh Θ X ⊎ Fresh Θ′ X′
        → (Joins Wᵢ X X′ → Paired W α β)
          × (Paired W α β → Joins Wᵢ X X′)
      -- a continuing name keeps its mark, also when it went one-sided
      -- and rejoined within the entries (D15)
      mark-left : ∀ {X Xₑ m}
        → Δᵢ ∋tv X → toExt Θ X ≡ just Xₑ
        → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
        → μʷ Wᵢ ∋ˡ emb (ηᴸʷ Wᵢ) X := m
      mark-right : ∀ {X′ X′ₑ m}
        → Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ
        → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
        → μʷ Wᵢ ∋ˡ emb (ηᴿʷ Wᵢ) X′ := m
  open Interior public

  -- `ConversionInterior W Θ Θ′ Wᶜ`: Wᶜ relates the two contexts in
  -- which the boundary conversions are read.  Those contexts keep every
  -- exterior name and add a name for each newly encountered rep. var;
  -- an unbind never removes a conversion-context name.  Consequently a
  -- name continues exactly when its rep. var already has an exterior
  -- name, and it is fresh exactly when that rep. var has none.
  record ConversionInterior (W : World Δ Δ′) (Θ Θ′ : Boundary)
      (Wᶜ : World Δᶜ Δ′ᶜ) : Set where
    constructor conversion-interior-world
    field
      conv-left  : Δ ⊢ᶜ Θ ⇒ Δᶜ
      conv-right : Δ′ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
      conv-same-ϱᵍ : ϱᵍʷ Wᶜ ≡ ϱᵍʷ W
      conv-same-ϱˡ : ϱˡʷ Wᶜ ≡ ϱˡʷ W
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
      conv-mark-left : ∀ {X Xₑ α m}
        → Δᶜ ∋ᵗ X := α → Δ ∋ᵗ Xₑ := α
        → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
        → μʷ Wᶜ ∋ˡ emb (ηᴸʷ Wᶜ) X := m
      conv-mark-right : ∀ {X′ X′ₑ β m}
        → Δ′ᶜ ∋ᵗ X′ := β → Δ′ ∋ᵗ X′ₑ := β
        → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
        → μʷ Wᶜ ∋ˡ emb (ηᴿʷ Wᶜ) X′ := m
  open ConversionInterior public

  ------------------------------------------------------------------------
  -- 7. Term-context imprecision (GTSFImp `CtxImp`)
  ------------------------------------------------------------------------

  -- An entry reads only the center and the two embeddings (not ϱ, not
  -- the pending names): a variable is typed at the plain index, and
  -- `CtxImp (record W { πʷ = π })` IS `CtxImp W`.  Hence the entry type
  -- is parameterized by those three fields, not by the world.
  record CtxImpEntry {ns ns′ : TyCtx} (μ : ImpEnv) (ηᴸ : ns ↪ μ)
      (ηᴿ : ns′ ↪ μ) : Set where
    constructor ctx-imp
    field
      tyᴸ  : Ty
      tyᴿ  : Ty
      impʷ : μ ⊢ renameᵗ (emb ηᴸ) tyᴸ ⊑ renameᵗ (emb ηᴿ) tyᴿ
  open CtxImpEntry public

  -- term-context imprecision at μ, ηᴸ, ηᴿ
  Entries : ∀ {ns ns′} (μ : ImpEnv) → ns ↪ μ → ns′ ↪ μ → Set
  Entries μ ηᴸ ηᴿ = List (CtxImpEntry μ ηᴸ ηᴿ)

  CtxImp : World Δ Δ′ → Set
  CtxImp W = Entries (μʷ W) (ηᴸʷ W) (ηᴿʷ W)

  -- the two term contexts (Terms.Ctx = List Ty)
  lhs : ∀ {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ} → Entries μ ηᴸ ηᴿ → List Ty
  lhs = map tyᴸ

  rhs : ∀ {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ} → Entries μ ηᴸ ηᴿ → List Ty
  rhs = map tyᴿ

  infix 4 _∋ʷ_⦂_
  data _∋ʷ_⦂_ {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ}
      : Entries μ ηᴸ ηᴿ → ℕ → CtxImpEntry μ ηᴸ ηᴿ → Set where
    Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
    Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

  -- `⇑γ` for `Λ⊑Λ`: both types shifted, the proof any at the new world
  -- (`CtxImp W → CtxImp (W ⊕ m)`)
  data LiftCtx {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ} (m : VarImp)
      : Entries μ ηᴸ ηᴿ
      → Entries (m ∷ μ) (keep {α = zero} (relabel suc ηᴸ))
                (keep {α = zero} (relabel suc ηᴿ))
      → Set where
    lift-[] : LiftCtx m [] []
    lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx m γ γ′
      → LiftCtx m (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

  -- `⇑ᴸγ` for `Λ⊑`: the right types cross unweakened.  The premise world
  -- is any world over `underΛ Δ` (`W ⊕ᴸ` for a fresh left-only binder, or
  -- the `Open1` of a pending name, design.md D27)
  data LiftCtxᴸ {ns ns′ ns₁ μ μ₁} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ}
      {ηᴸ₁ : ns₁ ↪ μ₁} {ηᴿ₁ : ns′ ↪ μ₁}
      : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
    liftᴸ-[] : LiftCtxᴸ [] []
    liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
      → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

  ------------------------------------------------------------------------
  -- 8. Well-formedness (design.md §12.2), a SEPARATE predicate
  ------------------------------------------------------------------------

  -- The two embeddings jointly: every center name is in at least one
  -- image (no skip/skip); a left-only name is X⊑★; a name in both images
  -- names paired rep. vars ("names name paired rep. vars").
  data Joint (P : RVar → RVar → Set)
      : ∀ {η η′ Ω} → η ↪ Ω → η′ ↪ Ω → Set where
    joint[]    : Joint P []↪ []↪
    both       : ∀ {α β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
      → P α β → Joint P ι ι′
      → Joint P (keep {α = α} {m = m} ι) (keep {α = β} {m = m} ι′)
    left-only  : ∀ {α η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
      → Joint P ι ι′
      → Joint P (keep {α = α} {m = X⊑★} ι) (skip {m = X⊑★} ι′)
    right-only : ∀ {β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
      → Joint P ι ι′
      → Joint P (skip {m = m} ι) (keep {α = β} {m = m} ι′)

  -- Representation imprecision `μ ⊢ R ⊑ᴿ⟨ W ⟩ R′` (design.md D23): two
  -- payloads compared in the representation universe (Ctx §4).  μ holds
  -- one mark per local ∀-bound variable, shared by both sides as in
  -- `_⊢_⊑_` (index < length μ is local); index `length μ + α` is the
  -- free rep. var α.  The rules are `_⊢_⊑_`'s, with `X⊑X` split into a
  -- local case and a free case (paired through ϱ = ϱᵍ ∪ ϱˡ), and one
  -- extra case: a free left rep. var against ★ (`α⊑★`, no condition:
  -- a rep. var carries no mark; marks belong to names, D11/D12).
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

  -- "Paired rep. vars agree": both abstract; an abstract left rep. var
  -- against β:=★; or two payloads related by `RepImp` (design.md D23)
  data Agree (W : World Δ Δ′) (α β : RVar) : Set where
    abst-abst : reps Δ ∋ʳ α := abstR → reps Δ′ ∋ʳ β := abstR
      → Agree W α β
    abst-★    : reps Δ ∋ʳ α := abstR → Δ′ ∋rep β := ★
      → Agree W α β
    rep-rep   : ∀ {R R′}
      → Δ ∋rep α := R → Δ′ ∋rep β := R′
      → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′
      → Agree W α β

  -- Named uniqueness (design.md D25).  ϱ itself may give a rep. var
  -- several partners on either side; but among the rep. vars NAMED on
  -- one side, at most one is paired with a given rep. var named on the
  -- other side.  This is what `Interior`'s rejoin reads: a name a
  -- boundary introduces must join every other-side name in scope whose
  -- rep. var is paired with its own, and an embedding joins a name to at
  -- most one other name.  Rep. vars without a name in scope (store rep.
  -- vars, rep. vars hidden by an unbind) are unconstrained.
  NamedUniqueᴸ : World Δ Δ′ → Set
  NamedUniqueᴸ {Δ} {Δ′} W = ∀ {α α′ β}
    → names Δ ∋ᵅ α → names Δ ∋ᵅ α′ → names Δ′ ∋ᵅ β
    → Paired W α β → Paired W α′ β → α ≡ α′

  NamedUniqueᴿ : World Δ Δ′ → Set
  NamedUniqueᴿ {Δ} {Δ′} W = ∀ {α β β′}
    → names Δ ∋ᵅ α → names Δ′ ∋ᵅ β → names Δ′ ∋ᵅ β′
    → Paired W α β → Paired W α β′ → β ≡ β′

  -- β has no left partner that is named in Δ (D25's scoped analogue of
  -- D13's `NoLeftPartner`; a pending name's rep. var)
  NoNamedPartner : World Δ Δ′ → RVar → Set
  NoNamedPartner {Δ} W β = ∀ {α} → names Δ ∋ᵅ α → ¬ Paired W α β

  -- a right name no left name joins
  RightOnly : World Δ Δ′ → ℕ → Set
  RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

  -- a pending name (design.md D27): bound to a ★ rep. var β, right-only,
  -- at X⊑★ (the mark `∀⊑` gives a left-only binder), and β has no left
  -- partner with a name (so the pop keeps named uniqueness, as `wf-⊕⁺`)
  PendingOK : World Δ Δ′ → ℕ → Set
  PendingOK {Δ′ = Δ′} W k =
    Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
      × (μʷ W ∋ˡ emb (ηᴿʷ W) k := X⊑★) × NoNamedPartner W β

  record WfWorld (W : World Δ Δ′) : Set where
    constructor wf-world
    field
      wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
      wf-agree : ∀ {α β} → Paired W α β → Agree W α β
      -- D25 (replaces D13's one-left-partner rule): named uniqueness
      wf-namedᴸ : NamedUniqueᴸ W
      wf-namedᴿ : NamedUniqueᴿ W
      -- D27: the pending names are pending names, and distinct
      wf-pending  : All (PendingOK W) (πʷ W)
      wf-distinct : AllPairs _≢_ (πʷ W)
  open WfWorld public

module CI where
  open import Data.Nat using (ℕ)
  open import Ctx using (Ctxᵗ; _∋ˡ_:=_)
  open import Types using (Ty; ★)
  open import Conversion
    using (Mid; Tail; Conv; id; _↦_; `∀; mid; seal; _⨾seal_; tail;
           unseal; unseal_⨾_; ⌞_⌟)
  open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
  open IW

  private
    variable
      Δ Δ′ : Ctxᵗ
      A A′ : Ty
      X X′ : ℕ
      g g′ : Mid
      t t′ : Tail
      c c′ s s′ : Conv

  infix 4 _⊢ᵐ_⊑_ _⊢ᵀ_⊑_ _⊢ᶜ_⊑_

  mutual
    data MidImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
        : Mid → Mid → Set where
      conv-id⊑id : μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′
          --------------------------------
        → MidImp W (id A) (id A′)

      conv-↦⊑↦ : ConvImp W s s′ → ConvImp W c c′
          --------------------------------
        → MidImp W (s ↦ c) (s′ ↦ c′)

      conv-∀⊑∀ : ConvImp (W ⊕ X⊑X) c c′
          --------------------------------
        → MidImp W (`∀ c) (`∀ c′)

      -- C23b B0: the right conversion has no matching universal layer.
      conv-∀⊑ : ConvImp (W ⊕ᴸ) c ⌞ g′ ⌟
          --------------------------------
        → MidImp W (`∀ c) g′

    data TailImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
        : Tail → Tail → Set where
      conv-mid⊑mid : MidImp W g g′
          --------------------------------
        → TailImp W (mid g) (mid g′)

      conv-seal⊑seal : Joins W X X′
          --------------------------------
        → TailImp W (seal X) (seal X′)

      conv-⨾seal⊑⨾seal : TailImp W t t′ → Joins W X X′
          --------------------------------
        → TailImp W (t ⨾seal X) (t′ ⨾seal X′)

      -- C23a B3: a precise seal is absent from the dynamic conversion.
      conv-seal⊑id★ : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
          --------------------------------
        → TailImp W (seal X) (mid (id ★))

      -- the chain form: the last seal of a precise chain is absent
      conv-⨾seal⊑ : TailImp W t t′ → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
          --------------------------------
        → TailImp W (t ⨾seal X) t′

    data ConvImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
        : Conv → Conv → Set where
      conv-tail⊑tail : TailImp W t t′
          --------------------------------
        → ConvImp W (tail t) (tail t′)

      conv-unseal⊑unseal : Joins W X X′
          --------------------------------
        → ConvImp W (unseal X) (unseal X′)

      conv-unseal⨾⊑unseal⨾ : Joins W X X′ → ConvImp W c c′
          --------------------------------
        → ConvImp W (unseal X ⨾ c) (unseal X′ ⨾ c′)

      -- C23a B3: a precise unseal is absent from the dynamic conversion.
      conv-unseal⊑id★ : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
          --------------------------------
        → ConvImp W (unseal X) ⌞ id ★ ⌟

      -- the chain form: the first unseal of a precise chain is absent
      conv-unseal⨾⊑ : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★ → ConvImp W c c′
          --------------------------------
        → ConvImp W (unseal X ⨾ c) c′

  _⊢ᵐ_⊑_ : World Δ Δ′ → Mid → Mid → Set
  W ⊢ᵐ g ⊑ g′ = MidImp W g g′

  _⊢ᵀ_⊑_ : World Δ Δ′ → Tail → Tail → Set
  W ⊢ᵀ t ⊑ t′ = TailImp W t t′

  _⊢ᶜ_⊑_ : World Δ Δ′ → Conv → Conv → Set
  W ⊢ᶜ c ⊑ c′ = ConvImp W c c′

module TI where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.List using (List; []; _∷_; _++_; length)
  open import Data.List.Relation.Unary.All using (All; [])
  open import Data.Maybe using (just)
  open import Data.Product using (Σ-syntax; _×_; _,_)
  open import Data.Sum using (_⊎_; inj₁)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import Types using (Ty; `ℕ; `𝔹; ★; _⇒_; `∀)
  open import Ctx
  open import Conversion using (Conv; _⊢_∶_⇝_; ⌞_⌟; Mid; `∀)
  open import Boundary
    using (Boundary; Change; bind; BoundaryWf; TyBetaBoundary; Fresh; toExt)
  open import Coercion
    using (Coercion; ModeEnv; _∣_⊢ᵖ_∶_⟹_; NonVar; _∈ᵗ_; ∀ᵖ_; genᵖ_)
  open import Terms
  open import Imprecision using (VarImp; X⊑X; ⇒⊑⇒)
  open IW
  open CI using (ConvImp)

  private
    variable
      Δ Δ′ Δᵢ : Ctxᵗ
      Γ : Ctx

  ------------------------------------------------------------------------
  -- 1. Side-premise bundles
  ------------------------------------------------------------------------

  -- the literals and their types (the three constant forms of GTNF)
  data Lit : Term → Ty → Set where
    lit-$     : ∀ {n} → Lit ($ n) `ℕ
    lit-true  : Lit `true `𝔹
    lit-false : Lit `false `𝔹

  -- the premises of `⊢cast` but the subterm's typing
  data CastTy (Δ : Ctxᵗ) (μ : ModeEnv) (p : Coercion) (B A : Ty) : Set where
    cast-ty : Δ ∣ μ ⊢ᵖ p ∶ B ⟹ A → length μ ≡ length (names Δ)
      → CastTy Δ μ p B A

  -- the premises of `⊢ν` but `L`'s typing: `ν A · L ⟨ c ⟩` at B, for an
  -- `L : ∀ C`
  data NuTy (Δ : Ctxᵗ) (A C : Ty) (c : Conv) (B : Ty) : Set where
    nu-ty : ∀ {R Δᵢ Δᶜ Cₑ}
      → Δ ⊢ᵗ A
      → Δ ⊢ᶜ A ~ R
      → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
      → Δᶜ ⊢ c ∶ C ⇝ Cₑ
      → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
      → Δ ⊢ᵗ B
      → NuTy Δ A C c B

  -- the premises of `boundary` but the interior's typing: `[Θ] M ⟨c⟩`
  -- at Bₑ on Δ, for an interior `M : Bᵢ` on Δᵢ
  data BdyTy (Δ : Ctxᵗ) (Θ : Boundary) (Δᵢ : Ctxᵗ) (Bᵢ : Ty) (c : Conv)
      (Bₑ : Ty) : Set where
    bdy-ty : ∀ {Δᶜ Cᵢ Cₑ}
      → BoundaryWf Δ Θ Δᵢ Δᶜ
      → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
      → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
      → Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ
      → Δ ⊢ᵗ Bₑ
      → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ

  -- D17's conversion premise, tied to the exact conversion contexts
  -- selected by the two `NuTy` witnesses.  `underν²` puts the two ν-bound
  -- rep. vars in ϱˡ; the two TyBeta boundaries then introduce their
  -- both-sided names in the conversion contexts.
  NuConversionImp : ∀ {Δ Δ′ A A′ C C′ c c′ B B′}
    → (W : World Δ Δ′)
    → NuTy Δ A C c B → NuTy Δ′ A′ C′ c′ B′ → Set
  NuConversionImp {c = c} {c′ = c′} W
    (nu-ty {R = R} {Δᶜ = Δᶜ} wA rA mw ⊢c eq wB)
    (nu-ty {R = R′} {Δᶜ = Δ′ᶜ} wA′ rA′ mw′ ⊢c′ eq′ wB′) =
    Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
      (ConversionInterior (underν² R R′ W) TyBetaBoundary TyBetaBoundary Wᶜ
      × ConvImp Wᶜ c c′)

  -- D17's boundary case, likewise tied to the conversion contexts in the
  -- two `BdyTy` witnesses.  This is separate from `Interior`, whose worlds
  -- relate the terms inside the boundaries.
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

  -- Reassembly: each bundle and the subterm's typing give the typing.
  ⊢lit : ∀ {k A} → Lit k A → Δ ∣ Γ ⊢ k ⦂ A
  ⊢lit lit-$     = ⊢$
  ⊢lit lit-true  = ⊢true
  ⊢lit lit-false = ⊢false

  ⊢cast′ : ∀ {M μ p B A} → CastTy Δ μ p B A → Δ ∣ Γ ⊢ M ⦂ B
    → Δ ∣ Γ ⊢ M ⟨ μ ∣ p ⟩ ⦂ A
  ⊢cast′ (cast-ty ⊢p len) ⊢M = ⊢cast ⊢M ⊢p len

  ⊢ν′ : ∀ {A C c B L} → NuTy Δ A C c B → Δ ∣ Γ ⊢ L ⦂ `∀ C
    → Δ ∣ Γ ⊢ ν A · L ⟨ c ⟩ ⦂ B
  ⊢ν′ (nu-ty wA rA mw ⊢c eq wB) ⊢L = ⊢ν wA rA ⊢L mw ⊢c eq wB

  ⊢⟪⟫′ : ∀ {Θ Bᵢ c Bₑ M} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ
  ⊢⟪⟫′ (bdy-ty mw ⊢c eqᵢ eqₑ wB) ⊢M = boundary mw ⊢M ⊢c eqᵢ eqₑ wB

  -- Inversion: a typing gives the bundle back (used by the examples to
  -- read side premises off a `tc` derivation).
  cast-inv : ∀ {M μ p A} → Δ ∣ Γ ⊢ M ⟨ μ ∣ p ⟩ ⦂ A
    → Σ[ B ∈ Ty ] ((Δ ∣ Γ ⊢ M ⦂ B) × CastTy Δ μ p B A)
  cast-inv (⊢cast ⊢M ⊢p len) = _ , ⊢M , cast-ty ⊢p len

  ν-inv : ∀ {A L c B} → Δ ∣ Γ ⊢ ν A · L ⟨ c ⟩ ⦂ B
    → Σ[ C ∈ Ty ] ((Δ ∣ Γ ⊢ L ⦂ `∀ C) × NuTy Δ A C c B)
  ν-inv (⊢ν wA rA ⊢L mw ⊢c eq wB) = _ , ⊢L , nu-ty wA rA mw ⊢c eq wB

  ⟪⟫-inv : ∀ {M Θ c Bₑ} → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ
    → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Bᵢ ∈ Ty ]
        ((Δᵢ ∣ [] ⊢ M ⦂ Bᵢ) × BdyTy Δ Θ Δᵢ Bᵢ c Bₑ)
  ⟪⟫-inv (boundary mw ⊢M ⊢c eqᵢ eqₑ wB) =
    _ , _ , ⊢M , bdy-ty mw ⊢c eqᵢ eqₑ wB

  ------------------------------------------------------------------------
  -- 2. Pending names (design.md D27) and the relation
  ------------------------------------------------------------------------

  -- `Λ⊑`'s binder: a fresh left-only name (no pending name), or the POP
  -- of the head pending name k (`Open1`, ImprecisionWorld §5: the left
  -- binder joins the right name k; its abstract rep. var is paired
  -- lexically with k's β:=★)
  data Claim : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
    claim-fresh : ∀ {Ω ϱᵍ ϱˡ} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
      → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in Claim W (W ⊕ᴸ)
    claim-pop   : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      → Open1 W W₁ → Claim W W₁

  -- `cast⊑`'s pending names (conclusion π, premise πₚ): none; or a `∀ᵖ`
  -- layer passes them to the cast value (as InstX's `inst-∀`); or a
  -- `genᵖ` layer pops the LAST pending name (as InstX's `inst-gen`: the
  -- value under a gen does not see the binder, so its premise has none).
  -- One gen pops one name: `inst-gen`'s result is no value, so InstX
  -- cannot open a second gen layer either.
  data CastClaim (M : Term) : Coercion → List ℕ → List ℕ → Set where
    cc-plain : ∀ {c} → CastClaim M c [] []
    cc-∀     : ∀ {c k π πₚ}
      → Value M
      → CastClaim M c π πₚ
      → CastClaim M (∀ᵖ c) (k ∷ π) (k ∷ πₚ)
    cc-gen   : ∀ {c k}
      → Value M
      → CastClaim M (genᵖ c) (k ∷ []) []

  -- `ForallConv c π`: c has a `∀` layer for each name of π
  data ForallConv : Conv → List ℕ → Set where
    fc-[] : ∀ {c} → ForallConv c []
    fc-∷  : ∀ {s k π} → ForallConv s π → ForallConv ⌞ `∀ s ⌟ (k ∷ π)

  -- `⟪⟫⊑`'s pending names (conclusion, interior) pass into the left
  -- boundary unchanged (they are RIGHT name positions, and the right
  -- does not move) when the boundary is a ∀-value (as InstX's `inst-⟪⟫`)
  data BdyClaim (M : Term) (c : Conv) : List ℕ → List ℕ → Set where
    bc-plain : BdyClaim M c [] []
    bc-∀     : ∀ {k π}
      → Simple M
      → ForallConv c (k ∷ π)
      → BdyClaim M c (k ∷ π) (k ∷ π)

  -- a pending name continues through Θ′ (k′ is its interior position)
  data Carried (Θ′ : Boundary) : List ℕ → List ℕ → Set where
    ca-[] : Carried Θ′ [] []
    ca-∷  : ∀ {k k′ π π′}
      → toExt Θ′ k′ ≡ just k
      → Carried Θ′ π π′
      → Carried Θ′ (k ∷ π) (k′ ∷ π′)

  -- THE PUSH of `⊑⟪⟫` (conclusion π, interior): the carried names, then
  -- new names that Θ′ introduces (`Fresh`); pushing needs a left value.
  -- What a pending name is (bound to a ★ rep. var, right-only, X⊑★) is
  -- `WfWorld` of the interior world (ImprecisionWorld §8).
  data Push (Θ′ : Boundary) (M : Term) (π : List ℕ) : List ℕ → Set where
    push : ∀ {π′ new}
      → Carried Θ′ π π′
      → All (Fresh Θ′) new
      → (new ≡ [] ⊎ Value M)
      → Push Θ′ M π (π′ ++ new)

  -- the push of nothing: the plain right-only boundary rule
  push-none : ∀ {Θ′ M} → Push Θ′ M [] []
  push-none = push ca-[] [] (inj₁ refl)


open IW
open CI using (ConvImp)
open TI

------------------------------------------------------------------------
-- 1. HEAD's relation (TermImprecision §2, verbatim), with its two
--    pending-name side relations as PARAMETERS: `ClaimR` (Λ⊑'s binder)
--    and `PushR` (⊑⟪⟫'s push).  `Rel Claim Push` is HEAD's relation.
------------------------------------------------------------------------

module Rel
    (ClaimR : ∀ {Δ Δ′ : Ctxᵗ} → World Δ Δ′ → World (underΛ Δ) Δ′ → Set)
    (PushR : Boundary → Term → List ℕ → List ℕ → Set) where

  infix 3 _∣_⊢_⊑_∶_

  -- The relation is INDEXED by the world (not parameterized).  The
  -- structural rules are stated at a world in constructor form with no
  -- pending name, `world Ω ηᴸ ηᴿ ϱᵍ ϱˡ []` (Ω the center, ImprecisionWorld
  -- §3), where the index `_⊑ᵂ⟨_⟩_` computes to the plain `Ω ⊢ … ⊑ …`;
  -- the rules for pending names relate the `πʷ` of their worlds by
  -- `Claim`, `CastClaim`, `BdyClaim`, `Push`.
  data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ}
      : (W : World Δ Δ′) → CtxImp W → Term → Term
      → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

    ----------------------------------------------------------------------
    -- Congruence (GTSFImp x⊑x², κ⊑κ², ƛ⊑ƛ², ·⊑·²)

    x⊑x : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
      → γ ∋ʷ x ⦂ ctx-imp A A′ p
        --------------------------------
      → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

    κ⊑κ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ k ι}
      → Lit k ι
      → (p : ι ⊑ᵂ⟨ W ⟩ ι)
        --------------------------------
      → W ∣ γ ⊢ k ⊑ k ∶ p

    ƛ⊑ƛ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → Δ ⊢ᵗ A
      → Δ′ ⊢ᵗ A′
      → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
        ---------------------------------------------
      → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

    ·⊑· : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ L L′ M M′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
      → W ∣ γ ⊢ M ⊑ M′ ∶ pA
        ---------------------------------------------
      → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

    ----------------------------------------------------------------------
    -- Blame (GTSFImp blame⊑²); no pending name (under one the left is a
    -- value)

    blame⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ ℓ M′ A A′}
      → Δ ⊢ᵗ A
      → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
      → (p : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

    ----------------------------------------------------------------------
    -- Casts (GTSFImp cast⊑cast², cast⊑², ⊑cast²)

    cast⊑cast : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ μ c B A
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    -- D27: plain, a ∀ᵖ layer passes the pending names, or a gen layer
    -- pops the last one (`CastClaim`); the premise world is W with the
    -- premise's pending names
    cast⊑ : ∀ {W : World Δ Δ′} {πₚ γ M M′ μ c B A A′}
        {p : B ⊑ᵂ⟨ record W { πʷ = πₚ } ⟩ A′}
      → CastClaim M c (πʷ W) πₚ
      → record W { πʷ = πₚ } ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ μ c B A
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

    -- carries the pending names (the right cast does not touch the left)
    ⊑cast : ∀ {W : World Δ Δ′} {γ M M′ μ′ c′ A B′ A′}
        {p : A ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    ----------------------------------------------------------------------
    -- Type abstraction (GTSFImp Λ⊑Λ², Λ⊑²)

    Λ⊑Λ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
      → LiftCtx X⊑X γ γ′
      → Value V
      → Value V′
      → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

    -- the right term crosses the left binder unweakened; D27: the binder
    -- is fresh and left-only, or it POPS the head pending name (`Claim`)
    Λ⊑ : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
        {γ γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W₁ ⟩ B′}
      → ClaimR W W₁
      → NonVar A
      → 0 ∈ᵗ A
      → LiftCtxᴸ γ γ′
      → Value V
      → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
        ---------------------------------------------
      → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

    -- (∀⊑⟪+⟫ was REMOVED by design.md D26; its instances are now a push
    -- of `⊑⟪⟫` followed by a pop of `Λ⊑` or `cast⊑`, D27)

    ----------------------------------------------------------------------
    -- Instantiation (GTSFImp •⊑•², •⊑²); there is no ⊑ν

    ν⊑ν : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
      → W ∣ γ ⊢ L ⊑ L′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ A′
      → (n : NuTy Δ A C c B)
      → (n′ : NuTy Δ′ A′ C′ c′ B′)
      → NuConversionImp W n n′
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
        ---------------------------------------------
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

    ν⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ M′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ ★
      → NuTy Δ A C c B
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
        ---------------------------------------------
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

    ----------------------------------------------------------------------
    -- Boundaries (these replace GTSFImp's reveal/conceal rules).  The
    -- interior is term-closed, so each premise has γ = [].  The interior
    -- world must be well formed (design.md §12.2, D15; Jeremy,
    -- 2026-10-03): `WfWorld Wᵢ` is a premise (with the conditions on the
    -- interior's pending names, D27).

    ⟪⟫⊑⟪⟫ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
        ∀ {Δᵢ Δ′ᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ}
      → let Wᵢ = world {Δᵢ} {Δ′ᵢ} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ [] in
        ∀ {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
      → Interior W Θ Θ′ Wᵢ
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
      → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
      → BdyConversionImp W b b′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

    -- D27: the pending names pass into a ∀-boundary (`BdyClaim`)
    ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
        {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
      → Interior W Θ [] Wᵢ
      → BdyClaim M c (πʷ W) (πʷ Wᵢ)
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → BdyTy Δ Θ Δᵢ Aᵢ c A
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

    -- D27: carry the pending names through Θ′ and push new ones (`Push`)
    ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
        {γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
      → Interior W [] Θ′ Wᵢ
      → PushR Θ′ M (πʷ W) (πʷ Wᵢ)
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
        ---------------------------------------------
      → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  -- The relation with its two types explicit.  `_⊑ᵂ⟨_⟩_` (OpenImp)
  -- cannot be inverted when the pending names are not known, so a
  -- statement over pending names gives A and A′ this way.
  infix 3 _∣_⊢_⊑_∶⟨_,_⟩_
  _∣_⊢_⊑_∶⟨_,_⟩_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
    → (A A′ : Ty) → A ⊑ᵂ⟨ W ⟩ A′ → Set
  W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p = _∣_⊢_⊑_∶_ W γ M M′ {A} {A′} p


------------------------------------------------------------------------
-- 2. The candidate fixes, as instances of `Rel`
------------------------------------------------------------------------

private
  variable
    Δ Δ′ : Ctxᵗ

-- (a) push order `new ++ π′`: new names BEFORE the carried ones
data PushA (Θ′ : Boundary) (M : Term) (π : List ℕ) : List ℕ → Set where
  pushA : ∀ {π′ new}
    → Carried Θ′ π π′
    → All (Fresh Θ′) new
    → (new ≡ [] ⊎ Value M)
    → PushA Θ′ M π (new ++ π′)

-- (c1) any interleaving of the carried and the new names (the order of
-- each part kept): the most liberal ORDER
data Shuffle : List ℕ → List ℕ → List ℕ → Set where
  sh-[] : Shuffle [] [] []
  sh-l  : ∀ {x xs ys zs} → Shuffle xs ys zs → Shuffle (x ∷ xs) ys (x ∷ zs)
  sh-r  : ∀ {y xs ys zs} → Shuffle xs ys zs → Shuffle xs (y ∷ ys) (y ∷ zs)

data PushS (Θ′ : Boundary) (M : Term) (π : List ℕ) : List ℕ → Set where
  pushS : ∀ {π′ new πᵢ}
    → Carried Θ′ π π′
    → All (Fresh Θ′) new
    → (new ≡ [] ⊎ Value M)
    → Shuffle π′ new πᵢ
    → PushS Θ′ M π πᵢ

-- (b) the order stated at the POP: a binder may pop ANY pending name
-- (not only the head)
data OpenAny {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  open-any : ∀ {μ ϱᵍ ϱˡ k π₁ π₂ β} {ι : names Δ ↪ μ} {ι′ : names Δ′ ↪ μ}
      {ι⁺ : names (underΛ Δ) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → OpenAny (world μ ι ι′ ϱᵍ ϱˡ (π₁ ++ k ∷ π₂))
              (world μ ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) (π₁ ++ π₂))

data ClaimAny : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  any-fresh : ∀ {Ω ϱᵍ ϱˡ} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
    → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in ClaimAny W (W ⊕ᴸ)
  any-pop   : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
    → OpenAny W W₁ → ClaimAny W W₁

-- (c2) CLAIM A REP. VAR: with nothing pending, the left binder may be
-- left-only (X⊑★, as `claim-fresh`) and paired LEXICALLY with a right
-- ★ rep. var β that has no right name in scope and no named left
-- partner.  A right boundary that later names β (`+X^β`) rejoins the
-- binder by `Interior.join-fresh` (D25), so no pending name and no
-- order is needed.  HEAD's two claims are kept (`claim-old`).
data ClaimRep : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  claim-old : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
    → Claim W W₁ → ClaimRep W W₁
  claim-rep : ∀ {Ω ϱᵍ ϱˡ β} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
    → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      Δ′ ∋rep β := ★
    → ¬ (names Δ′ ∋ᵅ β)
    → NoNamedPartner W β
    → ClaimRep W (world (X⊑★ ∷ Ω) (keep (relabel suc ηᴸ)) (skip ηᴿ)
                    (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) [])

module D27  = Rel Claim Push        -- HEAD
module FixA = Rel Claim PushA
module FixS = Rel Claim PushS
module FixB = Rel ClaimAny Push
module FixR = Rel ClaimRep Push

------------------------------------------------------------------------
-- 3. The example H1′: sources, initial cast terms, runs
------------------------------------------------------------------------
-- Sources (cast insertion is the compilation; an ascription at the
-- term's own type inserts no cast):
--   L:  (ΛX.ΛY.λx:X.λy:Y.x  : ∀X.∀Y.X→Y→X)
--   R:  ((ΛX.ΛY.λx:X.λy:Y.x : ∀Y.★→Y→★) : ★→★→★)
-- The sources are related: same term, and `∀X.∀Y.X→Y→X ⊑ ∀Y.★→Y→★
-- ⊑ ★→★→★` (`src-1`, `src-2` below).

module Ex where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)

  K2 KY : Ty
  K2 = `∀ (`∀ (` 1 ⇒ (` 0 ⇒ ` 1)))   -- ∀X.∀Y.X→Y→X
  KY = `∀ (★ ⇒ (` 0 ⇒ ★))              -- ∀Y.★→Y→★

  src-1 : [] ⊢ K2 ⊑ KY
  src-1 = ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
            (∀⊑∀ (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))

  src-2 : [] ⊢ KY ⊑ (★ ⇒ (★ ⇒ ★))
  src-2 = ∀⊑ nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var))
            (⇒⊑⇒ ★⊑★ (⇒⊑⇒ (X⊑★ here) ★⊑★))

  NL L1 KL : Term
  NL = ƛ (` 1) ∙ (ƛ (` 0) ∙ ` 1)        -- λx:X.λy:Y.x
  L1 = Λ NL
  KL = Λ L1

  vNL : Value NL
  vNL = V-simple S-ƛ
  vL1 : Value L1
  vL1 = V-simple (S-Λ vNL)
  vKL : Value KL
  vKL = V-simple (S-Λ vL1)

  -- the two casts: ∀X.∀Y.X→Y→X ⇒ ∀Y.★→Y→★ ⇒ ★→★→★
  instX∀ instY ci cf : Coercion
  instX∀ = instᵖ (∀ᵖ (((` 1) ？ 0) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) !))))
  instY  = instᵖ (idᵖ ★ ↦ᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★))
  ci     = idᵖ ★ ↦ᵖ (idᵖ (` 0) ↦ᵖ idᵖ ★)
  cf     = idᵖ ★ ↦ᵖ (idᵖ ★ ↦ᵖ idᵖ ★)

  L₀ R₀ : Term
  L₀ = KL
  R₀ = (KL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ K2
  L₀-⊢ = tc

  R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ ★ ⇒ (★ ⇒ ★)
  R₀-⊢ = tc

  -- the right's states 2 and 4 (state 4 is its final value)
  ΘA ΘY ΘX : Boundary
  ΘA = bind 0 0 ∷ []      -- the first Inst boundary +X^α
  ΘY = bind 0 0 ∷ []      -- the second Inst boundary +Y^β (outer)
  ΘX = bind 1 1 ∷ []      -- +X^α after InstX moved it inside

  cA cX cY : Conv
  cA = tail (mid (`∀ (tail (mid (tail (seal 1)
         ↦ tail (mid (tail (mid (id (` 0))) ↦ unseal 1)))))))
  cX = tail (mid (tail (seal 1)
         ↦ tail (mid (tail (mid (id (` 0))) ↦ unseal 1))))
  cY = tail (mid (tail (mid (id ★))
         ↦ tail (mid (tail (seal 0) ↦ tail (mid (id ★))))))

  BA R₂ BX CI BY R₄ : Term
  BA = L1 ⟪ ΘA , cA ⟫
  R₂ = (BA ⟨ [] ∣ ∀ᵖ ci ⟩) ⟨ [] ∣ instY ⟩
  BX = NL ⟪ ΘX , cX ⟫
  CI = BX ⟨ X∼X ∷ [] ∣ ci ⟩
  BY = CI ⟪ ΘY , cY ⟫
  R₄ = BY ⟨ [] ∣ cf ⟩

  R₂-state : head (drop 2 (evalTerms 30 R₀-⊢)) ≡ just R₂
  R₂-state = refl

  R₄-state : head (drop 4 (evalTerms 30 R₀-⊢)) ≡ just R₄
  R₄-state = refl

  -- the run stops at R₄: it is a value, the right's final value
  R₄-final : length (evalTerms 30 R₀-⊢) ≡ 5
  R₄-final = refl

  -- the variant with ONE cast `inst X. inst Y. (X? → Y? → X!)` to
  -- ★→★→★ (PushTypePremise H1): its pre-Merge state 4 is the same
  -- nesting, but the right then Merges, and the merged boundary
  -- [+Y^β, +X^α] may push [X, Y] in either order
  inst2 : Coercion
  inst2 = instᵖ (instᵖ (((` 1) ？ 0) ↦ᵖ (((` 0) ？ 0) ↦ᵖ ((` 1) !))))

  R₀m : Term
  R₀m = KL ⟨ [] ∣ inst2 ⟩

  R₀m-⊢ : empty ∣ [] ⊢ R₀m ⦂ ★ ⇒ (★ ⇒ ★)
  R₀m-⊢ = tc

  R₀m-steps : length (evalTerms 30 R₀m-⊢) ≡ 6
  R₀m-steps = refl

  -- the earlier states are no values (an `inst` cast is not inert;
  -- states 1 and 3 are ν-terms, and `Value` has no ν case)
  R₀-nv : ¬ Value R₀
  R₀-nv (V-simple (S-cast _ ()))

  R₂-nv : ¬ Value R₂
  R₂-nv (V-simple (S-cast _ ()))

  vR₄ : Value R₄
  vR₄ = V-simple (S-cast (V-⟪⟫ (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦) I-fun) I-↦)

  -- the typing bundles, read off `tc` derivations
  ΔT1 ΔT2 ΔA ΔY ΔXY Δ1 : Ctxᵗ
  ΔT1 = allocate ★ empty                          -- after the 1st TyBeta
  ΔT2 = allocate ★ ΔT1                            -- after the 2nd TyBeta
  ΔA  = (bindR ★ ∷ []) ∣ (0 ∷ [])                -- inside +X^α (state 2)
  ΔY  = (bindR ★ ∷ bindR ★ ∷ []) ∣ (0 ∷ [])      -- inside +Y^β
  ΔXY = (bindR ★ ∷ bindR ★ ∷ []) ∣ (0 ∷ 1 ∷ [])  -- inside +Y^β, +X^α
  Δ1  = underΛ empty                              -- left, under ΛX

  R₂-⊢ : ΔT1 ∣ [] ⊢ R₂ ⦂ ★ ⇒ (★ ⇒ ★)
  R₂-⊢ = tc

  R₄-⊢ : ΔT2 ∣ [] ⊢ R₄ ⦂ ★ ⇒ (★ ⇒ ★)
  R₄-⊢ = tc

  instX∀-ty : CastTy empty [] instX∀ K2 KY
  instX∀-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (proj₁ (proj₂ (cast-inv {Γ = []} R₀-⊢)))))

  instY-ty₀ : CastTy empty [] instY KY (★ ⇒ (★ ⇒ ★))
  instY-ty₀ = proj₂ (proj₂ (cast-inv {Γ = []} R₀-⊢))

  instY-ty₂ : CastTy ΔT1 [] instY KY (★ ⇒ (★ ⇒ ★))
  instY-ty₂ = proj₂ (proj₂ (cast-inv {Γ = []} R₂-⊢))

  ∀ci-ty : CastTy ΔT1 [] (∀ᵖ ci) KY KY
  ∀ci-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (proj₁ (proj₂ (cast-inv {Γ = []} R₂-⊢)))))

  bA : BdyTy ΔT1 ΘA ΔA (`∀ (` 1 ⇒ (` 0 ⇒ ` 1))) cA KY
  bA = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (proj₁ (proj₂ (cast-inv {Γ = []}
      (proj₁ (proj₂ (cast-inv {Γ = []} R₂-⊢)))))))))

  ⊢BY : ΔT2 ∣ [] ⊢ BY ⦂ ★ ⇒ (★ ⇒ ★)
  ⊢BY = proj₁ (proj₂ (cast-inv {Γ = []} R₄-⊢))

  cf-ty : CastTy ΔT2 [] cf (★ ⇒ (★ ⇒ ★)) (★ ⇒ (★ ⇒ ★))
  cf-ty = proj₂ (proj₂ (cast-inv {Γ = []} R₄-⊢))

  bY : BdyTy ΔT2 ΘY ΔY (★ ⇒ (` 0 ⇒ ★)) cY (★ ⇒ (★ ⇒ ★))
  bY = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} ⊢BY)))

  ⊢CI : ΔY ∣ [] ⊢ CI ⦂ ★ ⇒ (` 0 ⇒ ★)
  ⊢CI = proj₁ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} ⊢BY)))

  ci-ty : CastTy ΔY (X∼X ∷ []) ci (★ ⇒ (` 0 ⇒ ★)) (★ ⇒ (` 0 ⇒ ★))
  ci-ty = proj₂ (proj₂ (cast-inv {Γ = []} ⊢CI))

  bX : BdyTy ΔY ΘX ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cX (★ ⇒ (` 0 ⇒ ★))
  bX = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (proj₁ (proj₂ (cast-inv {Γ = []} ⊢CI))))))

  -- indices
  q-top : ∀ {μ} → μ ⊢ K2 ⊑ (★ ⇒ (★ ⇒ ★))
  q-top = ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
    (∀⊑ nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var))
      (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here)))))

  q-src1 : ∀ {μ} → μ ⊢ K2 ⊑ KY
  q-src1 = ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
            (∀⊑∀ (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))

  idK : ∀ {μ} → μ ⊢ `∀ (` 1 ⇒ (` 0 ⇒ ` 1)) ⊑ `∀ (` 1 ⇒ (` 0 ⇒ ` 1))
  idK = ∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X))

------------------------------------------------------------------------
-- 4. Positive derivations, in every relation that contains HEAD's
--    Claim and Push (so in D27 and in each fix)
------------------------------------------------------------------------

module Pos
    (ClaimR : ∀ {Δ Δ′ : Ctxᵗ} → World Δ Δ′ → World (underΛ Δ) Δ′ → Set)
    (PushR : Boundary → Term → List ℕ → List ℕ → Set)
    (inC : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁} → Claim W W₁ → ClaimR W W₁)
    (inP : ∀ {Θ′ M π πᵢ} → Push Θ′ M π πᵢ → PushR Θ′ M π πᵢ) where
  open Rel ClaimR PushR
  open Ex
  open import examples.TypeCheck using (tf)

  -- the initial pair, at ∅ʷ: ⊑cast twice, then KL ⊑ KL by Λ⊑Λ twice
  init : ∅ʷ ∣ [] ⊢ L₀ ⊑ R₀ ∶ q-top
  init =
    ⊑cast
      (⊑cast
        (Λ⊑Λ lift-[] vL1 vL1
          (Λ⊑Λ lift-[] vNL vNL
            (ƛ⊑ƛ {pA = X⊑X} tf tf
              (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
            idK)
          (∀⊑∀ idK))
        instX∀-ty q-src1)
      instY-ty₀ q-top

  -- state 2: the push and pop of P3 (the right's first Inst boundary
  -- +X^α pushes X, the left's ΛX pops it), then Λ⊑Λ for Y
  W₂ : World empty ΔT1
  W₂ = world [] []↪ []↪ [] [] []

  WA : World empty ΔA
  WA = world (X⊑★ ∷ []) (skip []↪) (keep []↪) [] [] (0 ∷ [])

  intA : Interior W₂ [] ΘA WA
  intA = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  wfA : WfWorld WA
  wfA = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    ((0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })) ∷ [])
    ([] ∷ [])

  st2 : W₂ ∣ [] ⊢ L₀ ⊑ R₂ ∶ q-top
  st2 =
    ⊑cast
      (⊑cast
        (⊑⟪⟫ intA (inP (push ca-[] (refl ∷ []) (inj₂ vKL))) wfA
          (Λ⊑ (inC (claim-pop (open1 join-here here r-here)))
            nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
            (Λ⊑Λ lift-[] vNL vNL
              (ƛ⊑ƛ {pA = X⊑X} tf tf
                (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
              idK)
            idK)
          bA q-src1)
        ∀ci-ty q-src1)
      instY-ty₂ q-top

module PosD27  = Pos Claim Push (λ c → c) (λ p → p)
module PosFixR = Pos ClaimRep Push claim-old (λ p → p)

------------------------------------------------------------------------
-- 5. Fix (c2): the final pair (KL, R₄) IS related.  The left's ΛX
--    claims the rep. var α (rep. var 1, no right name yet) at the top;
--    +Y^β pushes Y (HEAD's Push); the inner +X^α names α, so its fresh
--    X REJOINS the left X (Interior.join-fresh, D25) and only carries
--    Y; the left's ΛY pops Y; then the bodies at X ⊑ X, Y ⊑ Y.
------------------------------------------------------------------------

module FinalR where
  open FixR
  open Ex
  open import examples.TypeCheck using (tf)

  W₄ : World empty ΔT2
  W₄ = world [] []↪ []↪ [] [] []

  -- after the claim: left X at center 0 (X⊑★), paired with α
  W₄₁ : World Δ1 ΔT2
  W₄₁ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] ((0 , 1) ∷ []) []

  -- inside +Y^β: Y at center 0, pending; left X at center 1
  WY : World Δ1 ΔY
  WY = world (X⊑★ ∷ X⊑★ ∷ []) (skip (keep []↪)) (keep (skip []↪))
         [] ((0 , 1) ∷ []) (0 ∷ [])

  -- inside +X^α: X rejoins the left X at center 1; Y still pending
  WX : World Δ1 ΔXY
  WX = world (X⊑★ ∷ X⊑★ ∷ []) (skip (keep []↪)) (keep (keep []↪))
         [] ((0 , 1) ∷ []) (0 ∷ [])

  intY : Interior W₄₁ [] ΘY WY
  intY = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ { here here _ → (λ ()) , (λ { (inj₁ ())
                                               ; (inj₂ (there⇔ ())) })
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) refl here → there here
                     ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  intX : Interior WY [] ΘX WX
  intX = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , there here)
                        (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) (_ , here) refl refl →
                         (λ ()) , (λ ())
                     ; (_ , here) (_ , there here) _ ()
                     ; (_ , here) (_ , there (there ())) _ _
                     ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here (there here) _ →
                         (λ _ → inj₂ here⇔) , (λ _ → refl)
                     ; here here (inj₁ ()) ; here here (inj₂ ())
                     ; here (there (there ())) _
                     ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) refl (there here) → there here
                     ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) refl here → here
                     ; (_ , there here) () _
                     ; (_ , there (there ())) _ _ }
    }

  wfY : WfWorld WY
  wfY = wf-world (right-only (left-only joint[]))
    (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here (r-there r-here)
       ; (inj₂ (there⇔ ())) })
    (λ { (_ , here) (_ , here) _ _ _ → refl
       ; (_ , there ()) _ _ _ _ ; _ (_ , there ()) _ _ _ })
    (λ { _ (_ , here) (_ , here) _ _ → refl
       ; _ (_ , there ()) _ _ _ ; _ _ (_ , there ()) _ _ })
    ((0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) }) , here ,
      (λ { _ (inj₁ ()) ; _ (inj₂ (there⇔ ())) })) ∷ [])
    ([] ∷ [])

  wfX : WfWorld WX
  wfX = wf-world (right-only (both (inj₂ here⇔) joint[]))
    (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here (r-there r-here)
       ; (inj₂ (there⇔ ())) })
    (λ { (_ , here) (_ , here) _ _ _ → refl
       ; (_ , there ()) _ _ _ _ ; _ (_ , there ()) _ _ _ })
    (λ { _ _ _ (inj₂ here⇔) (inj₂ here⇔) → refl
       ; _ _ _ (inj₁ ()) _ ; _ _ _ _ (inj₁ ())
       ; _ _ _ (inj₂ (there⇔ ())) _ ; _ _ _ _ (inj₂ (there⇔ ())) })
    ((0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) }) , here ,
      (λ { _ (inj₁ ()) ; _ (inj₂ (there⇔ ())) })) ∷ [])
    ([] ∷ [])

  rK★ : ∀ {μ} → (X⊑★ ∷ μ) ⊢ `∀ (` 1 ⇒ (` 0 ⇒ ` 1)) ⊑ (★ ⇒ (★ ⇒ ★))
  rK★ = ∀⊑ nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var))
    (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here))))

  -- THE FINAL PAIR, related in fix (c2)
  final : W₄ ∣ [] ⊢ L₀ ⊑ R₄ ∶ q-top
  final =
    Λ⊑ (claim-rep (r-there r-here) (λ { (_ , ()) }) (λ { (_ , ()) }))
      nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
      (⊑cast
        (⊑⟪⟫ intY (push ca-[] (refl ∷ []) (inj₂ vL1)) wfY
          (⊑cast
            (⊑⟪⟫ intX (push (ca-∷ refl ca-[]) [] (inj₁ refl)) wfX
              (Λ⊑ (claim-old (claim-pop (open1 join-here here r-here)))
                nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var)) liftᴸ-[] vNL
                (ƛ⊑ƛ {pA = X⊑X} tf tf
                  (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
                (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)))
              bX
              (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))
            ci-ty
            (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))
          bY rK★)
        cf-ty rK★)
      q-top

  -- (c2) needs no push at all here: both left binders claim their rep.
  -- vars at the top (X ↦ α, Y ↦ β), and both right boundaries rejoin
  Δ2 : Ctxᵗ
  Δ2 = underΛ Δ1

  W₄₂ : World Δ2 ΔT2      -- Y_L at center 0 ↦ β, X_L at center 1 ↦ α
  W₄₂ = world (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (skip (skip []↪))
          [] ((0 , 0) ∷ (1 , 1) ∷ []) []

  WY2 : World Δ2 ΔY
  WY2 = world (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (keep (skip []↪))
          [] ((0 , 0) ∷ (1 , 1) ∷ []) []

  WX2 : World Δ2 ΔXY
  WX2 = world (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (keep (keep []↪))
          [] ((0 , 0) ∷ (1 , 1) ∷ []) []

  intY2 : Interior W₄₂ [] ΘY WY2
  intY2 = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; (there here) here _ →
            (λ ()) , (λ { (inj₁ ()) ; (inj₂ (there⇔ (there⇔ ()))) })
        ; _ (there ()) _ ; (there (there ())) _ _ }
    ; mark-left  = λ { (_ , here) refl here → here
                     ; (_ , there here) refl (there here) → there here
                     ; (_ , there (there ())) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  intX2 : Interior WY2 [] ΘX WX2
  intX2 = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , there here)
                        (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
        ; (_ , there here) (_ , here) refl refl → (λ ()) , (λ ())
        ; _ (_ , there here) _ ()
        ; _ (_ , there (there ())) _ _
        ; (_ , there (there ())) _ _ _ }
    ; join-fresh = λ
        { (there here) (there here) _ →
            (λ _ → inj₂ (there⇔ here⇔)) , (λ _ → refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ ()) ; (inj₂ (there⇔ (there⇔ ()))) })
        ; _ here (inj₁ ()) ; _ here (inj₂ ())
        ; _ (there (there ())) _ ; (there (there ())) _ _ }
    ; mark-left  = λ { (_ , here) refl here → here
                     ; (_ , there here) refl (there here) → there here
                     ; (_ , there (there ())) _ _ }
    ; mark-right = λ { (_ , here) refl here → here
                     ; (_ , there here) () _
                     ; (_ , there (there ())) _ _ }
    }

  agree2 : ∀ {Δ′} {W : World Δ2 Δ′} {α β}
    → Δ′ ∋rep 0 := ★ → Δ′ ∋rep 1 := ★
    → (ϱᵍʷ W ≡ []) → (ϱˡʷ W ≡ (0 , 0) ∷ (1 , 1) ∷ [])
    → Paired W α β → Agree W α β
  agree2 h0 h1 eg el (inj₁ p) rewrite eg with p
  ... | ()
  agree2 h0 h1 eg el (inj₂ p) rewrite el with p
  ... | here⇔            = abst-★ r-here h0
  ... | there⇔ here⇔     = abst-★ (r-there-abst r-here) h1
  ... | there⇔ (there⇔ ())

  uniq2 : ∀ {Δ′} {W : World Δ2 Δ′} → (ϱᵍʷ W ≡ [])
    → (ϱˡʷ W ≡ (0 , 0) ∷ (1 , 1) ∷ [])
    → ∀ {α α′ β β′} → Paired W α β → Paired W α′ β′
    → (α ≡ α′ → β ≡ β′) × (β ≡ β′ → α ≡ α′)
  uniq2 eg el (inj₁ p) _ rewrite eg with p
  ... | ()
  uniq2 eg el _ (inj₁ p) rewrite eg with p
  ... | ()
  uniq2 eg el (inj₂ p) (inj₂ p′) rewrite el with p | p′
  ... | here⇔ | here⇔ = (λ _ → refl) , (λ _ → refl)
  ... | here⇔ | there⇔ here⇔ = (λ ()) , (λ ())
  ... | there⇔ here⇔ | here⇔ = (λ ()) , (λ ())
  ... | there⇔ here⇔ | there⇔ here⇔ = (λ _ → refl) , (λ _ → refl)
  ... | there⇔ (there⇔ ()) | _
  ... | _ | there⇔ (there⇔ ())

  wfY2 : WfWorld WY2
  wfY2 = wf-world (both (inj₂ here⇔) (left-only joint[]))
    (agree2 r-here (r-there r-here) refl refl)
    (λ _ _ _ p p′ → proj₂ (uniq2 {W = WY2} refl refl p p′) refl)
    (λ _ _ _ p p′ → proj₁ (uniq2 {W = WY2} refl refl p p′) refl)
    [] []

  wfX2 : WfWorld WX2
  wfX2 = wf-world (both (inj₂ here⇔) (both (inj₂ (there⇔ here⇔)) joint[]))
    (agree2 r-here (r-there r-here) refl refl)
    (λ _ _ _ p p′ → proj₂ (uniq2 {W = WX2} refl refl p p′) refl)
    (λ _ _ _ p p′ → proj₁ (uniq2 {W = WX2} refl refl p p′) refl)
    [] []

  qF : (X⊑★ ∷ X⊑★ ∷ []) ⊢ ` 1 ⇒ (` 0 ⇒ ` 1) ⊑ ★ ⇒ (★ ⇒ ★)
  qF = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here)))

  qC : (X⊑★ ∷ X⊑★ ∷ []) ⊢ ` 1 ⇒ (` 0 ⇒ ` 1) ⊑ ★ ⇒ (` 0 ⇒ ★)
  qC = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))

  final-no-push : W₄ ∣ [] ⊢ L₀ ⊑ R₄ ∶ q-top
  final-no-push =
    Λ⊑ (claim-rep (r-there r-here) (λ { (_ , ()) }) (λ { (_ , ()) }))
      nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
      (Λ⊑ (claim-rep r-here (λ { (_ , ()) })
            (λ { _ (inj₁ ()) ; _ (inj₂ (there⇔ ())) }))
        nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var)) liftᴸ-[] vNL
        (⊑cast
          (⊑⟪⟫ intY2 push-none wfY2
            (⊑cast
              (⊑⟪⟫ intX2 push-none wfX2
                (ƛ⊑ƛ {pA = X⊑X} tf tf
                  (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
                bX qC)
              ci-ty qC)
            bY qF)
          cf-ty qF)
        rK★)
      q-top

  -- the DGG's `RelatedValues` side conditions hold at W₄
  W₄-wf : WfWorld W₄
  W₄-wf = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) _ _ _ _ }) (λ { _ (_ , ()) _ _ _ }) [] []

------------------------------------------------------------------------
-- 6. (KL, R₄) is NOT related by HEAD's relation, nor by fixes (a),
--    (b), (c1): for EVERY push relation `PushR`, and every claim
--    relation that (i) leaves a binder unpaired when nothing is
--    pending, and (ii) only renumbers the older pairs and joins.  At
--    every world over the final contexts with no pending name (the
--    DGG's `RelatedValues`), at every index.
------------------------------------------------------------------------

-- generic facts
var⊑var : ∀ {μ a b} → μ ⊢ ` a ⊑ ` b → a ≡ b
var⊑var X⊑X = refl

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

emb-relabel : ∀ {η Ω} (f : RVar → RVar) (ι : η ↪ Ω) (x : ℕ)
  → emb (relabel f ι) x ≡ emb ι x
emb-relabel f []↪      x       = refl
emb-relabel f (keep ι) zero    = refl
emb-relabel f (keep ι) (suc x) = cong suc (emb-relabel f ι x)
emb-relabel f (skip ι) x       = cong suc (emb-relabel f ι x)

-- a pop keeps the older left names at their centers
join-suc : ∀ {η η′ μ} {ι : η ↪ μ} {ι′ : η′ ↪ μ} {ι⁺ k}
  → Join↪ ι ι′ ι⁺ k → ∀ x → emb ι⁺ (suc x) ≡ emb ι x
join-suc {ι = skip ι} join-here x = cong suc (emb-relabel suc ι x)
join-suc (join-there j) x = cong suc (join-suc j x)

shiftᴸ-0 : ∀ {ϱ b} → ¬ (shiftᴸ ϱ ∋ᵨ 0 ⇔ b)
shiftᴸ-0 {_ ∷ ϱ} (there⇔ h) = shiftᴸ-0 h

shiftᴸ-suc : ∀ {ϱ a b} → shiftᴸ ϱ ∋ᵨ suc a ⇔ b → ϱ ∋ᵨ a ⇔ b
shiftᴸ-suc {(a , b) ∷ ϱ} here⇔      = here⇔
shiftᴸ-suc {_ ∷ ϱ}       (there⇔ h) = there⇔ (shiftᴸ-suc h)

map-suc-∋ : ∀ {ns X α} → ns ∋ˡ X := α → map suc ns ∋ˡ X := suc α
map-suc-∋ here      = here
map-suc-∋ (there h) = there (map-suc-∋ h)

lookΛ : ∀ {Δ X α} → Δ ∋ᵗ X := α → underΛ Δ ∋ᵗ suc X := suc α
lookΛ {_ ∣ _} h = there (map-suc-∋ h)

-- what the proof needs of a claim relation
record ClaimOK
    (ClaimR : ∀ {Δ Δ′ : Ctxᵗ} → World Δ Δ′ → World (underΛ Δ) Δ′ → Set)
    : Set₁ where
  field
    unpaired0 : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁}
      → ClaimR W W₁ → πʷ W ≡ [] → ∀ {b} → ¬ Paired W₁ 0 b
    old-pairs : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁}
      → ClaimR W W₁ → ∀ {a b} → Paired W₁ (suc a) b → Paired W a b
    old-joins : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁}
      → ClaimR W W₁ → ∀ {x y} → Joins W₁ (suc x) y → Joins W x y

pairs-⊕ᴸ : ∀ {ϱᵍ ϱˡ a b}
  → (shiftᴸ ϱᵍ ∋ᵨ suc a ⇔ b) ⊎ (shiftᴸ ϱˡ ∋ᵨ suc a ⇔ b)
  → (ϱᵍ ∋ᵨ a ⇔ b) ⊎ (ϱˡ ∋ᵨ a ⇔ b)
pairs-⊕ᴸ (inj₁ h) = inj₁ (shiftᴸ-suc h)
pairs-⊕ᴸ (inj₂ h) = inj₂ (shiftᴸ-suc h)

pairs-pop : ∀ {ϱᵍ ϱˡ a b β}
  → (shiftᴸ ϱᵍ ∋ᵨ suc a ⇔ b) ⊎ (((zero , β) ∷ shiftᴸ ϱˡ) ∋ᵨ suc a ⇔ b)
  → (ϱᵍ ∋ᵨ a ⇔ b) ⊎ (ϱˡ ∋ᵨ a ⇔ b)
pairs-pop (inj₁ h)           = inj₁ (shiftᴸ-suc h)
pairs-pop (inj₂ (there⇔ h))  = inj₂ (shiftᴸ-suc h)

joins-⊕ᴸ : ∀ {η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} {m x y}
  → emb (keep {α = zero} {m = m} (relabel suc ι)) (suc x)
      ≡ emb (skip {m = m} ι′) y
  → emb ι x ≡ emb ι′ y
joins-⊕ᴸ {ι = ι} {x = x} e = trans (sym (emb-relabel suc ι x)) (suc-inj e)

claim-joins : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁}
  → Claim W W₁ → ∀ {x y} → Joins W₁ (suc x) y → Joins W x y
claim-joins (claim-fresh {ηᴸ = ηᴸ} {ηᴿ = ηᴿ}) {x} {y} e =
  joins-⊕ᴸ {ι = ηᴸ} {ι′ = ηᴿ} {m = X⊑★} {x = x} {y = y} e
claim-joins (claim-pop (open1 j _ _)) {x} e = trans (sym (join-suc j x)) e

any-joins : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁}
  → ClaimAny W W₁ → ∀ {x y} → Joins W₁ (suc x) y → Joins W x y
any-joins (any-fresh {ηᴸ = ηᴸ} {ηᴿ = ηᴿ}) {x} {y} e =
  joins-⊕ᴸ {ι = ηᴸ} {ι′ = ηᴿ} {m = X⊑★} {x = x} {y = y} e
any-joins (any-pop (open-any j _ _)) {x} e = trans (sym (join-suc j x)) e

claimOK : ClaimOK Claim
claimOK = record
  { unpaired0 = λ { claim-fresh _ (inj₁ h) → shiftᴸ-0 h
                  ; claim-fresh _ (inj₂ h) → shiftᴸ-0 h
                  ; (claim-pop (open1 _ _ _)) () _ }
  ; old-pairs = λ { claim-fresh p → pairs-⊕ᴸ p
                  ; (claim-pop (open1 _ _ _)) p → pairs-pop p }
  ; old-joins = claim-joins
  }

++-∷-≢ : ∀ {A : Set} (xs : List A) {y ys} → xs ++ y ∷ ys ≢ []
++-∷-≢ []      ()
++-∷-≢ (_ ∷ _) ()

claimAnyOK : ClaimOK ClaimAny
claimAnyOK = record
  { unpaired0 = λ { any-fresh _ (inj₁ h) → shiftᴸ-0 h
                  ; any-fresh _ (inj₂ h) → shiftᴸ-0 h
                  ; (any-pop (open-any {π₁ = π₁} _ _ _)) e _ →
                      ++-∷-≢ π₁ e }
  ; old-pairs = λ { any-fresh p → pairs-⊕ᴸ p
                  ; (any-pop (open-any _ _ _)) p → pairs-pop p }
  ; old-joins = any-joins
  }

module NoRel
    (ClaimR : ∀ {Δ Δ′ : Ctxᵗ} → World Δ Δ′ → World (underΛ Δ) Δ′ → Set)
    (PushR : Boundary → Term → List ℕ → List ℕ → Set)
    (ok : ClaimOK ClaimR) where
  open Rel ClaimR PushR
  open ClaimOK ok
  open Ex

  NotRel : ∀ {Δ Δ′} → World Δ Δ′ → Term → Term → Set
  NotRel W M M′ = ∀ {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W ∣ γ ⊢ M ⊑ M′ ∶ q)

  Unp : ∀ {Δ Δ′} → World Δ Δ′ → RVar → Set
  Unp W α = ∀ {b} → ¬ Paired W α b

  unp-claim : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁ α}
    → ClaimR W W₁ → Unp W α → Unp W₁ (suc α)
  unp-claim cl u p = u (old-pairs cl p)

  unp-int : ∀ {Δ Δ′ Δᵢ Δ′ᵢ Θ Θ′} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {α}
    → Interior W Θ Θ′ Wᵢ → Unp W α → Unp Wᵢ α
  unp-int {W = W} {Wᵢ} int u (inj₁ h) =
    u (inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (same-ϱᵍ int) h))
  unp-int {W = W} {Wᵢ} int u (inj₂ h) =
    u (inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (same-ϱˡ int) h))

  -- 6a. The bodies: λx:X.λy:Y.x ⊑ λx:X.λy:Y.x JOINS the two X's (the
  -- domain index is `X ⊑ X`, a variable against a variable)
  nl-nl : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ NL ⊑ NL ∶ q → Joins W 1 1 × Δ′ ∋tv 1
  nl-nl (ƛ⊑ƛ {pA = pA} _ (wf-var h) _) = var⊑var pA , h

  l1-nl : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ L1 ⊑ NL ∶ q → Joins W 0 1 × Δ′ ∋tv 1
  l1-nl (Λ⊑ cl _ _ _ _ d _) with nl-nl d
  ... | j , h = old-joins cl j , h

  -- 6b. Left X UNPAIRED (left at position X, rep. var α): the right's
  -- fresh X of +X^α never joins it (`join-fresh`), so the bodies fail
  bxN : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 1 := α → Unp W α → NotRel W NL BX
  bxN hα u (⊑⟪⟫ int _ _ d _ _) with nl-nl d
  ... | j , (β , hβ) = u (proj₁ (join-fresh int hα hβ (inj₂ refl)) j)

  bxL : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 0 := α → Unp W α → NotRel W L1 BX
  bxL hα u (⊑⟪⟫ int _ _ d _ _) with l1-nl d
  ... | j , (β , hβ) = u (proj₁ (join-fresh int hα hβ (inj₂ refl)) j)
  bxL {Δ = Δ} hα u (Λ⊑ cl _ _ _ _ d _) =
    bxN (lookΛ {Δ = Δ} hα) (unp-claim cl u) d

  ciN : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 1 := α → Unp W α → NotRel W NL CI
  ciN hα u (⊑cast d _ _) = bxN hα u d

  ciL : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 0 := α → Unp W α → NotRel W L1 CI
  ciL hα u (⊑cast d _ _)       = bxL hα u d
  ciL {Δ = Δ} hα u (Λ⊑ cl _ _ _ _ d _) =
    ciN (lookΛ {Δ = Δ} hα) (unp-claim cl u) d

  byN : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 1 := α → Unp W α → NotRel W NL BY
  byN hα u (⊑⟪⟫ int _ _ d _ _) = ciN hα (unp-int int u) d

  byL : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 0 := α → Unp W α → NotRel W L1 BY
  byL hα u (⊑⟪⟫ int _ _ d _ _) = ciL hα (unp-int int u) d
  byL {Δ = Δ} hα u (Λ⊑ cl _ _ _ _ d _) =
    byN (lookΛ {Δ = Δ} hα) (unp-claim cl u) d

  rfN : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 1 := α → Unp W α → NotRel W NL R₄
  rfN hα u (⊑cast d _ _) = byN hα u d

  rfL : ∀ {Δ Δ′} {W : World Δ Δ′} {α}
    → Δ ∋ᵗ 0 := α → Unp W α → NotRel W L1 R₄
  rfL hα u (⊑cast d _ _)       = byL hα u d
  rfL {Δ = Δ} hα u (Λ⊑ cl _ _ _ _ d _) =
    rfN (lookΛ {Δ = Δ} hα) (unp-claim cl u) d

  -- 6c. Left X claimed INSIDE +Y^β: then +Y^β's premise relates the
  -- whole KL to CI, at an index `K2 ⊑ ★ → Y → ★` under at most ONE
  -- pending name (only Y is in scope).  That index is empty: opened at
  -- one name it is `∀Y′. c → Y′ → c ⊑ ★ → Y → ★` (needs Y′ ⊑ Y),
  -- unopened it needs the bound Y′ ⊑ Y too.  Whatever the push order.
  ci-trg : ∀ {Δ μ B A} → Δ ∣ μ ⊢ᵖ ci ∶ B ⟹ A → A ≡ ★ ⇒ (` 0 ⇒ ★)
  ci-trg (⊢fun (⊢id _ _) (⊢fun (⊢id _ _) (⊢id _ _))) = refl

  rty-NL : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ NL ⊑ CI ∶ q → A′ ≡ ★ ⇒ (` 0 ⇒ ★)
  rty-NL (⊑cast _ (cast-ty ⊢p _) _) = ci-trg ⊢p

  rty-L1 : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ L1 ⊑ CI ∶ q → A′ ≡ ★ ⇒ (` 0 ⇒ ★)
  rty-L1 (⊑cast _ (cast-ty ⊢p _) _) = ci-trg ⊢p
  rty-L1 (Λ⊑ _ _ _ _ _ d _)          = rty-NL d

  rty-KL : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ KL ⊑ CI ∶ q → A′ ≡ ★ ⇒ (` 0 ⇒ ★)
  rty-KL (⊑cast _ (cast-ty ⊢p _) _) = ci-trg ⊢p
  rty-KL (Λ⊑ _ _ _ _ _ d _)          = rty-L1 d

  idx : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ q → A ⊑ᵂ⟨ W ⟩ A′
  idx {q = q} _ = q

  noIdx : ∀ {μ cs ρ e} → length cs ≤ 1
    → ¬ OpenImp μ cs ρ K2 (★ ⇒ (` e ⇒ ★))
  noIdx {cs = []}    _ (∀⊑ _ _ (∀⊑ _ _ (⇒⊑⇒ _ (⇒⊑⇒ () _))))
  noIdx {cs = _ ∷ []} _ (∀⊑ _ _ (⇒⊑⇒ _ (⇒⊑⇒ () _)))
  noIdx {cs = _ ∷ _ ∷ _} (s≤s ())

  length-map : ∀ {A B : Set} (f : A → B) (xs : List A)
    → length (map f xs) ≡ length xs
  length-map f []       = refl
  length-map f (_ ∷ xs) = cong suc (length-map f xs)

  -- inside +Y^β the right has ONE name, so at most one pending name
  piY : ∀ {Δ′ᵢ} {Wᵢ : World empty Δ′ᵢ}
    → ΔT2 ⊢ⁱ ΘY ⇒ Δ′ᵢ → WfWorld Wᵢ → length (πʷ Wᵢ) ≤ 1
  piY {Wᵢ = Wᵢ} (interior (changes∷ changes[] (step-bind _ _ ins-here))) wf
    with πʷ Wᵢ | wf-pending wf | wf-distinct wf
  ... | []         | _ | _ = z≤n
  ... | _ ∷ []     | _ | _ = s≤s z≤n
  ... | _ ∷ _ ∷ _  | (_ , here , _) ∷ (_ , here , _) ∷ _ | (n ∷ _) ∷ _ =
    ⊥-elim (n refl)

  -- the LEFT types: against NL, BX, CI the left KL has type K2
  NLty : Ty
  NLty = ` 1 ⇒ (` 0 ⇒ ` 1)

  ltyN-NL : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ NL ⊑ NL ∶ q → A ≡ NLty
  ltyN-NL (ƛ⊑ƛ _ _ (ƛ⊑ƛ _ _ (x⊑x (Sʷ Zʷ)))) = refl

  ltyN-BX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ NL ⊑ BX ∶ q → A ≡ NLty
  ltyN-BX (⊑⟪⟫ _ _ _ d _ _) = ltyN-NL d

  ltyN-CI : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ NL ⊑ CI ∶ q → A ≡ NLty
  ltyN-CI (⊑cast d _ _) = ltyN-BX d

  ltyL-NL : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ L1 ⊑ NL ∶ q → A ≡ `∀ NLty
  ltyL-NL (Λ⊑ _ _ _ _ _ d _) = cong `∀ (ltyN-NL d)

  ltyL-BX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ L1 ⊑ BX ∶ q → A ≡ `∀ NLty
  ltyL-BX (⊑⟪⟫ _ _ _ d _ _) = ltyL-NL d
  ltyL-BX (Λ⊑ _ _ _ _ _ d _) = cong `∀ (ltyN-BX d)

  ltyL-CI : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ L1 ⊑ CI ∶ q → A ≡ `∀ NLty
  ltyL-CI (⊑cast d _ _)       = ltyL-BX d
  ltyL-CI (Λ⊑ _ _ _ _ _ d _)  = cong `∀ (ltyN-CI d)

  ltyK-NL : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ KL ⊑ NL ∶ q → A ≡ K2
  ltyK-NL (Λ⊑ _ _ _ _ _ d _) = cong `∀ (ltyL-NL d)

  ltyK-BX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ KL ⊑ BX ∶ q → A ≡ K2
  ltyK-BX (⊑⟪⟫ _ _ _ d _ _)  = ltyK-NL d
  ltyK-BX (Λ⊑ _ _ _ _ _ d _) = cong `∀ (ltyL-BX d)

  ltyK-CI : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ KL ⊑ CI ∶ q → A ≡ K2
  ltyK-CI (⊑cast d _ _)      = ltyK-BX d
  ltyK-CI (Λ⊑ _ _ _ _ _ d _) = cong `∀ (ltyL-CI d)

  noKCI : ∀ {Δ′ᵢ} {W : World empty ΔT2} {Wᵢ : World empty Δ′ᵢ}
      {γ A A′} {q : A ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W [] ΘY Wᵢ → WfWorld Wᵢ → ¬ (Wᵢ ∣ γ ⊢ KL ⊑ CI ∶ q)
  noKCI {Wᵢ = Wᵢ} int wf d =
    noIdx {μ = μʷ Wᵢ} {cs = map (emb (ηᴿʷ Wᵢ)) (πʷ Wᵢ)}
          {ρ = emb (ηᴸʷ Wᵢ)} {e = emb (ηᴿʷ Wᵢ) 0}
          (subst (_≤ 1) (sym (length-map (emb (ηᴿʷ Wᵢ)) (πʷ Wᵢ)))
                 (piY (int-right int) wf))
          (subst₂ (λ X Y → X ⊑ᵂ⟨ Wᵢ ⟩ Y) (ltyK-CI d) (rty-KL d) (idx d))

  -- 6d. THE THEOREM
  topBY : ∀ {W : World empty ΔT2} → πʷ W ≡ [] → NotRel W KL BY
  topBY π0 (⊑⟪⟫ int _ wf d _ _)  = noKCI int wf d
  topBY π0 (Λ⊑ cl _ _ _ _ d _)   = byL here (unpaired0 cl π0) d

  unrelated : ∀ {W : World empty ΔT2} → πʷ W ≡ [] → NotRel W L₀ R₄
  unrelated π0 (⊑cast d _ _)       = topBY π0 d
  unrelated π0 (Λ⊑ cl _ _ _ _ d _) = rfL here (unpaired0 cl π0) d

-- HEAD (D27), fix (a) new-first, fix (c1) any interleaving, fix (b)
-- pop any pending name: (KL, R₄) is unrelated in each
module NoD27  = NoRel Claim    Push  claimOK
module NoFixA = NoRel Claim    PushA claimOK
module NoFixS = NoRel Claim    PushS claimOK
module NoFixB = NoRel ClaimAny Push  claimAnyOK

------------------------------------------------------------------------
-- 7. Fix (c2) alone, with HEAD's marks, REVIVES C4 (PushTypePremise §3,
--    HiddenNames §5): the claimed binder is left-only at X⊑★, and the
--    rejoin keeps that mark (`Interior.mark-left`), so the right's
--    `x⟨X!⟩` passes at X ⊑ ★.  Under D28 the rejoined name's mark is
--    derived from the right rep. var (X⊑X unless permitted), so this
--    derivation's `X ⊑ ★` step has no mark to use (argued, PushOrder.md).
------------------------------------------------------------------------

module C4Revived where
  open FixR
  open Ex using (ΔT1; ΔA; Δ1)
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)

  idX tagX 5★ F L₀c bodyR BdY R₂c : Term
  idX   = ƛ (` 0) ∙ ` 0
  tagX  = ` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩
  5★    = $ 5 ⟨ [] ∣ `ℕ ! ⟩
  F     = Λ idX ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩
  L₀c   = (F · 5★) ⟨ [] ∣ `ℕ ？ 0 ⟩
  bodyR = ƛ (` 0) ∙ tagX
  BdY   = bodyR ⟪ bind 0 0 ∷ [] , reveal 0 (` 0 ⇒ ★) ⟫
  R₂c   = ((BdY ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ ★ ⟩) · 5★) ⟨ [] ∣ `ℕ ？ 0 ⟩

  -- C4's initial programs (PushTypePremise §3): L₀c is the left's
  -- initial cast term; R₂c is the right's state 2 (after Inst, TyBeta)
  R₀c : Term
  R₀c = ((Λ bodyR ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩) · 5★)
          ⟨ [] ∣ `ℕ ？ 0 ⟩

  L₀c-⊢ : empty ∣ [] ⊢ L₀c ⦂ `ℕ
  L₀c-⊢ = tc

  R₀c-⊢ : empty ∣ [] ⊢ R₀c ⦂ `ℕ
  R₀c-⊢ = tc

  R₂c-state : head (drop 2 (evalTerms 30 R₀c-⊢)) ≡ just R₂c
  R₂c-state = refl

  -- the left reaches 5, the right blames
  L₀c-5 : last (evalTerms 30 L₀c-⊢) ≡ just ($ 5)
  L₀c-5 = refl

  R₀c-blame : last (evalTerms 30 R₀c-⊢) ≡ just (blame 0)
  R₀c-blame = refl

  instL-ty : CastTy empty [] (instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)))
               (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instL-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = F})))

  bBdY : BdyTy ΔT1 (bind 0 0 ∷ []) ΔA (` 0 ⇒ ★) (reveal 0 (` 0 ⇒ ★))
           (★ ⇒ ★)
  bBdY = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔT1} {M = BdY}))))

  tagX-ty : CastTy ΔA (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
  tagX-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  W2c : World empty ΔT1
  W2c = world [] []↪ []↪ [] [] []

  W1c : World Δ1 ΔT1      -- after claim-rep: left X paired with αᴿ
  W1c = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] ((0 , 0) ∷ []) []

  Wci : World Δ1 ΔA       -- inside +X^α: X rejoined, still X⊑★
  Wci = world (X⊑★ ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) []

  intc : Interior W1c [] (bind 0 0 ∷ []) Wci
  intc = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  wfc : WfWorld Wci
  wfc = wf-world (both (inj₂ here⇔) joint[])
    (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here r-here
       ; (inj₂ (there⇔ ())) })
    (λ { (_ , here) (_ , here) _ _ _ → refl
       ; (_ , there ()) _ _ _ _ ; _ (_ , there ()) _ _ _ })
    (λ { _ (_ , here) (_ , here) _ _ → refl
       ; _ (_ , there ()) _ _ _ ; _ _ (_ , there ()) _ _ })
    [] []

  -- C4's pair (L₀c, R₂c), related in fix (c2) at HEAD's marks
  c4-related : W2c ∣ [] ⊢ L₀c ⊑ R₂c ∶ ι⊑ι base-ℕ
  c4-related =
    cast⊑cast
      (·⊑·
        (cast⊑cast
          (Λ⊑ (claim-rep r-here (λ { (_ , ()) }) (λ { (_ , ()) }))
            nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (⊑⟪⟫ intc push-none wfc
              (ƛ⊑ƛ {pA = X⊑X} tf tf
                (⊑cast (x⊑x Zʷ) tagX-ty (X⊑★ here)))
              bBdY (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
            (∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))))
          instL-ty
          (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl)
          (⇒⊑⇒ ★⊑★ ★⊑★))
        (cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
          (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★))
      (cast-ty (⊢check g-ℕ) refl) (cast-ty (⊢check g-ℕ) refl)
      (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- 8. Carry-over: a derivation of one instance is one of another when
--    the claims and pushes are included.  HEAD ⊆ (c1), (b), (c2)
--    unconditionally; HEAD ⊆ (a) at pushes with nothing carried or
--    nothing new (`toA`), which is every push of the corpus.
------------------------------------------------------------------------

module Map
    (C₁ C₂ : ∀ {Δ Δ′ : Ctxᵗ} → World Δ Δ′ → World (underΛ Δ) Δ′ → Set)
    (P₁ P₂ : Boundary → Term → List ℕ → List ℕ → Set)
    (fC : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁} → C₁ W W₁ → C₂ W W₁)
    (fP : ∀ {Θ′ M π πᵢ} → P₁ Θ′ M π πᵢ → P₂ Θ′ M π πᵢ) where
  module R₁ = Rel C₁ P₁
  module R₂ = Rel C₂ P₂

  map⊑ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → R₁._∣_⊢_⊑_∶_ W γ M M′ q → R₂._∣_⊢_⊑_∶_ W γ M M′ q
  map⊑ (R₁.x⊑x h)               = R₂.x⊑x h
  map⊑ (R₁.κ⊑κ l p)             = R₂.κ⊑κ l p
  map⊑ (R₁.ƛ⊑ƛ a a′ d)          = R₂.ƛ⊑ƛ a a′ (map⊑ d)
  map⊑ (R₁.·⊑· d e)             = R₂.·⊑· (map⊑ d) (map⊑ e)
  map⊑ (R₁.blame⊑ a t p)        = R₂.blame⊑ a t p
  map⊑ (R₁.cast⊑cast d c c′ q)  = R₂.cast⊑cast (map⊑ d) c c′ q
  map⊑ (R₁.cast⊑ cc d c q)      = R₂.cast⊑ cc (map⊑ d) c q
  map⊑ (R₁.⊑cast d c q)         = R₂.⊑cast (map⊑ d) c q
  map⊑ (R₁.Λ⊑Λ l v v′ d q)      = R₂.Λ⊑Λ l v v′ (map⊑ d) q
  map⊑ (R₁.Λ⊑ cl nv o l v d q)  = R₂.Λ⊑ (fC cl) nv o l v (map⊑ d) q
  map⊑ (R₁.ν⊑ν d a n n′ ci q)   = R₂.ν⊑ν (map⊑ d) a n n′ ci q
  map⊑ (R₁.ν⊑ d a n q)          = R₂.ν⊑ (map⊑ d) a n q
  map⊑ (R₁.⟪⟫⊑⟪⟫ i wf d b b′ ci q) = R₂.⟪⟫⊑⟪⟫ i wf (map⊑ d) b b′ ci q
  map⊑ (R₁.⟪⟫⊑ i bc wf d b q)   = R₂.⟪⟫⊑ i bc wf (map⊑ d) b q
  map⊑ (R₁.⊑⟪⟫ i pu wf d b q)   = R₂.⊑⟪⟫ i (fP pu) wf (map⊑ d) b q

shuffle-++ : ∀ xs ys → Shuffle xs ys (xs ++ ys)
shuffle-++ []       []       = sh-[]
shuffle-++ []       (y ∷ ys) = sh-r (shuffle-++ [] ys)
shuffle-++ (x ∷ xs) ys       = sh-l (shuffle-++ xs ys)

push→S : ∀ {Θ′ M π πᵢ} → Push Θ′ M π πᵢ → PushS Θ′ M π πᵢ
push→S (push {π′ = π′} {new = nw} ca fr v) =
  pushS ca fr v (shuffle-++ π′ nw)

claim→any : ∀ {Δ Δ′} {W : World Δ Δ′} {W₁} → Claim W W₁ → ClaimAny W W₁
claim→any claim-fresh = any-fresh
claim→any (claim-pop (open1 j h r)) = any-pop (open-any {π₁ = []} j h r)

module ToR = Map Claim ClaimRep Push Push claim-old (λ p → p)
module ToS = Map Claim Claim Push PushS (λ c → c) push→S
module ToB = Map Claim ClaimAny Push Push claim→any (λ p → p)

-- (a): a push with nothing carried or nothing new is order-free
++-[] : ∀ (xs : List ℕ) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

toA : ∀ {Θ′ M π π′ nw}
  → Carried Θ′ π π′ → All (Fresh Θ′) nw → (nw ≡ [] ⊎ Value M)
  → π′ ≡ [] ⊎ nw ≡ []
  → PushA Θ′ M π (π′ ++ nw)
toA {nw = nw} ca fr v (inj₁ refl) =
  subst (PushA _ _ _) (++-[] nw) (pushA ca fr v)
toA {π′ = π′} ca [] v (inj₂ refl) =
  subst (PushA _ _ _) (sym (++-[] π′)) (pushA ca [] v)

-- the example's own pushes carry over: state 2 in (c1), (b), (c2)
st2-S = ToS.map⊑ PosD27.st2
st2-B = ToB.map⊑ PosD27.st2
st2-R = ToR.map⊑ PosD27.st2

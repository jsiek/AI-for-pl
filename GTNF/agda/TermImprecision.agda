module TermImprecision where

-- File Charter:
--   * CAST-TERM IMPRECISION `W ∣ γ ⊢ M ⊑ M′ ∶[ O ] p` (GTNF/design.md
--     §10, with D12-D16, D28, D29 and D31), over the worlds `World` of
--     ImprecisionWorld.  M is the MORE precise (left) term, typed on
--     `Δ`; M′ the right one, typed on `Δ′`; `p : A ⊑ᵂ⟨ W ⟩[ O ] A′`
--     relates their types, the left type opened at the SLOTS O
--     (ImprecisionWorld §4; GTSFImp's index shape, `_∣_⊢²_⊑_∶_`).
--     `W ∣ γ ⊢ M ⊑ M′ ∶ p` is the O = [] case, the form of every
--     top-level statement.  §1 the side-premise bundles `Lit`,
--     `CastTy`, `NuTy`, `BdyTy` (each is exactly the premises of the
--     corresponding typing rule of Terms, minus the subterm), with their
--     reassembly into a typing; §2 the slot side relations (`Bind`,
--     `CastOpen`, `BdyOpen`, `Carried`, `NewSlot`, `Fill`, `Push`) and
--     the relation.
--   * THE INDEX CARRIES THE OPENINGS (design.md D31, adopted
--     2026-10-09; checked first as proof/DGG/notes/D28pD30.agda).  A
--     slot `opn k` opens the next left ∀ at the right type variable k;
--     a slot `skp` skips it (left-only, X⊑★).  Only `⊑⟪⟫` creates slots
--     (`Push`: openings of type variables its boundary introduces, and
--     skips, only for a left gen-cast value; a new opening may FILL a
--     carried skip); only `Λ⊑` consumes one by changing the world
--     (`Bind`, `b-join`: the left binder joins the opening, `Join1`);
--     `cast⊑` passes or consumes them along the coercion's binder
--     layers, with no world change (`CastOpen`: a ∀ layer passes its
--     slot to the cast value, a gen layer consumes its slot); `⟪⟫⊑`
--     passes them into a ∀-boundary (`BdyOpen`).  `⊑cast` keeps them;
--     every other rule is at O = [].
--   * PERMISSIONS ARE CHOSEN AT JOINING BOUNDARIES (design.md D31;
--     history: D28's grants at right checks).  Each boundary rule may add
--     to κ, for its interior only, the right rep. vars K of type
--     variables it JOINS (`All (JoinRep …) K`; the premise world is
--     `Wᵢ +κ K`), and pays with its interior index read at Wᵢ, WITHOUT
--     K (`pay`, "the join pays").  No cast rule changes the world.
--     - R1′: `⟪⟫⊑` takes `All (UnbindOK W A) Θ`, A its exterior type:
--       a left unbind whose rep. var's type variable occurs in A (a
--       seal) needs α unpermitted (R1, counterexample C5); a pure hide
--       needs nothing (P4h).
--     - R2 is on the ★ conversion clauses (ConversionImprecision),
--       read in the EXTERIOR conversion world (unchanged by K).
--   * THE RULES, design.md §10, one constructor each: congruence `x⊑x`,
--     `κ⊑κ` (the literals `$ n`, `true`, `false`, one rule through
--     `Lit`), `ƛ⊑ƛ`, `·⊑·`; `blame⊑`; `cast⊑cast`, `cast⊑`, `⊑cast`;
--     `Λ⊑Λ`, `Λ⊑`; `ν⊑ν`, `ν⊑`; `⟪⟫⊑⟪⟫`, `⟪⟫⊑`, `⊑⟪⟫`.  15 rules:
--     GTSFImp's 17 minus `⊕⊑⊕` (GTNF has no binary operators yet) and
--     minus `∀⊑⟪+⟫` (removed by D26).
--   * CLAIM-REP (design.md D29).  `Λ⊑`'s `Bind` has a third case,
--     `b-rep`: with no slot, the left binder pairs its abstract rep. var
--     lexically with an unnamed right ★ rep. var β (`W ⊕ᴸ⇔ β`); the
--     right boundary that later binds a type variable to β rejoins it
--     by `Interior.join-fresh` (D25).  It relates a left ∀-value to a
--     right value whose boundaries instantiate in the opposite order
--     (H1).
--   * COERCIONS ARE NOT COMPARED.  Each is typed on its own side under
--     the mode environment its cast carries (`CastTy`, as `⊢cast`).
--     In contrast, D17 compares the two conversions of `ν⊑ν` and
--     `⟪⟫⊑⟪⟫` structurally (`NuConversionImp`, `BdyConversionImp`, in
--     the exterior world).  One-sided rules still type their sole
--     conversion but have no conversion-imprecision premise.
--   * EXPLICIT CONCLUSION PROOFS.  As in GTSFImp, a rule whose
--     conclusion type is not built from its premises' proofs by a
--     constructor takes that proof `q` as an argument: `emb` under a
--     binder is only extensionally `extᵗ`, so `∀⊑∀`-style proofs cannot
--     be computed from the premise's.
--   * TYPING SIDE PREMISES.  Both typings `Δ ∣ lhs γ ⊢ M ⦂ A` and
--     `Δ′ ∣ rhs γ ⊢ M′ ⦂ A′` follow from a derivation
--     (proof/DGG/ImprecisionTyping), at the ACTUAL left type A whatever
--     the slots.  The premises that serve that purpose only:
--     - `ƛ⊑ƛ`: the two annotations' `_⊢ᵗ_` (for `⊢ƛ`);
--     - `blame⊑`: `Δ ⊢ᵗ A` (for `⊢blame`) and the whole right typing;
--     - the cast rules: `CastTy` (for `⊢cast`);
--     - `Λ⊑Λ`, `Λ⊑`: `Value` of the bodies (for `⊢Λ`'s value
--       restriction);
--     - `ν⊑ν`, `ν⊑`: `NuTy` (for `⊢ν`);
--     - the boundary rules: `BdyTy` (for `boundary`).
--   * DE BRUIJN READINGS.
--     - `ν X:=A.(L X)⟨c⟩` is Terms' `ν A · L ⟨ c ⟩`.
--     - an opening's "β:=★" is `Δ′ ∋rep β := ★` (`OpeningOK`); the join
--       of type variable 0 of `W ⊕ʳ^ β` has premise world `W ⊕⁺^ β`
--       (`join-⊕`).
--   * DEVIATION from design.md §10 (also in the report):
--     - `Λ⊑` does not repeat the right term's typing (GTSFImp's `Λ⊑²`
--       does): the premise already types M′ on the unchanged `Δ′` and
--       `rhs γ′ = rhs γ`.
--   * HISTORY (design.md §C12).  D26 replaced GTSFImp's `∀⊑⟪+⟫` by
--     openings of `⊑⟪⟫`; D27 kept them as a pending list in the world,
--     popped by `Λ⊑` and gen casts; D28 added grants (`⊑cast` permitted
--     β under a right check of β's type variable); D31 replaced both:
--     the openings are slots of the index, and permissions are chosen
--     at joining boundaries.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.AllPairs using (AllPairs; [])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Types using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀)
open import Ctx
open import Conversion using (Conv; _⊢_∶_⇝_; ⌞_⌟; Mid; `∀)
open import Boundary
  using (Boundary; Change; bind; BoundaryWf; TyBetaBoundary; Fresh; toExt)
open import Coercion
  using (Coercion; ModeEnv; _∣_⊢ᵖ_∶_⟹_; NonVar; _∈ᵗ_; ∀ᵖ_; genᵖ_)
open import Terms
open import Imprecision using (⇒⊑⇒)
open import ImprecisionWorld
open import ConversionImprecision using (ConvImp)

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
-- 2. Slots (design.md D31) and the relation
------------------------------------------------------------------------

-- `Λ⊑`'s binder (conclusion slots, premise slots): fresh and left-only
-- (no slot); the JOIN of the next opening k (`Join1`, ImprecisionWorld
-- §5: the left binder joins the right type variable k; its abstract
-- rep. var is paired lexically with k's β:=★); or (design.md D29)
-- claim-rep, a fresh left-only binder whose abstract rep. var claims an
-- unnamed right ★ rep. var β (`W ⊕ᴸ⇔ β`, no slot): no right type
-- variable in scope is bound to β and β has no left partner bound to a
-- type variable; the right boundary that later binds a type variable to
-- β rejoins the binder (`Interior.join-fresh`, D25)
data Bind {Δ Δ′ : Ctxᵗ}
    : World Δ Δ′ → List Slot → World (underΛ Δ) Δ′ → List Slot → Set where
  b-fresh : ∀ {W} → Bind W [] (W ⊕ᴸ) []
  b-join  : ∀ {W W₁ k O} → Join1 W k W₁ → Bind W (opn k ∷ O) W₁ O
  b-rep   : ∀ {W β}
    → Δ′ ∋rep β := ★
    → ¬ (names Δ′ ∋ᵅ β)
    → NoNamedPartner W β
    → Bind W [] (W ⊕ᴸ⇔ β) []

-- `cast⊑`'s slots (conclusion, premise), along the coercion's binder
-- layers: a `∀ᵖ` layer passes its slot to the cast value, a `genᵖ`
-- layer consumes its slot (the value under a gen does not see the
-- binder); every other cast has none.  Not `drop k O` (design.md D31:
-- for `∀Y. gen Z. p` the slot of the ∀ layer must reach the value).
data CastOpen (M : Term) : Coercion → List Slot → List Slot → Set where
  co-plain : ∀ {c} → CastOpen M c [] []
  co-∀     : ∀ {c s O Oₚ} → Value M → CastOpen M c O Oₚ
    → CastOpen M (∀ᵖ c) (s ∷ O) (s ∷ Oₚ)
  co-gen   : ∀ {c s O Oₚ} → Value M → CastOpen M c O Oₚ
    → CastOpen M (genᵖ c) (s ∷ O) Oₚ

-- `ForallConv c O`: c has a `∀` layer for each slot of O
data ForallConv : Conv → List Slot → Set where
  fc-[] : ∀ {c} → ForallConv c []
  fc-∷  : ∀ {s c O} → ForallConv s O → ForallConv ⌞ `∀ s ⌟ (c ∷ O)

-- `⟪⟫⊑`'s slots pass into the left boundary unchanged (they are RIGHT
-- positions, and the right does not move) when the boundary is a
-- ∀-value (as InstX's `inst-⟪⟫`)
data BdyOpen (M : Term) (c : Conv) : List Slot → Set where
  bo-plain : BdyOpen M c []
  bo-∀     : ∀ {s O} → Simple M → ForallConv c (s ∷ O) → BdyOpen M c (s ∷ O)

-- `⊑⟪⟫`: the carried slots (an opening continues through Θ′; k′ is its
-- interior position; a skip continues) ...
data Carried (Θ′ : Boundary) : List Slot → List Slot → Set where
  ca-[]  : Carried Θ′ [] []
  ca-opn : ∀ {k k′ O O′} → toExt Θ′ k′ ≡ just k → Carried Θ′ O O′
    → Carried Θ′ (opn k ∷ O) (opn k′ ∷ O′)
  ca-skp : ∀ {O O′} → Carried Θ′ O O′ → Carried Θ′ (skp ∷ O) (skp ∷ O′)

-- ... the new slots: an opening of a type variable Θ′ introduces, or a
-- skip, only for a left gen-cast value (a value under a cast whose
-- coercion has a gen layer under its ∀ layers) ...
data GenLayer : Coercion → Set where
  gl-gen : ∀ {c} → GenLayer (genᵖ c)
  gl-∀   : ∀ {c} → GenLayer c → GenLayer (∀ᵖ c)

data GenCastValue : Term → Set where
  gcv : ∀ {V μ c} → Value V → GenLayer c → GenCastValue (V ⟨ μ ∣ c ⟩)

data NewSlot (Θ′ : Boundary) (M : Term) : Slot → Set where
  ns-opn : ∀ {k} → Fresh Θ′ k → NewSlot Θ′ M (opn k)
  ns-skp : GenCastValue M → NewSlot Θ′ M skp

-- ... merged: the carried slots keep their order; a new opening may
-- FILL a carried skip (left to right); the remaining new slots go last
-- (`Fill O′ N Oᵢ`, "fill O′ with N into Oᵢ")
data Fill : List Slot → List Slot → List Slot → Set where
  f-end  : ∀ {N} → Fill [] N N
  f-keep : ∀ {s O N Oᵢ} → Fill O N Oᵢ → Fill (s ∷ O) N (s ∷ Oᵢ)
  f-fill : ∀ {k O N Oᵢ} → Fill O N Oᵢ
    → Fill (skp ∷ O) (opn k ∷ N) (opn k ∷ Oᵢ)

-- THE PUSH of `⊑⟪⟫` (conclusion slots O, new slots N, interior slots
-- Oᵢ); new slots need a left value
data Push (Θ′ : Boundary) (M : Term) (O : List Slot)
    : List Slot → List Slot → Set where
  push : ∀ {O′ N Oᵢ}
    → Carried Θ′ O O′
    → Fill O′ N Oᵢ
    → All (NewSlot Θ′ M) N
    → (N ≡ [] ⊎ Value M)
    → Push Θ′ M O N Oᵢ

infix 3 _∣_⊢_⊑_∶[_]_

-- The relation is INDEXED by the world (not parameterized) and by the
-- slots O of its index.
data _∣_⊢_⊑_∶[_]_ {Δ Δ′ : Ctxᵗ}
    : (W : World Δ Δ′) → CtxImp W → Term → Term → (O : List Slot)
    → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩[ O ] A′ → Set where

  ----------------------------------------------------------------------
  -- Congruence (GTSFImp x⊑x², κ⊑κ², ƛ⊑ƛ², ·⊑·²); no slot

  x⊑x : ∀ {W γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
      --------------------------------
    → W ∣ γ ⊢ ` x ⊑ ` x ∶[ [] ] p

  κ⊑κ : ∀ {W γ k ι}
    → Lit k ι
    → (p : ι ⊑ᵂ⟨ W ⟩ ι)
      --------------------------------
    → W ∣ γ ⊢ k ⊑ k ∶[ [] ] p

  ƛ⊑ƛ : ∀ {W γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶[ [] ] pB
      ---------------------------------------------
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶[ [] ] ⇒⊑⇒ pA pB

  ·⊑· : ∀ {W γ L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶[ [] ] ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶[ [] ] pA
      ---------------------------------------------
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶[ [] ] pB

  ----------------------------------------------------------------------
  -- Blame (GTSFImp blame⊑²); no slot (under one the left is a value)

  blame⊑ : ∀ {W γ ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶[ [] ] p

  ----------------------------------------------------------------------
  -- Casts (GTSFImp cast⊑cast², cast⊑², ⊑cast²); no cast rule changes
  -- the world

  cast⊑cast : ∀ {W γ M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶[ [] ] p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶[ [] ] q

  -- the premise slots follow the coercion's binder layers (`CastOpen`)
  cast⊑ : ∀ {W γ M M′ μ c B A A′ O Oₚ} {p : B ⊑ᵂ⟨ W ⟩[ Oₚ ] A′}
    → CastOpen M c O Oₚ
    → W ∣ γ ⊢ M ⊑ M′ ∶[ Oₚ ] p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂ⟨ W ⟩[ O ] A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶[ O ] q

  -- GTSFImp's plain rule; keeps the slots
  ⊑cast : ∀ {W γ M M′ μ′ c′ A B′ A′ O} {p : A ⊑ᵂ⟨ W ⟩[ O ] B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶[ O ] p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩[ O ] A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶[ O ] q

  ----------------------------------------------------------------------
  -- Type abstraction (GTSFImp Λ⊑Λ², Λ⊑²)

  Λ⊑Λ : ∀ {W γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕² ⟩ A′}
    → LiftCtx γ γ′
    → Value V
    → Value V′
    → W ⊕² ∣ γ′ ⊢ V ⊑ V′ ∶[ [] ] r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶[ [] ] q

  -- the right term crosses the left binder unweakened; the binder is
  -- fresh, the JOIN of the next opening (the only consumption of a slot
  -- that changes the world: a term binder), or claim-rep (`Bind`)
  Λ⊑ : ∀ {W W₁ γ γ′ V M′ A B′ O O₁} {r : A ⊑ᵂ⟨ W₁ ⟩[ O₁ ] B′}
    → Bind W O W₁ O₁
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶[ O₁ ] r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩[ O ] B′)
      ---------------------------------------------
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶[ O ] q

  ----------------------------------------------------------------------
  -- Instantiation (GTSFImp •⊑•², •⊑²); there is no ⊑ν

  ν⊑ν : ∀ {W γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶[ [] ] r
    → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      ---------------------------------------------
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶[ [] ] q

  ν⊑ : ∀ {W γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶[ [] ] r
    → A ⊑ᵂ⟨ W ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      ---------------------------------------------
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶[ [] ] q

  ----------------------------------------------------------------------
  -- Boundaries (these replace GTSFImp's reveal/conceal rules).  The
  -- interior is term-closed, so each premise has γ = [].  Each rule may
  -- PERMIT, for its interior only, the right rep. vars K of type
  -- variables it joins (`JoinRep`; premise world `Wᵢ +κ K`, well formed),
  -- and PAYS with its interior index read at Wᵢ, without K (design.md
  -- D31).

  ⟪⟫⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {K}
      {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ +κ K ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → All (JoinRep Wᵢ Θ Θ′ []) K
    → WfWorld (Wᵢ +κ K)
    → (pay : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ ∶[ [] ] r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶[ [] ] q

  -- the slots pass into a ∀-boundary (`BdyOpen`); R1′: every left
  -- unbind entry of Θ whose type variable occurs in the exterior type A
  -- has an unpermitted rep. var (`UnbindOK W A`)
  ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′} {K}
      {γ M M′ Θ c Aᵢ A A′ O} {r : Aᵢ ⊑ᵂ⟨ Wᵢ +κ K ⟩[ O ] A′}
    → Interior W Θ [] Wᵢ
    → All (UnbindOK W A) Θ
    → BdyOpen M c O
    → All (JoinRep Wᵢ Θ [] []) K
    → WfWorld (Wᵢ +κ K)
    → (pay : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩[ O ] A′)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ ∶[ O ] r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂ⟨ W ⟩[ O ] A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶[ O ] q

  -- the only rule that creates slots: carry the slots through Θ′, add
  -- the new slots N (`Push`); the interior slots are well formed
  ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ} {K}
      {γ M M′ Θ′ c′ A A′ᵢ A′ O N Oᵢ} {r : A ⊑ᵂ⟨ Wᵢ +κ K ⟩[ Oᵢ ] A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → Push Θ′ M O N Oᵢ
    → All (SlotOK Wᵢ) Oᵢ
    → AllPairs SlotNe Oᵢ
    → All (JoinRep Wᵢ [] Θ′ N) K
    → WfWorld (Wᵢ +κ K)
    → (pay : A ⊑ᵂ⟨ Wᵢ ⟩[ Oᵢ ] A′ᵢ)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ ∶[ Oᵢ ] r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩[ O ] A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶[ O ] q

-- THE TOP-LEVEL FORM: no slot
infix 3 _∣_⊢_⊑_∶_
_∣_⊢_⊑_∶_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
  → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set
W ∣ γ ⊢ M ⊑ M′ ∶ p = W ∣ γ ⊢ M ⊑ M′ ∶[ [] ] p

-- The relation with its two types explicit.  `_⊑ᵂ⟨_⟩[_]_` (OpenO)
-- cannot be inverted for A, A′, so a statement over them gives A and A′
-- this way.
infix 3 _∣_⊢_⊑_∶⟨_,_⟩[_]_ _∣_⊢_⊑_∶⟨_,_⟩_
_∣_⊢_⊑_∶⟨_,_⟩[_]_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
  → (A A′ : Ty) → (O : List Slot) → A ⊑ᵂ⟨ W ⟩[ O ] A′ → Set
W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p = _∣_⊢_⊑_∶[_]_ W γ M M′ O {A} {A′} p

_∣_⊢_⊑_∶⟨_,_⟩_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
  → (A A′ : Ty) → A ⊑ᵂ⟨ W ⟩ A′ → Set
W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p = _∣_⊢_⊑_∶[_]_ W γ M M′ [] {A} {A′} p

-- the push of nothing: the plain right-only boundary
push-none : ∀ {Θ′ M} → Push Θ′ M [] [] []
push-none = push ca-[] f-end [] (inj₁ refl)

-- `⊑⟪⟫` with no slot and no permission (the interior index is the
-- payment)
⊑⟪⟫₀ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ} {γ M M′ Θ′ c′ A A′ᵢ A′}
    {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
  → Interior W [] Θ′ Wᵢ
  → WfWorld Wᵢ
  → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q
⊑⟪⟫₀ {r = r} I wf d b q = ⊑⟪⟫ I push-none [] [] [] wf r d b q

-- `⟪⟫⊑` with no slot and no permission
⟪⟫⊑₀ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′} {γ M M′ Θ c Aᵢ A A′}
    {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
  → Interior W Θ [] Wᵢ
  → All (UnbindOK W A) Θ
  → WfWorld Wᵢ
  → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q
⟪⟫⊑₀ {r = r} I ok wf d b q = ⟪⟫⊑ I ok bo-plain [] wf r d b q

-- `⟪⟫⊑⟪⟫` with no permission
⟪⟫⊑⟪⟫₀ : ∀ {W : World Δ Δ′} {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
    {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
  → Interior W Θ Θ′ Wᵢ
  → WfWorld Wᵢ
  → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
  → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q
⟪⟫⊑⟪⟫₀ {r = r} I wf d b b′ bc q = ⟪⟫⊑⟪⟫ I [] wf r d b b′ bc q

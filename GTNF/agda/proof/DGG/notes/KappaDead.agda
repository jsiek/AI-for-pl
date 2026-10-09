module proof.DGG.notes.KappaDead where

-- File Charter:
--   * QUESTION (Jeremy, 2026-10-09).  D31 lets a joining boundary
--     permit right rep. vars K for its interior, so the induction
--     hypotheses of Sim/SimBack/CatchupRight/CatchupLeft run at worlds
--     with κ ≠ [].  Do the counterexamples C1, C2, C3, C4, C4g, proved
--     unrelated at κʷ ≡ [] (examples/TermImprecisionPermissionExamples),
--     stay dead at ANY κ?  Notes: KappaDead.md.  LEFT is MORE precise.
--   * ANSWER (mechanized, no postulates, no holes):
--       C3.c3-dead          C3 is DEAD in every world over its contexts,
--                           any κ, any slots (R2 against the joined
--                           mark; types alone on the one-sided orders)
--       C1.c1-at-κ          C1 is RELATED at κ = [α] (left-first route)
--       C2.c2-at-κ          C2 is RELATED at κ = [α] (P4 B4's S ⊑ J)
--       C4.c4-at-κ,         C4 and C4g are RELATED at κ = [αᴿ] (open,
--       C4.c4g-at-κ         join, peel; αᴿ has no left partner at all)
--     all in well-formed worlds (`c1-world-wf`, `C4.wf-V4`, `V⁰-wf`).
--     In these worlds the right store has one rep. var, so every
--     well-formed κ is [] or permits it (`Worlds.κ-only0`): "any κ" and
--     "the relevant rep. var permitted from the start" coincide.
--   * THE WORLD ARISES (§6, §7): a matched `+Y^α ∥ +Y^α` with body type
--     ℕ joins Y and permits α, paying ℕ ⊑ ℕ; a matched hide
--     `−Y^α ∥ −Y^α` keeps κ.  `WrapC1.wrapped-c1`, `WrapC2.wrapped-c2`,
--     `WrapC4.wrapped-c4` relate the wrapped pairs at a TOP-LEVEL
--     world (κ = [], `Wrap.top-wf`); the wrapped right blames, the
--     wrapped left answers 5 (`WR-blames`, `WL-answers`,
--     `WrapC1.WL-never-blames`), and no left reduct is related to any
--     right reduct (`RefuteC1.unrelated`): SimBack AS STATED in
--     proof/DGG/SimBackDef (WfWorld, κʷ W ≡ []) is refuted by
--     wrapped C1.  Whether the wrapped state is reachable from related
--     SOURCES is not settled here (KappaDead.md §4).
--   * THE INVARIANT (§8): `PermitNamed W O`, every permitted β has a
--     left partner bound to a left type variable in scope, or is opened
--     by a slot.  It forces κ = [] in all four counterexample worlds
--     (`c1-world-bad`, `c2-world-bad`, `c4-world-bad`), holds where P4
--     uses its permission (`p4-shape`), and the HEAD rules break it at
--     the wrapper's matched hide (`wrapper-breaks`): boundaries must
--     revoke what they leave without a named left partner.
--   * PROVENANCE.  §0 is a COPY of HEAD 8fe66241's TermImprecision
--     (§1-§2 verbatim) and HEAD's `JoinRep` (ImprecisionWorld §9): the
--     working tree's TermImprecision/ImprecisionWorld are being changed
--     concurrently (D32: `Revoke`, `jr-rebind`).  World, marks,
--     Interior, WfWorld and ConvImp are imported (unchanged from HEAD).
--     Every D31 derivation here is also a D32 derivation (`rv-none`),
--     so the positive results carry over to D32 as drafted.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld hiding (JoinRep)
open import ConversionImprecision

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ : Ctxᵗ
    Γ : Ctx

------------------------------------------------------------------------
-- 0. HEAD's JoinRep (ImprecisionWorld §9, D31) and HEAD's relation
-- (TermImprecision §1-§2), copied
------------------------------------------------------------------------

data JoinRep {Δᵢ Δ′ᵢ : Ctxᵗ} (Wᵢ : World Δᵢ Δ′ᵢ) (Θ Θ′ : Boundary)
    (N : List Slot) (β : RVar) : Set where
  jr-join : ∀ {X X′}
    → Δᵢ ∋tv X → Δ′ᵢ ∋ᵗ X′ := β
    → Fresh Θ X ⊎ Fresh Θ′ X′
    → Joins Wᵢ X X′
    → JoinRep Wᵢ Θ Θ′ N β
  jr-open : ∀ {k} → N ∋ᵒ k → Δ′ᵢ ∋ᵗ k := β → JoinRep Wᵢ Θ Θ′ N β

------------------------------------------------------------------------
-- 0a. (TermImprecision §1) Side-premise bundles
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
-- 0b. (TermImprecision §2) Slots (design.md D31) and the relation
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

------------------------------------------------------------------------
-- 1. Worlds with one store rep. var per side (payload R, paired
-- globally), at ANY permissions κ.  A well-formed κ lists only right
-- rep. vars (`wf-permits`), and the right store has the one rep. var 0,
-- so every κ is [], or permits 0 (`permit 0 κ ≡ X⊑★` iff κ ≢ []): in
-- these worlds "any κ" and "the relevant right rep. var permitted
-- from the start" (Jeremy's question 2) are the same case.
------------------------------------------------------------------------

open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms)
open import proof.ImprecisionWorld using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])

nth : List Term → ℕ → Term
nth []       _       = $ 0
nth (x ∷ xs) zero    = x
nth (x ∷ xs) (suc n) = nth xs n

ι : ∀ {μ} → μ ⊢ `ℕ ⊑ `ℕ
ι = ι⊑ι base-ℕ

Θ₀ unb₀ : Boundary
Θ₀   = bind 0 0 ∷ []
unb₀ = unbind 0 0 ∷ []

ϱ₀ : RepRel
ϱ₀ = (0 , 0) ∷ []

module Worlds (R : Ty) (Ξ : RepCtx) (r0 : Ξ ∋ʳ 0 := bindR R)
  (v0 : Ξ ∋ʳ 0) (only0 : ∀ {α} → Ξ ∋ʳ α → α ≡ 0)
  (rimp : ∀ {Δ Δ′} {W : World Δ Δ′} → [] ⊢ R ⊑ᴿ⟨ W ⟩ R) where

  Δ₀ Δ₁ : Ctxᵗ
  Δ₀ = Ξ ∣ []
  Δ₁ = Ξ ∣ (0 ∷ [])

  -- no type variable
  V⁰ : List RVar → World Δ₀ Δ₀
  V⁰ κ = world 0 []↪ []↪ ϱ₀ [] κ

  -- X both-sided (its mark is permit 0 κ)
  V² : List RVar → World Δ₁ Δ₁
  V² κ = world 1 (keep []↪) (keep []↪) ϱ₀ [] κ

  -- X left-only (X⊑★ whatever κ)
  Vᴸ : List RVar → World Δ₁ Δ₀
  Vᴸ κ = world 1 (keep []↪) (skip []↪) ϱ₀ [] κ

  agree : ∀ {ns ns′ n} {η : ns ↪ n} {η′ : ns′ ↪ n} {κ α β}
    → Paired (world {Ξ ∣ ns} {Ξ ∣ ns′} n η η′ ϱ₀ [] κ) α β
    → Agree (world {Ξ ∣ ns} {Ξ ∣ ns′} n η η′ ϱ₀ [] κ) α β
  agree (inj₁ here⇔)         = rep-rep r0 r0 rimp
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

  permits : (κ : List RVar) → All (λ β → β ≡ 0) κ → All (Ξ ∋ʳ_) κ
  permits [] [] = []
  permits (_ ∷ κ) (refl ∷ ps) = v0 ∷ permits κ ps

  V⁰-wf : ∀ {κ} → All (λ β → β ≡ 0) κ → WfWorld (V⁰ κ)
  V⁰-wf {κ} ps = wf-world joint[] agree (namedᴸ-≤1 (V⁰ κ) ≤1-[])
    (namedᴿ-≤1 (V⁰ κ) ≤1-[]) (permits κ ps)

  V²-wf : ∀ {κ} → All (λ β → β ≡ 0) κ → WfWorld (V² κ)
  V²-wf {κ} ps = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 (V² κ) ≤1-∷[]) (namedᴿ-≤1 (V² κ) ≤1-∷[]) (permits κ ps)

  Vᴸ-wf : ∀ {κ} → All (λ β → β ≡ 0) κ → WfWorld (Vᴸ κ)
  Vᴸ-wf {κ} ps = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 (Vᴸ κ) ≤1-∷[]) (namedᴿ-≤1 (Vᴸ κ) ≤1-[]) (permits κ ps)

  -- EVERY well-formed κ of these worlds lists only rep. var 0
  κ-only0 : ∀ {ns ns′ n} {η : ns ↪ n} {η′ : ns′ ↪ n} {ϱᵍ ϱˡ κ}
    → WfWorld (world {Ξ ∣ ns} {Ξ ∣ ns′} n η η′ ϱᵍ ϱˡ κ)
    → All (λ β → β ≡ 0) κ
  κ-only0 wf = go (wf-permits wf)
    where
    go : ∀ {κ} → All (Ξ ∋ʳ_) κ → All (λ β → β ≡ 0) κ
    go [] = []
    go (h ∷ ps) = only0 h ∷ go ps

  -- the interiors
  int-bind² : ∀ {κ} → Interior (V⁰ κ) Θ₀ Θ₀ (V² κ)
  int-bind² = record
    { int-left   = interior (changes∷ changes[]
                     (step-bind v0 fresh[] ins-here))
    ; int-right  = interior (changes∷ changes[]
                     (step-bind v0 fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  conv-bind² : ∀ {κ} → ConversionInterior (V⁰ κ) Θ₀ Θ₀ (V² κ)
  conv-bind² = record
    { conv-left       =
        conversion (conv-bind v0 conv[] fresh[] ins-here)
    ; conv-right      =
        conversion (conv-bind v0 conv[] fresh[] ins-here)
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

  -- the LEFT's +X^0 alone: X is left-only (the right has no type
  -- variable to rejoin)
  int-bindᴸ : ∀ {κ} → Interior (V⁰ κ) Θ₀ [] (Vᴸ κ)
  int-bindᴸ = record
    { int-left   = interior (changes∷ changes[]
                     (step-bind v0 fresh[] ins-here))
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) (_ , ()) _ _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { _ () _ }
    }

  -- the RIGHT's +X^0 alone: the left's X rejoins through ϱ (D25)
  int-bindᴿ : ∀ {κ} → Interior (Vᴸ κ) [] Θ₀ (V² κ)
  int-bindᴿ = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind v0 fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  -- the RIGHT's −X^0 alone: X goes left-only; κ passes through
  int-unbindᴿ : ∀ {κ} → Interior (V² κ) [] unb₀ (Vᴸ κ)
  int-unbindᴿ = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind v0 del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    }

  -- matched −X^0 ∥ −X^0 (the seals, or matched hides)
  int-unb² : ∀ {κ} → Interior (V² κ) unb₀ unb₀ (V⁰ κ)
  int-unb² = record
    { int-left   = interior (changes∷ changes[]
                     (step-unbind v0 del-here fresh[]))
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind v0 del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  conv-unb² : ∀ {κ} → ConversionInterior (V² κ) unb₀ unb₀ (V² κ)
  conv-unb² = record
    { conv-left       = conversion (conv-unbind v0 conv[])
    ; conv-right      = conversion (conv-unbind v0 conv[])
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

ΔR ΔRᵢ ΔL ΔLᵢ : Ctxᵗ
ΔR  = allocate ★ empty
ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])
ΔL  = allocate `ℕ empty
ΔLᵢ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])

only0 : ∀ {R α} → (bindR R ∷ []) ∋ʳ α → α ≡ 0
only0 (_ , here) = refl
only0 (_ , there ())

-- typing side premises, read off `tc`
ct : ∀ {Δ₂ M μ c A} → Δ₂ ∣ [] ⊢ M ⟨ μ ∣ c ⟩ ⦂ A
  → Σ[ B ∈ Ty ] CastTy Δ₂ μ c B A
ct ⊢M = _ , proj₂ (proj₂ (cast-inv ⊢M))

bt : ∀ {Δ₂ M Θ c A} → Δ₂ ∣ [] ⊢ M ⟪ Θ , c ⟫ ⦂ A
  → Σ[ Δ₃ ∈ Ctxᵗ ] Σ[ B ∈ Ty ] BdyTy Δ₂ Θ Δ₃ B c A
bt ⊢M with ⟪⟫-inv ⊢M
... | Δ₃ , B , _ , b = Δ₃ , B , b

κ₀ : List RVar
κ₀ = 0 ∷ []

p₀ : All (λ β → β ≡ 0) κ₀
p₀ = refl ∷ []

module W★ = Worlds ★ (bindR ★ ∷ []) r-here (_ , here) only0 ★⊑★
module Wℕ = Worlds `ℕ (bindR `ℕ ∷ []) r-here (_ , here) only0
  (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- 2. C1 (PermissionExamples.C1; HiddenNames §2): DERIVABLE at κ = [0].
--
-- Source programs (UNRELATED: ∀X.X→X ⋢ ∀X.X→★):
--   L   ((ΛX. λx:X. x) : ★→★) 5 : ℕ
--   R   ((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ
-- Initial cast terms (UNRELATED, PendingOpenings):
--   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
--   R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
-- The pair L₆ ⊑ R₇ (left state 6, right state 7, store α:=★ each):
--   L₆  (([+X^α] S ⟨+X⟩)⟨id(★)⟩)⟨ℕ?ℓ0⟩       S = [−X^α] 5⟨ℕ!⟩ ⟨−X⟩
--   R₇  ([+X^α] S⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
-- R₇ blames in one step; L₆ answers 5.  PermissionExamples proves it
-- unrelated at κʷ ≡ [].  AT κ = [α]: the LEFT-FIRST route goes
-- through.  The left's `+X^α` (`⟪⟫⊑`) introduces X left-only (X⊑★,
-- whatever κ, so the payment X ⊑ ★ holds); the right's `+X^α`
-- (`⊑⟪⟫`) REJOINS X through ϱ and permits nothing (K = []), but α is
-- permitted from OUTSIDE, so the rejoined X is X⊑★ and its payment
-- X ⊑ ★ holds too; the tag `X!` is then a plain ⊑cast.  (The matched
-- route stays dead at any κ: `+X ⊑ id(★)` needs R2's LeftUnpermitted
-- against the mark X⊑★, as `C3.matched-conv` below.)
------------------------------------------------------------------------

module C1 where
  open W★

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? : Coercion
  ℕ? = `ℕ ？ 0

  S LB Lid L₆ RX RB R₇ L₀ R₀ : Term
  S   = 5★ ⟪ unb₀ , tail (seal 0) ⟫
  LB  = S ⟪ Θ₀ , unseal 0 ⟫
  Lid = LB ⟨ [] ∣ idᵖ ★ ⟩
  L₆  = Lid ⟨ [] ∣ ℕ? ⟩
  RX  = S ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩
  RB  = RX ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫
  R₇  = RB ⟨ [] ∣ ℕ? ⟩
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

  L₆-⊢ : ΔR ∣ [] ⊢ L₆ ⦂ `ℕ
  L₆-⊢ = tc

  R₇-⊢ : ΔR ∣ [] ⊢ R₇ ⦂ `ℕ
  R₇-⊢ = tc

  ℕ!-ty : CastTy ΔR [] (`ℕ !) `ℕ ★
  ℕ!-ty = proj₂ (ct {M = $ 5} tc)

  ℕ?-ty : CastTy ΔR [] ℕ? ★ `ℕ
  ℕ?-ty = proj₂ (ct {M = LB ⟨ [] ∣ idᵖ ★ ⟩} tc)

  id★-ty : CastTy ΔR [] (idᵖ ★) ★ ★
  id★-ty = proj₂ (ct {M = LB} tc)

  tagX-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
  tagX-ty = proj₂ (ct {Δ₂ = ΔRᵢ} {M = S} tc)

  bS : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
  bS = proj₂ (proj₂ (bt {Δ₂ = ΔRᵢ} {M = 5★} tc))

  bLB : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
  bLB = proj₂ (proj₂ (bt {M = S} tc))

  bRB : BdyTy ΔR Θ₀ ΔRᵢ ★ ⌞ id ★ ⌟ ★
  bRB = proj₂ (proj₂ (bt {M = RX} tc))

  5★⊑5★ : ∀ {κ} → V⁰ κ ∣ [] ⊢ 5★ ⊑ 5★ ∶ ★⊑★
  5★⊑5★ = cast⊑cast (κ⊑κ lit-$ ι) ℕ!-ty ℕ!-ty ★⊑★

  -- the matched seals, at any κ
  S⊑S : ∀ {κ} → All (λ β → β ≡ 0) κ → V² κ ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S ps = ⟪⟫⊑⟪⟫₀ int-unb² (V⁰-wf ps) 5★⊑5★ bS bS
    (_ , conv-unb² , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- at κ = [0] the rejoined X is X⊑★: the tag is a plain ⊑cast
  S⊑RX : V² κ₀ ∣ [] ⊢ S ⊑ RX ∶ X⊑★ here
  S⊑RX = ⊑cast (S⊑S p₀) tagX-ty (X⊑★ here)

  -- the right's +X^0 rejoins X; K = []; the payment X ⊑ ★ holds at κ₀
  S⊑RB : Vᴸ κ₀ ∣ [] ⊢ S ⊑ RB ∶ X⊑★ here
  S⊑RB = ⊑⟪⟫₀ int-bindᴿ (V²-wf p₀) S⊑RX bRB (X⊑★ here)

  -- the left's +X^0 first: X left-only, the payment X ⊑ ★ holds
  LB⊑RB : V⁰ κ₀ ∣ [] ⊢ LB ⊑ RB ∶ ★⊑★
  LB⊑RB = ⟪⟫⊑₀ int-bindᴸ (ok-bind ∷ []) (Vᴸ-wf p₀) S⊑RB bLB ★⊑★

  -- C1 IS RELATED AT κ = [0] (a well-formed world, `V⁰-wf p₀`)
  c1-at-κ : V⁰ κ₀ ∣ [] ⊢ L₆ ⊑ R₇ ∶ ι
  c1-at-κ =
    cast⊑cast (cast⊑ co-plain LB⊑RB id★-ty ★⊑★) ℕ?-ty ℕ?-ty ι

  c1-world-wf : WfWorld (V⁰ κ₀)
  c1-world-wf = V⁰-wf p₀


-- the pieces of C2 and C3 (PermissionExamples.C3, ModeCondition `Esc`)
I★ idX : Term
I★  = ƛ ★ ∙ ` 0
idX = ƛ (` 0) ∙ ` 0

revX cE id★→ : Conv
revX  = reveal 0 (` 0 ⇒ ` 0)
cE    = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))
id★→ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

genE genE-body : Coercion
genE-body = ((` 0) !) ↦ᵖ idᵖ ★
genE      = genᵖ genE-body

--  LE = ((ν X:=ℕ. ((ΛY. λx:Y. x) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩⟨ℕ?ℓ0⟩
--  RE = ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩ X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
LE RE : Term
LE = (((ν `ℕ · Λ idX ⟨ revX ⟩) · $ 5) ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
RE = ((ν `ℕ · (I★ ⟨ [] ∣ genE ⟩) ⟨ cE ⟩) · $ 5) ⟨ [] ∣ `ℕ ？ 0 ⟩

LE-⊢ : empty ∣ [] ⊢ LE ⦂ `ℕ
LE-⊢ = tc

RE-⊢ : empty ∣ [] ⊢ RE ⦂ `ℕ
RE-⊢ = tc

------------------------------------------------------------------------
-- 3. C2 (PermissionExamples.C2; ModeCondition `Esc.esc-cex`, the late
-- pair): DERIVABLE at κ = [0].
--
-- Source programs (UNRELATED: ∀Y.Y→Y ⋢ ∀Y.Y→★):
--   L   (((ΛY. λx:Y. x) [ℕ]) 5 : ★) : ℕ
--   R   ((((λx:★. x) : ∀Y. Y→★) [ℕ]) 5) : ℕ
-- Initial cast terms LE, RE above (UNRELATED).  The pair LE₃ ⊑ RE₅
-- (left state 3, right state 5, store α:=ℕ each):
--   LE₃  (([+X^α] S₄ ⟨+X⟩)⟨ℕ!⟩)⟨ℕ?ℓ0⟩            S₄ = [−X^α] 5 ⟨−X⟩
--   RE₅  ([+X^α] ([−X^α] J ⟨id(★)⟩)⟨id★⟩^[X:★∼X] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
--        J = [+X^α] S₄⟨X!⟩^[X:X∼★] ⟨id(★)⟩
-- RE₅ blames; LE₃ answers 5.  AT κ = [α], left first: the left's +X
-- makes X left-only; every right +X^α rejoins it at the permitted α
-- (X⊑★, the payments X ⊑ ★ hold), every right −X^α makes it left-only
-- again; the innermost pair is P4 B4's own `S ⊑ J`.
------------------------------------------------------------------------

module C2 where
  open Wℕ

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S₄ LB₄ Lℕ LE₃ RX J RU RI RB₅ RE₅ : Term
  S₄  = $ 5 ⟪ unb₀ , tail (seal 0) ⟫
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

  LE₃-⊢ : ΔL ∣ [] ⊢ LE₃ ⦂ `ℕ
  LE₃-⊢ = tc

  RE₅-⊢ : ΔL ∣ [] ⊢ RE₅ ⦂ `ℕ
  RE₅-⊢ = tc

  ℕ?-ty : CastTy ΔL [] (`ℕ ？ 0) ★ `ℕ
  ℕ?-ty = proj₂ (ct {M = Lℕ} tc)

  ℕ!-ty : CastTy ΔL [] (`ℕ !) `ℕ ★
  ℕ!-ty = proj₂ (ct {M = LB₄} tc)

  tagX-ty : CastTy ΔLᵢ (X∼★ ∷ []) ((` 0) !) (` 0) ★
  tagX-ty = proj₂ (ct {Δ₂ = ΔLᵢ} {M = S₄} tc)

  idI-ty : CastTy ΔLᵢ (★∼X ∷ []) (idᵖ ★) ★ ★
  idI-ty = proj₂ (ct {Δ₂ = ΔLᵢ} {M = RU} tc)

  bS₄ : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  bS₄ = proj₂ (proj₂ (bt {Δ₂ = ΔLᵢ} {M = $ 5} tc))

  bLB₄ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bLB₄ = proj₂ (proj₂ (bt {M = S₄} tc))

  bJ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bJ = proj₂ (proj₂ (bt {M = RX} tc))

  bRU : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bRU = proj₂ (proj₂ (bt {Δ₂ = ΔLᵢ} {M = J} tc))

  bRB₅ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bRB₅ = proj₂ (proj₂ (bt {M = RI} tc))

  S₄⊑S₄ : ∀ {κ} → All (λ β → β ≡ 0) κ → V² κ ∣ [] ⊢ S₄ ⊑ S₄ ∶ X⊑X
  S₄⊑S₄ ps = ⟪⟫⊑⟪⟫₀ int-unb² (V⁰-wf ps) (κ⊑κ lit-$ ι) bS₄ bS₄
    (_ , conv-unb² , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- P4 B4's `S ⊑ J`, at κ = [0]
  S⊑J : Vᴸ κ₀ ∣ [] ⊢ S₄ ⊑ J ∶ X⊑★ here
  S⊑J = ⊑⟪⟫₀ int-bindᴿ (V²-wf p₀)
    (⊑cast (S₄⊑S₄ p₀) tagX-ty (X⊑★ here)) bJ (X⊑★ here)

  S⊑RI : V² κ₀ ∣ [] ⊢ S₄ ⊑ RI ∶ X⊑★ here
  S⊑RI = ⊑cast (⊑⟪⟫₀ int-unbindᴿ (Vᴸ-wf p₀) S⊑J bRU (X⊑★ here))
    idI-ty (X⊑★ here)

  S⊑RB₅ : Vᴸ κ₀ ∣ [] ⊢ S₄ ⊑ RB₅ ∶ X⊑★ here
  S⊑RB₅ = ⊑⟪⟫₀ int-bindᴿ (V²-wf p₀) S⊑RI bRB₅ (X⊑★ here)

  -- C2 IS RELATED AT κ = [0] (a well-formed world, `V⁰-wf p₀`)
  c2-at-κ : V⁰ κ₀ ∣ [] ⊢ LE₃ ⊑ RE₅ ∶ ι
  c2-at-κ =
    cast⊑cast
      (cast⊑ co-plain
        (⟪⟫⊑₀ int-bindᴸ (ok-bind ∷ []) (Vᴸ-wf p₀) S⊑RB₅ bLB₄
          (ι⊑★ base-ℕ))
        ℕ!-ty ★⊑★)
      ℕ?-ty ℕ?-ty ι

------------------------------------------------------------------------
-- 4. C4 and C4g (PermissionExamples.C4, C4g; HiddenNames §5, §19;
-- PushTypePremise §3): DERIVABLE at κ = [0].
--
-- Source programs (UNRELATED: ∀X.X→X ⋢ ∀X.X→★):
--   L     ((ΛX. λx:X. x) : ★→★) 5 : ℕ
--   R     ((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ                       (C4)
--   R(g)  (((λx:★. x) : ∀X.X→★ by gen X.(X! → id★)) : ★→★) 5 : ℕ (C4g)
-- Initial cast terms: C1.L₀, C1.R₀ (UNRELATED); C4g's right R0g.
-- The pairs: L₀ (the left has not run) against the right's state 2
-- (after Inst, TyBeta; store αᴿ:=★):
--   R₂   (([+X^αᴿ] (λx:X. x⟨X!⟩) ⟨−X → id(★)⟩)⟨id★ → id★⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
--   R2g  (([+X^αᴿ] ([−X^αᴿ] λx:★. x ⟨id★→⟩)⟨X! → id★⟩^[X:★∼X]
--          ⟨−X → id(★)⟩)⟨id★ → id★⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
-- The right blames; the left answers 5.  AT κ = [αᴿ]: the right's Inst
-- boundary (`⊑⟪⟫`) OPENS the left's ∀ at its X (slot [opn 0]) and
-- permits nothing (K = []); αᴿ is permitted from OUTSIDE, so the
-- payment ∀X.X→X ⊑^[X] X→★ (X opened, X⊑★) holds; `Λ⊑` joins the
-- opening; the tag (C4) or the gen body's X! (C4g) is a plain ⊑cast.
-- The permitted αᴿ has NO left partner at all.
--
-- The module is generic in the left store Ξˡ and the global pairing ϱ
-- (C4 itself: Ξˡ = [], ϱ = []; the wrapper of §6 uses Ξˡ = [α:=★],
-- ϱ = [(0,0)]); the two worlds that `⊑⟪⟫` checks are parameters.
------------------------------------------------------------------------

instL : Coercion
instL = instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !))

id★↦ : Coercion
id★↦ = idᵖ ★ ↦ᵖ idᵖ ★

bodyR I★⁻ Bdg : Term
bodyR = ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)
I★⁻   = I★ ⟪ unb₀ , id★→ ⟫
Bdg   = I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩

genE-body-ty : CastTy ΔRᵢ (★∼X ∷ []) genE-body (★ ⇒ ★) (` 0 ⇒ ★)
genE-body-ty = proj₂ (ct {Δ₂ = ΔRᵢ} {M = I★⁻} tc)

bI★⁻ : BdyTy ΔRᵢ unb₀ ΔR (★ ⇒ ★) id★→ (★ ⇒ ★)
bI★⁻ = proj₂ (proj₂ (bt {Δ₂ = ΔRᵢ} {M = I★} tc))

module C4D (Ξˡ : RepCtx) (ϱ : RepRel)
  (wfᵢ : WfWorld (world {Ξˡ ∣ []} {ΔRᵢ} 1 (skip []↪) (keep []↪) ϱ [] κ₀))
  (wf₁ : WfWorld (world {underΛ (Ξˡ ∣ [])} {ΔRᵢ} 1 (keep []↪) (keep []↪)
           (shiftᴸ ϱ) ((0 , 0) ∷ []) κ₀))
  (wfᴴ : WfWorld (world {underΛ (Ξˡ ∣ [])} {ΔR} 1 (keep []↪) (skip []↪)
           (shiftᴸ ϱ) ((0 , 0) ∷ []) κ₀))
  (instL-ty : CastTy (Ξˡ ∣ []) [] instL (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★))
  where

  Δˡ : Ctxᵗ
  Δˡ = Ξˡ ∣ []

  -- outside: no type variable, αᴿ permitted
  V4 : World Δˡ ΔR
  V4 = world 0 []↪ []↪ ϱ [] κ₀

  -- inside the right's Inst boundary: X right-only
  V4ᵢ : World Δˡ ΔRᵢ
  V4ᵢ = world 1 (skip []↪) (keep []↪) ϱ [] κ₀

  -- after `Λ⊑` joins the opening: X both-sided, mark permit 0 κ₀ = X⊑★
  V4₁ : World (underΛ Δˡ) ΔRᵢ
  V4₁ = world 1 (keep []↪) (keep []↪) (shiftᴸ ϱ) ((0 , 0) ∷ []) κ₀

  -- inside the right's crossΛ hide (C4g): X left-only
  V4ᴴ : World (underΛ Δˡ) ΔR
  V4ᴴ = world 1 (keep []↪) (skip []↪) (shiftᴸ ϱ) ((0 , 0) ∷ []) κ₀

  int4 : Interior V4 [] Θ₀ V4ᵢ
  int4 = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  intᴴ : Interior V4₁ [] unb₀ V4ᴴ
  intᴴ = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    }

  slot-ok : SlotOK V4ᵢ (opn 0)
  slot-ok = 0 , here , r-here , (λ { (_ , ()) }) , (λ ())

  join : Join1 V4ᵢ 0 V4₁
  join = join1 join-here here r-here

  ∀id : Ty
  ∀id = `∀ (` 0 ⇒ ` 0)

  -- the exterior index at κ₀: ∀X.X→X ⊑ ★→★ (no type variable)
  ∀id⊑★ : ∀id ⊑ᵂ⟨ V4 ⟩ (★ ⇒ ★)
  ∀id⊑★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  -- THE PAYMENT, opened at X: X→X ⊑ X→★ with X⊑★ (αᴿ permitted from
  -- outside); at κ = [] it fails (PermissionExamples `pay-∀`)
  pay : ∀id ⊑ᵂ⟨ V4ᵢ ⟩[ opn 0 ∷ [] ] (` 0 ⇒ ★)
  pay = ⇒⊑⇒ X⊑X (X⊑★ here)

  idX⊑bodyR : V4₁ ∣ [] ⊢ idX ⊑ bodyR ∶ ⇒⊑⇒ X⊑X (X⊑★ here)
  idX⊑bodyR =
    ƛ⊑ƛ {pA = X⊑X} tf tf
      (⊑cast (x⊑x Zʷ) C1.tagX-ty (X⊑★ here))

  -- C4g: the gen body (λx:★.x hidden) ⟨X! → id★⟩
  idX⊑Bdg : V4₁ ∣ [] ⊢ idX ⊑ Bdg ∶ ⇒⊑⇒ X⊑X (X⊑★ here)
  idX⊑Bdg =
    ⊑cast {p = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)}
      (⊑⟪⟫₀ intᴴ wfᴴ (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) bI★⁻
        (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      genE-body-ty (⇒⊑⇒ (X⊑X {X = 0}) (X⊑★ here))

  -- the right's Inst boundary, against the left Λ: open, join, peel
  module Inst (Bd : Term)
    (Bd⊑ : V4₁ ∣ [] ⊢ idX ⊑ Bd ∶ ⇒⊑⇒ X⊑X (X⊑★ here))
    (bBd : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ★) cE (★ ⇒ ★)) where

    Λ⊑RB : V4 ∣ [] ⊢ Λ idX ⊑ Bd ⟪ Θ₀ , cE ⟫ ∶ ∀id⊑★
    Λ⊑RB =
      ⊑⟪⟫ int4
        (push ca-[] f-end (ns-opn refl ∷ []) (inj₂ (V-simple (S-Λ
          (V-simple S-ƛ)))))
        (slot-ok ∷ []) ([] ∷ []) [] wfᵢ pay
        (Λ⊑ (b-join join) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
          Bd⊑ pay)
        bBd ∀id⊑★

    L₀′ R′ : Term
    L₀′ = ((Λ idX ⟨ [] ∣ instL ⟩) · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩
    R′  = (((Bd ⟪ Θ₀ , cE ⟫) ⟨ [] ∣ id★↦ ⟩) · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩

    pair : V4 ∣ [] ⊢ L₀′ ⊑ R′ ∶ ι
    pair =
      cast⊑cast
        (·⊑· {pA = ★⊑★} {pB = ★⊑★}
          (cast⊑cast Λ⊑RB instL-ty
            (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl)
            (⇒⊑⇒ ★⊑★ ★⊑★))
          (cast⊑cast (κ⊑κ lit-$ ι) (cast-ty (⊢tag g-ℕ) refl)
            (cast-ty (⊢tag g-ℕ) refl) ★⊑★))
        (cast-ty (⊢check g-ℕ) refl) (cast-ty (⊢check g-ℕ) refl) ι

-- C4 and C4g themselves: the left store is empty, nothing is paired
module C4 where
  Wᵢ : World empty ΔRᵢ
  Wᵢ = world 1 (skip []↪) (keep []↪) [] [] κ₀

  W₁ : World (underΛ empty) ΔRᵢ
  W₁ = world 1 (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) κ₀

  Wᴴ : World (underΛ empty) ΔR
  Wᴴ = world 1 (keep []↪) (skip []↪) [] ((0 , 0) ∷ []) κ₀

  wfᵢ : WfWorld Wᵢ
  wfᵢ = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 Wᵢ ≤1-[]) (namedᴿ-≤1 Wᵢ ≤1-∷[]) ((_ , here) ∷ [])

  agree₁ : ∀ {ns′ η η′ α β}
    → Paired (world {underΛ empty} {ns′} 1 η η′ [] ((0 , 0) ∷ []) κ₀) α β
    → reps ns′ ∋ʳ 0 := bindR ★
    → Agree (world {underΛ empty} {ns′} 1 η η′ [] ((0 , 0) ∷ []) κ₀) α β
  agree₁ (inj₁ ()) _
  agree₁ (inj₂ here⇔) r = abst-★ r-here r
  agree₁ (inj₂ (there⇔ ())) _

  wf₁ : WfWorld W₁
  wf₁ = wf-world (both (inj₂ here⇔) joint[]) (λ p → agree₁ p r-here)
    (namedᴸ-≤1 W₁ ≤1-∷[]) (namedᴿ-≤1 W₁ ≤1-∷[]) ((_ , here) ∷ [])

  wfᴴ : WfWorld Wᴴ
  wfᴴ = wf-world (left-only joint[]) (λ p → agree₁ p r-here)
    (namedᴸ-≤1 Wᴴ ≤1-∷[]) (namedᴿ-≤1 Wᴴ ≤1-[]) ((_ , here) ∷ [])

  instL-ty : CastTy empty [] instL (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instL-ty = proj₂ (ct {M = Λ idX} tc)

  open C4D [] [] wfᵢ wf₁ wfᴴ instL-ty public

  -- C4: the right's body is λx:X. x⟨X!⟩
  module I4 = Inst bodyR idX⊑bodyR (proj₂ (proj₂ (bt {M = bodyR} tc)))
  -- C4g: the right's body is the gen body
  module I4g = Inst Bdg idX⊑Bdg (proj₂ (proj₂ (bt {M = Bdg} tc)))

  R₂ R2g R0g : Term
  R₂  = I4.R′
  R2g = I4g.R′
  R0g = (((I★ ⟨ [] ∣ genE ⟩) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩)
          · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩

  R0g-⊢ : empty ∣ [] ⊢ R0g ⦂ `ℕ
  R0g-⊢ = tc

  -- the states (the left is C1's initial term, not yet run)
  L-is-L₀ : I4.L₀′ ≡ C1.L₀
  L-is-L₀ = refl

  R₂-state : nth (evalTerms 30 C1.R₀-⊢) 2 ≡ R₂
  R₂-state = refl

  R2g-state : nth (evalTerms 30 R0g-⊢) 2 ≡ R2g
  R2g-state = refl

  -- C4 AND C4g ARE RELATED AT κ = [0] (well-formed worlds, `wf-V4`)
  c4-at-κ : V4 ∣ [] ⊢ C1.L₀ ⊑ R₂ ∶ ι
  c4-at-κ = I4.pair

  c4g-at-κ : V4 ∣ [] ⊢ C1.L₀ ⊑ R2g ∶ ι
  c4g-at-κ = I4g.pair

  wf-V4 : WfWorld V4
  wf-V4 = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 V4 ≤1-[]) (namedᴿ-≤1 V4 ≤1-[]) ((_ , here) ∷ [])

------------------------------------------------------------------------
-- 5. C3 (PermissionExamples.C3; ModeCondition `Esc.esc-cex-early`,
-- both after TyBeta): DEAD AT ANY κ, in EVERY world over its contexts
-- (no WfWorld, no hypothesis on κ).  Sources and initial cast terms:
-- C2's (LE, RE above, UNRELATED).  The pair (store α:=ℕ each):
--   LE₁  ((([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)⟨ℕ!⟩)⟨ℕ?ℓ0⟩
--   RE₁  (([+X^α] ([−X^α] λx:★. x ⟨id★→⟩)⟨X! → id★⟩^[X:★∼X]
--          ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
-- The two one-sided orders meet X ⊑ ℕ or ℕ ⊑ X (types alone); the
-- matched order compares `−X → +X` with `−X → id(★)`: the seal JOINS X
-- (`conv-seal⊑seal`), and the ★ clause `+X ⊑ id(★)` needs the mark
-- X⊑★ AND R2's `LeftUnpermitted`: for a joined X its mark is its right
-- rep. var's permission, which R2 says is X⊑X.  The permissions κ
-- never enter.
------------------------------------------------------------------------

lookup-unique : ∀ {A : Set} {xs : List A} {k a b}
  → xs ∋ˡ k := a → xs ∋ˡ k := b → a ≡ b
lookup-unique here      here       = refl
lookup-unique (there h) (there h′) = lookup-unique h h′

-- the derived mark of a right type variable is its permission
dmarks-emb : ∀ {ns n X β} (η : ns ↪ n) (κ : List RVar) → ns ∋ˡ X := β
  → dmarks η κ ∋ˡ emb η X := permit β κ
dmarks-emb (keep η) κ here      = here
dmarks-emb (keep η) κ (there h) = there (dmarks-emb η κ h)
dmarks-emb (skip η) κ h         = there (dmarks-emb η κ h)

-- the index of a non-∀ left type has no slot
data NonForall : Ty → Set where
  nf-var : ∀ {X} → NonForall (` X)
  nf-ℕ   : NonForall `ℕ
  nf-★   : NonForall ★
  nf-⇒   : ∀ {A B} → NonForall (A ⇒ B)

nfO : ∀ {μ e O ρ A B} → NonForall A → OpenO μ e O ρ A B → O ≡ []
nfO {O = []}        _      _  = refl
nfO {O = opn _ ∷ _} nf-var ()
nfO {O = opn _ ∷ _} nf-ℕ   ()
nfO {O = opn _ ∷ _} nf-★   ()
nfO {O = opn _ ∷ _} nf-⇒   ()
nfO {O = skp ∷ _}   nf-var ()
nfO {O = skp ∷ _}   nf-ℕ   ()
nfO {O = skp ∷ _}   nf-★   ()
nfO {O = skp ∷ _}   nf-⇒   ()

plain-idx : ∀ {V : World Δ Δ′} {O A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩[ O ] A′
  → marksʷ V ⊢ embᴸ V A ⊑ embᴿ V A′
plain-idx {V = V} {O} {A} {A′} nf q =
  subst (λ O → A ⊑ᵂ⟨ V ⟩[ O ] A′) (nfO {μ = marksʷ V} {e = emb (ηᴿʷ V)}
    {O = O} {ρ = emb (ηᴸʷ V)} {A = A} {B = embᴿ V A′} nf q) q

-- the left type of a left λ (every rule that keeps a left λ keeps its
-- left type)
lam-ty : ∀ {V : World Δ Δ′} {γ A₀ N M′ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → V ∣ γ ⊢ ƛ A₀ ∙ N ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q
  → Σ[ B ∈ Ty ] A ≡ A₀ ⇒ B
lam-ty (ƛ⊑ƛ _ _ _)                 = _ , refl
lam-ty (⊑cast d _ _)               = lam-ty d
lam-ty (⊑⟪⟫ _ _ _ _ _ _ _ d _ _)   = lam-ty d

-- the right type of a right cast
open import proof.TypeSafety.CoercionTyping using (coercion-trg)

cast-trg : ∀ {μ c B A} → CastTy Δ μ c B A → A ≡ trgᵖ c
cast-trg (cast-ty ⊢p _) = sym (coercion-trg ⊢p)

ty-cast : ∀ {Γ M μ c A} → Δ ∣ Γ ⊢ M ⟨ μ ∣ c ⟩ ⦂ A → A ≡ trgᵖ c
ty-cast (⊢cast _ ⊢p _) = sym (coercion-trg ⊢p)

cast-ty-r : ∀ {V : World Δ Δ′} {γ M M′ μ c O A A′}
    {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → V ∣ γ ⊢ M ⊑ M′ ⟨ μ ∣ c ⟩ ∶⟨ A , A′ ⟩[ O ] q → A′ ≡ trgᵖ c
cast-ty-r (blame⊑ _ ⊢M′ _)              = ty-cast ⊢M′
cast-ty-r (cast⊑cast _ _ ct′ _)         = cast-trg ct′
cast-ty-r (cast⊑ _ d _ _)               = cast-ty-r d
cast-ty-r (⊑cast _ ct _)                = cast-trg ct
cast-ty-r (Λ⊑ _ _ _ _ _ d _)            = cast-ty-r d
cast-ty-r (ν⊑ d _ _ _)                  = cast-ty-r d
cast-ty-r (⟪⟫⊑ _ _ _ _ _ _ d _ _)       = cast-ty-r d

paired-c : ∀ {Δᶜ Δ′ᶜ} {W : World Δ Δ′} {Wᶜ : World Δᶜ Δ′ᶜ} {Θ Θ′ α β}
  → ConversionInterior W Θ Θ′ Wᶜ → Paired W α β → Paired Wᶜ α β
paired-c {α = α} {β} ci (inj₁ p) =
  inj₁ (subst (λ ϱ → ϱ ∋ᵨ α ⇔ β) (sym (conv-same-ϱᵍ ci)) p)
paired-c {α = α} {β} ci (inj₂ p) =
  inj₂ (subst (λ ϱ → ϱ ∋ᵨ α ⇔ β) (sym (conv-same-ϱˡ ci)) p)

module C3 where
  LB₁ RB₁ LA RA LE₁ RE₁ : Term
  LB₁ = idX ⟪ Θ₀ , revX ⟫
  RB₁ = Bdg ⟪ Θ₀ , cE ⟫
  LA  = LB₁ · $ 5
  RA  = RB₁ · $ 5
  LE₁ = (LA ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE₁ = RA ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₁-state : nth (evalTerms 20 LE-⊢) 1 ≡ LE₁
  LE₁-state = refl

  RE₁-state : nth (evalTerms 30 RE-⊢) 1 ≡ RE₁
  RE₁-state = refl

  -- the matched conversions, at ANY κ (R2 against the joined mark)
  matched-conv : ∀ {W : World ΔL ΔL} {Δᵢ Δ′ᵢ Aᵢ A′ᵢ A A′ Θ Θ′}
    → (b : BdyTy ΔL Θ Δᵢ Aᵢ revX A) (b′ : BdyTy ΔL Θ′ Δ′ᵢ A′ᵢ cE A′)
    → ¬ BdyConversionImp W b b′
  matched-conv
    (bdy-ty _ (conv-tail (conv-mid (conv-fun
       (conv-tail (conv-seal (α , _ , lᴸ , _))) _))) _ _ _)
    (bdy-ty _ (conv-tail (conv-mid (conv-fun
       (conv-tail (conv-seal (β , _ , lᴿ , _))) _))) _ _ _)
    (Wᶜ , ci , conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
       (conv-tail⊑tail (conv-seal⊑seal j)) (conv-unseal⊑id★ h u))))
    with u lᴸ (paired-c ci (proj₁ (conv-join-fresh ci lᴸ lᴿ
           (inj₁ fresh[])) j))
  ... | unp
    with trans (sym unp)
      (lookup-unique (dmarks-emb (ηᴿʷ Wᶜ) (κʷ Wᶜ) lᴿ)
        (subst (λ c → marksʷ Wᶜ ∋ˡ c := X⊑★) j h))
  ... | ()

  no-fun : ∀ {V : World ΔL ΔL} {γ B B′} {q : (`ℕ ⇒ B) ⊑ᵂ⟨ V ⟩ (`ℕ ⇒ B′)}
    → ¬ (V ∣ γ ⊢ LB₁ ⊑ RB₁ ∶⟨ `ℕ ⇒ B , `ℕ ⇒ B′ ⟩ q)
  no-fun (⟪⟫⊑⟪⟫ _ _ _ _ _ b b′ bc _) = matched-conv b b′ bc
  no-fun (⟪⟫⊑ {Wᵢ = Vi} {K = K} {Aᵢ = Aᵢ} {O = O} {r = r}
      _ _ _ _ _ _ d _ _)
    with lam-ty d
  ... | _ , refl
    with plain-idx {V = Vi +κ K} {O = O} {A = Aᵢ} nf-⇒ r
  ... | ⇒⊑⇒ () _
  no-fun {B = B} (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} {r = r}
      _ _ _ _ _ _ _ d _ _)
    with cast-ty-r d
  ... | refl
    with plain-idx {V = Vi +κ K} {O = Oᵢ} {A = `ℕ ⇒ B} {A′ = A′ᵢ} nf-⇒ r
  ... | ⇒⊑⇒ () _

  no-app : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ LA ⊑ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-app (·⊑· f (κ⊑κ lit-$ _)) = no-fun f

  no-LAℕ!-RA : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-LAℕ!-RA (cast⊑ co-plain d _ _) = no-app d

  no-LE₁-RA : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ LE₁ ⊑ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-LE₁-RA (cast⊑ co-plain d _ _) = no-LAℕ!-RA d

  no-LA-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ LA ⊑ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  no-LA-RE₁ (⊑cast d _ _) = no-app d

  no-LAℕ!-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  no-LAℕ!-RE₁ (cast⊑cast d _ _ _) = no-app d
  no-LAℕ!-RE₁ (⊑cast d _ _) = no-LAℕ!-RA d
  no-LAℕ!-RE₁ (cast⊑ co-plain d _ _) = no-LA-RE₁ d

  -- C3 IS DEAD AT ANY κ: every world over (ΔL, ΔL), well formed or not,
  -- any permissions, any slots
  c3-dead : ∀ {W : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → ¬ (W ∣ γ ⊢ LE₁ ⊑ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  c3-dead (cast⊑cast d _ _ _) = no-LAℕ!-RA d
  c3-dead (⊑cast d _ _) = no-LE₁-RA d
  c3-dead (cast⊑ co-plain d _ _) = no-LAℕ!-RE₁ d

------------------------------------------------------------------------
-- 6. CAN κ = [α] ARISE?  THE WRAPPER.  A matched `+Y^α ∥ +Y^α` whose
-- body has type ℕ JOINS Y (fresh pair, ϱ) and PERMITS α (K = [α],
-- `JoinRep.jr-join`), paying with ℕ ⊑ ℕ; a matched hide
-- `−Y^α ∥ −Y^α` (`⟪⟫⊑⟪⟫`, which has no R1′ premise) removes Y on both
-- sides and keeps κ (`Interior.same-κ`).  Inside, the world is exactly
-- the C1/C2 world at κ = [α].  So
--   wrap M = [+Y^α] ([−Y^α] M ⟨id(ℕ)⟩) ⟨id(ℕ)⟩
-- relates wrap(L) ⊑ wrap(R) at a TOP-LEVEL world (κ = [], well
-- formed) whenever L ⊑ R at κ = [α].  Wrapped C1, C2, C4 (C4 with the
-- left store α:=★ too) are related at κ = []; the wrapped right blames,
-- the wrapped left answers 5 and never blames.
------------------------------------------------------------------------

module Runs where
  open import examples.Eval
    using (eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed;
           no-redex; out-of-fuel; traceTerms; step; StepResult)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  import Data.List.Relation.Unary.All as All

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

  -- every state of a list is not blame
  AllNB : List Term → Set
  AllNB xs = All NotBlame xs

open Runs using (all-reach; NotBlame; last)
open import Reduction using (_⊢_-→*_)

idℕᶜ : Conv
idℕᶜ = ⌞ id `ℕ ⌟

wrap : Term → Term
wrap M = (M ⟪ unb₀ , idℕᶜ ⟫) ⟪ Θ₀ , idℕᶜ ⟫

idℕ⊑idℕ : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂} → ConvImp W idℕᶜ idℕᶜ
idℕ⊑idℕ = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ι))

module Wrap (R : Ty) (Ξ : RepCtx) (r0 : Ξ ∋ʳ 0 := bindR R)
  (v0 : Ξ ∋ʳ 0) (only0 : ∀ {α} → Ξ ∋ʳ α → α ≡ 0)
  (rimp : ∀ {Δ Δ′} {W : World Δ Δ′} → [] ⊢ R ⊑ᴿ⟨ W ⟩ R) where
  open Worlds R Ξ r0 v0 only0 rimp

  -- the matched +Y ∥ +Y joins its fresh pair, so it may permit 0
  jr : JoinRep (V² []) Θ₀ Θ₀ [] 0
  jr = jr-join (_ , here) here (inj₁ refl) refl

  wrap⊑ : ∀ {M M′ γ}
    → (bU : BdyTy Δ₁ unb₀ Δ₀ `ℕ idℕᶜ `ℕ)
    → (bB : BdyTy Δ₀ Θ₀ Δ₁ `ℕ idℕᶜ `ℕ)
    → BdyConversionImp (V² κ₀) bU bU
    → BdyConversionImp (V⁰ []) bB bB
    → V⁰ κ₀ ∣ [] ⊢ M ⊑ M′ ∶ ι
    → V⁰ [] ∣ γ ⊢ wrap M ⊑ wrap M′ ∶ ι
  wrap⊑ bU bB cU cB d =
    ⟪⟫⊑⟪⟫ int-bind² (jr ∷ []) (V²-wf p₀) ι
      (⟪⟫⊑⟪⟫₀ int-unb² (V⁰-wf p₀) d bU bU cU ι)
      bB bB cB ι

  -- the top-level world: no type variable, no permission, well formed
  top-wf : WfWorld (V⁰ [])
  top-wf = V⁰-wf []

module WrapC1 where
  open Wrap ★ (bindR ★ ∷ []) r-here (_ , here) only0 ★⊑★
  open W★ using (V⁰)

  bU : BdyTy ΔRᵢ unb₀ ΔR `ℕ idℕᶜ `ℕ
  bU = proj₂ (proj₂ (bt {Δ₂ = ΔRᵢ} {M = $ 5} tc))

  bB : BdyTy ΔR Θ₀ ΔRᵢ `ℕ idℕᶜ `ℕ
  bB = proj₂ (proj₂ (bt {M = $ 5 ⟪ unb₀ , idℕᶜ ⟫} tc))

  WL WR : Term
  WL = wrap C1.L₆
  WR = wrap C1.R₇

  -- WRAPPED C1 IS RELATED AT THE TOP-LEVEL WORLD (κ = [], well formed)
  wrapped-c1 : V⁰ [] ∣ [] ⊢ WL ⊑ WR ∶ ι
  wrapped-c1 = wrap⊑ bU bB (_ , W★.conv-unb² , idℕ⊑idℕ)
    (_ , W★.conv-bind² , idℕ⊑idℕ) C1.c1-at-κ

  WL-⊢ : ΔR ∣ [] ⊢ WL ⦂ `ℕ
  WL-⊢ = tc

  WR-⊢ : ΔR ∣ [] ⊢ WR ⦂ `ℕ
  WR-⊢ = tc

  WR-blames : last (evalTerms 20 WR-⊢) ≡ blame 0
  WR-blames = refl

  WL-answers : last (evalTerms 20 WL-⊢) ≡ $ 5
  WL-answers = refl

  WL-never-blames : ∀ {ℓ} → ¬ (ΔR ⊢ WL -→* blame ℓ)
  WL-never-blames r = all-reach {P = NotBlame} 20 WL-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ []) r refl

module WrapC2 where
  open Wrap `ℕ (bindR `ℕ ∷ []) r-here (_ , here) only0 (ι⊑ι base-ℕ)
  open Wℕ using (V⁰)

  bU : BdyTy ΔLᵢ unb₀ ΔL `ℕ idℕᶜ `ℕ
  bU = proj₂ (proj₂ (bt {Δ₂ = ΔLᵢ} {M = $ 5} tc))

  bB : BdyTy ΔL Θ₀ ΔLᵢ `ℕ idℕᶜ `ℕ
  bB = proj₂ (proj₂ (bt {M = $ 5 ⟪ unb₀ , idℕᶜ ⟫} tc))

  WL WR : Term
  WL = wrap C2.LE₃
  WR = wrap C2.RE₅

  -- WRAPPED C2 IS RELATED AT THE TOP-LEVEL WORLD (κ = [], well formed)
  wrapped-c2 : V⁰ [] ∣ [] ⊢ WL ⊑ WR ∶ ι
  wrapped-c2 = wrap⊑ bU bB (_ , Wℕ.conv-unb² , idℕ⊑idℕ)
    (_ , Wℕ.conv-bind² , idℕ⊑idℕ) C2.c2-at-κ

  WL-⊢ : ΔL ∣ [] ⊢ WL ⦂ `ℕ
  WL-⊢ = tc

  WR-⊢ : ΔL ∣ [] ⊢ WR ⦂ `ℕ
  WR-⊢ = tc

  WR-blames : last (evalTerms 30 WR-⊢) ≡ blame 0
  WR-blames = refl

  WL-answers : last (evalTerms 30 WL-⊢) ≡ $ 5
  WL-answers = refl

-- C4 in the store α:=★ on both sides, paired (the wrapper's world)
module WrapC4 where
  open Wrap ★ (bindR ★ ∷ []) r-here (_ , here) only0 ★⊑★
  open W★ using (V⁰)
  open WrapC1 using (bU; bB)

  Wᵢ : World ΔR ΔRᵢ
  Wᵢ = world 1 (skip []↪) (keep []↪) ϱ₀ [] κ₀

  W₁ : World (underΛ ΔR) ΔRᵢ
  W₁ = world 1 (keep []↪) (keep []↪) ((1 , 0) ∷ []) ((0 , 0) ∷ []) κ₀

  Wᴴ : World (underΛ ΔR) ΔR
  Wᴴ = world 1 (keep []↪) (skip []↪) ((1 , 0) ∷ []) ((0 , 0) ∷ []) κ₀

  wfᵢ : WfWorld Wᵢ
  wfᵢ = wf-world (right-only joint[])
    (λ { (inj₁ here⇔) → rep-rep r-here r-here ★⊑★
       ; (inj₁ (there⇔ ())) ; (inj₂ ()) })
    (namedᴸ-≤1 Wᵢ ≤1-[]) (namedᴿ-≤1 Wᵢ ≤1-∷[]) ((_ , here) ∷ [])

  agree₁ : ∀ {ns′ η η′ α β}
    → Paired (world {underΛ ΔR} {ns′} 1 η η′ ((1 , 0) ∷ []) ((0 , 0) ∷ [])
               κ₀) α β
    → reps ns′ ∋ʳ 0 := bindR ★
    → Agree (world {underΛ ΔR} {ns′} 1 η η′ ((1 , 0) ∷ []) ((0 , 0) ∷ [])
               κ₀) α β
  agree₁ (inj₁ here⇔) r = rep-rep (r-there-abst r-here) r ★⊑★
  agree₁ (inj₁ (there⇔ ())) _
  agree₁ (inj₂ here⇔) r = abst-★ r-here r
  agree₁ (inj₂ (there⇔ ())) _

  wf₁ : WfWorld W₁
  wf₁ = wf-world (both (inj₂ here⇔) joint[]) (λ p → agree₁ p r-here)
    (namedᴸ-≤1 W₁ ≤1-∷[]) (namedᴿ-≤1 W₁ ≤1-∷[]) ((_ , here) ∷ [])

  wfᴴ : WfWorld Wᴴ
  wfᴴ = wf-world (left-only joint[]) (λ p → agree₁ p r-here)
    (namedᴸ-≤1 Wᴴ ≤1-∷[]) (namedᴿ-≤1 Wᴴ ≤1-[]) ((_ , here) ∷ [])

  instL-ty : CastTy ΔR [] instL (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instL-ty = proj₂ (ct {M = Λ idX} tc)

  open C4D (bindR ★ ∷ []) ϱ₀ wfᵢ wf₁ wfᴴ instL-ty
  module I4 = Inst bodyR idX⊑bodyR (proj₂ (proj₂ (bt {M = bodyR} tc)))

  WL WR : Term
  WL = wrap I4.L₀′
  WR = wrap I4.R′

  -- WRAPPED C4 IS RELATED AT THE TOP-LEVEL WORLD (κ = [], well formed)
  wrapped-c4 : V⁰ [] ∣ [] ⊢ WL ⊑ WR ∶ ι
  wrapped-c4 = wrap⊑ bU bB (_ , W★.conv-unb² , idℕ⊑idℕ)
    (_ , W★.conv-bind² , idℕ⊑idℕ) I4.pair

  WL-⊢ : ΔR ∣ [] ⊢ WL ⦂ `ℕ
  WL-⊢ = tc

  WR-⊢ : ΔR ∣ [] ⊢ WR ⦂ `ℕ
  WR-⊢ = tc

  WR-blames : last (evalTerms 30 WR-⊢) ≡ blame 0
  WR-blames = refl

  WL-answers : last (evalTerms 40 WL-⊢) ≡ $ 5
  WL-answers = refl

------------------------------------------------------------------------
-- 7. THE WRAPPED PAIRS REFUTE SimBack AS STATED (SimBackDef: any
-- WfWorld with κʷ W ≡ []).  The right's first step leads to states that
-- are `blame` under boundaries (`BlameR`); a derivation against such a
-- right term has a left term with blame on its spine (`SpineB`:
-- through casts, boundaries, Λ, ν), and no state of the wrapped left's
-- run has one.  So neither disjunct of SimBack holds: the left never
-- blames, and no left reduct is related to any right reduct.
------------------------------------------------------------------------

data BlameR : Term → Set where
  br-blame : ∀ {ℓ} → BlameR (blame ℓ)
  br-⟪⟫    : ∀ {M Θ c} → BlameR M → BlameR (M ⟪ Θ , c ⟫)

data SpineB : Term → Set where
  sb-blame : ∀ {ℓ} → SpineB (blame ℓ)
  sb-cast  : ∀ {M μ c} → SpineB M → SpineB (M ⟨ μ ∣ c ⟩)
  sb-⟪⟫    : ∀ {M Θ c} → SpineB M → SpineB (M ⟪ Θ , c ⟫)
  sb-Λ     : ∀ {M} → SpineB M → SpineB (Λ M)
  sb-ν     : ∀ {A L c} → SpineB L → SpineB (ν A · L ⟨ c ⟩)

spine : ∀ {V : World Δ Δ′} {γ M M′ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → BlameR M′ → V ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q → SpineB M
spine b (blame⊑ _ _ _)                       = sb-blame
spine b (cast⊑ _ d _ _)                      = sb-cast (spine b d)
spine b (Λ⊑ _ _ _ _ _ d _)                   = sb-Λ (spine b d)
spine b (ν⊑ d _ _ _)                         = sb-ν (spine b d)
spine b (⟪⟫⊑ _ _ _ _ _ _ d _ _)              = sb-⟪⟫ (spine b d)
spine (br-⟪⟫ b) (⟪⟫⊑⟪⟫ _ _ _ _ d _ _ _ _)    = sb-⟪⟫ (spine b d)
spine (br-⟪⟫ b) (⊑⟪⟫ _ _ _ _ _ _ _ d _ _)    = spine b d

-- decision procedures, for the finitely many states of a run
open import Data.Bool using (Bool; true; false)

sb? : Term → Bool
sb? (` x)           = false
sb? ($ n)           = false
sb? `true           = false
sb? `false          = false
sb? (ƛ A ∙ N)       = false
sb? (L · M)         = false
sb? (Λ M)           = sb? M
sb? (ν A · L ⟨ c ⟩) = sb? L
sb? (M ⟪ Θ , c ⟫)   = sb? M
sb? (M ⟨ μ ∣ c ⟩)   = sb? M
sb? (blame ℓ)       = true

sb-sound : ∀ {M} → SpineB M → sb? M ≡ true
sb-sound sb-blame    = refl
sb-sound (sb-cast s) = sb-sound s
sb-sound (sb-⟪⟫ s)   = sb-sound s
sb-sound (sb-Λ s)    = sb-sound s
sb-sound (sb-ν s)    = sb-sound s

br? : Term → Bool
br? (` x)           = false
br? ($ n)           = false
br? `true           = false
br? `false          = false
br? (ƛ A ∙ N)       = false
br? (L · M)         = false
br? (Λ M)           = false
br? (ν A · L ⟨ c ⟩) = false
br? (M ⟪ Θ , c ⟫)   = br? M
br? (M ⟨ μ ∣ c ⟩)   = false
br? (blame ℓ)       = true

br-complete : ∀ M → br? M ≡ true → BlameR M
br-complete (M ⟪ Θ , c ⟫) e = br-⟪⟫ (br-complete M e)
br-complete (blame ℓ)     e = br-blame
br-complete (` x)           ()
br-complete ($ n)           ()
br-complete `true           ()
br-complete `false          ()
br-complete (ƛ A ∙ N)       ()
br-complete (L · M)         ()
br-complete (Λ M)           ()
br-complete (ν A · L ⟨ c ⟩) ()
br-complete (M ⟨ μ ∣ c ⟩)   ()

NoSpineB : Term → Set
NoSpineB M = sb? M ≡ false

no-spine : ∀ {M} → NoSpineB M → ¬ SpineB M
no-spine {M} e s with trans (sym (sb-sound s)) e
... | ()

-- THE REFUTATION, for a left run and a right state whose reducts are
-- all BlameR: no left reduct is related to any right reduct
module Refute {ΔL₀ ΔR₀ : Ctxᵗ} {WL N′ : Term} {AL AR : Ty}
  (⊢WL : ΔL₀ ∣ [] ⊢ WL ⦂ AL) (⊢N′ : ΔR₀ ∣ [] ⊢ N′ ⦂ AR) (k : ℕ)
  (eL : Runs.EndsVB (examples.Eval.eval k WL ⊢WL))
  (aL : All NoSpineB (evalTerms k ⊢WL))
  (eR : Runs.EndsVB (examples.Eval.eval k N′ ⊢N′))
  (aR : All (λ N → br? N ≡ true) (evalTerms k ⊢N′)) where

  unrelated : ∀ {N₂ N₂′} → ΔL₀ ⊢ WL -→* N₂ → ΔR₀ ⊢ N′ -→* N₂′
    → ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ N₂ ⊑ N₂′ ∶⟨ A , A′ ⟩[ O ] q)
  unrelated {N₂′ = N₂′} rL rR d =
    no-spine (all-reach {P = NoSpineB} k ⊢WL eL aL rL)
      (spine (br-complete N₂′ (all-reach k ⊢N′ eR aR rR)) d)

module RefuteC1 where
  open WrapC1

  -- the right's one step: R₇ blames inside the two wrappers (the
  -- evaluator's state 1; by determinism the only successor of WR)
  N′ : Term
  N′ = (blame 0 ⟪ unb₀ , idℕᶜ ⟫) ⟪ Θ₀ , idℕᶜ ⟫

  N′-is : nth (evalTerms 20 WR-⊢) 1 ≡ N′
  N′-is = refl

  N′-⊢ : ΔR ∣ [] ⊢ N′ ⦂ `ℕ
  N′-⊢ = tc

  open Refute WL-⊢ N′-⊢ 20 tt
    (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])
    tt (refl ∷ refl ∷ refl ∷ [])
    public

------------------------------------------------------------------------
-- 8. THE INVARIANT a generalized Sim/SimBack needs (proposal).
-- `PermitNamed W O`: every permitted right rep. var β has a left
-- partner α (Paired W α β) to which a LEFT TYPE VARIABLE IN SCOPE is
-- bound, or β's type variable is opened by a slot of the index.  It
-- holds at κ = [] trivially (every top-level world), and inside P4's
-- permitting boundary (the left's X stays bound to α: `p4-shape`).
-- The worlds of C1, C2, C4, C4g have no left type variable and no
-- slot, so there it forces κ = [] (`no-names`), and the κ = [] proofs
-- of PermissionExamples apply.  The HEAD rules do NOT preserve it: the
-- wrapper's matched hide leaves α permitted with no named left partner
-- (`wrapper-breaks`).  Preserving it needs every boundary to REVOKE,
-- for its interior, the permissions it leaves without a named left
-- partner (D32's `Revoke`, made obligatory for those rep. vars).
------------------------------------------------------------------------

Named : ∀ {Δ Δ′} → World Δ Δ′ → List Slot → RVar → Set
Named {Δ} {Δ′} W O β =
  (Σ[ α ∈ RVar ] (names Δ ∋ᵅ α) × Paired W α β)
  ⊎ (Σ[ k ∈ ℕ ] (O ∋ᵒ k) × (Δ′ ∋ᵗ k := β))

PermitNamed : ∀ {Δ Δ′} → World Δ Δ′ → List Slot → Set
PermitNamed W O = All (Named W O) (κʷ W)

-- no left type variable, no slot: no permission
no-names : ∀ {W : World Δ Δ′}
  → (∀ {α} → ¬ (names Δ ∋ᵅ α)) → PermitNamed W [] → κʷ W ≡ []
no-names {W = W} nn pn with κʷ W
no-names nn [] | [] = refl
no-names nn (inj₁ (_ , n , _) ∷ _) | _ ∷ _ = ⊥-elim (nn n)
no-names nn (inj₂ (_ , () , _) ∷ _) | _ ∷ _

-- C1's and C2's world at κ = [0] violates it; so do C4's and C4g's
c1-world-bad : ¬ PermitNamed (W★.V⁰ κ₀) []
c1-world-bad pn with no-names {W = W★.V⁰ κ₀} (λ { (_ , ()) }) pn
... | ()

c2-world-bad : ¬ PermitNamed (Wℕ.V⁰ κ₀) []
c2-world-bad pn with no-names {W = Wℕ.V⁰ κ₀} (λ { (_ , ()) }) pn
... | ()

c4-world-bad : ¬ PermitNamed C4.V4 []
c4-world-bad pn with no-names {W = C4.V4} (λ { (_ , ()) }) pn
... | ()

-- inside P4's permitting boundary, and inside the right's −X under it,
-- the left's X is bound to α = 0, paired with αᴿ = 0: the invariant
-- holds where the permission is used
p4-shape : PermitNamed (Wℕ.V² κ₀) [] × PermitNamed (Wℕ.Vᴸ κ₀) []
p4-shape = (inj₁ (0 , (0 , here) , inj₁ here⇔) ∷ []) ,
           (inj₁ (0 , (0 , here) , inj₁ here⇔) ∷ [])

-- the wrapper: the outer matched boundary's interior satisfies it, the
-- matched hide's interior (same κ, `Interior.same-κ`) does not
wrapper-breaks : PermitNamed (W★.V² κ₀) [] × ¬ PermitNamed (W★.V⁰ κ₀) []
wrapper-breaks = (inj₁ (0 , (0 , here) , inj₁ here⇔) ∷ []) , c1-world-bad

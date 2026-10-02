module TermImprecision where

-- File Charter:
--   * CAST-TERM IMPRECISION `W ∣ γ ⊢ M ⊑ M′ ∶ p` (GTNF/design.md §12.3,
--     with D11-D16), over the worlds of ImprecisionWorld.  M is the
--     MORE precise (left) term, typed on `Δ`; M′ the right one, typed on
--     `Δ′`; `p : A ⊑ᵂ⟨ W ⟩ A′` relates their types (GTSFImp's index
--     shape, `_∣_⊢²_⊑_∶_`).  §1 the side-premise bundles `Lit`,
--     `CastTy`, `NuTy`, `BdyTy` (each is exactly the premises of the
--     corresponding typing rule of Terms, minus the subterm), with their
--     reassembly into a typing; §2 the relation.
--   * THE RULES, design.md §12.3 as updated by D14, one constructor
--     each: congruence `x⊑x`, `κ⊑κ` (the literals `$ n`, `true`,
--     `false`, one rule through `Lit`), `ƛ⊑ƛ`, `·⊑·`; `blame⊑`;
--     `cast⊑cast`, `cast⊑`, `⊑cast`; `Λ⊑Λ`, `Λ⊑`, `∀⊑⟪+⟫`; `ν⊑ν`,
--     `ν⊑`; `⟪⟫⊑⟪⟫`, `⟪⟫⊑`, `⊑⟪⟫`.  16 rules: §12.3's 17 minus
--     `⊕⊑⊕`, since GTNF has no binary operators yet.
--   * COERCIONS ARE NOT COMPARED.  Each is typed on its own side under
--     the mode environment its cast carries (`CastTy`, as `⊢cast`).
--     In contrast, D17 compares the two conversions of `ν⊑ν` and
--     `⟪⟫⊑⟪⟫` structurally.  `NuConversionImp` reads them in the two
--     `TyBetaBoundary` conversion contexts, with the ν-bound rep. vars
--     paired lexically.  `BdyConversionImp` reads them in the two
--     boundary conversion contexts.  One-sided rules still type their
--     sole conversion but have no conversion-imprecision premise.
--   * EXPLICIT CONCLUSION PROOFS.  As in GTSFImp, a rule whose
--     conclusion type is not built from its premises' proofs by a
--     constructor takes that proof `q` as an argument: `emb` under a
--     binder is only extensionally `extᵗ`, so `∀⊑∀`-style proofs cannot
--     be computed from the premise's.
--   * TYPING SIDE PREMISES.  Both typings `Δ ∣ lhs γ ⊢ M ⦂ A` and
--     `Δ′ ∣ rhs γ ⊢ M′ ⦂ A′` are meant to follow from a derivation (not
--     proved here).  The premises that serve that purpose only:
--     - `ƛ⊑ƛ`: the two annotations' `_⊢ᵗ_` (for `⊢ƛ`);
--     - `blame⊑`: `Δ ⊢ᵗ A` (for `⊢blame`) and the whole right typing;
--     - the cast rules: `CastTy` (for `⊢cast`);
--     - `Λ⊑Λ`, `Λ⊑`: `Value` of the bodies (for `⊢Λ`'s value restriction);
--     - `ν⊑ν`, `ν⊑`: `NuTy` (for `⊢ν`);
--     - the boundary rules and `∀⊑⟪+⟫`: `BdyTy` (for `boundary`);
--     - `∀⊑⟪+⟫`: also the LEFT typing of the ∀-value V, because V's
--       typing is not recoverable from that of `inst_X(V)` without a
--       strengthening lemma (the `gen` case of `InstX` puts V under
--       `crossΛᴹ`).
--     A premise at `γ = []` (boundary interiors, `∀⊑⟪+⟫`) yields its
--     typing at `[]`; the conclusion's at `lhs γ`/`rhs γ` then needs the
--     standard weakening of a term-closed term.
--   * DE BRUIJN READINGS.
--     - `ν X:=A.(L X)⟨c⟩` is Terms' `ν A · L ⟨ c ⟩`.
--     - `∀⊑⟪+⟫`'s right boundary is `bind 0 β ∷ []`: `Inst`'s ν leaves
--       `inst [] = bind 0 0 ∷ []` by `TyBeta`, and a sibling shift
--       renumbers only the rep. var (`renᴮᴿ`); "β:=★" is
--       `Δ′ ∋rep β := ★`, and its premise world is `W ⊕⁺ m ^ β`.
--     - Its premise uses the `InstX` RELATION of Reduction §0, not a
--       function: `InstX V N` with N read under `underΛ Δ`, the left
--       value's abstract rep. var at 0 (D16).
--   * DEVIATION from design.md §12.3 (also in the report):
--     - `Λ⊑` does not repeat the right term's typing (GTSFImp's `Λ⊑²`
--       does): the premise already types M′ on the unchanged `Δ′` and
--       `rhs γ′ = rhs γ`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; `ℕ; `𝔹; ★; _⇒_; `∀)
open import Ctx
open import Conversion using (Conv; _⊢_∶_⇝_)
open import Boundary using (Boundary; Change; bind; BoundaryWf; TyBetaBoundary)
open import Coercion
  using (Coercion; ModeEnv; _∣_⊢ᵖ_∶_⟹_; NonVar; _∈ᵗ_)
open import Terms
open import Reduction using (InstX)
open import Imprecision using (VarImp; X⊑X; ⇒⊑⇒)
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
-- 2. The relation
------------------------------------------------------------------------

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) (γ : CtxImp W)
    : Term → Term → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  ----------------------------------------------------------------------
  -- Congruence (GTSFImp x⊑x², κ⊑κ², ƛ⊑ƛ², ·⊑·²)

  x⊑x : ∀ {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
      --------------------------------
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {k ι}
    → Lit k ι
    → (p : ι ⊑ᵂ⟨ W ⟩ ι)
      --------------------------------
    → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
      ---------------------------------------------
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
      ---------------------------------------------
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  ----------------------------------------------------------------------
  -- Blame (GTSFImp blame⊑²)

  blame⊑ : ∀ {ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  ----------------------------------------------------------------------
  -- Casts (GTSFImp cast⊑cast², cast⊑², ⊑cast²)

  cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  ----------------------------------------------------------------------
  -- Type abstraction (GTSFImp Λ⊑Λ², Λ⊑²), and ∀⊑⟪+⟫ (D14)

  Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′
    → Value V
    → Value V′
    → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  -- the right term crosses the left-only binder unweakened
  Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′}
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W ⊕ᴸ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      ---------------------------------------------
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  -- a left ∀-value against the right boundary `[+X^β] V′ ⟨c′⟩` that
  -- `Inst` created; the mark m of the new name is chosen here (D11)
  ∀⊑⟪+⟫ : ∀ {V N V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
    → Δ′ ∋rep β := ★
    → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      ---------------------------------------------
    → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q

  ----------------------------------------------------------------------
  -- Instantiation (GTSFImp •⊑•², •⊑²); there is no ⊑ν

  ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      ---------------------------------------------
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      ---------------------------------------------
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ----------------------------------------------------------------------
  -- Boundaries (these replace GTSFImp's reveal/conceal rules).  The
  -- interior is term-closed, so each premise has γ = [].

  ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
      {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  ⊑⟪⟫ : ∀ {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      ---------------------------------------------
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

module TermImprecision where

-- File Charter:
--   * CAST-TERM IMPRECISION `W ∣ γ ⊢ M ⊑ M′ ∶ p` (GTNF/design.md §12.3,
--     with D11-D16 and D27), over the worlds `World` of
--     ImprecisionWorld.  M is the MORE precise (left) term, typed on
--     `Δ`; M′ the right one, typed on `Δ′`; `p : A ⊑ᵂ⟨ W ⟩ A′` relates
--     their types (GTSFImp's index shape, `_∣_⊢²_⊑_∶_`).  §1 the
--     side-premise bundles `Lit`, `CastTy`, `NuTy`, `BdyTy` (each is
--     exactly the premises of the corresponding typing rule of Terms,
--     minus the subterm), with their reassembly into a typing; §2 the
--     pending-name side relations (`Claim`, `CastClaim`, `BdyClaim`,
--     `Push`) and the relation.
--   * THE RULES, design.md §12.3 as updated by D14 and D27, one
--     constructor each: congruence `x⊑x`, `κ⊑κ` (the literals `$ n`, `true`,
--     `false`, one rule through `Lit`), `ƛ⊑ƛ`, `·⊑·`; `blame⊑`;
--     `cast⊑cast`, `cast⊑`, `⊑cast`; `Λ⊑Λ`, `Λ⊑`; `ν⊑ν`, `ν⊑`;
--     `⟪⟫⊑⟪⟫`, `⟪⟫⊑`, `⊑⟪⟫`.  15 rules: §12.3's 17 minus `⊕⊑⊕`, since
--     GTNF has no binary operators yet, and minus `∀⊑⟪+⟫`, removed by
--     design.md D26.
--   * PENDING NAMES IN THE WORLD (design.md D27; Jeremy, 2026-10-05;
--     replaces D26's `Opens`).  The pending right names are the field
--     `πʷ` of the world (ImprecisionWorld §3), next pop first.  The
--     index `A ⊑ᵂ⟨ W ⟩ A′` reads the ACTUAL left type A and opens one
--     `∀` per pending name; at `πʷ W = []` it is the plain
--     `μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′`.  Four rules
--     handle pending names (§2): `⊑⟪⟫` PUSHES right-only names that
--     its boundary introduces (`Push`; the left must be a value) and
--     carries the older ones through its boundary; `Λ⊑` POPS the head
--     name (`Claim`: `claim-pop` joins the left binder to it by
--     `Open1`); `cast⊑` passes them through a `∀ᵖ` cast or pops the
--     last one at a `genᵖ` cast (`CastClaim`); `⟪⟫⊑` passes them into a
--     ∀-boundary (`BdyClaim`).  `⊑cast` carries them; every other rule
--     is stated at a world in constructor form with `πʷ = []`.  The side
--     relations read only the `πʷ` of their worlds (`Push Θ′ M (πʷ W)
--     (πʷ Wᵢ)`); `cast⊑`'s premise world is `record W { πʷ = πₚ }`, at
--     which `CtxImp` (center and embeddings only) is `CtxImp W`, so its
--     γ is reused with no transport.  No `InstX` in the relation, and
--     the left term stays a value under a pending name.  Type
--     imprecision is unchanged.  Checked first as a local copy:
--     proof/DGG/notes/PendingOpenings.{agda,md}.
--   * HISTORY.  Before D26 a separate rule `∀⊑⟪+⟫` (D14, with D22's side
--     conditions) related a left ∀-value V to the right boundary
--     `[+X^β] V′ ⟨c′⟩` that `Inst` creates, with premise
--     `W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′` for `InstX V N`.  Its right boundary
--     was `bind 0 β ∷ []`: `Inst`'s ν leaves `inst [] = bind 0 0 ∷ []` by
--     `TyBeta`, and a sibling shift renumbers only the rep. var
--     (`renᴮᴿ`).  It failed at a Merge of that boundary with an inner
--     one (proof/DGG/notes/RestrictedForallBoundary.agda); D26 replaces
--     it by the openings of `⊑⟪⟫` (`Opens`: zero or more openings of
--     the left ∀-value, each relating `inst_X V` at an opened world).
--     D27 replaced `Opens` by pending names: `Opens` related the
--     ★-embedding counterexample (proof/DGG/notes/StarEmbedding.md is
--     the alternative D27 rejected), and its openings related InstX
--     images, which are not values.
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
--     - the boundary rules: `BdyTy` (for `boundary`);
--     A premise at `γ = []` (boundary interiors) yields its
--     typing at `[]`; the conclusion's at `lhs γ`/`rhs γ` then needs the
--     standard weakening of a term-closed term.
--   * DE BRUIJN READINGS.
--     - `ν X:=A.(L X)⟨c⟩` is Terms' `ν A · L ⟨ c ⟩`.
--     - a pending name's "β:=★" is `Δ′ ∋rep β := ★` (`PendingOK`); the
--       pop of name 0 of `W ⊕ʳ m ^ β` has premise world `W ⊕⁺ m ^ β`
--       (`open-⊕`).
--   * DEVIATION from design.md §12.3 (also in the report):
--     - `Λ⊑` does not repeat the right term's typing (GTSFImp's `Λ⊑²`
--       does): the premise already types M′ on the unchanged `Δ′` and
--       `rhs γ′ = rhs γ`.

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
    → Claim W W₁
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
    → Push Θ′ M (πʷ W) (πʷ Wᵢ)
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

-- the push of nothing: the plain right-only boundary rule
push-none : ∀ {Θ′ M} → Push Θ′ M [] []
push-none = push ca-[] [] (inj₁ refl)

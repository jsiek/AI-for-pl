module proof.DGG.notes.ModeCondition where

-- File Charter:
--   * THE PROPOSAL CHECKED HERE (option 2 of SidedMarks.md, Jeremy
--     2026-10-05): keep design.md D11's marks (chosen at the binder) and
--     D15 (a rejoined name keeps its mark), and instead restrict the
--     CAST rules by the MODE ENVIRONMENT the right cast carries.  The
--     condition is purely in the term relation: type imprecision
--     `_⊢_⊑_` (Imprecision.agda), the world layer and conversion
--     imprecision are UNCHANGED.  Findings in ModeCondition.md.  NOT a
--     Def module, not imported by All.agda; nothing outside this file
--     and its .md is edited.
--   * THE CONDITION (§2, `ModeOK`): a right cast `M′ ⟨ μ′ ∣ c′ ⟩`
--     related at indices p (source) and q (target) may not READ `X ⊑ ★`
--     (an `X⊑★` leaf of p or q, `ReadsStar`) at a center name that is
--     the image of a right name k whose mode in μ′ is `★∼X∼★` (the
--     source-scope mode compilation writes, `Coercion.cross`).  `★∼X`
--     (gen's binder, Reduction `inst-gen`) and its flip `X∼★`
--     (CastFun's argument cast) permit it.  Both `⊑cast` and
--     `cast⊑cast` carry it (§2; `cast⊑cast` must: §8).
--   * LOCAL COPY.  The world layer, ConversionImprecision and the
--     side-premise bundles come from SidedMarks.agda (a copy of git
--     HEAD 46f04f4f, pre-D27).  `Interior`, `ConversionInterior`,
--     `WfWorld`, `Opens` and the 15 rules are HEAD's, verbatim (with
--     HEAD's field names), so HEAD's example derivations port verbatim
--     (§4).  The relation is parameterized by a `CastPolicy` (§3):
--     `head⁰` is HEAD's relation (module `H`), `modes` the proposal
--     (module `M`), `asStated` the tag-only reading (module `A`, §8).
--   * §3 `lift`: on a right term none of whose casts carries `★∼X∼★`
--     (`NoX`, decided by `noX?`), every H-derivation is an
--     M-derivation.  §5 every right state of every Cambridge corpus
--     run (and of P4, K) is checked: the condition is vacuous on all
--     of them; only the counterexample's R₀ carries `★∼X∼★`
--     (`CorpusModes`, `reach-lift`).
--   * §4 HEAD's corpus derivations, ported verbatim (Cg X0, C12 X0/B1,
--     C13 B1, C14 B1, C2 X0/B6/B7, Ch B0/X0/B1, …), lifted to M.
--   * §6 Example P4 (= cambridge Cf from its second block), ALL
--     blocks, derived in H and lifted to M (`p4-B1ᴹ` … `p4-B6ᴹ`).
--   * §7 the SimBackBlame counterexample `L₆ ⊑ R₇`: HEAD's one-sided
--     derivation fails the condition, and NO M-derivation exists in
--     any world (`cex-unrelatedᴹ`).
--   * §8 the tag-only reading (`asStated`) is not closed under
--     reduction (`asStated-sim-fails`).
--   * §9 A NEW COUNTEREXAMPLE UNDER `modes` (`Esc.esc-cex`,
--     `Esc.esc-cex-early`): a gen-mode tag (`X∼★`) escapes a gen scope
--     whose codomain does not re-check; the decisive inner pair is
--     P4 B4's own J pair `S⊑J` (same world, terms, modes; reused
--     verbatim), so NO cast condition separates the two.  VERDICT: the
--     mode condition removes the known counterexample but not the
--     class; the distinction P4 needs lives in the world (how the
--     left-only interval was created), SidedMarks.md §6.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Bool using (Bool; true; false; _∧_; _∨_; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List using (List; []; _∷_; map; length; head; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
  using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction using (InstX; inst-Λ; inst-gen; inst-∀; inst-⟪⟫)
open import Imprecision
open import proof.DGG.notes.SidedMarks
  hiding (Policy; d11; sided; module Rel; module D; module S;
          module P4; module Corpus; module K; module C2; module Cex;
          module Runs; D11Marks; D11CMarks; opens-lft; wf-sid; no-rel;
          Sidedᵐ; s[]; s-both; s-left; s-right; s-none; right-mark;
          left-mark; sided-relabel; Sid; sid-⊕ᴸ; bad-cast;
          RepImp; Agree; abst-abst; abst-★; rep-rep)
open import proof.DGG.notes.SidedMarks
  using (RepImp; Agree; abst-abst; abst-★; rep-rep)

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. HEAD's interiors, well-formedness and openings (verbatim, with
-- HEAD's field names; D11/D15 marks in `Interior`)
------------------------------------------------------------------------

record Interior (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
  constructor interior-world
  field
    int-left  : Δ ⊢ⁱ Θ ⇒ Δᵢ
    int-right : Δ′ ⊢ⁱ Θ′ ⇒ Δ′ᵢ
    same-ϱᵍ : ϱᵍʷ Wᵢ ≡ ϱᵍʷ W
    same-ϱˡ : ϱˡʷ Wᵢ ≡ ϱˡʷ W
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
    mark-left : ∀ {X Xₑ m}
      → Δᵢ ∋tv X → toExt Θ X ≡ just Xₑ
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → μʷ Wᵢ ∋ˡ emb (ηᴸʷ Wᵢ) X := m
    mark-right : ∀ {X′ X′ₑ m}
      → Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → μʷ Wᵢ ∋ˡ emb (ηᴿʷ Wᵢ) X′ := m
open Interior public

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

record WfWorld (W : World Δ Δ′) : Set where
  constructor wf-world
  field
    wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wf-agree : ∀ {α β} → Paired W α β → Agree W α β
    wf-namedᴸ : NamedUniqueᴸ W
    wf-namedᴿ : NamedUniqueᴿ W
open WfWorld public

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

data Opens {Δ′ : Ctxᵗ} (Θ′ : Boundary)
    : ∀ {Δ Δ⁺} → World Δ Δ′ → Term → Ty → World Δ⁺ Δ′ → Term → Ty
    → Set where
  open-none : ∀ {Δ} {W : World Δ Δ′} {M A}
    → Opens Θ′ W M A W M A
  open-∀ : ∀ {Δ Δ⁺ k} {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {W⁺ : World Δ⁺ Δ′} {V N M₀ A A₀}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ [] ⊢ V ⦂ `∀ A
    → InstX V N
    → Fresh Θ′ k
    → Open1 W k W₁
    → Opens Θ′ W₁ N A W⁺ M₀ A₀
    → Opens Θ′ W V (`∀ A) W⁺ M₀ A₀

------------------------------------------------------------------------
-- 2. THE CONDITION
------------------------------------------------------------------------

-- the modes other than the source-scope mode
data NonCross : Mode → Set where
  nc-XX : NonCross X∼X
  nc-X★ : NonCross X∼★
  nc-★X : NonCross ★∼X

-- `ReadsStar d j`: the imprecision derivation d reads `X ⊑ ★` (an
-- `X⊑★` leaf) at the FREE center name j (under a binder the index
-- shifts; a leaf at a bound variable is not a center name)
data ReadsStar : ∀ {μ A B} → μ ⊢ A ⊑ B → ℕ → Set where
  rs-var  : ∀ {μ X} {h : μ ∋ˡ X := X⊑★} → ReadsStar (X⊑★ h) X
  rs-⇒ˡ   : ∀ {μ A A′ B B′ j} {d : μ ⊢ A ⊑ A′} {e : μ ⊢ B ⊑ B′}
    → ReadsStar d j → ReadsStar (⇒⊑⇒ d e) j
  rs-⇒ʳ   : ∀ {μ A A′ B B′ j} {d : μ ⊢ A ⊑ A′} {e : μ ⊢ B ⊑ B′}
    → ReadsStar e j → ReadsStar (⇒⊑⇒ d e) j
  rs-⇒★ˡ  : ∀ {μ A B j} {d : μ ⊢ A ⊑ ★} {e : μ ⊢ B ⊑ ★}
    → ReadsStar d j → ReadsStar (⇒⊑★ d e) j
  rs-⇒★ʳ  : ∀ {μ A B j} {d : μ ⊢ A ⊑ ★} {e : μ ⊢ B ⊑ ★}
    → ReadsStar e j → ReadsStar (⇒⊑★ d e) j
  rs-∀∀   : ∀ {μ A B j} {d : extᵐ μ ⊢ A ⊑ B}
    → ReadsStar d (suc j) → ReadsStar (∀⊑∀ d) j
  rs-∀⊑   : ∀ {μ A B j nv i} {d : instᵐ μ ⊢ A ⊑ ⇑ᵗ B}
    → ReadsStar d (suc j) → ReadsStar (∀⊑ nv i d) j
  rs-∀⊑★  : ∀ {μ A j ns} {d : extᵐ μ ⊢ A ⊑ ★}
    → ReadsStar d (suc j) → ReadsStar (∀⊑★ ns d) j

-- THE CONDITION.  A right cast with mode environment μ′, related at
-- an index d, may read `X ⊑ ★` at center j only if j is not the image
-- of a right name that μ′ gives the source-scope mode `★∼X∼★`.
ModeOK : (W : World Δ Δ′) → ModeEnv → ∀ {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → Set
ModeOK W μ′ d = ∀ {j k} → ReadsStar d j
  → emb (ηᴿʷ W) k ≡ j → μ′ ∋ˡ k := ★∼X∼★ → ⊥

-- the tag-only reading of the proposal (§8): the right-only cast tags
-- or checks no name at the source-scope mode
data CrossFreeG (μ : ModeEnv) : Ty → Set where
  cfg-nv  : ∀ {G} → GroundNV G → CrossFreeG μ G
  cfg-var : ∀ {X m} → μ ∋ˡ X := m → NonCross m → CrossFreeG μ (` X)

data CrossFree : ModeEnv → Coercion → Set where
  cf-id      : ∀ {μ A} → CrossFree μ (idᵖ A)
  cf-tag     : ∀ {μ G} → CrossFreeG μ G → CrossFree μ (G !)
  cf-chk     : ∀ {μ G ℓ} → CrossFreeG μ G → CrossFree μ (G ？ ℓ)
  cf-↦       : ∀ {μ p q} → CrossFree (flipEnv μ) p → CrossFree μ q
    → CrossFree μ (p ↦ᵖ q)
  cf-∀       : ∀ {μ p} → CrossFree (X∼X ∷ μ) p → CrossFree μ (∀ᵖ p)
  cf-inst    : ∀ {μ p} → CrossFree (X∼★ ∷ μ) p → CrossFree μ (instᵖ p)
  cf-gen     : ∀ {μ p} → CrossFree (★∼X ∷ μ) p → CrossFree μ (genᵖ p)
  cf-seq-tag : ∀ {μ p G} → CrossFree μ p → CrossFreeG μ G
    → CrossFree μ (p ︔ G !)
  cf-seq-chk : ∀ {μ p G ℓ} → CrossFreeG μ G → CrossFree μ p
    → CrossFree μ (G ？ ℓ ︔ p)
  cf-bot-elim  : ∀ {μ} → CrossFree μ bot-elim
  cf-bot-intro : ∀ {μ ℓ} → CrossFree μ (bot-intro ℓ)

------------------------------------------------------------------------
-- 3. Policies and the relation (HEAD's 15 rules; the two two-sided /
-- right-only cast rules carry the policy's premise)
------------------------------------------------------------------------

record CastPolicy : Set₁ where
  field
    -- `⊑cast`: the right cast's world, modes, coercion, and its source
    -- index p : A ⊑ B′ and target index q : A ⊑ A′
    RCast : ∀ {Δ Δ′} (W : World Δ Δ′) → ModeEnv → Coercion
      → ∀ {A B′ A′} → A ⊑ᵂ⟨ W ⟩ B′ → A ⊑ᵂ⟨ W ⟩ A′ → Set
    -- `cast⊑cast`: the right cast's modes, and both indices
    CCast : ∀ {Δ Δ′} (W : World Δ Δ′) → ModeEnv
      → ∀ {B B′ A A′} → B ⊑ᵂ⟨ W ⟩ B′ → A ⊑ᵂ⟨ W ⟩ A′ → Set

-- HEAD (D11, D15): no premise
head⁰ : CastPolicy
head⁰ = record
  { RCast = λ _ _ _ _ _ → ⊤
  ; CCast = λ _ _ _ _ → ⊤
  }

-- THE PROPOSAL
modes : CastPolicy
modes = record
  { RCast = λ W μ′ _ p q → ModeOK W μ′ p × ModeOK W μ′ q
  ; CCast = λ W μ′ p q → ModeOK W μ′ p × ModeOK W μ′ q
  }

-- the tag-only reading: `⊑cast` only, by the coercion's own tags
asStated : CastPolicy
asStated = record
  { RCast = λ _ μ′ c′ _ _ → CrossFree μ′ c′
  ; CCast = λ _ _ _ _ → ⊤
  }

module Rel (P : CastPolicy) where
  open CastPolicy P

  infix 3 _∣_⊢_⊑_∶_

  data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) (γ : CtxImp W)
      : Term → Term → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

    x⊑x : ∀ {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
      → γ ∋ʷ x ⦂ ctx-imp A A′ p
      → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

    κ⊑κ : ∀ {k ι}
      → Lit k ι
      → (p : ι ⊑ᵂ⟨ W ⟩ ι)
      → W ∣ γ ⊢ k ⊑ k ∶ p

    ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → Δ ⊢ᵗ A
      → Δ′ ⊢ᵗ A′
      → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
      → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

    ·⊑· : ∀ {L L′ M M′ A A′ B B′}
        {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
      → W ∣ γ ⊢ M ⊑ M′ ∶ pA
      → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

    blame⊑ : ∀ {ℓ M′ A A′}
      → Δ ⊢ᵗ A
      → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
      → (p : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

    cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ μ c B A
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → ⦃ CCast W μ′ p q ⦄
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᵂ⟨ W ⟩ A′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ μ c B A
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

    ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → ⦃ RCast W μ′ c′ p q ⦄
      → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
      → LiftCtx X⊑X γ γ′
      → Value V
      → Value V′
      → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
      → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

    Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′}
      → NonVar A
      → 0 ∈ᵗ A
      → LiftCtxᴸ γ γ′
      → Value V
      → W ⊕ᴸ ∣ γ′ ⊢ V ⊑ M′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

    ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
      → W ∣ γ ⊢ L ⊑ L′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ A′
      → (n : NuTy Δ A C c B)
      → (n′ : NuTy Δ′ A′ C′ c′ B′)
      → NuConversionImp W n n′
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

    ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ M′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ ★
      → NuTy Δ A C c B
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

    ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
        {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
      → Interior W Θ Θ′ Wᵢ
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
      → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
      → BdyConversionImp W b b′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

    ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World Δᵢ Δ′}
        {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
      → Interior W Θ [] Wᵢ
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → BdyTy Δ Θ Δᵢ Aᵢ c A
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

    ⊑⟪⟫ : ∀ {Δ′ᵢ Δ⁺} {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
        {M M₀ M′ Θ′ c′ A A₀ A′ᵢ A′} {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
      → Interior W [] Θ′ Wᵢ
      → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
      → WfWorld Wᵢ⁺
      → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ M′ ∶ r
      → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

-- the policy premise is an INSTANCE argument, so that HEAD's derivations
-- (which have no such premise) port verbatim into H (`⊤` is found)
instance
  ⊤-instance : ⊤
  ⊤-instance = tt

module H = Rel head⁰
module M = Rel modes
module A = Rel asStated

open H public using () renaming (_∣_⊢_⊑_∶_ to _∣_⊢ᴴ_⊑_∶_)
open M public using () renaming (_∣_⊢_⊑_∶_ to _∣_⊢ᴹ_⊑_∶_)
open A public using () renaming (_∣_⊢_⊑_∶_ to _∣_⊢ᴬ_⊑_∶_)

------------------------------------------------------------------------
-- 3b. Where the condition is vacuous: right terms with no source-scope
-- mode.  On them H and M relate the same pairs (`lift`, `forget`).
------------------------------------------------------------------------

-- every cast of the term carries a mode environment without `★∼X∼★`
data NoX : Term → Set where
  nx-var   : ∀ {x} → NoX (` x)
  nx-$     : ∀ {n} → NoX ($ n)
  nx-true  : NoX `true
  nx-false : NoX `false
  nx-ƛ     : ∀ {A N} → NoX N → NoX (ƛ A ∙ N)
  nx-·     : ∀ {L M} → NoX L → NoX M → NoX (L · M)
  nx-Λ     : ∀ {V} → NoX V → NoX (Λ V)
  nx-ν     : ∀ {A L c} → NoX L → NoX (ν A · L ⟨ c ⟩)
  nx-⟪⟫    : ∀ {N Θ c} → NoX N → NoX (N ⟪ Θ , c ⟫)
  nx-cast  : ∀ {N μ p} → NoX N → All NonCross μ → NoX (N ⟨ μ ∣ p ⟩)
  nx-blame : ∀ {ℓ} → NoX (blame ℓ)

nonCross? : Mode → Bool
nonCross? X∼X   = true
nonCross? X∼★   = true
nonCross? ★∼X   = true
nonCross? ★∼X∼★ = false

envOK? : ModeEnv → Bool
envOK? []      = true
envOK? (m ∷ μ) = nonCross? m ∧ envOK? μ

noX? : Term → Bool
noX? (` x)          = true
noX? ($ n)          = true
noX? `true          = true
noX? `false         = true
noX? (ƛ A ∙ N)      = noX? N
noX? (L · N)        = noX? L ∧ noX? N
noX? (Λ V)          = noX? V
noX? (ν A · L ⟨ c ⟩) = noX? L
noX? (N ⟪ Θ , c ⟫)  = noX? N
noX? (N ⟨ μ ∣ p ⟩)  = noX? N ∧ envOK? μ
noX? (blame ℓ)      = true

T∧ : ∀ {a b} → T (a ∧ b) → T a × T b
T∧ {true}  t = tt , t
T∧ {false} ()

nonCross-sound : ∀ m → T (nonCross? m) → NonCross m
nonCross-sound X∼X   _ = nc-XX
nonCross-sound X∼★   _ = nc-X★
nonCross-sound ★∼X   _ = nc-★X
nonCross-sound ★∼X∼★ ()

envOK-sound : ∀ μ → T (envOK? μ) → All NonCross μ
envOK-sound []      _ = []
envOK-sound (m ∷ μ) t with T∧ {nonCross? m} t
... | a , b = nonCross-sound m a ∷ envOK-sound μ b

noX-sound : ∀ N → T (noX? N) → NoX N
noX-sound (` x) _ = nx-var
noX-sound ($ n) _ = nx-$
noX-sound `true _ = nx-true
noX-sound `false _ = nx-false
noX-sound (ƛ A ∙ N) t = nx-ƛ (noX-sound N t)
noX-sound (L · N) t with T∧ {noX? L} t
... | a , b = nx-· (noX-sound L a) (noX-sound N b)
noX-sound (Λ V) t = nx-Λ (noX-sound V t)
noX-sound (ν A · L ⟨ c ⟩) t = nx-ν (noX-sound L t)
noX-sound (N ⟪ Θ , c ⟫) t = nx-⟪⟫ (noX-sound N t)
noX-sound (N ⟨ μ ∣ p ⟩) t with T∧ {noX? N} t
... | a , b = nx-cast (noX-sound N a) (envOK-sound μ b)
noX-sound (blame ℓ) _ = nx-blame

-- the list version, for the states of a run
allNoX? : List Term → Bool
allNoX? []       = true
allNoX? (N ∷ Ns) = noX? N ∧ allNoX? Ns

allNoX-sound : ∀ Ns → T (allNoX? Ns) → All NoX Ns
allNoX-sound []       _ = []
allNoX-sound (N ∷ Ns) t with T∧ {noX? N} t
... | a , b = noX-sound N a ∷ allNoX-sound Ns b

all-lookup : ∀ {P : Mode → Set} {μ k m} → All P μ → μ ∋ˡ k := m → P m
all-lookup (p ∷ ps) here      = p
all-lookup (p ∷ ps) (there h) = all-lookup ps h

not-cross : ¬ NonCross ★∼X∼★
not-cross ()

-- with no source-scope mode, the condition holds at every index
vacuous : ∀ {W : World Δ Δ′} {μ′ A A′} {d : A ⊑ᵂ⟨ W ⟩ A′}
  → All NonCross μ′ → ModeOK W μ′ d
vacuous a _ _ h = not-cross (all-lookup a h)

-- EVERY H-DERIVATION AGAINST A RIGHT TERM WITHOUT SOURCE-SCOPE MODES
-- IS AN M-DERIVATION (the premises' right terms are subterms of R)
lift : ∀ {W : World Δ Δ′} {γ L R A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → NoX R → W ∣ γ ⊢ᴴ L ⊑ R ∶ q → W ∣ γ ⊢ᴹ L ⊑ R ∶ q
lift nx (H.x⊑x h) = M.x⊑x h
lift nx (H.κ⊑κ l p) = M.κ⊑κ l p
lift (nx-ƛ nx) (H.ƛ⊑ƛ a a′ d) = M.ƛ⊑ƛ a a′ (lift nx d)
lift (nx-· nx nx′) (H.·⊑· d e) = M.·⊑· (lift nx d) (lift nx′ e)
lift nx (H.blame⊑ a t p) = M.blame⊑ a t p
lift {W = W} (nx-cast nx a) (H.cast⊑cast {p = p} d c c′ q) =
  M.cast⊑cast (lift nx d) c c′ q
    ⦃ vacuous {W = W} {d = p} a , vacuous {W = W} {d = q} a ⦄
lift nx (H.cast⊑ d c q) = M.cast⊑ (lift nx d) c q
lift {W = W} (nx-cast nx a) (H.⊑cast {p = p} d c′ q) =
  M.⊑cast (lift nx d) c′ q
    ⦃ vacuous {W = W} {d = p} a , vacuous {W = W} {d = q} a ⦄
lift (nx-Λ nx) (H.Λ⊑Λ l v v′ d q) = M.Λ⊑Λ l v v′ (lift nx d) q
lift nx (H.Λ⊑ nv i l v d q) = M.Λ⊑ nv i l v (lift nx d) q
lift (nx-ν nx) (H.ν⊑ν d a n n′ c q) = M.ν⊑ν (lift nx d) a n n′ c q
lift nx (H.ν⊑ d a n q) = M.ν⊑ (lift nx d) a n q
lift (nx-⟪⟫ nx) (H.⟪⟫⊑⟪⟫ i wf d b b′ c q) =
  M.⟪⟫⊑⟪⟫ i wf (lift nx d) b b′ c q
lift nx (H.⟪⟫⊑ i wf d b q) = M.⟪⟫⊑ i wf (lift nx d) b q
lift (nx-⟪⟫ nx) (H.⊑⟪⟫ i os wf d b q) = M.⊑⟪⟫ i os wf (lift nx d) b q

-- and M is a sub-relation of H
forget : ∀ {W : World Δ Δ′} {γ L R A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ᴹ L ⊑ R ∶ q → W ∣ γ ⊢ᴴ L ⊑ R ∶ q
forget (M.x⊑x h) = H.x⊑x h
forget (M.κ⊑κ l p) = H.κ⊑κ l p
forget (M.ƛ⊑ƛ a a′ d) = H.ƛ⊑ƛ a a′ (forget d)
forget (M.·⊑· d e) = H.·⊑· (forget d) (forget e)
forget (M.blame⊑ a t p) = H.blame⊑ a t p
forget (M.cast⊑cast d c c′ q) = H.cast⊑cast (forget d) c c′ q
forget (M.cast⊑ d c q) = H.cast⊑ (forget d) c q
forget (M.⊑cast d c′ q) = H.⊑cast (forget d) c′ q
forget (M.Λ⊑Λ l v v′ d q) = H.Λ⊑Λ l v v′ (forget d) q
forget (M.Λ⊑ nv i l v d q) = H.Λ⊑ nv i l v (forget d) q
forget (M.ν⊑ν d a n n′ c q) = H.ν⊑ν (forget d) a n n′ c q
forget (M.ν⊑ d a n q) = H.ν⊑ (forget d) a n q
forget (M.⟪⟫⊑⟪⟫ i wf d b b′ c q) = H.⟪⟫⊑⟪⟫ i wf (forget d) b b′ c q
forget (M.⟪⟫⊑ i wf d b q) = H.⟪⟫⊑ i wf (forget d) b q
forget (M.⊑⟪⟫ i os wf d b q) = H.⊑⟪⟫ i os wf (forget d) b q

------------------------------------------------------------------------
-- 5. The corpus: every right state of every Cambridge run, of P4 and
-- of K, is free of the source-scope mode.  So on the WHOLE corpus the
-- condition is vacuous: a pair (L′, R′) with R′ a reachable right
-- state is H-derivable iff it is M-derivable (`lift`, `forget`,
-- `all-reach`).  Only the counterexample's R₀ has `★∼X∼★`.
------------------------------------------------------------------------

import proof.DGG.notes.SidedMarks as SM

module CorpusModes where
  open import examples.Eval using (evalTerms; eval)
  open import Reduction using (_⊢_-→*_)
  open import examples.CambridgeExamples
  open import examples.ImprecisionExamples using (R4-⊢)

  -- the right runs, with the fuel CambridgeExamples' `*-R-run` uses
  noX-P4   : All NoX (evalTerms 17 R4-⊢)
  noX-P4   = allNoX-sound _ tt
  noX-K    : All NoX (evalTerms 20 SM.K.RK-⊢)
  noX-K    = allNoX-sound _ tt
  noX-Cf   : All NoX (evalTerms 16 Cf-R-⊢)
  noX-Cf   = allNoX-sound _ tt
  noX-Cg   : All NoX (evalTerms 21 Cg-R-⊢)
  noX-Cg   = allNoX-sound _ tt
  noX-Ch   : All NoX (evalTerms 15 Ch-R-⊢)
  noX-Ch   = allNoX-sound _ tt
  noX-C2   : All NoX (evalTerms 21 C2-R-⊢)
  noX-C2   = allNoX-sound _ tt
  noX-C5   : All NoX (evalTerms 6 C5-R-⊢)
  noX-C5   = allNoX-sound _ tt
  noX-C10  : All NoX (evalTerms 6 C10-R-⊢)
  noX-C10  = allNoX-sound _ tt
  noX-C12  : All NoX (evalTerms 24 C12-R-⊢)
  noX-C12  = allNoX-sound _ tt
  noX-C13  : All NoX (evalTerms 29 C13-R-⊢)
  noX-C13  = allNoX-sound _ tt
  noX-C14  : All NoX (evalTerms 38 C14-R-⊢)
  noX-C14  = allNoX-sound _ tt
  noX-C17  : All NoX (evalTerms 7 C17-R-⊢)
  noX-C17  = allNoX-sound _ tt
  noX-C18  : All NoX (evalTerms 22 C18-R-⊢)
  noX-C18  = allNoX-sound _ tt
  noX-C18b : All NoX (evalTerms 23 C18b-R-⊢)
  noX-C18b = allNoX-sound _ tt
  noX-C19  : All NoX (evalTerms 7 C19-R-⊢)
  noX-C19  = allNoX-sound _ tt
  noX-C23a : All NoX (evalTerms 27 C23a-R-⊢)
  noX-C23a = allNoX-sound _ tt
  noX-C23b : All NoX (evalTerms 25 C23b-R-⊢)
  noX-C23b = allNoX-sound _ tt
  noX-CJ   : All NoX (evalTerms 7 CJ-R-⊢)
  noX-CJ   = allNoX-sound _ tt
  noX-C8   : All NoX (evalTerms 11 C8-R-⊢)
  noX-C8   = allNoX-sound _ tt
  noX-C22  : All NoX (evalTerms 10 C22-R-⊢)
  noX-C22  = allNoX-sound _ tt

  -- ON A CROSS-FREE RUN, every reachable right state relates the same
  -- left terms in H and in M
  reach-lift : ∀ {Δ′ R R′ B} (k : ℕ) (⊢R : Δ′ ∣ [] ⊢ R ⦂ B)
      {Δ} {W : World Δ Δ′} {γ L A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → EndsVB (eval k R ⊢R) → All NoX (evalTerms k ⊢R)
    → Δ′ ⊢ R -→* R′
    → W ∣ γ ⊢ᴴ L ⊑ R′ ∶ q → W ∣ γ ⊢ᴹ L ⊑ R′ ∶ q
  reach-lift k ⊢R e a r = lift (all-reach k ⊢R e a r)

  -- the counterexample's right program does carry it
  cex-R₀-cross : noX? SM.Cex.R₀ ≡ false
  cex-R₀-cross = refl

------------------------------------------------------------------------
-- 4. HEAD's corpus derivations (46f04f4f), PORTED VERBATIM into H:
-- examples/TermImprecisionExamples.agda (module TIE) and
-- examples/TermImprecisionRebaseExamples.agda (module Rebase), with
-- only their import lines replaced.  That they check against H is the
-- evidence that H is HEAD's relation.  §4b lifts them to M.
------------------------------------------------------------------------

module TIE where
  open H
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples
    using (L1; R1; L1-⊢; R1-⊢; R2; L3-⊢; R3-⊢;
           L6; R6; L6-⊢; R6-⊢)

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
  five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
    → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
  five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

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
  Wν = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ [])

  Wν-conv : ∀ {R R′}
    → ConversionInterior (underν² R R′ ∅ʷ) Θ₀ Θ₀ Wν
  Wν-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
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
  W₁ = world [] []↪ []↪ ((0 , 0) ∷ []) []

  -- the interior world: X both-sided at X⊑X
  Wᵢ₁ : World ΔLᵢ ΔRᵢ
  Wᵢ₁ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

  int₀ : ∀ {R} → allocate R empty ⊢ⁱ Θ₀ ⇒ ((bindR R ∷ []) ∣ (0 ∷ []))
  int₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  Wᵢ₁-int : Interior W₁ Θ₀ Θ₀ Wᵢ₁
  Wᵢ₁-int = record
    { int-left   = int₀
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  Wᵢ₁-conv : ConversionInterior W₁ Θ₀ Θ₀ Wᵢ₁
  Wᵢ₁-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
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
    (namedᴸ-≤1 Wᵢ₁ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₁ ≤1-∷[])
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
  W₂ = world [] []↪ []↪ [] []

  -- X is left-only, so its mark is X⊑★
  Wᵢ₂ : World ΔLᵢ empty
  Wᵢ₂ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] []

  Wᵢ₂-int : Interior W₂ Θ₀ [] Wᵢ₂
  Wᵢ₂-int = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  Wᵢ₂-wf : WfWorld Wᵢ₂
  Wᵢ₂-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 Wᵢ₂ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₂ ≤1-[])
    where
    agree : ∀ {α β} → Paired Wᵢ₂ α β → Agree Wᵢ₂ α β
    agree (inj₁ ())
    agree (inj₂ ())

  p2-tybeta : W₂ ∣ [] ⊢ L1′ ⊑ R2 ∶ ℕ⊑★
  p2-tybeta =
    ·⊑· (⟪⟫⊑ Wᵢ₂-int Wᵢ₂-wf
                (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) bL-ty
                (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P3, after the right's Inst, TyBeta and Beta, before the left's
  -- TyBeta: ⊑⟪⟫ with one opening (D26; before D26, ∀⊑⟪+⟫) relates the
  -- left Λ to the right's Inst boundary
  ------------------------------------------------------------------------

  R3′ : Term
  R3′ = ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ ★ ⟩) · 5⟨ℕ!⟩

  L3′-state : head (drop 1 (evalTerms 11 L3-⊢)) ≡ just L1
  L3′-state = refl

  R3′-state : head (drop 3 (evalTerms 16 R3-⊢)) ≡ just R3′
  R3′-state = refl

  W₃ : World empty ΔR
  W₃ = world [] []↪ []↪ [] []

  -- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★)
  ∀id⊑★ : ∀X⇒X ⊑ᵂ⟨ W₃ ⟩ (★ ⇒ ★)
  ∀id⊑★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  ΛidX-⊢ : empty ∣ [] ⊢ Λ idX ⦂ ∀X⇒X
  ΛidX-⊢ = tc

  -- the Inst boundary `+X^α` (α:=★ at rep. var 0) alone: X is a
  -- right-only name, with the mark m chosen here (D11)
  int-ro₃ : ∀ {m} → Interior W₃ [] Θ₀ (W₃ ⊕ʳ m ^ 0)
  int-ro₃ = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  -- the opened world: the left Λ's abstract rep. var paired lexically
  -- with αᴿ:=★ (`abst-★`), the shared name at X⊑X
  W₃⁺-wf : WfWorld (W₃ ⊕⁺ X⊑X ^ 0)
  W₃⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 (W₃ ⊕⁺ X⊑X ^ 0) ≤1-∷[]) (namedᴿ-≤1 (W₃ ⊕⁺ X⊑X ^ 0) ≤1-∷[])
    where
    agree : ∀ {α β} → Paired (W₃ ⊕⁺ X⊑X ^ 0) α β
      → Agree (W₃ ⊕⁺ X⊑X ^ 0) α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-★ r-here r-here
    agree (inj₂ (there⇔ ()))

  -- one opening of the left `ΛX. λx:X. x` at the boundary's name 0
  -- (`inst-Λ`)
  openΛidX : Opens Θ₀ (W₃ ⊕ʳ X⊑X ^ 0) (Λ idX) ∀X⇒X (W₃ ⊕⁺ X⊑X ^ 0) idX
    (` 0 ⇒ ` 0)
  openΛidX =
    open-∀ nv-⇒ (∈-⇒ˡ ∈-var) (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
      (inst-Λ (V-simple S-ƛ)) refl (open-⊕ r-here) open-none

  p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  p3-inst =
    ·⊑· (ν⊑ (⊑cast (⊑⟪⟫ int-ro₃ openΛidX W₃⁺-wf
                           (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                           bR-ty ∀id⊑★)
                   (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl) ∀id⊑★)
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
  W₆ = world [] []↪ []↪ ((0 , 0) ∷ []) []

  Wᵢ₆ : World Δ6ᵢ Δ6ᵢ
  Wᵢ₆ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

  int₆ : Δ6 ⊢ⁱ Θ₀ ⇒ Δ6ᵢ
  int₆ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  Wᵢ₆-int : Interior W₆ Θ₀ Θ₀ Wᵢ₆
  Wᵢ₆-int = record
    { int-left   = int₆
    ; int-right  = int₆
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  Wᵢ₆-wf : WfWorld Wᵢ₆
  Wᵢ₆-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wᵢ₆ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₆ ≤1-∷[])
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
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
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
        (⊑cast
          (ƛ⊑ƛ {pA = X⊑X} {pB = ι⊑ι base-ℕ}
            tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
          body6R-ty (⇒⊑⇒ X⊑X ℕ⊑★))
        b6L-ty b6R-ty b6-conv (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★))
      (κ⊑κ lit-true (ι⊑ι base-𝔹))


module Rebase where
  open H
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples
  open import TermSubst using (crossΛᴹ)
  open TIE
    using (idX; revX; ℕ⊑★; five⊑; Θ₀; L1′; ΔL; ΔR; ΔLᵢ; ΔRᵢ;
           W₁; Wᵢ₁; Wᵢ₁-int; Wᵢ₁-conv; Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv;
           revX⊑revX; νL-ty; Wν; Wν-conv; W₃; R3′; p3-inst; int-ro₃)
  open import examples.ImprecisionExamples using (L1)

  ------------------------------------------------------------------------
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

  X⇒X⊑★⇒★ : ∀ {Δ Δ′} {W : World Δ Δ′} → μʷ W ∋ˡ emb (ηᴸʷ W) 0 := X⊑★
    → (` 0 ⇒ ` 0) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
  X⇒X⊑★⇒★ m = ⇒⊑⇒ (X⊑★ m) (X⊑★ m)

  ℕ⇒ℕ : ∀ {Δ Δ′} (W : World Δ Δ′) → (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ `ℕ)
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

    -- outside: no names
    Wc⁰ : World ΔL (Ξ′ ∣ [])
    Wc⁰ = world [] []↪ []↪ ϱ []

    -- c both-sided, its right name at rep. var β
    Wc² : (β : RVar) → World ΔLᵢ (Ξ′ ∣ (β ∷ []))
    Wc² β = world (X⊑★ ∷ []) (keep []↪) (keep []↪) ϱ []

    -- c left-only
    Wcᴸ : World ΔLᵢ (Ξ′ ∣ [])
    Wcᴸ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) ϱ []

    -- the matched TyBeta boundaries [+X^αᴸ] ∥ [+Y^0]
    Wc-bind² : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0 → Interior Wc⁰ Θ₀ Θ₀ (Wc² 0)
    Wc-bind² v p = record
      { int-left   = interior (changes∷ changes[]
                       (step-bind (_ , here) fresh[] ins-here))
      ; int-right  = interior (changes∷ changes[]
                       (step-bind v fresh[] ins-here))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
      ; join-fresh = λ { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
                       ; here (there ()) _ ; (there ()) _ _ }
      ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      }

    Wc-bind²-conv : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0
      → ConversionInterior Wc⁰ Θ₀ Θ₀ (Wc² 0)
    Wc-bind²-conv v p = record
      { conv-left       =
          conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
      ; conv-right      = conversion (conv-bind v conv[] fresh[] ins-here)
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
      ; conv-join-cont  = λ { _ _ () _ }
      ; conv-join-fresh = λ
          { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; conv-mark-left  = λ { _ () _ }
      ; conv-mark-right = λ { _ () _ }
      }

    -- a right-only −Y^β: c goes left-only, keeping c⊑★
    Wc-unbindᴿ : ∀ {β} → Ξ′ ∋ʳ β → Interior (Wc² β) [] (unbind 0 β ∷ []) Wcᴸ
    Wc-unbindᴿ v = record
      { int-left   = interior changes[]
      ; int-right  = interior (changes∷ changes[]
                       (step-unbind v del-here fresh[]))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , ()) _ _ }
      ; join-fresh = λ { _ () _ }
      ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , ()) _ _ }
      }

    -- a right-only +X^β: c rejoins αᴸ, β's left partner named in scope (D25)
    Wc-bindᴿ : ∀ {β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
      → Interior Wcᴸ [] (bind 0 β ∷ []) (Wc² β)
    Wc-bindᴿ v p = record
      { int-left   = interior changes[]
      ; int-right  = interior (changes∷ changes[] (step-bind v fresh[] ins-here))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
      ; join-fresh = λ
          { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      }

  -- the types at these worlds
  c⊑★ᴸ : ∀ Ξ′ ϱ → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wcᴸ {Ξ′} {ϱ} ⟩ (★ ⇒ ★)
  c⊑★ᴸ Ξ′ ϱ = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

  c⊑★² : ∀ Ξ′ ϱ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} β ⟩ (★ ⇒ ★)
  c⊑★² Ξ′ ϱ β = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

  c⊑c² : ∀ Ξ′ ϱ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} β ⟩ (` 0 ⇒ ` 0)
  c⊑c² Ξ′ ϱ β = ⇒⊑⇒ (X⊑X {X = 0}) (X⊑X {X = 0})

  -- the core `[+X^αᴿ] (λx:X. x) ⟨−X → +X⟩` against λx:X. x, and one
  -- gen layer `[+Y^β] ([−Y^β] M ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩` around a
  -- right term M, at the right context Ξ′ (the typing bundles are passed
  -- in, read off `tc` at each instance)
  core⊑ : ∀ {Ξ′ ϱ β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} β)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ idX ⟪ bind 0 β ∷ [] , revX ⟫
        ∶ c⊑★ᴸ Ξ′ ϱ
  core⊑ {Ξ′} {ϱ} v p W²-wf b =
    ⊑⟪⟫ (Wc-bindᴿ v p) open-none W²-wf
      (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
      b (c⊑★ᴸ Ξ′ ϱ)

  -- the gen layer's right term, around M
  genLayer : RVar → Term → Term
  genLayer β M =
    (((M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩)
      ⟪ bind 0 β ∷ [] , revX ⟫

  layer⊑ : ∀ {Ξ′ ϱ β M}
    → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} β)
    → WfWorld (Wcᴸ {Ξ′} {ϱ})
    → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (β ∷ [])) (unbind 0 β ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (β ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ genLayer β M
        ∶ c⊑★ᴸ Ξ′ ϱ
  layer⊑ {Ξ′} {ϱ} {β} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b =
    ⊑⟪⟫ (Wc-bindᴿ v p) open-none W²-wf
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫ (Wc-unbindᴿ v) open-none Wᴸ-wf
          (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ)) bᵤ (c⊑★² Ξ′ ϱ β))
        cₜ (c⊑c² Ξ′ ϱ β))
      b (c⊑★ᴸ Ξ′ ϱ)

  -- the outermost gen layer, matched with the left's TyBeta boundary
  outer⊑ : ∀ {Ξ′ ϱ M B′}
    → (v : Ξ′ ∋ʳ 0) → (p : ϱ ∋ᵨ 0 ⇔ 0)
    → WfWorld (Wc² {Ξ′} {ϱ} 0)
    → WfWorld (Wcᴸ {Ξ′} {ϱ})
    → Wcᴸ {Ξ′} {ϱ} ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → (b : BdyTy (Ξ′ ∣ []) Θ₀ (Ξ′ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX B′)
    → BdyConversionImp (Wc⁰ {Ξ′} {ϱ}) bL-ty b
    → (q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ Wc⁰ {Ξ′} {ϱ} ⟩ B′)
    → Wc⁰ {Ξ′} {ϱ} ∣ [] ⊢ idX ⟪ Θ₀ , revX ⟫ ⊑ genLayer 0 M ∶ q
  outer⊑ {Ξ′} {ϱ} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b bc q =
    ⟪⟫⊑⟪⟫ (Wc-bind² v p) W²-wf
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫ (Wc-unbindᴿ v) open-none Wᴸ-wf
          (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ)) bᵤ (c⊑★² Ξ′ ϱ 0))
        cₜ (c⊑c² Ξ′ ϱ 0))
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
  module Wf₁₂ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₂ ∣ nsR)
    W = world μ η η′ ϱ₁₂ []

    -- both pairs agree: ℕ ⊑ ℕ and ℕ ⊑ ★
    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())

  W₁₂-wf : WfWorld W₁₂
  W₁₂-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₁₂ [] []↪ []↪

  W₁₂²-wf : WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} 0)
  W₁₂²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₁₂ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₂} {ϱ₁₂})
  W₁₂ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (skip []↪)

  W₁₂ˣ-wf : WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} 1)
  W₁₂ˣ-wf = wf-world (both (inj₁ (there⇔ here⇔)) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  c12-b1 : W₁₂ ∣ [] ⊢ L1′ ⊑ C12-R₃ ∶ ι⊑ι base-ℕ
  c12-b1 =
    ·⊑·
      (outer⊑ (_ , here) here⇔ W₁₂²-wf W₁₂ᴸ-wf
        (core⊑ (_ , there here) (there⇔ here⇔) W₁₂ˣ-wf B12x-ty)
        id★↦-ty B12ᵤ-ty B12ₜ-ty B12-ty
        (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₁₂))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- Shared pieces for the right-led blocks
  ------------------------------------------------------------------------

  -- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★), in any world
  ∀id⊑★ : ∀ {Δ Δ′} (W : World Δ Δ′) → `∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
  ∀id⊑★ W = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  ∀id⊑∀id : ∀ {Δ Δ′} (W : World Δ Δ′)
    → `∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ W ⟩ `∀ (` 0 ⇒ ` 0)
  ∀id⊑∀id W = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

  ★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → (★ ⇒ ★) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
  ★⇒★ W = ⇒⊑⇒ ★⊑★ ★⊑★

  ℕ⇒ℕ⊑★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
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
  -- Cg's right-led block X0 (D14, D26: ⊑⟪⟫ with one opening at mark X⊑★)
  ------------------------------------------------------------------------

  -- the opened premise world: the left Λ's abstract rep. var paired
  -- LEXICALLY with αᴿ:=★; the shared name at X⊑★ (chosen here, D11)
  Wg⁺ : World (underΛ empty) ΔRₓ
  Wg⁺ = W₃ ⊕⁺ X⊑★ ^ 0

  -- inside the right's −X^αᴿ: X is left-only, X⊑★
  Wg⁻ : World (underΛ empty) ΔR
  Wg⁻ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] ((0 , 0) ∷ [])

  Wg⁻-int : Interior Wg⁺ [] (unbind 0 0 ∷ []) Wg⁻
  Wg⁻-int = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  -- WfWorld for the worlds of the lexical pair (aᴸ_ΛY, αᴿ:=★): the left
  -- member abstract, the right member at ★ (`abst-★`)
  module WfΛ★ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((abstR ∷ []) ∣ nsL) ((bindR ★ ∷ []) ∣ nsR)
    W = world μ η η′ [] ((0 , 0) ∷ [])

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-★ r-here r-here
    agree (inj₂ (there⇔ ()))


  Wg⁺-wf : WfWorld Wg⁺
  Wg⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open WfΛ★ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  Wg⁻-wf : WfWorld Wg⁻
  Wg⁻-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[])
    where open WfΛ★ (X⊑★ ∷ []) (keep []↪) (skip []↪)

  cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
  cg-x0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑⟪⟫ int-ro₃
            (open-∀ nv-⇒ (∈-⇒ˡ ∈-var) (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
              (inst-Λ (V-simple S-ƛ)) refl (open-⊕ r-here) open-none)
            Wg⁺-wf
            (⊑cast
              (⊑⟪⟫ Wg⁻-int open-none Wg⁻-wf
                (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
                I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
              tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
            Bg-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
      five⊑

  ------------------------------------------------------------------------
  -- C2's right-led block X0 (D14, D26: ⊑⟪⟫ opening a gen-cast left
  -- ∀-value, `inst-gen`)
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

  -- the premise world, now at X⊑X (the gen wrappers are matched)
  W2⁺ : World (underΛ empty) ΔRₓ
  W2⁺ = W₃ ⊕⁺ X⊑X ^ 0

  -- inside both −X^α: no names
  W2⁻ : World (reps (underΛ empty) ∣ []) ΔR
  W2⁻ = world [] []↪ []↪ [] ((0 , 0) ∷ [])

  unbind₀-int : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ (unbind 0 0 ∷ [])
    ⇒ ((b ∷ Ξ) ∣ [])
  unbind₀-int = interior (changes∷ changes[]
    (step-unbind (_ , here) del-here fresh[]))

  unbind₀-conv : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ (unbind 0 0 ∷ [])
    ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  unbind₀-conv = conversion (conv-unbind (_ , here) conv[])

  W2⁻-int : Interior W2⁺ (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W2⁻
  W2⁻-int = record
    { int-left   = unbind₀-int
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  -- the conversion contexts skip the unbinds: they are the exterior
  unbind₀-conv-self : ∀ {b b′ Ξ Ξ′}
      {W : World ((b ∷ Ξ) ∣ (0 ∷ [])) ((b′ ∷ Ξ′) ∣ (0 ∷ []))}
    → ConversionInterior W (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W
  unbind₀-conv-self = record
    { conv-left       = unbind₀-conv
    ; conv-right      = unbind₀-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
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
    ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    }

  W2⁺-conv : ConversionInterior W2⁺ (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W2⁺
  W2⁺-conv = unbind₀-conv-self

  I★⁻ᴸ-ty : BdyTy (underΛ empty) (unbind 0 0 ∷ []) (reps (underΛ empty) ∣ [])
    (★ ⇒ ★) id★→ (★ ⇒ ★)
  I★⁻ᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = underΛ empty} {M = I★⁻}))))

  tagᴸ-ty : CastTy (underΛ empty) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᴸ-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ empty} {M = I★gen})))

  W2⁺-wf : WfWorld W2⁺
  W2⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open WfΛ★ (X⊑X ∷ []) (keep []↪) (keep []↪)

  W2⁻-wf : WfWorld W2⁻
  W2⁻-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[])
    where open WfΛ★ [] []↪ []↪

  c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
  c2-x0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑⟪⟫ int-ro₃
            (open-∀ nv-⇒ (∈-⇒ˡ ∈-var)
              (V-simple (S-cast (V-simple S-ƛ) I-gen)) I★genI-⊢
              (inst-gen (V-simple S-ƛ)) refl (open-⊕ r-here) open-none)
            W2⁺-wf
            (cast⊑cast
              (⟪⟫⊑⟪⟫ W2⁻-int W2⁻-wf
                (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
                I★⁻ᴸ-ty I★⁻ᴿ-ty
                (W2⁺ , W2⁺-conv , id★→⊑id★→) (★⇒★ W2⁺))
              tagᴸ-ty tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
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
  -- boundaries (X both-sided at X⊑X, chosen at B1); the final interior
  -- world of (−X, +X) ∥ (−X, +X) is Wᵢ₁ again (X continues, keeps X⊑X);
  -- inside the two −X, W₁ again (no names)
  Wᵢ₁-unb : Interior Wᵢ₁ unb₀ unb₀ W₁
  Wᵢ₁-unb = record
    { int-left   = unbind₀-int
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  W₁-wf : WfWorld W₁
  W₁-wf = wf-world joint[] agree (namedᴸ-≤1 W₁ ≤1-[]) (namedᴿ-≤1 W₁ ≤1-[])
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
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
        ; (_ , here) (_ , there ()) _ _
        ; (_ , there ()) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
    }

  Wᵢ₁-Θ⁻⁺-conv : ConversionInterior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
  Wᵢ₁-Θ⁻⁺-conv = record
    { conv-left       = Θ⁻⁺-conv
    ; conv-right      = Θ⁻⁺-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
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
    ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
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
    ⊑cast
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
    ⊑cast
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

  module Wf₁₃ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₃ ∣ nsR)
    W = world μ η η′ ϱ₁₂ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())


  W₁₃²-wf : ∀ {β}
    → ϱ₁₂ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ₁₃} {ϱ₁₂} β)
  W₁₃²-wf p = wf-world (both (inj₁ p) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open Wf₁₃ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₁₃ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₃} {ϱ₁₂})
  W₁₃ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₁₃ (X⊑★ ∷ []) (keep []↪) (skip []↪)

  c13-b1 : W₁₃ ∣ [] ⊢ L1′ ⊑ C13-R₄ ∶ ℕ⊑★
  c13-b1 =
    ·⊑·
      (⊑cast
        (outer⊑ (_ , here) here⇔ (W₁₃²-wf here⇔) W₁₃ᴸ-wf
          (core⊑ (_ , there here) (there⇔ here⇔)
            (W₁₃²-wf (there⇔ here⇔)) B13x-ty)
          id★↦-ty B13ᵤ-ty B13ₜ-ty B13-ty
          (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
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
  module Wf₁₄ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₄ ∣ nsR)
    W = world μ η η′ ϱ₁₄ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ here⇔))) =
      rep-rep r-here (r-there (r-there r-here)) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ (there⇔ ()))))
    agree (inj₂ ())


  W₁₄-wf : WfWorld W₁₄
  W₁₄-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₁₄ [] []↪ []↪

  W₁₄²-wf : ∀ {β} → ϱ₁₄ ∋ᵨ 0 ⇔ β → WfWorld (Wc² {Ξ₁₄} {ϱ₁₄} β)
  W₁₄²-wf p = wf-world (both (inj₁ p) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open Wf₁₄ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₁₄ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₄} {ϱ₁₄})
  W₁₄ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₁₄ (X⊑★ ∷ []) (keep []↪) (skip []↪)

  c14-b1 : W₁₄ ∣ [] ⊢ L1′ ⊑ C14-R₅ ∶ ι⊑ι base-ℕ
  c14-b1 =
    ·⊑·
      (outer⊑ (_ , here) here⇔ (W₁₄²-wf here⇔) W₁₄ᴸ-wf
        (layer⊑ (_ , there here) (there⇔ here⇔)
          (W₁₄²-wf (there⇔ here⇔)) W₁₄ᴸ-wf
          (core⊑ (_ , there (there here)) (there⇔ (there⇔ here⇔))
            (W₁₄²-wf (there⇔ (there⇔ here⇔))) B14x-ty)
          id★↦-ty B14yᵤ-ty B14yₜ-ty B14y-ty)
        id★↦-ty B14ᵤ-ty B14ₜ-ty B14-ty
        (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
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
  ΛΛ-wf : WfWorld (∅ʷ ⊕ X⊑X)
  ΛΛ-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 (∅ʷ ⊕ X⊑X) ≤1-∷[]) (namedᴿ-≤1 (∅ʷ ⊕ X⊑X) ≤1-∷[])
    where
    agree : ∀ {α β} → Paired (∅ʷ ⊕ X⊑X) α β → Agree (∅ʷ ⊕ X⊑X) α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-abst r-here r-here
    agree (inj₂ (there⇔ ()))

  -- Ch B0: Λ⊑Λ under the right's inst cast; the left ν is one-sided
  ch-b0 : ∅ʷ ∣ [] ⊢ Ch-L ⊑ Ch-R ∶ ℕ⊑★
  ch-b0 =
    ·⊑· (ν⊑ (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ)) five⊑

  -- Cg B0: Λ⊑ (Y left-only at X⊑★) under the right's gen and inst casts
  cg-b0 : ∅ʷ ∣ [] ⊢ Cg-L ⊑ Cg-R ∶ ℕ⊑★
  cg-b0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑cast
            (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
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
        (⊑cast
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
      (ν⊑ν (⊑cast (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) genI∘instI-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty C12-ν-ty (Wν , Wν-conv , revX⊑revX refl) (ℕ⇒ℕ ∅ʷ))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- Ch's right-led block X0 (= P3's block, ⊑⟪⟫ with one opening) and Ch B1
  ------------------------------------------------------------------------

  Ch-R₂-state : head (drop 2 (evalTerms 15 Ch-R-⊢)) ≡ just R3′
  Ch-R₂-state = refl

  -- one opening at X⊑X: (aᴸ_ΛY, αᴿ:=★) ∈ ϱˡ in the opened world
  -- W₃ ⊕⁺ X⊑X ^ 0
  ch-x0 : W₃ ∣ [] ⊢ Ch-L ⊑ R3′ ∶ ℕ⊑★
  ch-x0 = p3-inst

  -- ch-x0's premise world is W2⁺ (the same world as C2's X0)
  ch-x0-world : W₃ ⊕⁺ X⊑X ^ 0 ≡ W2⁺
  ch-x0-world = refl

  -- Ch B1: after the left's TyBeta the lexical pair is global,
  -- ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}
  Ch-L₁-state : head (drop 1 (evalTerms 10 Ch-L-⊢)) ≡ just L1′
  Ch-L₁-state = refl

  ch-b1 : W₁ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
  ch-b1 =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
          (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
          bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
      five⊑

  ------------------------------------------------------------------------
  -- C12's right-led block X0: ν⊑ν around ⊑⟪⟫ with one opening (D26)
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
  Wν₂ = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ [])

  Wν₂-conv : ConversionInterior (underν² `ℕ `ℕ W₃) Θ₀ Θ₀ Wν₂
  Wν₂-conv = record
    { conv-left       = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-right      = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
  c12-x0 =
    ·⊑·
      (ν⊑ν
        (⊑cast
          (⊑cast
            (⊑⟪⟫ int-ro₃
              (open-∀ nv-⇒ (∈-⇒ˡ ∈-var) (V-simple (S-Λ (V-simple S-ƛ)))
                ΛidX-⊢ (inst-Λ (V-simple S-ƛ)) refl (open-⊕ r-here)
                open-none)
              W2⁺-wf
              (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
              bR-ty (∀id⊑★ W₃))
            id★↦ᴿ-ty (∀id⊑★ W₃))
          genIᴿ-ty (∀id⊑∀id W₃))
        (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl) (ℕ⇒ℕ W₃))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))


------------------------------------------------------------------------
-- 4b. HEAD's corpus derivations lifted to M: every right term is free
-- of the source-scope mode (`noX?` computes to true), so `lift` applies
------------------------------------------------------------------------

module HeadInM where
  open TIE
  open Rebase

  nx : ∀ {R} → T (noX? R) → NoX R
  nx {R} = noX-sound R

  p1-initᴹ   = lift (nx tt) p1-init
  p1-tybetaᴹ = lift (nx tt) p1-tybeta
  p2-tybetaᴹ = lift (nx tt) p2-tybeta
  p3-instᴹ   = lift (nx tt) p3-inst
  p6-tybetaᴹ = lift (nx tt) p6-tybeta
  cg-b0ᴹ     = lift (nx tt) cg-b0
  cg-x0ᴹ     = lift (nx tt) cg-x0
  c12-b0ᴹ    = lift (nx tt) c12-b0
  c12-x0ᴹ    = lift (nx tt) c12-x0
  c12-b1ᴹ    = lift (nx tt) c12-b1
  c13-b1ᴹ    = lift (nx tt) c13-b1
  c14-b1ᴹ    = lift (nx tt) c14-b1
  c2-b0ᴹ     = lift (nx tt) c2-b0
  c2-x0ᴹ     = lift (nx tt) c2-x0
  c2-b6ᴹ     = lift (nx tt) c2-b6
  c2-b7ᴹ     = lift (nx tt) c2-b7
  ch-b0ᴹ     = lift (nx tt) ch-b0
  ch-x0ᴹ     = lift (nx tt) ch-x0
  ch-b1ᴹ     = lift (nx tt) ch-b1

------------------------------------------------------------------------
-- 6. Example P4 (= cambridge Cf from its second block): every block,
-- derived in H (D11 marks) and lifted to M.  The right's gen wrapper
-- `X! → X?` and its pieces carry `★∼X` / `X∼★` (never `★∼X∼★`).
------------------------------------------------------------------------

module P4 where
  open H
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples using (L4; R4; L4-⊢; R4-⊢)
  open SM.P4 using (nth)

  Ls Rs : List Term
  Ls = evalTerms 11 L4-⊢
  Rs = evalTerms 17 R4-⊢
  open TIE using (idX; revX; Θ₀; L1′; ΔL; ΔLᵢ; bL-ty; revX⊑revX; νL-ty;
                  Wν; Wν-conv)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; Wc-bindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; ℕ⇒ℕ; ∀id⊑★; ∀id⊑∀id; I★⁻; I★gen; Bg; tagX↦;
           id★→)
  open SM.P4 using (νbody-ty; genArg; genArg-ty)
  open import examples.CambridgeExamples using (I★)

  ---------------------------------------------------------------------
  -- The worlds.  Both sides allocate αᴸ:=ℕ, αᴿ:=ℕ (rep. var 0); the
  -- matched TyBetas pair them globally.  The boundary name X is
  -- both-sided at X⊑★ (`Wc² 0`), left-only after a right `−X`
  -- (`Wcᴸ`), and rejoins at the right's `+X` keeping X⊑★ (D15).

  Ξ₄ : RepCtx
  Ξ₄ = bindR `ℕ ∷ []

  ϱ₄ : RepRel
  ϱ₄ = (0 , 0) ∷ []

  W₄ : World ΔL ΔL
  W₄ = Wc⁰ {Ξ₄} {ϱ₄}

  W₄² : World ΔLᵢ ΔLᵢ
  W₄² = Wc² {Ξ₄} {ϱ₄} 0

  W₄ᴸ : World ΔLᵢ ΔL
  W₄ᴸ = Wcᴸ {Ξ₄} {ϱ₄}

  module Wf₄ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World (Ξ₄ ∣ nsL) (Ξ₄ ∣ nsR)
    W = world μ η η′ ϱ₄ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  W₄-wf : WfWorld W₄
  W₄-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₄ [] []↪ []↪

  W₄²-wf : WfWorld W₄²
  W₄²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
    where open Wf₄ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₄ᴸ-wf : WfWorld W₄ᴸ
  W₄ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[])
    where open Wf₄ (X⊑★ ∷ []) (keep []↪) (skip []↪)

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

  unb-int : Interior W₄² unb₀ unb₀ W₄
  unb-int = record
    { int-left   = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  unb-conv : ConversionInterior W₄² unb₀ unb₀ W₄²
  unb-conv = record
    { conv-left       = conversion (conv-unbind (_ , here) conv[])
    ; conv-right      = conversion (conv-unbind (_ , here) conv[])
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
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
    ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    }

  bS : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S}))))

  S⊑S : W₄² ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S = ⟪⟫⊑⟪⟫ unb-int W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (W₄² , unb-conv , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- the left's λx:X. x against the right's λx:★. x (X left-only)
  idX⊑I★ : W₄ᴸ ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξ₄ ϱ₄
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  bI★⁻ : BdyTy ΔLᵢ unb₀ ΔL (★ ⇒ ★) id★→ (★ ⇒ ★)
  bI★⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★⁻}))))

  -- idX ⊑ [−X^α] (λx:★. x) ⟨id(★) → id(★)⟩ at X→X ⊑ ★→★ (X both-sided)
  idX⊑I★⁻ : W₄² ∣ [] ⊢ idX ⊑ I★⁻ ∶ c⊑★² Ξ₄ ϱ₄ 0
  idX⊑I★⁻ = ⊑⟪⟫ (Wc-unbindᴿ v₀) open-none W₄ᴸ-wf idX⊑I★ bI★⁻
    (c⊑★² Ξ₄ ϱ₄ 0)

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
      (⊑cast
        (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
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
        (⊑cast
          (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
          genArg-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty νR₁-ty
        (Wν , Wν-conv , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B2 (2, 2): after both TyBetas.  The right's gen wrapper
  -- `X! → X?` at `^[X:★∼X]`, by ⊑cast at X→X ⊑ ★→★

  bBg : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bBg = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = Bg}))))

  p4-B2 : W₄ ∣ [] ⊢ nth Ls 2 ⊑ nth Rs 2 ∶ ι⊑ι base-ℕ
  p4-B2 =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
        (⊑cast idX⊑I★⁻ tagᵍ-ty (c⊑c² Ξ₄ ϱ₄ 0))
        bL-ty bBg (W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B3 (3, 4): after the left's Wrap and the right's Wrap, CastFun.
  -- The right's X? at `^[X:★∼X]` and its argument's X! at `^[X:X∼★]`
  -- (CastFun flipped the environment), both by ⊑cast reading X ⊑ ★

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

  S⊑S! : W₄² ∣ [] ⊢ S ⊑ S ⟨ X∼★ ∷ [] ∣ tagX ⟩ ∶ X⊑★ here
  S⊑S! = ⊑cast S⊑S tagˣ-ty (X⊑★ here)

  p4-B3 : W₄ ∣ [] ⊢ nth Ls 3 ⊑ nth Rs 4 ∶ ι⊑ι base-ℕ
  p4-B3 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast {p = X⊑★ here} (·⊑· idX⊑I★⁻ S⊑S!) chkᵍ-ty X⊑X)
      bUnsealL₃ bUnsealR₄
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B4 (4, 6): after the left's Beta and the right's Wrap, Beta.  THE
  -- "J" PAIR (SidedMarks.md §4) is the premise `S ⊑ J`: X left-only
  -- after the right's −X, rejoined at the right's +X keeping X⊑★

  J : Term
  J = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ₀ , id★ᶜ ⟫

  bJ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bJ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = J}))))

  bJ⁻ : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bJ⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = J ⟪ unb₀ , id★ᶜ ⟫}))))

  -- the J pair (index X ⊑ ★, X left-only)
  S⊑J : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here
  S⊑J = ⊑⟪⟫ (Wc-bindᴿ v₀ here⇔) open-none W₄²-wf S⊑S! bJ (X⊑★ here)

  p4-B4 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ nth Rs 6 ∶ ι⊑ι base-ℕ
  p4-B4 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast {p = X⊑★ here}
        (⊑⟪⟫ (Wc-unbindᴿ v₀) open-none W₄ᴸ-wf S⊑J bJ⁻ (X⊑★ here))
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
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
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
      ; conv-join-cont  = λ { _ _ () _ }
      ; conv-join-fresh = λ
          { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; conv-mark-left  = λ { _ () _ }
      ; conv-mark-right = λ { _ () _ }
      }

  -- B6 (6, 12): 5 ⊑ 5
  p4-B6 : W₄ ∣ [] ⊢ nth Ls 6 ⊑ nth Rs 12 ∶ ι⊑ι base-ℕ
  p4-B6 = κ⊑κ lit-$ (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- EVERY BLOCK IS AN M-DERIVATION (no right state carries ★∼X∼★)

  p4-B1ᴹ : ∅ʷ ∣ [] ⊢ᴹ L4 ⊑ R4 ∶ ι⊑ι base-ℕ
  p4-B1ᴹ = lift (noX-sound _ tt) p4-B1

  p4-B1′ᴹ : ∅ʷ ∣ [] ⊢ᴹ nth Ls 1 ⊑ nth Rs 1 ∶ ι⊑ι base-ℕ
  p4-B1′ᴹ = lift (noX-sound _ tt) p4-B1′

  p4-B2ᴹ : W₄ ∣ [] ⊢ᴹ nth Ls 2 ⊑ nth Rs 2 ∶ ι⊑ι base-ℕ
  p4-B2ᴹ = lift (noX-sound _ tt) p4-B2

  p4-B3ᴹ : W₄ ∣ [] ⊢ᴹ nth Ls 3 ⊑ nth Rs 4 ∶ ι⊑ι base-ℕ
  p4-B3ᴹ = lift (noX-sound _ tt) p4-B3

  p4-B4ᴹ : W₄ ∣ [] ⊢ᴹ nth Ls 4 ⊑ nth Rs 6 ∶ ι⊑ι base-ℕ
  p4-B4ᴹ = lift (noX-sound _ tt) p4-B4

  p4-B5ᴹ : W₄ ∣ [] ⊢ᴹ nth Ls 5 ⊑ nth Rs 11 ∶ ι⊑ι base-ℕ
  p4-B5ᴹ = lift (noX-sound _ tt) p4-B5

  p4-B6ᴹ : W₄ ∣ [] ⊢ᴹ nth Ls 6 ⊑ nth Rs 12 ∶ ι⊑ι base-ℕ
  p4-B6ᴹ = lift (noX-sound _ tt) p4-B6

  -- the J pair in M, stated directly (its right cast reads X ⊑ ★ at
  -- the rejoined X, whose mode is X∼★)
  S⊑Jᴹ : W₄ᴸ ∣ [] ⊢ᴹ S ⊑ J ∶ X⊑★ here
  S⊑Jᴹ = lift (noX-sound _ tt) S⊑J

------------------------------------------------------------------------
-- 7. The SimBackBlame counterexample (PendingOpenings §5d) under M
------------------------------------------------------------------------

-- only a source-scope tag or check of a name is "bad" now
data RBadˣ : Term → Set where
  rx-tag  : ∀ {U μ k} → μ ∋ˡ k := ★∼X∼★ → RBadˣ (U ⟨ μ ∣ (` k) ! ⟩)
  rx-chk  : ∀ {U μ k ℓ} → μ ∋ˡ k := ★∼X∼★ → RBadˣ (U ⟨ μ ∣ (` k) ？ ℓ ⟩)
  rx-cast : ∀ {R μ c} → RBadˣ R → RBadˣ (R ⟨ μ ∣ c ⟩)
  rx-⟪⟫   : ∀ {R Θ d} → RBadˣ R → RBadˣ (R ⟪ Θ , d ⟫)
  rx-·    : ∀ {F N} → RBadˣ F → RBadˣ (F · N)

rx-bad : ∀ {U μ c} → RBadˣ (U ⟨ μ ∣ c ⟩) → BadCo c ⊎ RBadˣ U
rx-bad (rx-tag _)  = inj₁ b-tag
rx-bad (rx-chk _)  = inj₁ b-chk
rx-bad (rx-cast r) = inj₂ r

-- a derivation of `T ⊑ ★` with T a variable reads X ⊑ ★ there
star-at : ∀ {μ T j} (q : μ ⊢ T ⊑ ★) → T ≡ ` j → ReadsStar q j
star-at (X⊑★ h) refl = rs-var
star-at ★⊑★ ()
star-at (ι⊑★ base-ℕ) ()
star-at (ι⊑★ base-𝔹) ()
star-at (⇒⊑★ _ _) ()
star-at (∀⊑ _ _ _) ()
star-at ∀★⊑★ ()
star-at (∀⊑★ _ _) ()
star-at bot⊑★ ()

opens-lftᴹ : ∀ {Δ Δ⁺ Δ′} {Θ′} {W : World Δ Δ′} {W⁺ : World Δ⁺ Δ′}
    {N A N₀ A₀}
  → LftA N → Opens Θ′ W N A W⁺ N₀ A₀ → LftA N₀
opens-lftᴹ l open-none = l
opens-lftᴹ l (open-∀ _ _ _ _ i _ _ os) = opens-lftᴹ (instx-lft l i) os

-- NO M-DERIVATION, in ANY world, relates a left `LftA` term to a right
-- term whose head path reaches a source-scope tag or check of a name:
-- `⊑cast` of it reads X ⊑ ★ at that name's image (`⊑var`, `star-at`),
-- which `ModeOK` forbids; `cast⊑cast` against a good left cast is
-- refuted by `cc-bad` (atomic types cannot clash).  No world property
-- is used.
no-relᴹ : ∀ {W : World Δ Δ′} {γ : CtxImp W} {L R A A′}
    {q : A ⊑ᵂ⟨ W ⟩ A′}
  → LftA L → RBadˣ R → ¬ (W ∣ γ ⊢ᴹ L ⊑ R ∶ q)
no-relᴹ l (rx-tag h)
  (M.⊑cast {p = p} d (cast-ty (⊢tag-var _ _ _) _) q ⦃ _ , okq ⦄) =
  okq (star-at q (⊑var p)) refl h
no-relᴹ l (rx-tag h) (M.⊑cast d (cast-ty (⊢tag ()) _) q)
no-relᴹ l (rx-chk h)
  (M.⊑cast {p = p} d (cast-ty (⊢check-var _ _ _) _) q ⦃ okp , _ ⦄) =
  okp (star-at p (⊑var q)) refl h
no-relᴹ l (rx-chk h) (M.⊑cast d (cast-ty (⊢check ()) _) q)
no-relᴹ l (rx-cast r) (M.⊑cast d ct q) = no-relᴹ l r d
no-relᴹ {W = W} (la-cast l g) r (M.cast⊑cast {p = p} d ct ct′ q)
  with rx-bad r
... | inj₁ b = cc-bad {V = W} g b ct ct′ p q
... | inj₂ r′ = no-relᴹ l r′ d
no-relᴹ (la-cast l g) r (M.cast⊑ d _ _) = no-relᴹ l r d
no-relᴹ (la-· l) (rx-· r) (M.·⊑· d _) = no-relᴹ l r d
no-relᴹ (la-Λ l) r (M.Λ⊑ _ _ _ _ d _) = no-relᴹ l r d
no-relᴹ (la-ν l) r (M.ν⊑ d _ _ _) = no-relᴹ l r d
no-relᴹ (la-⟪⟫ l) (rx-⟪⟫ r) (M.⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-relᴹ l r d
no-relᴹ (la-⟪⟫ l) r (M.⟪⟫⊑ _ _ d _ _) = no-relᴹ l r d
no-relᴹ l (rx-⟪⟫ r) (M.⊑⟪⟫ _ os _ d _ _) = no-relᴹ (opens-lftᴹ l os) r d

module Cex where
  open import examples.TypeCheck using (tc; tf)
  open SM.Cex
    using (5★; ℕ?; unb₀; sealed5; L₀; R₀; L₆; R₇; L₆-state; R₇-state;
           ΔR; ΔRᵢ; R₇-blames; L₆-never-blames; LH; RH; LH-ends; RH-ends)
  open SM.Cex.InD11
    using (Wαα; Wl; Wj; agree★; int₀; unbind₀-int; unbind₀-conv;
           bSeal; bL₆; bR₇; tagX-ty; id★-ty; ℕ?-ty)

  ---------------------------------------------------------------------
  -- (a) HEAD's one-sided derivation, ported into H (D11 mark fields)

  open TIE using (Θ₀)

  module InH where
    open H

    Wαα-wf : WfWorld Wαα
    Wαα-wf = wf-world joint[] (agree★ r-here r-here refl refl)
      (namedᴸ-≤1 Wαα ≤1-[]) (namedᴿ-≤1 Wαα ≤1-[])

    Wl-wf : WfWorld Wl
    Wl-wf = wf-world (left-only joint[]) (agree★ r-here r-here refl refl)
      (namedᴸ-≤1 Wl ≤1-∷[]) (namedᴿ-≤1 Wl ≤1-[])

    Wj-wf : WfWorld Wj
    Wj-wf = wf-world (both (inj₁ here⇔) joint[])
      (agree★ r-here r-here refl refl)
      (namedᴸ-≤1 Wj ≤1-∷[]) (namedᴿ-≤1 Wj ≤1-∷[])

    IntL : Interior Wαα Θ₀ [] Wl
    IntL = record
      { int-left   = int₀
      ; int-right  = interior changes[]
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , ()) _ _ }
      ; join-fresh = λ { _ () _ }
      ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , ()) _ _ }
      }

    IntR : Interior Wl [] Θ₀ Wj
    IntR = record
      { int-left   = interior changes[]
      ; int-right  = int₀
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
      ; join-fresh = λ
          { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      }

    Wj-unb : Interior Wj unb₀ unb₀ Wαα
    Wj-unb = record
      { int-left   = unbind₀-int
      ; int-right  = unbind₀-int
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , ()) _ _ _ }
      ; join-fresh = λ { () _ _ }
      ; mark-left  = λ { (_ , ()) _ _ }
      ; mark-right = λ { (_ , ()) _ _ }
      }

    Wj-conv-self : ConversionInterior Wj unb₀ unb₀ Wj
    Wj-conv-self = record
      { conv-left       = unbind₀-conv
      ; conv-right      = unbind₀-conv
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
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
      ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                            ; (there ()) _ _ }
      ; conv-mark-right = λ { here here m → m ; here (there ()) _
                            ; (there ()) _ _ }
      }

    five★⊑ : Wαα ∣ [] ⊢ 5★ ⊑ 5★ ∶ ★⊑★
    five★⊑ = cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
      (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★

    sealed⊑sealed : Wj ∣ [] ⊢ sealed5 ⊑ sealed5 ∶ X⊑X
    sealed⊑sealed =
      ⟪⟫⊑⟪⟫ Wj-unb Wαα-wf five★⊑ bSeal bSeal
        (Wj , Wj-conv-self , conv-tail⊑tail (conv-seal⊑seal refl))
        X⊑X

    L₆⊑R₇ : Wαα ∣ [] ⊢ L₆ ⊑ R₇ ∶ ι⊑ι base-ℕ
    L₆⊑R₇ =
      cast⊑cast
        (cast⊑
          (⟪⟫⊑ IntL Wl-wf
            (⊑⟪⟫ IntR open-none Wj-wf
              (⊑cast sealed⊑sealed tagX-ty (X⊑★ here))
              bR₇ (X⊑★ here))
            bL₆ ★⊑★)
          id★-ty ★⊑★)
        ℕ?-ty ℕ?-ty (ι⊑ι base-ℕ)

  -- the step of (a) that M rejects: `⊑cast` of the right's `X!` at
  -- `^[X:★∼X∼★]` reads X ⊑ ★ at the rejoined X (image of right name 0)
  cex-step-rejected :
    ¬ ModeOK Wj (★∼X∼★ ∷ []) {A = ` 0} {A′ = ★} (X⊑★ here)
  cex-step-rejected ok = ok {j = 0} {k = 0} rs-var refl here

  ---------------------------------------------------------------------
  -- (b) NO M-DERIVATION, in any world, relates L₆ to R₇ (so neither
  -- (a) nor the ⟪⟫⊑⟪⟫ derivation through `conv-unseal⊑id★`, nor any
  -- other, survives)

  cex-unrelatedᴹ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W ∣ γ ⊢ᴹ L₆ ⊑ R₇ ∶ p)
  cex-unrelatedᴹ =
    no-relᴹ
      (la-cast (la-cast (la-⟪⟫ (la-⟪⟫ (la-cast la-$ g-ℕ!))) g-id★) g-ℕ?)
      (rx-cast (rx-⟪⟫ (rx-tag here)))

  -- SidedMarks' probe H1 (hide, rebind, escape), likewise
  h1-unrelatedᴹ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W ∣ γ ⊢ᴹ LH ⊑ RH ∶ p)
  h1-unrelatedᴹ =
    no-relᴹ (la-cast (la-⟪⟫ (la-⟪⟫ (la-cast la-$ g-ℕ!))) g-ℕ?)
      (rx-cast (rx-⟪⟫ (rx-⟪⟫ (rx-⟪⟫ (rx-tag here)))))

------------------------------------------------------------------------
-- 8. The tag-only reading (`asStated`: `⊑cast` only, by the coercion's
-- own tags) is NOT closed under reduction.  A right source-scope tag
-- matched by a left tag (`cast⊑cast`, unrestricted) is exposed when the
-- left's tag is consumed by its check and the right's is not.
------------------------------------------------------------------------

lookup-unique : ∀ {A : Set} {xs : List A} {k a b}
  → xs ∋ˡ k := a → xs ∋ˡ k := b → a ≡ b
lookup-unique here      here       = refl
lookup-unique (there h) (there h′) = lookup-unique h h′

crossfree-tag : ∀ {μ k} → μ ∋ˡ k := ★∼X∼★ → ¬ CrossFree μ ((` k) !)
crossfree-tag h (cf-tag (cfg-nv ()))
crossfree-tag h (cf-tag (cfg-var h′ nc)) with lookup-unique h h′
crossfree-tag h (cf-tag (cfg-var h′ ())) | refl

-- under `asStated`, a right source-scope tag faces no `⊑cast`
data RTagˣ : Term → Set where
  rt-tag  : ∀ {U μ k} → μ ∋ˡ k := ★∼X∼★ → RTagˣ (U ⟨ μ ∣ (` k) ! ⟩)
  rt-cast : ∀ {R μ c} → RTagˣ R → RTagˣ (R ⟨ μ ∣ c ⟩)

rt-bad : ∀ {U μ c} → RTagˣ (U ⟨ μ ∣ c ⟩) → BadCo c ⊎ RTagˣ U
rt-bad (rt-tag _)  = inj₁ b-tag
rt-bad (rt-cast r) = inj₂ r

no-relᴬ : ∀ {W : World Δ Δ′} {γ : CtxImp W} {L R A A′}
    {q : A ⊑ᵂ⟨ W ⟩ A′}
  → LftA L → RTagˣ R → ¬ (W ∣ γ ⊢ᴬ L ⊑ R ∶ q)
no-relᴬ l (rt-tag h) (A.⊑cast d ct q ⦃ cf ⦄) = crossfree-tag h cf
no-relᴬ l (rt-cast r) (A.⊑cast d ct q) = no-relᴬ l r d
no-relᴬ {W = W} (la-cast l g) r (A.cast⊑cast {p = p} d ct ct′ q)
  with rt-bad r
... | inj₁ b = cc-bad {V = W} g b ct ct′ p q
... | inj₂ r′ = no-relᴬ l r′ d
no-relᴬ (la-cast l g) r (A.cast⊑ d _ _) = no-relᴬ l r d
no-relᴬ (la-⟪⟫ l) r (A.⟪⟫⊑ _ _ d _ _) = no-relᴬ l r d
no-relᴬ (la-Λ l) r (A.Λ⊑ _ _ _ _ d _) = no-relᴬ l r d
no-relᴬ (la-ν l) r (A.ν⊑ d _ _ _) = no-relᴬ l r d

module AsStated where
  open import examples.TypeCheck using (tc; tf)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)
  open import examples.Eval using (evalTerms)
  open SM.Cex using (5★; unb₀; sealed5; ΔRᵢ)
  open SM.Cex.InD11 using (Wαα; Wj; bSeal)
  open Cex.InH using (Wαα-wf; Wj-unb; Wj-conv-self)
  open A

  tagX chkX : Coercion
  tagX = (` 0) !
  chkX = (` 0) ？ 0

  -- in the joined world Wj (X at X⊑★, D11): the left tags and checks X,
  -- the right tags X and keeps the tag (all at the source-scope mode)
  Lp Rp T! : Term
  T! = sealed5 ⟨ ★∼X∼★ ∷ [] ∣ tagX ⟩
  Lp = T! ⟨ ★∼X∼★ ∷ [] ∣ chkX ⟩
  Rp = T! ⟨ ★∼X∼★ ∷ [] ∣ idᵖ ★ ⟩

  T!-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) tagX (` 0) ★
  T!-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = T!})))

  chk-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) chkX ★ (` 0)
  chk-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = Lp})))

  id-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) (idᵖ ★) ★ ★
  id-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = Rp})))

  five★⊑ : Wαα ∣ [] ⊢ 5★ ⊑ 5★ ∶ ★⊑★
  five★⊑ = cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
    (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★

  sealed⊑sealed : Wj ∣ [] ⊢ sealed5 ⊑ sealed5 ∶ X⊑X
  sealed⊑sealed =
    ⟪⟫⊑⟪⟫ Wj-unb Wαα-wf five★⊑ bSeal bSeal
      (Wj , Wj-conv-self , conv-tail⊑tail (conv-seal⊑seal refl))
      X⊑X

  -- the pre-state is related (only `cast⊑cast`: unrestricted here)
  pre : Wj ∣ [] ⊢ Lp ⊑ Rp ∶ X⊑★ here
  pre = cast⊑cast (cast⊑cast sealed⊑sealed T!-ty T!-ty ★⊑★)
          chk-ty id-ty (X⊑★ here)

  Lp-step : ΔRᵢ ⊢ Lp -→ sealed5 ∣ none
  Lp-step = justStep refl

  Rp-⊢ : ΔRᵢ ∣ [] ⊢ Rp ⦂ ★
  Rp-⊢ = tc

  Unrelᴬ : Term → Term → Set
  Unrelᴬ L R = ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W ∣ γ ⊢ᴬ L ⊑ R ∶ p)

  sealed-lft : LftA sealed5
  sealed-lft = la-⟪⟫ (la-cast la-$ g-ℕ!)

  -- after the left's TagUntag, NO state the right can reach is related
  -- to the left's, in any world: `Sim` fails for `asStated`
  asStated-sim-fails :
    (Wj ∣ [] ⊢ᴬ Lp ⊑ Rp ∶ X⊑★ here)
    × (ΔRᵢ ⊢ Lp -→ sealed5 ∣ none)
    × (∀ {R′} → ΔRᵢ ⊢ Rp -→* R′ → Unrelᴬ sealed5 R′)
  asStated-sim-fails =
    pre , Lp-step ,
    all-reach {P = Unrelᴬ sealed5} 5 Rp-⊢ tt
      ((no-relᴬ sealed-lft (rt-cast (rt-tag here)))
       ∷ (no-relᴬ sealed-lft (rt-tag here)) ∷ [])

  -- under `modes` the pre-state's outer step is already rejected: the
  -- right's `id(★)` at `^[X:★∼X∼★]` reads X ⊑ ★ at the joined X
  pre-rejectedᴹ : ¬ ModeOK Wj (★∼X∼★ ∷ []) {A = ` 0} {A′ = ★} (X⊑★ here)
  pre-rejectedᴹ = Cex.cex-step-rejected

------------------------------------------------------------------------
-- 9. A NEW COUNTEREXAMPLE TO SimBackBlame UNDER `modes`: a gen-mode
-- tag escapes.  The right generalizes λx:★. x by `gen Y. (Y! → id(★))`
-- (the codomain does NOT re-check Y), so the argument's tag `X!`
-- (mode X∼★, from CastFun's flip of ★∼X) leaves the gen scope still
-- tagged, sealed away by the TyBeta boundary's `id(★)`, and the outer
-- `ℕ?` blames.  The left reveals and returns 5.
------------------------------------------------------------------------

module Esc where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)
  open import examples.CambridgeExamples using (I★)
  open TIE using (idX; revX; Θ₀; ΔL; ΔLᵢ)
  open SM.P4 using (nth)

  genE : Coercion
  genE = genᵖ (((` 0) !) ↦ᵖ idᵖ ★)

  cE : Conv
  cE = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))

  LE RE : Term
  LE = (((ν `ℕ · Λ idX ⟨ revX ⟩) · $ 5) ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE = ((ν `ℕ · (I★ ⟨ [] ∣ genE ⟩) ⟨ cE ⟩) · $ 5) ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE-⊢ : empty ∣ [] ⊢ LE ⦂ `ℕ
  LE-⊢ = tc

  RE-⊢ : empty ∣ [] ⊢ RE ⦂ `ℕ
  RE-⊢ = tc

  LEs REs : List Term
  LEs = evalTerms 20 LE-⊢
  REs = evalTerms 30 RE-⊢

  open H
  open P4 using (W₄; W₄²; W₄ᴸ; W₄-wf; W₄²-wf; W₄ᴸ-wf; v₀; Ξ₄; ϱ₄; S; J;
                 S⊑J; bJ⁻; idX⊑I★⁻; id★ᶜ)
  open Rebase using (Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; Wc-bindᴿ;
                     I★⁻; ℕ⇒ℕ)

  -- the left's state 3 and the right's state 5 (after its Beta)
  LE₃ RE₅ : Term
  LE₃ = nth LEs 3
  RE₅ = nth REs 5

  LE₃-is : LE₃ ≡ ((S ⟪ Θ₀ , unseal 0 ⟫) ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  LE₃-is = refl

  -- RE₅ contains P4 B4's J pair VERBATIM
  RE₅-is : RE₅ ≡ (((J ⟪ unbind 0 0 ∷ [] , id★ᶜ ⟫) ⟨ ★∼X ∷ [] ∣ idᵖ ★ ⟩)
                   ⟪ Θ₀ , id★ᶜ ⟫) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE₅-is = refl

  -- the left's +X^α alone: X left-only (X⊑★)
  IntLE : Interior W₄ Θ₀ [] W₄ᴸ
  IntLE = record
    { int-left   = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  bLE : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bLE = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔL} {M = S ⟪ Θ₀ , unseal 0 ⟫}))))

  RE₅ᵢ : Term
  RE₅ᵢ = (J ⟪ unbind 0 0 ∷ [] , id★ᶜ ⟫) ⟨ ★∼X ∷ [] ∣ idᵖ ★ ⟩

  bRE : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bRE = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔL} {M = RE₅ᵢ ⟪ Θ₀ , id★ᶜ ⟫}))))

  idᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) (idᵖ ★) ★ ★
  idᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = RE₅ᵢ})))

  ℕ!-ty : CastTy ΔL [] (`ℕ !) `ℕ ★
  ℕ!-ty = cast-ty (⊢tag g-ℕ) refl

  ℕ?-ty : CastTy ΔL [] (`ℕ ？ 0) ★ `ℕ
  ℕ?-ty = cast-ty (⊢check g-ℕ) refl

  -- THE PAIR: the left's +X^α by ⟪⟫⊑ (X left-only), the right's +X^α
  -- by ⊑⟪⟫ (X rejoins through (α, α), keeping X⊑★, D15), the right's
  -- codomain `id(★)` at `^[X:★∼X]` by ⊑cast, the right's −X^α by ⊑⟪⟫,
  -- and then P4 B4's own J pair `S⊑J`
  esc-late : W₄ ∣ [] ⊢ LE₃ ⊑ RE₅ ∶ ι⊑ι base-ℕ
  esc-late =
    cast⊑cast
      (cast⊑
        (⟪⟫⊑ IntLE W₄ᴸ-wf
          (⊑⟪⟫ (Wc-bindᴿ v₀ here⇔) open-none W₄²-wf
            (⊑cast {p = X⊑★ here}
              (⊑⟪⟫ (Wc-unbindᴿ v₀) open-none W₄ᴸ-wf S⊑J bJ⁻ (X⊑★ here))
              idᵍ-ty (X⊑★ here))
            bRE (X⊑★ here))
          bLE (ι⊑★ base-ℕ))
        ℕ!-ty ★⊑★)
      ℕ?-ty ℕ?-ty (ι⊑ι base-ℕ)

  esc-lateᴹ : W₄ ∣ [] ⊢ᴹ LE₃ ⊑ RE₅ ∶ ι⊑ι base-ℕ
  esc-lateᴹ = lift (noX-sound _ tt) esc-late

  ---------------------------------------------------------------------
  -- The earlier pair (both after TyBeta), through the conversion clause
  -- `conv-unseal⊑id★` at the JOINED X (D11 allows it: X⊑★)

  LE₁ RE₁ : Term
  LE₁ = nth LEs 1
  RE₁ = nth REs 1

  genE-body : Coercion
  genE-body = ((` 0) !) ↦ᵖ idᵖ ★

  bodyᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) genE-body (★ ⇒ ★) (` 0 ⇒ ★)
  bodyᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩})))

  bRE₁ : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ★) cE (`ℕ ⇒ ★)
  bRE₁ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔL} {M = (I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩) ⟪ Θ₀ , cE ⟫}))))

  esc-early : W₄ ∣ [] ⊢ LE₁ ⊑ RE₁ ∶ ι⊑ι base-ℕ
  esc-early =
    cast⊑cast
      (cast⊑
        (·⊑·
          (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
            (⊑cast idX⊑I★⁻ bodyᵍ-ty (⇒⊑⇒ X⊑X (X⊑★ here)))
            TIE.bL-ty bRE₁
            (W₄² , Wc-bind²-conv v₀ here⇔ ,
              conv-tail⊑tail (conv-mid⊑mid
                (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal refl))
                          (conv-unseal⊑id★ here))))
            (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑★ base-ℕ)))
          (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
        ℕ!-ty ★⊑★)
      ℕ?-ty ℕ?-ty (ι⊑ι base-ℕ)

  esc-earlyᴹ : W₄ ∣ [] ⊢ᴹ LE₁ ⊑ RE₁ ∶ ι⊑ι base-ℕ
  esc-earlyᴹ = lift (noX-sound _ tt) esc-early

  ---------------------------------------------------------------------
  -- The runs: the left never blames, the right blames

  NotBlame : Term → Set
  NotBlame N = ∀ {ℓ} → N ≡ blame ℓ → ⊥

  LE-never-blames : ∀ {ℓ} → ¬ (empty ⊢ LE -→* blame ℓ)
  LE-never-blames r = all-reach {P = NotBlame} 20 LE-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ [])
    r refl

  last : List Term → Term
  last []           = $ 0
  last (x ∷ [])     = x
  last (x ∷ y ∷ xs) = last (y ∷ xs)

  RE-blames : last REs ≡ blame 0
  RE-blames = refl

  -- every reachable left state from LE₁ / LE₃ is reachable from LE, so
  -- none blames; the right states RE₁, RE₅ reach `blame ℓ0`
  LE₁-state : nth LEs 1 ≡ LE₁
  LE₁-state = refl

  ---------------------------------------------------------------------
  -- NO CAST CONDITION SEPARATES THIS FROM P4: the decisive premise of
  -- `esc-late` is P4 B4's `S⊑J` itself — same world W₄ᴸ, same terms,
  -- same modes, same index.  The two derivations differ only OUTSIDE:
  -- in P4 the left-only interval comes from the right's −X (matched
  -- +X ⊑ +X boundaries, the tag re-checked by `X?`); here from the
  -- left's own +X (`IntLE`), and the right's +X^α has `id(★)`.
  esc-inner≡p4-inner : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here
  esc-inner≡p4-inner = S⊑J

  LE₃-⊢ : ΔL ∣ [] ⊢ LE₃ ⦂ `ℕ
  LE₃-⊢ = tc

  RE₅-⊢ : ΔL ∣ [] ⊢ RE₅ ⦂ `ℕ
  RE₅-⊢ = tc

  LE₁-⊢ : ΔL ∣ [] ⊢ LE₁ ⦂ `ℕ
  LE₁-⊢ = tc

  RE₁-⊢ : ΔL ∣ [] ⊢ RE₁ ⦂ `ℕ
  RE₁-⊢ = tc

  LE₃-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₃ -→* blame ℓ)
  LE₃-never-blames r = all-reach {P = NotBlame} 20 LE₃-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  LE₁-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₁ -→* blame ℓ)
  LE₁-never-blames r = all-reach {P = NotBlame} 20 LE₁-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  RE₅-blames : last (evalTerms 20 RE₅-⊢) ≡ blame 0
  RE₅-blames = refl

  RE₁-blames : last (evalTerms 20 RE₁-⊢) ≡ blame 0
  RE₁-blames = refl

  -- SimBackBlame FAILS UNDER `modes` (twice): related pairs whose right
  -- run blames while the left never does
  esc-cex : (W₄ ∣ [] ⊢ᴹ LE₃ ⊑ RE₅ ∶ ι⊑ι base-ℕ)
    × (last (evalTerms 20 RE₅-⊢) ≡ blame 0)
    × (∀ {ℓ} → ¬ (ΔL ⊢ LE₃ -→* blame ℓ))
  esc-cex = esc-lateᴹ , RE₅-blames , LE₃-never-blames

  esc-cex-early : (W₄ ∣ [] ⊢ᴹ LE₁ ⊑ RE₁ ∶ ι⊑ι base-ℕ)
    × (last (evalTerms 20 RE₁-⊢) ≡ blame 0)
    × (∀ {ℓ} → ¬ (ΔL ⊢ LE₁ -→* blame ℓ))
  esc-cex-early = esc-earlyᴹ , RE₁-blames , LE₁-never-blames

  -- the source programs themselves are not related: ∀X.X→X ⋢ ∀X.X→★
  -- (so this, like L₆ ⊑ R₇, refutes SimBackBlame, not the DGG)
  esc-source-unrelated : ∀ {μ} → ¬ (μ ⊢ `∀ (` 0 ⇒ ` 0) ⊑ `∀ (` 0 ⇒ ★))
  esc-source-unrelated (∀⊑∀ (⇒⊑⇒ _ (X⊑★ ())))
  esc-source-unrelated (∀⊑ _ _ ())

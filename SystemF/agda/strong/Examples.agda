module strong.Examples where

-- Strong System F v8 — the worked examples of notes/notes-v8.md, as
-- machine-checked traces.  Every conversion the rules build is checked
-- by `refl` against the form the notes write, so the builders, the
-- views, the composition, and the reduction rules are all validated
-- against the design document.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction using (_⨟_; normalize; instReveal)
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- §6  Polymorphic identity
------------------------------------------------------------------------
--   ((Λα,X. λx:X.x) •(X→X)[ℕ]) · 7  —↠  7
------------------------------------------------------------------------

module §6 where

  -- Λα,X. λx:X.x        (the Λ body is a value: the λ)
  idᴾ : Term
  idᴾ = Λ (ƛ ` 0 ∙ ` 0)

  P : Term
  P = (idᴾ • (` 0 ⇒ ` 0) [ `ℕ ]) · ($ 7)

  ⊢P : [] ∣ [] ∣ [] ⊢ P ⦂ `ℕ
  ⊢P = ⊢· (⊢•[] (⊢Λ (Vs Sƛ) (⊢ƛ (wf-var n-here-asgn) (⊢` here))) wf-ℕ) ⊢$

  -- TyBeta's conversion, as the notes write it:
  --   ((seal{-X:=α} ∷ id(X)) → (unseal{+X:=α} ∷ id(ℕ))) ∷ id(ℕ→ℕ)
  c-bnd : Conv
  c-bnd = ((seal 0 (bnd 0) ∷ᶜ id (` 0)) ↦ (unseal 0 (bnd 0) ∷ᶜ id `ℕ))
            ∷ᶜ id (`ℕ ⇒ `ℕ)

  builder-agrees : revTy zero (bnd zero) `ℕ (` 0 ⇒ ` 0) ≡ c-bnd
  builder-agrees = refl

  -- the same conversion after the allocation discharges α to level 0
  c-lvl : Conv
  c-lvl = ((seal 0 (lvl 0) ∷ᶜ id (` 0)) ↦ (unseal 0 (lvl 0) ∷ᶜ id `ℕ))
            ∷ᶜ id (`ℕ ⇒ `ℕ)

  c₁ c₂ : Conv
  c₁ = seal 0 (lvl 0) ∷ᶜ id (` 0)    -- contravariant: ends at the λ's X
  c₂ = unseal 0 (lvl 0) ∷ᶜ id `ℕ     -- covariant

  arr-agrees : arr (` 0) c-lvl ≡ just (c₁ , c₂)
  arr-agrees = refl

  -- the boundary value and the sealed argument are values
  nf-c-lvl : NF c-lvl
  nf-c-lvl = nf-cons (nf-fun (nf-cons nf-seal nf-id irr-id)
                             (nf-cons nf-unseal nf-id irr-id))
                     nf-id irr-id

  val-bndry : Value ((ƛ ` 0 ∙ ` 0) ⟨ c-lvl ⟩)
  val-bndry = V⟨⟩ Sƛ nf-c-lvl (inert-arr (` 0) refl)

  val-sealed-7 : Value (($ 7) ⟨ c₁ ⟩)
  val-sealed-7 = V⟨⟩ S$ (nf-cons nf-seal nf-id irr-id) (inert-var refl)

  -- the merge cancels the pair
  merge-cancels : c₁ ⨟ c₂ ≡ id `ℕ
  merge-cancels = refl

  trace : [] ∣ [] ⊢ P —↠ $ 7 ⊣ (`ℕᴿ ∷ [])
  trace =
    -- TyBeta: the Λ's bound address becomes the ν's
    ξ-·-l (TyBeta (Vs Sƛ) quote-ℕ) then
    -- Alloc: α ≔ ℕ enters the store as level 0
    ξ-·-l Alloc then
    -- Wrap: arr splits the conversion; the argument crosses inward
    Wrap val-bndry (Vs S$) refl then
    -- Beta, under the boundary
    ξ-⟨⟩ refl (Beta val-sealed-7) then
    -- Merge: seal ⨟ unseal cancels to id(ℕ)
    Merge val-sealed-7 then
    -- Const: base(id ℕ) is defined
    Const literal-$ refl then
    done

------------------------------------------------------------------------
-- A variant of the K combinator
------------------------------------------------------------------------
--   g = Λα,X. λx:X. Λγ,Z. λz:Z. x  :  ∀X. X → (∀Z. Z → X)
--   P = (((g •[ℕ]) · 7) •[𝔹]) · true
--
-- A sealed, variable-typed value crosses an uninstantiated `Λ` behind
-- the COLOR WRAP, and is later unsealed: the crossings nest, and plain
-- adjacent fusion cancels them.
------------------------------------------------------------------------

module K where

  -- Λα,X. λx:X. Λγ,Z. λz:Z. x
  g : Term
  g = Λ (ƛ ` 0 ∙ Λ (ƛ ` 0 ∙ ` 1))

  Bₓ : Ty                     -- X → (∀Z. Z → X), under Λα,X
  Bₓ = ` 0 ⇒ `∀ (` 0 ⇒ ` 1)

  ⊢g : [] ∣ [] ∣ [] ⊢ g ⦂ `∀ Bₓ
  ⊢g = ⊢Λ (Vs Sƛ)
        (⊢ƛ (wf-var n-here-asgn)
          (⊢Λ (Vs Sƛ)
            (⊢ƛ (wf-var n-here-asgn) (⊢` (there here)))))

  -- the notes' c_ZX and c_X, and the builder agrees with both
  c_ZX : Conv
  c_ZX = ((hide 1 (bnd 1) ∷ᶜ id (` 0)) ↦ (unseal 1 (bnd 1) ∷ᶜ id `ℕ))
           ∷ᶜ id (` 0 ⇒ `ℕ)

  c_X : Conv
  c_X = ((seal 0 (bnd 0) ∷ᶜ id (` 0)) ↦ (all c_ZX ∷ᶜ id (`∀ (` 0 ⇒ `ℕ))))
          ∷ᶜ id (`ℕ ⇒ `∀ (` 0 ⇒ `ℕ))

  builder-agrees : revTy zero (bnd zero) `ℕ Bₓ ≡ c_X
  builder-agrees = refl

  -- after Alloc (α ≔ ℕ at level 0)
  c_ZX⁰ : Conv
  c_ZX⁰ = ((hide 1 (lvl 0) ∷ᶜ id (` 0)) ↦ (unseal 1 (lvl 0) ∷ᶜ id `ℕ))
            ∷ᶜ id (` 0 ⇒ `ℕ)

  c_X⁰ : Conv
  c_X⁰ = ((seal 0 (lvl 0) ∷ᶜ id (` 0)) ↦ (all c_ZX⁰ ∷ᶜ id (`∀ (` 0 ⇒ `ℕ))))
           ∷ᶜ id (`ℕ ⇒ `∀ (` 0 ⇒ `ℕ))

  W₀ : Term                   -- the sealed 7
  W₀ = ($ 7) ⟨ seal 0 (lvl 0) ∷ᶜ id (` 0) ⟩

  cov : Conv                  -- c_X⁰'s covariant component
  cov = all c_ZX⁰ ∷ᶜ id (`∀ (` 0 ⇒ `ℕ))

  arr-agrees : arr (` 0) c_X⁰ ≡ just (seal 0 (lvl 0) ∷ᶜ id (` 0) , cov)
  arr-agrees = refl

  nf-c_ZX⁰ : NF c_ZX⁰
  nf-c_ZX⁰ = nf-cons (nf-fun (nf-cons nf-hide nf-id irr-id)
                             (nf-cons nf-unseal nf-id irr-id))
                     nf-id irr-id

  nf-c_X⁰ : NF c_X⁰
  nf-c_X⁰ = nf-cons (nf-fun (nf-cons nf-seal nf-id irr-id)
                            (nf-cons (nf-all nf-c_ZX⁰) nf-id irr-id))
                    nf-id irr-id

  val-bndry : Value ((ƛ ` 0 ∙ Λ (ƛ ` 0 ∙ ` 1)) ⟨ c_X⁰ ⟩)
  val-bndry = V⟨⟩ Sƛ nf-c_X⁰ (inert-arr (` 0) refl)

  val-W₀ : Value W₀
  val-W₀ = V⟨⟩ S$ (nf-cons nf-seal nf-id irr-id) (inert-var refl)

  -- Beta's COLOR WRAP: crossing into Z's scope behind an identity
  -- conceal of the Λ's own bound address.
  wrapped : Term
  wrapped = crossΛ W₀ (` 0)

  wrap-shape :
    wrapped ≡ (($ 7) ⟨ seal 0 (lvl 0) ∷ᶜ id (` 0) ⟩)
                ⟨ hide 0 (bnd 0) ∷ᶜ id (` 1) ⟩
  wrap-shape = refl

  -- the value after the first application: a Λ under a boundary
  after-beta : Term
  after-beta = (Λ (ƛ ` 0 ∙ wrapped)) ⟨ cov ⟩

  step₁ : [] ∣ [] ⊢ (g • Bₓ [ `ℕ ]) · ($ 7)
            —↠ after-beta ⊣ (`ℕᴿ ∷ [])
  step₁ =
    ξ-·-l (TyBeta (Vs Sƛ) quote-ℕ) then
    ξ-·-l Alloc then
    Wrap val-bndry (Vs S$) refl then
    ξ-⟨⟩ refl (Beta val-W₀) then
    done

  -- It IS a value: the Λ body is a λ, and `all` is defined on `cov`.
  all-agrees : allView cov ≡ just (c_ZX⁰ ⧺ id (` 0 ⇒ `ℕ))
  all-agrees = refl

  val-after-beta : Value after-beta
  val-after-beta =
    V⟨⟩ (SΛ (Vs Sƛ))
        (nf-cons (nf-all nf-c_ZX⁰) nf-id irr-id)
        (inert-all refl)

------------------------------------------------------------------------
-- The two v7 failure configurations, as v8 REGRESSION TESTS
------------------------------------------------------------------------
-- `notes/old/probes-pre-merge/V7MergeScopeClashProbe.agda` and
-- `notes/probes/V7CancelDriftProbe.agda` (retired) exhibited words that
-- stranded a crossing or a drift.  In v8 the words the rules actually
-- build are NESTED, and adjacent fusion cancels them; the overlapping
-- word normalizes to itself and is excluded by TYPING, not by
-- normalization.
------------------------------------------------------------------------

module Regression where

  -- The K example's merged word: push X, push Z, pop Z, pop X.
  nested : Conv
  nested = seal 0 (lvl 0) ∷ᶜ hide 0 (lvl 1)
             ∷ᶜ show 0 (lvl 1) ∷ᶜ unseal 0 (lvl 0) ∷ᶜ id `ℕ

  nested-cancels : normalize nested ≡ id `ℕ
  nested-cancels = refl

  -- The overlapping word: push X, push Z, pop X, pop Z.
  overlapping : Conv
  overlapping = seal 0 (lvl 0) ∷ᶜ hide 0 (lvl 1)
                  ∷ᶜ unseal 0 (lvl 0) ∷ᶜ show 0 (lvl 1) ∷ᶜ id `ℕ

  overlapping-is-normal : normalize overlapping ≡ overlapping
  overlapping-is-normal = refl

  -- A seal and its unseal separated by a crossing of ANOTHER address
  -- still cancel once the inner crossings have cancelled — the v7
  -- cancel-drift configuration, now harmless.
  drifted : Conv
  drifted = seal 0 (lvl 0) ∷ᶜ hide 0 (lvl 1) ∷ᶜ show 0 (lvl 1)
              ∷ᶜ unseal 0 (lvl 0) ∷ᶜ id (`ℕ ⇒ `ℕ)

  drift-cancels : normalize drifted ≡ id (`ℕ ⇒ `ℕ)
  drift-cancels = refl

------------------------------------------------------------------------
-- §14  Polymorphic argument under `Λ` (the value-restricted form)
------------------------------------------------------------------------
--   ((Λα,X. λf:∀Z.Z→Z. Λβ,Y. λy:Y. (f •(Z→Z)[Y]) · y)
--     •((∀Z.Z→Z)→(∀Y.Y→Y))[ℕ])
--   · (Λγ,Z. λz:Z.z)
--
-- Here `X ∉ B`, so `+X(B)` is the MISS case and the identity crossings
-- appear.  The body is η-expanded (the notes' λ-insertion) so that the
-- inner `Λ` body is a value.
------------------------------------------------------------------------

module §14 where

  ∀ZZ→Z : Ty                  -- ∀Z. Z → Z
  ∀ZZ→Z = `∀ (` 0 ⇒ ` 0)

  B : Ty                      -- (∀Z.Z→Z) → (∀Y.Y→Y), under Λα,X
  B = ∀ZZ→Z ⇒ ∀ZZ→Z

  f-body : Term               -- Λβ,Y. λy:Y. (f •(Z→Z)[Y]) · y
  f-body = Λ (ƛ ` 0 ∙ ((` 1 • (` 0 ⇒ ` 0) [ ` 0 ]) · ` 0))

  F : Term
  F = Λ (ƛ ∀ZZ→Z ∙ f-body)

  idᶻ : Term                  -- Λγ,Z. λz:Z.z
  idᶻ = Λ (ƛ ` 0 ∙ ` 0)

  P : Term
  P = (F • B [ `ℕ ]) · idᶻ

  ⊢P : [] ∣ [] ∣ [] ⊢ P ⦂ ∀ZZ→Z
  ⊢P = ⊢· (⊢•[] (⊢Λ (Vs Sƛ)
                   (⊢ƛ (wf-∀ (wf-⇒ (wf-var n-here-bind) (wf-var n-here-bind)))
                     (⊢Λ (Vs Sƛ)
                       (⊢ƛ (wf-var n-here-asgn)
                         (⊢· (⊢•[] (⊢` (there here)) (wf-var n-here-asgn))
                             (⊢` here))))))
                wf-ℕ)
          (⊢Λ (Vs Sƛ) (⊢ƛ (wf-var n-here-asgn) (⊢` here)))

  -- X ∉ B, so the builder takes the MISS equation: one identity
  -- crossing, exactly as the notes write `+X(B) = id{+X:=α} ∷ id(B)`.
  miss-agrees : revTy zero (bnd zero) `ℕ B ≡ show 0 (bnd 0) ∷ᶜ id B
  miss-agrees = refl

  cᴮ : Conv                   -- after Alloc
  cᴮ = show 0 (lvl 0) ∷ᶜ id B

  -- `arr` peels the crossing into BOTH components, dualizing the
  -- contravariant one: (id{-X:=α} ∷ id(∀Z.Z→Z), id{+X:=α} ∷ id(∀Y.Y→Y))
  arr-agrees :
    arr ∀ZZ→Z cᴮ ≡ just (hide 0 (lvl 0) ∷ᶜ id ∀ZZ→Z
                        , show 0 (lvl 0) ∷ᶜ id ∀ZZ→Z)
  arr-agrees = refl

  c₁ c₂ : Conv
  c₁ = hide 0 (lvl 0) ∷ᶜ id ∀ZZ→Z
  c₂ = show 0 (lvl 0) ∷ᶜ id ∀ZZ→Z

  W : Term                    -- the crossed argument
  W = idᶻ ⟨ c₁ ⟩

  val-W : Value W
  val-W = V⟨⟩ (SΛ (Vs Sƛ)) (nf-cons nf-hide nf-id irr-id) (inert-all refl)

  val-F : Value ((ƛ ∀ZZ→Z ∙ f-body) ⟨ cᴮ ⟩)
  val-F = V⟨⟩ Sƛ (nf-cons nf-show nf-id irr-id) (inert-arr ∀ZZ→Z refl)

  -- Beta's color wrap sends W across the inner Λβ,Y.
  after-beta : Term
  after-beta =
    (Λ (ƛ ` 0 ∙ (((crossΛ W ∀ZZ→Z) • (` 0 ⇒ ` 0) [ ` 0 ]) · ` 0))) ⟨ c₂ ⟩

  trace₁ : [] ∣ [] ⊢ P —↠ after-beta ⊣ (`ℕᴿ ∷ [])
  trace₁ =
    ξ-·-l (TyBeta (Vs Sƛ) quote-ℕ) then
    ξ-·-l Alloc then
    Wrap val-F val-W′ refl then
    ξ-⟨⟩ refl (Beta val-W) then
    done
    where val-W′ = Vs (SΛ (Vs Sƛ))

  -- the crossed argument now carries BOTH crossings, nested: the outer
  -- X-conceal from `arr`, the inner Y-conceal from the color wrap
  wrap-shape :
    crossΛ W ∀ZZ→Z ≡ (idᶻ ⟨ hide 0 (lvl 0) ∷ᶜ id ∀ZZ→Z ⟩)
                       ⟨ hide 0 (bnd 0) ∷ᶜ id ∀ZZ→Z ⟩
  wrap-shape = refl

  -- The result is a VALUE: the value restriction parks the inner
  -- Merge/TyWrap until this Λ is instantiated.
  val-after-beta : Value after-beta
  val-after-beta =
    V⟨⟩ (SΛ (Vs Sƛ)) (nf-cons nf-show nf-id irr-id) (inert-all refl)

  ------------------------------------------------------------------
  -- Instantiating it: •(Y→Y)[𝔹] drives TyWrap
  ------------------------------------------------------------------

  d : Conv                    -- allView c₂, in post-instantiation form
  d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)

  all-agrees : allView c₂ ≡ just d
  all-agrees = refl

  -- THE §14 CHECK: `instReveal` reproduces the notes' conversion
  --   ((-Y:=β ∷ id(Y)) → (+Y:=β ∷ id(𝔹))) ∷ id{+X:=α} ∷ id(𝔹→𝔹)
  -- with the fresh crossing FIRST and the hoisted one reindexed to the
  -- slot the fresh name vacates.
  inst-agrees :
    instReveal zero (bnd zero) `𝔹 d
      ≡ ((seal 0 (bnd 0) ∷ᶜ id (` 0)) ↦ (unseal 0 (bnd 0) ∷ᶜ id `𝔹))
          ∷ᶜ show 0 (lvl 0) ∷ᶜ id (`𝔹 ⇒ `𝔹)
  inst-agrees = refl

  step-tywrap :
    [] ∣ [] ⊢ after-beta • (` 0 ⇒ ` 0) [ `𝔹 ]
      —→ ν `𝔹ᴿ ∙ ((ƛ ` 0 ∙ (((crossΛ W ∀ZZ→Z) • (` 0 ⇒ ` 0) [ ` 0 ]) · ` 0))
                    ⟨ instReveal zero (bnd zero) `𝔹 d ⟩)
      ⊣ []
  step-tywrap = TyWrap val-after-beta refl quote-𝔹

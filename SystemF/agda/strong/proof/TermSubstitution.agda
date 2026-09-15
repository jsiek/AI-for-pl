-- Strong System F v8 — term-variable renaming and substitution, and
-- `Beta`.
--
-- The recipe is the usual one: a map of variable lookups extends under
-- a binder, typing follows the map, substitution is the same with
-- TYPED IMAGES, and `Beta` is the single-variable instance.
--
-- THE TWIST is the color wrap.  Crossing a `Λ` does not merely reindex
-- the images: `underΛ` WRAPS each value image in a boundary
--
--     crossΛ V A = (renAddrᴹ suc V) ⟨ hide 0 (bnd 0) ∷ᶜ id (⇑ᵗ A) ⟩
--
-- and shifts its type to `⇑ᵗ A`, so that the value's own nodes never
-- enter the new name's scope — that is what makes color preservation
-- hold for `Beta`.  So the substitution invariant must be closed under
-- `underΛ`, and `underΛ-ok` is where the wrap's typing is discharged:
-- the boundary's interior is the context WITHOUT the crossing
-- assignment, the conversion is the crossing itself, and the image
-- moves under one new address binder.  Crossing a `ν` is the same
-- story with no name and no wrap (`underν`).
--
-- The module is parameterized by ADDRESS WEAKENING of terms — pushing
-- one address entry — which is the address-universe instance of the
-- same recipe.  It is isolated here because its `_∋r_:=_` component
-- needs the store invariant `StoreOk` (a stored representation mentions
-- only levels, so weakening does not shift it).
module strong.proof.TermSubstitution where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.proof.ArrTyping using
  (Renamesᵗ; ext-renames; wf-ren; pop-renames; wf-shift)
open import strong.proof.AddrWeaken using
  (⊢-ren; ren-wk; ren-stk; wfᵗ-ren; suc-inj)

------------------------------------------------------------------------
-- The color wrap, and crossing a `ν`
------------------------------------------------------------------------

-- Weakening by one BASE entry.  With the context split, this extends
-- the base and leaves the stack's STRUCTURE alone — so every name
-- lookup and every pop is untouched, which is exactly what the old
-- flat contexts could not deliver.  What still moves is the addresses
-- the stack's `asgn` entries STORE, and the bound addresses in the
-- term, both by the cutoff renaming at the stack's binder count.

shiftAtᵇ : ℕ → Renameᵇ
shiftAtᵇ zero = suc
shiftAtᵇ (suc k) = extᵇ (shiftAtᵇ k)

-- The color wrap and the `ν` crossing both come down to ONE base
-- weakening, `proof.AddrWeaken.⊢-ren`: the new binder goes on the base,
-- the stack rides along by `⤒`, and the boundaries inside the value
-- keep their crossings.

module Proof where

  -- The `⤒`'d stack assigns no name to the base's NEWEST address: every
  -- assignment it carries was shifted, and a `bind` names a stack
  -- address.
  ⤒-fresh : ∀ {Ss Bs} → NotAssigned (⤒ Ss ∥ Bs) (bse zero)
  ⤒-fresh {[]} ()
  ⤒-fresh {bind ∷ Ss} (n-skip-bind-e p) = ⤒-fresh p
  ⤒-fresh {asgn (lvl ℓ) ∷ Ss} (n-skip-asgn p) = ⤒-fresh p
  ⤒-fresh {asgn (bnd i) ∷ Ss} (n-skip-asgn p) = ⤒-fresh p
  ⤒-fresh {asgn (bse j) ∷ Ss} (n-skip-asgn p) = ⤒-fresh p

  nuWeaken : ∀ {Sg Ss Bs Γ M A e} → StoreOk Sg
    → Sg ∣ (Ss ∥ Bs) ∣ Γ ⊢ M ⦂ A
    → Sg ∣ (⤒ Ss ∥ e ∷ Bs) ∣ Γ ⊢ renBseᴹ suc M ⦂ A
  nuWeaken sok ⊢M = ⊢-ren suc-inj (ren-wk sok) ⊢M



  ----------------------------------------------------------------------
  -- Term-variable renaming
  ----------------------------------------------------------------------

  ∋-⤊ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⤊ Γ ∋ x ⦂ ⇑ᵗ A
  ∋-⤊ here = here
  ∋-⤊ (there p) = there (∋-⤊ p)

  ∋-⤊-inv : ∀ {Γ x A} → ⤊ Γ ∋ x ⦂ A
    → Σ[ B ∈ Ty ] ((Γ ∋ x ⦂ B) × (A ≡ ⇑ᵗ B))
  ∋-⤊-inv {Γ = B ∷ Γ} here = B , here , refl
  ∋-⤊-inv {Γ = B ∷ Γ} (there p) with ∋-⤊-inv p
  ∋-⤊-inv {Γ = B ∷ Γ} (there p) | C , q , refl = C , there q , refl

  Renamesⁿ : (ℕ → ℕ) → Ctx → Ctx → Set
  Renamesⁿ ρ Γ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

  extⁿ-renames : ∀ {ρ Γ Γ′ B} → Renamesⁿ ρ Γ Γ′
    → Renamesⁿ (extⁿ ρ) (B ∷ Γ) (B ∷ Γ′)
  extⁿ-renames r here = here
  extⁿ-renames r (there p) = there (r p)

  ⤊-renames : ∀ {ρ Γ Γ′} → Renamesⁿ ρ Γ Γ′ → Renamesⁿ ρ (⤊ Γ) (⤊ Γ′)
  ⤊-renames r p with ∋-⤊-inv p
  ⤊-renames r p | C , q , refl = ∋-⤊ (r q)

  -- Values are closed under renaming: a boundary is left alone, and
  -- every other value former recurses.
  mutual
    ren-simple : ∀ {ρ V} → Simple V → Simple (renⁿ ρ V)
    ren-simple S$ = S$
    ren-simple S# = S#
    ren-simple Sƛ = Sƛ
    ren-simple (SΛ v) = SΛ (ren-value v)

    ren-value : ∀ {ρ V} → Value V → Value (renⁿ ρ V)
    ren-value (Vs s) = Vs (ren-simple s)
    ren-value (V⟨⟩ s nf inert) = V⟨⟩ s nf inert

  ren-⊢ : ∀ {Sg Δ Γ Γ′ ρ M A} → Renamesⁿ ρ Γ Γ′
    → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A → Sg ∣ Δ ∣ Γ′ ⊢ renⁿ ρ M ⦂ A
  ren-⊢ r (⊢` x) = ⊢` (r x)
  ren-⊢ r ⊢$ = ⊢$
  ren-⊢ r ⊢# = ⊢#
  ren-⊢ r (⊢⊕ l m) = ⊢⊕ (ren-⊢ r l) (ren-⊢ r m)
  ren-⊢ r (⊢ƛ wf body) = ⊢ƛ wf (ren-⊢ (extⁿ-renames r) body)
  ren-⊢ r (⊢· l m) = ⊢· (ren-⊢ r l) (ren-⊢ r m)
  ren-⊢ r (⊢Λ v body) = ⊢Λ (ren-value v) (ren-⊢ (⤊-renames r) body)
  ren-⊢ r (⊢•[] l wf) = ⊢•[] (ren-⊢ r l) wf
  ren-⊢ r (⊢ν wf body) = ⊢ν wf (ren-⊢ r body)
  ren-⊢ r (⊢⟨⟩ nf body conv) = ⊢⟨⟩ nf body conv

  -- A renaming that does nothing leaves the term alone (the usual
  -- identity law of the renaming algebra).
  extⁿ-id : ∀ {ρ} → (∀ x → ρ x ≡ x) → ∀ x → extⁿ ρ x ≡ x
  extⁿ-id h zero = refl
  extⁿ-id h (suc x) = cong suc (h x)

  renⁿ-id : ∀ {ρ} → (∀ x → ρ x ≡ x) → ∀ M → renⁿ ρ M ≡ M
  renⁿ-id h (` x) = cong `_ (h x)
  renⁿ-id h ($ n) = refl
  renⁿ-id h (# b) = refl
  renⁿ-id h (M ⊕[ p ] N) = cong₂ _⊕[ p ]_ (renⁿ-id h M) (renⁿ-id h N)
  renⁿ-id h (ƛ A ∙ N) = cong (ƛ A ∙_) (renⁿ-id (extⁿ-id h) N)
  renⁿ-id h (L · M) = cong₂ _·_ (renⁿ-id h L) (renⁿ-id h M)
  renⁿ-id h (Λ V) = cong Λ_ (renⁿ-id h V)
  renⁿ-id h (L • B [ A ]) = cong (λ z → z • B [ A ]) (renⁿ-id h L)
  renⁿ-id h (ν R ∙ M) = cong (ν R ∙_) (renⁿ-id h M)
  renⁿ-id h (M ⟨ c ⟩) = refl

  ⊢-cast : ∀ {Sg Δ Γ M N A} → M ≡ N → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A
    → Sg ∣ Δ ∣ Γ ⊢ N ⦂ A
  ⊢-cast refl t = t

  -- the weakening the images need: a CLOSED term types anywhere
  weaken-[] : ∀ {Sg Δ Γ M A} → Sg ∣ Δ ∣ [] ⊢ M ⦂ A → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A
  weaken-[] {M = M} ⊢M =
    ⊢-cast (renⁿ-id (λ x → refl) M) (ren-⊢ (λ ()) ⊢M)

  ----------------------------------------------------------------------
  -- Substitution, with typed images
  ----------------------------------------------------------------------

  data ImgOk (Sg : Store) (Δ : Ctxᵗ) (Γ′ : Ctx) : Img → Ty → Set where
    img-var : ∀ {x A} → Γ′ ∋ x ⦂ A → ImgOk Sg Δ Γ′ (ivar x) A
    -- a value image is CLOSED, and carries its type's well-formedness:
    -- the color wrap needs it, and `⊢ƛ` supplies it at the `Beta` site
    img-val : ∀ {V A} → Δ ⊢ᵗ A → Sg ∣ Δ ∣ [] ⊢ V ⦂ A
            → ImgOk Sg Δ Γ′ (ival V A) A

  imgTm-typing : ∀ {Sg Δ Γ′ img A} → ImgOk Sg Δ Γ′ img A
    → Sg ∣ Δ ∣ Γ′ ⊢ imgTm img ⦂ A
  imgTm-typing (img-var x) = ⊢` x
  imgTm-typing (img-val wf ⊢V) = weaken-[] ⊢V

  Substⁿ : Store → Ctxᵗ → Ctx → Ctx → (ℕ → Img) → Set
  Substⁿ Sg Δ Γ Γ′ σ = ∀ {x A} → Γ ∋ x ⦂ A → ImgOk Sg Δ Γ′ (σ x) A

  extImg-ok : ∀ {Sg Δ Γ Γ′ σ B} → Substⁿ Sg Δ Γ Γ′ σ
    → Substⁿ Sg Δ (B ∷ Γ) (B ∷ Γ′) (extImg σ)
  extImg-ok s here = img-var here
  extImg-ok {σ = σ} s {x = suc x} (there p) with σ x | s p
  extImg-ok {σ = σ} s {x = suc x} (there p) | ivar y | img-var q =
    img-var (there q)
  extImg-ok {σ = σ} s {x = suc x} (there p) | ival V A | img-val wf ⊢V =
    img-val wf ⊢V

  ----------------------------------------------------------------------
  -- THE COLOR WRAP
  ----------------------------------------------------------------------
  -- Under a `Λ`, the context gains an address binder and a CROSSING
  -- ASSIGNMENT naming it.  A value image must therefore cross into that
  -- name's scope, and `crossΛ` sends it across a boundary whose
  -- conversion is exactly that crossing — so the value's own nodes stay
  -- outside the new name's scope, which is what color preservation
  -- needs.  The boundary's interior is the context WITHOUT the
  -- assignment, which is where the address-weakened value lives.

  -- Well-formedness of a TYPE travels along any map of NAME lookups;
  -- a base renaming is one (`proof.AddrWeaken.wfᵗ-ren`), since it
  -- leaves names alone entirely.

  -- the `Λ` pushes to BOTH halves: its address onto the base, the
  -- crossing assignment naming it onto the stack.
  Λctx : Ctxᵗ → Ctxᵗ
  Λctx (Ss ∥ Bs) = asgn (bse zero) ∷ ⤒ Ss ∥ addr ∷ Bs

  crossΛ-typing : ∀ {Sg Ss Bs Γ′ V A} → StoreOk Sg
    → (Ss ∥ Bs) ⊢ᵗ A → Sg ∣ (Ss ∥ Bs) ∣ [] ⊢ V ⦂ A
    → (Λctx (Ss ∥ Bs) ⊢ᵗ ⇑ᵗ A)
      × (Sg ∣ Λctx (Ss ∥ Bs) ∣ Γ′ ⊢ crossΛ V A ⦂ ⇑ᵗ A)
  crossΛ-typing sok wf ⊢V =
      wf-shift pop-here wfᵢ
    , ⊢⟨⟩ (nf-cons nf-hide nf-id irr-id)
          (nuWeaken sok ⊢V)
          (conv-cons (conv-hide wfᵢ pop-here ⤒-fresh)
                     (conv-id (wf-shift pop-here wfᵢ)))
    where
    wfᵢ = wfᵗ-ren (ren-stk (ren-wk sok)) wf

  -- Crossing a `Λ`: the images cross behind the color wrap, and the
  -- term context's types shift by the one new name.
  underΛ-ok : ∀ {Sg Δ Γ Γ′ σ} → StoreOk Sg → Substⁿ Sg Δ Γ Γ′ σ
    → Substⁿ Sg (Λctx Δ) (⤊ Γ) (⤊ Γ′) (λ x → underΛ (σ x))
  underΛ-ok {σ = σ} sok s {x = x} p with ∋-⤊-inv p
  underΛ-ok {σ = σ} sok s {x = x} p | B , q , refl with σ x | s q
  underΛ-ok {σ = σ} sok s {x = x} p | B , q , refl | ivar y | img-var r =
    img-var (∋-⤊ r)
  underΛ-ok {σ = σ} sok s {x = x} p | B , q , refl | ival V A | img-val wf ⊢V
    with crossΛ-typing sok wf ⊢V
  underΛ-ok {σ = σ} sok s {x = x} p | B , q , refl | ival V A | img-val wf ⊢V
    | wfΛ , ⊢wrap = img-val wfΛ ⊢wrap

  -- Crossing a `ν`: an address binder and no name, so the images only
  -- move under one address and the types do not shift.
  underν-ok : ∀ {Sg Ss Bs Γ Γ′ σ R} → StoreOk Sg → Substⁿ Sg (Ss ∥ Bs) Γ Γ′ σ
    → Substⁿ Sg (⤒ Ss ∥ nuBind R ∷ Bs) Γ Γ′ (λ x → underν (σ x))
  underν-ok {σ = σ} sok s {x = x} p with σ x | s p
  underν-ok {σ = σ} sok s {x = x} p | ivar y | img-var r = img-var r
  underν-ok {σ = σ} sok s {x = x} p | ival V A | img-val wf ⊢V =
    img-val (wfᵗ-ren (ren-stk (ren-wk sok)) wf) (nuWeaken sok ⊢V)

  ----------------------------------------------------------------------
  -- Substitution preserves typing
  ----------------------------------------------------------------------

  mutual
    subst-simple : ∀ {σ V} → Simple V → Simple (substᵐ σ V)
    subst-simple S$ = S$
    subst-simple S# = S#
    subst-simple Sƛ = Sƛ
    subst-simple (SΛ v) = SΛ (subst-value v)

    subst-value : ∀ {σ V} → Value V → Value (substᵐ σ V)
    subst-value (Vs s) = Vs (subst-simple s)
    subst-value (V⟨⟩ s nf inert) = V⟨⟩ s nf inert

  subst-⊢ : ∀ {Sg Δ Γ Γ′ σ M A} → StoreOk Sg → Substⁿ Sg Δ Γ Γ′ σ
    → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A → Sg ∣ Δ ∣ Γ′ ⊢ substᵐ σ M ⦂ A
  subst-⊢ sok s (⊢` x) = imgTm-typing (s x)
  subst-⊢ sok s ⊢$ = ⊢$
  subst-⊢ sok s ⊢# = ⊢#
  subst-⊢ sok s (⊢⊕ l m) = ⊢⊕ (subst-⊢ sok s l) (subst-⊢ sok s m)
  subst-⊢ sok s (⊢ƛ wf body) = ⊢ƛ wf (subst-⊢ sok (extImg-ok s) body)
  subst-⊢ sok s (⊢· l m) = ⊢· (subst-⊢ sok s l) (subst-⊢ sok s m)
  subst-⊢ sok s (⊢Λ v body) =
    ⊢Λ (subst-value v) (subst-⊢ sok (underΛ-ok sok s) body)
  subst-⊢ sok s (⊢•[] l wf) = ⊢•[] (subst-⊢ sok s l) wf
  subst-⊢ sok s (⊢ν wf body) = ⊢ν wf (subst-⊢ sok (underν-ok sok s) body)
  subst-⊢ sok s (⊢⟨⟩ nf body conv) = ⊢⟨⟩ nf body conv

  ----------------------------------------------------------------------
  -- Beta
  ----------------------------------------------------------------------

  single-ok : ∀ {Sg Δ Γ′ V A} → Δ ⊢ᵗ A → Sg ∣ Δ ∣ [] ⊢ V ⦂ A
    → Substⁿ Sg Δ (A ∷ Γ′) Γ′ (singleImgEnv V A)
  single-ok wf ⊢V here = img-val wf ⊢V
  single-ok wf ⊢V (there p) = img-var p

  preserve-Beta : ∀ {Sg Δ A N W B} → StoreOk Sg
    → Sg ∣ Δ ∣ [] ⊢ (ƛ A ∙ N) · W ⦂ B
    → Sg ∣ Δ ∣ [] ⊢ N [ W ∶ A ]ᵐ ⦂ B
  preserve-Beta sok (⊢· (⊢ƛ wfA ⊢N) ⊢W) = subst-⊢ sok (single-ok wfA ⊢W) ⊢N

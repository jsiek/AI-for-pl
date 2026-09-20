module strong.proof.IdLayer where

-- THE ID-LAYER FACTS — what makes IdPush and CancelR legitimate.
--
-- §1  the pushed name is ALREADY WRITTEN in the inner `id (` X)`
--     conversion (idpush-name), and the same argument fixes CancelR's
--     two names (cancel-name): typing forces X and Y to name ONE
--     representation variable, X across Θ₁'s bind block.  Neither rule
--     invents a variable, and neither needs an equation as a premise.
-- §2  `unseal` is the ONLY active conversion an id-(` X) layer can ever
--     meet, so the id-base branch of `Active` is vacuous for these rules.
-- §3  the naked drop `V ⟪ Θ , id A ⟫ -→ V` — the door, closed: it is sound
--     exactly when the boundary changes NO FRAME.
--
-- WHAT THE TWO UNIVERSES CHANGE (2026-09-19).  §1 used to be an EQUATION
-- between ordinary de Bruijn indices, `X ≡ numBinds Θ₁ + Y`, because one
-- universe carried both roles and `shiftBy` moved a name.  Here the two
-- conversions are read on DIFFERENT name maps that can reorder relative to
-- each other, so no equation between X and Y is available or wanted: the
-- fact is one universe up, about the REPRESENTATION VARIABLE each name
-- denotes.  That is the form `proof/MoveScope.preserve-IdPush` consumes.
--
-- WHAT WAS DELETED.  `convCtx-lock` — "a conceal is invisible to the
-- conversion context" as an EQUALITY between computed contexts — has no
-- two-universe counterpart.  The relational statement of the same fact is
-- `conv-lock` itself (strong.CtxMorph §3), which skips a lock outright.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.proof.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.proof.Canonical
  using (same-base-target; sameTyExt-base-target)
open import strong.proof.Preserve using (shiftRep-var)

------------------------------------------------------------------------
-- §1  THE NAMES ARE FORCED
------------------------------------------------------------------------

-- The heart of both cases, on the two `env` premises alone.  The inner
-- boundary's exterior type B is read at the OUTER interior; its own
-- conversion spells it `` ` X `` across Θ₁'s bind block, and the outer
-- conversion spells it `` ` Y ``.  So X denotes `n + α` exactly when Y
-- denotes α.
-- Stated on NAME MAPS: like `_⊢_≈_⊣_` itself, the judgement reaches a
-- context only through the `names` projection, which does not determine
-- it, so the contexts are not inferable from the two premises.
push-rep : (n : ℕ) {ηᵢ η₁ᶜ ηᶜ : TyCtx} {B : Ty} {X Y : ℕ}
  → ∃[ R ] ((ηᵢ ⊢ B ~ R) × (η₁ᶜ ⊢ ` X ~ shiftRep n R))
  → ∃[ R ] ((ηᵢ ⊢ B ~ R) × (ηᶜ ⊢ ` Y ~ R))
    ---------------------------------------------------------------
  → Σ[ α ∈ RVar ] ((ηᶜ ∋ˡ Y := α) × (η₁ᶜ ∋ˡ X := n + α))
push-rep n {η₁ᶜ = η₁ᶜ} {X = X} (R , p , q) (R′ , p′ , same-var d)
  with same-rep-unique p p′
push-rep n {η₁ᶜ = η₁ᶜ} {X = X} (R , p , q) (R′ , p′ , same-var {α = α} d)
  | refl
  with subst (λ T → η₁ᶜ ⊢ ` X ~ T) (shiftRep-var n α) q
... | same-var d′ = α , d , d′

-- In any typed id-layer under an `unseal`, the inner `id (` X)`'s variable
-- NAMES the pushed conversion's binder, one bind block in.  IdPush
-- therefore invents no representation variable.
idpush-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    --------------------------------------------------------------------
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ α ∈ RVar ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
        × (Δᶜ ∋ᵗ Y := α)
        × (Δ₁ᶜ ∋ᵗ X := numBinds Θ₁ + α))
idpush-name {Θ₁ = Θ₁}
    (env mw₂ (env mw₁ ⊢V (conv-idv tvX) sm₁ se₁ wB)
         (conv-unseal dY) sm₂ se₂ wE)
  with push-rep (numBinds Θ₁) se₁ sm₂
... | α , d , d′ =
  _ , _ , _ , α
  , mw-interior mw₂ , mw-conversion mw₂ , mw-conversion mw₁
  , d , d′

-- THE SAME FACT FOR CANCEL.  The inner `seal X` has the same TARGET
-- spelling `` ` X ``, so the same two premises settle it, and CancelR
-- needs no premise relating its two names either.
cancel-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    --------------------------------------------------------------------
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ α ∈ RVar ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
        × (Δᶜ ∋ᵗ Y := α)
        × (Δ₁ᶜ ∋ᵗ X := numBinds Θ₁ + α))
cancel-name {Θ₁ = Θ₁}
    (env mw₂ (env mw₁ ⊢V (conv-seal dX) sm₁ se₁ wB)
         (conv-unseal dY) sm₂ se₂ wE)
  with push-rep (numBinds Θ₁) se₁ sm₂
... | α , d , d′ =
  _ , _ , _ , α
  , mw-interior mw₂ , mw-conversion mw₂ , mw-conversion mw₁
  , d , d′

------------------------------------------------------------------------
-- §2  THE ONLY ACTIVE CONVERSION AN ID-LAYER MEETS IS `unseal`
------------------------------------------------------------------------

-- A base ordinary type denotes a base representation type.
same-base-source : ∀ {η A R} → η ⊢ A ~ R → Base A → Base R
same-base-source same-ℕ base-ℕ = base-ℕ
same-base-source same-𝔹 base-𝔹 = base-𝔹

-- A wrapper whose conversion is `id (` X)` has a VARIABLE exterior type,
-- and an outer `id A` conversion at a BASE type demands a base interior.
-- So the id-base branch of `Active` is unreachable over this LHS.
--
-- The argument runs through the representation universe rather than
-- through `shiftBy`: the outer `id A` forces the inner boundary's exterior
-- type to be a base type, and `SameTyExt` carries a base type to a base
-- type across the bind block — but the inner conversion's target is a
-- variable.
outer-id-base-untypeable : ∀ {Δ Γ V Θ₁ Θ₂ X A C} → Base A
  → ¬ (Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , id A ⟫ ⦂ C)
outer-id-base-untypeable {Θ₁ = Θ₁} bA
    (env {Δᵢ = Δᵢ} mw₂
         (env {Δᶜ = Δ₁ᶜ} mw₁ ⊢V (conv-idv tvX) sm₁ se₁ wB)
         (conv-id bA′) (R , p , q) se₂ wE)
  with sameTyExt-base-target {n = numBinds Θ₁} {Δ = Δᵢ} {Δ′ = Δ₁ᶜ}
         (same-base-target p (same-base-source q bA′)) se₁
... | ()
outer-id-base-untypeable () (env _ (env _ _ (conv-idv _) _ _ _)
                                 (conv-idv _) _ _ _)

-- A boundary can never conceal the name its OWN conversion cites —
-- `value-var-visible` (strong.Terms) says a value's variable type is
-- visible on the value's exterior context, because `env`'s last conjunct
-- checks it there.  So "Θ₁ locks Y while the conversion cites Y" is
-- untypeable.

------------------------------------------------------------------------
-- §3  THE NAKED DROP — the door, closed
------------------------------------------------------------------------

-- `V ⟪ Θ , id A ⟫ -→ V` is unsound because V is typed on the morphism's
-- INTERIOR, not on Δ.  A concrete failing instance: the boundary's
-- conversion cites an ordinary name that Δ does not have at all.

Δₑ : Ctxᵗ
Δₑ = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

Δₑ-no-1 : ∀ {α} → Δₑ ∋ᵗ 1 := α → ⊥
Δₑ-no-1 (there ())

naked-drop-trap : ∀ {C} →
  ¬ (Δₑ ∣ [] ⊢ ($ 7) ⟪ morph [] [] , seal 1 ⟫ ⦂ C)
naked-drop-trap (env mwᵥ ⊢$ ⊢c smᵢ smₑ wE)
  with mw-conversion mwᵥ
naked-drop-trap (env mwᵥ ⊢$ (conv-seal (α , R , name , rep , same)) smᵢ smₑ wE)
  | conversion conv[] = Δₑ-no-1 name

------------------------------------------------------------------------
-- §3b  THE SOUND SIDE CONDITION
------------------------------------------------------------------------

-- The drop is sound exactly when the boundary changes NO FRAME.  Then both
-- induced contexts are the exterior itself and the identity conversion
-- fixes the type, so the interior derivation IS the exterior one.

extendReps-[] : (Γ : Ctxᵗ) → extendReps [] Γ ≡ Γ
extendReps-[] (Ξ ∣ Δ) = cong (Ξ ∣_) (shiftRVars-0 Δ)

empty-interior : (Γ : Ctxᵗ) → Γ ⊢ⁱ morph [] [] ⇒ extendReps [] Γ
empty-interior Γ = interior changes[]

empty-conversion : (Γ : Ctxᵗ) → Γ ⊢ᶜ morph [] [] ⇒ extendReps [] Γ
empty-conversion Γ = conversion conv[]

drop-empty-frame : ∀ {Δ Γ V A B}
  → Δ ∣ Γ ⊢ V ⟪ morph [] [] , id A ⟫ ⦂ B
    ------------------------------------
  → Δ ∣ [] ⊢ V ⦂ B
drop-empty-frame {Δ = Δ} {V = V} (env mwᵥ ⊢V ⊢c (R , pᵢ , qᵢ) (S , pₑ , qₑ) wE)
  with trans (interior-functional (mw-interior mwᵥ) (empty-interior Δ))
             (extendReps-[] Δ)
     | trans (conversion-functional (mw-conversion mwᵥ) (empty-conversion Δ))
             (extendReps-[] Δ)
... | refl | refl
  with same-rep-unique qᵢ (subst (λ T → names Δ ⊢ T ~ S)
                                 (sym (conv-id-refl ⊢c)) qₑ)
... | refl =
  subst (λ T → Δ ∣ [] ⊢ V ⦂ T)
        (same-target-unique (name-fn (mw-exterior mwᵥ)) pᵢ pₑ)
        ⊢V

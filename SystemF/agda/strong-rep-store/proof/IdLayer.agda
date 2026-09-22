module strong-rep-store.proof.IdLayer where

-- THE ID-LAYER FACTS — what makes IdPush and CancelR legitimate.
--
-- §1  the pushed name is ALREADY WRITTEN in the inner `id (` X)`
--     conversion (idpush-name), and the same argument fixes CancelR's
--     two names (cancel-name): typing forces X and Y to name ONE
--     representation variable.  Neither rule invents a variable, and
--     neither needs an equation as a premise.
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
-- WHAT THE STORE CHANGES (2026-09-22).  The two names denote the SAME
-- representation variable, not one `numBinds Θ₁` above the other: a
-- boundary scope carries no bind block, so there is no prefix between the
-- inner conversion context and the outer one.  `push-rep` therefore lost
-- its depth argument and its `shiftRep` bookkeeping, and both `env`
-- comparisons it reads are the one relation `_⊢_≈_⊣_` at equal depth.
--
-- WHAT WAS DELETED.  `convCtx-lock` — "a conceal is invisible to the
-- conversion context" as an EQUALITY between computed contexts — has no
-- two-universe counterpart.  The relational statement of the same fact is
-- `conv-lock` itself (strong-rep-store.Boundary §3), which skips a lock
-- outright.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.proof.Canonical
  using (same-base-target; ≈-base-target)

------------------------------------------------------------------------
-- §1  THE NAMES ARE FORCED
------------------------------------------------------------------------

-- The heart of both cases, on the two `env` premises alone.  The inner
-- boundary's exterior type B is read at the OUTER interior; its own
-- conversion spells it `` ` X `` and the outer conversion spells it
-- `` ` Y ``.  Since the store experiment there is no bind prefix between
-- the two readings, so the two names denote the SAME representation
-- variable — the old `X ↦ numBinds Θ₁ + α` offset is gone with the binds.
-- Stated on NAME MAPS: like `_⊢_≈_⊣_` itself, the judgement reaches a
-- context only through the `names` projection, which does not determine
-- it, so the contexts are not inferable from the two premises.
push-rep : {ηᵢ η₁ᶜ ηᶜ : TyCtx} {B : Ty} {X Y : ℕ}
  → ∃[ R ] ((ηᵢ ⊢ B ~ R) × (η₁ᶜ ⊢ ` X ~ R))
  → ∃[ R ] ((ηᵢ ⊢ B ~ R) × (ηᶜ ⊢ ` Y ~ R))
    ---------------------------------------------------------------
  → Σ[ α ∈ RVar ] ((ηᶜ ∋ˡ Y := α) × (η₁ᶜ ∋ˡ X := α))
push-rep (R , p , q) (R′ , p′ , same-var d)
  with same-rep-unique p p′
push-rep (R , p , same-var d′) (R′ , p′ , same-var d) | refl =
  _ , d , d′

-- In any typed id-layer under an `unseal`, the inner `id (` X)`'s variable
-- NAMES the pushed conversion's binder.  IdPush therefore invents no
-- representation variable.
idpush-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    --------------------------------------------------------------------
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ α ∈ RVar ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
        × (Δᶜ ∋ᵗ Y := α)
        × (Δ₁ᶜ ∋ᵗ X := α))
idpush-name
    (env mw₂ (env mw₁ ⊢V (conv-idv tvX) sm₁ se₁ wB)
         (conv-unseal dY) sm₂ se₂ wE)
  with push-rep se₁ sm₂
idpush-name
    (env mw₂ (env mw₁ ⊢V (conv-idv tvX) sm₁ se₁ wB)
         (conv-unseal dY) sm₂ se₂ wE)
  | α , d , d′ =
  _ , _ , _ , α
  , bw-interior mw₂ , bw-conversion mw₂ , bw-conversion mw₁
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
        × (Δ₁ᶜ ∋ᵗ X := α))
cancel-name
    (env mw₂ (env mw₁ ⊢V (conv-seal dX) sm₁ se₁ wB)
         (conv-unseal dY) sm₂ se₂ wE)
  with push-rep se₁ sm₂
cancel-name
    (env mw₂ (env mw₁ ⊢V (conv-seal dX) sm₁ se₁ wB)
         (conv-unseal dY) sm₂ se₂ wE)
  | α , d , d′ =
  _ , _ , _ , α
  , bw-interior mw₂ , bw-conversion mw₂ , bw-conversion mw₁
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
-- The argument runs through the representation universe: the outer `id A`
-- forces the inner boundary's exterior type to be a base type, and
-- `≈-base-target` (proof/Canonical) carries a base type to a base type
-- across the exterior comparison — but the inner conversion's target is a
-- variable.
outer-id-base-untypeable : ∀ {Δ Γ V Θ₁ Θ₂ X A C} → Base A
  → ¬ (Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , id A ⟫ ⦂ C)
outer-id-base-untypeable bA
    (env {Δᵢ = Δᵢ} mw₂
         (env {Δᶜ = Δ₁ᶜ} mw₁ ⊢V (conv-idv tvX) sm₁ se₁ wB)
         (conv-id bA′) (R , p , q) se₂ wE)
  with ≈-base-target {Δ = Δᵢ} {Δ′ = Δ₁ᶜ}
         (same-base-target p (same-base-source q bA′)) se₁
outer-id-base-untypeable bA
    (env {Δᵢ = Δᵢ} mw₂
         (env {Δᶜ = Δ₁ᶜ} mw₁ ⊢V (conv-idv tvX) sm₁ se₁ wB)
         (conv-id bA′) (R , p , q) se₂ wE) | ()
outer-id-base-untypeable () (env _ (env _ _ (conv-idv _) _ _ _)
                                 (conv-idv _) _ _ _)

-- A boundary can never conceal the name its OWN conversion cites —
-- `value-var-visible` (strong-rep-store.Terms) says a value's variable type is
-- visible on the value's exterior context, because `env`'s last conjunct
-- checks it there.  So "Θ₁ locks Y while the conversion cites Y" is
-- untypeable.

------------------------------------------------------------------------
-- §3  THE NAKED DROP — the door, closed
------------------------------------------------------------------------

-- `V ⟪ Θ , id A ⟫ -→ V` is unsound because V is typed on the boundary scope's
-- INTERIOR, not on Δ.  A concrete failing instance: the boundary's
-- conversion cites an ordinary name that Δ does not have at all.

Δₑ : Ctxᵗ
Δₑ = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

Δₑ-no-1 : ∀ {α} → Δₑ ∋ᵗ 1 := α → ⊥
Δₑ-no-1 (there ())

naked-drop-trap : ∀ {C} →
  ¬ (Δₑ ∣ [] ⊢ ($ 7) ⟪ boundary [] , seal 1 ⟫ ⦂ C)
naked-drop-trap (env mwᵥ ⊢$ ⊢c smᵢ smₑ wE)
  with bw-conversion mwᵥ
naked-drop-trap (env mwᵥ ⊢$ (conv-seal (α , R , name , rep , same)) smᵢ smₑ wE)
  | conversion conv[] = Δₑ-no-1 name

------------------------------------------------------------------------
-- §3b  THE SOUND SIDE CONDITION
------------------------------------------------------------------------

-- The drop is sound exactly when the boundary changes NO FRAME.  Then both
-- induced contexts are the exterior itself and the identity conversion
-- fixes the type, so the interior derivation IS the exterior one.

empty-interior : (Γ : Ctxᵗ) → Γ ⊢ⁱ boundary [] ⇒ Γ
empty-interior Γ = interior changes[]

empty-conversion : (Γ : Ctxᵗ) → Γ ⊢ᶜ boundary [] ⇒ Γ
empty-conversion Γ = conversion conv[]

drop-empty-frame : ∀ {Δ Γ V A B}
  → Δ ∣ Γ ⊢ V ⟪ boundary [] , id A ⟫ ⦂ B
    ------------------------------------
  → Δ ∣ [] ⊢ V ⦂ B
drop-empty-frame {Δ = Δ} {V = V} (env mwᵥ ⊢V ⊢c (R , pᵢ , qᵢ) (S , pₑ , qₑ) wE)
  with interior-functional (bw-interior mwᵥ) (empty-interior Δ)
     | conversion-functional (bw-conversion mwᵥ) (empty-conversion Δ)
... | refl | refl
  with same-rep-unique qᵢ (subst (λ T → names Δ ⊢ T ~ S)
                                 (sym (conv-id-refl ⊢c)) qₑ)
... | refl =
  subst (λ T → Δ ∣ [] ⊢ V ⦂ T)
        (same-target-unique (name-fn (bw-exterior mwᵥ)) pᵢ pₑ)
        ⊢V

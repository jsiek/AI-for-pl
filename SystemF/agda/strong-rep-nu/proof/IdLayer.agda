module strong-rep-nu.proof.IdLayer where

-- File Charter:
--   * THE ID-LAYER FACTS about the two `Merge` redexes the retired
--     IdPush and CancelR used to handle (an `unseal Y` over `id (` X)`
--     or over `seal X`).  §1 typing FORCES the inner conversion's name
--     and the outer's to denote ONE representation variable
--     (`idpush-name`, `cancel-name`), which is why composition's
--     seal-then-unseal clause compares no names.  §2 `unseal` is the
--     ONLY active conversion an id-(` X) layer can meet.  §3 the naked
--     drop is sound exactly when the boundary changes NO FRAME.
--   * §1 used to be an EQUATION between ordinary indices; with two
--     universes the fact is one universe UP, and with the store the
--     two names denote the same variable outright.
-- Commentary: Commentary.md § proof/IdLayer.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Base; base-ℕ; base-𝔹)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary

------------------------------------------------------------------------
-- §1  THE NAMES ARE FORCED
------------------------------------------------------------------------

-- The heart of both cases, on the two `boundary` premises alone: the
-- inner conversion's TARGET representation and the outer's SOURCE
-- representation both read the one middle type.
-- Commentary.md § proof/IdLayer.agda / §1
push-rep : {ηᵢ : TyCtx} {B : Ty} {α β : RVar}
  → ηᵢ ⊢ B ~ ` α → ηᵢ ⊢ B ~ ` β → α ≡ β
push-rep p q with same-rep-unique p q
push-rep p q | refl = refl

-- In any typed id-layer under an `unseal`, the inner `id (` X)`'s variable
-- NAMES the pushed conversion's binder.  IdPush therefore invents no
-- representation variable.
idpush-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , ⌞ id (` X) ⌟ ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    --------------------------------------------------------------------
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ α ∈ RVar ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
        × (Δᶜ ∋ᵗ Y := α)
        × (Δ₁ᶜ ∋ᵗ X := α))
idpush-name
    (boundary mw₂ (boundary mw₁ ⊢V (conv-tail (conv-mid (conv-idv d′))) sm₁ se₁ wB)
         (conv-unseal (d , _) ok) sm₂ se₂ wE)
  with push-rep se₁ sm₂
... | refl =
  _ , _ , _ , _
  , bw-interior mw₂ , bw-conversion mw₂ , bw-conversion mw₁
  , d , d′

-- THE SAME FACT FOR CANCEL.  The inner `seal X` has the same TARGET
-- representation `` ` α ``, so the same two premises settle it, and
-- CancelR needs no premise relating its two names either.
cancel-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , tail (seal X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
    --------------------------------------------------------------------
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ α ∈ RVar ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
        × (Δᶜ ∋ᵗ Y := α)
        × (Δ₁ᶜ ∋ᵗ X := α))
cancel-name
    (boundary mw₂ (boundary mw₁ ⊢V (conv-tail (conv-seal (d′ , _) okX)) sm₁ se₁ wB)
         (conv-unseal (d , _) ok) sm₂ se₂ wE)
  with push-rep se₁ sm₂
... | refl =
  _ , _ , _ , _
  , bw-interior mw₂ , bw-conversion mw₂ , bw-conversion mw₁
  , d , d′

------------------------------------------------------------------------
-- §2  THE ONLY ACTIVE CONVERSION AN ID-LAYER MEETS IS `unseal`
------------------------------------------------------------------------

-- A wrapper whose conversion is `id (` X)` has a VARIABLE exterior
-- representation, and an outer `id A` at a BASE type demands a base
-- one — so the id-base branch of `Active` is unreachable over this LHS.
-- Commentary.md § proof/IdLayer.agda / §2
outer-id-base-untypeable : ∀ {Δ Γ V Θ₁ Θ₂ X A C} → Base A
  → ¬ (Δ ∣ Γ ⊢ (V ⟪ Θ₁ , ⌞ id (` X) ⌟ ⟫) ⟪ Θ₂ , ⌞ id A ⌟ ⟫ ⦂ C)
outer-id-base-untypeable bA
    (boundary mw₂
         (boundary mw₁ ⊢V (conv-tail (conv-mid (conv-idv d))) sm₁ se₁ wB)
         (conv-tail (conv-mid (conv-id bA′))) sm₂ se₂ wE)
  with same-rep-unique se₁ sm₂
outer-id-base-untypeable base-ℕ
    (boundary mw₂
         (boundary mw₁ ⊢V (conv-tail (conv-mid (conv-idv d))) sm₁ se₁ wB)
         (conv-tail (conv-mid (conv-id bA′))) sm₂ se₂ wE) | ()
outer-id-base-untypeable base-𝔹
    (boundary mw₂
         (boundary mw₁ ⊢V (conv-tail (conv-mid (conv-idv d))) sm₁ se₁ wB)
         (conv-tail (conv-mid (conv-id bA′))) sm₂ se₂ wE) | ()
outer-id-base-untypeable ()
  (boundary _ (boundary _ _ (conv-tail (conv-mid (conv-idv _))) _ _ _)
       (conv-tail (conv-mid (conv-idv _))) _ _ _)

-- A boundary can never conceal the name its OWN conversion cites
-- (`value-var-visible`, strong-rep-nu.Terms).

------------------------------------------------------------------------
-- §3  THE NAKED DROP — the door, closed
------------------------------------------------------------------------

-- Unsound, because V is typed on the boundary scope's INTERIOR, not on
-- Δ.  The concrete failing instance follows.
-- Commentary.md § proof/IdLayer.agda / §3

Δₑ : Ctxᵗ
Δₑ = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

Δₑ-no-1 : ∀ {α} → Δₑ ∋ᵗ 1 := α → ⊥
Δₑ-no-1 (there ())

naked-drop-trap : ∀ {C} →
  ¬ (Δₑ ∣ [] ⊢ ($ 7) ⟪ [] , tail (seal 1) ⟫ ⦂ C)
naked-drop-trap (boundary mwᵥ ⊢$ ⊢c smᵢ smₑ wE)
  with bw-conversion mwᵥ
naked-drop-trap
  (boundary mwᵥ ⊢$ (conv-tail (conv-seal (name , rep , _) ok))
       smᵢ smₑ wE)
  | conversion conv[] = Δₑ-no-1 name

------------------------------------------------------------------------
-- §3b  THE SOUND SIDE CONDITION
------------------------------------------------------------------------

-- Sound exactly when the boundary changes NO FRAME: both induced
-- contexts are then the exterior itself.

empty-interior : (Γ : Ctxᵗ) → Γ ⊢ⁱ [] ⇒ Γ
empty-interior Γ = interior changes[]

empty-conversion : (Γ : Ctxᵗ) → Γ ⊢ᶜ [] ⇒ Γ
empty-conversion Γ = conversion conv[]

drop-empty-frame : ∀ {Δ Γ V A B}
  → Δ ∣ Γ ⊢ V ⟪ [] , ⌞ id A ⌟ ⟫ ⦂ B
    ------------------------------------
  → Δ ∣ [] ⊢ V ⦂ B
drop-empty-frame {Δ = Δ} {V = V} (boundary mwᵥ ⊢V ⊢c pᵢ pₑ wE)
  with interior-functional (bw-interior mwᵥ) (empty-interior Δ)
     | conv-id-refl ⊢c
drop-empty-frame {Δ = Δ} {V = V} (boundary mwᵥ ⊢V ⊢c pᵢ pₑ wE)
  | refl | refl =
  subst (λ T → Δ ∣ [] ⊢ V ⦂ T)
        (same-target-unique (name-fn (bw-exterior mwᵥ)) pᵢ pₑ)
        ⊢V

module alt.ThetaReduction where

-- File Charter:
--   * Defines term-variable substitution and telescope-indexed one-step
--     reduction for the Θ-indexed alternative syntax.
--   * Regular-type renaming uses the repository's context injections.  At a
--     crossing it inserts or deletes the distinguished type variable canonically;
--     weakening is the derived skip-at-position instance.  Term substitution
--     stops at closed crossing interiors; open ν interiors receive ordinary
--     renaming and substitution.
--   * Evaluation descends beneath ν, but ν is immobile with respect to
--     eliminations.  Constants, blame, tags, inert casts, lambdas, and type
--     abstractions dissolve through the λB rules; seal-headed values remain.
--   * Identity cancellation is strict in both node fields.  A mismatched
--     identity conceal/reveal pair is an adapter value only when its operand
--     has an immobile head and the node data differ.
--   * Ground injections commute out of identity conceals unconditionally and
--     out of identity reveals when their tags strengthen.  The region's own
--     tag resolves at its reveal boundary to the representation's injection.
--     Ground projection commutes into the remaining reveal values.  These
--     rules use expansion; only the boundary resolution reads `rep?`.
--   * Universal crossings use ScTyWrap: they move beneath Λ without
--     instantiating, allocating, or inspecting the telescope.
--   * β-Λ requires a λB Value body.  Typing imposes no corresponding body
--     predicate, so reducible Λ bodies advance through `ξ-Λ` first.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term Θ Δ → Term Θ Δ
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ A ˙ M) = ƛ A ˙ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ rename ρ M
rename ρ (L ⦂∀ C [ A ]) = rename ρ L ⦂∀ C [ A ]
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
-- Crossing interiors remain closed.  Region interiors are open and therefore
-- receive the ordinary term-variable action.
rename ρ (M ↑[ Y ≔ α ] c) = M ↑[ Y ≔ α ] c
rename ρ (M ↓[ Y ≔ α ] c) = M ↓[ Y ≔ α ] c
rename ρ (ν[ A ] M) = ν[ A ] rename ρ M
rename ρ blame = blame

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

-- `insert↪ᵗ` and `delete↪ᵗ` are exported by ThetaTyping because balanced
-- telescope extension and term renaming share exactly this type variable bookkeeping.

renameᵗᵐ : Δ ↪ᵗ Δ′ → Term Θ Δ → Term Θ Δ′
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ A ˙ M) =
  ƛ renameᵗ (toRenameᵗ ρ) A ˙ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (keep ρ) M)
renameᵗᵐ ρ (L ⦂∀ C [ A ]) =
  renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
    [ renameᵗ (toRenameᵗ ρ) A ]
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) =
  renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ c ⟩) = renameᵗᵐ ρ M ⟨ renameᵐᶜ ρ c ⟩
renameᵗᵐ ρ (M ↑[ Y ≔ α ] c) =
  renameᵗᵐ (insert↪ᵗ ρ Y) M
    ↑[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ] c
renameᵗᵐ (keep ρ) (M ↓[ Y ≔ α ] c) =
  renameᵗᵐ (delete↪ᵗ (keep ρ) Y) M
    ↓[ toRenameᵗ (keep ρ) Y ≔ α ] c
renameᵗᵐ (skip ρ) (M ↓[ Y ≔ α ] c) =
  renameᵗᵐ (delete↪ᵗ (skip ρ) Y) M
    ↓[ toRenameᵗ (skip ρ) Y ≔ α ] c
renameᵗᵐ ρ (ν[ A ] M) =
  ν[ renameᵗ (toRenameᵗ ρ) A ] renameᵗᵐ ρ M
renameᵗᵐ ρ blame = blame

skipAt↪ᵗ : ∀ {Δ} → TyVar (suc Δ) → Δ ↪ᵗ suc Δ
skipAt↪ᵗ zero = skip id↪ᵗ
skipAt↪ᵗ {Δ = suc Δ} (suc X) = keep (skipAt↪ᵗ X)

toRename-id↪ᵗ : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ id↪ᵗ X ≡ X
toRename-id↪ᵗ zero = refl
toRename-id↪ᵗ (suc X) = cong suc (toRename-id↪ᵗ X)

skipAt-punchIn : ∀ {Δ} (X : TyVar (suc Δ)) (Y : TyVar Δ)
  → toRenameᵗ (skipAt↪ᵗ X) Y ≡ punchIn X Y
skipAt-punchIn zero Y = cong suc (toRename-id↪ᵗ Y)
skipAt-punchIn (suc X) zero = refl
skipAt-punchIn (suc X) (suc Y) = cong suc (skipAt-punchIn X Y)

weakenᵗᵐ : ∀ {Θ Δ} (X : TyVar (suc Δ))
  → Term Θ Δ
  → Term Θ (suc Δ)
weakenᵗᵐ X = renameᵗᵐ (skipAt↪ᵗ X)

wk~ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (X : TyVar (suc Δ))
  → μ ⊢ A ∼ B
  → renameEnv∼ (skipAt↪ᵗ X) μ ⊢ wkᵗ X A ∼ wkᵗ X B
wk~ {μ = μ} X c =
  rename∼ (punchIn X) preserves c
  where
  preserves : ∀ Y
    → renameEnv∼ (skipAt↪ᵗ X) μ (punchIn X Y) ≡ μ Y
  preserves Y = trans
    (cong (renameEnv∼ (skipAt↪ᵗ X) μ) (sym (skipAt-punchIn X Y)))
    (renameEnv∼-preserves (skipAt↪ᵗ X) μ Y)

strengthenEnv∼ : ∀ {Δ}
  → TyVar (suc Δ)
  → Env∼ (suc Δ)
  → Env∼ Δ
strengthenEnv∼ Y μ X = μ (punchIn Y X)

strengthen∼★ : ∀ {Δ} {Y : TyVar (suc Δ)}
    {μ : Env∼ (suc Δ)} {H : Ty (suc Δ)} {H₀ : Ty Δ}
  → strengthenᵗ? Y H ≡ just H₀
  → μ ⊢ H ∼★
  → strengthenEnv∼ Y μ ⊢ H₀ ∼★
strengthen∼★ refl ⇒∼★ = ⇒∼★
strengthen∼★ refl ι∼★ = ι∼★
strengthen∼★ {Y = Y} eq (X∼★ᵍ {X = X} mode) with Y ≟ X
strengthen∼★ () (X∼★ᵍ mode) | yes refl
strengthen∼★ {Y = Y} {μ = μ} refl
    (X∼★ᵍ {X = X} mode) | no Y≢X =
  X∼★ᵍ (trans (cong μ (punchIn-punchOut Y X Y≢X)) mode)
strengthen∼★ {Y = Y} eq (X∼★ᶜ {X = X} mode) with Y ≟ X
strengthen∼★ () (X∼★ᶜ mode) | yes refl
strengthen∼★ {Y = Y} {μ = μ} refl
    (X∼★ᶜ {X = X} mode) | no Y≢X =
  X∼★ᶜ (trans (cong μ (punchIn-punchOut Y X Y≢X)) mode)
strengthen∼★ refl ∀∼★ = ∀∼★

weaken∼★ : ∀ {Δ} {μ : Env∼ Δ} {H : Ty Δ}
  → (X : TyVar (suc Δ))
  → μ ⊢ H ∼★
  → renameEnv∼ (skipAt↪ᵗ X) μ ⊢ wkᵗ X H ∼★
weaken∼★ {μ = μ} X H∼★ =
  rename∼★ (punchIn X) preserves H∼★
  where
  preserves : ∀ Y
    → renameEnv∼ (skipAt↪ᵗ X) μ (punchIn X Y) ≡ μ Y
  preserves Y = trans
    (cong (renameEnv∼ (skipAt↪ᵗ X) μ) (sym (skipAt-punchIn X Y)))
    (renameEnv∼-preserves (skipAt↪ᵗ X) μ Y)

wkInj : ∀ {Δ} {μ : Env∼ Δ} {H : Ty Δ}
  → (X : TyVar (suc Δ))
  → (Hᵍ : Ground H)
  → μ ⊢ H ∼★
  → renameEnv∼ (skipAt↪ᵗ X) μ ⊢ wkᵗ X H ∼ ★
wkInj X Hᵍ H∼★ =
  _! ⦃ wkGround X Hᵍ ⦄ ⦃ weaken∼★ X H∼★ ⦄
    (idᵍ (wkGround X Hᵍ)) ⦃ ground-nonstar (wkGround X Hᵍ) ⦄

strInj : ∀ {Δ} {Y : TyVar (suc Δ)}
    {μ : Env∼ (suc Δ)} {H : Ty (suc Δ)} {H₀ : Ty Δ}
  → (Hᵍ : Ground H)
  → (H∼★ : μ ⊢ H ∼★)
  → (strengthens : strengthenᵗ? Y H ≡ just H₀)
  → strengthenEnv∼ Y μ ⊢ H₀ ∼ ★
strInj Hᵍ H∼★ strengthens =
  _! ⦃ strengthenGround Hᵍ strengthens ⦄
    ⦃ strengthen∼★ strengthens H∼★ ⦄
    (idᵍ (strengthenGround Hᵍ strengthens))
    ⦃ ground-nonstar (strengthenGround Hᵍ strengthens) ⦄

------------------------------------------------------------------------
-- Public injection of a representation
------------------------------------------------------------------------

-- The occurrence-indexed hypotheses let the recursive construction cross a
-- universal structurally when its binder is absent, and factor through `inst`
-- or `gen` when it is present.  At the public `idᶜ` entry every free variable
-- is crossable in both directions.

private
  not-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
    → X ∉ᵗ A
    → X ∈ᵗ A
    → ⊥
  not-occurs (∉-var X≠Y) var-∈ = ≢ᶠ→≢ X≠Y refl
  not-occurs ∉-base ()
  not-occurs ∉-star ()
  not-occurs (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
    not-occurs X∉A X∈A
  not-occurs (∉-fun X∉A X∉B) (∈-fun-right X∉A′ X∈B) =
    not-occurs X∉B X∈B
  not-occurs (∉-all X∉A) (∈-all X∈A) = not-occurs X∉A X∈A

  fun-occurs-left : ∀ {Δ} {X : TyVar Δ} {A B : Ty Δ}
    → X ∈ᵗ A
    → X ∈ᵗ A ⇒ B
  fun-occurs-left = ∈-fun-left

  fun-occurs-right : ∀ {Δ} {X : TyVar Δ} {A B : Ty Δ}
    → X ∈ᵗ B
    → X ∈ᵗ A ⇒ B
  fun-occurs-right {X = X} {A = A} X∈B with occurs? X A
  fun-occurs-right X∈B | present X∈A = ∈-fun-left X∈A
  fun-occurs-right X∈B | absent X∉A = ∈-fun-right X∉A X∈B

  mutual
    inject★-from-occurs : ∀ {Δ} {μ : Env∼ Δ} (A : Ty Δ)
      → (∀ X → X ∈ᵗ A → μ ⊢ ＇ X ∼★)
      → μ ⊢ A ∼ ★
    inject★-from-occurs (＇ X) gate =
      _! ⦃ G∼★ = gate X var-∈ ⦄ (id (＇ X)) ⦃ nonstar-X ⦄
    inject★-from-occurs (‵ ι) gate =
      _! ⦃ Gᵍ = ‵ ι ⦄ (id (‵ ι)) ⦃ nonstar-ι ⦄
    inject★-from-occurs ★ gate = id ★
    inject★-from-occurs (A ⇒ B) gate =
      _! ⦃ Gᵍ = ★⇒★ ⦄
        (project★-from-occurs A
          (λ X X∈A → flip-∼★ (gate X (fun-occurs-left X∈A))) ↦
         inject★-from-occurs B
          (λ X X∈B → gate X (fun-occurs-right X∈B)))
        ⦃ nonstar-⇒ ⦄
    inject★-from-occurs (`∀ A) gate with occurs? zero A
    inject★-from-occurs (`∀ A) gate | absent z∉A =
      _! ⦃ Gᵍ = ∀★ ⦄
        (∀ᶜ (inject★-from-occurs A inner)) ⦃ nonstar-∀ ⦄
      where
      inner : ∀ X → X ∈ᵗ A → extᵐ _ ⊢ ＇ X ∼★
      inner zero z∈A = ⊥-elim (not-occurs z∉A z∈A)
      inner (suc X) X∈A =
        rename∼★ suc (λ Y → refl) (gate X (∈-all X∈A))
    inject★-from-occurs (`∀ (＇ zero)) gate | present var-∈ =
      _! ⦃ Gᵍ = ∀★ ⦄ bot-elim ⦃ nonstar-∀ ⦄
    inject★-from-occurs (`∀ (＇ suc X)) gate | present ()
    inject★-from-occurs (`∀ (‵ ι)) gate | present ()
    inject★-from-occurs (`∀ ★) gate | present ()
    inject★-from-occurs (`∀ (A ⇒ B)) gate | present z∈A =
      factor-inst-star (inject★-from-occurs (A ⇒ B) inner)
        nonvar-fun z∈A
      where
      inner : ∀ X → X ∈ᵗ A ⇒ B → instᵐ _ ⊢ ＇ X ∼★
      inner zero X∈A = X∼★ᵍ refl
      inner (suc X) X∈A =
        rename∼★ suc (λ Y → refl) (gate X (∈-all X∈A))
    inject★-from-occurs (`∀ (`∀ A)) gate | present z∈A =
      factor-inst-star (inject★-from-occurs (`∀ A) inner)
        nonvar-all z∈A
      where
      inner : ∀ X → X ∈ᵗ `∀ A → instᵐ _ ⊢ ＇ X ∼★
      inner zero X∈A = X∼★ᵍ refl
      inner (suc X) X∈A =
        rename∼★ suc (λ Y → refl) (gate X (∈-all X∈A))

    project★-from-occurs : ∀ {Δ} {μ : Env∼ Δ} (A : Ty Δ)
      → (∀ X → X ∈ᵗ A → μ ⊢★∼ ＇ X)
      → μ ⊢ ★ ∼ A
    project★-from-occurs (＇ X) gate =
      ？_ ⦃ ★∼G = gate X var-∈ ⦄ (id (＇ X)) ⦃ nonstar-X ⦄
    project★-from-occurs (‵ ι) gate =
      ？_ ⦃ Gᵍ = ‵ ι ⦄ (id (‵ ι)) ⦃ nonstar-ι ⦄
    project★-from-occurs ★ gate = id ★
    project★-from-occurs (A ⇒ B) gate =
      ？_ ⦃ Gᵍ = ★⇒★ ⦄
        (inject★-from-occurs A
          (λ X X∈A → flip-★∼ (gate X (fun-occurs-left X∈A))) ↦
         project★-from-occurs B
          (λ X X∈B → gate X (fun-occurs-right X∈B)))
        ⦃ nonstar-⇒ ⦄
    project★-from-occurs (`∀ A) gate with occurs? zero A
    project★-from-occurs (`∀ A) gate | absent z∉A =
      ？_ ⦃ Gᵍ = ∀★ ⦄
        (∀ᶜ (project★-from-occurs A inner)) ⦃ nonstar-∀ ⦄
      where
      inner : ∀ X → X ∈ᵗ A → extᵐ _ ⊢★∼ ＇ X
      inner zero z∈A = ⊥-elim (not-occurs z∉A z∈A)
      inner (suc X) X∈A =
        rename★∼ suc (λ Y → refl) (gate X (∈-all X∈A))
    project★-from-occurs (`∀ (＇ zero)) gate | present var-∈ =
      ？_ ⦃ Gᵍ = ∀★ ⦄ bot-intro ⦃ nonstar-∀ ⦄
    project★-from-occurs (`∀ (＇ suc X)) gate | present ()
    project★-from-occurs (`∀ (‵ ι)) gate | present ()
    project★-from-occurs (`∀ ★) gate | present ()
    project★-from-occurs (`∀ (A ⇒ B)) gate | present z∈A =
      factor-gen-star (project★-from-occurs (A ⇒ B) inner)
        nonvar-fun z∈A
      where
      inner : ∀ X → X ∈ᵗ A ⇒ B → genᵐ _ ⊢★∼ ＇ X
      inner zero X∈A = ★∼Xᵍ refl
      inner (suc X) X∈A =
        rename★∼ suc (λ Y → refl) (gate X (∈-all X∈A))
    project★-from-occurs (`∀ (`∀ A)) gate | present z∈A =
      factor-gen-star (project★-from-occurs (`∀ A) inner)
        nonvar-all z∈A
      where
      inner : ∀ X → X ∈ᵗ `∀ A → genᵐ _ ⊢★∼ ＇ X
      inner zero X∈A = ★∼Xᵍ refl
      inner (suc X) X∈A =
        rename★∼ suc (λ Y → refl) (gate X (∈-all X∈A))

inj★ : ∀ {Δ} (C : Ty Δ) → C ∼ ★
inj★ C = inject★-from-occurs C (λ X X∈C → X∼★ᶜ refl)

idGround∼★ : ∀ {Δ} {G : Ty Δ} → Ground G → idᶜ ⊢ G ∼★
idGround∼★ (＇ X) = X∼★ᶜ refl
idGround∼★ (‵ ι) = ι∼★
idGround∼★ ★⇒★ = ⇒∼★
idGround∼★ ∀★ = ∀∼★

inj★-ground : ∀ {Δ} {G : Ty Δ} (Gᵍ : Ground G)
  → inj★ G ≡ _! ⦃ Gᵍ ⦄ ⦃ idGround∼★ Gᵍ ⦄
      (idᵍ Gᵍ) ⦃ ground-nonstar Gᵍ ⦄
inj★-ground (＇ X) = refl
inj★-ground (‵ ι) = refl
inj★-ground ★⇒★ = refl
inj★-ground ∀★ = refl

-- A public injection is either the identity at ★ or a cast to a ground
-- followed by that ground's exact tag.  The first cast is inert for
-- functions and binder-independent universals; a dependent universal instead
-- exposes `inst`, so its contractum is deliberately transient.
data InjectionPlan {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
  bare : InjectionPlan μ ★
  box : ∀ {C G : Ty Δ}
    → (Gᵍ : Ground G)
    → μ ⊢ C ∼ G
    → InjectionPlan μ C

injection-plan-from-cast : ∀ {Δ} {μ : Env∼ Δ} {C : Ty Δ}
  → μ ⊢ C ∼ ★
  → InjectionPlan μ C
injection-plan-from-cast (id ★) = bare
injection-plan-from-cast (_! ⦃ Gᵍ = Gᵍ ⦄ c) = box Gᵍ c
injection-plan-from-cast (？_ ⦃ g ⦄ c ⦃ () ⦄)
injection-plan-from-cast ((inst c) ★≢★) = ⊥-elim (★≢★ refl)

private
  injectionPlan-from-occurs : ∀ {Δ} {μ : Env∼ Δ} (C : Ty Δ)
    → (∀ X → X ∈ᵗ C → μ ⊢ ＇ X ∼★)
    → InjectionPlan μ C
  injectionPlan-from-occurs (＇ X) gate =
    box (＇ X) (id (＇ X))
  injectionPlan-from-occurs (‵ ι) gate = box (‵ ι) (id (‵ ι))
  injectionPlan-from-occurs ★ gate = bare
  injectionPlan-from-occurs (A ⇒ B) gate =
    box ★⇒★
      (project★-from-occurs A
        (λ X X∈A → flip-∼★ (gate X (fun-occurs-left X∈A))) ↦
       inject★-from-occurs B (λ X X∈B → gate X (fun-occurs-right X∈B)))
  injectionPlan-from-occurs (`∀ A) gate with occurs? zero A
  injectionPlan-from-occurs (`∀ A) gate | absent z∉A =
    box ∀★ (∀ᶜ (inject★-from-occurs A inner))
    where
    inner : ∀ X → X ∈ᵗ A → extᵐ _ ⊢ ＇ X ∼★
    inner zero z∈A = ⊥-elim (not-occurs z∉A z∈A)
    inner (suc X) X∈A =
      rename∼★ suc (λ Y → refl) (gate X (∈-all X∈A))
  injectionPlan-from-occurs (`∀ (＇ zero)) gate | present var-∈ =
    box ∀★ bot-elim
  injectionPlan-from-occurs (`∀ (＇ suc X)) gate | present ()
  injectionPlan-from-occurs (`∀ (‵ ι)) gate | present ()
  injectionPlan-from-occurs (`∀ ★) gate | present ()
  injectionPlan-from-occurs (`∀ (A ⇒ B)) gate | present z∈A =
    injection-plan-from-cast
      (factor-inst-star (inject★-from-occurs (A ⇒ B) inner)
        nonvar-fun z∈A)
    where
    inner : ∀ X → X ∈ᵗ A ⇒ B → instᵐ _ ⊢ ＇ X ∼★
    inner zero X∈A = X∼★ᵍ refl
    inner (suc X) X∈A =
      rename∼★ suc (λ Y → refl) (gate X (∈-all X∈A))
  injectionPlan-from-occurs (`∀ (`∀ A)) gate | present z∈A =
    injection-plan-from-cast
      (factor-inst-star (inject★-from-occurs (`∀ A) inner)
        nonvar-all z∈A)
    where
    inner : ∀ X → X ∈ᵗ `∀ A → instᵐ _ ⊢ ＇ X ∼★
    inner zero X∈A = X∼★ᵍ refl
    inner (suc X) X∈A =
      rename∼★ suc (λ Y → refl) (gate X (∈-all X∈A))

injectionPlan : ∀ {Δ} (C : Ty Δ) → InjectionPlan idᶜ C
injectionPlan C =
  injectionPlan-from-occurs C (λ X X∈C → X∼★ᶜ refl)

smart-inj★ : ∀ {Θ Δ} → Term Θ Δ → (C : Ty Δ) → Term Θ Δ
smart-inj★ V C with injectionPlan C
smart-inj★ V C | bare = V
smart-inj★ V C | box Gᵍ c =
  (V ⟨ c ⟩) ⟨ _! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = idGround∼★ Gᵍ ⦄
    (idᵍ Gᵍ) ⦃ ground-nonstar Gᵍ ⦄ ⟩

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Subst : AnchorCtx → TyCtx → Set
Subst Θ Δ = Var → Term Θ Δ

exts : Subst Θ Δ → Subst Θ Δ
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

liftˢ : Subst Θ Δ → Subst Θ (suc Δ)
liftˢ σ x = weakenᵗᵐ zero (σ x)

shiftᶿˢ : Subst Θ Δ → Subst (suc Θ) Δ
shiftᶿˢ σ x = shiftᶿ (σ x)

subst : Subst Θ Δ → Term Θ Δ → Term Θ Δ
subst σ (` x) = σ x
subst σ (ƛ A ˙ M) = ƛ A ˙ subst (exts σ) M
subst σ (L · M) = subst σ L · subst σ M
subst σ (Λ M) = Λ (subst (liftˢ σ) M)
subst σ (L ⦂∀ C [ A ]) = subst σ L ⦂∀ C [ A ]
subst σ ($ κ) = $ κ
subst σ (L ⊕[ op ] M) = subst σ L ⊕[ op ] subst σ M
subst σ (M ⟨ c ⟩) = subst σ M ⟨ c ⟩
-- Crossing interiors remain closed.  Region interiors are open and therefore
-- receive the ordinary term-variable action.
subst σ (M ↑[ Y ≔ α ] c) = M ↑[ Y ≔ α ] c
subst σ (M ↓[ Y ≔ α ] c) = M ↓[ Y ≔ α ] c
subst σ (ν[ A ] M) = ν[ A ] subst (shiftᶿˢ σ) M
subst σ blame = blame

singleSub : Term Θ Δ → Subst Θ Δ
singleSub N zero = N
singleSub N (suc x) = ` x

infixl 8 _[_]
_[_] : Term Θ Δ → Term Θ Δ → Term Θ Δ
M [ N ] = subst (singleSub N) M
------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _⊢_—→_

data _⊢_—→_ : ∀ {Θ Δ σ}
  → TyEnv Θ Δ σ → Term Θ Δ → Term Θ Δ → Set where
  δ-⊕ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {op κ₁ κ₂ κ₃}
    → δ op κ₁ κ₂ κ₃
      -----------------------------------------
    → Ψ ⊢ ($ κ₁ ⊕[ op ] $ κ₂) —→ ($ κ₃)

  β : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V N : Term Θ Δ} {A : Ty Δ}
    → Value V
      -----------------------------
    → Ψ ⊢ (ƛ A ˙ N) · V —→ N [ V ]

  β-id : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A : Ty Δ} {a : Atom A}
    → Value V
      ---------------------------------
    → Ψ ⊢ V ⟨ id {μ = μ} a ⟩ —→ V

  β-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V W : Term Θ Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
    → Value W
      ------------------------------------------------
    → Ψ ⊢ (V ⟨ c ↦ d ⟩) · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩

  β-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {C : Ty Δ}
      {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
      -------------------------------------------------------
    → Ψ ⊢ (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] —→ (V ⦂∀ A [ C ]) ⟨ d ⟩

  ground : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → A ≢ G
      -------------------------------------------------
    → Ψ ⊢ V ⟨ c ! ⟩ —→ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩

  expand : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → G ≢ B
      -------------------------------------------------
    → Ψ ⊢ V ⟨ ？ c ⟩ —→ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩

  inject-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ Δ} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {μ : Env∼ Δ} {H : Ty Δ}
      ⦃ Hᵍ : Ground H ⦄ ⦃ H∼★ : μ ⊢ H ∼★ ⦄
      ⦃ Hns : NonStar H ⦄
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ (V ⟨ (idᵍ Hᵍ) ! ⟩) ↓[ X ≔ α ] id↓ —→
        (V ↓[ X ≔ α ] expand↓ (wkᵗ X H) id↓) ⟨ wkInj X Hᵍ H∼★ ⟩

  inject-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {Y : TyVar (suc Δ)} {β : TyVar Θ}
      {μ : Env∼ (suc Δ)} {H : Ty (suc Δ)} {H₀ : Ty Δ}
      ⦃ Hᵍ : Ground H ⦄ ⦃ H∼★ : μ ⊢ H ∼★ ⦄
      ⦃ Hns : NonStar H ⦄
    → (s : strengthenᵗ? Y H ≡ just H₀)
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ (V ⟨ (idᵍ Hᵍ) ! ⟩) ↑[ Y ≔ β ] id↑ —→
        (V ↑[ Y ≔ β ] expand↑ H id↑) ⟨ strInj Hᵍ H∼★ s ⟩

  inject-reveal-resolve : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {C : Ty Δ} {μ : Env∼ (suc Δ)}
      ⦃ X∼★ : μ ⊢ ＇ X ∼★ ⦄
      ⦃ Xns : NonStar (＇ X) ⦄
    → rep? Ψ α ≡ just C
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢
        (V ⟨ _! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ ⦄
          (id { μ = μ } (＇ X)) ⦃ Xns ⦄ ⟩) ↑[ X ≔ α ] id↑ —→
        smart-inj★ (V ↑[ X ≔ α ] unseal) C

  ★-project-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value (V ↑[ X ≔ α ] id↑)
      ------------------------------------------------------------
    → Ψ ⊢ (V ↑[ X ≔ α ] id↑) ⟨ ？ (idᵍ Gᵍ) ⟩ —→
        (V ⟨ wk~ X (？ (idᵍ Gᵍ)) ⟩) ↑[ X ≔ α ] expand↑ (wkᵗ X G) id↑

  tag-untag : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ μ′ : Env∼ Δ}
      {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : μ′ ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      -------------------------------------------------------
    → Ψ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V

  tag-untag-bad : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ μ′ : Env∼ Δ}
      {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : μ′ ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → G ≢ H
      ------------------------------------------------------------
    → Ψ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩ —→ blame

  blame-bot-intro : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
    → Value V
      ------------------------------------------
    → Ψ ⊢ V ⟨ bot-intro {μ = μ} ⟩ —→ blame

  β-reveal-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {W : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal} {d : Reveal}
    → Value V
    → Value W
      ----------------------------------------------------------------------
    → Ψ ⊢ (V ↑[ X ≔ α ] (c ↦↑ d)) · W —→ (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d

  β-conceal-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ Δ} {W : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal} {d : Conceal}
    → Value V
    → Value W
      ----------------------------------------------------------------------
    → Ψ ⊢ (V ↓[ X ≔ α ] (c ↦↓ d)) · W —→ (V · (W ↑[ X ≔ α ] c)) ↓[ X ≔ α ] d

  id-cancel : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {R : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Value R
      ----------------------------------------------------
    → Ψ ⊢ (R ↓[ X ≔ α ] id↓) ↑[ X ≔ α ] id↑ —→ R

  id-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → Ψ ⊢ ($ κ) ↑[ X ≔ α ] id↑ —→ $ κ

  id-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → Ψ ⊢ ($ κ) ↓[ X ≔ α ] id↓ —→ $ κ

  conceal-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {R : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Value R
      ------------------------------------------------------------
    → Ψ ⊢ (R ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal —→ R

  blame-·₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M : Term Θ Δ}
      ------------------------
    → Ψ ⊢ blame · M —→ blame

  blame-·₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    → Value V
      ------------------------
    → Ψ ⊢ V · blame —→ blame

  blame-Λ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      ----------------------
    → Ψ ⊢ Λ blame —→ blame

  blame-• : ∀ {Θ : AnchorCtx} {Δ : TyCtx}
      {σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {B : Ty (suc Δ)}
      ----------------------------------
    → Ψ ⊢ blame ⦂∀ B [ A ] —→ blame

  blame-⟨⟩ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {μ : Env∼ Δ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
      ------------------------
    → Ψ ⊢ blame ⟨ c ⟩ —→ blame

  blame-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
      --------------------------------------
    → Ψ ⊢ blame ↑[ X ≔ α ] c —→ blame

  blame-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
      --------------------------------------
    → Ψ ⊢ blame ↓[ X ≔ α ] c —→ blame

  blame-⊕₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ Δ} {op : Prim}
      --------------------------------
    → Ψ ⊢ blame ⊕[ op ] M —→ blame

  blame-⊕₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {op : Prim}
    → Value V
      --------------------------------
    → Ψ ⊢ V ⊕[ op ] blame —→ blame

  blame-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ}
      -------------------------
    → Ψ ⊢ ν[ A ] blame —→ blame

  const-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ} {κ}
      ----------------------
    → Ψ ⊢ ν[ A ] ($ κ) —→ $ κ

  tag-out : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {V : Term (suc Θ) Δ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ ν[ A ] (V ⟨ (idᵍ Gᵍ) ! ⟩) —→
        (ν[ A ] V) ⟨ (idᵍ Gᵍ) ! ⟩

  inert-cast-out : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {V : Term (suc Θ) Δ} {μ : Env∼ Δ}
      {B C : Ty Δ} {c : μ ⊢ B ∼ C}
    → Value V
    → Inert c
      -----------------------------------------
    → Ψ ⊢ ν[ A ] (V ⟨ c ⟩) —→ (ν[ A ] V) ⟨ c ⟩

  NUWRAP : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A B : Ty Δ} {N : Term (suc Θ) Δ}
      ---------------------------------------------
    → Ψ ⊢ ν[ A ] (ƛ B ˙ N) —→ ƛ B ˙ (ν[ A ] N)

  NUTYWRAP : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {V : Term (suc Θ) (suc Δ)}
      -----------------------------------------
    → Ψ ⊢ ν[ A ] (Λ V) —→ Λ (ν[ ⇑ᵗ A ] V)

  β-Λ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {B : Ty (suc Δ)} {C : Ty Δ}
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ (Λ V) ⦂∀ B [ C ] —→ ν[ C ] (shiftᶿ V ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)

  -- The consistency evidence mentions only the regular context.  `shiftᶿ`
  -- changes only the anchor count, so the inner cast reuses `c` unchanged.
  β-gen : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ} {A C : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------------------------------------------
    → Ψ ⊢ (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→
        ν[ C ] (((shiftᶿ V ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
          ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)

  -- β-inst instantiates the polymorphic value V at ★ and applies the
  -- closed consistency evidence.  Allocation and the seal/unseal
  -- mediation are deliberately not this rule's job: the contractum is an
  -- ordinary type application, and the downstream ⦂∀ rules (β-Λ, β-∀,
  -- β-gen, β-reveal-∀, β-conceal-∀) perform them for whichever canonical
  -- ∀-value V is.
  -- U35 producer audit: this is the only rule whose contractum introduces a
  -- type-application node absent from its redex, and its argument is ★.
  -- β-∀ copies its existing argument; ξ-• only propagates an
  -- existing node.  No reduction rule mints `⦂∀ _ [ ＇ X ]` at a live
  -- crossing.
  β-inst : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → Value V
    → (B≢★ : B ≢ ★)
      ------------------------------------------------------------
    → Ψ ⊢ V ⟨ (inst c) B≢★ ⟩ —→ (V ⦂∀ A [ ★ ]) ⟨ c [ ★/0 ]ᶜ ⟩

  -- ScTyWrap pushes a crossing through Λ without opening the binder.
  -- The raw shape is already typed one binder deeper by the crossing rule,
  -- so it is carried verbatim and the pivot merely shifts by `suc`.
  β-reveal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc (suc Δ))}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ ((Λ V) ↑[ X ≔ α ] `∀↑ c) —→ Λ (V ↑[ suc X ≔ α ] c)

  β-conceal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ ((Λ V) ↓[ X ≔ α ] `∀↓ c) —→ Λ (V ↓[ suc X ≔ α ] c)

  ξ-Λ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M M′ : Term Θ (suc Δ)}
    → Ψ ,typ ⊢ M —→ M′
      ----------------------
    → Ψ ⊢ Λ M —→ Λ M′

  ξ-·₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {L L′ M : Term Θ Δ}
    → Ψ ⊢ L —→ L′
      --------------------
    → Ψ ⊢ L · M —→ L′ · M

  ξ-·₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V M M′ : Term Θ Δ}
    → Value V
    → Ψ ⊢ M —→ M′
      --------------------
    → Ψ ⊢ V · M —→ V · M′

  ξ-• : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M M′ : Term Θ Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → Ψ ⊢ M —→ M′
      ------------------------------------
    → Ψ ⊢ M ⦂∀ B [ A ] —→ M′ ⦂∀ B [ A ]

  ξ-⟨⟩ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M M′ : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → Ψ ⊢ M —→ M′
      ---------------------------
    → Ψ ⊢ M ⟨ c ⟩ —→ M′ ⟨ c ⟩

  ξ-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M M′ : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
      {fresh : α ∉ᵛ σ}
    → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ⊢ M —→ M′
      ------------------------------------------
    → Ψ ⊢ M ↑[ X ≔ α ] c —→ M′ ↑[ X ≔ α ] c

  ξ-conceal : ∀ {Θ Δ σ} {Ψ′ : TyEnv Θ (suc Δ) σ}
      {M M′ : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Ψ′ ,end[ X ] ⊢ M —→ M′
      ------------------------------------------
    → Ψ′ ⊢ M ↓[ X ≔ α ] c —→ M′ ↓[ X ≔ α ] c

  ξ-⊕₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {L L′ M : Term Θ Δ} {op : Prim}
    → Ψ ⊢ L —→ L′
      --------------------------------
    → Ψ ⊢ L ⊕[ op ] M —→ L′ ⊕[ op ] M

  ξ-⊕₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V M M′ : Term Θ Δ} {op : Prim}
    → Value V
    → Ψ ⊢ M —→ M′
      --------------------------------
    → Ψ ⊢ V ⊕[ op ] M —→ V ⊕[ op ] M′

  ξ-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {M M′ : Term (suc Θ) Δ}
    → Ψ ,:= A ⊢ M —→ M′
      -------------------------------
    → Ψ ⊢ ν[ A ] M —→ ν[ A ] M′

------------------------------------------------------------------------
-- Values do not reduce
------------------------------------------------------------------------

mutual
  value-no-step : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V M′ : Term Θ Δ}
    → Value V
    → ¬ (Ψ ⊢ V —→ M′)
  value-no-step (ƛ A ˙ N) ()
  value-no-step (Λ Vᵥ) (ξ-Λ step) = value-no-step Vᵥ step
  value-no-step ($ κ) ()
  value-no-step (inject Vᵥ) (ground Vᵥ′ G≢G) = G≢G refl
  value-no-step (inject Vᵥ) (ξ-⟨⟩ step) = value-no-step Vᵥ step
  value-no-step (Vᵥ 《 inert 》) (ξ-⟨⟩ step) =
    value-no-step Vᵥ step
  value-no-step (seal-value Vᵥ) (ξ-conceal step) =
    value-no-step Vᵥ step
  value-no-step (reveal-fun Vᵥ) (ξ-reveal step) =
    value-no-step Vᵥ step
  value-no-step (conceal-fun Vᵥ) (ξ-conceal step) =
    value-no-step Vᵥ step
  value-no-step (adapter Vᵥ head pair≢) (id-cancel Vᵥ′) =
    pair≢ (refl , refl)
  value-no-step (adapter Vᵥ head pair≢) (ξ-reveal step) =
    conceal-id-no-step Vᵥ head step
  value-no-step (adapter-region Vᵥ head X∈A) (ξ-reveal step) =
    region-no-step Vᵥ head step

  conceal-id-no-step : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ Δ} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {M′ : Term Θ (suc Δ)}
    → Value V
    → ImmobileHead V
    → ¬ (Ψ ⊢ V ↓[ X ≔ α ] id↓ —→ M′)
  conceal-id-no-step Vᵥ seal-head (ξ-conceal step) =
    value-no-step Vᵥ step
  conceal-id-no-step Vᵥ reveal-fun-head (ξ-conceal step) =
    value-no-step Vᵥ step
  conceal-id-no-step Vᵥ conceal-fun-head (ξ-conceal step) =
    value-no-step Vᵥ step
  conceal-id-no-step Vᵥ adapter-head (ξ-conceal step) =
    value-no-step Vᵥ step
  conceal-id-no-step Vᵥ adapter-region-head (ξ-conceal step) =
    value-no-step Vᵥ step

  region-no-step : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {V : Term (suc Θ) Δ} {M′ : Term Θ Δ}
    → Value V
    → ImmobileHead V
    → ¬ (Ψ ⊢ ν[ A ] V —→ M′)
  region-no-step Vᵥ seal-head (ξ-ν step) = value-no-step Vᵥ step
  region-no-step Vᵥ reveal-fun-head (ξ-ν step) =
    value-no-step Vᵥ step
  region-no-step Vᵥ conceal-fun-head (ξ-ν step) =
    value-no-step Vᵥ step
  region-no-step Vᵥ adapter-head (ξ-ν step) = value-no-step Vᵥ step
  region-no-step Vᵥ adapter-region-head (ξ-ν step) =
    value-no-step Vᵥ step

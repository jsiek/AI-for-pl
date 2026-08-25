{-# OPTIONS --safe #-}

module proof.DGG.ConversionPivotAlignment where

-- File Charter:
--   * Computes the possibly empty structural position of the generator in a
--     generator-indexed reveal or conceal conversion.
--   * Makes paired conversion rules compare pivot positions independently of
--     endpoint variable names and representation types.
--   * Proves positions invariant under renaming, normalization, and trusted
--     store-change transport.
--   * Maps the computed position to the legacy catch-up boundary pivot while
--     that boundary API still distinguishes neutral and active wrappers.
--   * Contains no term-imprecision rules, world transport, or compatibility
--     aliases.

open import Types using (Ty; TyCtx; TyVar; _⇒ʳ_; renameᵗ)
open import Data.Maybe using (Maybe; just; nothing)
open import TyStore using (TyStore)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; trans; cong)
import Conversion as Conv
import Reduction as R
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective)
open import proof.TypeInTermSubst using
  ( StoreRename
  ; StoreRename-ext
  ; StoreRename-id
  ; StoreRename-suc-bind
  ; conceal-rename-id
  ; conceal-renameᵗ
  ; renameᵗ-id
  ; renameᵗ-pointwise-id
  ; reveal-rename-id
  ; reveal-renameᵗ
  )
import proof.Reduction as PR


data GeneratorPosition : Set where
  generator-absent : GeneratorPosition
  generator-here : GeneratorPosition
  generator-⇒-left : GeneratorPosition → GeneratorPosition
  generator-⇒-right : GeneratorPosition → GeneratorPosition
  generator-⇒-both : GeneratorPosition → GeneratorPosition
    → GeneratorPosition
  generator-∀ : GeneratorPosition → GeneratorPosition


joinGeneratorPositions : GeneratorPosition → GeneratorPosition
  → GeneratorPosition
joinGeneratorPositions generator-absent generator-absent = generator-absent
joinGeneratorPositions left generator-absent = generator-⇒-left left
joinGeneratorPositions generator-absent right = generator-⇒-right right
joinGeneratorPositions left right = generator-⇒-both left right

liftGeneratorPosition : GeneratorPosition → GeneratorPosition
liftGeneratorPosition generator-absent = generator-absent
liftGeneratorPosition position = generator-∀ position


generatorBoundaryPivot : ∀ {Delta : TyCtx}
  → TyVar Delta → GeneratorPosition → Maybe (TyVar Delta)
generatorBoundaryPivot X generator-absent = nothing
generatorBoundaryPivot X generator-here = just X
generatorBoundaryPivot X (generator-⇒-left position) = just X
generatorBoundaryPivot X (generator-⇒-right position) = just X
generatorBoundaryPivot X (generator-⇒-both left right) = just X
generatorBoundaryPivot X (generator-∀ position) = just X


mutual
  revealGeneratorPosition : ∀ {Delta : TyCtx} {Sigma : TyStore Delta}
      {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↑ Delta A B}
    → Sigma Conv.⊢↑[ X ⦂ R ] c
    → GeneratorPosition
  revealGeneratorPosition (Conv.⊢↑-unseal member) = generator-here
  revealGeneratorPosition (Conv.⊢↑-⇒ c⊢ d⊢) =
    joinGeneratorPositions (concealGeneratorPosition c⊢)
      (revealGeneratorPosition d⊢)
  revealGeneratorPosition (Conv.⊢↑-∀ eq c⊢) =
    liftGeneratorPosition (revealGeneratorPosition c⊢)
  revealGeneratorPosition (Conv.⊢↑-id-var member X≠Y) =
    generator-absent
  revealGeneratorPosition (Conv.⊢↑-id-base member) = generator-absent
  revealGeneratorPosition (Conv.⊢↑-id-star member) = generator-absent

  concealGeneratorPosition : ∀ {Delta : TyCtx} {Sigma : TyStore Delta}
      {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↓ Delta A B}
    → Sigma Conv.⊢↓[ X ⦂ R ] c
    → GeneratorPosition
  concealGeneratorPosition (Conv.⊢↓-seal member) = generator-here
  concealGeneratorPosition (Conv.⊢↓-⇒ c⊢ d⊢) =
    joinGeneratorPositions (revealGeneratorPosition c⊢)
      (concealGeneratorPosition d⊢)
  concealGeneratorPosition (Conv.⊢↓-∀ eq c⊢) =
    liftGeneratorPosition (concealGeneratorPosition c⊢)
  concealGeneratorPosition (Conv.⊢↓-id-var member X≠Y) =
    generator-absent
  concealGeneratorPosition (Conv.⊢↓-id-base member) =
    generator-absent
  concealGeneratorPosition (Conv.⊢↓-id-star member) =
    generator-absent


revealGeneratorPosition-store-transport : ∀ {Delta : TyCtx}
    {Sigma Sigma′ : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
    {c : Conv.Conv↑ Delta A B}
  → (eq : Sigma ≡ Sigma′)
  → (c⊢ : Sigma Conv.⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition
      (subst (λ Store → Store Conv.⊢↑[ X ⦂ R ] c) eq c⊢)
    ≡ revealGeneratorPosition c⊢
revealGeneratorPosition-store-transport refl c⊢ = refl

concealGeneratorPosition-store-transport : ∀ {Delta : TyCtx}
    {Sigma Sigma′ : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
    {c : Conv.Conv↓ Delta A B}
  → (eq : Sigma ≡ Sigma′)
  → (c⊢ : Sigma Conv.⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition
      (subst (λ Store → Store Conv.⊢↓[ X ⦂ R ] c) eq c⊢)
    ≡ concealGeneratorPosition c⊢
concealGeneratorPosition-store-transport refl c⊢ = refl


mutual
  revealGeneratorPosition-unique : ∀ {Delta : TyCtx}
      {Sigma : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↑ Delta A B}
    → (c⊢ c⊢′ : Sigma Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c⊢′
  revealGeneratorPosition-unique (Conv.⊢↑-unseal member)
      (Conv.⊢↑-unseal member′) =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-⇒ c⊢ d⊢)
      (Conv.⊢↑-⇒ c⊢′ d⊢′)
    rewrite concealGeneratorPosition-unique c⊢ c⊢′
      | revealGeneratorPosition-unique d⊢ d⊢′ =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-∀ refl c⊢)
      (Conv.⊢↑-∀ refl c⊢′)
    rewrite revealGeneratorPosition-unique c⊢ c⊢′ =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-id-var member X≠Y)
      (Conv.⊢↑-id-var member′ X≠Y′) =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-id-base member)
      (Conv.⊢↑-id-base member′) =
    refl
  revealGeneratorPosition-unique (Conv.⊢↑-id-star member)
      (Conv.⊢↑-id-star member′) =
    refl

  concealGeneratorPosition-unique : ∀ {Delta : TyCtx}
      {Sigma : TyStore Delta} {X : TyVar Delta} {R A B : Ty Delta}
      {c : Conv.Conv↓ Delta A B}
    → (c⊢ c⊢′ : Sigma Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c⊢′
  concealGeneratorPosition-unique (Conv.⊢↓-seal member)
      (Conv.⊢↓-seal member′) =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-⇒ c⊢ d⊢)
      (Conv.⊢↓-⇒ c⊢′ d⊢′)
    rewrite revealGeneratorPosition-unique c⊢ c⊢′
      | concealGeneratorPosition-unique d⊢ d⊢′ =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-∀ refl c⊢)
      (Conv.⊢↓-∀ refl c⊢′)
    rewrite concealGeneratorPosition-unique c⊢ c⊢′ =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-id-var member X≠Y)
      (Conv.⊢↓-id-var member′ X≠Y′) =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-id-base member)
      (Conv.⊢↓-id-base member′) =
    refl
  concealGeneratorPosition-unique (Conv.⊢↓-id-star member)
      (Conv.⊢↓-id-star member′) =
    refl


mutual
  revealGeneratorPosition-rename : ∀ {Δ Δ′ : TyCtx}
      {ρ : Δ ⇒ʳ Δ′} {Σ : TyStore Δ} {Σ′ : TyStore Δ′}
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conv.Conv↑ Δ A B}
    → (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → (store-rename : StoreRename ρ Σ Σ′)
    → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition
        (reveal-renameᵗ injective store-rename c⊢)
      ≡ revealGeneratorPosition c⊢
  revealGeneratorPosition-rename injective store-rename
      (Conv.⊢↑-unseal member) =
    refl
  revealGeneratorPosition-rename injective store-rename
      (Conv.⊢↑-⇒ c⊢ d⊢)
    rewrite concealGeneratorPosition-rename injective store-rename c⊢
      | revealGeneratorPosition-rename injective store-rename d⊢ =
    refl
  revealGeneratorPosition-rename injective store-rename
      (Conv.⊢↑-∀ refl c⊢) =
    cong liftGeneratorPosition
      (revealGeneratorPosition-rename (ext-injective injective)
        (StoreRename-ext store-rename) c⊢)
  revealGeneratorPosition-rename injective store-rename
      (Conv.⊢↑-id-var member X≠Y) =
    refl
  revealGeneratorPosition-rename injective store-rename
      (Conv.⊢↑-id-base member) =
    refl
  revealGeneratorPosition-rename injective store-rename
      (Conv.⊢↑-id-star member) =
    refl

  concealGeneratorPosition-rename : ∀ {Δ Δ′ : TyCtx}
      {ρ : Δ ⇒ʳ Δ′} {Σ : TyStore Δ} {Σ′ : TyStore Δ′}
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conv.Conv↓ Δ A B}
    → (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → (store-rename : StoreRename ρ Σ Σ′)
    → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition
        (conceal-renameᵗ injective store-rename c⊢)
      ≡ concealGeneratorPosition c⊢
  concealGeneratorPosition-rename injective store-rename
      (Conv.⊢↓-seal member) =
    refl
  concealGeneratorPosition-rename injective store-rename
      (Conv.⊢↓-⇒ c⊢ d⊢)
    rewrite revealGeneratorPosition-rename injective store-rename c⊢
      | concealGeneratorPosition-rename injective store-rename d⊢ =
    refl
  concealGeneratorPosition-rename injective store-rename
      (Conv.⊢↓-∀ refl c⊢) =
    cong liftGeneratorPosition
      (concealGeneratorPosition-rename (ext-injective injective)
        (StoreRename-ext store-rename) c⊢)
  concealGeneratorPosition-rename injective store-rename
      (Conv.⊢↓-id-var member X≠Y) =
    refl
  concealGeneratorPosition-rename injective store-rename
      (Conv.⊢↓-id-base member) =
    refl
  concealGeneratorPosition-rename injective store-rename
      (Conv.⊢↓-id-star member) =
    refl


private
  reveal-representation-transport : ∀ {Δ} {Σ : TyStore Δ} {X}
      {R R′ A B : Ty Δ} {c : Conv.Conv↑ Δ A B}
    → R ≡ R′
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → Σ Conv.⊢↑[ X ⦂ R′ ] c
  reveal-representation-transport refl c⊢ = c⊢

  conceal-representation-transport : ∀ {Δ} {Σ : TyStore Δ} {X}
      {R R′ A B : Ty Δ} {c : Conv.Conv↓ Δ A B}
    → R ≡ R′
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → Σ Conv.⊢↓[ X ⦂ R′ ] c
  conceal-representation-transport refl c⊢ = c⊢

  reveal-representation-transport-position : ∀ {Δ}
      {Σ : TyStore Δ} {X} {R R′ A B : Ty Δ}
      {c : Conv.Conv↑ Δ A B}
    → (eq : R ≡ R′)
    → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition (reveal-representation-transport eq c⊢)
        ≡ revealGeneratorPosition c⊢
  reveal-representation-transport-position refl c⊢ = refl

  conceal-representation-transport-position : ∀ {Δ}
      {Σ : TyStore Δ} {X} {R R′ A B : Ty Δ}
      {c : Conv.Conv↓ Δ A B}
    → (eq : R ≡ R′)
    → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition (conceal-representation-transport eq c⊢)
        ≡ concealGeneratorPosition c⊢
  conceal-representation-transport-position refl c⊢ = refl

  reveal-endpoint-transport : ∀ {Δ} {Σ : TyStore Δ} {X R}
      {A₀ A₁ B₀ B₁ : Ty Δ} {c : Conv.Conv↑ Δ A₀ B₀}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → Σ Conv.⊢↑[ X ⦂ R ]
        subst (Conv.Conv↑ Δ A₁) eqB
          (subst (λ A → Conv.Conv↑ Δ A B₀) eqA c)
  reveal-endpoint-transport refl refl c⊢ = c⊢

  conceal-endpoint-transport : ∀ {Δ} {Σ : TyStore Δ} {X R}
      {A₀ A₁ B₀ B₁ : Ty Δ} {c : Conv.Conv↓ Δ A₀ B₀}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → Σ Conv.⊢↓[ X ⦂ R ]
        subst (Conv.Conv↓ Δ A₁) eqB
          (subst (λ A → Conv.Conv↓ Δ A B₀) eqA c)
  conceal-endpoint-transport refl refl c⊢ = c⊢

  reveal-endpoint-transport-position : ∀ {Δ}
      {Σ : TyStore Δ} {X R} {A₀ A₁ B₀ B₁ : Ty Δ}
      {c : Conv.Conv↑ Δ A₀ B₀}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition (reveal-endpoint-transport eqA eqB c⊢)
        ≡ revealGeneratorPosition c⊢
  reveal-endpoint-transport-position refl refl c⊢ = refl

  conceal-endpoint-transport-position : ∀ {Δ}
      {Σ : TyStore Δ} {X R} {A₀ A₁ B₀ B₁ : Ty Δ}
      {c : Conv.Conv↓ Δ A₀ B₀}
    → (eqA : A₀ ≡ A₁)
    → (eqB : B₀ ≡ B₁)
    → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition (conceal-endpoint-transport eqA eqB c⊢)
        ≡ concealGeneratorPosition c⊢
  conceal-endpoint-transport-position refl refl c⊢ = refl

  reveal-rename-id-position : ∀ {Δ} {Σ : TyStore Δ} {X R A B}
      {c : Conv.Conv↑ Δ A B}
    → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition (reveal-rename-id c⊢)
        ≡ revealGeneratorPosition c⊢
  reveal-rename-id-position {R = R} c⊢ =
    trans
      (revealGeneratorPosition-unique (reveal-rename-id c⊢)
        (reveal-representation-transport (renameᵗ-id R)
          (reveal-renameᵗ (λ eq → eq) StoreRename-id c⊢)))
      (trans
        (reveal-representation-transport-position (renameᵗ-id R)
          (reveal-renameᵗ (λ eq → eq) StoreRename-id c⊢))
        (revealGeneratorPosition-rename (λ eq → eq) StoreRename-id c⊢))

  conceal-rename-id-position : ∀ {Δ} {Σ : TyStore Δ} {X R A B}
      {c : Conv.Conv↓ Δ A B}
    → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition (conceal-rename-id c⊢)
        ≡ concealGeneratorPosition c⊢
  conceal-rename-id-position {R = R} c⊢ =
    trans
      (concealGeneratorPosition-unique (conceal-rename-id c⊢)
        (conceal-representation-transport (renameᵗ-id R)
          (conceal-renameᵗ (λ eq → eq) StoreRename-id c⊢)))
      (trans
        (conceal-representation-transport-position (renameᵗ-id R)
          (conceal-renameᵗ (λ eq → eq) StoreRename-id c⊢))
        (concealGeneratorPosition-rename (λ eq → eq) StoreRename-id c⊢))


revealGeneratorPosition-normalize : ∀ {Δ} {Σ : TyStore Δ}
    {X R A B} {c : Conv.Conv↑ Δ A B}
  → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (PR.normalizeReveal-⊢↑ c⊢)
    ≡ revealGeneratorPosition c⊢
revealGeneratorPosition-normalize {R = R} {A = A} {B = B} c⊢ =
  trans
    (revealGeneratorPosition-unique (PR.normalizeReveal-⊢↑ c⊢)
      (reveal-endpoint-transport eqA eqB (reveal-rename-id c⊢)))
    (trans
      (reveal-endpoint-transport-position eqA eqB
        (reveal-rename-id c⊢))
      (reveal-rename-id-position c⊢))
  where
  eqA = renameᵗ-pointwise-id (λ X → X) A (λ X → refl)
  eqB = renameᵗ-pointwise-id (λ X → X) B (λ X → refl)


concealGeneratorPosition-normalize : ∀ {Δ} {Σ : TyStore Δ}
    {X R A B} {c : Conv.Conv↓ Δ A B}
  → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (PR.normalizeConceal-⊢↓ c⊢)
    ≡ concealGeneratorPosition c⊢
concealGeneratorPosition-normalize {R = R} {A = A} {B = B} c⊢ =
  trans
    (concealGeneratorPosition-unique (PR.normalizeConceal-⊢↓ c⊢)
      (conceal-endpoint-transport eqA eqB (conceal-rename-id c⊢)))
    (trans
      (conceal-endpoint-transport-position eqA eqB
        (conceal-rename-id c⊢))
      (conceal-rename-id-position c⊢))
  where
  eqA = renameᵗ-pointwise-id (λ X → X) A (λ X → refl)
  eqB = renameᵗ-pointwise-id (λ X → X) B (λ X → refl)


revealGeneratorPosition-apply : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {χs : R.StoreChanges Δ Δ′} {X : TyVar Δ} {R A B : Ty Δ}
    {c : Conv.Conv↑ Δ A B}
  → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (PR.applyReveals-⊢↑ {χs = χs} c⊢)
    ≡ revealGeneratorPosition c⊢
revealGeneratorPosition-apply {χs = R.[]} c⊢ = refl
revealGeneratorPosition-apply {χs = R.keep R.∷ χs} c⊢ =
  trans (revealGeneratorPosition-apply
          {χs = χs} (PR.normalizeReveal-⊢↑ c⊢))
    (revealGeneratorPosition-normalize c⊢)
revealGeneratorPosition-apply {χs = R.bind A R.∷ χs} c⊢ =
  trans (revealGeneratorPosition-apply {χs = χs} shifted)
    (revealGeneratorPosition-rename fin-suc-injective
      StoreRename-suc-bind c⊢)
  where
  shifted = reveal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢


concealGeneratorPosition-apply : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {χs : R.StoreChanges Δ Δ′} {X : TyVar Δ} {R A B : Ty Δ}
    {c : Conv.Conv↓ Δ A B}
  → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (PR.applyConceals-⊢↓ {χs = χs} c⊢)
    ≡ concealGeneratorPosition c⊢
concealGeneratorPosition-apply {χs = R.[]} c⊢ = refl
concealGeneratorPosition-apply {χs = R.keep R.∷ χs} c⊢ =
  trans (concealGeneratorPosition-apply
          {χs = χs} (PR.normalizeConceal-⊢↓ c⊢))
    (concealGeneratorPosition-normalize c⊢)
concealGeneratorPosition-apply {χs = R.bind A R.∷ χs} c⊢ =
  trans (concealGeneratorPosition-apply {χs = χs} shifted)
    (concealGeneratorPosition-rename fin-suc-injective
      StoreRename-suc-bind c⊢)
  where
  shifted = conceal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢

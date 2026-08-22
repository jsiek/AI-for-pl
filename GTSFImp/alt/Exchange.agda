module alt.Exchange where

-- File Charter:
--   * Defines the exchange of the two newest scoped-type slots and lifts it
--     to reveal and conceal conversions, including pivot strictness.
--   * States the omitted β-inst, β-reveal-∀, and β-conceal-∀ redexes and
--     shift-free contracta, then validates the contracta against explicit
--     typing components.
--   * The exchange is deliberately the top-two transposition, rather than a
--     general adjacent transposition: all three rules allocate their fresh
--     crossing at slot zero, immediately below a source `∀` binder.  Nested
--     pre-existing crossings move from X to suc X by ordinary `punchIn`.
--   * Compared with the Design.md sketch, endpoint-correct entry and exit
--     conversions are explicit parameters when propositional endpoint
--     equality is not definitional, following the checked β-Λ/β-gen rules.
--     For β-reveal-∀ and β-conceal-∀ the validation takes the restricted
--     `BindingsExtensionality` principle explicitly.  Inserting the fresh
--     crossing before an existing crossing and inserting the existing
--     crossing after the fresh one give pointwise equal `Bindings`; this
--     assumption turns that finite pointwise proof into function equality.
--     No postulate is introduced, and all exchanged inner typing is derived
--     below.

open import Data.Fin using (Fin; fromℕ; inject₁; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types
open import TermCtx using (TermCtx)
open import Consistency
open import alt.Store
open import alt.Conversion
open import alt.Terms

------------------------------------------------------------------------
-- Exchange of the two newest scoped slots
------------------------------------------------------------------------

swap : ∀ {Δ} → Fin (suc (suc Δ)) → Fin (suc (suc Δ))
swap zero = suc zero
swap (suc zero) = zero
swap (suc (suc X)) = suc (suc X)

swapᵗ : ∀ {Δ} → Ty (suc (suc Δ)) → Ty (suc (suc Δ))
swapᵗ = renameᵗ swap

swap-involutive : ∀ {Δ} (X : Fin (suc (suc Δ)))
  → swap (swap X) ≡ X
swap-involutive zero = refl
swap-involutive (suc zero) = refl
swap-involutive (suc (suc X)) = refl

renameᵗ-id : ∀ {Δ} (A : Ty Δ) → renameᵗ (λ X → X) A ≡ A
renameᵗ-id (＇ X) = refl
renameᵗ-id (‵ ι) = refl
renameᵗ-id ★ = refl
renameᵗ-id (A ⇒ B) rewrite renameᵗ-id A | renameᵗ-id B = refl
renameᵗ-id (`∀ A) = cong `∀
  (trans (renameᵗ-cong A ext-id) (renameᵗ-id A))
  where
  ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
  ext-id zero = refl
  ext-id (suc X) = refl

swapᵗ-involutive : ∀ {Δ} (A : Ty (suc (suc Δ)))
  → swapᵗ (swapᵗ A) ≡ A
swapᵗ-involutive A =
  trans (renameᵗ-comp swap swap A)
        (trans (renameᵗ-cong A swap-involutive)
               (renameᵗ-id A))

swap-shift : ∀ {Δ} (A : Ty (suc Δ))
  → swapᵗ (⇑ᵗ A) ≡ renameᵗ (extᵗ suc) A
swap-shift A =
  trans (renameᵗ-comp suc swap A)
        (renameᵗ-cong A swap-after-shift)
  where
  swap-after-shift : ∀ X → swap (suc X) ≡ extᵗ suc X
  swap-after-shift zero = refl
  swap-after-shift (suc X) = refl

swap-double-wk : ∀ {Δ} (A : Ty Δ)
  → swapᵗ (wkᵗ zero (wkᵗ zero A)) ≡ wkᵗ zero (wkᵗ zero A)
swap-double-wk {Δ} A =
  trans (renameᵗ-comp (punchIn zero) swap (wkᵗ zero A))
        (trans (renameᵗ-comp (punchIn zero) swap-after-punch A)
               (trans (renameᵗ-cong A same-double-punch)
                      (sym (renameᵗ-comp (punchIn zero)
                                          (punchIn zero) A))))
  where
  swap-after-punch : Fin (suc Δ) → Fin (suc (suc Δ))
  swap-after-punch X = swap (punchIn zero X)

  same-double-punch : ∀ X
    → swap-after-punch (punchIn zero X)
      ≡ punchIn zero (punchIn zero X)
  same-double-punch X = refl

punchIn-exchange : ∀ {Δ} (X : Fin (suc Δ)) (Y : Fin Δ)
  → punchIn zero (punchIn X Y) ≡ punchIn (suc X) (punchIn zero Y)
punchIn-exchange zero Y = refl
punchIn-exchange (suc X) zero = refl
punchIn-exchange (suc X) (suc Y) = refl

wk-exchange : ∀ {Δ} (X : Fin (suc Δ)) (A : Ty Δ)
  → wkᵗ zero (wkᵗ X A) ≡ wkᵗ (suc X) (wkᵗ zero A)
wk-exchange X A =
  trans (renameᵗ-comp (punchIn X) (punchIn zero) A)
        (trans (renameᵗ-cong A (punchIn-exchange X))
               (sym (renameᵗ-comp (punchIn zero)
                                   (punchIn (suc X)) A)))

substSecondᵗ : ∀ {Δ} → Ty (suc Δ) → Fin (suc (suc Δ)) → Ty (suc Δ)
substSecondᵗ B zero = ＇ zero
substSecondᵗ B (suc zero) = B
substSecondᵗ B (suc (suc X)) = ＇ (suc X)

swap-open : ∀ {Δ} (A : Ty (suc (suc Δ))) (B : Ty (suc Δ))
  → (swapᵗ A) [ B ]ᵗ ≡ substᵗ (substSecondᵗ B) A
swap-open A B =
  trans (substᵗ-rename (singleSubᵗ B) swap A)
        (substᵗ-cong A after-swap)
  where
  after-swap : ∀ X → singleSubᵗ B (swap X) ≡ substSecondᵗ B X
  after-swap zero = refl
  after-swap (suc zero) = refl
  after-swap (suc (suc X)) = refl

swap-shift-open-zero : ∀ {Δ} (A : Ty (suc Δ))
  → (swapᵗ (⇑ᵗ A)) [ ＇ zero ]ᵗ ≡ A
swap-shift-open-zero A =
  trans (swap-open (⇑ᵗ A) (＇ zero))
        (trans (substᵗ-rename (substSecondᵗ (＇ zero)) suc A)
               (trans (substᵗ-cong A second-after-shift)
                      (substᵗ-id A)))
  where
  second-after-shift : ∀ X
    → substSecondᵗ (＇ zero) (suc X) ≡ ＇ X
  second-after-shift zero = refl
  second-after-shift (suc X) = refl

wk-under-∀ : ∀ {Δ} (X : Fin (suc Δ)) (A : Ty (suc Δ))
  → renameᵗ (extᵗ (punchIn X)) A ≡ wkᵗ (suc X) A
wk-under-∀ X A = renameᵗ-cong A under-∀
  where
  under-∀ : ∀ Y → extᵗ (punchIn X) Y ≡ punchIn (suc X) Y
  under-∀ zero = refl
  under-∀ (suc Y) = refl

wk-zero-∀-swap : ∀ {Δ} (A : Ty (suc Δ))
  → wkᵗ zero (`∀ A) ≡ `∀ (swapᵗ (⇑ᵗ A))
wk-zero-∀-swap A = cong `∀ (sym (swap-shift A))

------------------------------------------------------------------------
-- Exchange lifted to conversions and pivot strictness
------------------------------------------------------------------------

swap↑ : ∀ {Δ} {A B : Ty (suc (suc Δ))}
  → Conv↑ (suc (suc Δ)) A B
  → Conv↑ (suc (suc Δ)) (swapᵗ A) (swapᵗ B)
swap↑ = rename↑ swap

swap↓ : ∀ {Δ} {A B : Ty (suc (suc Δ))}
  → Conv↓ (suc (suc Δ)) A B
  → Conv↓ (suc (suc Δ)) (swapᵗ A) (swapᵗ B)
swap↓ = rename↓ swap

mutual
  rename-strict↑ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {X A B}
      {c : Conv↑ Δ A B}
    → PivotStrict↑ X c
    → PivotStrict↑ (ρ X) (rename↑ ρ c)
  rename-strict↑ ρ strict-unseal = strict-unseal
  rename-strict↑ ρ (strict-↑⇒ c-strict d-strict) =
    strict-↑⇒ (rename-strict↓ ρ c-strict) (rename-strict↑ ρ d-strict)
  rename-strict↑ ρ (strict-↑∀ c-strict) =
    strict-↑∀ (rename-strict↑ (extᵗ ρ) c-strict)
  rename-strict↑ ρ strict-id↑ = strict-id↑

  rename-strict↓ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {X A B}
      {c : Conv↓ Δ A B}
    → PivotStrict↓ X c
    → PivotStrict↓ (ρ X) (rename↓ ρ c)
  rename-strict↓ ρ strict-seal = strict-seal
  rename-strict↓ ρ (strict-↓⇒ c-strict d-strict) =
    strict-↓⇒ (rename-strict↑ ρ c-strict) (rename-strict↓ ρ d-strict)
  rename-strict↓ ρ (strict-↓∀ c-strict) =
    strict-↓∀ (rename-strict↓ (extᵗ ρ) c-strict)
  rename-strict↓ ρ strict-id↓ = strict-id↓

swap-strict↑ : ∀ {Δ} {X : Fin (suc (suc Δ))} {A B}
    {c : Conv↑ (suc (suc Δ)) A B}
  → PivotStrict↑ X c
  → PivotStrict↑ (swap X) (swap↑ c)
swap-strict↑ = rename-strict↑ swap

swap-strict↓ : ∀ {Δ} {X : Fin (suc (suc Δ))} {A B}
    {c : Conv↓ (suc (suc Δ)) A B}
  → PivotStrict↓ X c
  → PivotStrict↓ (swap X) (swap↓ c)
swap-strict↓ = rename-strict↓ swap

------------------------------------------------------------------------
-- Allocation contexts and structural-delimiter representation evidence
------------------------------------------------------------------------

weakenBinding : ∀ {n} → Binding n → Binding (suc n)
weakenBinding ∀-bound = ∀-bound
weakenBinding (anchored α) = anchored (inject₁ α)

weakenBindings : ∀ {n Δ} → Bindings Δ n → Bindings Δ (suc n)
weakenBindings κ X = weakenBinding (κ X)

insertBinding-exchange : ∀ {n Δ} (X : Fin (suc Δ))
    (fresh old : Binding n) (κ : Bindings Δ n)
    (Y : Fin (suc (suc Δ)))
  → insertBinding zero fresh (insertBinding X old κ) Y
    ≡ insertBinding (suc X) old (insertBinding zero fresh κ) Y
insertBinding-exchange zero fresh old κ zero = refl
insertBinding-exchange zero fresh old κ (suc zero) = refl
insertBinding-exchange zero fresh old κ (suc (suc Y)) = refl
insertBinding-exchange (suc X) fresh old κ zero = refl
insertBinding-exchange (suc X) fresh old κ (suc Y) = refl

weakenBindings-insert : ∀ {n Δ} (X : Fin (suc Δ))
    (b : Binding n) (κ : Bindings Δ n) (Y : Fin (suc Δ))
  → weakenBindings (insertBinding X b κ) Y
    ≡ insertBinding X (weakenBinding b) (weakenBindings κ) Y
weakenBindings-insert zero b κ zero = refl
weakenBindings-insert zero b κ (suc Y) = refl
weakenBindings-insert {Δ = suc Δ} (suc X) b κ zero = refl
weakenBindings-insert {Δ = suc Δ} (suc X) b κ (suc Y) =
  weakenBindings-insert X b (λ Z → κ (suc Z)) Y

wkᶜ-exchange : ∀ {Δ} (X : Fin (suc Δ)) (Γ : TermCtx Δ)
  → wkᶜ zero (wkᶜ X Γ) ≡ wkᶜ (suc X) (wkᶜ zero Γ)
wkᶜ-exchange X [] = refl
wkᶜ-exchange X (A ∷ Γ)
    rewrite wk-exchange X A | wkᶜ-exchange X Γ =
  refl

BindingsExtensionality : Set
BindingsExtensionality = ∀ {n Δ} {κ κ′ : Bindings Δ n}
  → (∀ X → κ X ≡ κ′ X)
  → κ ≡ κ′

cross-bindings-exchange : BindingsExtensionality
  → ∀ {n Δ} (X : Fin (suc Δ))
    (fresh old : Binding n) (κ : Bindings Δ n)
  → insertBinding zero fresh (insertBinding X old κ)
    ≡ insertBinding (suc X) old (insertBinding zero fresh κ)
cross-bindings-exchange ext X fresh old κ =
  ext (insertBinding-exchange X fresh old κ)

allocation-bindings-exchange : BindingsExtensionality
  → ∀ {n Δ} (X : Fin (suc Δ))
    (b : Binding n) (κ : Bindings Δ n)
  → weakenBindings (insertBinding X b κ)
    ≡ insertBinding X (weakenBinding b) (weakenBindings κ)
allocation-bindings-exchange ext X b κ =
  ext (weakenBindings-insert X b κ)

allocation-cross-bindings-exchange : BindingsExtensionality
  → ∀ {n Δ} (X : Fin (suc Δ))
    (fresh : Binding (suc n)) (old : Binding n) (κ : Bindings Δ n)
  → insertBinding zero fresh
      (weakenBindings (insertBinding X old κ))
    ≡ insertBinding (suc X) (weakenBinding old)
      (insertBinding zero fresh (weakenBindings κ))
allocation-cross-bindings-exchange ext X fresh old κ =
  trans
    (cong (insertBinding zero fresh)
      (allocation-bindings-exchange ext X old κ))
    (cross-bindings-exchange ext X fresh
      (weakenBinding old) (weakenBindings κ))

allocCtx : (Γ : Ctx) → Ty (sizeᵉ Γ) → Ctx
allocCtx ⟨ Δ , n , κ , Σ , Γ ⟩ R =
  ⟨ Δ , suc n , weakenBindings κ , bind Σ R , Γ ⟩

cross-ctx-exchange : BindingsExtensionality
  → ∀ {Γ} {S : Ty (sizeᵉ Γ)} {X : Fin (suc (Δᵉ Γ))}
      {α : Name} {R : Ty (sizeᵉ Γ)}
    (p : α ⦂ R ∈ Σᵉ Γ)
  → cross-ctx
      (cross-ctx (allocCtx Γ S) X (weaken-lookup p)) zero fresh-lookup
    ≡ cross-ctx
      (cross-ctx (allocCtx Γ S) zero fresh-lookup)
      (suc X) (weaken-lookup p)
cross-ctx-exchange ext {Γ = ⟨ Δ , n , κ , Σ , Γ ⟩}
    {S = S} {X = X} p
    rewrite
      cross-bindings-exchange ext X (anchored (fromℕ n))
        (anchored (inject₁ (lookup-name p))) (weakenBindings κ)
    | wkᶜ-exchange X Γ =
  refl

allocation-cross-ctx : BindingsExtensionality
  → ∀ {Γ} {S : Ty (sizeᵉ Γ)} {X : Fin (suc (Δᵉ Γ))}
      {α : Name} {R : Ty (sizeᵉ Γ)}
    (p : α ⦂ R ∈ Σᵉ Γ)
  → allocCtx (cross-ctx Γ X p) S
    ≡ cross-ctx (allocCtx Γ S) X (weaken-lookup p)
allocation-cross-ctx ext {Γ = ⟨ Δ , n , κ , Σ , Γ ⟩}
    {S = S} {X = X} p
    rewrite allocation-bindings-exchange ext X
      (anchored (lookup-name p)) κ =
  refl

allocation-cross-ctx-exchange : BindingsExtensionality
  → ∀ {Γ} {S : Ty (sizeᵉ Γ)} {X : Fin (suc (Δᵉ Γ))}
      {α : Name} {R : Ty (sizeᵉ Γ)}
    (p : α ⦂ R ∈ Σᵉ Γ)
  → cross-ctx (allocCtx (cross-ctx Γ X p) S) zero fresh-lookup
    ≡ cross-ctx
      (cross-ctx (allocCtx Γ S) zero fresh-lookup)
      (suc X) (weaken-lookup p)
allocation-cross-ctx-exchange ext
    {Γ = ⟨ Δ , n , κ , Σ , Γ ⟩} {S = S} {X = X} p
    rewrite
      allocation-cross-bindings-exchange ext X (anchored (fromℕ n))
        (anchored (lookup-name p)) κ
    | wkᶜ-exchange X Γ =
  refl

cross-ctx-exchange-typing : BindingsExtensionality
  → ∀ {Γ} {S : Ty (sizeᵉ Γ)} {X : Fin (suc (Δᵉ Γ))}
      {α : Name} {R : Ty (sizeᵉ Γ)}
      {M : Term (suc (suc (Δᵉ Γ)))}
      {A : Ty (suc (suc (Δᵉ Γ)))}
    (p : α ⦂ R ∈ Σᵉ Γ)
  → cross-ctx
      (cross-ctx (allocCtx Γ S) X (weaken-lookup p)) zero fresh-lookup
      ⊢ M ⦂ A
  → cross-ctx
      (cross-ctx (allocCtx Γ S) zero fresh-lookup)
      (suc X) (weaken-lookup p)
      ⊢ M ⦂ A
cross-ctx-exchange-typing ext
    {Γ = ⟨ Δ , n , κ , Σ , Γ ⟩} {S = S} {X = X} p M⊢
    rewrite
      cross-bindings-exchange ext X (anchored (fromℕ n))
        (anchored (inject₁ (lookup-name p))) (weakenBindings κ)
    | wkᶜ-exchange X Γ =
  M⊢

allocation-cross-ctx-exchange-typing : BindingsExtensionality
  → ∀ {Γ} {S : Ty (sizeᵉ Γ)} {X : Fin (suc (Δᵉ Γ))}
      {α : Name} {R : Ty (sizeᵉ Γ)}
      {M : Term (suc (suc (Δᵉ Γ)))}
      {A : Ty (suc (suc (Δᵉ Γ)))}
    (p : α ⦂ R ∈ Σᵉ Γ)
  → cross-ctx
      (cross-ctx (allocCtx Γ S) zero fresh-lookup)
      (suc X) (weaken-lookup p)
      ⊢ M ⦂ A
  → cross-ctx (allocCtx (cross-ctx Γ X p) S) zero fresh-lookup
      ⊢ M ⦂ A
allocation-cross-ctx-exchange-typing ext
    {Γ = ⟨ Δ , n , κ , Σ , Γ ⟩} {S = S} {X = X} p M⊢
    rewrite
      allocation-cross-bindings-exchange ext X (anchored (fromℕ n))
        (anchored (lookup-name p)) κ
    | wkᶜ-exchange X Γ =
  M⊢

mutual
  delimiter-reps↑ : ∀ {Δ n} (ρ : VarRel Δ n) (S : Ty n)
      (A : Ty Δ)
    → Reps↑ ρ S (delimiter↑ A)
  delimiter-reps↑ ρ S (＇ X) = reps-id↑
  delimiter-reps↑ ρ S (‵ ι) = reps-id↑
  delimiter-reps↑ ρ S ★ = reps-id↑
  delimiter-reps↑ ρ S (A ⇒ B) =
    reps-↑⇒ (delimiter-reps↓ ρ S A) (delimiter-reps↑ ρ S B)
  delimiter-reps↑ ρ S (`∀ A) =
    reps-↑∀ (delimiter-reps↑ (LiftRel ρ) (⇑ᵗ S) A)

  delimiter-reps↓ : ∀ {Δ n} (ρ : VarRel Δ n) (S : Ty n)
      (A : Ty Δ)
    → Reps↓ ρ S (delimiter↓ A)
  delimiter-reps↓ ρ S (＇ X) = reps-id↓
  delimiter-reps↓ ρ S (‵ ι) = reps-id↓
  delimiter-reps↓ ρ S ★ = reps-id↓
  delimiter-reps↓ ρ S (A ⇒ B) =
    reps-↓⇒ (delimiter-reps↑ ρ S A) (delimiter-reps↓ ρ S B)
  delimiter-reps↓ ρ S (`∀ A) =
    reps-↓∀ (delimiter-reps↓ (LiftRel ρ) (⇑ᵗ S) A)

∀-entry-application : ∀ {Δ} → Name → Term Δ → Ty (suc Δ)
  → Term (suc Δ)
∀-entry-application α V A =
  (V ↓⟨ zero ≔ α ⟩ delimiter↓ (wkᵗ zero (`∀ A)))
    ⦂∀ swapᵗ (⇑ᵗ A) [ ＇ zero ]

∀-entry-application-typed : ∀ {Γ} {V : Term (Δᵉ Γ)}
    {A : Ty (suc (Δᵉ Γ))} {α : Name} {R : Ty (sizeᵉ Γ)}
  → (p : α ⦂ R ∈ Σᵉ Γ)
  → Γ ⊢ V ⦂ `∀ A
  → cross-ctx Γ zero p ⊢ ∀-entry-application α V A ⦂ A
∀-entry-application-typed {Γ} {V = V} {A = A} {α = α} {R = R} p V⊢ =
  subst
    (λ T → cross-ctx Γ zero p ⊢ ∀-entry-application α V A ⦂ T)
    (swap-shift-open-zero A) (⊢• exchanged⊢)
  where
  entered⊢ : cross-ctx Γ zero p ⊢
      V ↓⟨ zero ≔ α ⟩ delimiter↓ (wkᵗ zero (`∀ A))
      ⦂ wkᵗ zero (`∀ A)
  entered⊢ =
    ⊢conceal p (delimiter-strict↓ zero (wkᵗ zero (`∀ A)))
      (delimiter-reps↓
        (BindingRel (κᵉ (cross-ctx Γ zero p))) R
        (wkᵗ zero (`∀ A))) V⊢

  exchanged⊢ : cross-ctx Γ zero p ⊢
      V ↓⟨ zero ≔ α ⟩ delimiter↓ (wkᵗ zero (`∀ A))
      ⦂ `∀ (swapᵗ (⇑ᵗ A))
  exchanged⊢ =
    subst
      (λ T → cross-ctx Γ zero p ⊢
        V ↓⟨ zero ≔ α ⟩ delimiter↓ (wkᵗ zero (`∀ A)) ⦂ T)
      (wk-zero-∀-swap A) entered⊢

------------------------------------------------------------------------
-- β-inst: redex, exchanged contractum, and typing validation
------------------------------------------------------------------------

β-inst-redex : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
  → Term Δ
  → instᵐ μ ⊢ A ∼ ⇑ᵗ B
  → B ≢ ★
  → Term Δ
β-inst-redex V c B≢★ = V ⟨ (inst c) B≢★ ⟩

β-inst-result : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
  → Name
  → Term Δ
  → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → Conv↑ (suc Δ) A (wkᵗ zero (A [ ★ ]ᵗ))
  → Term Δ
β-inst-result {A = A} α V c d =
  ((∀-entry-application α V A) ↑⟨ zero ≔ α ⟩ d)
  ⟨ c [ ★/0 ]ᶜ ⟩

β-inst-redex-typed : ∀ {Γ} {μ : Env∼ (Δᵉ Γ)}
    {A : Ty (suc (Δᵉ Γ))} {B : Ty (Δᵉ Γ)} {V : Term (Δᵉ Γ)}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
  → Γ ⊢ V ⦂ `∀ A
  → (B≢★ : B ≢ ★)
  → Γ ⊢ β-inst-redex V c B≢★ ⦂ B
β-inst-redex-typed {c = c} V⊢ B≢★ = ⊢⟨⟩ V⊢ ((inst c) B≢★)

β-inst-result-typed : ∀ {Γ} {μ : Env∼ (Δᵉ Γ)}
    {A : Ty (suc (Δᵉ Γ))} {B : Ty (Δᵉ Γ)} {V : Term (Δᵉ Γ)}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    {d : Conv↑ (suc (Δᵉ Γ)) A (wkᵗ zero (A [ ★ ]ᵗ))}
  → allocCtx Γ ★ ⊢ V ⦂ `∀ A
  → PivotStrict↑ zero d
  → Reps↑
      (BindingRel
        (κᵉ (cross-ctx (allocCtx Γ ★) zero fresh-lookup)))
      (⇑ᵗ ★) d
  → allocCtx Γ ★ ⊢ β-inst-result (sizeᵉ Γ) V c d ⦂ B
β-inst-result-typed {Γ} {A = A} {V = V} {c = c} {d = d}
    V⊢ d-strict d-reps =
  ⊢⟨⟩ revealed⊢ (c [ ★/0 ]ᶜ)
  where
  Γ⁺ = allocCtx Γ ★
  p = fresh-lookup {Σ = Σᵉ Γ} {R = ★}

  applied⊢ : cross-ctx Γ⁺ zero p ⊢
      ∀-entry-application (sizeᵉ Γ) V A ⦂ A
  applied⊢ = ∀-entry-application-typed p V⊢

  revealed⊢ : Γ⁺ ⊢
      (∀-entry-application (sizeᵉ Γ) V A)
        ↑⟨ zero ≔ sizeᵉ Γ ⟩ d
      ⦂ A [ ★ ]ᵗ
  revealed⊢ = ⊢reveal p d-strict d-reps applied⊢

------------------------------------------------------------------------
-- Endpoint transport for opening a structural `∀` crossing
------------------------------------------------------------------------

cast↑-target : ∀ {Δ} {A B B′ : Ty Δ}
  → B ≡ B′
  → Conv↑ Δ A B
  → Conv↑ Δ A B′
cast↑-target refl c = c

cast↓-source : ∀ {Δ} {A A′ B : Ty Δ}
  → A ≡ A′
  → Conv↓ Δ A B
  → Conv↓ Δ A′ B
cast↓-source refl c = c

cast↑-target-strict : ∀ {Δ} {A B B′ : Ty Δ} {X}
    (eq : B ≡ B′) {c : Conv↑ Δ A B}
  → PivotStrict↑ X c
  → PivotStrict↑ X (cast↑-target eq c)
cast↑-target-strict refl c-strict = c-strict

cast↓-source-strict : ∀ {Δ} {A A′ B : Ty Δ} {X}
    (eq : A ≡ A′) {c : Conv↓ Δ A B}
  → PivotStrict↓ X c
  → PivotStrict↓ X (cast↓-source eq c)
cast↓-source-strict refl c-strict = c-strict

cast↑-target-reps : ∀ {Δ n} {ρ : VarRel Δ n} {S : Ty n}
    {A B B′ : Ty Δ} (eq : B ≡ B′) {c : Conv↑ Δ A B}
  → Reps↑ ρ S c
  → Reps↑ ρ S (cast↑-target eq c)
cast↑-target-reps refl c-reps = c-reps

cast↓-source-reps : ∀ {Δ n} {ρ : VarRel Δ n} {S : Ty n}
    {A A′ B : Ty Δ} (eq : A ≡ A′) {c : Conv↓ Δ A B}
  → Reps↓ ρ S c
  → Reps↓ ρ S (cast↓-source eq c)
cast↓-source-reps refl c-reps = c-reps

open-∀↑ : ∀ {Δ} {X : Fin (suc Δ)} {B : Ty (suc Δ)} {C}
  → Conv↑ (suc (suc Δ)) C (renameᵗ (extᵗ (punchIn X)) B)
  → Conv↑ (suc (suc Δ)) C (wkᵗ (suc X) B)
open-∀↑ {X = X} {B} = cast↑-target (wk-under-∀ X B)

open-∀↓ : ∀ {Δ} {X : Fin (suc Δ)} {B : Ty (suc Δ)} {C}
  → Conv↓ (suc (suc Δ)) (renameᵗ (extᵗ (punchIn X)) B) C
  → Conv↓ (suc (suc Δ)) (wkᵗ (suc X) B) C
open-∀↓ {X = X} {B} = cast↓-source (wk-under-∀ X B)

------------------------------------------------------------------------
-- β-reveal-∀: redex, exchanged contractum, and typing validation
------------------------------------------------------------------------

β-reveal-∀-redex : ∀ {Δ} {B : Ty (suc Δ)} {C}
  → Name
  → Term (suc Δ)
  → (X : Fin (suc Δ))
  → Conv↑ (suc (suc Δ)) C (renameᵗ (extᵗ (punchIn X)) B)
  → Ty Δ
  → Term Δ
β-reveal-∀-redex {B = B} α V X c A =
  (V ↑⟨ X ≔ α ⟩ `∀↑ c) ⦂∀ B [ A ]

β-reveal-∀-result : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)} {C}
  → Name
  → Name
  → (X : Fin (suc Δ))
  → Term (suc Δ)
  → (c : Conv↑ (suc (suc Δ)) C
          (renameᵗ (extᵗ (punchIn X)) B))
  → Conv↑ (suc Δ) B (wkᵗ zero (B [ A ]ᵗ))
  → Term Δ
β-reveal-∀-result {C = C} fresh α X V c d =
  (((∀-entry-application fresh V C)
      ↑⟨ suc X ≔ α ⟩ open-∀↑ c)
  ↑⟨ zero ≔ fresh ⟩ d)

β-reveal-∀-redex-typed : ∀ {Γ} {A : Ty (Δᵉ Γ)}
    {B : Ty (suc (Δᵉ Γ))} {C : Ty (suc (suc (Δᵉ Γ)))}
    {V : Term (suc (Δᵉ Γ))} {X : Fin (suc (Δᵉ Γ))}
    {α : Name} {R : Ty (sizeᵉ Γ)}
    {c : Conv↑ (suc (suc (Δᵉ Γ))) C
           (renameᵗ (extᵗ (punchIn X)) B)}
  → (p : α ⦂ R ∈ Σᵉ Γ)
  → PivotStrict↑ (suc X) c
  → Reps↑ (LiftRel (BindingRel (κᵉ (cross-ctx Γ X p))))
      (⇑ᵗ R) c
  → cross-ctx Γ X p ⊢ V ⦂ `∀ C
  → Γ ⊢ β-reveal-∀-redex α V X c A ⦂ B [ A ]ᵗ
β-reveal-∀-redex-typed {B = B} {X = X} p c-strict c-reps V⊢ =
  ⊢• (⊢reveal p (strict-↑∀ c-strict) (reps-↑∀ c-reps) V⊢)

β-reveal-∀-result-typed : ∀ {Γ} {A : Ty (Δᵉ Γ)}
    {B : Ty (suc (Δᵉ Γ))} {C : Ty (suc (suc (Δᵉ Γ)))}
    {V : Term (suc (Δᵉ Γ))} {X : Fin (suc (Δᵉ Γ))}
    {α : Name} {R S : Ty (sizeᵉ Γ)}
    {c : Conv↑ (suc (suc (Δᵉ Γ))) C
           (renameᵗ (extᵗ (punchIn X)) B)}
    {d : Conv↑ (suc (Δᵉ Γ)) B (wkᵗ zero (B [ A ]ᵗ))}
  → (p : α ⦂ R ∈ Σᵉ Γ)
  → BindingsExtensionality
  → cross-ctx (allocCtx Γ S) X (weaken-lookup p) ⊢ V ⦂ `∀ C
  → Reps↑
      (BindingRel
        (κᵉ
          (cross-ctx (cross-ctx (allocCtx Γ S) zero fresh-lookup)
            (suc X) (weaken-lookup p))))
      (⇑ᵗ R) c
  → PivotStrict↑ (suc X) c
  → Reps↑
      (BindingRel
        (κᵉ (cross-ctx (allocCtx Γ S) zero fresh-lookup)))
      (⇑ᵗ S) d
  → PivotStrict↑ zero d
  → allocCtx Γ S ⊢
      β-reveal-∀-result (sizeᵉ Γ) α X V c d ⦂ B [ A ]ᵗ
β-reveal-∀-result-typed {Γ} {B = B} {C = C} {V = V} {X = X}
    {α = α} {S = S} {c = c} {d = d}
    p ext V⊢ c-reps c-strict d-reps d-strict =
  ⊢reveal fresh d-strict d-reps old-revealed⊢
  where
  Γ⁺ = allocCtx Γ S
  fresh = fresh-lookup {Σ = Σᵉ Γ} {R = S}
  freshΓ = cross-ctx Γ⁺ zero fresh
  old = weaken-lookup p
  oldΓ = cross-ctx Γ⁺ X old

  inner-left⊢ : cross-ctx oldΓ zero fresh ⊢
      ∀-entry-application (sizeᵉ Γ) V C ⦂ C
  inner-left⊢ = ∀-entry-application-typed fresh V⊢

  inner-right⊢ : cross-ctx freshΓ (suc X) old ⊢
      ∀-entry-application (sizeᵉ Γ) V C ⦂ C
  inner-right⊢ = cross-ctx-exchange-typing ext p inner-left⊢

  old-revealed⊢ : freshΓ ⊢
      (∀-entry-application (sizeᵉ Γ) V C)
        ↑⟨ suc X ≔ α ⟩ open-∀↑ c
      ⦂ B
  old-revealed⊢ =
    ⊢reveal old
      (cast↑-target-strict (wk-under-∀ X B) c-strict)
      (cast↑-target-reps (wk-under-∀ X B) c-reps)
      inner-right⊢

------------------------------------------------------------------------
-- β-conceal-∀: redex, exchanged contractum, and typing validation
------------------------------------------------------------------------

β-conceal-∀-redex : ∀ {Δ} {B : Ty (suc (suc Δ))}
    {C : Ty (suc Δ)}
  → Name
  → Term Δ
  → (X : Fin (suc Δ))
  → Conv↓ (suc (suc Δ)) (renameᵗ (extᵗ (punchIn X)) C) B
  → Ty (suc Δ)
  → Term (suc Δ)
β-conceal-∀-redex {B = B} α V X c A =
  (V ↓⟨ X ≔ α ⟩ `∀↓ c) ⦂∀ B [ A ]

β-conceal-∀-result : ∀ {Δ} {A : Ty (suc Δ)}
    {B : Ty (suc (suc Δ))} {C : Ty (suc Δ)}
  → Name
  → Name
  → (X : Fin (suc Δ))
  → Term Δ
  → (c : Conv↓ (suc (suc Δ))
          (renameᵗ (extᵗ (punchIn X)) C) B)
  → Conv↑ (suc (suc Δ)) B (wkᵗ zero (B [ A ]ᵗ))
  → Term (suc Δ)
β-conceal-∀-result {C = C} fresh α X V c d =
  (((∀-entry-application fresh V C)
    ↓⟨ suc X ≔ α ⟩ open-∀↓ c)
  ↑⟨ zero ≔ fresh ⟩ d)

β-conceal-∀-redex-typed : ∀ {Γ}
    {A : Ty (suc (Δᵉ Γ))} {B : Ty (suc (suc (Δᵉ Γ)))}
    {C : Ty (suc (Δᵉ Γ))} {V : Term (Δᵉ Γ)}
    {X : Fin (suc (Δᵉ Γ))} {α : Name} {R : Ty (sizeᵉ Γ)}
    {c : Conv↓ (suc (suc (Δᵉ Γ)))
           (renameᵗ (extᵗ (punchIn X)) C) B}
  → (p : α ⦂ R ∈ Σᵉ Γ)
  → PivotStrict↓ (suc X) c
  → Reps↓ (LiftRel (BindingRel (κᵉ (cross-ctx Γ X p))))
      (⇑ᵗ R) c
  → Γ ⊢ V ⦂ `∀ C
  → cross-ctx Γ X p ⊢
      β-conceal-∀-redex α V X c A ⦂ B [ A ]ᵗ
β-conceal-∀-redex-typed p c-strict c-reps V⊢ =
  ⊢• (⊢conceal p (strict-↓∀ c-strict) (reps-↓∀ c-reps) V⊢)

β-conceal-∀-result-typed : ∀ {Γ}
    {A : Ty (suc (Δᵉ Γ))} {B : Ty (suc (suc (Δᵉ Γ)))}
    {C : Ty (suc (Δᵉ Γ))} {V : Term (Δᵉ Γ)}
    {X : Fin (suc (Δᵉ Γ))} {α : Name} {R S : Ty (sizeᵉ Γ)}
    {c : Conv↓ (suc (suc (Δᵉ Γ)))
           (renameᵗ (extᵗ (punchIn X)) C) B}
    {d : Conv↑ (suc (suc (Δᵉ Γ))) B
           (wkᵗ zero (B [ A ]ᵗ))}
  → (p : α ⦂ R ∈ Σᵉ Γ)
  → BindingsExtensionality
  → allocCtx Γ S ⊢ V ⦂ `∀ C
  → Reps↓
      (BindingRel
        (κᵉ
          (cross-ctx (cross-ctx (allocCtx Γ S) zero fresh-lookup)
            (suc X) (weaken-lookup p))))
      (⇑ᵗ R) c
  → PivotStrict↓ (suc X) c
  → Reps↑
      (BindingRel
        (κᵉ
          (cross-ctx (allocCtx (cross-ctx Γ X p) S) zero fresh-lookup)))
      (⇑ᵗ S) d
  → PivotStrict↑ zero d
  → allocCtx (cross-ctx Γ X p) S ⊢
      β-conceal-∀-result (sizeᵉ Γ) α X V c d ⦂ B [ A ]ᵗ
β-conceal-∀-result-typed {Γ} {B = B} {C = C} {V = V} {X = X}
    {α = α} {S = S} {c = c} {d = d}
    p ext V⊢ c-reps c-strict d-reps d-strict =
  ⊢reveal fresh-final d-strict d-reps concealed-left⊢
  where
  Γ⁺ = allocCtx Γ S
  fresh = fresh-lookup {Σ = Σᵉ Γ} {R = S}
  freshΓ = cross-ctx Γ⁺ zero fresh
  old = weaken-lookup p
  oldΓ = cross-ctx Γ X p
  oldΓ⁺ = allocCtx oldΓ S
  fresh-final = fresh-lookup {Σ = Σᵉ oldΓ} {R = S}

  applied⊢ : freshΓ ⊢
      ∀-entry-application (sizeᵉ Γ) V C ⦂ C
  applied⊢ = ∀-entry-application-typed fresh V⊢

  concealed-right⊢ : cross-ctx freshΓ (suc X) old ⊢
      (∀-entry-application (sizeᵉ Γ) V C)
        ↓⟨ suc X ≔ α ⟩ open-∀↓ c
      ⦂ B
  concealed-right⊢ =
    ⊢conceal old
      (cast↓-source-strict (wk-under-∀ X C) c-strict)
      (cast↓-source-reps (wk-under-∀ X C) c-reps)
      applied⊢

  concealed-left⊢ : cross-ctx oldΓ⁺ zero fresh-final ⊢
      (∀-entry-application (sizeᵉ Γ) V C)
        ↓⟨ suc X ≔ α ⟩ open-∀↓ c
      ⦂ B
  concealed-left⊢ =
    allocation-cross-ctx-exchange-typing ext p concealed-right⊢

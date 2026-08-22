module alt.Reduction where

-- File Charter:
--   * Defines shift-free call-by-value reduction for alt.Terms.
--   * Store allocation changes only the global store; the term type context
--     is fixed by every step and evaluation frames leave siblings untouched.
--   * Restores ordinary beta with annotated, structural substitution.
--   * Provides store-indexed multi-step traces and anchored tag comparison.

open import Data.Fin using (inject₁; zero)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Consistency
open import Primitives
open import alt.Store hiding (bind)
open import alt.Conversion
open import alt.Terms

------------------------------------------------------------------------
-- Store changes
------------------------------------------------------------------------

data StoreΔ : ℕ → ℕ → Set where
  keep : ∀ {n} → StoreΔ n n
  bind : ∀ {n} → Ty n → StoreΔ n (suc n)

applyStore : ∀ {n n′} → StoreΔ n n′ → Store n → Store n′
applyStore keep Σ = Σ
applyStore (bind R) Σ = alt.Store.bind Σ R

applyBinding : ∀ {n n′} → StoreΔ n n′ → Binding n → Binding n′
applyBinding keep ∀-bound = ∀-bound
applyBinding keep (anchored α) = anchored α
applyBinding (bind R) ∀-bound = ∀-bound
applyBinding (bind R) (anchored α) = anchored (inject₁ α)

applyBindings : ∀ {n n′ Δ}
  → StoreΔ n n′
  → Bindings Δ n
  → Bindings Δ n′
applyBindings χ κ X = applyBinding χ (κ X)

data StoreΔs : ℕ → ℕ → Set where
  [] : ∀ {n} → StoreΔs n n
  _∷_ : ∀ {n n′ n″}
    → StoreΔ n n′
    → StoreΔs n′ n″
    → StoreΔs n n″

infixr 5 _∷_

applyStores : ∀ {n n′} → StoreΔs n n′ → Store n → Store n′
applyStores [] Σ = Σ
applyStores (χ ∷ χs) Σ = applyStores χs (applyStore χ Σ)

applyBindingss : ∀ {n n′ Δ}
  → StoreΔs n n′
  → Bindings Δ n
  → Bindings Δ n′
applyBindingss [] κ = κ
applyBindingss (χ ∷ χs) κ = applyBindingss χs (applyBindings χ κ)

------------------------------------------------------------------------
-- Ground-tag comparison through anchors
------------------------------------------------------------------------

data TagMatch {Δ n} (κ : Bindings Δ n) : Ty Δ → Ty Δ → Set where
  match-var : ∀ {X Y α}
    → κ X ≡ anchored α
    → κ Y ≡ anchored α
    → TagMatch κ (＇ X) (＇ Y)

  match-base : ∀ {ι}
    → TagMatch κ (‵ ι) (‵ ι)

  match-fun : TagMatch κ (★ ⇒ ★) (★ ⇒ ★)

  match-all : TagMatch κ (`∀ ★) (`∀ ★)

data TagMismatch {Δ n} (κ : Bindings Δ n) : Ty Δ → Ty Δ → Set where
  mismatch-var : ∀ {X Y α β}
    → κ X ≡ anchored α
    → κ Y ≡ anchored β
    → α ≢ β
    → TagMismatch κ (＇ X) (＇ Y)

  mismatch-var-base : ∀ {X ι}
    → TagMismatch κ (＇ X) (‵ ι)
  mismatch-var-fun : ∀ {X}
    → TagMismatch κ (＇ X) (★ ⇒ ★)
  mismatch-var-all : ∀ {X}
    → TagMismatch κ (＇ X) (`∀ ★)

  mismatch-base-var : ∀ {ι X}
    → TagMismatch κ (‵ ι) (＇ X)
  mismatch-base : ∀ {ι ι′}
    → ι ≢ ι′
    → TagMismatch κ (‵ ι) (‵ ι′)
  mismatch-base-fun : ∀ {ι}
    → TagMismatch κ (‵ ι) (★ ⇒ ★)
  mismatch-base-all : ∀ {ι}
    → TagMismatch κ (‵ ι) (`∀ ★)

  mismatch-fun-var : ∀ {X}
    → TagMismatch κ (★ ⇒ ★) (＇ X)
  mismatch-fun-base : ∀ {ι}
    → TagMismatch κ (★ ⇒ ★) (‵ ι)
  mismatch-fun-all : TagMismatch κ (★ ⇒ ★) (`∀ ★)

  mismatch-all-var : ∀ {X}
    → TagMismatch κ (`∀ ★) (＇ X)
  mismatch-all-base : ∀ {ι}
    → TagMismatch κ (`∀ ★) (‵ ι)
  mismatch-all-fun : TagMismatch κ (`∀ ★) (★ ⇒ ★)

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _∣_⊢_—→[_]_

data _∣_⊢_—→[_]_ : ∀ {n Δ n′}
    → Store n
    → Bindings Δ n
    → Term Δ
    → StoreΔ n n′
    → Term Δ
    → Set where

  δ-⊕ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {op κ₁ κ₂ κ₃}
    → δ op κ₁ κ₂ κ₃
    → Σ ∣ κ ⊢ $ κ₁ ⊕[ op ] $ κ₂ —→[ keep ] $ κ₃

  β : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V N : Term Δ} {A : Ty Δ}
    → Value V
    → Σ ∣ κ ⊢ (ƛ A ˙ N) · V —→[ keep ] N [ V ]

  β-id : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ : Env∼ Δ} {A : Ty Δ} {a : Atom A}
    → Value V
    → Σ ∣ κ ⊢ V ⟨ id {μ = μ} a ⟩ —→[ keep ] V

  β-⇒ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V W : Term Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
    → Value W
    → Σ ∣ κ ⊢ (V ⟨ c ↦ d ⟩) · W —→[ keep ]
        (V · (W ⟨ c ⟩)) ⟨ d ⟩

  β-∀ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)} {C : Ty Δ}
      {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
    → Σ ∣ κ ⊢ (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] —→[ keep ]
        (V ⦂∀ A [ C ]) ⟨ d ⟩

  ground : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ : Env∼ Δ} {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → A ≢ G
    → Σ ∣ κ ⊢ V ⟨ c ! ⟩ —→[ keep ]
        V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩

  expand : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ : Env∼ Δ} {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → G ≢ B
    → Σ ∣ κ ⊢ V ⟨ ？ c ⟩ —→[ keep ]
        V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩

  tag-untag : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ ν : Env∼ Δ} {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : ν ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → TagMatch κ G H
    → Σ ∣ κ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩
        —→[ keep ] V

  tag-untag-bad : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ ν : Env∼ Δ} {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : ν ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → TagMismatch κ G H
    → Σ ∣ κ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩
        —→[ keep ] blame

  blame-bot-intro : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ : Env∼ Δ}
    → Value V
    → Σ ∣ κ ⊢ V ⟨ bot-intro {μ = μ} ⟩ —→[ keep ] blame

  β-reveal-⇒ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term (suc Δ)} {W : Term Δ} {A₀ B₀ : Ty Δ}
      {A B : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : Name}
      {c : Conv↓ (suc Δ) (wkᵗ X A₀) A}
      {d : Conv↑ (suc Δ) B (wkᵗ X B₀)}
    → Value V
    → Value W
    → Σ ∣ κ ⊢ (V ↑[ X ≔ α ] (c ↦↑ d)) · W —→[ keep ]
        (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d

  β-conceal-⇒ : ∀ {n Δ} {Σ : Store n}
      {κ : Bindings (suc Δ) n}
      {V : Term Δ} {W : Term (suc Δ)} {A₀ B₀ : Ty Δ}
      {A′ B′ : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : Name}
      {c : Conv↑ (suc Δ) A′ (wkᵗ X A₀)}
      {d : Conv↓ (suc Δ) (wkᵗ X B₀) B′}
    → Value V
    → Value W
    → Σ ∣ κ ⊢ (V ↓[ X ≔ α ] (c ↦↓ d)) · W —→[ keep ]
        (V · (W ↑[ X ≔ α ] c)) ↓[ X ≔ α ] d

  id-reveal : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {X : TyVar (suc Δ)} {α : Name} {ι κ₀}
    → Σ ∣ κ ⊢ ($ κ₀) ↑[ X ≔ α ] id↑ (‵ ι)
        —→[ keep ] $ κ₀

  conceal-reveal : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {A : Ty Δ} {X : TyVar (suc Δ)} {α : Name}
    → Value V
    → Σ ∣ κ ⊢
        (V ↓[ X ≔ α ] alt.Conversion.seal X (wkᵗ X A))
          ↑[ X ≔ α ] unseal X (wkᵗ X A)
        —→[ keep ] V

  blame-·₁ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {M : Term Δ}
    → Σ ∣ κ ⊢ blame · M —→[ keep ] blame

  blame-·₂ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ}
    → Value V
    → Σ ∣ κ ⊢ V · blame —→[ keep ] blame

  blame-• : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → Σ ∣ κ ⊢ blame ⦂∀ B [ A ] —→[ keep ] blame

  blame-⟨⟩ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → Σ ∣ κ ⊢ blame ⟨ c ⟩ —→[ keep ] blame

  blame-reveal : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {A : Ty (suc Δ)} {B : Ty Δ} {X : TyVar (suc Δ)}
      {α : Name} {c : Conv↑ (suc Δ) A (wkᵗ X B)}
    → Σ ∣ κ ⊢ blame ↑[ X ≔ α ] c —→[ keep ] blame

  blame-conceal : ∀ {n Δ} {Σ : Store n} {κ : Bindings (suc Δ) n}
      {A : Ty Δ} {B : Ty (suc Δ)} {X : TyVar (suc Δ)}
      {α : Name} {c : Conv↓ (suc Δ) (wkᵗ X A) B}
    → Σ ∣ κ ⊢ blame ↓[ X ≔ α ] c —→[ keep ] blame

  blame-⊕₁ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {M : Term Δ} {op : Prim}
    → Σ ∣ κ ⊢ blame ⊕[ op ] M —→[ keep ] blame

  blame-⊕₂ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {op : Prim}
    → Value V
    → Σ ∣ κ ⊢ V ⊕[ op ] blame —→[ keep ] blame

  -- DEVIATION: β-Λ accepts the already endpoint-correct crossing
  -- conversion as data.  The literal generator has an extensionally equal
  -- endpoint whose equality to wkᵗ zero (B [ A ]ᵗ) is not definitional.
  β-Λ : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {A : Ty Δ} {B : Ty (suc Δ)} {R : Ty n}
      {V : Term (suc Δ)}
      {d : Conv↑ (suc Δ) B (wkᵗ zero (B [ A ]ᵗ))}
    → Value V
    → Transport (BindingRel κ) A R
    → Σ ∣ κ ⊢ (Λ V) ⦂∀ B [ A ] —→[ bind R ]
        V ↑[ zero ≔ n ] d

  -- DEVIATION: as for β-Λ, β-gen takes the endpoint-correct exit
  -- conversion as data.  Its entry delimiter is explicit and no term is
  -- renamed when the store grows.
  β-gen : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n}
      {V : Term Δ} {μ : Env∼ Δ} {A C : Ty Δ} {B : Ty (suc Δ)}
      {R : Ty n} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      {d : Conv↑ (suc Δ) B (wkᵗ zero (B [ C ]ᵗ))}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → Transport (BindingRel κ) C R
    → Σ ∣ κ ⊢ (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ]
        —→[ bind R ]
        ((V ↓[ zero ≔ n ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
          ↑[ zero ≔ n ] d

  -- DEVIATION: β-inst, β-reveal-∀, and β-conceal-∀ are omitted.  Their
  -- source forall slot and crossing slot require a typed exchange operation
  -- not present in the settled syntax.  See alt/Design.md.

  ξ-·₁ : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {L L′ M : Term Δ}
    → Σ ∣ κ ⊢ L —→[ χ ] L′
    → Σ ∣ κ ⊢ L · M —→[ χ ] L′ · M

  ξ-·₂ : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {V M M′ : Term Δ}
    → Value V
    → Σ ∣ κ ⊢ M —→[ χ ] M′
    → Σ ∣ κ ⊢ V · M —→[ χ ] V · M′

  ξ-• : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {M M′ : Term Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → Σ ∣ κ ⊢ M —→[ χ ] M′
    → Σ ∣ κ ⊢ M ⦂∀ B [ A ] —→[ χ ] M′ ⦂∀ B [ A ]

  ξ-⟨⟩ : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {M M′ : Term Δ} {μ : Env∼ Δ}
      {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → Σ ∣ κ ⊢ M —→[ χ ] M′
    → Σ ∣ κ ⊢ M ⟨ c ⟩ —→[ χ ] M′ ⟨ c ⟩

  ξ-reveal : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {M M′ : Term (suc Δ)}
      {A : Ty (suc Δ)} {B : Ty Δ} {X : TyVar (suc Δ)}
      {α : Name} {R : Ty n} {c : Conv↑ (suc Δ) A (wkᵗ X B)}
    → (p : α ⦂ R ∈ Σ)
    → Σ ∣ insertBinding X (anchored (lookup-name p)) κ
        ⊢ M —→[ χ ] M′
    → Σ ∣ κ ⊢ M ↑[ X ≔ α ] c
        —→[ χ ] M′ ↑[ X ≔ α ] c

  ξ-conceal : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {M M′ : Term Δ}
      {A : Ty Δ} {B : Ty (suc Δ)} {X : TyVar (suc Δ)}
      {α : Name} {R : Ty n} {c : Conv↓ (suc Δ) (wkᵗ X A) B}
    → (p : α ⦂ R ∈ Σ)
    → Σ ∣ κ ⊢ M —→[ χ ] M′
    → Σ ∣ insertBinding X (anchored (lookup-name p)) κ
        ⊢ M ↓[ X ≔ α ] c —→[ χ ] M′ ↓[ X ≔ α ] c

  ξ-⊕₁ : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {L L′ M : Term Δ} {op : Prim}
    → Σ ∣ κ ⊢ L —→[ χ ] L′
    → Σ ∣ κ ⊢ L ⊕[ op ] M —→[ χ ] L′ ⊕[ op ] M

  ξ-⊕₂ : ∀ {n n′ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {χ : StoreΔ n n′} {V M M′ : Term Δ} {op : Prim}
    → Value V
    → Σ ∣ κ ⊢ M —→[ χ ] M′
    → Σ ∣ κ ⊢ V ⊕[ op ] M —→[ χ ] V ⊕[ op ] M′

  -- DEFERRED: merge rule

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

infix 2 _∣_⊢_—↠[_]_

data _∣_⊢_—↠[_]_ : ∀ {n Δ n′}
    → Store n
    → Bindings Δ n
    → Term Δ
    → StoreΔs n n′
    → Term Δ
    → Set where
  ↠-refl : ∀ {n Δ} {Σ : Store n} {κ : Bindings Δ n} {M : Term Δ}
    → Σ ∣ κ ⊢ M —↠[ [] ] M

  ↠-step : ∀ {n n′ n″ Δ} {Σ : Store n} {κ : Bindings Δ n}
      {M N P : Term Δ} {χ : StoreΔ n n′} {χs : StoreΔs n′ n″}
    → Σ ∣ κ ⊢ M —→[ χ ] N
    → applyStore χ Σ ∣ applyBindings χ κ ⊢ N —↠[ χs ] P
    → Σ ∣ κ ⊢ M —↠[ χ ∷ χs ] P

infix 3 _∎[]
pattern _∎[] M = ↠-refl {M = M}

infixr 2 _—→[_]⟨_⟩_
pattern _—→[_]⟨_⟩_ L χ L—→M M—↠N =
  ↠-step {M = L} {χ = χ} L—→M M—↠N

module CoercionBridge where

-- File Charter:
--   * Typed bridge between the old binary coercions in `Coercions.agda` and
--     the newer list coercions in `CoercionReduction.agda`.
--   * The old-to-new map flattens sequencing and erases explicit identities;
--     the new-to-old map is typed because empty lists need a source type.
--   * Exports typed preservation, quotient-style round trips, and old
--     coercion normalization transported through the new normalizer.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Types
open import Coercions
import CoercionReduction as New
import CoercionEquality as NewEq

old→new : Coercion → New.Coercion
old→new (idᶜ A) = []
old→new (G !) = New.singleᶜ (New._! G)
old→new (((_`? {ℓ = ℓ}) G)) = New.singleᶜ (New._？_ G ℓ)
old→new (c ↦ d) = New.singleᶜ (New._↦_ (old→new c) (old→new d))
old→new (c ⨟ d) = New._⨟_ (old→new c) (old→new d)
old→new (⊥ᶜ A ⇨ B at ℓ) = New.singleᶜ (New.⊥ᶜ_⇨_at_ A B ℓ)

old→new-wt : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → New.⊢_⦂_⇨_ (old→new c) A B
old→new-wt ⊢idᶜ = New.⊢[]
old→new-wt (⊢! g) = New.⊢singleᶜ (New.⊢! g)
old→new-wt (⊢? g) = New.⊢singleᶜ (New.⊢? g)
old→new-wt (⊢↦ cwt dwt) =
  New.⊢singleᶜ (New.⊢↦ (old→new-wt cwt) (old→new-wt dwt))
old→new-wt (⊢⨟ cwt dwt) = New.⊢⨟ (old→new-wt cwt) (old→new-wt dwt)
old→new-wt ⊢⊥ = New.⊢singleᶜ New.⊢⊥

infix 4 _—→ᵒ_
infix 4 _—↠ᵒ_
infix 4 _≈ᵒ_
infix 4 _—↠≈ᵒ_
infix 4 _;ᵒ_—→_
infix 3 _∎ᵒ
infixr 2 _—→ᵒ⟨_⟩_

data _;ᵒ_—→_ : Coercion → Coercion → Coercion → Set where
  β-idLᵒ : ∀ {A c}
    → idᶜ A ;ᵒ c —→ c

  β-idRᵒ : ∀ {B c}
    → c ;ᵒ idᶜ B —→ c

  β-proj-inj-okᵒ : ∀ {G ℓ}
    → G ! ;ᵒ ((_`? {ℓ = ℓ}) G) —→ idᶜ G

  β-proj-inj-badᵒ : ∀ {G H ℓ}
    → G ≢ H
    → G ! ;ᵒ ((_`? {ℓ = ℓ}) H) —→ (⊥ᶜ G ⇨ H at ℓ)

  β-↦ᵒ : ∀ {c d c′ d′}
    → (c ↦ d) ;ᵒ (c′ ↦ d′) —→ ((c′ ⨟ c) ↦ (d ⨟ d′))

  β-⊥Lᵒ : ∀ {A B C d ℓ}
    → ⊢ d ⦂ B ⇨ C
    → (⊥ᶜ A ⇨ B at ℓ) ;ᵒ d —→ (⊥ᶜ A ⇨ C at ℓ)

  β-!⊥ᵒ : ∀ {G B ℓ}
    → G ! ;ᵒ (⊥ᶜ ★ ⇨ B at ℓ) —→ (⊥ᶜ G ⇨ B at ℓ)

  β-↦⊥ᵒ : ∀ {c d A B C D E ℓ}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → (c ↦ d) ;ᵒ (⊥ᶜ (C ⇒ D) ⇨ E at ℓ)
      —→ (⊥ᶜ (A ⇒ B) ⇨ E at ℓ)

data _—→ᵒ_ : Coercion → Coercion → Set where
  ξ-pairᵒ : ∀ {c d e}
    → c ;ᵒ d —→ e
    → (c ⨟ d) —→ᵒ e

  ξ-⨟₁ᵒ : ∀ {c c′ d}
    → c —→ᵒ c′
    → (c ⨟ d) —→ᵒ (c′ ⨟ d)

  ξ-⨟₂ᵒ : ∀ {c d d′}
    → d —→ᵒ d′
    → (c ⨟ d) —→ᵒ (c ⨟ d′)

  ξ-↦₁ᵒ : ∀ {c c′ d}
    → c —→ᵒ c′
    → (c ↦ d) —→ᵒ (c′ ↦ d)

  ξ-↦₂ᵒ : ∀ {c d d′}
    → d —→ᵒ d′
    → (c ↦ d) —→ᵒ (c ↦ d′)

data _—↠ᵒ_ : Coercion → Coercion → Set where
  _∎ᵒ : (c : Coercion) → c —↠ᵒ c

  _—→ᵒ⟨_⟩_ : (c : Coercion) {d e : Coercion}
    → c —→ᵒ d
    → d —↠ᵒ e
    → c —↠ᵒ e

multi-transᵒ : ∀ {c d e}
  → c —↠ᵒ d
  → d —↠ᵒ e
  → c —↠ᵒ e
multi-transᵒ (_ ∎ᵒ) d↠e = d↠e
multi-transᵒ (_ —→ᵒ⟨ c→d ⟩ d↠e) e↠f =
  _ —→ᵒ⟨ c→d ⟩ multi-transᵒ d↠e e↠f

data _≈ᵒ_ : Coercion → Coercion → Set where
  ≈ᵒ-refl : ∀ {c}
    → c ≈ᵒ c

  ≈ᵒ-sym : ∀ {c d}
    → c ≈ᵒ d
    → d ≈ᵒ c

  ≈ᵒ-trans : ∀ {c d e}
    → c ≈ᵒ d
    → d ≈ᵒ e
    → c ≈ᵒ e

  ≈ᵒ-⨟ : ∀ {c c′ d d′}
    → c ≈ᵒ c′
    → d ≈ᵒ d′
    → (c ⨟ d) ≈ᵒ (c′ ⨟ d′)

  ≈ᵒ-↦ : ∀ {c c′ d d′}
    → c ≈ᵒ c′
    → d ≈ᵒ d′
    → (c ↦ d) ≈ᵒ (c′ ↦ d′)

  ≈ᵒ-idL : ∀ {A c}
    → (idᶜ A ⨟ c) ≈ᵒ c

  ≈ᵒ-idR : ∀ {B c}
    → (c ⨟ idᶜ B) ≈ᵒ c

  ≈ᵒ-assoc : ∀ {c d e}
    → ((c ⨟ d) ⨟ e) ≈ᵒ (c ⨟ (d ⨟ e))

data _—↠≈ᵒ_ : Coercion → Coercion → Set where
  ≈ᵒ-done : ∀ {c d}
    → c ≈ᵒ d
    → c —↠≈ᵒ d

  step≈ᵒ : ∀ {c d e}
    → c —→ᵒ d
    → d —↠≈ᵒ e
    → c —↠≈ᵒ e

  eq≈ᵒ : ∀ {c d e}
    → c ≈ᵒ d
    → d —↠≈ᵒ e
    → c —↠≈ᵒ e

multi-trans≈ᵒ : ∀ {c d e}
  → c —↠≈ᵒ d
  → d —↠≈ᵒ e
  → c —↠≈ᵒ e
multi-trans≈ᵒ (≈ᵒ-done c≈d) d↠e = eq≈ᵒ c≈d d↠e
multi-trans≈ᵒ (step≈ᵒ c→d d↠e) e↠f =
  step≈ᵒ c→d (multi-trans≈ᵒ d↠e e↠f)
multi-trans≈ᵒ (eq≈ᵒ c≈d d↠e) e↠f =
  eq≈ᵒ c≈d (multi-trans≈ᵒ d↠e e↠f)

multi-ξ-⨟₁≈ᵒ : ∀ {c c′ d}
  → c —↠≈ᵒ c′
  → (c ⨟ d) —↠≈ᵒ (c′ ⨟ d)
multi-ξ-⨟₁≈ᵒ (≈ᵒ-done c≈c′) =
  ≈ᵒ-done (≈ᵒ-⨟ c≈c′ ≈ᵒ-refl)
multi-ξ-⨟₁≈ᵒ (step≈ᵒ c→d d↠e) =
  step≈ᵒ (ξ-⨟₁ᵒ c→d) (multi-ξ-⨟₁≈ᵒ d↠e)
multi-ξ-⨟₁≈ᵒ (eq≈ᵒ c≈d d↠e) =
  eq≈ᵒ (≈ᵒ-⨟ c≈d ≈ᵒ-refl) (multi-ξ-⨟₁≈ᵒ d↠e)

ξ-head≈ᵒ : ∀ {c d e rest}
  → c ;ᵒ d —→ e
  → (c ⨟ (d ⨟ rest)) —↠≈ᵒ (e ⨟ rest)
ξ-head≈ᵒ c;d→e =
  eq≈ᵒ (≈ᵒ-sym ≈ᵒ-assoc)
    (multi-ξ-⨟₁≈ᵒ
      (step≈ᵒ (ξ-pairᵒ c;d→e) (≈ᵒ-done ≈ᵒ-refl)))

multi-ξ-⨟₂≈ᵒ : ∀ {c d d′}
  → d —↠≈ᵒ d′
  → (c ⨟ d) —↠≈ᵒ (c ⨟ d′)
multi-ξ-⨟₂≈ᵒ (≈ᵒ-done d≈d′) =
  ≈ᵒ-done (≈ᵒ-⨟ ≈ᵒ-refl d≈d′)
multi-ξ-⨟₂≈ᵒ (step≈ᵒ d→e e↠f) =
  step≈ᵒ (ξ-⨟₂ᵒ d→e) (multi-ξ-⨟₂≈ᵒ e↠f)
multi-ξ-⨟₂≈ᵒ (eq≈ᵒ d≈e e↠f) =
  eq≈ᵒ (≈ᵒ-⨟ ≈ᵒ-refl d≈e) (multi-ξ-⨟₂≈ᵒ e↠f)

multi-ξ-↦₁≈ᵒ : ∀ {c c′ d}
  → c —↠≈ᵒ c′
  → (c ↦ d) —↠≈ᵒ (c′ ↦ d)
multi-ξ-↦₁≈ᵒ (≈ᵒ-done c≈c′) =
  ≈ᵒ-done (≈ᵒ-↦ c≈c′ ≈ᵒ-refl)
multi-ξ-↦₁≈ᵒ (step≈ᵒ c→d d↠e) =
  step≈ᵒ (ξ-↦₁ᵒ c→d) (multi-ξ-↦₁≈ᵒ d↠e)
multi-ξ-↦₁≈ᵒ (eq≈ᵒ c≈d d↠e) =
  eq≈ᵒ (≈ᵒ-↦ c≈d ≈ᵒ-refl) (multi-ξ-↦₁≈ᵒ d↠e)

multi-ξ-↦₂≈ᵒ : ∀ {c d d′}
  → d —↠≈ᵒ d′
  → (c ↦ d) —↠≈ᵒ (c ↦ d′)
multi-ξ-↦₂≈ᵒ (≈ᵒ-done d≈d′) =
  ≈ᵒ-done (≈ᵒ-↦ ≈ᵒ-refl d≈d′)
multi-ξ-↦₂≈ᵒ (step≈ᵒ d→e e↠f) =
  step≈ᵒ (ξ-↦₂ᵒ d→e) (multi-ξ-↦₂≈ᵒ e↠f)
multi-ξ-↦₂≈ᵒ (eq≈ᵒ d≈e e↠f) =
  eq≈ᵒ (≈ᵒ-↦ ≈ᵒ-refl d≈e) (multi-ξ-↦₂≈ᵒ e↠f)

record OldIrreducible (c : Coercion) : Set where
  constructor old-irred
  field
    no-old-step : ∀ {d} → ¬ (c —→ᵒ d)

OldNormal : Coercion → Set
OldNormal = OldIrreducible

irred-pair-no-step : ∀ {c d e}
  → New.IrredPairᶜ c d
  → ¬ (New._;_—→ᶜ_ c d e)
irred-pair-no-step New.irred-?! ()
irred-pair-no-step New.irred-?⊥ ()
irred-pair-no-step New.irred-?↦ ()
irred-pair-no-step New.irred-↦! ()

new-normal-no-step : ∀ {c d}
  → New.Normalᶜ c
  → ¬ (New._—→ᶜᶜ_ c d)
new-normal-no-step New.nf-[] ()
new-normal-no-step (New.nf-singleton New.nf-!) (New.ξ-∷ᶜ ())
new-normal-no-step (New.nf-singleton New.nf-?) (New.ξ-∷ᶜ ())
new-normal-no-step (New.nf-singleton (New.nf-↦ cnf dnf))
                    (New.ξ-↦₁ᶜ c→c′) =
  new-normal-no-step cnf c→c′
new-normal-no-step (New.nf-singleton (New.nf-↦ cnf dnf))
                    (New.ξ-↦₂ᶜ d→d′) =
  new-normal-no-step dnf d→d′
new-normal-no-step (New.nf-singleton (New.nf-↦ cnf dnf))
                    (New.ξ-∷ᶜ ())
new-normal-no-step (New.nf-singleton New.nf-⊥) (New.ξ-∷ᶜ ())
new-normal-no-step (New.nf-step snf irred restnf)
                    (New.ξ-pair c;d→e refl) =
  irred-pair-no-step irred c;d→e
new-normal-no-step (New.nf-step snf irred restnf)
                    (New.ξ-∷ᶜ cs→cs′) =
  new-normal-no-step restnf cs→cs′
new-normal-no-step (New.nf-step (New.nf-↦ cnf dnf) irred restnf)
                    (New.ξ-↦₁ᶜ c→c′) =
  new-normal-no-step cnf c→c′
new-normal-no-step (New.nf-step (New.nf-↦ cnf dnf) irred restnf)
                    (New.ξ-↦₂ᶜ d→d′) =
  new-normal-no-step dnf d→d′

mutual
  new→old-crcn : ∀ {c A B}
    → New.⊢_⦂_⇨ᶜ_ c A B
    → Σ[ d ∈ Coercion ] ⊢ d ⦂ A ⇨ B
  new→old-crcn (New.⊢! g) = _ ! , ⊢! g
  new→old-crcn (New.⊢? {G = G} {ℓ = ℓ} g) = (_`? {ℓ = ℓ}) G , ⊢? g
  new→old-crcn (New.⊢↦ cwt dwt) with new→old cwt | new→old dwt
  ... | c , cwt′ | d , dwt′ = c ↦ d , ⊢↦ cwt′ dwt′
  new→old-crcn (New.⊢⊥ {A = A} {B = B} {ℓ = ℓ}) =
    ⊥ᶜ A ⇨ B at ℓ , ⊢⊥

  new→old : ∀ {c A B}
    → New.⊢_⦂_⇨_ c A B
    → Σ[ d ∈ Coercion ] ⊢ d ⦂ A ⇨ B
  new→old New.⊢[] = idᶜ _ , ⊢idᶜ
  new→old (New.⊢∷ cwt New.⊢[]) = new→old-crcn cwt
  new→old (New.⊢∷ cwt (New.⊢∷ dwt restwt))
    with new→old-crcn cwt | new→old (New.⊢∷ dwt restwt)
  ... | c , cwt′ | d , dwt′ = c ⨟ d , ⊢⨟ cwt′ dwt′

mutual
  new→old-crcn-roundtrip : ∀ {c A B}
    → (cwt : New.⊢_⦂_⇨ᶜ_ c A B)
    → old→new (proj₁ (new→old-crcn cwt)) ≡ New.singleᶜ c
  new→old-crcn-roundtrip (New.⊢! g) = refl
  new→old-crcn-roundtrip (New.⊢? g) = refl
  new→old-crcn-roundtrip (New.⊢↦ cwt dwt)
    rewrite new→old-roundtrip cwt | new→old-roundtrip dwt =
    refl
  new→old-crcn-roundtrip New.⊢⊥ = refl

  new→old-roundtrip : ∀ {c A B}
    → (cwt : New.⊢_⦂_⇨_ c A B)
    → old→new (proj₁ (new→old cwt)) ≡ c
  new→old-roundtrip New.⊢[] = refl
  new→old-roundtrip (New.⊢∷ cwt restwt) =
    new→old-cons-roundtrip cwt restwt

  new→old-cons-roundtrip : ∀ {c cs A B C}
    → (cwt : New.⊢_⦂_⇨ᶜ_ c A B)
    → (restwt : New.⊢_⦂_⇨_ cs B C)
    → old→new (proj₁ (new→old (New.⊢∷ cwt restwt))) ≡ c ∷ cs
  new→old-cons-roundtrip cwt New.⊢[] =
    new→old-crcn-roundtrip cwt
  new→old-cons-roundtrip cwt (New.⊢∷ dwt restwt)
    rewrite new→old-crcn-roundtrip cwt
          | new→old-cons-roundtrip dwt restwt =
    refl

new→old-cons≈ : ∀ {c cs A B C}
  → (cwt : New.⊢_⦂_⇨ᶜ_ c A B)
  → (restwt : New.⊢_⦂_⇨_ cs B C)
  → proj₁ (new→old (New.⊢∷ cwt restwt))
    ≈ᵒ
    (proj₁ (new→old-crcn cwt) ⨟ proj₁ (new→old restwt))
new→old-cons≈ cwt New.⊢[] =
  ≈ᵒ-sym ≈ᵒ-idR
new→old-cons≈ cwt (New.⊢∷ dwt restwt) =
  ≈ᵒ-refl

new→old-⨟≈ : ∀ {c d A B C}
  → (cwt : New.⊢_⦂_⇨_ c A B)
  → (dwt : New.⊢_⦂_⇨_ d B C)
  → proj₁ (new→old (New.⊢⨟ cwt dwt))
    ≈ᵒ
    (proj₁ (new→old cwt) ⨟ proj₁ (new→old dwt))
new→old-⨟≈ New.⊢[] dwt =
  ≈ᵒ-sym ≈ᵒ-idL
new→old-⨟≈ (New.⊢∷ cwt New.⊢[]) New.⊢[] =
  ≈ᵒ-sym ≈ᵒ-idR
new→old-⨟≈ (New.⊢∷ cwt New.⊢[]) (New.⊢∷ dwt restwt) =
  ≈ᵒ-refl
new→old-⨟≈ (New.⊢∷ cwt (New.⊢∷ dwt restwt)) ewt =
  ≈ᵒ-trans
    (≈ᵒ-⨟ ≈ᵒ-refl
      (new→old-⨟≈ (New.⊢∷ dwt restwt) ewt))
    (≈ᵒ-sym ≈ᵒ-assoc)

≡⇒≈ᶜ : ∀ {c d}
  → c ≡ d
  → NewEq._≈ᶜ_ c d
≡⇒≈ᶜ refl = NewEq.≈-refl

record TypedOldEq (A B : Ty) (c d : Coercion) : Set where
  constructor typed-old-eq
  field
    left-wt : ⊢ c ⦂ A ⇨ B
    right-wt : ⊢ d ⦂ A ⇨ B
    quotient-eq : NewEq._≈ᶜ_ (old→new c) (old→new d)

old-quotient-roundtrip : ∀ {c A B}
  → (cwt : ⊢ c ⦂ A ⇨ B)
  → TypedOldEq A B c (proj₁ (new→old (old→new-wt cwt)))
old-quotient-roundtrip cwt =
  typed-old-eq
    cwt
    (proj₂ (new→old (old→new-wt cwt)))
    (NewEq.≈-sym (≡⇒≈ᶜ (new→old-roundtrip (old→new-wt cwt))))

old-roundtrip≈ᵒ : ∀ {c A B}
  → (cwt : ⊢ c ⦂ A ⇨ B)
  → c ≈ᵒ proj₁ (new→old (old→new-wt cwt))
old-roundtrip≈ᵒ ⊢idᶜ = ≈ᵒ-refl
old-roundtrip≈ᵒ (⊢! g) = ≈ᵒ-refl
old-roundtrip≈ᵒ (⊢? g) = ≈ᵒ-refl
old-roundtrip≈ᵒ (⊢↦ cwt dwt) =
  ≈ᵒ-↦ (old-roundtrip≈ᵒ cwt) (old-roundtrip≈ᵒ dwt)
old-roundtrip≈ᵒ (⊢⨟ cwt dwt) =
  ≈ᵒ-trans
    (≈ᵒ-⨟ (old-roundtrip≈ᵒ cwt) (old-roundtrip≈ᵒ dwt))
    (≈ᵒ-sym (new→old-⨟≈ (old→new-wt cwt) (old→new-wt dwt)))
old-roundtrip≈ᵒ ⊢⊥ = ≈ᵒ-refl

irred-pair-no-stepᵒ : ∀ {c d A B C e}
  → (cwt : New.⊢_⦂_⇨ᶜ_ c A B)
  → (dwt : New.⊢_⦂_⇨ᶜ_ d B C)
  → New.IrredPairᶜ c d
  → ¬ (proj₁ (new→old-crcn cwt) ;ᵒ
        proj₁ (new→old-crcn dwt) —→ e)
irred-pair-no-stepᵒ (New.⊢? g) (New.⊢! h) New.irred-?! ()
irred-pair-no-stepᵒ (New.⊢? g) New.⊢⊥ New.irred-?⊥ ()
irred-pair-no-stepᵒ (New.⊢? g) (New.⊢↦ cwt dwt) New.irred-?↦ ()
irred-pair-no-stepᵒ (New.⊢↦ cwt dwt) (New.⊢! g) New.irred-↦! ()

irred-head-no-stepᵒ : ∀ {c d cs A B C D e}
  → (cwt : New.⊢_⦂_⇨ᶜ_ c A B)
  → (dwt : New.⊢_⦂_⇨ᶜ_ d B C)
  → (restwt : New.⊢_⦂_⇨_ cs C D)
  → New.IrredPairᶜ c d
  → ¬ (proj₁ (new→old-crcn cwt) ;ᵒ
        proj₁ (new→old (New.⊢∷ dwt restwt)) —→ e)
irred-head-no-stepᵒ (New.⊢? g) (New.⊢! h) New.⊢[]
                      New.irred-?! ()
irred-head-no-stepᵒ (New.⊢? g) (New.⊢! h) (New.⊢∷ restwt restwt′)
                      New.irred-?! ()
irred-head-no-stepᵒ (New.⊢? g) New.⊢⊥ New.⊢[]
                      New.irred-?⊥ ()
irred-head-no-stepᵒ (New.⊢? g) New.⊢⊥ (New.⊢∷ restwt restwt′)
                      New.irred-?⊥ ()
irred-head-no-stepᵒ (New.⊢? g) (New.⊢↦ cwt dwt) New.⊢[]
                      New.irred-?↦ ()
irred-head-no-stepᵒ (New.⊢? g) (New.⊢↦ cwt dwt)
                      (New.⊢∷ restwt restwt′) New.irred-?↦ ()
irred-head-no-stepᵒ (New.⊢↦ cwt dwt) (New.⊢! g) New.⊢[]
                      New.irred-↦! ()
irred-head-no-stepᵒ (New.⊢↦ cwt dwt) (New.⊢! g)
                      (New.⊢∷ restwt restwt′) New.irred-↦! ()

mutual
  single-normal→old-normal : ∀ {c A B}
    → (cwt : New.⊢_⦂_⇨ᶜ_ c A B)
    → New.SingleNormalᶜ c
    → OldNormal (proj₁ (new→old-crcn cwt))
  single-normal→old-normal (New.⊢! g) New.nf-! =
    old-irred (λ ())
  single-normal→old-normal (New.⊢? g) New.nf-? =
    old-irred (λ ())
  single-normal→old-normal (New.⊢↦ cwt dwt) (New.nf-↦ cnf dnf) =
    old-irred
      (λ { (ξ-↦₁ᵒ c→c′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal cwt cnf) c→c′
         ; (ξ-↦₂ᵒ d→d′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal dwt dnf) d→d′ })
  single-normal→old-normal New.⊢⊥ New.nf-⊥ =
    old-irred (λ ())

  new-normal→old-normal : ∀ {c A B}
    → (cwt : New.⊢_⦂_⇨_ c A B)
    → New.Normalᶜ c
    → OldNormal (proj₁ (new→old cwt))
  new-normal→old-normal New.⊢[] New.nf-[] =
    old-irred (λ ())
  new-normal→old-normal (New.⊢∷ cwt New.⊢[])
                          (New.nf-singleton snf) =
    single-normal→old-normal cwt snf
  new-normal→old-normal
    (New.⊢∷ (New.⊢? g) (New.⊢∷ (New.⊢! h) New.⊢[]))
    (New.nf-step snf New.irred-?! restnf) =
    old-irred
      (λ { (ξ-pairᵒ c;rest→e) →
              irred-head-no-stepᵒ (New.⊢? g) (New.⊢! h) New.⊢[]
                                   New.irred-?! c;rest→e
         ; (ξ-⨟₁ᵒ c→c′) →
              OldIrreducible.no-old-step
                (single-normal→old-normal (New.⊢? g) snf) c→c′
         ; (ξ-⨟₂ᵒ rest→rest′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal (New.⊢∷ (New.⊢! h) New.⊢[])
                                        restnf)
                rest→rest′ })
  new-normal→old-normal
    (New.⊢∷ (New.⊢? g) (New.⊢∷ New.⊢⊥ New.⊢[]))
    (New.nf-step snf New.irred-?⊥ restnf) =
    old-irred
      (λ { (ξ-pairᵒ c;rest→e) →
              irred-head-no-stepᵒ (New.⊢? g) New.⊢⊥ New.⊢[]
                                   New.irred-?⊥ c;rest→e
         ; (ξ-⨟₁ᵒ c→c′) →
              OldIrreducible.no-old-step
                (single-normal→old-normal (New.⊢? g) snf) c→c′
         ; (ξ-⨟₂ᵒ rest→rest′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal (New.⊢∷ New.⊢⊥ New.⊢[])
                                        restnf)
                rest→rest′ })
  new-normal→old-normal
    (New.⊢∷ (New.⊢? g) (New.⊢∷ (New.⊢↦ cwt dwt) New.⊢[]))
    (New.nf-step snf New.irred-?↦ restnf) =
    old-irred
      (λ { (ξ-pairᵒ c;rest→e) →
              irred-head-no-stepᵒ (New.⊢? g) (New.⊢↦ cwt dwt)
                                   New.⊢[] New.irred-?↦ c;rest→e
         ; (ξ-⨟₁ᵒ c→c′) →
              OldIrreducible.no-old-step
                (single-normal→old-normal (New.⊢? g) snf) c→c′
         ; (ξ-⨟₂ᵒ rest→rest′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal
                  (New.⊢∷ (New.⊢↦ cwt dwt) New.⊢[]) restnf)
                rest→rest′ })
  new-normal→old-normal
    (New.⊢∷ (New.⊢↦ cwt dwt) (New.⊢∷ (New.⊢! g) New.⊢[]))
    (New.nf-step snf New.irred-↦! restnf) =
    old-irred
      (λ { (ξ-pairᵒ c;rest→e) →
              irred-head-no-stepᵒ (New.⊢↦ cwt dwt) (New.⊢! g)
                                   New.⊢[] New.irred-↦! c;rest→e
         ; (ξ-⨟₁ᵒ c→c′) →
              OldIrreducible.no-old-step
                (single-normal→old-normal (New.⊢↦ cwt dwt) snf) c→c′
         ; (ξ-⨟₂ᵒ rest→rest′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal (New.⊢∷ (New.⊢! g) New.⊢[])
                                        restnf)
                rest→rest′ })
  new-normal→old-normal
    (New.⊢∷ cwt (New.⊢∷ dwt (New.⊢∷ ewt restwt)))
    (New.nf-step snf irred restnf) =
    old-irred
      (λ { (ξ-pairᵒ c;rest→e) →
              irred-head-no-stepᵒ cwt dwt (New.⊢∷ ewt restwt)
                                     irred c;rest→e
         ; (ξ-⨟₁ᵒ c→c′) →
              OldIrreducible.no-old-step
                (single-normal→old-normal cwt snf) c→c′
         ; (ξ-⨟₂ᵒ rest→rest′) →
              OldIrreducible.no-old-step
                (new-normal→old-normal
                  (New.⊢∷ dwt (New.⊢∷ ewt restwt)) restnf)
                rest→rest′ })

β-↦-target≈ᵒ : ∀ {c d c′ d′ A B C D E F}
  → (cwt : New.⊢_⦂_⇨_ c C A)
  → (dwt : New.⊢_⦂_⇨_ d B D)
  → (c′wt : New.⊢_⦂_⇨_ c′ E C)
  → (d′wt : New.⊢_⦂_⇨_ d′ D F)
  → ((proj₁ (new→old c′wt) ⨟ proj₁ (new→old cwt)) ↦
     (proj₁ (new→old dwt) ⨟ proj₁ (new→old d′wt)))
    ≈ᵒ
    proj₁ (new→old-crcn
      (New.⊢↦ (New.⊢⨟ c′wt cwt) (New.⊢⨟ dwt d′wt)))
β-↦-target≈ᵒ cwt dwt c′wt d′wt =
  ≈ᵒ-↦
    (≈ᵒ-sym (new→old-⨟≈ c′wt cwt))
    (≈ᵒ-sym (new→old-⨟≈ dwt d′wt))

new-step→old-quot : ∀ {c d A B}
  → (cwt : New.⊢_⦂_⇨_ c A B)
  → (c→d : c New.—→ᶜᶜ d)
  → proj₁ (new→old cwt)
    —↠≈ᵒ
    proj₁ (new→old (New.preserve-—→ᶜᶜ cwt c→d))
new-step→old-quot
  (New.⊢∷ (New.⊢! g) (New.⊢∷ (New.⊢? h) New.⊢[]))
  (New.ξ-pair New.β-proj-inj-okᶜ refl) =
  step≈ᵒ (ξ-pairᵒ β-proj-inj-okᵒ) (≈ᵒ-done ≈ᵒ-refl)
new-step→old-quot
  (New.⊢∷ (New.⊢! g)
    (New.⊢∷ (New.⊢? h) (New.⊢∷ restwt restwt′)))
  (New.ξ-pair New.β-proj-inj-okᶜ refl) =
  multi-trans≈ᵒ (ξ-head≈ᵒ β-proj-inj-okᵒ)
                 (≈ᵒ-done ≈ᵒ-idL)
new-step→old-quot
  (New.⊢∷ (New.⊢! g) (New.⊢∷ (New.⊢? h) New.⊢[]))
  (New.ξ-pair (New.β-proj-inj-badᶜ G≢H) refl) =
  step≈ᵒ (ξ-pairᵒ (β-proj-inj-badᵒ G≢H)) (≈ᵒ-done ≈ᵒ-refl)
new-step→old-quot
  (New.⊢∷ (New.⊢! g)
    (New.⊢∷ (New.⊢? h) (New.⊢∷ restwt restwt′)))
  (New.ξ-pair (New.β-proj-inj-badᶜ G≢H) refl) =
  ξ-head≈ᵒ (β-proj-inj-badᵒ G≢H)
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt)
    (New.⊢∷ (New.⊢↦ c′wt d′wt) New.⊢[]))
  (New.ξ-pair New.β-↦ᶜ refl) =
  step≈ᵒ (ξ-pairᵒ β-↦ᵒ)
    (≈ᵒ-done (β-↦-target≈ᵒ cwt dwt c′wt d′wt))
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt)
    (New.⊢∷ (New.⊢↦ c′wt d′wt) (New.⊢∷ restwt restwt′)))
  (New.ξ-pair New.β-↦ᶜ refl) =
  multi-trans≈ᵒ (ξ-head≈ᵒ β-↦ᵒ)
    (≈ᵒ-done (≈ᵒ-⨟ (β-↦-target≈ᵒ cwt dwt c′wt d′wt)
                       ≈ᵒ-refl))
new-step→old-quot
  (New.⊢∷ New.⊢⊥ (New.⊢∷ dwt New.⊢[]))
  (New.ξ-pair (New.β-⊥Lᶜ dwt′) refl)
  with New.coercion-crcn-target-unique dwt dwt′
new-step→old-quot
  (New.⊢∷ New.⊢⊥ (New.⊢∷ dwt New.⊢[]))
  (New.ξ-pair (New.β-⊥Lᶜ dwt′) refl) | refl =
  step≈ᵒ (ξ-pairᵒ (β-⊥Lᵒ (proj₂ (new→old-crcn dwt))))
          (≈ᵒ-done ≈ᵒ-refl)
new-step→old-quot
  (New.⊢∷ New.⊢⊥ (New.⊢∷ dwt (New.⊢∷ restwt restwt′)))
  (New.ξ-pair (New.β-⊥Lᶜ dwt′) refl)
  with New.coercion-crcn-target-unique dwt dwt′
new-step→old-quot
  (New.⊢∷ New.⊢⊥ (New.⊢∷ dwt (New.⊢∷ restwt restwt′)))
  (New.ξ-pair (New.β-⊥Lᶜ dwt′) refl) | refl =
  ξ-head≈ᵒ (β-⊥Lᵒ (proj₂ (new→old-crcn dwt)))
new-step→old-quot
  (New.⊢∷ (New.⊢! g) (New.⊢∷ New.⊢⊥ New.⊢[]))
  (New.ξ-pair New.β-!⊥ᶜ refl) =
  step≈ᵒ (ξ-pairᵒ β-!⊥ᵒ) (≈ᵒ-done ≈ᵒ-refl)
new-step→old-quot
  (New.⊢∷ (New.⊢! g)
    (New.⊢∷ New.⊢⊥ (New.⊢∷ restwt restwt′)))
  (New.ξ-pair New.β-!⊥ᶜ refl) =
  ξ-head≈ᵒ β-!⊥ᵒ
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt) (New.⊢∷ New.⊢⊥ New.⊢[]))
  (New.ξ-pair (New.β-↦⊥ᶜ cwt′ dwt′) refl)
  with New.coercion-target-unique cwt cwt′
     | New.coercion-source-unique dwt dwt′
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt) (New.⊢∷ New.⊢⊥ New.⊢[]))
  (New.ξ-pair (New.β-↦⊥ᶜ cwt′ dwt′) refl) | refl | refl =
  step≈ᵒ (ξ-pairᵒ (β-↦⊥ᵒ (proj₂ (new→old cwt))
                            (proj₂ (new→old dwt))))
          (≈ᵒ-done ≈ᵒ-refl)
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt)
    (New.⊢∷ New.⊢⊥ (New.⊢∷ restwt restwt′)))
  (New.ξ-pair (New.β-↦⊥ᶜ cwt′ dwt′) refl)
  with New.coercion-target-unique cwt cwt′
     | New.coercion-source-unique dwt dwt′
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt)
    (New.⊢∷ New.⊢⊥ (New.⊢∷ restwt restwt′)))
  (New.ξ-pair (New.β-↦⊥ᶜ cwt′ dwt′) refl) | refl | refl =
  ξ-head≈ᵒ (β-↦⊥ᵒ (proj₂ (new→old cwt))
                     (proj₂ (new→old dwt)))
new-step→old-quot
  (New.⊢∷ cwt (New.⊢∷ dwt restwt))
  (New.ξ-∷ᶜ rest→rest′) =
  eq≈ᵒ (new→old-cons≈ cwt (New.⊢∷ dwt restwt))
    (multi-trans≈ᵒ
      (multi-ξ-⨟₂≈ᵒ
        (new-step→old-quot (New.⊢∷ dwt restwt) rest→rest′))
      (≈ᵒ-done
        (≈ᵒ-sym
          (new→old-cons≈ cwt
            (New.preserve-—→ᶜᶜ (New.⊢∷ dwt restwt) rest→rest′)))))
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt) New.⊢[])
  (New.ξ-↦₁ᶜ c→c′) =
  multi-ξ-↦₁≈ᵒ (new-step→old-quot cwt c→c′)
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt) (New.⊢∷ restwt restwt′))
  (New.ξ-↦₁ᶜ c→c′) =
  multi-ξ-⨟₁≈ᵒ
    (multi-ξ-↦₁≈ᵒ (new-step→old-quot cwt c→c′))
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt) New.⊢[])
  (New.ξ-↦₂ᶜ d→d′) =
  multi-ξ-↦₂≈ᵒ (new-step→old-quot dwt d→d′)
new-step→old-quot
  (New.⊢∷ (New.⊢↦ cwt dwt) (New.⊢∷ restwt restwt′))
  (New.ξ-↦₂ᶜ d→d′) =
  multi-ξ-⨟₁≈ᵒ
    (multi-ξ-↦₂≈ᵒ (new-step→old-quot dwt d→d′))

new-multi→old-quot : ∀ {c d A B}
  → (cwt : New.⊢_⦂_⇨_ c A B)
  → (c↠d : c New.—↠ᶜᶜ d)
  → proj₁ (new→old cwt)
    —↠≈ᵒ
    proj₁ (new→old (New.preserve-—↠ᶜᶜ cwt c↠d))
new-multi→old-quot cwt (_ New.∎ᶜᶜ) =
  ≈ᵒ-done ≈ᵒ-refl
new-multi→old-quot cwt (_ New.—→ᶜᶜ⟨ c→d ⟩ d↠e) =
  multi-trans≈ᵒ
    (new-step→old-quot cwt c→d)
    (new-multi→old-quot (New.preserve-—→ᶜᶜ cwt c→d) d↠e)

old-normalization : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Σ[ d ∈ Coercion ]
      (⊢ d ⦂ A ⇨ B ×
       c —↠≈ᵒ d ×
       TypedOldEq A B c d ×
       OldNormal d ×
       OldIrreducible d)
old-normalization {c = c} cwt with New.normalization (old→new-wt cwt)
... | n , (c↠n , nf)
  with new→old-roundtrip (New.preserve-—↠ᶜᶜ (old→new-wt cwt) c↠n)
... | eq =
  let nwt = New.preserve-—↠ᶜᶜ (old→new-wt cwt) c↠n
      dnf = new-normal→old-normal nwt nf
      dnormal = dnf , dnf in
  proj₁ (new→old nwt)
  , ( proj₂ (new→old nwt)
    , ( eq≈ᵒ (old-roundtrip≈ᵒ cwt)
              (new-multi→old-quot (old→new-wt cwt) c↠n)
      , ( typed-old-eq cwt (proj₂ (new→old nwt))
            (NewEq.≈-trans
              (NewEq.—↠ᶜᶜ⇒≈ᶜ c↠n)
              (NewEq.≈-sym (≡⇒≈ᶜ eq)))
        , dnormal)))

old-normalization-reduces : ∀ {c A B}
  → (cwt : ⊢ c ⦂ A ⇨ B)
  → c —↠≈ᵒ proj₁ (old-normalization cwt)
old-normalization-reduces cwt =
  proj₁ (proj₂ (proj₂ (old-normalization cwt)))

old-normalization-normal : ∀ {c A B}
  → (cwt : ⊢ c ⦂ A ⇨ B)
  → OldNormal (proj₁ (old-normalization cwt))
old-normalization-normal cwt =
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (old-normalization cwt)))))

old-normalization-irreducible : ∀ {c A B}
  → (cwt : ⊢ c ⦂ A ⇨ B)
  → OldIrreducible (proj₁ (old-normalization cwt))
old-normalization-irreducible cwt =
  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (old-normalization cwt)))))

old→new-coerce : ∀ {A B}
  → (ℓ : Nat)
  → (p : A ~ B)
  → old→new (coerce ℓ p) ≡ New.coerce ℓ p
old→new-coerce ℓ ~-ℕ = refl
old→new-coerce ℓ ~-★ = refl
old→new-coerce ℓ ★~ℕ = refl
old→new-coerce ℓ ℕ~★ = refl
old→new-coerce ℓ (★~⇒ c d)
  rewrite old→new-coerce ℓ c | old→new-coerce ℓ d =
  refl
old→new-coerce ℓ (⇒~★ c d)
  rewrite old→new-coerce ℓ c | old→new-coerce ℓ d =
  refl
old→new-coerce ℓ (~-⇒ c d)
  rewrite old→new-coerce ℓ c | old→new-coerce ℓ d =
  refl

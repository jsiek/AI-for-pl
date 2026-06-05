module proof.CoercionNormalization where

-- File Charter:
--   * Private proof implementation for the coercion/quotiented-coercion
--     bridge.
--   * Proves round trips, reduction transport, and coercion normalization.
--   * The public normalization statement is wrapped by `MetaTheory.agda`.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Types
open import Coercions
open import CoercionNormalizationDefinitions
import proof.CoercionReduction as Quot
import proof.CoercionEquality as QuotEq

private
  coercion→quotiented : Coercion → Quot.Coercion
  coercion→quotiented (idᶜ A) = []
  coercion→quotiented (G !) = Quot.singleᶜ (Quot._! G)
  coercion→quotiented (((_`? {ℓ = ℓ}) G)) =
    Quot.singleᶜ (Quot._？_ G ℓ)
  coercion→quotiented (c ↦ d) =
    Quot.singleᶜ (Quot._↦_ (coercion→quotiented c)
                             (coercion→quotiented d))
  coercion→quotiented (c ⨟ d) =
    Quot._⨟_ (coercion→quotiented c) (coercion→quotiented d)
  coercion→quotiented (⊥ᶜ A ⇨ B at ℓ) =
    Quot.singleᶜ (Quot.⊥ᶜ_⇨_at_ A B ℓ)

  coercion→quotiented-wt : ∀ {c A B}
    → ⊢ c ⦂ A ⇨ B
    → Quot.⊢_⦂_⇨_ (coercion→quotiented c) A B
  coercion→quotiented-wt ⊢idᶜ = Quot.⊢[]
  coercion→quotiented-wt (⊢! g) = Quot.⊢singleᶜ (Quot.⊢! g)
  coercion→quotiented-wt (⊢? g) = Quot.⊢singleᶜ (Quot.⊢? g)
  coercion→quotiented-wt (⊢↦ cwt dwt) =
    Quot.⊢singleᶜ (Quot.⊢↦ (coercion→quotiented-wt cwt)
                             (coercion→quotiented-wt dwt))
  coercion→quotiented-wt (⊢⨟ cwt dwt) =
    Quot.⊢⨟ (coercion→quotiented-wt cwt) (coercion→quotiented-wt dwt)
  coercion→quotiented-wt ⊢⊥ = Quot.⊢singleᶜ Quot.⊢⊥

  mutual
    quotiented-crcn→coercion : ∀ {c A B}
      → Quot.⊢_⦂_⇨ᶜ_ c A B
      → Σ[ d ∈ Coercion ] ⊢ d ⦂ A ⇨ B
    quotiented-crcn→coercion (Quot.⊢! g) = _ ! , ⊢! g
    quotiented-crcn→coercion (Quot.⊢? {G = G} {ℓ = ℓ} g) =
      (_`? {ℓ = ℓ}) G , ⊢? g
    quotiented-crcn→coercion (Quot.⊢↦ cwt dwt)
      with quotiented→coercion cwt | quotiented→coercion dwt
    ... | c , cwt′ | d , dwt′ = c ↦ d , ⊢↦ cwt′ dwt′
    quotiented-crcn→coercion (Quot.⊢⊥ {A = A} {B = B} {ℓ = ℓ}) =
      ⊥ᶜ A ⇨ B at ℓ , ⊢⊥

    quotiented→coercion : ∀ {c A B}
      → Quot.⊢_⦂_⇨_ c A B
      → Σ[ d ∈ Coercion ] ⊢ d ⦂ A ⇨ B
    quotiented→coercion Quot.⊢[] = idᶜ _ , ⊢idᶜ
    quotiented→coercion (Quot.⊢∷ cwt Quot.⊢[]) =
      quotiented-crcn→coercion cwt
    quotiented→coercion (Quot.⊢∷ cwt (Quot.⊢∷ dwt restwt))
      with quotiented-crcn→coercion cwt
         | quotiented→coercion (Quot.⊢∷ dwt restwt)
    ... | c , cwt′ | d , dwt′ = c ⨟ d , ⊢⨟ cwt′ dwt′

  record TypedCoercionEq (A B : Ty) (c d : Coercion) : Set where
    constructor typed-coercion-eq
    field
      left-wt : ⊢ c ⦂ A ⇨ B
      right-wt : ⊢ d ⦂ A ⇨ B
      quotiented-eq : QuotEq._≈ᶜ_ (coercion→quotiented c)
                                    (coercion→quotiented d)

  multi-transᶜʳ : ∀ {c d e}
    → c —↠ᶜʳ d
    → d —↠ᶜʳ e
    → c —↠ᶜʳ e
  multi-transᶜʳ (_ ∎ᶜʳ) d↠e = d↠e
  multi-transᶜʳ (_ —→ᶜʳ⟨ c→d ⟩ d↠e) e↠f =
    _ —→ᶜʳ⟨ c→d ⟩ multi-transᶜʳ d↠e e↠f

  multi-trans≈ᶜʳ : ∀ {c d e}
    → c —↠≈ᶜʳ d
    → d —↠≈ᶜʳ e
    → c —↠≈ᶜʳ e
  multi-trans≈ᶜʳ (≈ᶜʳ-done c≈d) d↠e = eq≈ᶜʳ c≈d d↠e
  multi-trans≈ᶜʳ (step≈ᶜʳ c→d d↠e) e↠f =
    step≈ᶜʳ c→d (multi-trans≈ᶜʳ d↠e e↠f)
  multi-trans≈ᶜʳ (eq≈ᶜʳ c≈d d↠e) e↠f =
    eq≈ᶜʳ c≈d (multi-trans≈ᶜʳ d↠e e↠f)

  multi-ξ-⨟₁≈ᶜʳ : ∀ {c c′ d}
    → c —↠≈ᶜʳ c′
    → (c ⨟ d) —↠≈ᶜʳ (c′ ⨟ d)
  multi-ξ-⨟₁≈ᶜʳ (≈ᶜʳ-done c≈c′) =
    ≈ᶜʳ-done (≈ᶜʳ-⨟ c≈c′ ≈ᶜʳ-refl)
  multi-ξ-⨟₁≈ᶜʳ (step≈ᶜʳ c→d d↠e) =
    step≈ᶜʳ (ξ-⨟₁ᶜʳ c→d) (multi-ξ-⨟₁≈ᶜʳ d↠e)
  multi-ξ-⨟₁≈ᶜʳ (eq≈ᶜʳ c≈d d↠e) =
    eq≈ᶜʳ (≈ᶜʳ-⨟ c≈d ≈ᶜʳ-refl) (multi-ξ-⨟₁≈ᶜʳ d↠e)

  ξ-head≈ᶜʳ : ∀ {c d e rest}
    → c ;ᶜʳ d —→ e
    → (c ⨟ (d ⨟ rest)) —↠≈ᶜʳ (e ⨟ rest)
  ξ-head≈ᶜʳ c;d→e =
    eq≈ᶜʳ (≈ᶜʳ-sym ≈ᶜʳ-assoc)
      (multi-ξ-⨟₁≈ᶜʳ
        (step≈ᶜʳ (ξ-pairᶜʳ c;d→e) (≈ᶜʳ-done ≈ᶜʳ-refl)))

  multi-ξ-⨟₂≈ᶜʳ : ∀ {c d d′}
    → d —↠≈ᶜʳ d′
    → (c ⨟ d) —↠≈ᶜʳ (c ⨟ d′)
  multi-ξ-⨟₂≈ᶜʳ (≈ᶜʳ-done d≈d′) =
    ≈ᶜʳ-done (≈ᶜʳ-⨟ ≈ᶜʳ-refl d≈d′)
  multi-ξ-⨟₂≈ᶜʳ (step≈ᶜʳ d→e e↠f) =
    step≈ᶜʳ (ξ-⨟₂ᶜʳ d→e) (multi-ξ-⨟₂≈ᶜʳ e↠f)
  multi-ξ-⨟₂≈ᶜʳ (eq≈ᶜʳ d≈e e↠f) =
    eq≈ᶜʳ (≈ᶜʳ-⨟ ≈ᶜʳ-refl d≈e) (multi-ξ-⨟₂≈ᶜʳ e↠f)

  multi-ξ-↦₁≈ᶜʳ : ∀ {c c′ d}
    → c —↠≈ᶜʳ c′
    → (c ↦ d) —↠≈ᶜʳ (c′ ↦ d)
  multi-ξ-↦₁≈ᶜʳ (≈ᶜʳ-done c≈c′) =
    ≈ᶜʳ-done (≈ᶜʳ-↦ c≈c′ ≈ᶜʳ-refl)
  multi-ξ-↦₁≈ᶜʳ (step≈ᶜʳ c→d d↠e) =
    step≈ᶜʳ (ξ-↦₁ᶜʳ c→d) (multi-ξ-↦₁≈ᶜʳ d↠e)
  multi-ξ-↦₁≈ᶜʳ (eq≈ᶜʳ c≈d d↠e) =
    eq≈ᶜʳ (≈ᶜʳ-↦ c≈d ≈ᶜʳ-refl) (multi-ξ-↦₁≈ᶜʳ d↠e)

  multi-ξ-↦₂≈ᶜʳ : ∀ {c d d′}
    → d —↠≈ᶜʳ d′
    → (c ↦ d) —↠≈ᶜʳ (c ↦ d′)
  multi-ξ-↦₂≈ᶜʳ (≈ᶜʳ-done d≈d′) =
    ≈ᶜʳ-done (≈ᶜʳ-↦ ≈ᶜʳ-refl d≈d′)
  multi-ξ-↦₂≈ᶜʳ (step≈ᶜʳ d→e e↠f) =
    step≈ᶜʳ (ξ-↦₂ᶜʳ d→e) (multi-ξ-↦₂≈ᶜʳ e↠f)
  multi-ξ-↦₂≈ᶜʳ (eq≈ᶜʳ d≈e e↠f) =
    eq≈ᶜʳ (≈ᶜʳ-↦ ≈ᶜʳ-refl d≈e) (multi-ξ-↦₂≈ᶜʳ e↠f)

  irred-pair-no-step : ∀ {c d e}
    → Quot.IrredPairᶜ c d
    → ¬ (Quot._;_—→ᶜ_ c d e)
  irred-pair-no-step Quot.irred-?! ()
  irred-pair-no-step Quot.irred-?⊥ ()
  irred-pair-no-step Quot.irred-?↦ ()
  irred-pair-no-step Quot.irred-↦! ()

  quotiented-normal-no-step : ∀ {c d}
    → Quot.Normalᶜ c
    → ¬ (Quot._—→ᶜᶜ_ c d)
  quotiented-normal-no-step Quot.nf-[] ()
  quotiented-normal-no-step (Quot.nf-singleton Quot.nf-!) (Quot.ξ-∷ᶜ ())
  quotiented-normal-no-step (Quot.nf-singleton Quot.nf-?) (Quot.ξ-∷ᶜ ())
  quotiented-normal-no-step (Quot.nf-singleton (Quot.nf-↦ cnf dnf))
                      (Quot.ξ-↦₁ᶜ c→c′) =
    quotiented-normal-no-step cnf c→c′
  quotiented-normal-no-step (Quot.nf-singleton (Quot.nf-↦ cnf dnf))
                      (Quot.ξ-↦₂ᶜ d→d′) =
    quotiented-normal-no-step dnf d→d′
  quotiented-normal-no-step (Quot.nf-singleton (Quot.nf-↦ cnf dnf))
                      (Quot.ξ-∷ᶜ ())
  quotiented-normal-no-step (Quot.nf-singleton Quot.nf-⊥) (Quot.ξ-∷ᶜ ())
  quotiented-normal-no-step (Quot.nf-step snf pair-irred restnf)
                      (Quot.ξ-pair c;d→e refl) =
    irred-pair-no-step pair-irred c;d→e
  quotiented-normal-no-step (Quot.nf-step snf pair-irred restnf)
                      (Quot.ξ-∷ᶜ cs→cs′) =
    quotiented-normal-no-step restnf cs→cs′
  quotiented-normal-no-step (Quot.nf-step (Quot.nf-↦ cnf dnf)
                                          pair-irred restnf)
                      (Quot.ξ-↦₁ᶜ c→c′) =
    quotiented-normal-no-step cnf c→c′
  quotiented-normal-no-step (Quot.nf-step (Quot.nf-↦ cnf dnf)
                                          pair-irred restnf)
                      (Quot.ξ-↦₂ᶜ d→d′) =
    quotiented-normal-no-step dnf d→d′

  mutual
    quotiented-crcn→coercion-roundtrip : ∀ {c A B}
      → (cwt : Quot.⊢_⦂_⇨ᶜ_ c A B)
      → coercion→quotiented (proj₁ (quotiented-crcn→coercion cwt)) ≡ Quot.singleᶜ c
    quotiented-crcn→coercion-roundtrip (Quot.⊢! g) = refl
    quotiented-crcn→coercion-roundtrip (Quot.⊢? g) = refl
    quotiented-crcn→coercion-roundtrip (Quot.⊢↦ cwt dwt)
      rewrite quotiented→coercion-roundtrip cwt | quotiented→coercion-roundtrip dwt =
      refl
    quotiented-crcn→coercion-roundtrip Quot.⊢⊥ = refl

    quotiented→coercion-roundtrip : ∀ {c A B}
      → (cwt : Quot.⊢_⦂_⇨_ c A B)
      → coercion→quotiented (proj₁ (quotiented→coercion cwt)) ≡ c
    quotiented→coercion-roundtrip Quot.⊢[] = refl
    quotiented→coercion-roundtrip (Quot.⊢∷ cwt restwt) =
      quotiented→coercion-cons-roundtrip cwt restwt

    quotiented→coercion-cons-roundtrip : ∀ {c cs A B C}
      → (cwt : Quot.⊢_⦂_⇨ᶜ_ c A B)
      → (restwt : Quot.⊢_⦂_⇨_ cs B C)
      → coercion→quotiented (proj₁ (quotiented→coercion (Quot.⊢∷ cwt restwt))) ≡ c ∷ cs
    quotiented→coercion-cons-roundtrip cwt Quot.⊢[] =
      quotiented-crcn→coercion-roundtrip cwt
    quotiented→coercion-cons-roundtrip cwt (Quot.⊢∷ dwt restwt)
      rewrite quotiented-crcn→coercion-roundtrip cwt
            | quotiented→coercion-cons-roundtrip dwt restwt =
      refl

  quotiented→coercion-cons≈ : ∀ {c cs A B C}
    → (cwt : Quot.⊢_⦂_⇨ᶜ_ c A B)
    → (restwt : Quot.⊢_⦂_⇨_ cs B C)
    → proj₁ (quotiented→coercion (Quot.⊢∷ cwt restwt))
      ≈ᶜʳ
      (proj₁ (quotiented-crcn→coercion cwt) ⨟ proj₁ (quotiented→coercion restwt))
  quotiented→coercion-cons≈ cwt Quot.⊢[] =
    ≈ᶜʳ-sym ≈ᶜʳ-idR
  quotiented→coercion-cons≈ cwt (Quot.⊢∷ dwt restwt) =
    ≈ᶜʳ-refl

  quotiented→coercion-⨟≈ : ∀ {c d A B C}
    → (cwt : Quot.⊢_⦂_⇨_ c A B)
    → (dwt : Quot.⊢_⦂_⇨_ d B C)
    → proj₁ (quotiented→coercion (Quot.⊢⨟ cwt dwt))
      ≈ᶜʳ
      (proj₁ (quotiented→coercion cwt) ⨟ proj₁ (quotiented→coercion dwt))
  quotiented→coercion-⨟≈ Quot.⊢[] dwt =
    ≈ᶜʳ-sym ≈ᶜʳ-idL
  quotiented→coercion-⨟≈ (Quot.⊢∷ cwt Quot.⊢[]) Quot.⊢[] =
    ≈ᶜʳ-sym ≈ᶜʳ-idR
  quotiented→coercion-⨟≈ (Quot.⊢∷ cwt Quot.⊢[]) (Quot.⊢∷ dwt restwt) =
    ≈ᶜʳ-refl
  quotiented→coercion-⨟≈ (Quot.⊢∷ cwt (Quot.⊢∷ dwt restwt)) ewt =
    ≈ᶜʳ-trans
      (≈ᶜʳ-⨟ ≈ᶜʳ-refl
        (quotiented→coercion-⨟≈ (Quot.⊢∷ dwt restwt) ewt))
      (≈ᶜʳ-sym ≈ᶜʳ-assoc)

  ≡⇒≈ᶜ : ∀ {c d}
    → c ≡ d
    → QuotEq._≈ᶜ_ c d
  ≡⇒≈ᶜ refl = QuotEq.≈-refl

  coercion-quotiented-roundtrip : ∀ {c A B}
    → (cwt : ⊢ c ⦂ A ⇨ B)
    → TypedCoercionEq A B c (proj₁ (quotiented→coercion (coercion→quotiented-wt cwt)))
  coercion-quotiented-roundtrip cwt =
    typed-coercion-eq
      cwt
      (proj₂ (quotiented→coercion (coercion→quotiented-wt cwt)))
      (QuotEq.≈-sym (≡⇒≈ᶜ (quotiented→coercion-roundtrip (coercion→quotiented-wt cwt))))

  coercion-roundtrip≈ᶜʳ : ∀ {c A B}
    → (cwt : ⊢ c ⦂ A ⇨ B)
    → c ≈ᶜʳ proj₁ (quotiented→coercion (coercion→quotiented-wt cwt))
  coercion-roundtrip≈ᶜʳ ⊢idᶜ = ≈ᶜʳ-refl
  coercion-roundtrip≈ᶜʳ (⊢! g) = ≈ᶜʳ-refl
  coercion-roundtrip≈ᶜʳ (⊢? g) = ≈ᶜʳ-refl
  coercion-roundtrip≈ᶜʳ (⊢↦ cwt dwt) =
    ≈ᶜʳ-↦ (coercion-roundtrip≈ᶜʳ cwt) (coercion-roundtrip≈ᶜʳ dwt)
  coercion-roundtrip≈ᶜʳ (⊢⨟ cwt dwt) =
    ≈ᶜʳ-trans
      (≈ᶜʳ-⨟ (coercion-roundtrip≈ᶜʳ cwt) (coercion-roundtrip≈ᶜʳ dwt))
      (≈ᶜʳ-sym (quotiented→coercion-⨟≈ (coercion→quotiented-wt cwt) (coercion→quotiented-wt dwt)))
  coercion-roundtrip≈ᶜʳ ⊢⊥ = ≈ᶜʳ-refl

  irred-pair-no-stepᶜʳ : ∀ {c d A B C e}
    → (cwt : Quot.⊢_⦂_⇨ᶜ_ c A B)
    → (dwt : Quot.⊢_⦂_⇨ᶜ_ d B C)
    → Quot.IrredPairᶜ c d
    → ¬ (proj₁ (quotiented-crcn→coercion cwt) ;ᶜʳ
          proj₁ (quotiented-crcn→coercion dwt) —→ e)
  irred-pair-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢! h) Quot.irred-?! ()
  irred-pair-no-stepᶜʳ (Quot.⊢? g) Quot.⊢⊥ Quot.irred-?⊥ ()
  irred-pair-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢↦ cwt dwt) Quot.irred-?↦ ()
  irred-pair-no-stepᶜʳ (Quot.⊢↦ cwt dwt) (Quot.⊢! g) Quot.irred-↦! ()

  irred-head-no-stepᶜʳ : ∀ {c d cs A B C D e}
    → (cwt : Quot.⊢_⦂_⇨ᶜ_ c A B)
    → (dwt : Quot.⊢_⦂_⇨ᶜ_ d B C)
    → (restwt : Quot.⊢_⦂_⇨_ cs C D)
    → Quot.IrredPairᶜ c d
    → ¬ (proj₁ (quotiented-crcn→coercion cwt) ;ᶜʳ
          proj₁ (quotiented→coercion (Quot.⊢∷ dwt restwt)) —→ e)
  irred-head-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢! h) Quot.⊢[]
                        Quot.irred-?! ()
  irred-head-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢! h) (Quot.⊢∷ restwt restwt′)
                        Quot.irred-?! ()
  irred-head-no-stepᶜʳ (Quot.⊢? g) Quot.⊢⊥ Quot.⊢[]
                        Quot.irred-?⊥ ()
  irred-head-no-stepᶜʳ (Quot.⊢? g) Quot.⊢⊥ (Quot.⊢∷ restwt restwt′)
                        Quot.irred-?⊥ ()
  irred-head-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢↦ cwt dwt) Quot.⊢[]
                        Quot.irred-?↦ ()
  irred-head-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢↦ cwt dwt)
                        (Quot.⊢∷ restwt restwt′) Quot.irred-?↦ ()
  irred-head-no-stepᶜʳ (Quot.⊢↦ cwt dwt) (Quot.⊢! g) Quot.⊢[]
                        Quot.irred-↦! ()
  irred-head-no-stepᶜʳ (Quot.⊢↦ cwt dwt) (Quot.⊢! g)
                        (Quot.⊢∷ restwt restwt′) Quot.irred-↦! ()

  mutual
    quotiented-single-normal→irreducible : ∀ {c A B}
      → (cwt : Quot.⊢_⦂_⇨ᶜ_ c A B)
      → Quot.SingleNormalᶜ c
      → Irreducible (proj₁ (quotiented-crcn→coercion cwt))
    quotiented-single-normal→irreducible (Quot.⊢! g) Quot.nf-! =
      irred (λ ())
    quotiented-single-normal→irreducible (Quot.⊢? g) Quot.nf-? =
      irred (λ ())
    quotiented-single-normal→irreducible (Quot.⊢↦ cwt dwt) (Quot.nf-↦ cnf dnf) =
      irred
        (λ { (ξ-↦₁ᶜʳ c→c′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible cwt cnf) c→c′
           ; (ξ-↦₂ᶜʳ d→d′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible dwt dnf) d→d′ })
    quotiented-single-normal→irreducible Quot.⊢⊥ Quot.nf-⊥ =
      irred (λ ())

    quotiented-normal→irreducible : ∀ {c A B}
      → (cwt : Quot.⊢_⦂_⇨_ c A B)
      → Quot.Normalᶜ c
      → Irreducible (proj₁ (quotiented→coercion cwt))
    quotiented-normal→irreducible Quot.⊢[] Quot.nf-[] =
      irred (λ ())
    quotiented-normal→irreducible (Quot.⊢∷ cwt Quot.⊢[])
                            (Quot.nf-singleton snf) =
      quotiented-single-normal→irreducible cwt snf
    quotiented-normal→irreducible
      (Quot.⊢∷ (Quot.⊢? g) (Quot.⊢∷ (Quot.⊢! h) Quot.⊢[]))
      (Quot.nf-step snf Quot.irred-?! restnf) =
      irred
        (λ { (ξ-pairᶜʳ c;rest→e) →
                irred-head-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢! h) Quot.⊢[]
                                     Quot.irred-?! c;rest→e
           ; (ξ-⨟₁ᶜʳ c→c′) →
                Irreducible.no-step
                  (quotiented-single-normal→irreducible (Quot.⊢? g) snf) c→c′
           ; (ξ-⨟₂ᶜʳ rest→rest′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible (Quot.⊢∷ (Quot.⊢! h) Quot.⊢[])
                                          restnf)
                  rest→rest′ })
    quotiented-normal→irreducible
      (Quot.⊢∷ (Quot.⊢? g) (Quot.⊢∷ Quot.⊢⊥ Quot.⊢[]))
      (Quot.nf-step snf Quot.irred-?⊥ restnf) =
      irred
        (λ { (ξ-pairᶜʳ c;rest→e) →
                irred-head-no-stepᶜʳ (Quot.⊢? g) Quot.⊢⊥ Quot.⊢[]
                                     Quot.irred-?⊥ c;rest→e
           ; (ξ-⨟₁ᶜʳ c→c′) →
                Irreducible.no-step
                  (quotiented-single-normal→irreducible (Quot.⊢? g) snf) c→c′
           ; (ξ-⨟₂ᶜʳ rest→rest′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible (Quot.⊢∷ Quot.⊢⊥ Quot.⊢[])
                                          restnf)
                  rest→rest′ })
    quotiented-normal→irreducible
      (Quot.⊢∷ (Quot.⊢? g) (Quot.⊢∷ (Quot.⊢↦ cwt dwt) Quot.⊢[]))
      (Quot.nf-step snf Quot.irred-?↦ restnf) =
      irred
        (λ { (ξ-pairᶜʳ c;rest→e) →
                irred-head-no-stepᶜʳ (Quot.⊢? g) (Quot.⊢↦ cwt dwt)
                                     Quot.⊢[] Quot.irred-?↦ c;rest→e
           ; (ξ-⨟₁ᶜʳ c→c′) →
                Irreducible.no-step
                  (quotiented-single-normal→irreducible (Quot.⊢? g) snf) c→c′
           ; (ξ-⨟₂ᶜʳ rest→rest′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible
                    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) Quot.⊢[]) restnf)
                  rest→rest′ })
    quotiented-normal→irreducible
      (Quot.⊢∷ (Quot.⊢↦ cwt dwt) (Quot.⊢∷ (Quot.⊢! g) Quot.⊢[]))
      (Quot.nf-step snf Quot.irred-↦! restnf) =
      irred
        (λ { (ξ-pairᶜʳ c;rest→e) →
                irred-head-no-stepᶜʳ (Quot.⊢↦ cwt dwt) (Quot.⊢! g)
                                     Quot.⊢[] Quot.irred-↦! c;rest→e
           ; (ξ-⨟₁ᶜʳ c→c′) →
                Irreducible.no-step
                  (quotiented-single-normal→irreducible (Quot.⊢↦ cwt dwt) snf) c→c′
           ; (ξ-⨟₂ᶜʳ rest→rest′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible (Quot.⊢∷ (Quot.⊢! g) Quot.⊢[])
                                          restnf)
                  rest→rest′ })
    quotiented-normal→irreducible
      (Quot.⊢∷ cwt (Quot.⊢∷ dwt (Quot.⊢∷ ewt restwt)))
      (Quot.nf-step snf pair-irred restnf) =
      irred
        (λ { (ξ-pairᶜʳ c;rest→e) →
                irred-head-no-stepᶜʳ cwt dwt (Quot.⊢∷ ewt restwt)
                                       pair-irred c;rest→e
           ; (ξ-⨟₁ᶜʳ c→c′) →
                Irreducible.no-step
                  (quotiented-single-normal→irreducible cwt snf) c→c′
           ; (ξ-⨟₂ᶜʳ rest→rest′) →
                Irreducible.no-step
                  (quotiented-normal→irreducible
                    (Quot.⊢∷ dwt (Quot.⊢∷ ewt restwt)) restnf)
                  rest→rest′ })

  β-↦-target≈ᶜʳ : ∀ {c d c′ d′ A B C D E F}
    → (cwt : Quot.⊢_⦂_⇨_ c C A)
    → (dwt : Quot.⊢_⦂_⇨_ d B D)
    → (c′wt : Quot.⊢_⦂_⇨_ c′ E C)
    → (d′wt : Quot.⊢_⦂_⇨_ d′ D F)
    → ((proj₁ (quotiented→coercion c′wt) ⨟ proj₁ (quotiented→coercion cwt)) ↦
       (proj₁ (quotiented→coercion dwt) ⨟ proj₁ (quotiented→coercion d′wt)))
      ≈ᶜʳ
      proj₁ (quotiented-crcn→coercion
        (Quot.⊢↦ (Quot.⊢⨟ c′wt cwt) (Quot.⊢⨟ dwt d′wt)))
  β-↦-target≈ᶜʳ cwt dwt c′wt d′wt =
    ≈ᶜʳ-↦
      (≈ᶜʳ-sym (quotiented→coercion-⨟≈ c′wt cwt))
      (≈ᶜʳ-sym (quotiented→coercion-⨟≈ dwt d′wt))

  quotiented-step→coercion-reduction : ∀ {c d A B}
    → (cwt : Quot.⊢_⦂_⇨_ c A B)
    → (c→d : c Quot.—→ᶜᶜ d)
    → proj₁ (quotiented→coercion cwt)
      —↠≈ᶜʳ
      proj₁ (quotiented→coercion (Quot.preserve-—→ᶜᶜ cwt c→d))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢! g) (Quot.⊢∷ (Quot.⊢? h) Quot.⊢[]))
    (Quot.ξ-pair Quot.β-proj-inj-okᶜ refl) =
    step≈ᶜʳ (ξ-pairᶜʳ β-proj-inj-okᶜʳ) (≈ᶜʳ-done ≈ᶜʳ-refl)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢! g)
      (Quot.⊢∷ (Quot.⊢? h) (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair Quot.β-proj-inj-okᶜ refl) =
    multi-trans≈ᶜʳ (ξ-head≈ᶜʳ β-proj-inj-okᶜʳ)
                   (≈ᶜʳ-done ≈ᶜʳ-idL)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢! g) (Quot.⊢∷ (Quot.⊢? h) Quot.⊢[]))
    (Quot.ξ-pair (Quot.β-proj-inj-badᶜ G≢H) refl) =
    step≈ᶜʳ (ξ-pairᶜʳ (β-proj-inj-badᶜʳ G≢H)) (≈ᶜʳ-done ≈ᶜʳ-refl)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢! g)
      (Quot.⊢∷ (Quot.⊢? h) (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair (Quot.β-proj-inj-badᶜ G≢H) refl) =
    ξ-head≈ᶜʳ (β-proj-inj-badᶜʳ G≢H)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt)
      (Quot.⊢∷ (Quot.⊢↦ c′wt d′wt) Quot.⊢[]))
    (Quot.ξ-pair Quot.β-↦ᶜ refl) =
    step≈ᶜʳ (ξ-pairᶜʳ β-↦ᶜʳ)
      (≈ᶜʳ-done (β-↦-target≈ᶜʳ cwt dwt c′wt d′wt))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt)
      (Quot.⊢∷ (Quot.⊢↦ c′wt d′wt) (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair Quot.β-↦ᶜ refl) =
    multi-trans≈ᶜʳ (ξ-head≈ᶜʳ β-↦ᶜʳ)
      (≈ᶜʳ-done (≈ᶜʳ-⨟ (β-↦-target≈ᶜʳ cwt dwt c′wt d′wt)
                         ≈ᶜʳ-refl))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ dwt Quot.⊢[]))
    (Quot.ξ-pair (Quot.β-⊥Lᶜ dwt′) refl)
    with Quot.coercion-crcn-target-unique dwt dwt′
  quotiented-step→coercion-reduction
    (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ dwt Quot.⊢[]))
    (Quot.ξ-pair (Quot.β-⊥Lᶜ dwt′) refl) | refl =
    step≈ᶜʳ (ξ-pairᶜʳ (β-⊥Lᶜʳ (proj₂ (quotiented-crcn→coercion dwt))))
            (≈ᶜʳ-done ≈ᶜʳ-refl)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ dwt (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair (Quot.β-⊥Lᶜ dwt′) refl)
    with Quot.coercion-crcn-target-unique dwt dwt′
  quotiented-step→coercion-reduction
    (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ dwt (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair (Quot.β-⊥Lᶜ dwt′) refl) | refl =
    ξ-head≈ᶜʳ (β-⊥Lᶜʳ (proj₂ (quotiented-crcn→coercion dwt)))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢! g) (Quot.⊢∷ Quot.⊢⊥ Quot.⊢[]))
    (Quot.ξ-pair Quot.β-!⊥ᶜ refl) =
    step≈ᶜʳ (ξ-pairᶜʳ β-!⊥ᶜʳ) (≈ᶜʳ-done ≈ᶜʳ-refl)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢! g)
      (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair Quot.β-!⊥ᶜ refl) =
    ξ-head≈ᶜʳ β-!⊥ᶜʳ
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) (Quot.⊢∷ Quot.⊢⊥ Quot.⊢[]))
    (Quot.ξ-pair (Quot.β-↦⊥ᶜ cwt′ dwt′) refl)
    with Quot.coercion-target-unique cwt cwt′
       | Quot.coercion-source-unique dwt dwt′
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) (Quot.⊢∷ Quot.⊢⊥ Quot.⊢[]))
    (Quot.ξ-pair (Quot.β-↦⊥ᶜ cwt′ dwt′) refl) | refl | refl =
    step≈ᶜʳ (ξ-pairᶜʳ (β-↦⊥ᶜʳ (proj₂ (quotiented→coercion cwt))
                              (proj₂ (quotiented→coercion dwt))))
            (≈ᶜʳ-done ≈ᶜʳ-refl)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt)
      (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair (Quot.β-↦⊥ᶜ cwt′ dwt′) refl)
    with Quot.coercion-target-unique cwt cwt′
       | Quot.coercion-source-unique dwt dwt′
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt)
      (Quot.⊢∷ Quot.⊢⊥ (Quot.⊢∷ restwt restwt′)))
    (Quot.ξ-pair (Quot.β-↦⊥ᶜ cwt′ dwt′) refl) | refl | refl =
    ξ-head≈ᶜʳ (β-↦⊥ᶜʳ (proj₂ (quotiented→coercion cwt))
                       (proj₂ (quotiented→coercion dwt)))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ cwt (Quot.⊢∷ dwt restwt))
    (Quot.ξ-∷ᶜ rest→rest′) =
    eq≈ᶜʳ (quotiented→coercion-cons≈ cwt (Quot.⊢∷ dwt restwt))
      (multi-trans≈ᶜʳ
        (multi-ξ-⨟₂≈ᶜʳ
          (quotiented-step→coercion-reduction (Quot.⊢∷ dwt restwt) rest→rest′))
        (≈ᶜʳ-done
          (≈ᶜʳ-sym
            (quotiented→coercion-cons≈ cwt
              (Quot.preserve-—→ᶜᶜ (Quot.⊢∷ dwt restwt) rest→rest′)))))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) Quot.⊢[])
    (Quot.ξ-↦₁ᶜ c→c′) =
    multi-ξ-↦₁≈ᶜʳ (quotiented-step→coercion-reduction cwt c→c′)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) (Quot.⊢∷ restwt restwt′))
    (Quot.ξ-↦₁ᶜ c→c′) =
    multi-ξ-⨟₁≈ᶜʳ
      (multi-ξ-↦₁≈ᶜʳ (quotiented-step→coercion-reduction cwt c→c′))
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) Quot.⊢[])
    (Quot.ξ-↦₂ᶜ d→d′) =
    multi-ξ-↦₂≈ᶜʳ (quotiented-step→coercion-reduction dwt d→d′)
  quotiented-step→coercion-reduction
    (Quot.⊢∷ (Quot.⊢↦ cwt dwt) (Quot.⊢∷ restwt restwt′))
    (Quot.ξ-↦₂ᶜ d→d′) =
    multi-ξ-⨟₁≈ᶜʳ
      (multi-ξ-↦₂≈ᶜʳ (quotiented-step→coercion-reduction dwt d→d′))

  quotiented-multi→coercion-reduction : ∀ {c d A B}
    → (cwt : Quot.⊢_⦂_⇨_ c A B)
    → (c↠d : c Quot.—↠ᶜᶜ d)
    → proj₁ (quotiented→coercion cwt)
      —↠≈ᶜʳ
      proj₁ (quotiented→coercion (Quot.preserve-—↠ᶜᶜ cwt c↠d))
  quotiented-multi→coercion-reduction cwt (_ Quot.∎ᶜᶜ) =
    ≈ᶜʳ-done ≈ᶜʳ-refl
  quotiented-multi→coercion-reduction cwt (_ Quot.—→ᶜᶜ⟨ c→d ⟩ d↠e) =
    multi-trans≈ᶜʳ
      (quotiented-step→coercion-reduction cwt c→d)
      (quotiented-multi→coercion-reduction (Quot.preserve-—→ᶜᶜ cwt c→d) d↠e)

  normalization-with-typing : ∀ {c A B}
    → ⊢ c ⦂ A ⇨ B
    → Σ[ d ∈ Coercion ]
        (⊢ d ⦂ A ⇨ B ×
         c —↠≈ᶜʳ d ×
         TypedCoercionEq A B c d ×
         Irreducible d)
  normalization-with-typing {c = c} cwt with Quot.normalization (coercion→quotiented-wt cwt)
  ... | n , (c↠n , nf)
    with quotiented→coercion-roundtrip (Quot.preserve-—↠ᶜᶜ (coercion→quotiented-wt cwt) c↠n)
  ... | eq =
    let nwt = Quot.preserve-—↠ᶜᶜ (coercion→quotiented-wt cwt) c↠n
        dnf = quotiented-normal→irreducible nwt nf in
    proj₁ (quotiented→coercion nwt)
    , ( proj₂ (quotiented→coercion nwt)
      , ( eq≈ᶜʳ (coercion-roundtrip≈ᶜʳ cwt)
                (quotiented-multi→coercion-reduction (coercion→quotiented-wt cwt) c↠n)
        , ( typed-coercion-eq cwt (proj₂ (quotiented→coercion nwt))
              (QuotEq.≈-trans
                (QuotEq.—↠ᶜᶜ⇒≈ᶜ c↠n)
                (QuotEq.≈-sym (≡⇒≈ᶜ eq)))
          , dnf)))

  normalization-reduces : ∀ {c A B}
    → (cwt : ⊢ c ⦂ A ⇨ B)
    → c —↠≈ᶜʳ proj₁ (normalization-with-typing cwt)
  normalization-reduces cwt =
    proj₁ (proj₂ (proj₂ (normalization-with-typing cwt)))

  normalization-irreducible : ∀ {c A B}
    → (cwt : ⊢ c ⦂ A ⇨ B)
    → Irreducible (proj₁ (normalization-with-typing cwt))
  normalization-irreducible cwt =
    proj₂ (proj₂ (proj₂ (proj₂ (normalization-with-typing cwt))))

normalization : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Σ[ d ∈ Coercion ] (c —↠≈ᶜʳ d × Irreducible d)
normalization cwt =
  proj₁ (normalization-with-typing cwt)
  , (normalization-reduces cwt , normalization-irreducible cwt)

private
  coercion→quotiented-coerce : ∀ {A B}
    → (ℓ : Nat)
    → (p : A ~ B)
    → coercion→quotiented (coerce ℓ p) ≡ Quot.coerce ℓ p
  coercion→quotiented-coerce ℓ ~-ℕ = refl
  coercion→quotiented-coerce ℓ ~-★ = refl
  coercion→quotiented-coerce ℓ ★~ℕ = refl
  coercion→quotiented-coerce ℓ ℕ~★ = refl
  coercion→quotiented-coerce ℓ (★~⇒ c d)
    rewrite coercion→quotiented-coerce ℓ c | coercion→quotiented-coerce ℓ d =
    refl
  coercion→quotiented-coerce ℓ (⇒~★ c d)
    rewrite coercion→quotiented-coerce ℓ c | coercion→quotiented-coerce ℓ d =
    refl
  coercion→quotiented-coerce ℓ (~-⇒ c d)
    rewrite coercion→quotiented-coerce ℓ c | coercion→quotiented-coerce ℓ d =
    refl

module proof.InterpreterTermNarrowingInversionProof where

-- File Charter:
--   * Inverts intrinsically aligned application and primitive certificates.
--   * Rebuilds alignment around proof-only relational-store prefixes.
--   * Never combines independently inverted term shapes and static roots.
--   * Uses only static typing and narrowing; no semantics or reduction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import ImprecisionWf using
  (idι; _↦_; ∀ⁱ_; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterCoercionNarrowing using
  ( apply-coercion
  ; right-static-widening-action
  ; skip-coercion
  )
open import Narrowing.InterpreterReachableCoercionNarrowing using
  ( ReachableComponentCoercionNarrowing
  ; reachable-right-operational
  ; reachable-right-static-narrowing
  )
open import Narrowing.InterpreterReachableCoercionNarrowingProperties using
  (reachable-component-prefix)
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import Primitives using (addℕ)
open import Types
open import proof.InterpreterAlignedTermPrefix using
  (aligned-term-prefix-weaken)

application-aligned-operands :
  ∀ {Φ Δᴸ Δᴿ ρ γ L L′ M M′ B B′ pB} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γ
    (L N.· M) (L′ N.· M′) B B′ pB →
  Σ[ A ∈ Ty ] Σ[ A′ ∈ Ty ]
  Σ[ pA ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)
  × AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ A A′ pA
application-aligned-operands
    (application-aligned function argument) =
  _ , _ , _ , function , argument
application-aligned-operands
    (allocation-prefix-aligned prefix inner source target)
    with application-aligned-operands inner
application-aligned-operands
    (allocation-prefix-aligned prefix inner source target)
    | A , A′ , pA , function , argument =
  A , A′ , pA ,
  aligned-term-prefix-weaken prefix function ,
  aligned-term-prefix-weaken prefix argument

application-open-operands :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ L L′ M M′ B B′ pB}
    {R : RelatedWorlds.WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ
    (L N.· M) (L′ N.· M′) B B′ pB →
  Σ[ A ∈ Ty ] Σ[ A′ ∈ Ty ]
  Σ[ pA ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ L L′
      (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)
  × OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M M′ A A′ pA
application-open-operands
    (open-interpreter-narrowing alignment)
    with application-aligned-operands alignment
application-open-operands
    (open-interpreter-narrowing alignment)
    | A , A′ , pA , function , argument =
  A , A′ , pA ,
  open-interpreter-narrowing function ,
  open-interpreter-narrowing argument

primitive-aligned-operands :
  ∀ {Φ Δᴸ Δᴿ ρ γ L L′ M M′} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γ
    L L′ (‵ `ℕ) (‵ `ℕ) idι
  ×
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γ
    M M′ (‵ `ℕ) (‵ `ℕ) idι
primitive-aligned-operands
    (primitive-aligned left right) =
  left , right
primitive-aligned-operands
    (allocation-prefix-aligned prefix inner source target)
    with primitive-aligned-operands inner
primitive-aligned-operands
    (allocation-prefix-aligned prefix inner source target)
    | left , right =
  aligned-term-prefix-weaken prefix left ,
  aligned-term-prefix-weaken prefix right

primitive-open-operands :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ L L′ M M′}
    {R : RelatedWorlds.WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ L L′
    (‵ `ℕ) (‵ `ℕ) idι
  ×
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ M M′
    (‵ `ℕ) (‵ `ℕ) idι
primitive-open-operands
    (open-interpreter-narrowing alignment)
    with primitive-aligned-operands alignment
primitive-open-operands
    (open-interpreter-narrowing alignment)
    | left , right =
  open-interpreter-narrowing left ,
  open-interpreter-narrowing right

paired-instantiation-aligned-body :
  ∀ {Φ Δᴸ Δᴿ ρ γ A A′ L L′ c c′ B B′ p} →
  (terms :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root terms ≡ paired-instantiation-rootᴬ →
  Σ[ C ∈ Ty ] Σ[ C′ ∈ Ty ]
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ ]
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ L L′
      (`∀ C) (`∀ C′) q
paired-instantiation-aligned-body
    (paired-instantiation-aligned
      hA hA′ reveal reveal′ p p⇑ store context body)
    refl =
  _ , _ , _ , body
paired-instantiation-aligned-body
    (left-instantiation-aligned
      hA hA⇑ reveal store context body)
    ()
paired-instantiation-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    with paired-instantiation-aligned-body inner
      root-eq
paired-instantiation-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    | C , C′ , q , body =
  C , C′ , q , aligned-term-prefix-weaken prefix body

paired-instantiation-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ A A′ L L′ c c′ B B′ p}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    paired-instantiation-rootᴬ →
  Σ[ C ∈ Ty ] Σ[ C′ ∈ Ty ]
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ L L′
      (`∀ C) (`∀ C′) q
paired-instantiation-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    with paired-instantiation-aligned-body alignment
      root-eq
paired-instantiation-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    | C , C′ , q , body =
  C , C′ , q , open-interpreter-narrowing body

left-instantiation-aligned-body :
  ∀ {Φ Δᴸ Δᴿ ρ γ A L c N′ B B′ p} →
  (terms :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root terms ≡ left-instantiation-rootᴬ →
  Σ[ C ∈ Ty ]
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ ]
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ L N′
      (`∀ C) B′ q
left-instantiation-aligned-body
    (paired-instantiation-aligned
      hA hA′ reveal reveal′ p p⇑ store context body)
    ()
left-instantiation-aligned-body
    (left-instantiation-aligned
      hA hA⇑ reveal store context body)
    refl =
  _ , _ , body
left-instantiation-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    with left-instantiation-aligned-body inner root-eq
left-instantiation-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    | C , q , body =
  C , q , aligned-term-prefix-weaken prefix body

left-instantiation-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ A L c N′ B B′ p}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    left-instantiation-rootᴬ →
  Σ[ C ∈ Ty ]
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ L N′
      (`∀ C) B′ q
left-instantiation-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    with left-instantiation-aligned-body alignment root-eq
left-instantiation-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    | C , q , body =
  C , q , open-interpreter-narrowing body

right-narrowing-cast-aligned-body :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ c′ A B′ q} →
  (terms :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root terms ≡ right-narrowing-cast-rootᴬ →
  Σ[ A′ ∈ Ty ]
  Σ[ p ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ A A′ p
  × ReachableComponentCoercionNarrowing
      Φ Δᴸ Δᴿ ρ skip-coercion (apply-coercion c′) p q
right-narrowing-cast-aligned-body
    (right-narrowing-cast-aligned seal cast body q)
    refl =
  _ , _ , body , reachable-right-static-narrowing seal cast
right-narrowing-cast-aligned-body
    (right-id-widening-cast-aligned seal cast body q)
    ()
right-narrowing-cast-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    with right-narrowing-cast-aligned-body inner root-eq
right-narrowing-cast-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    | A′ , p , body , action =
  A′ , p , aligned-term-prefix-weaken prefix body ,
  reachable-component-prefix prefix action

right-narrowing-cast-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ M M′ c′ A B′ q}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-narrowing-cast-rootᴬ →
  Σ[ A′ ∈ Ty ]
  Σ[ p ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M M′ A A′ p
  × ReachableComponentCoercionNarrowing
      Φ Δᴸ Δᴿ ρ skip-coercion (apply-coercion c′) p q
right-narrowing-cast-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    with right-narrowing-cast-aligned-body alignment root-eq
right-narrowing-cast-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    | A′ , p , body , action =
  A′ , p , open-interpreter-narrowing body , action

right-id-widening-cast-aligned-body :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ c′ A B′ q} →
  (terms :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root terms ≡ right-id-widening-cast-rootᴬ →
  Σ[ A′ ∈ Ty ]
  Σ[ p ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ A A′ p
  × ReachableComponentCoercionNarrowing
      Φ Δᴸ Δᴿ ρ skip-coercion (apply-coercion c′) p q
right-id-widening-cast-aligned-body
    (right-narrowing-cast-aligned seal cast body q)
    ()
right-id-widening-cast-aligned-body
    (right-id-widening-cast-aligned seal cast body q)
    refl =
  _ , _ , body ,
  reachable-right-operational
    (right-static-widening-action seal cast)
right-id-widening-cast-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    with right-id-widening-cast-aligned-body inner root-eq
right-id-widening-cast-aligned-body
    (allocation-prefix-aligned prefix inner source target)
    root-eq
    | A′ , p , body , action =
  A′ , p , aligned-term-prefix-weaken prefix body ,
  reachable-component-prefix prefix action

right-id-widening-cast-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ M M′ c′ A B′ q}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-id-widening-cast-rootᴬ →
  Σ[ A′ ∈ Ty ]
  Σ[ p ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M M′ A A′ p
  × ReachableComponentCoercionNarrowing
      Φ Δᴸ Δᴿ ρ skip-coercion (apply-coercion c′) p q
right-id-widening-cast-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    with right-id-widening-cast-aligned-body alignment root-eq
right-id-widening-cast-open-body
    (open-interpreter-narrowing alignment)
    root-eq
    | A′ , p , body , action =
  A′ , p , open-interpreter-narrowing body , action

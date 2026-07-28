module proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleMaximality where

-- File Charter:
--   * Maximality proof boundary for the simple exhaustive endpoint MLB
--     algorithm.
--   * Imports raw enumeration completeness, proves whole-list pruning facts,
--     and assembles them into the public maximality theorems.
--   * Depends on `EndpointCanonicalMLBSimpleCompleteness` for the recursive
--     completeness argument and its fuel/instantiation machinery.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (sym; trans)
open import Relation.Nullary using (¬_; no; yes)

open import Types
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  ( allEndpointMlbsAt; below?; dedupe; endpointCtx; first; hasStrictAbove?
  ; pruneStrictlyBelow; pruneStrictlyBelowFrom
  ; rawEndpointMlbsAt; simpleEndpointMlb; MLB
  ; strictlyBelow?
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleSoundness using
  (first-sound; pruneStrictlyBelow-sound; rawEndpointMlbsAt-sound)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleCompleteness using
  ( below?-trueᵢ; dedupe-complete; impᵢ?; rawEndpointMlbsAt-complete
  ; strictlyBelow?-completeᵢ
  )
open import proof.Core.Properties.ImprecisionProperties using (imp?; ⊑-refl-idᵢ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (CommonLowerBoundᵢ)
open import proof.Core.Properties.NuImprecisionWfBridgeProperties using
  (old⊑→wf-idᵢ; ⊑-forgetᵢ)
open import proof.Core.Properties.NuImprecisionTransitivityProperties using
  (⊑-trans-idᵢ)

------------------------------------------------------------------------
-- Layer 2: whole-list pruning facts
------------------------------------------------------------------------

false≠true : false ≡ true → ⊥
false≠true ()

true≠false : true ≡ false → ⊥
true≠false ()

below?-soundᵢ :
  ∀ {Δ A B} →
  below? Δ A B ≡ true →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ
below?-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    with imp? (idᵢ Δ) A B
below?-soundᵢ {Δ = Δ} {A = A} {B = B} ok | yes A⊑B =
  old⊑→wf-idᵢ A⊑B
below?-soundᵢ {Δ = Δ} {A = A} {B = B} ok | no A⋢B =
  ⊥-elim (false≠true ok)

below?-false-soundᵢ :
  ∀ {Δ A B} →
  below? Δ A B ≡ false →
  ¬ (idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ)
below?-false-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    with imp? (idᵢ Δ) A B
below?-false-soundᵢ {Δ = Δ} {A = A} {B = B} ok | yes A⊑B =
  λ _ → ⊥-elim (true≠false ok)
below?-false-soundᵢ {Δ = Δ} {A = A} {B = B} ok | no A⋢B =
  λ A⊑B → A⋢B (⊑-forgetᵢ A⊑B)

strictlyBelow?-soundᵢ :
  ∀ {Δ A B} →
  strictlyBelow? Δ A B ≡ true →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ ×
  ¬ (idᵢ Δ ∣ Δ ⊢ B ⊑ A ⊣ Δ)
strictlyBelow?-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    with below? Δ A B in A≤B | below? Δ B A in B≤A
strictlyBelow?-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    | false | false =
  ⊥-elim (false≠true ok)
strictlyBelow?-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    | false | true =
  ⊥-elim (false≠true ok)
strictlyBelow?-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    | true | false =
  below?-soundᵢ A≤B , below?-false-soundᵢ B≤A
strictlyBelow?-soundᵢ {Δ = Δ} {A = A} {B = B} ok
    | true | true =
  ⊥-elim (false≠true ok)

hasStrictAbove?-cons-falseᵢ :
  ∀ {Δ C A} {xs : List Ty} →
  strictlyBelow? Δ C A ≡ false →
  hasStrictAbove? Δ C (A ∷ xs) ≡ hasStrictAbove? Δ C xs
hasStrictAbove?-cons-falseᵢ {Δ = Δ} {C = C} {A = A} eq
    with strictlyBelow? Δ C A
hasStrictAbove?-cons-falseᵢ {Δ = Δ} {C = C} {A = A} eq
    | false =
  refl
hasStrictAbove?-cons-falseᵢ {Δ = Δ} {C = C} {A = A} eq
    | true =
  ⊥-elim (true≠false eq)

lift-strict-above-evidenceᵢ :
  ∀ {Δ C A} {xs : List Ty} →
  (∃[ E ]
    (E ∈ xs ×
     idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ ×
     ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ))) →
  ∃[ E ]
    (E ∈ A ∷ xs ×
     idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ ×
     ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ))
lift-strict-above-evidenceᵢ evidence =
  proj₁ evidence ,
  there (proj₁ (proj₂ evidence)) ,
  proj₁ (proj₂ (proj₂ evidence)) ,
  proj₂ (proj₂ (proj₂ evidence))

hasStrictAbove?-soundᵢ :
  ∀ {Δ C} {xs : List Ty} →
  hasStrictAbove? Δ C xs ≡ true →
  ∃[ E ]
    (E ∈ xs ×
     idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ ×
     ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ))
hasStrictAbove?-soundᵢ {xs = []} ()
hasStrictAbove?-soundᵢ {Δ = Δ} {C = C} {xs = A ∷ As} ok
    with strictlyBelow? Δ C A in C<A
hasStrictAbove?-soundᵢ {Δ = Δ} {C = C} {xs = A ∷ As} ok
    | true =
  A , here refl , strictlyBelow?-soundᵢ C<A
hasStrictAbove?-soundᵢ {Δ = Δ} {C = C} {xs = A ∷ As} ok
    | false =
  lift-strict-above-evidenceᵢ
    (hasStrictAbove?-soundᵢ {xs = As} ok)

hasStrictAbove?-noneᵢ :
  ∀ {Δ C} {xs : List Ty} →
  (∀ {E} →
    E ∈ xs →
    idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ →
    ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ) →
    ⊥) →
  hasStrictAbove? Δ C xs ≡ false
hasStrictAbove?-noneᵢ {Δ = Δ} {C = C} {xs = xs} reject
    with hasStrictAbove? Δ C xs in above
hasStrictAbove?-noneᵢ {Δ = Δ} {C = C} {xs = xs} reject
    | false =
  refl
hasStrictAbove?-noneᵢ {Δ = Δ} {C = C} {xs = xs} reject
    | true =
  ⊥-elim (reject E∈ C⊑E E⋢C)
  where
    evidence = hasStrictAbove?-soundᵢ above
    E∈ = proj₁ (proj₂ evidence)
    C⊑E = proj₁ (proj₂ (proj₂ evidence))
    E⋢C = proj₂ (proj₂ (proj₂ evidence))

no-strict-selfᵢ :
  ∀ {Δ A E} →
  E ∈ A ∷ [] →
  idᵢ Δ ∣ Δ ⊢ A ⊑ E ⊣ Δ →
  ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ A ⊣ Δ) →
  ⊥
no-strict-selfᵢ (here refl) A⊑A A⋢A = A⋢A A⊑A
no-strict-selfᵢ (there ())

hasStrictAbove?-completeᵢ :
  ∀ {Δ C E} {xs : List Ty} →
  E ∈ xs →
  idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ →
  ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ) →
  hasStrictAbove? Δ C xs ≡ true
hasStrictAbove?-completeᵢ {xs = []} ()
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (here refl) C⊑E ¬E⊑C
    rewrite strictlyBelow?-completeᵢ C⊑E ¬E⊑C =
  refl
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (there E∈) C⊑E ¬E⊑C
    with strictlyBelow? Δ C B
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (there E∈) C⊑E ¬E⊑C
    | true =
  refl
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (there E∈) C⊑E ¬E⊑C
    | false =
  hasStrictAbove?-completeᵢ E∈ C⊑E ¬E⊑C

promote-no-strict-aboveᵢ :
  ∀ {Δ A C E} {xs : List Ty} →
  hasStrictAbove? Δ C xs ≡ false →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ →
  ¬ (idᵢ Δ ∣ Δ ⊢ A ⊑ C ⊣ Δ) →
  E ∈ A ∷ xs →
  idᵢ Δ ∣ Δ ⊢ A ⊑ E ⊣ Δ →
  ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ A ⊣ Δ) →
  ⊥
promote-no-strict-aboveᵢ Cmax C⊑A A⋢C (here refl) A⊑A A⋢A =
  A⋢A A⊑A
promote-no-strict-aboveᵢ
    {Δ = Δ} {A = A} {C = C} {E = E} {xs = xs}
    Cmax C⊑A A⋢C (there E∈) A⊑E E⋢A =
  false≠true (trans (sym Cmax) C<E)
  where
    C⊑E : idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ
    C⊑E = ⊑-trans-idᵢ C⊑A A⊑E
    E⋢C : ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ)
    E⋢C E⊑C = A⋢C (⊑-trans-idᵢ A⊑E E⊑C)
    C<E : hasStrictAbove? Δ C xs ≡ true
    C<E = hasStrictAbove?-completeᵢ E∈ C⊑E E⋢C

list-has-maximalᵢ :
  ∀ {Δ C₀} {xs : List Ty} →
  C₀ ∈ xs →
  ∃[ C ] (C ∈ xs × hasStrictAbove? Δ C xs ≡ false)
list-has-maximalᵢ {xs = []} ()
list-has-maximalᵢ {Δ = Δ} {xs = A ∷ []} C₀∈ =
  A , here refl ,
  hasStrictAbove?-noneᵢ
    {Δ = Δ} {C = A} {xs = A ∷ []} no-strict-selfᵢ
list-has-maximalᵢ {Δ = Δ} {xs = A ∷ B ∷ Bs} C₀∈
    with list-has-maximalᵢ {Δ = Δ} {xs = B ∷ Bs} (here refl)
list-has-maximalᵢ {Δ = Δ} {xs = A ∷ B ∷ Bs} C₀∈
    | C , C∈ , Cmax
    with strictlyBelow? Δ C A in C<A
list-has-maximalᵢ {Δ = Δ} {xs = A ∷ B ∷ Bs} C₀∈
    | C , C∈ , Cmax | false =
  C , there C∈ ,
  trans
    (hasStrictAbove?-cons-falseᵢ
      {Δ = Δ} {C = C} {A = A} {xs = B ∷ Bs} C<A)
    Cmax
list-has-maximalᵢ {Δ = Δ} {xs = A ∷ B ∷ Bs} C₀∈
    | C , C∈ , Cmax | true =
  A , here refl ,
  hasStrictAbove?-noneᵢ
    {Δ = Δ} {C = A} {xs = A ∷ B ∷ Bs}
    (promote-no-strict-aboveᵢ
      {Δ = Δ} {A = A} {C = C} {xs = B ∷ Bs}
      Cmax C⊑A A⋢C)
  where
    C<A-evidence =
      strictlyBelow?-soundᵢ {Δ = Δ} {A = C} {B = A} C<A
    C⊑A = proj₁ C<A-evidence
    A⋢C = proj₂ C<A-evidence

aboveList : TyCtx → Ty → List Ty → List Ty
aboveList Δ C [] = []
aboveList Δ C (A ∷ As) with below? Δ C A
aboveList Δ C (A ∷ As) | true = A ∷ aboveList Δ C As
aboveList Δ C (A ∷ As) | false = aboveList Δ C As

aboveList-soundᵢ :
  ∀ {Δ C E xs} →
  E ∈ aboveList Δ C xs →
  E ∈ xs × idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ
aboveList-soundᵢ {xs = []} ()
aboveList-soundᵢ {Δ = Δ} {C = C} {E = E} {xs = A ∷ As} E∈
    with below? Δ C A in C⊑A?
aboveList-soundᵢ {Δ = Δ} {C = C} {E = .A} {xs = A ∷ As}
    (here refl) | true =
  here refl , below?-soundᵢ C⊑A?
aboveList-soundᵢ {Δ = Δ} {C = C} {E = E} {xs = A ∷ As}
    (there E∈) | true =
  let E∈As , C⊑E = aboveList-soundᵢ E∈ in
  there E∈As , C⊑E
aboveList-soundᵢ {Δ = Δ} {C = C} {E = E} {xs = A ∷ As}
    E∈ | false =
  let E∈As , C⊑E = aboveList-soundᵢ E∈ in
  there E∈As , C⊑E

aboveList-completeᵢ :
  ∀ {Δ C E xs} →
  E ∈ xs →
  idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ →
  E ∈ aboveList Δ C xs
aboveList-completeᵢ {xs = []} () C⊑E
aboveList-completeᵢ {Δ = Δ} {C = C} {E = .A} {xs = A ∷ As}
    (here refl) C⊑A
    rewrite below?-trueᵢ C⊑A =
  here refl
aboveList-completeᵢ {Δ = Δ} {C = C} {E = E} {xs = A ∷ As}
    (there E∈) C⊑E
    with below? Δ C A
aboveList-completeᵢ {Δ = Δ} {C = C} {E = E} {xs = A ∷ As}
    (there E∈) C⊑E | true =
  there (aboveList-completeᵢ E∈ C⊑E)
aboveList-completeᵢ {Δ = Δ} {C = C} {E = E} {xs = A ∷ As}
    (there E∈) C⊑E | false =
  aboveList-completeᵢ E∈ C⊑E

list-has-maximal-aboveᵢ :
  ∀ {Δ C} {xs : List Ty} →
  C ∈ xs →
  idᵢ Δ ∣ Δ ⊢ C ⊑ C ⊣ Δ →
  ∃[ D ]
    (D ∈ xs ×
     hasStrictAbove? Δ D xs ≡ false ×
     idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ)
list-has-maximal-aboveᵢ {Δ = Δ} {C = C} {xs = xs} C∈ C⊑C =
  D , D∈xs , Dmax , C⊑D
  where
    C∈upper : C ∈ aboveList Δ C xs
    C∈upper = aboveList-completeᵢ C∈ C⊑C

    maximal = list-has-maximalᵢ C∈upper

    D : Ty
    D = proj₁ maximal

    D∈upper : D ∈ aboveList Δ C xs
    D∈upper = proj₁ (proj₂ maximal)

    DmaxUpper : hasStrictAbove? Δ D (aboveList Δ C xs) ≡ false
    DmaxUpper = proj₂ (proj₂ maximal)

    D∈xs : D ∈ xs
    D∈xs = proj₁ (aboveList-soundᵢ {xs = xs} D∈upper)

    C⊑D : idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ
    C⊑D = proj₂ (aboveList-soundᵢ {xs = xs} D∈upper)

    Dmax : hasStrictAbove? Δ D xs ≡ false
    Dmax =
      hasStrictAbove?-noneᵢ
        (λ {E} E∈xs D⊑E ¬E⊑D →
          false≠true
            (trans (sym DmaxUpper) (E-above E∈xs D⊑E ¬E⊑D)))
      where
        E-above :
          ∀ {E} →
          E ∈ xs →
          idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ →
          ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ D ⊣ Δ) →
          hasStrictAbove? Δ D (aboveList Δ C xs) ≡ true
        E-above E∈xs D⊑E ¬E⊑D =
          hasStrictAbove?-completeᵢ
            (aboveList-completeᵢ E∈xs (⊑-trans-idᵢ C⊑D D⊑E))
            D⊑E
            ¬E⊑D

pruneStrictlyBelowFrom-no-strict-above :
  ∀ {Δ C all} {xs : List Ty} →
  C ∈ pruneStrictlyBelowFrom Δ all xs →
  hasStrictAbove? Δ C all ≡ false
pruneStrictlyBelowFrom-no-strict-above {xs = []} ()
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} C∈
    with hasStrictAbove? Δ A all in aboveA
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} C∈
    | true =
  pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = As} C∈
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} (here refl)
    | false =
  aboveA
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} (there C∈)
    | false =
  pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = As} C∈

pruneStrictlyBelow-no-strict-above :
  ∀ {Δ C} {xs : List Ty} →
  C ∈ pruneStrictlyBelow Δ xs →
  hasStrictAbove? Δ C xs ≡ false
pruneStrictlyBelow-no-strict-above {Δ = Δ} {C = C} {xs = xs} C∈ =
  pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = xs} {xs = xs} C∈

pruneStrictlyBelowFrom-complete :
  ∀ {Δ C all} {xs : List Ty} →
  C ∈ xs →
  hasStrictAbove? Δ C all ≡ false →
  C ∈ pruneStrictlyBelowFrom Δ all xs
pruneStrictlyBelowFrom-complete {xs = []} () Cmax
pruneStrictlyBelowFrom-complete
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} C∈ Cmax
    with hasStrictAbove? Δ A all in aboveA
pruneStrictlyBelowFrom-complete
    {Δ = Δ} {C = .A} {all = all} {xs = A ∷ As} (here refl) Cmax
    | true =
  ⊥-elim (true≠false (trans (sym aboveA) Cmax))
pruneStrictlyBelowFrom-complete
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} (there C∈) Cmax
    | true =
  pruneStrictlyBelowFrom-complete C∈ Cmax
pruneStrictlyBelowFrom-complete
    {Δ = Δ} {C = .A} {all = all} {xs = A ∷ As} (here refl) Cmax
    | false =
  here refl
pruneStrictlyBelowFrom-complete
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} (there C∈) Cmax
    | false =
  there (pruneStrictlyBelowFrom-complete C∈ Cmax)

pruneStrictlyBelow-complete :
  ∀ {Δ C} {xs : List Ty} →
  C ∈ xs →
  hasStrictAbove? Δ C xs ≡ false →
  C ∈ pruneStrictlyBelow Δ xs
pruneStrictlyBelow-complete C∈ Cmax =
  pruneStrictlyBelowFrom-complete C∈ Cmax

rawEndpointMlbsAt-promote :
  ∀ {Δ A B C} →
  C ∈ rawEndpointMlbsAt Δ A B →
  ∃[ D ]
    (D ∈ allEndpointMlbsAt Δ A B ×
     idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ)
rawEndpointMlbsAt-promote {Δ = Δ} {A = A} {B = B} {C = C} C∈raw =
  D , D∈all , C⊑D
  where
    xs : List Ty
    xs = dedupe (rawEndpointMlbsAt Δ A B)

    C∈xs : C ∈ xs
    C∈xs = dedupe-complete C∈raw

    C-lower :
      idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
      idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
    C-lower =
      rawEndpointMlbsAt-sound
        {Δ = Δ} {A = A} {B = B} C∈raw

    C⊑C : idᵢ Δ ∣ Δ ⊢ C ⊑ C ⊣ Δ
    C⊑C = old⊑→wf-idᵢ (⊑-refl-idᵢ (⊑-src-wf (proj₁ C-lower)))

    maximal = list-has-maximal-aboveᵢ C∈xs C⊑C

    D : Ty
    D = proj₁ maximal

    D∈xs : D ∈ xs
    D∈xs = proj₁ (proj₂ maximal)

    Dmax : hasStrictAbove? Δ D xs ≡ false
    Dmax = proj₁ (proj₂ (proj₂ maximal))

    C⊑D : idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ
    C⊑D = proj₂ (proj₂ (proj₂ maximal))

    D∈all : D ∈ allEndpointMlbsAt Δ A B
    D∈all = pruneStrictlyBelow-complete D∈xs Dmax

first-complete :
  ∀ {C} {xs : List Ty} →
  C ∈ xs →
  ∃[ E ] first xs ≡ just E
first-complete {xs = []} ()
first-complete {xs = A ∷ As} C∈ = A , refl

-- This is success completeness only.  Adding `D ⊑ C` to the conclusion would
-- assert that the selected candidate is a GLB, which is false in general.
MLB-complete :
  ∀ {Δ A B D} →
  WfTy Δ A →
  WfTy Δ B →
  CommonLowerBoundᵢ Δ A B D →
  ∃[ C ] MLB Δ A B ≡ just C
MLB-complete {Δ = Δ} {A = A} {B = B}
    hA hB commonD =
  first-complete C∈all
  where
    coverage = rawEndpointMlbsAt-complete hA hB commonD

    E∈raw : proj₁ coverage ∈ rawEndpointMlbsAt Δ A B
    E∈raw = proj₁ (proj₂ coverage)

    E∈dedupe : proj₁ coverage ∈ dedupe (rawEndpointMlbsAt Δ A B)
    E∈dedupe = dedupe-complete E∈raw

    maximal = list-has-maximalᵢ E∈dedupe

    C∈all :
      proj₁ maximal ∈ allEndpointMlbsAt Δ A B
    C∈all =
      pruneStrictlyBelow-complete
        (proj₁ (proj₂ maximal)) (proj₂ (proj₂ maximal))

simpleEndpointMlb-complete :
  ∀ {A B D} →
  WfTy (endpointCtx A B) A →
  WfTy (endpointCtx A B) B →
  CommonLowerBoundᵢ (endpointCtx A B) A B D →
  ∃[ C ] simpleEndpointMlb A B ≡ just C
simpleEndpointMlb-complete {A = A} {B = B} hA hB commonD =
  MLB-complete
    {Δ = endpointCtx A B} hA hB commonD

------------------------------------------------------------------------
-- Layer 1: public maximality targets
------------------------------------------------------------------------

allEndpointMlbsAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  C ∈ allEndpointMlbsAt Δ A B →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ
allEndpointMlbsAt-maximal {Δ = Δ} {A = A} {B = B} {C = C} {D = D}
    hA hB C∈ commonD C⊑D
    with impᵢ? {Δ = Δ} {A = D} {B = C}
allEndpointMlbsAt-maximal {Δ = Δ} {A = A} {B = B} {C = C} {D = D}
    hA hB C∈ commonD C⊑D | yes D⊑C =
  D⊑C
allEndpointMlbsAt-maximal {Δ = Δ} {A = A} {B = B} {C = C} {D = D}
    hA hB C∈ commonD C⊑D | no ¬D⊑C =
  ⊥-elim (false≠true (trans (sym noAbove) above))
  where
    xs : List Ty
    xs = dedupe (rawEndpointMlbsAt Δ A B)

    C∈xs : C ∈ xs
    C∈xs = pruneStrictlyBelow-sound {Δ = Δ} {xs = xs} C∈

    noAbove : hasStrictAbove? Δ C xs ≡ false
    noAbove = pruneStrictlyBelow-no-strict-above {Δ = Δ} {xs = xs} C∈

    coverage :
      ∃[ E ]
        (E ∈ rawEndpointMlbsAt Δ A B ×
         idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
    coverage =
      rawEndpointMlbsAt-complete hA hB commonD

    E : Ty
    E = proj₁ coverage

    E∈raw : E ∈ rawEndpointMlbsAt Δ A B
    E∈raw = proj₁ (proj₂ coverage)

    D⊑E : idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ
    D⊑E = proj₂ (proj₂ coverage)

    E∈xs : E ∈ xs
    E∈xs = dedupe-complete E∈raw

    C⊑E : idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ
    C⊑E = ⊑-trans-idᵢ C⊑D D⊑E

    ¬E⊑C : ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ)
    ¬E⊑C E⊑C = ¬D⊑C (⊑-trans-idᵢ D⊑E E⊑C)

    above : hasStrictAbove? Δ C xs ≡ true
    above = hasStrictAbove?-completeᵢ E∈xs C⊑E ¬E⊑C

MLB-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  MLB Δ A B ≡ just C →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ
MLB-maximal {Δ = Δ} {A = A} {B = B}
    hA hB eq commonD C⊑D =
  allEndpointMlbsAt-maximal hA hB
    (first-sound {xs = allEndpointMlbsAt Δ A B} eq) commonD C⊑D

simpleEndpointMlb-maximal :
  ∀ {A B C D} →
  WfTy (endpointCtx A B) A →
  WfTy (endpointCtx A B) B →
  simpleEndpointMlb A B ≡ just C →
  CommonLowerBoundᵢ (endpointCtx A B) A B D →
  idᵢ (endpointCtx A B)
    ∣ endpointCtx A B ⊢ C ⊑ D ⊣ endpointCtx A B →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ D ⊑ C ⊣ endpointCtx A B
simpleEndpointMlb-maximal {A = A} {B = B} hA hB eq commonD C⊑D =
  MLB-maximal {Δ = endpointCtx A B} hA hB eq commonD C⊑D

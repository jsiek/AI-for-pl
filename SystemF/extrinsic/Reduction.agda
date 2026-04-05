module extrinsic.Reduction where

-- File Charter:
--   * Dynamic semantics for extrinsic System F.
--   * Defines values, one-step reduction, and multi-step closure.
--   * Re-exports `extrinsic.Terms` for shared syntax/typing.

open import extrinsic.Terms public

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

data Value : Term → Set where
  vLam  : {N : Term} → Value (ƛ N)
  vTrue : Value `true
  vFalse : Value `false
  vZero : Value `zero
  vSuc  : {V : Term} → Value V → Value (`suc V)
  vTlam : {N : Term} → Value (Λ N)

infix 2 _—→_
data _—→_ : Term → Term → Set where
  ξ-·₁ : {L L' M : Term} →
         L —→ L' →
         (L · M) —→ (L' · M)

  ξ-·₂ : {V M M' : Term} →
         Value V →
         M —→ M' →
         (V · M) —→ (V · M')

  β-ƛ : {N W : Term} →
        Value W →
        ((ƛ N) · W) —→ N [ W ]

  ξ-suc : {M M' : Term} →
          M —→ M' →
          (`suc M) —→ (`suc M')

  ξ-if : {L L' M N : Term} →
         L —→ L' →
         (`if_then_else L M N) —→ (`if_then_else L' M N)

  ξ-case : {L L' M N : Term} →
           L —→ L' →
           (case_[zero⇒_|suc⇒_] L M N) —→ (case_[zero⇒_|suc⇒_] L' M N)

  β-true : {M N : Term} →
           (`if_then_else `true M N) —→ M

  β-false : {M N : Term} →
            (`if_then_else `false M N) —→ N

  β-zero : {M N : Term} →
           (case_[zero⇒_|suc⇒_] `zero M N) —→ M

  β-suc : {V M N : Term} →
          Value V →
          (case_[zero⇒_|suc⇒_] (`suc V) M N) —→ N [ V ]

  ξ-·[] : {M M' : Term} →
          M —→ M' →
          M ·[] —→ M' ·[]

  β-Λ : {N : Term} {A : Ty} →
        (Λ N) ·[] —→ N

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term → Term → Set where
  _∎ : (M : Term) → M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} → L —→ M → M —↠ N → L —↠ N

multi-trans : {M N L : Term} → M —↠ N → N —↠ L → M —↠ L
multi-trans (_ ∎) ms2          = ms2
multi-trans (_ —→⟨ s ⟩ ms1') ms2    = _ —→⟨ s ⟩ (multi-trans ms1' ms2)

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N

------------------------------------------------------------------------
-- Multi-step congruence/helpers
------------------------------------------------------------------------

app-↠ : ∀ {L L' M M' : Term}
  → L —↠ L'
  → Value L'
  → M —↠ M'
  → (L · M) —↠ (L' · M')
app-↠ {L = L} {L' = L'} {M = M} {M' = M'} (L' ∎) vL' (M' ∎) =
  (L' · M') ∎
app-↠ {L = L} {L' = L'} {M = M} {M' = M'} (L' ∎) vL' (M —→⟨ s ⟩ M↠M') =
  (L' · M) —→⟨ ξ-·₂ vL' s ⟩ app-↠ (L' ∎) vL' M↠M'
app-↠ {L = L} {L' = L'} {M = M} {M' = M'} (L —→⟨ s ⟩ L↠L') vL' M↠M' =
  (L · M) —→⟨ ξ-·₁ s ⟩ app-↠ L↠L' vL' M↠M'

suc-↠ : ∀ {M N : Term}
  → M —↠ N
  → (`suc M) —↠ (`suc N)
suc-↠ (M ∎) = (`suc M) ∎
suc-↠ (M —→⟨ s ⟩ M↠N) = (`suc M) —→⟨ ξ-suc s ⟩ suc-↠ M↠N

case-↠ : ∀ {L L' M N : Term}
  → L —↠ L'
  → case_[zero⇒_|suc⇒_] L M N —↠ case_[zero⇒_|suc⇒_] L' M N
case-↠ {L = L} {L' = L'} {M = M} {N = N} (L' ∎) =
  (case_[zero⇒_|suc⇒_] L' M N) ∎
case-↠ {L = L} {L' = L'} {M = M} {N = N} (L —→⟨ s ⟩ L↠L') =
  (case_[zero⇒_|suc⇒_] L M N) —→⟨ ξ-case s ⟩ case-↠ L↠L'

if-true-↠ : ∀ {L M N : Term}
  → L —↠ `true
  → (`if_then_else L M N) —↠ M
if-true-↠ {M = M} {N = N} (L ∎) =
  (`if_then_else `true M N) —→⟨ β-true ⟩ (M ∎)
if-true-↠ {M = M} {N = N} (L —→⟨ s ⟩ L↠T) =
  (`if_then_else L M N) —→⟨ ξ-if s ⟩ if-true-↠ {M = M} {N = N} L↠T

if-false-↠ : ∀ {L M N : Term}
  → L —↠ `false
  → (`if_then_else L M N) —↠ N
if-false-↠ {M = M} {N = N} (L ∎) =
  (`if_then_else `false M N) —→⟨ β-false ⟩ (N ∎)
if-false-↠ {M = M} {N = N} (L —→⟨ s ⟩ L↠F) =
  (`if_then_else L M N) —→⟨ ξ-if s ⟩ if-false-↠ {M = M} {N = N} L↠F

·[]-↠ : ∀ {M M' : Term}
  → M —↠ M'
  → (M ·[]) —↠ (M' ·[])
·[]-↠ (M' ∎) = (M' ·[]) ∎
·[]-↠ (M —→⟨ s ⟩ M↠M') = (M ·[]) —→⟨ ξ-·[] s ⟩ ·[]-↠ M↠M'

β-ƛ-↠ : ∀ {N W : Term}
  → Value W
  → ((ƛ N) · W) —↠ N [ W ]
β-ƛ-↠ {N} {W} vW = ((ƛ N) · W) —→⟨ β-ƛ vW ⟩ ((N [ W ]) ∎)

case-zero-↠ : ∀ {M N : Term}
  → case_[zero⇒_|suc⇒_] `zero M N —↠ M
case-zero-↠ {M} {N} = (case_[zero⇒_|suc⇒_] `zero M N) —→⟨ β-zero ⟩ (M ∎)

β-Λ-↠ : ∀ {N : Term} {A : Ty}
  → (Λ N) ·[] —↠ N
β-Λ-↠ {N} {A} = ((Λ N) ·[]) —→⟨ β-Λ {A = A} ⟩ (N ∎)

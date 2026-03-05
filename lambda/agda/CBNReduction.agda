module CBNReduction where

open import Lambda

------------------------------------------------------------------------
-- Call-by-name one-step and multi-step reduction
------------------------------------------------------------------------

infix  2 _—→_
infix  2 _—↠_

data _—→_ : Term → Term → Set where
  cbn-xi-app1 : ∀ {L L' M} → L —→ L' → (L · M) —→ (L' · M)
  cbn-beta-lam : ∀ {N M} → ((ƛ N) · M) —→ (N [ M ])

data _—↠_ : Term → Term → Set where
  cbn-refl : ∀ (M : Term) → M —↠ M
  cbn-step : ∀ (L : Term) {M N : Term} → L —→ M → M —↠ N → L —↠ N

infix 3 _∎
pattern _∎ M = cbn-refl M

infixr 2 _—→⟨_⟩_
pattern _—→⟨_⟩_ L L—→M M—↠N = cbn-step L L—→M M—↠N

cbn-multi-trans : ∀ {M N L} → M —↠ N → N —↠ L → M —↠ L
cbn-multi-trans {L = L} (cbn-refl M) MS2 =
  let goal : M —↠ L
      goal = MS2
  in goal
cbn-multi-trans {L = L} (cbn-step M {M = M'} S MS1') MS2 =
  M —→⟨ S ⟩ cbn-multi-trans MS1' MS2

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = cbn-multi-trans L—↠M M—↠N

cbn-appL-cong : ∀ {L L' M}
  → L —↠ L'
  → (L · M) —↠ (L' · M)
cbn-appL-cong {M = M} (cbn-refl L) = (L · M) ∎
cbn-appL-cong {M = M} (cbn-step L {M = L1} {N = L2} R RS) =
  (L · M) —→⟨ cbn-xi-app1 R ⟩ cbn-appL-cong RS

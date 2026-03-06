module DynamicGradualGuarantee where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import GTLC using (_⊑_; _⇒_)
open import CastCalculus
open import Coercions using (_⊑ᶜ_; _↦_)

{-
Plan for the dynamic gradual guarantee in this development:
1. Prove one-step simulation both ways (`sim` and `sim-back`).
2. For `sim`, handle impossible and congruence (`ξ`) cases by recursion.
3. Use `catchup` for value-position congruence cases and beta helper lemmas.
4. Lift one-step simulation to multi-step simulation (`sim*` and `sim-back*`).
5. Use a catchup lemma for endpoints of precision when the more precise side is a value.
6. Combine (4) and (5) to prove `gg`.
7. Use `sim-back*` to transfer convergence from less precise to more precise,
   then prove the contrapositive `gg-diverge-cp` and `gg-diverge`.
-}

postulate
  catchup
    : ∀ {V N′}
    → Valueᶜ V
    → N′ ⊑ᶜᵀ V
    → ∃[ V′ ] ((Valueᶜ V′) × (N′ —↠ᶜ V′) × (V′ ⊑ᶜᵀ V))

  catchup-typed
    : ∀ {V N′ A}
    → Valueᶜ V
    → [] ⊢ᶜ V ⦂ A
    → N′ ⊑ᶜᵀ V
    → ∃[ V′ ] ((Valueᶜ V′) × ([] ⊢ᶜ V′ ⦂ A) × (N′ —↠ᶜ V′) × (V′ ⊑ᶜᵀ V))

  substᶜ-⊑
    : ∀ {N N′ V V′}
    → N′ ⊑ᶜᵀ N
    → V′ ⊑ᶜᵀ V
    → substᶜ N′ V′ ⊑ᶜᵀ substᶜ N V

  app-fun-⊑blame
    : ∀ {L′ M′}
    → L′ ⊑ᶜᵀ blame
    → (L′ · M′) —↠ᶜ blame

  app-arg-⊑blame
    : ∀ {V M′}
    → Valueᶜ V
    → M′ ⊑ᶜᵀ blame
    → (V · M′) —↠ᶜ blame

  sim-cast-head
    : ∀ {M M′ c c′ N}
    → M′ ⊑ᶜᵀ M
    → c′ ⊑ᶜ c
    → cast M [ c ] —→ᶜ N
    → ∃[ N′ ] ((cast M′ [ c′ ] —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))

  sim-castL-step
    : ∀ {M M′ c N}
    → M′ ⊑ᶜᵀ M
    → M —→ᶜ N
    → ∃[ N′ ] ((cast M′ [ c ] —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))

  sim-castR-step
    : ∀ {M M′ c N}
    → M′ ⊑ᶜᵀ M
    → cast M [ c ] —→ᶜ N
    → ∃[ N′ ] ((M′ —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))

  sim-cast*-step
    : ∀ {M M′ c c′ N}
    → M′ ⊑ᶜᵀ M
    → cast M [ c ] —→ᶜ N
    → ∃[ N′ ] ((cast M′ [ c′ ] —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))

postulate
  var-irreducible : ∀ {x N} → ` x —→ᶜ N → ⊥
  blame-irreducible : ∀ {N} → blame —→ᶜ N → ⊥

simβ
  : ∀ {F W N V′ W′ A B}
  → Valueᶜ F
  → Valueᶜ W
  → Valueᶜ V′
  → Valueᶜ W′
  → [] ⊢ᶜ F ⦂ (A ⇒ B)
  → [] ⊢ᶜ W ⦂ A
  → [] ⊢ᶜ V′ ⦂ (A ⇒ B)
  → [] ⊢ᶜ W′ ⦂ A
  → V′ ⊑ᶜᵀ F
  → W′ ⊑ᶜᵀ W
  → F · W —→ᶜ N
  → ∃[ N′ ] (((V′ · W′) —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))
simβ {F = F} {W = W} {V′ = ƛ A′ ⇒ N′} {W′ = W′} vF vW vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W (β-ƛ {A = A} {N = N} {V = V} vW0)
  with V′⊑F
... | ⊑ƛ A′⊑A N′⊑N =
  substᶜ N′ W′
  , (((ƛ _ ⇒ N′) · W′) —→ᶜ⟨ β-ƛ vW′ ⟩ substᶜ N′ W′ ∎ᶜ)
  , substᶜ-⊑ N′⊑N W′⊑W
simβ {F = F} {W = W} {V′ = cast V′ [ c ]} {W′ = W′}
     vF vW vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W
     (β-ƛ {A = A} {N = N} {V = V} vW0)
  with V′⊑F
... | ⊑castL V″⊑ƛ
  with canonical-⇒ vV′ V′⦂A⇒B
... | inj₂ (U , c₁ , d₁ , (vU , refl)) =
  {!!}
simβ {F = F} {W = W} vF vW vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W (β-↦ {V = V} {W = W₀} {c = c} {d = d} vV0 vW0)
  with V′⊑F
... | ⊑cast V″⊑cast↦ c′⊑c = {!   !}
... | ⊑castL V″⊑cast↦ = {!   !}
... | ⊑castR V″⊑cast↦ = {!   !}
... | ⊑cast* V″⊑cast↦ = {!   !}
simβ vF vW vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W (ξ {F = □· W} F—→N) =
  ⊥-elim (value-irreducible vF F—→N)
simβ vF vW vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W (ξ {F = (_ ·□ vF′)} W—→N) =
  ⊥-elim (value-irreducible vW W—→N)
simβ () vW vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W (ξ-blame {F = □· W})
simβ vF () vV′ vW′ F⦂A⇒B W⦂A V′⦂A⇒B W′⦂A V′⊑F W′⊑W (ξ-blame {F = (_ ·□ vF′)})

mutual
  sim-app
    : ∀ {L L′ M M′ N A}
    → L′ ⊑ᶜᵀ L
    → M′ ⊑ᶜᵀ M
    → [] ⊢ᶜ (L · M) ⦂ A
    → L · M —→ᶜ N
    → ∃[ N′ ] ((L′ · M′ —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))
  sim-app {M = M} {M′ = M′} L′⊑L M′⊑M (⊢· L⦂A⇒B M⦂A) (ξ {F = □· .M} L—→N)
    with sim L′⊑L L⦂A⇒B {!!} L—→N
  ... | N′ , L′—↠N′ , N′⊑N =
    (N′ · M′) , ξ* {F = □· M′} L′—↠N′ , ⊑· N′⊑N M′⊑M
  sim-app {L = L} {L′ = L′} {M′ = M′} L′⊑L M′⊑M (⊢· L⦂A⇒B M⦂A) (ξ {F = (.L ·□ vL)} M—→N)
    with catchup vL L′⊑L
  ... | V′ , vV′ , L′—↠V′ , V′⊑L
    with sim M′⊑M M⦂A {!!} M—→N
  ... | N′ , M′—↠N′ , N′⊑N =
    (V′ · N′)
    , ((ξ* {F = □· M′} L′—↠V′) ++ᶜ (ξ* {F = V′ ·□ vV′} M′—↠N′))
    , (⊑· V′⊑L N′⊑N)
  sim-app {M′ = M′} L′⊑L M′⊑M LM⦂A (ξ-blame {F = □· M}) =
    blame , app-fun-⊑blame L′⊑L , ⊑blame
  sim-app {L = L} {L′ = L′} {M′ = M′} L′⊑L M′⊑M LM⦂A (ξ-blame {F = (.L ·□ vL)})
    with catchup vL L′⊑L
  ... | V′ , vV′ , L′—↠V′ , V′⊑L
    with app-arg-⊑blame vV′ M′⊑M
  ... | V′·M′—↠blame =
    blame
    , ((ξ* {F = □· M′} L′—↠V′) ++ᶜ V′·M′—↠blame)
    , ⊑blame
  sim-app {L′ = L′} {M′ = M′} L′⊑L M′⊑M (⊢· L⦂A⇒B M⦂A) (β-ƛ {A = A} {N = N} {V = V} vV)
    with catchup-typed V-ƛ L⦂A⇒B L′⊑L
  ... | Vfun′ , vVfun′ , Vfun′⦂A⇒B , L′—↠Vfun′ , Vfun′⊑ƛN
    with catchup-typed vV M⦂A M′⊑M
  ... | W′ , vW′ , W′⦂A , M′—↠W′ , W′⊑V
    with simβ V-ƛ vV vVfun′ vW′ L⦂A⇒B M⦂A Vfun′⦂A⇒B W′⦂A Vfun′⊑ƛN W′⊑V (β-ƛ vV)
  ... | N′ , Vfun′·W′—↠N′ , N′⊑NV =
    N′
    , (((ξ* {F = □· M′} L′—↠Vfun′)
        ++ᶜ (ξ* {F = Vfun′ ·□ vVfun′} M′—↠W′))
        ++ᶜ Vfun′·W′—↠N′)
    , N′⊑NV
  sim-app {L′ = L′} {M′ = M′} L′⊑L M′⊑M (⊢· L⦂A⇒B M⦂A) (β-↦ {V = V} {W = W} {c = c} {d = d} vV vW)
    with catchup-typed (V-cast↦ vV) L⦂A⇒B L′⊑L
  ... | Vfun′ , vVfun′ , Vfun′⦂A⇒B , L′—↠Vfun′ , Vfun′⊑cast↦
    with catchup-typed vW M⦂A M′⊑M
  ... | W′ , vW′ , W′⦂A , M′—↠W′ , W′⊑W
    with simβ (V-cast↦ vV) vW vVfun′ vW′ L⦂A⇒B M⦂A Vfun′⦂A⇒B W′⦂A Vfun′⊑cast↦ W′⊑W (β-↦ vV vW)
  ... | N′ , Vfun′·W′—↠N′ , N′⊑N =
    N′
    , (((ξ* {F = □· M′} L′—↠Vfun′)
        ++ᶜ (ξ* {F = Vfun′ ·□ vVfun′} M′—↠W′))
        ++ᶜ Vfun′·W′—↠N′)
    , N′⊑N

  sim
    : ∀ {M M′ N A A′}
    → M′ ⊑ᶜᵀ M
    → [] ⊢ᶜ M ⦂ A
    → [] ⊢ᶜ M′ ⦂ A′
    → M —→ᶜ N
    → ∃[ N′ ] ((M′ —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))
  sim ⊑` M⦂A M′⦂A′ M—→N = ⊥-elim (var-irreducible M—→N)
  sim ⊑$ M⦂A M′⦂A′ M—→N = ⊥-elim (value-irreducible V-$ M—→N)
  sim (⊑ƛ A′⊑A M′⊑M) M⦂A M′⦂A′ M—→N = ⊥-elim (value-irreducible V-ƛ M—→N)
  sim (⊑· L′⊑L M′⊑M) M⦂A M′⦂A′ red = sim-app L′⊑L M′⊑M M⦂A red
  sim (⊑cast M′⊑M c′⊑c) (⊢cast M⦂A c⦂A⇨B) M′⦂A′ red = sim-cast-head M′⊑M c′⊑c red
  sim (⊑castL M′⊑M) M⦂A M′⦂A′ M—→N = sim-castL-step M′⊑M M—→N
  sim (⊑castR M′⊑M) M⦂A M′⦂A′ M—→N = sim-castR-step M′⊑M M—→N
  sim (⊑cast* M′⊑M) M⦂A M′⦂A′ M—→N = sim-cast*-step M′⊑M M—→N
  sim ⊑blame M⦂A M′⦂A′ M—→N = ⊥-elim (blame-irreducible M—→N)

postulate

  sim-back
    : ∀ {M M′ N′}
    → M′ ⊑ᶜᵀ M
    → M′ —→ᶜ N′
    → ∃[ N ] ((M —↠ᶜ N) × (N′ ⊑ᶜᵀ N))

  sim*
    : ∀ {M M′ N A}
    → M′ ⊑ᶜᵀ M
    → [] ⊢ᶜ M ⦂ A
    → M —↠ᶜ N
    → ∃[ N′ ] ((M′ —↠ᶜ N′) × (N′ ⊑ᶜᵀ N))

  sim-back*
    : ∀ {M M′ N′}
    → M′ ⊑ᶜᵀ M
    → M′ —↠ᶜ N′
    → ∃[ N ] ∃[ N″ ] ((M —↠ᶜ N) × (N′ —↠ᶜ N″) × (N ⊑ᶜᵀ N″))

  sim-back-converges
    : ∀ {M M′}
    → M′ ⊑ᶜᵀ M
    → Convergesᶜ M′
    → Convergesᶜ M

gg
  : ∀ {M M′ V A}
  → M′ ⊑ᶜᵀ M
  → [] ⊢ᶜ M ⦂ A
  → M —↠ᶜ V
  → Valueᶜ V
  → ∃[ V′ ] ((Valueᶜ V′) × (M′ —↠ᶜ V′) × (V′ ⊑ᶜᵀ V))
gg M′⊑M M⦂A M—↠V vV
  with sim* M′⊑M M⦂A M—↠V
... | N′ , M′—↠N′ , N′⊑V
  with catchup vV N′⊑V
... | V′ , vV′ , N′—↠V′ , V′⊑V =
  V′ , vV′ , (M′—↠N′ ++ᶜ N′—↠V′) , V′⊑V

gg-diverge-cp
  : ∀ {M M′}
  → M′ ⊑ᶜᵀ M
  → ¬ Convergesᶜ M
  → ¬ Convergesᶜ M′
gg-diverge-cp M′⊑M ¬M⇓ M′⇓ = ¬M⇓ (sim-back-converges M′⊑M M′⇓)

gg-diverge
  : ∀ {M M′}
  → M′ ⊑ᶜᵀ M
  → Divergesᶜ M
  → Divergesᶜ M′
gg-diverge M′⊑M M⇑ = gg-diverge-cp M′⊑M M⇑

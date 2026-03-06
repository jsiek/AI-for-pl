module CastCalculus where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Types
open import Contexts
open import GTLC
open import Coercions

data Termᶜ : Set where
  `_      : Var → Termᶜ
  $_      : Nat → Termᶜ
  ƛ_⇒_    : Ty → Termᶜ → Termᶜ
  _·_     : Termᶜ → Termᶜ → Termᶜ
  cast_[_] : Termᶜ → Coercion → Termᶜ
  blame   : Termᶜ

infix 4 _⊢ᶜ_⦂_

data _⊢ᶜ_⦂_ : Ctx → Termᶜ → Ty → Set where
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ᶜ ` x ⦂ A

  ⊢$ : ∀ {Γ n}
    → Γ ⊢ᶜ $ n ⦂ ℕ

  ⊢ƛ : ∀ {Γ A N B}
    → (A ∷ Γ) ⊢ᶜ N ⦂ B
    → Γ ⊢ᶜ ƛ A ⇒ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ᶜ L ⦂ (A ⇒ B)
    → Γ ⊢ᶜ M ⦂ A
    → Γ ⊢ᶜ L · M ⦂ B

  ⊢cast : ∀ {Γ M c A B}
    → Γ ⊢ᶜ M ⦂ A
    → ⊢ c ⦂ A ⇨ B
    → Γ ⊢ᶜ cast M [ c ] ⦂ B

  ⊢blame : ∀ {Γ A}
    → Γ ⊢ᶜ blame ⦂ A

infix 4 _⊢_⦂_⊑ᶜᵀ_⦂_

data _⊢_⦂_⊑ᶜᵀ_⦂_ {Γ₁ Γ₂ : Ctx} (ρ : Γ₁ ⊑ᵉ Γ₂) : Termᶜ → Ty → Termᶜ → Ty → Set where
  ⊑` : ∀ {A₁ A₂ x}
    → Γ₁ ∋ x ⦂ A₁
    → Γ₂ ∋ x ⦂ A₂
    → ρ ⊢ ` x ⦂ A₁ ⊑ᶜᵀ ` x ⦂ A₂

  ⊑$ : ∀ {n}
    → ρ ⊢ $ n ⦂ ℕ ⊑ᶜᵀ $ n ⦂ ℕ

  ⊑ƛ : ∀ {A A′ B B′ N M}
    → (A⊑A′ : A ⊑ A′)
    → (extend-⊑ᵉ A⊑A′ ρ) ⊢ N ⦂ B ⊑ᶜᵀ M ⦂ B′
    → ρ ⊢ ƛ A ⇒ N ⦂ (A ⇒ B) ⊑ᶜᵀ ƛ A′ ⇒ M ⦂ (A′ ⇒ B′)

  ⊑· : ∀ {A A′ B B′ L L′ M M′}
    → ρ ⊢ L ⦂ (A ⇒ B) ⊑ᶜᵀ L′ ⦂ (A′ ⇒ B′)
    → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → ρ ⊢ L · M ⦂ B ⊑ᶜᵀ L′ · M′ ⦂ B′

  ⊑cast : ∀ {A A′ B B′ M M′ c c′}
    → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → c ⊑ᶜ c′
    → ⊢ c ⦂ A ⇨ B
    → ⊢ c′ ⦂ A′ ⇨ B′
    → ρ ⊢ cast M [ c ] ⦂ B ⊑ᶜᵀ cast M′ [ c′ ] ⦂ B′

  ⊑castL : ∀ {A A′ B M M′ c}
    → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → ⊢ c ⦂ A ⇨ B
    → c ⊑ᶜ idᶜ A′
    → ρ ⊢ cast M [ c ] ⦂ B ⊑ᶜᵀ M′ ⦂ A′

  ⊑castR : ∀ {A A′ B′ M M′ c′}
    → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → ⊢ c′ ⦂ A′ ⇨ B′
    → idᶜ A ⊑ᶜ c′
    → ρ ⊢ M ⦂ A ⊑ᶜᵀ cast M′ [ c′ ] ⦂ B′

  ⊑blameR : ∀ {A₁ A₂ M}
    → Γ₁ ⊢ᶜ M ⦂ A₁
    → A₁ ⊑ A₂
    → ρ ⊢ M ⦂ A₁ ⊑ᶜᵀ blame ⦂ A₂

∋-unique : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-unique Z Z = refl
∋-unique (S ∋x) (S ∋x′) = ∋-unique ∋x ∋x′

⊑ᶜᵀ-left-typed
  : ∀ {Γ₁ Γ₂} {ρ : Γ₁ ⊑ᵉ Γ₂} {A₁ A₂ M M′}
  → ρ ⊢ M ⦂ A₁ ⊑ᶜᵀ M′ ⦂ A₂
  → Γ₁ ⊢ᶜ M ⦂ A₁
⊑ᶜᵀ-left-typed (⊑` ∋x _) = ⊢` ∋x
⊑ᶜᵀ-left-typed ⊑$ = ⊢$
⊑ᶜᵀ-left-typed {ρ = ρ} {A₁ = A ⇒ B} {A₂ = A′ ⇒ B′} (⊑ƛ A⊑A′ N⊑M) =
  ⊢ƛ (⊑ᶜᵀ-left-typed {ρ = extend-⊑ᵉ A⊑A′ ρ} N⊑M)
⊑ᶜᵀ-left-typed (⊑· L⊑L′ M⊑M′) = ⊢· (⊑ᶜᵀ-left-typed L⊑L′) (⊑ᶜᵀ-left-typed M⊑M′)
⊑ᶜᵀ-left-typed (⊑cast M⊑M′ _ cwt _) = ⊢cast (⊑ᶜᵀ-left-typed M⊑M′) cwt
⊑ᶜᵀ-left-typed (⊑castL M⊑M′ cwt _) = ⊢cast (⊑ᶜᵀ-left-typed M⊑M′) cwt
⊑ᶜᵀ-left-typed (⊑castR M⊑M′ _ _) = ⊑ᶜᵀ-left-typed M⊑M′
⊑ᶜᵀ-left-typed (⊑blameR M⦂A₁ _) = M⦂A₁

⊑ᶜᵀ-right-typed
  : ∀ {Γ₁ Γ₂} {ρ : Γ₁ ⊑ᵉ Γ₂} {A₁ A₂ M M′}
  → ρ ⊢ M ⦂ A₁ ⊑ᶜᵀ M′ ⦂ A₂
  → Γ₂ ⊢ᶜ M′ ⦂ A₂
⊑ᶜᵀ-right-typed (⊑` _ ∋x) = ⊢` ∋x
⊑ᶜᵀ-right-typed ⊑$ = ⊢$
⊑ᶜᵀ-right-typed {ρ = ρ} {A₁ = A ⇒ B} {A₂ = A′ ⇒ B′} (⊑ƛ A⊑A′ N⊑M) =
  ⊢ƛ (⊑ᶜᵀ-right-typed {ρ = extend-⊑ᵉ A⊑A′ ρ} N⊑M)
⊑ᶜᵀ-right-typed (⊑· L⊑L′ M⊑M′) = ⊢· (⊑ᶜᵀ-right-typed L⊑L′) (⊑ᶜᵀ-right-typed M⊑M′)
⊑ᶜᵀ-right-typed (⊑cast M⊑M′ _ _ c′wt) = ⊢cast (⊑ᶜᵀ-right-typed M⊑M′) c′wt
⊑ᶜᵀ-right-typed (⊑castL M⊑M′ _ _) = ⊑ᶜᵀ-right-typed M⊑M′
⊑ᶜᵀ-right-typed (⊑castR M⊑M′ c′wt _) = ⊢cast (⊑ᶜᵀ-right-typed M⊑M′) c′wt
⊑ᶜᵀ-right-typed (⊑blameR M⦂A₁ A₁⊑A₂) = ⊢blame

⊑ᶜᵀ-type-precision
  : ∀ {Γ₁ Γ₂} {ρ : Γ₁ ⊑ᵉ Γ₂} {A₁ A₂ M M′}
  → ρ ⊢ M ⦂ A₁ ⊑ᶜᵀ M′ ⦂ A₂
  → A₁ ⊑ A₂
⊑ᶜᵀ-type-precision {ρ = ρ} (⊑` {x = x} ∋x ∋x′) = ρ x _ _ ∋x ∋x′
⊑ᶜᵀ-type-precision ⊑$ = ⊑-ℕ
⊑ᶜᵀ-type-precision {ρ = ρ} {A₁ = A ⇒ B} {A₂ = A′ ⇒ B′} (⊑ƛ A⊑A′ N⊑M) =
  ⊑-⇒ A⊑A′ (⊑ᶜᵀ-type-precision {ρ = extend-⊑ᵉ A⊑A′ ρ} N⊑M)
⊑ᶜᵀ-type-precision (⊑· L⊑L′ M⊑M′) with ⊑ᶜᵀ-type-precision L⊑L′
... | ⊑-⇒ _ B⊑B′ = B⊑B′
⊑ᶜᵀ-type-precision (⊑cast M⊑M′ c⊑c′ cwt c′wt) with ⊑ᶜ→⊑ c′wt cwt c⊑c′
... | _ , B⊑B′ = B⊑B′
⊑ᶜᵀ-type-precision (⊑castL _ cwt c⊑id) with ⊑ᶜ→⊑ ⊢idᶜ cwt c⊑id
... | _ , B⊑A′ = B⊑A′
⊑ᶜᵀ-type-precision (⊑castR _ c′wt id⊑c′) with ⊑ᶜ→⊑ c′wt ⊢idᶜ id⊑c′
... | _ , A⊑B′ = A⊑B′
⊑ᶜᵀ-type-precision (⊑blameR _ A₁⊑A₂) = A₁⊑A₂

data Valueᶜ : Termᶜ → Set where
  V-$ : ∀ {n} → Valueᶜ ($ n)
  V-ƛ : ∀ {A N} → Valueᶜ (ƛ A ⇒ N)
  V-cast! : ∀ {V G} → Valueᶜ V → Valueᶜ (cast V [ G ! ])
  V-cast↦ : ∀ {V c d} → Valueᶜ V → Valueᶜ (cast V [ c ↦ d ])

data Frameᶜ : Set where
  □·_     : Termᶜ → Frameᶜ
  _·□_    : (V : Termᶜ) → Valueᶜ V → Frameᶜ
  cast□[_] : Coercion → Frameᶜ

plug : Frameᶜ → Termᶜ → Termᶜ
plug (□· M) L = L · M
plug (V ·□ vV) M = V · M
plug (cast□[ c ]) M = cast M [ c ]

Renameᶜ : Set
Renameᶜ = Var → Var

Substᶜ : Set
Substᶜ = Var → Termᶜ

extᶜ : Renameᶜ → Renameᶜ
extᶜ ρ zero = zero
extᶜ ρ (suc x) = suc (ρ x)

renameᶜ : Renameᶜ → Termᶜ → Termᶜ
renameᶜ ρ (` x) = ` (ρ x)
renameᶜ ρ ($ n) = $ n
renameᶜ ρ (ƛ A ⇒ N) = ƛ A ⇒ renameᶜ (extᶜ ρ) N
renameᶜ ρ (L · M) = renameᶜ ρ L · renameᶜ ρ M
renameᶜ ρ (cast M [ c ]) = cast (renameᶜ ρ M) [ c ]
renameᶜ ρ blame = blame

extsᶜ : Substᶜ → Substᶜ
extsᶜ σ zero = ` zero
extsᶜ σ (suc x) = renameᶜ suc (σ x)

subst-allᶜ : Substᶜ → Termᶜ → Termᶜ
subst-allᶜ σ (` x) = σ x
subst-allᶜ σ ($ n) = $ n
subst-allᶜ σ (ƛ A ⇒ N) = ƛ A ⇒ subst-allᶜ (extsᶜ σ) N
subst-allᶜ σ (L · M) = subst-allᶜ σ L · subst-allᶜ σ M
subst-allᶜ σ (cast M [ c ]) = cast (subst-allᶜ σ M) [ c ]
subst-allᶜ σ blame = blame

singleEnvᶜ : Termᶜ → Substᶜ
singleEnvᶜ M zero = M
singleEnvᶜ M (suc x) = ` x

substᶜ : Termᶜ → Termᶜ → Termᶜ
substᶜ N M = subst-allᶜ (singleEnvᶜ M) N

infix 4 _—→ᶜ_
infix 4 _—↠ᶜ_

data _—→ᶜ_ : Termᶜ → Termᶜ → Set where
  ξξ : ∀ {F M N M′ N′}
    → M′ ≡ plug F M
    → N′ ≡ plug F N
    → M —→ᶜ N
    → M′ —→ᶜ N′

  β-ƛ : ∀ {A N V}
    → Valueᶜ V
    → (ƛ A ⇒ N) · V —→ᶜ substᶜ N V

  β-id : ∀ {A V}
    → Valueᶜ V
    → cast V [ idᶜ A ] —→ᶜ V

  β-seq : ∀ {V c d}
    → Valueᶜ V
    → cast V [ c ⨟ d ] —→ᶜ cast (cast V [ c ]) [ d ]

  β-↦ : ∀ {V W c d}
    → Valueᶜ V
    → Valueᶜ W
    → cast V [ c ↦ d ] · W —→ᶜ cast (V · cast W [ c ]) [ d ]

  β-proj-inj-ok : ∀ {V G}
    → Valueᶜ V
    → cast (cast V [ G ! ]) [ G `? ] —→ᶜ V

  β-proj-inj-bad : ∀ {V G H}
    → Valueᶜ V
    → G ≢ H
    → cast (cast V [ G ! ]) [ H `? ] —→ᶜ blame

  ξξ-blame : ∀ {F M′}
    → M′ ≡ plug F blame
    → M′ —→ᶜ blame

pattern ξ {F} M—→N = ξξ {F = F} refl refl M—→N
pattern ξ-blame {F} = ξξ-blame {F = F} refl

postulate
  value-irreducible : ∀ {V N} → Valueᶜ V → V —→ᶜ N → ⊥

data _—↠ᶜ_ : Termᶜ → Termᶜ → Set where
  ms-refl : ∀ (M : Termᶜ)
    → M —↠ᶜ M

  ms-step : ∀ (L : Termᶜ) {M N : Termᶜ}
    → L —→ᶜ M
    → M —↠ᶜ N
    → L —↠ᶜ N

infix 3 _∎ᶜ
pattern _∎ᶜ M = ms-refl M

infixr 2 _—→ᶜ⟨_⟩_
pattern _—→ᶜ⟨_⟩_ L L—→M M—↠N = ms-step L L—→M M—↠N

_++ᶜ_ : ∀ {L M N} → L —↠ᶜ M → M —↠ᶜ N → L —↠ᶜ N
_++ᶜ_ {L = L} (L ∎ᶜ) M—↠N = M—↠N
_++ᶜ_ {L = L} (L —→ᶜ⟨ L—→M ⟩ M—↠N) N—↠P =
  L —→ᶜ⟨ L—→M ⟩ (M—↠N ++ᶜ N—↠P)

ξ* : ∀ {F M N}
  → M —↠ᶜ N
  → plug F M —↠ᶜ plug F N
ξ* {F = F} (M ∎ᶜ) = plug F M ∎ᶜ
ξ* {F = F} (M —→ᶜ⟨ M—→N ⟩ N—↠P) =
  plug F M —→ᶜ⟨ ξ M—→N ⟩ ξ* N—↠P

Convergesᶜ : Termᶜ → Set
Convergesᶜ M = ∃[ W ] ((M —↠ᶜ W) × (Valueᶜ W ⊎ (W ≡ blame)))

Divergesᶜ : Termᶜ → Set
Divergesᶜ M = ¬ Convergesᶜ M

data Progressᶜ (M : Termᶜ) : Set where
  done  : Valueᶜ M → Progressᶜ M
  step  : ∀ {N} → M —→ᶜ N → Progressᶜ M
  crash : M ≡ blame → Progressᶜ M

_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
ℕ ≟Ty ℕ = yes refl
ℕ ≟Ty ★ = no (λ ())
ℕ ≟Ty (B ⇒ C) = no (λ ())
★ ≟Ty ℕ = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (B ⇒ C) = no (λ ())
(A ⇒ B) ≟Ty ℕ = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no (λ { refl → A≢C refl })
... | _ | no B≢D = no (λ { refl → B≢D refl })

canonical-★-inj : ∀ {V} → Valueᶜ V → [] ⊢ᶜ V ⦂ ★ → ∃[ G ] ∃[ W ] (Valueᶜ W × (V ≡ cast W [ G ! ]))
canonical-★-inj V-$ ()
canonical-★-inj V-ƛ ()
canonical-★-inj (V-cast! {V = W} {G = G} vW) pf with pf
... | ⊢cast _ cwt with cwt
... | ⊢! _ = G , W , (vW , refl)
canonical-★-inj (V-cast↦ vV) (⊢cast _ ())

canonical-⇒
  : ∀ {V A B}
  → Valueᶜ V
  → [] ⊢ᶜ V ⦂ (A ⇒ B)
  → (∃[ N ] V ≡ (ƛ A ⇒ N))
    ⊎ (∃[ W ] ∃[ c ] ∃[ d ] (Valueᶜ W × (V ≡ cast W [ c ↦ d ])))
canonical-⇒ V-$ ()
canonical-⇒ (V-ƛ {N = N}) (⊢ƛ {A = A} N⦂B) = inj₁ (N , refl)
canonical-⇒ (V-cast! vW) (⊢cast _ ())
canonical-⇒ (V-cast↦ {V = W} {c = c} {d = d} vW) pf with pf
... | ⊢cast _ cwt with cwt
... | ⊢↦ _ _ = inj₂ (W , c , d , (vW , refl))

progressᶜ : ∀ {M A} → [] ⊢ᶜ M ⦂ A → Progressᶜ M
progressᶜ (⊢` ())
progressᶜ ⊢$ = done V-$
progressᶜ (⊢ƛ M⦂A) = done V-ƛ
progressᶜ (⊢· {L = L} {M = M} L⦂A⇒B M⦂A) with progressᶜ L⦂A⇒B
... | step L→L′ = step (ξ {F = □· M} L→L′)
... | crash refl = step (ξ-blame {F = □· M})
... | done vL with progressᶜ M⦂A
... | step M→M′ = step (ξ {F = (L ·□ vL)} M→M′)
... | crash refl = step (ξ-blame {F = (L ·□ vL)})
... | done vM with canonical-⇒ vL L⦂A⇒B
... | inj₁ (N , refl) = step (β-ƛ vM)
... | inj₂ (W , c , d , (vW , refl)) = step (β-↦ vW vM)
progressᶜ (⊢cast {c = c} M⦂A c⦂A⇨B) with progressᶜ M⦂A
... | step M→M′ = step (ξ {F = cast□[ c ]} M→M′)
... | crash refl = step ξ-blame
... | done vM with c⦂A⇨B
... | ⊢idᶜ = step (β-id vM)
... | ⊢! g = done (V-cast! vM)
... | ⊢↦ cwt dwt = done (V-cast↦ vM)
... | ⊢⨟ cwt dwt = step (β-seq vM)
... | ⊢? {G = G} g with canonical-★-inj vM M⦂A
... | H , W , (vW , refl) with H ≟Ty G
... | yes refl = step (β-proj-inj-ok vW)
... | no H≢G = step (β-proj-inj-bad vW H≢G)
progressᶜ ⊢blame = crash refl

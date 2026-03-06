module CastCalculus where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (Dec; yes; no)
open import GTLC using (Ty; ℕ; ★; _⇒_; _⊑_; Var)
open import Coercions using
  ( Coercion
  ; idᶜ
  ; _!
  ; _`?
  ; _↦_
  ; _⨟_
  ; _⊑ᶜ_
  ; ⊢_⦂_⇨_
  ; ⊢idᶜ
  ; ⊢!
  ; ⊢?
  ; ⊢↦
  ; ⊢⨟
  )

data Termᶜ : Set where
  `_      : Var → Termᶜ
  $_      : Nat → Termᶜ
  ƛ_⇒_    : Ty → Termᶜ → Termᶜ
  _·_     : Termᶜ → Termᶜ → Termᶜ
  cast_[_] : Termᶜ → Coercion → Termᶜ
  blame   : Termᶜ

Ctxᶜ : Set
Ctxᶜ = List Ty

infix 4 _∋ᶜ_⦂_

data _∋ᶜ_⦂_ : Ctxᶜ → Var → Ty → Set where
  Z : ∀ {Γ A} → (A ∷ Γ) ∋ᶜ zero ⦂ A
  S : ∀ {Γ A B x} → Γ ∋ᶜ x ⦂ A → (B ∷ Γ) ∋ᶜ suc x ⦂ A

infix 4 _⊢ᶜ_⦂_

data _⊢ᶜ_⦂_ : Ctxᶜ → Termᶜ → Ty → Set where
  ⊢` : ∀ {Γ x A}
    → Γ ∋ᶜ x ⦂ A
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

infix 4 _⊑ᶜᵀ_

data _⊑ᶜᵀ_ : Termᶜ → Termᶜ → Set where
  ⊑` : ∀ {x}
    → ` x ⊑ᶜᵀ ` x

  ⊑$ : ∀ {n}
    → $ n ⊑ᶜᵀ $ n

  ⊑ƛ : ∀ {A B N M}
    → A ⊑ B
    → N ⊑ᶜᵀ M
    → ƛ A ⇒ N ⊑ᶜᵀ ƛ B ⇒ M

  ⊑· : ∀ {L L′ M M′}
    → L ⊑ᶜᵀ L′
    → M ⊑ᶜᵀ M′
    → L · M ⊑ᶜᵀ L′ · M′

  ⊑cast : ∀ {M M′ c c′}
    → M ⊑ᶜᵀ M′
    → c ⊑ᶜ c′
    → cast M [ c ] ⊑ᶜᵀ cast M′ [ c′ ]

  ⊑castL : ∀ {M M′ c}
    → M ⊑ᶜᵀ M′
    → cast M [ c ] ⊑ᶜᵀ M′

  ⊑castR : ∀ {M M′ c}
    → M ⊑ᶜᵀ M′
    → M ⊑ᶜᵀ cast M′ [ c ]

  ⊑cast* : ∀ {M M′ c c′}
    → M ⊑ᶜᵀ M′
    → cast M [ c ] ⊑ᶜᵀ cast M′ [ c′ ]

  ⊑blame : blame ⊑ᶜᵀ blame

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

postulate
  substᶜ : Termᶜ → Termᶜ → Termᶜ

infix 4 _—→ᶜ_

data _—→ᶜ_ : Termᶜ → Termᶜ → Set where
  ξ : ∀ {F M M′}
    → M —→ᶜ M′
    → plug F M —→ᶜ plug F M′

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

  ξ-blame : ∀ {F}
    → plug F blame —→ᶜ blame

data Progressᶜ (M : Termᶜ) : Set where
  done  : Valueᶜ M → Progressᶜ M
  step  : ∀ {N} → M —→ᶜ N → Progressᶜ M
  crash : M ≡ blame → Progressᶜ M

¬-∋ᶜ[] : ∀ {x A} → [] ∋ᶜ x ⦂ A → ⊥
¬-∋ᶜ[] ()

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
progressᶜ (⊢` ∋x) = ⊥-elim (¬-∋ᶜ[] ∋x)
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

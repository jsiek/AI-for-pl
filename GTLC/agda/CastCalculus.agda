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
  inj_[_]! : Termᶜ → Ty → Termᶜ
  blame   : Termᶜ

data Valueᶜ : Termᶜ → Set where
  V-$ : ∀ {n} → Valueᶜ ($ n)
  V-ƛ : ∀ {A N} → Valueᶜ (ƛ A ⇒ N)
  V-! : ∀ {V G} → Valueᶜ V → Valueᶜ (inj V [ G ]!)
  V-cast↦ : ∀ {V c d} → Valueᶜ V → Valueᶜ (cast V [ c ↦ d ])

data Frameᶜ : Set where
  □·_     : Termᶜ → Frameᶜ
  _·□_    : (V : Termᶜ) → Valueᶜ V → Frameᶜ
  cast□[_] : Coercion → Frameᶜ

plug : Frameᶜ → Termᶜ → Termᶜ
plug (□· M) L = L · M
plug (V ·□ vV) M = V · M
plug (cast□[ c ]) M = cast M [ c ]


--------------------------------------------------------------------------------
-- Type System
--------------------------------------------------------------------------------

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

  ⊢! : ∀ {Γ M G}
    → Γ ⊢ᶜ M ⦂ G
    → Ground G
    → Valueᶜ M
    → Γ ⊢ᶜ inj M [ G ]! ⦂ ★

  ⊢blame : ∀ {Γ A}
    → Γ ⊢ᶜ blame ⦂ A

---------------------------------------------------------------
-- Term Precision 
---------------------------------------------------------------
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

  ⊑inj : ∀ {G M M′}
    → ρ ⊢ M ⦂ G ⊑ᶜᵀ M′ ⦂ G
    → Valueᶜ M
    → Valueᶜ M′
    → Ground G
    → ρ ⊢ inj M [ G ]! ⦂ ★ ⊑ᶜᵀ inj M′ [ G ]! ⦂ ★

  ⊑injL : ∀ {G A′ M M′}
    → ρ ⊢ M ⦂ G ⊑ᶜᵀ M′ ⦂ A′
    → Valueᶜ M
    → Ground G
    → Valueᶜ M′
    → ρ ⊢ inj M [ G ]! ⦂ ★ ⊑ᶜᵀ M′ ⦂ A′

  ⊑blameR : ∀ {A₁ A₂ M}
    → Γ₁ ⊢ᶜ M ⦂ A₁
    → A₁ ⊑ A₂
    → ρ ⊢ M ⦂ A₁ ⊑ᶜᵀ blame ⦂ A₂

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
⊑ᶜᵀ-left-typed (⊑inj M⊑M′ vM vM′ g) = ⊢! (⊑ᶜᵀ-left-typed M⊑M′) g vM
⊑ᶜᵀ-left-typed (⊑injL M⊑M′ vM g VM′) = ⊢! (⊑ᶜᵀ-left-typed M⊑M′) g vM


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
⊑ᶜᵀ-right-typed (⊑inj M⊑M′ vM vM′ g) = ⊢! (⊑ᶜᵀ-right-typed M⊑M′) g vM′
⊑ᶜᵀ-right-typed (⊑injL M⊑M′ vM g vM′) = ⊑ᶜᵀ-right-typed M⊑M′

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
⊑ᶜᵀ-type-precision (⊑inj M⊑M′ vM vM′ g) = ⊑-★
⊑ᶜᵀ-type-precision (⊑injL M⊑M′ vM g vM′) = ⊑-★

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

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
renameᶜ ρ (inj M [ G ]!) = inj (renameᶜ ρ M) [ G ]!
renameᶜ ρ blame = blame

extsᶜ : Substᶜ → Substᶜ
extsᶜ σ zero = ` zero
extsᶜ σ (suc x) = renameᶜ suc (σ x)

substᶜ : Substᶜ → Termᶜ → Termᶜ
substᶜ σ (` x) = σ x
substᶜ σ ($ n) = $ n
substᶜ σ (ƛ A ⇒ N) = ƛ A ⇒ substᶜ (extsᶜ σ) N
substᶜ σ (L · M) = substᶜ σ L · substᶜ σ M
substᶜ σ (cast M [ c ]) = cast (substᶜ σ M) [ c ]
substᶜ σ (inj M [ G ]!) = inj (substᶜ σ M) [ G ]!
substᶜ σ blame = blame

singleEnvᶜ : Termᶜ → Substᶜ
singleEnvᶜ M zero = M
singleEnvᶜ M (suc x) = ` x

_[_]ᶜ : Termᶜ → Termᶜ → Termᶜ
N [ M ]ᶜ = substᶜ (singleEnvᶜ M) N

--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

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
    → (ƛ A ⇒ N) · V —→ᶜ N [ V ]ᶜ

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
    → cast (inj V [ G ]!) [ G `? ] —→ᶜ V

  β-proj-inj-bad : ∀ {V G H}
    → Valueᶜ V
    → G ≢ H
    → cast (inj V [ G ]!) [ H `? ] —→ᶜ blame

  β-inj : ∀{V}{G}
    → Valueᶜ V
    → cast V [ G ! ] —→ᶜ inj V [ G ]!

  ξξ-blame : ∀ {F M′}
    → M′ ≡ plug F blame
    → M′ —→ᶜ blame

pattern ξ F M—→N = ξξ {F = F} refl refl M—→N
pattern ξ-blame F = ξξ-blame {F = F} refl

postulate
  value-irreducible : ∀ {V N} → Valueᶜ V → V —→ᶜ N → ⊥
  var-irreducible : ∀ {x N} → ` x —→ᶜ N → ⊥
  blame-irreducible : ∀ {N} → blame —→ᶜ N → ⊥

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

infixr 2 _—↠ᶜ⟨_⟩_
_—↠ᶜ⟨_⟩_ : ∀ (L : Termᶜ) {M N : Termᶜ}
    → L —↠ᶜ M
    → M —↠ᶜ N
      ---------
    → L —↠ᶜ N
L —↠ᶜ⟨ L—↠M ⟩ M—↠N = L—↠M ++ᶜ M—↠N

ξ* : ∀ F {M N}
  → M —↠ᶜ N
  → plug F M —↠ᶜ plug F N
ξ* F (M ∎ᶜ) = plug F M ∎ᶜ
ξ* F (M —→ᶜ⟨ M—→N ⟩ N—↠P) =
  plug F M —→ᶜ⟨ ξ F M—→N ⟩ ξ* F N—↠P

Convergesᶜ : Termᶜ → Set
Convergesᶜ M = ∃[ W ] ((M —↠ᶜ W) × (Valueᶜ W ⊎ (W ≡ blame)))

data Result : Termᶜ → Set where
  r-val : (V : Termᶜ) → Valueᶜ V → Result V
  r-blame : Result blame

Divergesᶜ : Termᶜ → Set
Divergesᶜ M = ¬ Convergesᶜ M

--------------------------------------------------------------------------------
-- Proof of Progress
--------------------------------------------------------------------------------

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

canonical-★-inj : ∀ {V}
  → Valueᶜ V
  → [] ⊢ᶜ V ⦂ ★
  → ∃[ G ] ∃[ W ] (Valueᶜ W × (V ≡ inj W [ G ]!))
canonical-★-inj V-$ ()
canonical-★-inj V-ƛ ()
canonical-★-inj (V-! {V = W} vW) (⊢! pf x x₁) = _ , W , vW , refl
canonical-★-inj (V-cast↦ vV) (⊢cast _ ())

canonical-⇒
  : ∀ {V A B}
  → Valueᶜ V
  → [] ⊢ᶜ V ⦂ (A ⇒ B)
  → (∃[ N ] V ≡ (ƛ A ⇒ N))
    ⊎ (∃[ W ] ∃[ c ] ∃[ d ] (Valueᶜ W × (V ≡ cast W [ c ↦ d ])))
canonical-⇒ V-$ ()
canonical-⇒ (V-ƛ {N = N}) (⊢ƛ {A = A} N⦂B) = inj₁ (N , refl)
canonical-⇒ (V-cast↦ {V = W} {c = c} {d = d} vW) pf with pf
... | ⊢cast _ cwt with cwt
... | ⊢↦ _ _ = inj₂ (W , c , d , (vW , refl))

progressᶜ : ∀ {M A} → [] ⊢ᶜ M ⦂ A → Progressᶜ M
progressᶜ (⊢` ())
progressᶜ ⊢$ = done V-$
progressᶜ (⊢ƛ M⦂A) = done V-ƛ
progressᶜ (⊢· {L = L} {M = M} L⦂A⇒B M⦂A) with progressᶜ L⦂A⇒B
... | step L→L′ = step (ξ (□· M) L→L′)
... | crash refl = step (ξ-blame (□· M))
... | done vL with progressᶜ M⦂A
... | step M→M′ = step (ξ (L ·□ vL) M→M′)
... | crash refl = step (ξ-blame (L ·□ vL))
... | done vM with canonical-⇒ vL L⦂A⇒B
... | inj₁ (N , refl) = step (β-ƛ vM)
... | inj₂ (W , c , d , (vW , refl)) = step (β-↦ vW vM)
progressᶜ (⊢cast {c = c} M⦂A c⦂A⇨B) with progressᶜ M⦂A
... | step M→M′ = step (ξ (cast□[ c ]) M→M′)
... | crash refl = step (ξ-blame cast□[ c ])
... | done vM with c⦂A⇨B
... | ⊢idᶜ = step (β-id vM)
... | ⊢! g = step (β-inj vM)
... | ⊢↦ cwt dwt = done (V-cast↦ vM)
... | ⊢⨟ cwt dwt = step (β-seq vM)
... | ⊢? {G = G} g with canonical-★-inj vM M⦂A
... | H , W , (vW , refl) with H ≟Ty G
... | yes refl = step (β-proj-inj-ok vW)
... | no H≢G = step (β-proj-inj-bad vW H≢G)
progressᶜ ⊢blame = crash refl
progressᶜ (⊢! M⦂ g vM) = done (V-! vM)

--------------------------------------------------------------------------------
-- Proof of Preservation
--------------------------------------------------------------------------------

Renᶜ-typed : Renameᶜ → Ctx → Ctx → Set
Renᶜ-typed ρ Γ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

Substᶜ-typed : Substᶜ → Ctx → Ctx → Set
Substᶜ-typed σ Γ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ⊢ᶜ σ x ⦂ A

ext-renᶜ-typed
  : ∀ {Γ Γ′ A ρ}
  → Renᶜ-typed ρ Γ Γ′
  → Renᶜ-typed (extᶜ ρ) (A ∷ Γ) (A ∷ Γ′)
ext-renᶜ-typed ρ-typed Z = Z
ext-renᶜ-typed ρ-typed (S ∋x) = S (ρ-typed ∋x)

renameᶜ-preserve
  : ∀ {Γ Γ′ M A ρ}
  → Renᶜ-typed ρ Γ Γ′
  → Γ ⊢ᶜ M ⦂ A
  → Γ′ ⊢ᶜ renameᶜ ρ M ⦂ A
renameᶜ-preserve ρ-typed (⊢` ∋x) = ⊢` (ρ-typed ∋x)
renameᶜ-preserve ρ-typed ⊢$ = ⊢$
renameᶜ-preserve ρ-typed (⊢ƛ N⦂B) =
  ⊢ƛ (renameᶜ-preserve (ext-renᶜ-typed ρ-typed) N⦂B)
renameᶜ-preserve ρ-typed (⊢· L⦂ M⦂) =
  ⊢· (renameᶜ-preserve ρ-typed L⦂) (renameᶜ-preserve ρ-typed M⦂)
renameᶜ-preserve ρ-typed (⊢cast M⦂ c⦂) =
  ⊢cast (renameᶜ-preserve ρ-typed M⦂) c⦂
renameᶜ-preserve ρ-typed (⊢! M⦂ g vM) =
  ⊢! (renameᶜ-preserve ρ-typed M⦂) g (helper vM)
  where
  helper : ∀ {V} → Valueᶜ V → Valueᶜ (renameᶜ _ V)
  helper V-$ = V-$
  helper V-ƛ = V-ƛ
  helper (V-! vV) = V-! (helper vV)
  helper (V-cast↦ vV) = V-cast↦ (helper vV)
renameᶜ-preserve ρ-typed ⊢blame = ⊢blame

wk-renᶜ-typed : ∀ {Γ A} → Renᶜ-typed suc Γ (A ∷ Γ)
wk-renᶜ-typed ∋x = S ∋x

ext-substᶜ-typed
  : ∀ {Γ Γ′ A σ}
  → Substᶜ-typed σ Γ Γ′
  → Substᶜ-typed (extsᶜ σ) (A ∷ Γ) (A ∷ Γ′)
ext-substᶜ-typed σ-typed Z = ⊢` Z
ext-substᶜ-typed σ-typed (S ∋x) =
  renameᶜ-preserve wk-renᶜ-typed (σ-typed ∋x)

substᶜ-preserve
  : ∀ {Γ Γ′ M A σ}
  → Substᶜ-typed σ Γ Γ′
  → Γ ⊢ᶜ M ⦂ A
  → Γ′ ⊢ᶜ substᶜ σ M ⦂ A
substᶜ-preserve σ-typed (⊢` ∋x) = σ-typed ∋x
substᶜ-preserve σ-typed ⊢$ = ⊢$
substᶜ-preserve σ-typed (⊢ƛ N⦂B) =
  ⊢ƛ (substᶜ-preserve (ext-substᶜ-typed σ-typed) N⦂B)
substᶜ-preserve σ-typed (⊢· L⦂ M⦂) =
  ⊢· (substᶜ-preserve σ-typed L⦂) (substᶜ-preserve σ-typed M⦂)
substᶜ-preserve σ-typed (⊢cast M⦂ c⦂) =
  ⊢cast (substᶜ-preserve σ-typed M⦂) c⦂
substᶜ-preserve σ-typed (⊢! M⦂ g vM) =
  ⊢! (substᶜ-preserve σ-typed M⦂) g (helper vM)
  where
  helper : ∀ {V} → Valueᶜ V → Valueᶜ (substᶜ _ V)
  helper V-$ = V-$
  helper V-ƛ = V-ƛ
  helper (V-! vV) = V-! (helper vV)
  helper (V-cast↦ vV) = V-cast↦ (helper vV)
substᶜ-preserve σ-typed ⊢blame = ⊢blame

single-substᶜ-typed
  : ∀ {A V}
  → [] ⊢ᶜ V ⦂ A
  → Substᶜ-typed (singleEnvᶜ V) (A ∷ []) []
single-substᶜ-typed V⦂ Z = V⦂
single-substᶜ-typed V⦂ (S ())

substᶜ-preserve-single
  : ∀ {A B N V}
  → (A ∷ []) ⊢ᶜ N ⦂ B
  → [] ⊢ᶜ V ⦂ A
  → [] ⊢ᶜ N [ V ]ᶜ ⦂ B
substᶜ-preserve-single N⦂ V⦂ = substᶜ-preserve (single-substᶜ-typed V⦂) N⦂

frame-blameᶜ
  : ∀ {F A}
  → [] ⊢ᶜ plug F blame ⦂ A
  → [] ⊢ᶜ blame ⦂ A
frame-blameᶜ {F = □· M} (⊢· L⦂ M⦂) = ⊢blame
frame-blameᶜ {F = V ·□ vV} (⊢· V⦂ M⦂) = ⊢blame
frame-blameᶜ {F = cast□[ c ]} (⊢cast M⦂ c⦂) = ⊢blame

mutual
  preserveᶜ : ∀ {M N A}
      → [] ⊢ᶜ M ⦂ A
      → M —→ᶜ N
      → [] ⊢ᶜ N ⦂ A
  preserveᶜ M⦂A (ξξ {F = F} refl refl M→N) =
    frame-preserveᶜ {F = F} M⦂A M→N
  preserveᶜ (⊢· (⊢ƛ N⦂B) V⦂A) (β-ƛ vV) =
    substᶜ-preserve-single N⦂B V⦂A
  preserveᶜ (⊢cast V⦂A ⊢idᶜ) (β-id vV) = V⦂A
  preserveᶜ (⊢cast V⦂A (⊢⨟ c⦂ d⦂)) (β-seq vV) =
    ⊢cast (⊢cast V⦂A c⦂) d⦂
  preserveᶜ (⊢· (⊢cast V⦂ (⊢↦ c⦂ d⦂)) W⦂) (β-↦ vV vW) =
    ⊢cast (⊢· V⦂ (⊢cast W⦂ c⦂)) d⦂
  preserveᶜ (⊢cast (⊢! V⦂ g vV′) (⊢? x)) (β-proj-inj-ok vV) = V⦂
  preserveᶜ M⦂A (β-proj-inj-bad vV G≢H) = ⊢blame
  preserveᶜ (⊢cast V⦂ (⊢! g)) (β-inj vV) = ⊢! V⦂ g vV
  preserveᶜ M⦂A (ξξ-blame {F = F} refl) = frame-blameᶜ {F = F} M⦂A

  frame-preserveᶜ
    : ∀ {F M N A}
    → [] ⊢ᶜ plug F M ⦂ A
    → M —→ᶜ N
    → [] ⊢ᶜ plug F N ⦂ A
  frame-preserveᶜ {F = □· M₁} (⊢· M⦂ M₁⦂) M→N =
    ⊢· (preserveᶜ M⦂ M→N) M₁⦂
  frame-preserveᶜ {F = V ·□ vV} (⊢· V⦂ M⦂) M→N =
    ⊢· V⦂ (preserveᶜ M⦂ M→N)
  frame-preserveᶜ {F = cast□[ c ]} (⊢cast M⦂ c⦂) M→N =
    ⊢cast (preserveᶜ M⦂ M→N) c⦂

preserveᶜ*
  : ∀ {M N A}
  → [] ⊢ᶜ M ⦂ A
  → M —↠ᶜ N
  → [] ⊢ᶜ N ⦂ A
preserveᶜ* M⦂ (M ∎ᶜ) = M⦂
preserveᶜ* M⦂ (M —→ᶜ⟨ M→N ⟩ N—↠P) =
  preserveᶜ* (preserveᶜ M⦂ M→N) N—↠P


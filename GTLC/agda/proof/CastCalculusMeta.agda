module proof.CastCalculusMeta where

-- File Charter:
--   * Private progress/preservation metatheory for the cast calculus.
--   * Exported through `MetaTheory.agda` and consumed by GTLC proof modules.

open import Agda.Builtin.Nat using (suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Types
open import Contexts
open import Coercions
open import CastCalculus
data Progressᶜ (M : Termᶜ) : Set where
  done  : Valueᶜ M → Progressᶜ M
  step  : ∀ {N} → M —→ᶜ N → Progressᶜ M
  crash : ∀ {ℓ} → M ≡ blame {ℓ = ℓ} → Progressᶜ M

canonical-★-inj : ∀ {V}
  → Valueᶜ V
  → [] ⊢ᶜ V ⦂ ★
  → ∃[ G ] ∃[ W ] (Valueᶜ W × (V ≡ cast W [ G ! ]))
canonical-★-inj V-$ ()
canonical-★-inj V-ƛ ()
canonical-★-inj (V-cast! {V = W} {G = G} vW) (⊢cast _ (⊢! _)) = G , W , vW , refl
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
... | ⊢! g = done (V-cast! vM)
... | ⊢↦ cwt dwt = done (V-cast↦ vM)
... | ⊢⨟ cwt dwt = step (β-seq vM)
... | ⊢? {G = G} {ℓ = ℓ} g with canonical-★-inj vM M⦂A
... | H , W , (vW , refl) with H ≟Ty G
... | yes refl = step (β-proj-inj-ok vW)
... | no H≢G = step (β-proj-inj-bad {ℓ = ℓ} vW H≢G)
progressᶜ ⊢blame = crash refl

--------------------------------------------------------------------------------
-- Proof of Preservation
--------------------------------------------------------------------------------

_⦂_⇒ʳ_ : Renameᶜ → Ctx → Ctx → Set
ρ ⦂ Γ ⇒ʳ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

_⦂_⇒ˢ_ : Substᶜ → Ctx → Ctx → Set
σ ⦂ Γ ⇒ˢ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ⊢ᶜ σ x ⦂ A

ext-renᶜ-typed
  : ∀ {Γ Γ′ A ρ}
  → ρ ⦂ Γ ⇒ʳ Γ′
  → extᶜ ρ ⦂ (A ∷ Γ) ⇒ʳ (A ∷ Γ′)
ext-renᶜ-typed ρ-typed Z = Z
ext-renᶜ-typed ρ-typed (S ∋x) = S (ρ-typed ∋x)

renameᶜ-preserve
  : ∀ {Γ Γ′ M A ρ}
  → ρ ⦂ Γ ⇒ʳ Γ′
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
renameᶜ-preserve ρ-typed ⊢blame = ⊢blame

wk-renᶜ-typed : ∀ {Γ A} → suc ⦂ Γ ⇒ʳ (A ∷ Γ)
wk-renᶜ-typed ∋x = S ∋x

ext-substᶜ-typed
  : ∀ {Γ Γ′ A σ}
  → σ ⦂ Γ ⇒ˢ Γ′
  → extsᶜ σ ⦂ (A ∷ Γ) ⇒ˢ (A ∷ Γ′)
ext-substᶜ-typed σ-typed Z = ⊢` Z
ext-substᶜ-typed σ-typed (S ∋x) =
  renameᶜ-preserve wk-renᶜ-typed (σ-typed ∋x)

substᶜ-preserve-value
  : ∀ {σ V}
  → Valueᶜ V
  → Valueᶜ (substᶜ σ V)
substᶜ-preserve-value V-$ = V-$
substᶜ-preserve-value V-ƛ = V-ƛ
substᶜ-preserve-value (V-cast! vV) = V-cast! (substᶜ-preserve-value vV)
substᶜ-preserve-value (V-cast↦ vV) = V-cast↦ (substᶜ-preserve-value vV)

substᶜ-preserve
  : ∀ {Γ Γ′ M A σ}
  → σ ⦂ Γ ⇒ˢ Γ′
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
substᶜ-preserve σ-typed ⊢blame = ⊢blame

single-substᶜ-typed
  : ∀ {A V}
  → [] ⊢ᶜ V ⦂ A
  → singleEnvᶜ V ⦂ (A ∷ []) ⇒ˢ []
single-substᶜ-typed V⦂ Z = V⦂
single-substᶜ-typed V⦂ (S ())

substᶜ-preserve-single
  : ∀ {A B N V}
  → (A ∷ []) ⊢ᶜ N ⦂ B
  → [] ⊢ᶜ V ⦂ A
  → [] ⊢ᶜ N [ V ]ᶜ ⦂ B
substᶜ-preserve-single N⦂ V⦂ = substᶜ-preserve (single-substᶜ-typed V⦂) N⦂

frame-blameᶜ
  : ∀ {F A ℓ}
  → [] ⊢ᶜ plug F (blame {ℓ = ℓ}) ⦂ A
  → [] ⊢ᶜ blame {ℓ = ℓ} ⦂ A
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
  preserveᶜ (⊢cast (⊢cast V⦂ (⊢! g)) (⊢? x)) (β-proj-inj-ok vV) = V⦂
  preserveᶜ M⦂A (β-proj-inj-bad vV G≢H) = ⊢blame
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

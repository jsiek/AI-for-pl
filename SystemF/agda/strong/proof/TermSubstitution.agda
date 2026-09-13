module strong.proof.TermSubstitution where

-- Strong System F v7 — term substitution, factored over the operation that
-- carries a closed substitution image across a type abstraction.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import strong.Types
open import strong.Ctx
open import strong.Terms
open import strong.TermSubst
open import strong.proof.CtxProperties using (ok-Λ)

lookup-tail : ∀ {Γ x A} Γ′
  → Γ ∋ x ⦂ A
  → (Γ ++ Γ′) ∋ x ⦂ A
lookup-tail Γ′ here = here
lookup-tail Γ′ (there x) = there (lookup-tail Γ′ x)

weaken-tail : ∀ {Δ Γ M A} Γ′
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ∣ Γ ++ Γ′ ⊢ M ⦂ A
weaken-tail Γ′ (⊢` x) = ⊢` (lookup-tail Γ′ x)
weaken-tail Γ′ ⊢$ = ⊢$
weaken-tail Γ′ ⊢# = ⊢#
weaken-tail Γ′ (⊢⊕ left right) =
  ⊢⊕ (weaken-tail Γ′ left) (weaken-tail Γ′ right)
weaken-tail Γ′ (⊢ƛ wf body) = ⊢ƛ wf (weaken-tail Γ′ body)
weaken-tail Γ′ (⊢· left right) =
  ⊢· (weaken-tail Γ′ left) (weaken-tail Γ′ right)
weaken-tail {Δ = Δ} {Γ = Γ} {M = Λ N} {A = `∀ A} Γ′ (⊢Λ body) =
  ⊢Λ (subst (λ Ξ → (name zero ∷ abst ∷ Δ) ∣ Ξ ⊢ N ⦂ A)
    (sym (map-++ ⇑ᵗ Γ Γ′))
    (weaken-tail {Γ = map ⇑ᵗ Γ} (map ⇑ᵗ Γ′) body))
weaken-tail Γ′ (⊢•[] left wf) = ⊢•[] (weaken-tail Γ′ left) wf
weaken-tail Γ′ (⊢ν store scope nf body conv) =
  ⊢ν store scope nf body conv

weaken-closed : ∀ {Δ Γ M A}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ∣ Γ ⊢ M ⦂ A
weaken-closed {Γ = Γ} typing = weaken-tail Γ typing

data _∣_⊢ⁱ_⦂_ (Δ : Ctxᵗ) (Γ : Ctx) : Img → Ty → Set where
  typed-var : ∀ {x A}
    → Γ ∋ x ⦂ A
    → Δ ∣ Γ ⊢ⁱ ivar x ⦂ A
  typed-val : ∀ {V A}
    → Δ ⊢ᵗ A
    → Δ ∣ [] ⊢ V ⦂ A
    → Δ ∣ Γ ⊢ⁱ ival V A ⦂ A

record EnvTyping (Δ : Ctxᵗ) (Γ Γ′ : Ctx) (σ : ℕ → Img) : Set where
  field
    lookup : ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ A
open EnvTyping

img-typing : ∀ {Δ Γ i A}
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
  → Δ ∣ Γ ⊢ imgTm i ⦂ A
img-typing (typed-var x) = ⊢` x
img-typing (typed-val wf value) = weaken-closed value

shift-img : ∀ {Δ Γ i A B}
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
  → Δ ∣ B ∷ Γ ⊢ⁱ shiftImgⁿ i ⦂ A
shift-img (typed-var x) = typed-var (there x)
shift-img (typed-val wf value) = typed-val wf value

ext-env : ∀ {Δ Γ Γ′ σ A}
  → EnvTyping Δ Γ Γ′ σ
  → EnvTyping Δ (A ∷ Γ) (A ∷ Γ′) (extImg σ)
lookup (ext-env env) here = typed-var here
lookup (ext-env env) (there x) = shift-img (lookup env x)

map-lookup : ∀ {Γ x A}
  → Γ ∋ x ⦂ A
  → map ⇑ᵗ Γ ∋ x ⦂ ⇑ᵗ A
map-lookup here = here
map-lookup (there x) = there (map-lookup x)

unmap-lookup : ∀ {Γ x B}
  → map ⇑ᵗ Γ ∋ x ⦂ B
  → Σ[ A ∈ Ty ] ((B ≡ ⇑ᵗ A) × (Γ ∋ x ⦂ A))
unmap-lookup {Γ = A ∷ Γ} here = A , refl , here
unmap-lookup {Γ = A ∷ Γ} (there x) with unmap-lookup x
unmap-lookup {Γ = A ∷ Γ} (there x) | B , refl , y =
  B , refl , there y

typePrefix : ℕ → Ctxᵗ → Ctxᵗ
typePrefix zero Δ = Δ
typePrefix (suc n) Δ = name zero ∷ abst ∷ typePrefix n Δ

liftInsert : ℕ → ℕ → ℕ
liftInsert zero = suc
liftInsert (suc n) = extᵗ (liftInsert n)

insert-tv : ∀ k {Δ X}
  → typePrefix k Δ ∋tv X
  → typePrefix k (name zero ∷ abst ∷ Δ) ∋tv liftInsert k X
insert-tv zero x = tv-over-name (tv-over-abst x)
insert-tv (suc k) tv-here = tv-here
insert-tv (suc k) (tv-over-name (tv-over-abst x)) =
  tv-over-name (tv-over-abst (insert-tv k x))

insert-wf : ∀ k {Δ A}
  → typePrefix k Δ ⊢ᵗ A
  → typePrefix k (name zero ∷ abst ∷ Δ) ⊢ᵗ renameᵗ (liftInsert k) A
insert-wf k (wf-var x) = wf-var (insert-tv k x)
insert-wf k wf-ℕ = wf-ℕ
insert-wf k wf-𝔹 = wf-𝔹
insert-wf k (wf-⇒ a b) = wf-⇒ (insert-wf k a) (insert-wf k b)
insert-wf k (wf-∀ a) = wf-∀ (insert-wf (suc k) a)

module WithCross
  (cross-typing : ∀ {Δ V A}
    → Δ ok
    → Δ ⊢ᵗ A
    → Δ ∣ [] ⊢ V ⦂ A
    → (name zero ∷ abst ∷ Δ) ∣ [] ⊢ crossΛ V A ⦂ ⇑ᵗ A)
  where

  underΛ-img : ∀ {Δ Γ i A}
    → Δ ok
    → Δ ∣ Γ ⊢ⁱ i ⦂ A
    → (name zero ∷ abst ∷ Δ) ∣ map ⇑ᵗ Γ
        ⊢ⁱ underΛ i ⦂ ⇑ᵗ A
  underΛ-img ctx-ok (typed-var x) = typed-var (map-lookup x)
  underΛ-img ctx-ok (typed-val wf value) =
    typed-val (insert-wf zero wf) (cross-typing ctx-ok wf value)

  underΛ-env : ∀ {Δ Γ Γ′ σ}
    → Δ ok
    → EnvTyping Δ Γ Γ′ σ
    → EnvTyping (name zero ∷ abst ∷ Δ) (map ⇑ᵗ Γ) (map ⇑ᵗ Γ′)
        (λ x → underΛ (σ x))
  lookup (underΛ-env ctx-ok env) x with unmap-lookup x
  lookup (underΛ-env ctx-ok env) x | A , refl , y =
    underΛ-img ctx-ok (lookup env y)

  subst-typing : ∀ {Δ Γ Γ′ σ M A}
    → Δ ok
    → EnvTyping Δ Γ Γ′ σ
    → Δ ∣ Γ ⊢ M ⦂ A
    → Δ ∣ Γ′ ⊢ substᵐ σ M ⦂ A
  subst-typing ctx-ok env (⊢` x) = img-typing (lookup env x)
  subst-typing ctx-ok env ⊢$ = ⊢$
  subst-typing ctx-ok env ⊢# = ⊢#
  subst-typing ctx-ok env (⊢⊕ left right) =
    ⊢⊕ (subst-typing ctx-ok env left) (subst-typing ctx-ok env right)
  subst-typing ctx-ok env (⊢ƛ wf body) =
    ⊢ƛ wf (subst-typing ctx-ok (ext-env env) body)
  subst-typing ctx-ok env (⊢· left right) =
    ⊢· (subst-typing ctx-ok env left) (subst-typing ctx-ok env right)
  subst-typing ctx-ok env (⊢Λ body) =
    ⊢Λ (subst-typing (ok-Λ ctx-ok) (underΛ-env ctx-ok env) body)
  subst-typing ctx-ok env (⊢•[] left wf) =
    ⊢•[] (subst-typing ctx-ok env left) wf
  subst-typing ctx-ok env (⊢ν store scope nf body conv) =
    ⊢ν store scope nf body conv

  beta-env : ∀ {Δ W A}
    → Δ ⊢ᵗ A
    → Δ ∣ [] ⊢ W ⦂ A
    → EnvTyping Δ (A ∷ []) []
        (singleImgEnv W A)
  lookup (beta-env wf value) here = typed-val wf value

  preserve-Beta : ∀ {Δ A N W B}
    → Δ ok
    → Value W
    → Δ ⊢ᵗ A
    → Δ ∣ A ∷ [] ⊢ N ⦂ B
    → Δ ∣ [] ⊢ W ⦂ A
    → Δ ∣ [] ⊢ N [ W ∶ A ]ᵐ ⦂ B
  preserve-Beta ctx-ok value wf body arg =
    subst-typing ctx-ok (beta-env wf arg) body

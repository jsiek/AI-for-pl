module Compile where

open import Types
open import Contexts
open import GTLC renaming
  ( _⊢_⦂_ to _⊢ᴳ_⦂_
  ; _⊢_⦂_⊑ᵀ_⦂_ to _⊢ᴳ_⦂_⊑ᴳᵀ_⦂_
  ; ⊢` to ⊢`ᴳ
  ; ⊢$ to ⊢$ᴳ
  ; ⊢ƛ to ⊢ƛᴳ
  ; ⊢· to ⊢·ᴳ
  ; ⊢·★ to ⊢·★ᴳ
  ; ⊑` to ⊑`ᴳ
  ; ⊑$ to ⊑$ᴳ
  ; ⊑ƛ to ⊑ƛᴳ
  ; ⊑· to ⊑·ᴳ
  ; ⊑·★ to ⊑·★ᴳ
  ; ⊑·★L to ⊑·★Lᴳ
  ; ⊑ᵀ-left-typed to ⊑ᵀ-left-typedᴳ
  ; ⊑ᵀ-right-typed to ⊑ᵀ-right-typedᴳ
  ; ⊑ᵀ-type-precision to ⊑ᵀ-type-precisionᴳ
  )
open import Coercions using
  ( coerce
  ; coerce-wt
  ; coerce-⊑ᶜ
  ; idᶜ
  ; _⊑ᶜ_
  ; ⊑idR
  ; ⊑idR⨟
  ; ⊢idᶜ
  ; ⊢?
  ; ⊢↦
  ; G-⇒
  )
open import CastCalculus

compile-∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ A
compile-∋ Z = Z
compile-∋ (S ∋x) = S (compile-∋ ∋x)

compile : ∀ {Γ M A} → Γ ⊢ᴳ M ⦂ A → Termᶜ
compile (⊢`ᴳ {x = x} _) = ` x
compile (⊢$ᴳ {n = n}) = $ n
compile (⊢ƛᴳ {A = A} N⦂B) = ƛ A ⇒ compile N⦂B
compile (⊢·ᴳ L⦂A⇒B M⦂A′ A′~A) =
  compile L⦂A⇒B · cast compile M⦂A′ [ coerce A′~A ]
compile (⊢·★ᴳ {A = A} L⦂★ M⦂A) =
  cast compile L⦂★ [ coerce (★~-ty (★ ⇒ ★)) ] · cast compile M⦂A [ coerce (~★-ty A) ]

compile-preserves : ∀ {Γ M A} (d : Γ ⊢ᴳ M ⦂ A) → Γ ⊢ᶜ compile d ⦂ A
compile-preserves (⊢`ᴳ ∋x) = ⊢` (compile-∋ ∋x)
compile-preserves (⊢$ᴳ {n = n}) = ⊢$
compile-preserves (⊢ƛᴳ {A = A} N⦂B) = ⊢ƛ (compile-preserves N⦂B)
compile-preserves (⊢·ᴳ L⦂A⇒B M⦂A′ A′~A) =
  ⊢·
    (compile-preserves L⦂A⇒B)
    (⊢cast (compile-preserves M⦂A′) (coerce-wt A′~A))
compile-preserves (⊢·★ᴳ {A = A} L⦂★ M⦂A) =
  ⊢·
    (⊢cast (compile-preserves L⦂★) (coerce-wt (★~-ty (★ ⇒ ★))))
    (⊢cast (compile-preserves M⦂A) (coerce-wt (~★-ty A)))

⇒-dom-⊑ : ∀ {A A′ B B′} → (A ⇒ B) ⊑ (A′ ⇒ B′) → A ⊑ A′
⇒-dom-⊑ (⊑-⇒ A⊑A′ _) = A⊑A′

coerce-★⇒★-⊑id : ∀ {A B} → coerce (★~-ty (★ ⇒ ★)) ⊑ᶜ idᶜ (A ⇒ B)
coerce-★⇒★-⊑id {A} {B} =
  ⊑idR⨟
    (⊑idR (λ ()) (⊢? G-⇒) ⊑-★ (⊑-⇒ ⊑-★ ⊑-★))
    (⊑idR (λ ()) (⊢↦ ⊢idᶜ ⊢idᶜ) (⊑-⇒ ⊑-★ ⊑-★) (⊑-⇒ ⊑-★ ⊑-★))

compile-preserves-precision
  : ∀ {Γ Γ′ M M′ A A′}
  → (ρ : Γ′ ⊑ᵉ Γ)
  → (d : ρ ⊢ᴳ M′ ⦂ A′ ⊑ᴳᵀ M ⦂ A)
  → ρ ⊢ compile (⊑ᵀ-left-typedᴳ d) ⦂ A′ ⊑ᶜᵀ compile (⊑ᵀ-right-typedᴳ d) ⦂ A
compile-preserves-precision ρ (⊑`ᴳ ∋x′ ∋x) =
  ⊑` (compile-∋ ∋x′) (compile-∋ ∋x)
compile-preserves-precision ρ ⊑$ᴳ = ⊑$
compile-preserves-precision ρ (⊑ƛᴳ A′⊑A N′⊑N) =
  ⊑ƛ A′⊑A (compile-preserves-precision (extend-⊑ᵉ A′⊑A ρ) N′⊑N)
compile-preserves-precision ρ
  (⊑·ᴳ {A = A′} {A′ = A} {Aarg = A′arg} {A′arg = Aarg}
        L′⊑L M′⊑M A′arg~A′ Aarg~A)
  with ⊑ᵀ-type-precisionᴳ L′⊑L
... | A′⇒B′⊑A⇒B =
  ⊑·
    (compile-preserves-precision ρ L′⊑L)
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-⊑ᶜ (⊑ᵀ-type-precisionᴳ M′⊑M) Aarg~A (⇒-dom-⊑ A′⇒B′⊑A⇒B) A′arg~A′)
      (coerce-wt A′arg~A′)
      (coerce-wt Aarg~A))
compile-preserves-precision ρ (⊑·★ᴳ {A = A′} {A′ = A} L′⊑L M′⊑M) =
  ⊑·
    (⊑cast
      (compile-preserves-precision ρ L′⊑L)
      (coerce-⊑ᶜ (⊑ᵀ-type-precisionᴳ L′⊑L) (★~-ty (★ ⇒ ★)) ⊑-refl (★~-ty (★ ⇒ ★)))
      (coerce-wt (★~-ty (★ ⇒ ★)))
      (coerce-wt (★~-ty (★ ⇒ ★))))
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-⊑ᶜ (⊑ᵀ-type-precisionᴳ M′⊑M) (~★-ty A) ⊑-★ (~★-ty A′))
      (coerce-wt (~★-ty A′))
      (coerce-wt (~★-ty A)))
compile-preserves-precision ρ
  (⊑·★Lᴳ {A = A′} {A′ = A} {A′arg = Aarg} L′⊑L M′⊑M Aarg~A) =
  ⊑·
    (⊑castL
      (compile-preserves-precision ρ L′⊑L)
      (coerce-wt (★~-ty (★ ⇒ ★)))
      coerce-★⇒★-⊑id)
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-⊑ᶜ (⊑ᵀ-type-precisionᴳ M′⊑M) Aarg~A ⊑-★ (~★-ty A′))
      (coerce-wt (~★-ty A′))
      (coerce-wt Aarg~A))

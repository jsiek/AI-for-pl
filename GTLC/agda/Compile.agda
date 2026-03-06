module Compile where

open import GTLC renaming
  ( _∋_⦂_ to _∋ᴳ_⦂_
  ; _⊢_⦂_ to _⊢ᴳ_⦂_
  ; _⊑ᵀ_ to _⊑ᴳᵀ_
  ; Z to Zᴳ
  ; S to Sᴳ
  ; ⊢` to ⊢`ᴳ
  ; ⊢$ to ⊢$ᴳ
  ; ⊢ƛ to ⊢ƛᴳ
  ; ⊢· to ⊢·ᴳ
  ; ⊢·★ to ⊢·★ᴳ
  ; ⊑` to ⊑`ᴳ
  ; ⊑$ to ⊑$ᴳ
  ; ⊑ƛ to ⊑ƛᴳ
  ; ⊑· to ⊑·ᴳ
  )
open import Coercions using (coerce; coerce-wt)
open import CastCalculus

compile-∋ : ∀ {Γ x A} → Γ ∋ᴳ x ⦂ A → Γ ∋ᶜ x ⦂ A
compile-∋ Zᴳ = Z
compile-∋ (Sᴳ ∋x) = S (compile-∋ ∋x)

compile : ∀ {Γ M A} → Γ ⊢ᴳ M ⦂ A → Termᶜ
compile (⊢`ᴳ {x = x} _) = ` x
compile (⊢$ᴳ {n = n}) = $ n
compile (⊢ƛᴳ {A = A} N⦂B) = ƛ A ⇒ compile N⦂B
compile (⊢·ᴳ L⦂A⇒B M⦂A′ A′~A) =
  compile L⦂A⇒B · cast compile M⦂A′ [ coerce A′~A ]
compile (⊢·★ᴳ {A = A} L⦂★ M⦂A) =
  cast compile L⦂★ [ coerce (★~-ty (A ⇒ ★)) ] · compile M⦂A

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
    (⊢cast (compile-preserves L⦂★) (coerce-wt (★~-ty (A ⇒ ★))))
    (compile-preserves M⦂A)

compile-preserves-precision
  : ∀ {Γ Γ′ M M′ A A′}
  → (d′ : Γ′ ⊢ᴳ M′ ⦂ A′)
  → (d  : Γ ⊢ᴳ M ⦂ A)
  → M′ ⊑ᴳᵀ M
  → compile d′ ⊑ᶜᵀ compile d
compile-preserves-precision (⊢`ᴳ {x = x} ∋x′) (⊢`ᴳ ∋x) ⊑`ᴳ = ⊑`
compile-preserves-precision (⊢$ᴳ {n = n}) (⊢$ᴳ {n = m}) ⊑$ᴳ = ⊑$
compile-preserves-precision (⊢ƛᴳ {A = A′} N′⦂B′) (⊢ƛᴳ {A = A} N⦂B) (⊑ƛᴳ A′⊑A N′⊑N) =
  ⊑ƛ A′⊑A (compile-preserves-precision N′⦂B′ N⦂B N′⊑N)
compile-preserves-precision (⊢·ᴳ L′⦂A⇒B M′⦂A′ A′~A) (⊢·ᴳ L⦂A⇒B M⦂A A~A₀) (⊑·ᴳ L′⊑L M′⊑M) =
  ⊑·
    (compile-preserves-precision L′⦂A⇒B L⦂A⇒B L′⊑L)
    (⊑cast* (compile-preserves-precision M′⦂A′ M⦂A M′⊑M))
compile-preserves-precision (⊢·★ᴳ {A = A′} L′⦂★ M′⦂A′) (⊢·ᴳ {A = A} L⦂A⇒B M⦂A₀ A₀~A) (⊑·ᴳ L′⊑L M′⊑M) =
  ⊑·
    (⊑castL (compile-preserves-precision L′⦂★ L⦂A⇒B L′⊑L))
    (⊑castR (compile-preserves-precision M′⦂A′ M⦂A₀ M′⊑M))
compile-preserves-precision (⊢·ᴳ L′⦂A⇒B M′⦂A′ A′~A) (⊢·★ᴳ {A = A} L⦂★ M⦂A) (⊑·ᴳ L′⊑L M′⊑M) =
  ⊑·
    (⊑castR (compile-preserves-precision L′⦂A⇒B L⦂★ L′⊑L))
    (⊑castL (compile-preserves-precision M′⦂A′ M⦂A M′⊑M))
compile-preserves-precision (⊢·★ᴳ {A = A′} L′⦂★ M′⦂A′) (⊢·★ᴳ {A = A} L⦂★ M⦂A) (⊑·ᴳ L′⊑L M′⊑M) =
  ⊑·
    (⊑cast* (compile-preserves-precision L′⦂★ L⦂★ L′⊑L))
    (compile-preserves-precision M′⦂A′ M⦂A M′⊑M)

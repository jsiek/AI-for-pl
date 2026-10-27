module Compile where

-- File Charter:
--   * Elaboration of PolyGν into PolyCν (thesis Fig. 10.10), ∀ν fragment,
--     by recursion on typing derivations.
--   * An ascription M :: B, with M : A, becomes ⟨B?⟩↓ ⟨A?⟩↑ M.
--   * An elimination at type ? first casts down to the ground type
--     (the thesis's G ⇓ M).
--   * The branches of an `if` are cast down to the meet of their types.

open import Data.List using ([])

open import Types
open import Terms
open import GradualTerms

------------------------------------------------------------------------
-- Cast helpers
------------------------------------------------------------------------

-- ⟨B?⟩↓ ⟨A?⟩↑ M
ascribe : Ty → Ty → Term → Term
ascribe A B M = cast down (dynᵖ B) (cast up (dynᵖ A) M)

-- G ⇓ M, for M : A: a downcast from ? to G when A is ?
⇓ : Ground → Ty → Term → Term
⇓ G (‵ α) M = M
⇓ G 𝔹 M = M
⇓ G ★ M = cast down (tag G (idᵖ (groundTy G))) M
⇓ G (A ⇒ B) M = M
⇓ G (∀ν A) M = M

-- the derivations C ⊑ A and C ⊑ B for a meet C = A ⊓ B
meetL : ∀ {A B C} → Meet A B C → Prec
meetL {B = B} m★L = dynᵖ B
meetL {A = A} m★R = idᵖ A
meetL {A = ‵ α} m‵ = ‵⊑ α
meetL m𝔹 = 𝔹⊑
meetL (m⇒ m n) = meetL m ⇒⊑ meetL n
meetL (m∀ m) = ∀⊑ (meetL m)

meetR : ∀ {A B C} → Meet A B C → Prec
meetR {B = B} m★L = idᵖ B
meetR {A = A} m★R = dynᵖ A
meetR {B = ‵ α} m‵ = ‵⊑ α
meetR m𝔹 = 𝔹⊑
meetR (m⇒ m n) = meetR m ⇒⊑ meetR n
meetR (m∀ m) = ∀⊑ (meetR m)

------------------------------------------------------------------------
-- Elaboration
------------------------------------------------------------------------

elab : ∀ {Δ Γ M A} → Δ ∣ Γ ⊢ᴳ M ⦂ A → Term
elab (⊢` {x = x} x∈) = ` x
elab (⊢⦂⦂ {A = A} {B = B} ⊢M A∼B wfB) = ascribe A B (elab ⊢M)
elab (⊢seal {X = X} {A = A} {B = B} X≅A ⊢M B∼A) =
  seal (tvar X) (ascribe B A (elab ⊢M))
elab (⊢unseal {X = X} {B = B} X≅A ⊢M B∼X) =
  unseal (tvar X) (⇓ (G‵ (tvar X)) B (elab ⊢M))
elab (⊢is {G = G} {A = A} wfG ⊢M) = is G (cast up (dynᵖ A) (elab ⊢M))
elab ⊢true = true
elab ⊢false = false
elab (⊢if {A = A} ⊢L A∼𝔹 ⊢M ⊢N m) =
  if (⇓ G𝔹 A (elab ⊢L))
     (cast down (meetL m) (elab ⊢M))
     (cast down (meetR m) (elab ⊢N))
elab (⊢ƛ {A = A} wfA ⊢M) = ƛ A (elab ⊢M)
elab (⊢· {A = A} {A₁ = A₁} {B = B} ⊢L shp ⊢M B∼A₁) =
  ⇓ G⇒ A (elab ⊢L) · ascribe B A₁ (elab ⊢M)
elab (⊢letv ⊢M ⊢N) = letv (elab ⊢M) (elab ⊢N)
elab (⊢Λν ⊢M) = Λν [] (elab ⊢M)
elab (⊢inst {A = A} {B = B} ⊢M shp wfB ⊢N wfC) =
  inst (⇓ G∀ A (elab ⊢M)) B (idᵖ B) (elab ⊢N)

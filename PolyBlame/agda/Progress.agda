module Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)

open import PolyBlame

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress (Σ : Store) (M : Term) : Set where
  done  : Value M → Progress Σ M
  step  : ∀ {Σ' N} → (Σ ⊲ M) —→ (Σ' ⊲ N) → Progress Σ M
  crash : M ≡ blame → Progress Σ M

------------------------------------------------------------------------
-- Small helpers for context closure
------------------------------------------------------------------------

ξ : {Σ Π : Store} {F : Frame} {M N : Term} →
    (Σ ⊲ M) —→ (Π ⊲ N) →
    (Σ ⊲ plug F M) —→ (Π ⊲ plug F N)
ξ s = ξξ refl refl s

ξ-blame : {Σ : Store} {F : Frame} →
          (Σ ⊲ plug F blame) —→ (Σ ⊲ blame)
ξ-blame = ξξ-blame refl

------------------------------------------------------------------------
-- Decidable tag equality
------------------------------------------------------------------------

infix 4 _≟Base_
_≟Base_ : (ι ι' : Base) → Dec (ι ≡ ι')
`ℕ ≟Base `ℕ = yes refl
`ℕ ≟Base `𝔹 = no (λ ())
`𝔹 ≟Base `ℕ = no (λ ())
`𝔹 ≟Base `𝔹 = yes refl

infix 4 _≟Ground_
_≟Ground_ : (G H : Ground) → Dec (G ≡ H)
G-α α ≟Ground G-α β with α ≟ β
... | yes refl = yes refl
... | no α≢β   = no (λ { refl → α≢β refl })
G-α α ≟Ground G-ι ι = no (λ ())
G-α α ≟Ground G-★⇒★ = no (λ ())
G-ι ι ≟Ground G-α α = no (λ ())
G-ι ι ≟Ground G-ι ι' with ι ≟Base ι'
... | yes refl = yes refl
... | no ι≢ι'   = no (λ { refl → ι≢ι' refl })
G-ι ι ≟Ground G-★⇒★ = no (λ ())
G-★⇒★ ≟Ground G-α α = no (λ ())
G-★⇒★ ≟Ground G-ι ι = no (λ ())
G-★⇒★ ≟Ground G-★⇒★ = yes refl

------------------------------------------------------------------------
-- Canonical forms for closed values
------------------------------------------------------------------------

data NatCanon (V : Term) : Set where
  cκℕ : (n : ℕ) → V ≡ ($ (κℕ n)) → NatCanon V

data FunCanon (V : Term) : Set where
  cƛ    : {A : Ty} {N : Term} → V ≡ (ƛ A ⇒ N) → FunCanon V
  c↑→   : {W : Term} {s t : Imp} → Value W → V ≡ (W at up ⌈ s →ᵖ t ⌉) → FunCanon V
  c↓→   : {W : Term} {s t : Imp} → Value W → V ≡ (W at down ⌈ s →ᵖ t ⌉) → FunCanon V

data ForallCanon (V : Term) : Set where
  cΛ    : {N : Term} → V ≡ (Λ N) → ForallCanon V
  c↑∀   : {W : Term} {p : Imp} → Value W → V ≡ (W at up ⌈ ∀ᵖ p ⌉) → ForallCanon V
  c↓∀   : {W : Term} {p : Imp} → Value W → V ≡ (W at down ⌈ ∀ᵖ p ⌉) → ForallCanon V
  c↓ν   : {W : Term} {p : Imp} → Value W → V ≡ (W at down (nuImp p)) → ForallCanon V

data StarCanon (V : Term) : Set where
  cTag : {W : Term} {g : CImp} {G : Ground} →
         Value W →
         V ≡ (W at up (injTag g G)) →
         StarCanon V

data AlphaCanon (α : Seal) (V : Term) : Set where
  cSeal : {W : Term} {p : Imp} →
          Value W →
          V ≡ (W at down (sealImp α p)) →
          AlphaCanon α V

canonical-ℕ :
  ∀ {Δ Σ V} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ ‵ `ℕ →
  NatCanon V
canonical-ℕ vƛ ()
canonical-ℕ vΛ ()
canonical-ℕ {V = $ (κℕ n)} vκ ⊢$ = cκℕ n refl
canonical-ℕ (v+tag v) (⊢cast-up hV ())
canonical-ℕ (v-seal v) (⊢cast-down hV ())
canonical-ℕ (v→+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-ℕ (v→- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-ℕ (v∀+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-ℕ (v∀- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-ℕ (vν- v) (⊢cast-down hV ())

canonical-⇒ :
  ∀ {Δ Σ V A B} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ (A ⇒ B) →
  FunCanon V
canonical-⇒ vƛ (⊢ƛ hA hN) = cƛ refl
canonical-⇒ vΛ ()
canonical-⇒ {V = $ (κℕ n)} vκ ()
canonical-⇒ (v+tag v) (⊢cast-up hV ())
canonical-⇒ (v-seal v) (⊢cast-down hV ())
canonical-⇒ (v→+ v) (⊢cast-up hV (⊢⌈⌉ (⊢→ᵖ hp hq))) = c↑→ v refl
canonical-⇒ (v→- v) (⊢cast-down hV (⊢⌈⌉ (⊢→ᵖ hp hq))) = c↓→ v refl
canonical-⇒ (v∀+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-⇒ (v∀- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-⇒ (vν- v) (⊢cast-down hV ())

canonical-∀ :
  ∀ {Δ Σ V A} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ `∀ A →
  ForallCanon V
canonical-∀ vƛ ()
canonical-∀ vΛ (⊢Λ hN) = cΛ refl
canonical-∀ {V = $ (κℕ n)} vκ ()
canonical-∀ (v+tag v) (⊢cast-up hV ())
canonical-∀ (v-seal v) (⊢cast-down hV ())
canonical-∀ (v→+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-∀ (v→- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-∀ (v∀+ v) (⊢cast-up hV (⊢⌈⌉ (⊢∀ᵖ hp))) = c↑∀ v refl
canonical-∀ (v∀- v) (⊢cast-down hV (⊢⌈⌉ (⊢∀ᵖ hp))) = c↓∀ v refl
canonical-∀ (vν- v) (⊢cast-down hV (⊢ν hp hA hB)) = c↓ν v refl

canonical-★ :
  ∀ {Δ Σ V} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ `★ →
  StarCanon V
canonical-★ vƛ ()
canonical-★ vΛ ()
canonical-★ {V = $ (κℕ n)} vκ ()
canonical-★ (v+tag v) (⊢cast-up hV (⊢tag hp)) = cTag v refl
canonical-★ (v-seal v) (⊢cast-down hV ())
canonical-★ (v→+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-★ (v→- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-★ (v∀+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-★ (v∀- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-★ (vν- v) (⊢cast-down hV ())

canonical-α :
  ∀ {Δ Σ α V} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ ｀ α →
  AlphaCanon α V
canonical-α vƛ ()
canonical-α vΛ ()
canonical-α {V = $ (κℕ n)} vκ ()
canonical-α (v+tag v) (⊢cast-up hV ())
canonical-α (v-seal v) (⊢cast-down hV (⊢seal x hp)) = cSeal v refl
canonical-α (v→+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-α (v→- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-α (v∀+ v) (⊢cast-up hV (⊢⌈⌉ ()))
canonical-α (v∀- v) (⊢cast-down hV (⊢⌈⌉ ()))
canonical-α (vν- v) (⊢cast-down hV ())

------------------------------------------------------------------------
-- Cast progress helpers
------------------------------------------------------------------------

cast-up-progress :
  ∀ {Δ Σ V A B p} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ A →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
  Progress Σ (V at up p)
cast-up-progress vV hV (⊢⌈⌉ (⊢idα x)) = step (β-id+ vV tt)
cast-up-progress vV hV (⊢⌈⌉ (⊢idX x)) = step (β-id+ vV tt)
cast-up-progress vV hV (⊢⌈⌉ ⊢idι) = step (β-id+ vV tt)
cast-up-progress vV hV (⊢⌈⌉ (⊢→ᵖ hp hq)) = done (v→+ vV)
cast-up-progress vV hV (⊢⌈⌉ (⊢∀ᵖ hp)) = done (v∀+ vV)
cast-up-progress vV hV ⊢id★ = step (β-id+ vV tt)
cast-up-progress vV hV (⊢tag hp) = done (v+tag vV)
cast-up-progress vV hV (⊢seal x hp) with canonical-α vV hV
... | cSeal vW refl = step (β-seal vW)
cast-up-progress vV hV (⊢ν hp hA hB) = step (β-ν+ vV)

cast-down-progress :
  ∀ {Δ Σ V A B p} →
  Value V →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ B →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
  Progress Σ (V at down p)
cast-down-progress vV hV (⊢⌈⌉ (⊢idα x)) = step (β-id- vV tt)
cast-down-progress vV hV (⊢⌈⌉ (⊢idX x)) = step (β-id- vV tt)
cast-down-progress vV hV (⊢⌈⌉ ⊢idι) = step (β-id- vV tt)
cast-down-progress vV hV (⊢⌈⌉ (⊢→ᵖ hp hq)) = done (v→- vV)
cast-down-progress vV hV (⊢⌈⌉ (⊢∀ᵖ hp)) = done (v∀- vV)
cast-down-progress vV hV ⊢id★ = step (β-id- vV tt)
cast-down-progress {p = injTag h H} vV hV (⊢tag hp) with canonical-★ vV hV
... | cTag {g = g} {G = G} vW refl with G ≟Ground H
...   | yes refl = step (β-tag-ok vW)
...   | no G≢H = step (β-tag-bad vW G≢H)
cast-down-progress vV hV (⊢seal x hp) = done (v-seal vV)
cast-down-progress vV hV (⊢ν hp hA hB) = done (vν- vV)

------------------------------------------------------------------------
-- Progress theorem
------------------------------------------------------------------------

progress :
  ∀ {Δ Σ M A} →
  Δ ∣ Σ ⊢ [] ⊢ M ⦂ A →
  Progress Σ M
progress (⊢` ())
progress (⊢ƛ hA hN) = done vƛ
progress (⊢· {L = L} {M = M} hL hM) with progress hL
... | step sL = step (ξ {F = □· M} sL)
... | crash refl = step (ξ-blame {F = □· M})
... | done vL with progress hM
...   | step sM = step (ξ {F = L ·□ vL} sM)
...   | crash refl = step (ξ-blame {F = L ·□ vL})
...   | done vM with canonical-⇒ vL hL
...     | cƛ refl = step (β-ƛ vM)
...     | c↑→ vW refl = step (β-→+ vW vM)
...     | c↓→ vW refl = step (β-→- vW vM)
progress (⊢Λ hN) = done vΛ
progress (⊢·α {L = L} {α = α} hL hα) with progress hL
... | step sL = step (ξ {F = □·α α} sL)
... | crash refl = step (ξ-blame {F = □·α α})
... | done vL with canonical-∀ vL hL
...   | cΛ refl = step β-Λ
...   | c↑∀ vW refl = step (β-∀+ vW)
...   | c↓∀ vW refl = step (β-∀- vW)
...   | c↓ν vW refl = step (β-ν- vW)
progress (⊢ν hA hN hB) = step ξν
progress ⊢$ = done vκ
progress (⊢⊕ {M = M} {N = N} {op = op} hM hN) with progress hM
... | step sM = step (ξ {F = □⊕[ op ] N} sM)
... | crash refl = step (ξ-blame {F = □⊕[ op ] N})
... | done vM with progress hN
...   | step sN = step (ξ {F = M ⊕[ op ]□ vM} sN)
...   | crash refl = step (ξ-blame {F = M ⊕[ op ]□ vM})
...   | done vN with canonical-ℕ vM hM | canonical-ℕ vN hN
...     | cκℕ m refl | cκℕ n refl with op
...       | addℕ = step (β-δ δ-add)
progress (⊢cast-up {M = M} {p = p} hM hp) with progress hM
... | step sM = step (ξ {F = □at-up p} sM)
... | crash refl = step (ξ-blame {F = □at-up p})
... | done vM = cast-up-progress vM hM hp
progress (⊢cast-down {M = M} {p = p} hM hp) with progress hM
... | step sM = step (ξ {F = □at-down p} sM)
... | crash refl = step (ξ-blame {F = □at-down p})
... | done vM = cast-down-progress vM hM hp
progress (⊢blame hA) = crash refl

module strong-rep-nu.notes.PeelPremise where

-- THE ARGUMENT FOR THE `Peel` PREMISE, now used by Progress.
--
-- The proof formerly lived in this notes module.  Its reusable pieces have
-- moved into the core:
--
--   * strong-rep-nu.Boundary §3b proves (Q): the conversion contexts on the
-- two
--     sides of a crossing name the same representation variables;
--   * strong-rep-nu.Boundary §3c constructs the dual's conversion context;
--   * strong-rep-nu.Conversion §2c weakens a well-typed conversion and
-- exports
--     `peel-premises` / `peel-premises-boundary`.
--
-- This note retains the concrete mixed-frame witness that motivated (Q) and
-- checks that the moved package constructs exactly the premise `Peel` needs.

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types using (`ℕ; `𝔹)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.TypeCheck

------------------------------------------------------------------------
-- 1. The mixed frame where list equality fails
------------------------------------------------------------------------

reps₃ : RepCtx
reps₃ = bindR `ℕ ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []

Δ₃ : Ctxᵗ
Δ₃ = reps₃ ∣ (0 ∷ 1 ∷ [])

Mixed : Boundary
Mixed = (bind 0 2 ∷ unbind 0 0 ∷ [])

nmI nmC : Ctxᵗ → Boundary → Maybe TyCtx
nmI Γ Θ with interior? Γ Θ
nmI Γ Θ | just (Γᵢ , _) = just (names Γᵢ)
nmI Γ Θ | nothing = nothing
nmC Γ Θ with conversion? Γ Θ
nmC Γ Θ | just (Γᶜ , _) = just (names Γᶜ)
nmC Γ Θ | nothing = nothing

Γᵢ Γᶜ Γᵈ : Ctxᵗ
Γᵢ = reps₃ ∣ (2 ∷ 1 ∷ [])
Γᶜ = reps₃ ∣ (2 ∷ 0 ∷ 1 ∷ [])
Γᵈ = reps₃ ∣ (0 ∷ 2 ∷ 1 ∷ [])

is-Γᵢ : nmI Δ₃ Mixed ≡ just (names Γᵢ)
is-Γᵢ = refl

-- The source spelling is read here.
is-Γᶜ : nmC Δ₃ Mixed ≡ just (names Γᶜ)
is-Γᶜ = refl

-- The dual spelling is used here.  The map is a permutation of Γᶜ's map,
-- not the same list.
is-Γᵈ : nmC Γᵢ (dual Mixed) ≡ just (names Γᵈ)
is-Γᵈ = refl

weakened : SameConv Γᵈ (unseal 1) Γᶜ (unseal 0)
weakened = unseal 2 , sameᶜ-unseal (there here) , sameᶜ-unseal here

------------------------------------------------------------------------
-- 2. The moved core package, exercised on the same frame
------------------------------------------------------------------------

mixed-interior : Δ₃ ⊢ⁱ Mixed ⇒ Γᵢ
mixed-interior = proj₂ (int! Δ₃ Mixed)

mixed-conversion : Δ₃ ⊢ᶜ Mixed ⇒ Γᶜ
mixed-conversion = proj₂ (conv! Δ₃ Mixed)

mixed-dual-conversion : Γᵢ ⊢ᶜ dual Mixed ⇒ Γᵈ
mixed-dual-conversion = proj₂ (conv! Γᵢ (dual Mixed))

-- (Q) transports the representation named by source position zero to the
-- dual's position one.
mixed-Q : (names Γᵈ) ∋ᵅ 2
mixed-Q = Q mixed-interior mixed-conversion mixed-dual-conversion
            (0 , here)

-- The conversion weakening theorem consumes the same readings and returns
-- the premise carried by `Peel`.
mixed-premise : ∃[ s′ ] SameConv Γᵈ s′ Γᶜ (unseal 0)
mixed-premise = premise-exists mixed-interior mixed-conversion
                               mixed-dual-conversion
                               (proj₂ (proj₂ (cv! Γᶜ (unseal 0))))

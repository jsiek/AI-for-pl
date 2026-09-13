module strong.notes.probes.V7CancelDriftProbe where

-- PROBE (2026-09-13): under the spine-only conversion rules,
-- `preserve-step` for `_—→ᶜ_` is FALSE at the cancellation case.
--
-- The spine-only rules let a `seal α ; unseal α` pair's two FLANKS
-- drift: the visibility of anchors the pair's types never mention may
-- differ between the context where the seal starts and the context
-- where the unseal ends.  The pair's two read-backs of α's
-- representation then disagree in their variable NAMES.  While the pair
-- stands, the disagreement is honest — each read-back is stated at its
-- own flank.  When `fuse` cancels the pair, the following head inherits
-- the near flank's read-back as its source — and if that head is a `↦`,
-- its source domain is pinned by its component's terminator SYNTAX,
-- which spells the far flank's name.  No rule bridges there.
--
-- Three anchors, newest first: γ ≔ ℕ (an innocent bystander),
-- α ≔ β→β (the sealed anchor, whose representation NAMES β), β ≔ ℕ.
-- The seal's flank Δ₁ has γ revealed, so β's name there is ` 2; the
-- unseal's flank Δ₃ has γ concealed, so β's name there is ` 1.
--
--   c  =  seal α ∷ unseal α ∷ (id(`1) ↦ id(`1)) ∷ id(`1 ⇒ `1)
--
-- types as  Δ₁ ⊢ c ∶ (`2 ⇒ `2) ⇝ (`1 ⇒ `1) ⊣ Δ₃  (`conv-typed`), and
-- one ξ-pair step cancels the pair (`conv-steps`), but the residue has
-- no derivation at those endpoints (`residue-untyped`): `conv-fun`
-- forces its source domain to be the ↦ component's target, ` 1, and the
-- required source says ` 2.
--
-- The drift is exactly what `Merge` composites contain (the class-2
-- configuration of V7MergeScopeRepairedProbe), so this cannot be
-- dismissed as unreachable.

open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction

-- α's representation, as stored beneath its entry: β is the next entry
-- down, so it is anchor zero from there.
Rα : RepTy
Rα = `α zero ⇒ᴿ `α zero

-- Newest first: γ, then α, then β.
Δ₁ : Ctxᵗ
Δ₁ = anch revealed (bindA `ℕᴿ)
   ∷ anch revealed (bindA Rα)
   ∷ anch revealed (bindA `ℕᴿ) ∷ []

Δ₃ : Ctxᵗ
Δ₃ = anch concealed (bindA `ℕᴿ)
   ∷ anch revealed (bindA Rα)
   ∷ anch revealed (bindA `ℕᴿ) ∷ []

-- β's name: ` 2 where γ is revealed, ` 1 where γ is concealed.
β₁ : Δ₁ ∋n 2 := 2
β₁ = n-revealed (n-revealed n-here)

β₃ : Δ₃ ∋n 1 := 2
β₃ = n-concealed (n-revealed n-here)

-- α, at index 1, named ` 1 on the seal's revealed flank.
α₁ : Δ₁ ∋n 1 := 1
α₁ = n-revealed n-here

αr₁ : Δ₁ ∋r 1 := (`α 2 ⇒ᴿ `α 2)
αr₁ = r-there r-here

αr₃ : Δ₃ ∋r 1 := (`α 2 ⇒ᴿ `α 2)
αr₃ = r-there r-here

c : Conv
c = seal 1 ∷ᶜ unseal 1
      ∷ᶜ (id (` 1) ↦ id (` 1)) ∷ᶜ id (` 1 ⇒ ` 1)

residue : Conv
residue = (id (` 1) ↦ id (` 1)) ∷ᶜ id (` 1 ⇒ ` 1)

-- The whole conversion is well-typed: each read-back is stated at its
-- own flank, and the drifted γ bit is exactly what `SameBindings`
-- permits.
conv-typed : Δ₁ ⊢ c ∶ (` 2 ⇒ ` 2) ⇝ (` 1 ⇒ ` 1) ⊣ Δ₃
conv-typed =
  conv-cons
    (conv-seal α₁ αr₁ (read-⇒ (read-var β₁) (read-var β₁)) sb-refl)
    (tail-cons
      (conv-unseal α₁ αr₁ (read-⇒ (read-var β₃) (read-var β₃))
        (sb-∷ sb-refl))
      (tail-cons
        (conv-fun
          (conv-id (same-free β₃ β₃ (same-anchor a₂ a₂ refl)) sb-refl)
          (conv-id (same-free β₃ β₃ (same-anchor a₂ a₂ refl)) sb-refl))
        (tail-id (wf-⇒ (wf-var tvβ) (wf-var tvβ)))))
  where
  a₂ : Δ₃ ∋a 2
  a₂ = a-there (a-there a-here)
  tvβ : Δ₃ ∋tv 1
  tvβ = tv-concealed (tv-revealed tv-here)

-- One step cancels the pair.
conv-steps : c —→ᶜ residue
conv-steps = ξ-pair refl

-- The residue has NO derivation at the same endpoints: `conv-fun` pins
-- the source domain to the component's target, which its terminator
-- spells ` 1, and the source type says ` 2.
residue-untyped : Δ₁ ⊢ residue ∶ (` 2 ⇒ ` 2) ⇝ (` 1 ⇒ ` 1) ⊣ Δ₃ → ⊥
residue-untyped (conv-cons (conv-fun () _) _)

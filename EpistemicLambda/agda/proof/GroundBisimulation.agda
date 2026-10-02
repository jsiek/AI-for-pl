module proof.GroundBisimulation where

-- File Charter:
--   * Private proofs for Milestone 1 observer bisimulation.
--   * Shows that equal public cell contents remain related after arbitrary
--     matching reads and writes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat
  renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import STLCRef
open import GroundInterface
open import Bisimulation

------------------------------------------------------------------------
-- Store lemmas
------------------------------------------------------------------------

nothing≢just : ∀ {A : Set}{x : A} -> nothing ≡ just x -> ⊥
nothing≢just ()

update-from-lookup : ∀ {μ l V W}
  -> lookupStore μ l ≡ just V
  -> Σ Store (λ μ′ -> updateStore μ l W ≡ just μ′)
update-from-lookup {μ = []} ()
update-from-lookup {μ = V ∷ μ} {l = zeroℕ} {W = W} eq = W ∷ μ , refl
update-from-lookup {μ = V ∷ μ} {l = sucℕ l} {W = W} eq
  with update-from-lookup {μ = μ} {l = l} {W = W} eq
update-from-lookup {μ = V ∷ μ} {l = sucℕ l} {W = W} eq
  | μ′ , update rewrite update = V ∷ μ′ , refl

lookup-after-update : ∀ {μ μ′ l V}
  -> updateStore μ l V ≡ just μ′
  -> lookupStore μ′ l ≡ just V
lookup-after-update {μ = []} ()
lookup-after-update {μ = W ∷ μ} {l = zeroℕ} refl = refl
lookup-after-update {μ = W ∷ μ} {l = sucℕ l} {V = V} update
  with updateStore μ l V in recursive
lookup-after-update {μ = W ∷ μ} {l = sucℕ l} {V = V} update
  | nothing = ⊥-elim (nothing≢just update)
lookup-after-update {μ = W ∷ μ} {l = sucℕ l} {V = V} update
  | just μ′ with update
lookup-after-update {μ = W ∷ μ} {l = sucℕ l} {V = V} update
  | just μ′ | refl =
    lookup-after-update {μ = μ} {μ′ = μ′} {l = l} {V = V} recursive

------------------------------------------------------------------------
-- The canonical ground relation is a bisimulation
------------------------------------------------------------------------

forth-ground : ∀ {P Q a P′}
  -> GroundRelated P Q
  -> P —[ a ]→ᵒ P′
  -> ∃[ Q′ ] (Q —[ a ]→ᵒ Q′) × GroundRelated P′ Q′
forth-ground stoppedᵣ ()
forth-ground divergingᵣ ()
forth-ground natᵣ expose-nat = stopped , expose-nat , stoppedᵣ
forth-ground unitᵣ expose-unit = stopped , expose-unit , stoppedᵣ
forth-ground (exposed-refᵣ {k = k} {ν = ν} cells) expose-ref =
  public-ref k ν , expose-ref , public-refᵣ cells
forth-ground (public-refᵣ {k = k} {ν = ν} cells)
             (read-ref lookup-left) =
  public-ref k ν ,
  read-ref (trans (sym (contents-agree cells)) lookup-left) ,
  public-refᵣ cells
forth-ground (public-refᵣ {l = l} {k = k} {μ = μ} {ν = ν} cells)
             (write-ref {μ′ = μ′} {n = n} update-left)
  with left-natural cells
forth-ground (public-refᵣ {l = l} {k = k} {μ = μ} {ν = ν} cells)
             (write-ref {μ′ = μ′} {n = n} update-left)
  | old , lookup-left
  with update-from-lookup
         {μ = ν} {l = k} {W = numeral n}
         (trans (sym (contents-agree cells)) lookup-left)
forth-ground (public-refᵣ {l = l} {k = k} {μ = μ} {ν = ν} cells)
             (write-ref {μ′ = μ′} {n = n} update-left)
  | old , lookup-left | ν′ , update-right =
  public-ref k ν′ ,
  write-ref update-right ,
  public-refᵣ
    (relate-key
      (trans (lookup-after-update
                {μ = μ} {μ′ = μ′} {l = l} {V = numeral n} update-left)
             (sym (lookup-after-update
                {μ = ν} {μ′ = ν′} {l = k} {V = numeral n}
                update-right)))
      (n , lookup-after-update
             {μ = μ} {μ′ = μ′} {l = l} {V = numeral n} update-left))

back-ground : ∀ {P Q a Q′}
  -> GroundRelated P Q
  -> Q —[ a ]→ᵒ Q′
  -> ∃[ P′ ] (P —[ a ]→ᵒ P′) × GroundRelated P′ Q′
back-ground stoppedᵣ ()
back-ground divergingᵣ ()
back-ground natᵣ expose-nat = stopped , expose-nat , stoppedᵣ
back-ground unitᵣ expose-unit = stopped , expose-unit , stoppedᵣ
back-ground (exposed-refᵣ {l = l} {μ = μ} cells) expose-ref =
  public-ref l μ , expose-ref , public-refᵣ cells
back-ground (public-refᵣ {l = l} {μ = μ} cells)
            (read-ref lookup-right) =
  public-ref l μ ,
  read-ref (trans (contents-agree cells) lookup-right) ,
  public-refᵣ cells
back-ground (public-refᵣ {l = l} {k = k} {μ = μ} {ν = ν} cells)
            (write-ref {μ′ = ν′} {n = n} update-right)
  with left-natural cells
back-ground (public-refᵣ {l = l} {k = k} {μ = μ} {ν = ν} cells)
            (write-ref {μ′ = ν′} {n = n} update-right)
  | old , lookup-left
  with update-from-lookup
         {μ = μ} {l = l} {W = numeral n}
         lookup-left
back-ground (public-refᵣ {l = l} {k = k} {μ = μ} {ν = ν} cells)
            (write-ref {μ′ = ν′} {n = n} update-right)
  | old , lookup-left | μ′ , update-left =
  public-ref l μ′ ,
  write-ref update-left ,
  public-refᵣ
    (relate-key
      (trans (lookup-after-update
                {μ = μ} {μ′ = μ′} {l = l} {V = numeral n} update-left)
             (sym (lookup-after-update
                {μ = ν} {μ′ = ν′} {l = k} {V = numeral n}
                update-right)))
      (n , lookup-after-update
             {μ = μ} {μ′ = μ′} {l = l} {V = numeral n} update-left))

ground-related-is-bisimulation : IsBisimulation GroundRelated
ground-related-is-bisimulation = record
  { forth = forth-ground
  ; back = back-ground
  }

ground-related-bisimilar : ∀ {P Q} -> GroundRelated P Q -> P ≈ Q
ground-related-bisimilar related = record
  { Relation = GroundRelated
  ; is-bisimulation = ground-related-is-bisimulation
  ; related = related
  }

unit-heaps-bisimilar : ∀ {μ ν}
  -> exposed unit-result μ ≈ exposed unit-result ν
unit-heaps-bisimilar = ground-related-bisimilar unitᵣ

renamed-reference-bisimilar : ∀ {l k μ ν}
  -> KeyCorrespondence μ l ν k
  -> exposed (ref-result l) μ ≈ exposed (ref-result k) ν
renamed-reference-bisimilar cells =
  ground-related-bisimilar (exposed-refᵣ cells)

public-reference-bisimilar : ∀ {l k μ ν}
  -> KeyCorrespondence μ l ν k
  -> public-ref l μ ≈ public-ref k ν
public-reference-bisimilar cells =
  ground-related-bisimilar (public-refᵣ cells)

------------------------------------------------------------------------
-- Public observations distinguish naturals and divergence
------------------------------------------------------------------------

nat-observation-injective : ∀ {m n μ ν}
  -> exposed (nat-result m) μ ≈ exposed (nat-result n) ν
  -> m ≡ n
nat-observation-injective bisim
  with IsBisimulation.forth (_≈_.is-bisimulation bisim)
         (_≈_.related bisim) expose-nat
... | stopped , expose-nat , related = refl

unit-not-bisimilar-diverging : ∀ {μ}
  -> exposed unit-result μ ≈ diverging
  -> ⊥
unit-not-bisimilar-diverging bisim
  with IsBisimulation.forth (_≈_.is-bisimulation bisim)
         (_≈_.related bisim) expose-unit
... | Q′ , () , related

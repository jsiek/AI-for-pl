{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.SimBackContextualCatchupProbe where

-- File Charter:
--   * Pins a trusted β-inst reduction when it is placed on the source side of
--     a backward catch-up square.
--   * Constructs the matching aligned left-only world evolution against an
--     already allocated target dynamic cell.
--   * Records no production interface and changes neither CTI nor SimBack.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (★)
open import TyStore using (store-empty; store-bind; Z∋)
open import Conversion using (〖_,_↑_〗; _⊢↑[_⦂_]_)
open import CastTerms using (⟨_,_,_⟩; _,ˢ_)
open import Reduction using (bind; _—→[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing)
import TrustedLambdaCatchupProbe as TLC
import Imprecision as I
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (evolution-bind-left-aligned)
open import proof.DGG.WorldEvolutionSequence using
  (MultiWorldEvolution; evolutions-refl; evolutions-step-left)


-- The declarations imported from TrustedLambdaCatchupProbe use `target` in
-- their historical names.  Reduction syntax itself is unoriented; below that
-- same explicitly constructed β-inst step occupies the source/left endpoint.

source-β-inst-start-world :
  ⟨ 0 , store-empty , [] ⟩ ⊑ᶜ
    (⟨ 0 , store-empty , [] ⟩ ,ˢ ★)
source-β-inst-start-world =
  bindRightᶜ emptyᶜ ★ (inj₁ refl)

source-β-inst-allocation-world :
  (⟨ 0 , store-empty , [] ⟩ ,ˢ ★) ⊑ᶜ
    (⟨ 0 , store-empty , [] ⟩ ,ˢ ★)
source-β-inst-allocation-world =
  bindLeftᶜ source-β-inst-start-world ★

source-β-inst-update :
  PivotUpdateᵗ
    (ηᴸᶜ source-β-inst-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ source-β-inst-allocation-world) Fin.zero)
source-β-inst-update =
  repointⁱ (ηᴸᶜ source-β-inst-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ source-β-inst-allocation-world) Fin.zero)
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

source-β-inst-reveal⊢ :
  store-bind store-empty ★
    ⊢↑[ Fin.zero ⦂ ★ ]
      〖 Fin.zero , ★ ↑ TLC.target-body 〗
source-β-inst-reveal⊢ =
  structural-reveal-typing TLC.target-body (Z∋ refl)

target-β-inst-reveal⊢ :
  store-bind store-empty ★
    ⊢↑[ Fin.zero ⦂ ★ ]
      〖 Fin.zero , ★ ↑ TLC.target-body 〗
target-β-inst-reveal⊢ =
  structural-reveal-typing TLC.target-body (Z∋ refl)

source-β-inst-boundary :
  AlignmentBoundaryᶜ source-β-inst-allocation-world Fin.zero Fin.zero
    source-β-inst-update
source-β-inst-boundary =
  paired-reveal-alignmentᶜ
    source-β-inst-reveal⊢ target-β-inst-reveal⊢ refl I.★⊑★

source-β-inst-aligned-world :
  (⟨ 0 , store-empty , [] ⟩ ,ˢ ★) ⊑ᶜ
    (⟨ 0 , store-empty , [] ⟩ ,ˢ ★)
source-β-inst-aligned-world =
  rebaseSourceᶜ source-β-inst-allocation-world Fin.zero Fin.zero
    source-β-inst-update
    (alignment-onlyᶜ source-β-inst-boundary)
    (I.X⊑★ refl)

source-β-inst-no-open-before :
  openFramesᶜ source-β-inst-start-world ≡ []
source-β-inst-no-open-before = refl

source-β-inst-no-open-after :
  openFramesᶜ source-β-inst-aligned-world ≡ []
source-β-inst-no-open-after = refl

source-β-inst-aligned-evolution :
  MultiWorldEvolution
    {W = source-β-inst-start-world}
    {W′ = source-β-inst-aligned-world}
    (bind ★ ∷ˢ []ˢ) []ˢ
source-β-inst-aligned-evolution =
  evolutions-step-left refl
    (evolution-bind-left-aligned refl source-β-inst-update
      source-β-inst-boundary (I.X⊑★ refl))
    evolutions-refl


source-β-inst-aligned-path :
  (TLC.target-inst-redex —→[ bind ★ ] TLC.target-after-inst)
  × MultiWorldEvolution
      {W = source-β-inst-start-world}
      {W′ = source-β-inst-aligned-world}
      (bind ★ ∷ˢ []ˢ) []ˢ
source-β-inst-aligned-path =
  TLC.target-inst-step , source-β-inst-aligned-evolution

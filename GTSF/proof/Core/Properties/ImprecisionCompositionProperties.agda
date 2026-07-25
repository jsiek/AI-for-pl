module proof.Core.Properties.ImprecisionCompositionProperties where

-- File Charter:
--   * Connects indexed type-imprecision composition to its hereditary shape.
--   * Proves that the canonical composed derivation realizes the direct
--     Unicode composition judgment.
--   * Proves result uniqueness and associativity of shape composition.
--   * Contains no term relation, cast typing, store invariant, or simulation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; id★ˢ
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; comp-id★
  ; comp-idˣ-idˣ
  ; comp-idˣ-tagˣ
  ; comp-idι-idι
  ; comp-idι-tag
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-tag-id★
  ; comp-tag-⇛-id★
  ; comp-tagˣ-id★
  ; comp-ν
  ; _；_≋_
  )
open import ImprecisionWf using
  ( id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
open import Imprecision using (idᵢ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ComposeCtxᵢ
  ; compose-idᵢ
  ; compose-id-leftᵢ
  ; compose-∀∀ᵢ
  ; compose-∀νᵢ
  ; compose-νidᵢ
  ; ⊑-trans-composeᵢ
  ; ⊑-trans-idᵢ
  ; ⊑-trans-left-idᵢ
  )
open import Types using (★)


compose-result-unique :
  ∀ {p q r r′} →
  p ； q ≋ r →
  p ； q ≋ r′ →
  r ≡ r′
compose-result-unique comp-id★ comp-id★ = refl
compose-result-unique comp-idˣ-idˣ comp-idˣ-idˣ = refl
compose-result-unique comp-idˣ-tagˣ comp-idˣ-tagˣ = refl
compose-result-unique comp-idι-idι comp-idι-idι = refl
compose-result-unique comp-idι-tag comp-idι-tag = refl
compose-result-unique
    (comp-↦-↦ comp₁ comp₂)
    (comp-↦-↦ comp₁′ comp₂′) =
  cong₂ _↦ˢ_
    (compose-result-unique comp₁ comp₁′)
    (compose-result-unique comp₂ comp₂′)
compose-result-unique
    (comp-↦-tag comp₁ comp₂)
    (comp-↦-tag comp₁′ comp₂′) =
  cong₂ tag_⇛ˢ_
    (compose-result-unique comp₁ comp₁′)
    (compose-result-unique comp₂ comp₂′)
compose-result-unique
    (comp-∀-∀ comp)
    (comp-∀-∀ comp′) =
  cong ∀ˢ_ (compose-result-unique comp comp′)
compose-result-unique
    (comp-∀-ν comp)
    (comp-∀-ν comp′) =
  cong νˢ_ (compose-result-unique comp comp′)
compose-result-unique comp-tag-id★ comp-tag-id★ = refl
compose-result-unique
    (comp-tag-⇛-id★ comp₁ comp₂)
    (comp-tag-⇛-id★ comp₁′ comp₂′) =
  cong₂ tag_⇛ˢ_
    (compose-result-unique comp₁ comp₁′)
    (compose-result-unique comp₂ comp₂′)
compose-result-unique comp-tagˣ-id★ comp-tagˣ-id★ = refl
compose-result-unique
    (comp-ν comp)
    (comp-ν comp′) =
  cong νˢ_ (compose-result-unique comp comp′)


compose-assoc-right :
  ∀ {p q r u v w} →
  p ； q ≋ u →
  u ； r ≋ v →
  q ； r ≋ w →
  p ； w ≋ v
compose-assoc-right comp-id★ comp-id★ comp-id★ =
  comp-id★
compose-assoc-right
    comp-idˣ-idˣ comp-idˣ-idˣ comp-idˣ-idˣ =
  comp-idˣ-idˣ
compose-assoc-right
    comp-idˣ-idˣ comp-idˣ-tagˣ comp-idˣ-tagˣ =
  comp-idˣ-tagˣ
compose-assoc-right
    comp-idˣ-tagˣ comp-tagˣ-id★ comp-tagˣ-id★ =
  comp-idˣ-tagˣ
compose-assoc-right comp-idι-idι comp-idι-idι comp-idι-idι =
  comp-idι-idι
compose-assoc-right comp-idι-idι comp-idι-tag comp-idι-tag =
  comp-idι-tag
compose-assoc-right comp-idι-tag comp-tag-id★ comp-tag-id★ =
  comp-idι-tag
compose-assoc-right
    (comp-↦-↦ pq₁ pq₂)
    (comp-↦-↦ ur₁ ur₂)
    (comp-↦-↦ qr₁ qr₂) =
  comp-↦-↦
    (compose-assoc-right pq₁ ur₁ qr₁)
    (compose-assoc-right pq₂ ur₂ qr₂)
compose-assoc-right
    (comp-↦-↦ pq₁ pq₂)
    (comp-↦-tag ur₁ ur₂)
    (comp-↦-tag qr₁ qr₂) =
  comp-↦-tag
    (compose-assoc-right pq₁ ur₁ qr₁)
    (compose-assoc-right pq₂ ur₂ qr₂)
compose-assoc-right
    (comp-↦-tag pq₁ pq₂)
    (comp-tag-⇛-id★ ur₁ ur₂)
    (comp-tag-⇛-id★ qr₁ qr₂) =
  comp-↦-tag
    (compose-assoc-right pq₁ ur₁ qr₁)
    (compose-assoc-right pq₂ ur₂ qr₂)
compose-assoc-right
    (comp-∀-∀ pq)
    (comp-∀-∀ ur)
    (comp-∀-∀ qr) =
  comp-∀-∀ (compose-assoc-right pq ur qr)
compose-assoc-right
    (comp-∀-∀ pq)
    (comp-∀-ν ur)
    (comp-∀-ν qr) =
  comp-∀-ν (compose-assoc-right pq ur qr)
compose-assoc-right
    (comp-∀-ν pq)
    (comp-ν ur)
    (comp-ν qr) =
  comp-∀-ν (compose-assoc-right pq ur qr)
compose-assoc-right comp-tag-id★ comp-tag-id★ comp-id★ =
  comp-tag-id★
compose-assoc-right
    (comp-tag-⇛-id★ pq₁ pq₂)
    (comp-tag-⇛-id★ ur₁ ur₂)
    comp-id★ =
  comp-tag-⇛-id★
    (compose-assoc-right pq₁ ur₁ comp-id★)
    (compose-assoc-right pq₂ ur₂ comp-id★)
compose-assoc-right comp-tagˣ-id★ comp-tagˣ-id★ comp-id★ =
  comp-tagˣ-id★
compose-assoc-right
    (comp-ν pq)
    (comp-ν ur)
    qr =
  comp-ν (compose-assoc-right pq ur qr)


compose-assoc-left :
  ∀ {p q r u v w} →
  p ； q ≋ u →
  q ； r ≋ w →
  p ； w ≋ v →
  u ； r ≋ v
compose-assoc-left comp-id★ comp-id★ comp-id★ =
  comp-id★
compose-assoc-left
    comp-idˣ-idˣ comp-idˣ-idˣ comp-idˣ-idˣ =
  comp-idˣ-idˣ
compose-assoc-left
    comp-idˣ-idˣ comp-idˣ-tagˣ comp-idˣ-tagˣ =
  comp-idˣ-tagˣ
compose-assoc-left
    comp-idˣ-tagˣ comp-tagˣ-id★ comp-idˣ-tagˣ =
  comp-tagˣ-id★
compose-assoc-left comp-idι-idι comp-idι-idι comp-idι-idι =
  comp-idι-idι
compose-assoc-left comp-idι-idι comp-idι-tag comp-idι-tag =
  comp-idι-tag
compose-assoc-left comp-idι-tag comp-tag-id★ comp-idι-tag =
  comp-tag-id★
compose-assoc-left
    (comp-↦-↦ pq₁ pq₂)
    (comp-↦-↦ qr₁ qr₂)
    (comp-↦-↦ pw₁ pw₂) =
  comp-↦-↦
    (compose-assoc-left pq₁ qr₁ pw₁)
    (compose-assoc-left pq₂ qr₂ pw₂)
compose-assoc-left
    (comp-↦-↦ pq₁ pq₂)
    (comp-↦-tag qr₁ qr₂)
    (comp-↦-tag pw₁ pw₂) =
  comp-↦-tag
    (compose-assoc-left pq₁ qr₁ pw₁)
    (compose-assoc-left pq₂ qr₂ pw₂)
compose-assoc-left
    (comp-↦-tag pq₁ pq₂)
    (comp-tag-⇛-id★ qr₁ qr₂)
    (comp-↦-tag pw₁ pw₂) =
  comp-tag-⇛-id★
    (compose-assoc-left pq₁ qr₁ pw₁)
    (compose-assoc-left pq₂ qr₂ pw₂)
compose-assoc-left
    (comp-∀-∀ pq)
    (comp-∀-∀ qr)
    (comp-∀-∀ pw) =
  comp-∀-∀ (compose-assoc-left pq qr pw)
compose-assoc-left
    (comp-∀-∀ pq)
    (comp-∀-ν qr)
    (comp-∀-ν pw) =
  comp-∀-ν (compose-assoc-left pq qr pw)
compose-assoc-left
    (comp-∀-ν pq)
    (comp-ν qr)
    (comp-∀-ν pw) =
  comp-ν (compose-assoc-left pq qr pw)
compose-assoc-left comp-tag-id★ comp-id★ comp-tag-id★ =
  comp-tag-id★
compose-assoc-left
    (comp-tag-⇛-id★ pq₁ pq₂)
    comp-id★
    (comp-tag-⇛-id★ pw₁ pw₂) =
  comp-tag-⇛-id★
    (compose-assoc-left pq₁ comp-id★ pw₁)
    (compose-assoc-left pq₂ comp-id★ pw₂)
compose-assoc-left comp-tagˣ-id★ comp-id★ comp-tagˣ-id★ =
  comp-tagˣ-id★
compose-assoc-left
    (comp-ν pq)
    qr
    (comp-ν pw) =
  comp-ν (compose-assoc-left pq qr pw)


shape-trans-composeᵢ :
  ∀ {ρ Δᴸ Δᴹ Δᴿ Φᴸ Φᴿ Φᴼ A B C}
    (ctx : ComposeCtxᵢ ρ Δᴸ Φᴸ Φᴿ Φᴼ)
    (p : Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ)
    (q : Φᴿ ∣ Δᴹ ⊢ B ⊑ C ⊣ Δᴿ) →
  ⌊ p ⌋ ； ⌊ q ⌋ ≋ ⌊ ⊑-trans-composeᵢ ctx p q ⌋
shape-trans-composeᵢ ctx id★ id★ =
  comp-id★
shape-trans-composeᵢ ctx
    (idˣ x∈ X<Δᴸ Y<Δᴹ) (idˣ y∈ Y<Δᴹ′ Z<Δᴿ) =
  comp-idˣ-idˣ
shape-trans-composeᵢ ctx
    (idˣ x∈ X<Δᴸ Y<Δᴹ) (tagˣ y★∈ Y<Δᴹ′) =
  comp-idˣ-tagˣ
shape-trans-composeᵢ ctx idι idι =
  comp-idι-idι
shape-trans-composeᵢ ctx idι (tag ι) =
  comp-idι-tag
shape-trans-composeᵢ ctx (p₁ ↦ p₂) (q₁ ↦ q₂) =
  comp-↦-↦
    (shape-trans-composeᵢ ctx p₁ q₁)
    (shape-trans-composeᵢ ctx p₂ q₂)
shape-trans-composeᵢ ctx (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  comp-↦-tag
    (shape-trans-composeᵢ ctx p₁ q₁)
    (shape-trans-composeᵢ ctx p₂ q₂)
shape-trans-composeᵢ ctx (∀ⁱ p) (∀ⁱ q) =
  comp-∀-∀
    (shape-trans-composeᵢ (compose-∀∀ᵢ ctx) p q)
shape-trans-composeᵢ ctx (∀ⁱ p) (ν safe occ q) =
  comp-∀-ν
    (shape-trans-composeᵢ (compose-∀νᵢ ctx) p q)
shape-trans-composeᵢ ctx (tag ι) id★ =
  comp-tag-id★
shape-trans-composeᵢ ctx (tag p ⇛ q) id★ =
  comp-tag-⇛-id★
    (shape-trans-composeᵢ ctx p id★)
    (shape-trans-composeᵢ ctx q id★)
shape-trans-composeᵢ ctx (tagˣ x★∈ X<Δᴸ) id★ =
  comp-tagˣ-id★
shape-trans-composeᵢ ctx (ν safe occ p) q =
  comp-ν
    (shape-trans-composeᵢ (compose-νidᵢ ctx) p q)


shape-trans-idᵢ :
  ∀ {Δ A B C}
    (p : idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ)
    (q : idᵢ Δ ∣ Δ ⊢ B ⊑ C ⊣ Δ) →
  ⌊ p ⌋ ； ⌊ q ⌋ ≋ ⌊ ⊑-trans-idᵢ p q ⌋
shape-trans-idᵢ {Δ = Δ} p q =
  shape-trans-composeᵢ (compose-idᵢ Δ) p q


shape-trans-left-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B C}
    (p : idᵢ Δᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴸ)
    (q : Φ ∣ Δᴸ ⊢ B ⊑ C ⊣ Δᴿ) →
  ⌊ p ⌋ ； ⌊ q ⌋ ≋ ⌊ ⊑-trans-left-idᵢ p q ⌋
shape-trans-left-idᵢ {Φ = Φ} {Δᴸ = Δᴸ} p q =
  shape-trans-composeᵢ (compose-id-leftᵢ Δᴸ Φ) p q


compose-target-star-right-id★ :
  ∀ {Φ Δᴸ Δᴿ A}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  ⌊ p ⌋ ； id★ˢ ≋ ⌊ p ⌋
compose-target-star-right-id★ id★ =
  comp-id★
compose-target-star-right-id★ (tag ι) =
  comp-tag-id★
compose-target-star-right-id★ (tag p ⇛ q) =
  comp-tag-⇛-id★
    (compose-target-star-right-id★ p)
    (compose-target-star-right-id★ q)
compose-target-star-right-id★ (tagˣ x★∈ X<Δᴸ) =
  comp-tagˣ-id★
compose-target-star-right-id★ (ν safe occ p) =
  comp-ν (compose-target-star-right-id★ p)

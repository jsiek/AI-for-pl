{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxDirectCTITypingProbe where

-- File Charter:
--   * Proves source and target endpoint typing for every constructor of the
--     direct/no-alias-boundary two-Ctx cast-term-imprecision probe.
--   * Checks the initial, source-fresh-behind, generator-indexed, and
--     pivot-position-gated conversion surfaces while retaining canonical
--     type-proof indices.
--   * Leaves exact target alias chains to the separate scoped-boundary probe.

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Types using (Ty)
open import CastTerms using
  (Ctx; Δᵉ; Term; _⊢_⦂_; ⊢`; ⊢ƛ; ⊢·; ⊢$; ⊢⊕; ⊢⟨⟩;
   ⊢blame; ⊢Λ; ⊢•; ⊢reveal; ⊢conceal)
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)
import proof.DGG.notes.probes.TwoCtxDirectCTIProbe as Direct

direct-cti-endpoint-typingᴰ : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {M : Term (Δᵉ Cᴸ)} {M′ : Term (Δᵉ Cᴿ)}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    {p : A ⊑ᵀ⟨ W ⟩ B}
  → W Direct.⊢ᴰ M ⊑ M′ ∶ p
  → (Cᴸ ⊢ M ⦂ A) × (Cᴿ ⊢ M′ ⦂ B)
direct-cti-endpoint-typingᴰ (Direct.var⊑varᴰ x x′) =
  ⊢` x , ⊢` x′
direct-cti-endpoint-typingᴰ (Direct.lambda⊑lambdaᴰ relation) =
  ⊢ƛ (proj₁ endpoints) , ⊢ƛ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ (Direct.app⊑appᴰ fun-rel arg-rel) =
  ⊢· (proj₁ fun-endpoints) (proj₁ arg-endpoints) ,
  ⊢· (proj₂ fun-endpoints) (proj₂ arg-endpoints)
  where
  fun-endpoints = direct-cti-endpoint-typingᴰ fun-rel
  arg-endpoints = direct-cti-endpoint-typingᴰ arg-rel
direct-cti-endpoint-typingᴰ (Direct.all⊑allᴰ v v′ relation p) =
  ⊢Λ v (proj₁ endpoints) , ⊢Λ v′ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.all⊑ᴰ nonvar occurs plan v target⊢ relation p) =
  ⊢Λ v (proj₁ endpoints) , target⊢
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.type-app⊑type-appᴰ p relation q r) =
  ⊢• (proj₁ endpoints) , ⊢• (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ (Direct.type-app⊑ᴰ p relation q r) =
  ⊢• (proj₁ endpoints) , proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ (Direct.constant⊑constantᴰ kappa p) =
  ⊢$ kappa , ⊢$ kappa
direct-cti-endpoint-typingᴰ
    (Direct.primitive⊑primitiveᴰ op left-rel right-rel p) =
  ⊢⊕ op (proj₁ left-endpoints) (proj₁ right-endpoints) ,
  ⊢⊕ op (proj₂ left-endpoints) (proj₂ right-endpoints)
  where
  left-endpoints = direct-cti-endpoint-typingᴰ left-rel
  right-endpoints = direct-cti-endpoint-typingᴰ right-rel
direct-cti-endpoint-typingᴰ (Direct.blame⊑ᴰ target⊢ p) =
  ⊢blame , target⊢
direct-cti-endpoint-typingᴰ (Direct.cast⊑castᴰ c c′ relation p) =
  ⊢⟨⟩ (proj₁ endpoints) c , ⊢⟨⟩ (proj₂ endpoints) c′
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ (Direct.cast⊑ᴰ c relation p) =
  ⊢⟨⟩ (proj₁ endpoints) c , proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ (Direct.⊑castᴰ c′ relation p) =
  proj₁ endpoints , ⊢⟨⟩ (proj₂ endpoints) c′
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.target-revealᴰ
      (Direct.target-reveal-absent c⊢ absent) relation p) =
  proj₁ endpoints ,
  ⊢reveal c⊢ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.target-revealᴰ
      (Direct.target-reveal-only disaligned c⊢ present) relation p) =
  proj₁ endpoints ,
  ⊢reveal c⊢ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.target-concealᴰ
      (Direct.target-conceal-absent c⊢ absent) relation p) =
  proj₁ endpoints ,
  ⊢conceal c⊢ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.target-concealᴰ
      (Direct.target-conceal-only disaligned c⊢ present) relation p) =
  proj₁ endpoints ,
  ⊢conceal c⊢ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.source-revealᴰ
      (Direct.source-reveal-absent c⊢ absent) relation p) =
  ⊢reveal c⊢ (proj₁ endpoints) ,
  proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.source-revealᴰ
      (Direct.source-reveal-only mark disaligned represented c⊢ present)
      relation p) =
  ⊢reveal c⊢ (proj₁ endpoints) ,
  proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.source-revealᴰ
      (Direct.source-reveal-rebase disaligned plan represented c⊢ present)
      relation p) =
  ⊢reveal c⊢ (proj₁ endpoints) ,
  proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.source-concealᴰ
      (Direct.source-conceal-absent c⊢ absent) relation p) =
  ⊢conceal c⊢ (proj₁ endpoints) ,
  proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.source-concealᴰ
      (Direct.source-conceal-only mark disaligned represented c⊢ present)
      relation p) =
  ⊢conceal c⊢ (proj₁ endpoints) ,
  proj₂ endpoints
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.paired-revealᴰ
      (Direct.paired-reveal-action plan represented c⊢ c′⊢ aligned present)
      relation p) =
  ⊢reveal c⊢ (proj₁ endpoints) ,
  ⊢reveal c′⊢ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation
direct-cti-endpoint-typingᴰ
    (Direct.paired-concealᴰ
      (Direct.paired-conceal-action plan eq represented c⊢ c′⊢ aligned
        present)
      relation p) =
  ⊢conceal c⊢ (proj₁ endpoints) ,
  ⊢conceal c′⊢ (proj₂ endpoints)
  where
  endpoints = direct-cti-endpoint-typingᴰ relation

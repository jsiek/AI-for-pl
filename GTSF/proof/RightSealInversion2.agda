{-# OPTIONS --allow-unsolved-metas #-}

module proof.RightSealInversion2 where

-- File Charter:
--   * Attempts to prove the cambridge25 Right Seal Inversion 2 lemma.
--   * The theorem keeps the composition equation in the conclusion: stripping
--     a right `unseal α A` produces both a witness coercion and evidence that
--     the original index composes with `seal A α`.
--   * The direct `⊒cast+` seal case is immediate.  The remaining holes record
--     the proof obligations that arise from store-shaping and left-cast cases.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.Catchup using
  ( replace-here
  ; compose-leftⁿ-⇑ˢ
  ; compose-leftⁿ-add-left-star-var
  ; extendReplaceRel-compose-left
  ; extendReplaceRel-term
  )
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.NarrowWidenProperties using (StoreDetWf)

RightSealInversion2 : Set₁
RightSealInversion2 =
  ∀ {Δ σ γ M V q A α} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ unseal α A ⟩ ∶ q →
  ∃[ r ]
    (Δ ∣ σ ⊢ q ⨾ⁿ seal A α ≈ r ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r

right-seal-compose-endpoints :
  ∀ {Δ σ q r A B A₀ α} →
  Δ ∣ σ ⊢ q ⨾ⁿ seal A₀ α ≈ r ∶ A ⊒ B →
  Δ ∣ σ ⊢ q ⨾ⁿ seal A₀ α ≈ r ∶ src q ⊒ ＇ α
right-seal-compose-endpoints
    (compose-leftⁿ wfΣ q⊒ seal⊒
      (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒))
    rewrite proj₁ (coercion-src-tgtᵐ (proj₁ q⊒))
          | proj₂ (coercion-src-tgtᵐ (proj₁ seal⊒)) =
  compose-leftⁿ wfΣ q⊒ seal⊒
    (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)

right-seal-compose-ν-lift :
  ∀ {Δ σ p r A α} →
  Δ ∣ σ ⊢ p ⨾ⁿ seal A α ≈ r ∶ src p ⊒ ＇ α →
  suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ
    ⊢ ⇑ᶜ p ⨾ⁿ seal (⇑ᵗ A) (suc α) ≈ ⇑ᶜ r
      ∶ ⇑ᵗ (src p) ⊒ ＇ suc α
right-seal-compose-ν-lift p⨟seal≈r =
  compose-leftⁿ-add-left-star-var zero
    (compose-leftⁿ-⇑ˢ p⨟seal≈r)

rightSealInversion2-ν⊒-right-sealed :
  ∀ {Δ σ γ N W p r A B A₀ α} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ ∣ σ ⊢ p ⨾ⁿ seal A₀ α ≈ r ∶ src p ⊒ ＇ α →
  suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ N ⊒ ⇑ᵗᵐ W ∶ ⇑ᶜ p →
  ∃[ u ]
    (Δ ∣ σ ⊢ p ⨾ⁿ seal A₀ α ≈ u ∶ src p ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ ν ★ N (⇑ᶜ p) ⊒ W ⟨ seal A₀ α ⟩ ∶ u
rightSealInversion2-ν⊒-right-sealed pᶜ p⨟seal≈r N⊒W =
  _ , p⨟seal≈r , ⊒cast- pᶜ p⨟seal≈r (ν⊒ pᶜ N⊒W)

rightSealInversion2-cast+ :
  ∀ {Δ σ γ M M′ V q r s A B C D A₀ α} →
  M′ ⟨ - s ⟩ ≡ V ⟨ unseal α A₀ ⟩ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r →
  ∃[ u ]
    (Δ ∣ σ ⊢ q ⨾ⁿ seal A₀ α ≈ u ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ u
rightSealInversion2-cast+ {s = id A} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = c ︔ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = c ↦ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = `∀ c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (＇ β) !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (‵ ι) !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = ★ !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (A ⇒ B) !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (`∀ A) !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (＇ β) ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (‵ ι) ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = ★ ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (A ⇒ B) ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = (`∀ A) ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = seal A α} refl
    qᶜ q⨟seal≈r M⊒V =
  _ , right-seal-compose-endpoints q⨟seal≈r , M⊒V
rightSealInversion2-cast+ {s = unseal α A} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = gen A c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = inst B c} ()
    qᶜ q⨟s≈r M⊒M′

rightSealInversion2-cast- :
  ∀ {Δ σ γ M M′ V q r s A B C D A₀ α} →
  M′ ⟨ s ⟩ ≡ V ⟨ unseal α A₀ ⟩ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q →
  ∃[ u ]
    (Δ ∣ σ ⊢ r ⨾ⁿ seal A₀ α ≈ u ∶ src r ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ u
rightSealInversion2-cast- {s = id A} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = c ︔ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = c ↦ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = `∀ c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = G !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = G ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = seal A α} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = unseal α A} refl
    qᶜ
    (compose-leftⁿ wfΣ q⊒ (cast-unseal hA α∈Σ ok , cross ())
      q⨟s≈r)
    M⊒M′
rightSealInversion2-cast- {s = gen A c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = inst B c} ()
    qᶜ q⨟s≈r M⊒M′

rightSealInversion2-aux :
  ∀ {Δ σ γ M T V q A α} →
  T ≡ V ⟨ unseal α A ⟩ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ q →
  ∃[ r ]
    (Δ ∣ σ ⊢ q ⨾ⁿ seal A α ≈ r ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r
-- The `extend` case is a direct store-replacement transport: recurse in the
-- exact-store premise, then replace the head store entry with its narrowing.
rightSealInversion2-aux eq (extend qᶜ pαᶜ M⊒T)
    with rightSealInversion2-aux eq M⊒T
rightSealInversion2-aux eq (extend qᶜ pαᶜ M⊒T)
    | r , q⨟seal≈r , M⊒V =
  r ,
  extendReplaceRel-compose-left (replace-here qᶜ) q⨟seal≈r ,
  extendReplaceRel-term (replace-here qᶜ) M⊒V
-- The `split` case changes both the store and the left term's opened type
-- variable.  The same store replacement lemmas handle the store component,
-- but the proof still needs an opening-transport lemma for the stripped term.
rightSealInversion2-aux eq (split qᶜ pαᶜ M⊒T) = {!!}
rightSealInversion2-aux () (⊒blame pᶜ)
rightSealInversion2-aux () (x⊒x pᶜ x∋p)
rightSealInversion2-aux () (ƛ⊒ƛ p↦qᶜ N⊒N′)
rightSealInversion2-aux () (·⊒· qᶜ L⊒L′ M⊒M′)
rightSealInversion2-aux () (Λ⊒Λ allᶜ vV V⊒V′)
rightSealInversion2-aux () (⊒Λ pᶜ N⊒V′)
rightSealInversion2-aux () (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
rightSealInversion2-aux () (α⊒α qᶜ pαᶜ L⊒L′)
rightSealInversion2-aux () (⊒α pαᶜ L⊒L′)
rightSealInversion2-aux () (ν⊒ν pᶜ qᶜ N⊒N′)
rightSealInversion2-aux () (⊒ν pᶜ N⊒N′)
-- The `ν⊒` case is a left wrapper: the right term is unconstrained, so the
-- proof should recurse under `⇑ᵗᵐ` and then rebuild `ν⊒`.
-- The attempted recursive call produces a shifted composition
-- `⇑ᶜ p ⨾ⁿ seal (⇑ᵗ A) (suc α) ≈ r`; rebuilding needs an
-- unshifting lemma that factors this through a witness for
-- `p ⨾ⁿ seal A α`.
rightSealInversion2-aux eq (ν⊒ pᶜ N⊒N′) = {!!}
rightSealInversion2-aux () (κ⊒κ κ)
rightSealInversion2-aux () (⊕⊒⊕ M⊒M′ N⊒N′)
-- Direct right-positive seal cast.  Here the syntax of `- (seal A α)` is
-- exactly `unseal α A`, so the constructor already carries the desired
-- composition evidence and the stripped premise.
-- Other right-positive casts can only reach `V ⟨ unseal α A ⟩` when the
-- dual of their cast is definitionally an unseal.  The non-seal cases are
-- expected to be syntactically impossible; they are left split out while the
-- exact dual-action refinements are worked through.
rightSealInversion2-aux eq (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  rightSealInversion2-cast+ eq qᶜ q⨟s≈r M⊒M′
-- Right-negative casts would require the cast itself to be `unseal α A`, but
-- the composition side condition classifies that cast as a narrowing.  Since
-- `unseal` is a widening constructor, the main branch should close by the
-- impossible narrowing evidence.
rightSealInversion2-aux eq (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  rightSealInversion2-cast- eq qᶜ q⨟s≈r M⊒M′
-- Left cast cases recurse on the premise.  After the recursive inversion, the
-- first missing algebra is an associativity/factoring lemma for narrowing
-- composition:
--
--   r ≈ t ⨾ⁿ p
--   r ⨾ⁿ seal A α ≈ u
--   --------------------
--   ∃[ v ] p ⨾ⁿ seal A α ≈ v × u ≈ t ⨾ⁿ v
--
-- The direct rebuild attempt then hits a second obligation: `cast+⊒` and
-- `cast-⊒` require the premise index to be cast-like (`∶ᶜ`), but the
-- recursive inversion only returns a term relation at the composed witness.
-- A complete proof needs either a strengthened IH that also returns enough
-- typing for the witness, or a derived left-cast transport lemma that produces
-- the stripped term relation without exposing that `∶ᶜ` requirement at the
-- call site.
rightSealInversion2-aux eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) = {!!}
rightSealInversion2-aux eq (cast-⊒ pᶜ r≈t⨟p M⊒M′) = {!!}

rightSealInversion2 : RightSealInversion2
rightSealInversion2 M⊒Vunseal =
  rightSealInversion2-aux refl M⊒Vunseal

right-seal-inversion₂ : RightSealInversion2
right-seal-inversion₂ = rightSealInversion2

------------------------------------------------------------------------
-- Counterexample search: ν-wrapped right unseal
------------------------------------------------------------------------

private
  NatTy : Ty
  NatTy = ‵ `ℕ

  alpha0 : TyVar
  alpha0 = 0

  alpha1 : TyVar
  alpha1 = 1

  k0 : Const
  k0 = κℕ 0

  Store0 : Store
  Store0 = (alpha0 , NatTy) ∷ []

  Sigma0 : StoreNrw
  Sigma0 = (alpha0 ꞉ id NatTy) ∷ []

  Store1Target : Store
  Store1Target = (alpha1 , NatTy) ∷ []

  Store1Source : Store
  Store1Source = (0 , ★) ∷ Store1Target

  Sigma1 : StoreNrw
  Sigma1 = (⊒ 0 ꞉=☆) ∷ (alpha1 ꞉ id NatTy) ∷ []

  seal0 : Coercion
  seal0 = seal NatTy alpha0

  seal1 : Coercion
  seal1 = seal NatTy alpha1

  unseal0 : Coercion
  unseal0 = unseal alpha0 NatTy

  wfStore0 : StoreDetWf 1 Store0
  wfStore0 =
    record
      { at = record
          { bound = λ { (here refl) → z<s }
          ; wfTy = λ { (here refl) → wfBase }
          }
      ; wfOlder = λ { (here refl) → wfBase }
      ; unique = λ { (here refl) (here refl) → refl }
      }

  wfStore1Target : StoreDetWf 2 Store1Target
  wfStore1Target =
    record
      { at = record
          { bound = λ { (here refl) → s<s z<s }
          ; wfTy = λ { (here refl) → wfBase }
          }
      ; wfOlder = λ { (here refl) → wfBase }
      ; unique = λ { (here refl) (here refl) → refl }
      }

  wfStore1Source : StoreDetWf 2 Store1Source
  wfStore1Source =
    record
      { at = record
          { bound = λ { (here refl) → z<s ; (there (here refl)) → s<s z<s }
          ; wfTy = λ { (here refl) → wf★ ; (there (here refl)) → wfBase }
          }
      ; wfOlder = λ
          { (here refl) → wf★
          ; (there (here refl)) → wfBase
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there (here ()))
          ; (there (here ())) (here refl)
          ; (there (here refl)) (there (here refl)) → refl
          }
      }

  Sigma0⊒ : 1 ⊢ Sigma0 ꞉ Store0 ⊒ˢ Store0
  Sigma0⊒ =
    ⊒ˢ-both wfBase wfBase
      (id-onlyᵈ , (cast-id wfBase refl , cross (id-‵ `ℕ)))
      ⊒ˢ-nil

  Sigma1⊒ : 2 ⊢ Sigma1 ꞉ Store1Source ⊒ˢ Store1Target
  Sigma1⊒ =
    ⊒ˢ-left
      (⊒ˢ-both wfBase wfBase
        (id-onlyᵈ , (cast-id wfBase refl , cross (id-‵ `ℕ)))
        ⊒ˢ-nil)

  endpoints0 : EndpointWf 1 Store0 NatTy (＇ alpha0)
  endpoints0 = wfBaseˢ , wfVarˢ (here refl)

  endpoints1Target : EndpointWf 2 Store1Target NatTy (＇ alpha1)
  endpoints1Target = wfBaseˢ , wfVarˢ (here refl)

  endpoints1Source : EndpointWf 2 Store1Source NatTy (＇ alpha1)
  endpoints1Source = wfBaseˢ , wfVarˢ (there (here refl))

  idNatᶜ : ∀ {Δ Σ} → Δ ∣ Σ ⊢ id NatTy ∶ᶜ NatTy ⊒ NatTy
  idNatᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

  idNat⊒ : ∀ {Δ Σ} →
    seal-or-idᵈ ∣ Δ ∣ Σ ⊢ id NatTy ∶ NatTy ⊒ NatTy
  idNat⊒ = cast-id wfBase refl , cross (id-‵ `ℕ)

  seal0⊒ : seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ seal0 ∶ NatTy ⊒ ＇ alpha0
  seal0⊒ = cast-seal wfBase (here refl) refl , sealⁿ NatTy alpha0

  seal1⊒Target :
    seal-or-idᵈ ∣ 2 ∣ Store1Target ⊢ seal1 ∶ NatTy ⊒ ＇ alpha1
  seal1⊒Target =
    cast-seal wfBase (here refl) refl , sealⁿ NatTy alpha1

  seal1⊒Source :
    seal-or-idᵈ ∣ 2 ∣ Store1Source ⊢ seal1 ∶ NatTy ⊒ ＇ alpha1
  seal1⊒Source =
    cast-seal wfBase (there (here refl)) refl , sealⁿ NatTy alpha1

  right-seal-compose0 :
    1 ∣ Sigma0 ⊢ id NatTy ⨾ⁿ seal0 ≈ seal0 ∶ NatTy ⊒ ＇ alpha0
  right-seal-compose0 =
    compose-leftⁿ wfStore0 idNat⊒ seal0⊒
      (endpointsⁿ refl refl refl refl Sigma0⊒ endpoints0 endpoints0
        (seal-or-idᵈ , proj₂ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒))
        (seal-or-idᵈ , seal0⊒))

  right-seal-compose1 :
    2 ∣ Sigma1 ⊢ id NatTy ⨾ⁿ seal1 ≈ seal1 ∶ NatTy ⊒ ＇ alpha1
  right-seal-compose1 =
    compose-leftⁿ wfStore1Target idNat⊒ seal1⊒Target
      (endpointsⁿ refl refl refl refl
        Sigma1⊒
        endpoints1Target
        endpoints1Source
        (seal-or-idᵈ ,
          proj₂ (_⨟ⁿ_ {wfΣ = wfStore1Target} idNat⊒ seal1⊒Target))
        (seal-or-idᵈ , seal1⊒Source))

  right-sealed-constant1 :
    2 ∣ Sigma1 ∣ [] ⊢ $ k0 ⊒ ($ k0) ⟨ seal1 ⟩ ∶ seal1
  right-sealed-constant1 =
    ⊒cast- idNatᶜ right-seal-compose1 (κ⊒κ k0)

  right-unsealed-constant1 :
    2 ∣ Sigma1 ∣ []
      ⊢ $ k0 ⊒ (($ k0) ⟨ seal1 ⟩) ⟨ unseal alpha1 NatTy ⟩
      ∶ id NatTy
  right-unsealed-constant1 =
    ⊒cast+ idNatᶜ right-seal-compose1 right-sealed-constant1

  right-seal-inversion₂-counterexample-premise :
    1 ∣ Sigma0 ∣ []
      ⊢ ν ★ ($ k0) (⇑ᶜ (id NatTy))
        ⊒ (($ k0) ⟨ seal0 ⟩) ⟨ unseal0 ⟩
      ∶ id NatTy
  right-seal-inversion₂-counterexample-premise =
    ν⊒ idNatᶜ right-unsealed-constant1

  -- This was the first ν-shaped counterexample candidate.  It fails: the
  -- stripped conclusion is rebuilt by relating the ν term to the bare constant
  -- at `id Nat`, then adding the right seal with `⊒cast-`.
  right-seal-inversion₂-ν-candidate-stripped :
    1 ∣ Sigma0 ∣ []
      ⊢ ν ★ ($ k0) (⇑ᶜ (id NatTy)) ⊒ ($ k0) ⟨ seal0 ⟩
      ∶ seal0
  right-seal-inversion₂-ν-candidate-stripped =
    ⊒cast-
      idNatᶜ
      right-seal-compose0
      (ν⊒ idNatᶜ (κ⊒κ k0))

right-seal-inversion₂-ν-candidate-result :
  ∃[ r ]
    (1 ∣ Sigma0
      ⊢ id NatTy ⨾ⁿ seal0 ≈ r ∶ src (id NatTy) ⊒ ＇ alpha0) ×
    1 ∣ Sigma0 ∣ []
      ⊢ ν ★ ($ k0) (⇑ᶜ (id NatTy)) ⊒ ($ k0) ⟨ seal0 ⟩ ∶ r
right-seal-inversion₂-ν-candidate-result =
  seal0 ,
  right-seal-compose-endpoints right-seal-compose0 ,
  right-seal-inversion₂-ν-candidate-stripped

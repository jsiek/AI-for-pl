{-# OPTIONS --allow-unsolved-metas #-}

module proof.RightSealInversion2 where

-- File Charter:
--   * Revised target statement for Right Seal Inversion 2, specialized to the
--     seal-unseal redex shape available at the DGG call sites.
--   * The old general statement is kept as `GeneralRightSealInversion2`; its
--     counterexample documents why arbitrary `V ⟨ unseal α A ⟩` is too
--     broad.
--   * The exported call-site statement takes the right-cast premises that DGG
--     already has: the explicit composition of `q` with `seal B α` and the premise
--     narrowing to the sealed value `V ⟨ seal A α ⟩`.
--   * The counterexample uses `ν⊒` and a context variable: inside the fresh
--     source-only store, the variable can be unsealed on the left and then
--     re-sealed/unsealed on the right; after the outer `ν⊒`, the stripped
--     conclusion would have to relate the ν source to the bare variable at a
--     seal index, which is impossible.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.NarrowWidenProperties using
  (StoreDetWf; narrowing-var-to-older⊥)

GeneralRightSealInversion2 : Set₁
GeneralRightSealInversion2 =
  ∀ {Δ σ γ M V q A α E Σ μ} →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ src q ⊒ E) →
  (seal⊒ : μ ∣ Δ ∣ Σ ⊢ seal A α ∶ E ⊒ ＇ α) →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ unseal α A ⟩ ∶ q →
  ∃[ r ]
    (Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ seal⊒)
      ≈ r ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r

RightSealInversion2 : Set₁
RightSealInversion2 =
  ∀ {Δ σ M V q r A B C D E F G α Σ μ} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ E ⊒ G) →
  (seal⊒ : μ ∣ Δ ∣ Σ ⊢ seal B α ∶ G ⊒ F) →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ seal⊒) ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ u ]
    (Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ seal⊒)
      ≈ u ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ u

right-seal-compose-endpoints :
  ∀ {Δ σ q r A B A₀ α E Σ μ} →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ E) →
  (seal⊒ : μ ∣ Δ ∣ Σ ⊢ seal A₀ α ∶ E ⊒ B) →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ seal⊒) ≈ r ∶ A ⊒ B →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ seal⊒) ≈ r
    ∶ src q ⊒ ＇ α
right-seal-compose-endpoints wfΣ q⊒ seal⊒
    (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)
    rewrite proj₁ (coercion-src-tgtᵐ (proj₁ q⊒))
          | proj₂ (coercion-src-tgtᵐ (proj₁ seal⊒)) =
  endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒

rightSealInversion2 : RightSealInversion2
rightSealInversion2 _ _ wfΣ q⊒ seal⊒ q⨟seal≈r M⊒Vseal =
  _ , right-seal-compose-endpoints wfΣ q⊒ seal⊒ q⨟seal≈r , M⊒Vseal

right-seal-inversion₂ : RightSealInversion2
right-seal-inversion₂ = rightSealInversion2

right-seal-inversion₂-cast-unseal⊥ :
  ∀ {Δ σ q r B C D E F G α Σ μ} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ E ⊒ G) →
  (unseal⊒ : μ ∣ Δ ∣ Σ ⊢ unseal α B ∶ G ⊒ F) →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ unseal⊒) ≈ r ∶ E ⊒ F →
  ⊥
right-seal-inversion₂-cast-unseal⊥ qᶜ wfΣ q⊒
    (cast-unseal hB α∈Σ ok , cross ())
    q⨟unseal≈r

-- Failed proof-search note for `GeneralRightSealInversion2`.  The direct
-- induction can strip the direct right-positive cast, but the `ν⊒`, `split`,
-- and left-cast branches require facts that the DGG call sites do not need.
-- The variable counterexample below isolates the false general premise.

------------------------------------------------------------------------
-- General-statement counterexample search: ν-wrapped right unseal
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

  unseal1 : Coercion
  unseal1 = unseal alpha1 NatTy

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

  idAlpha0 : Coercion
  idAlpha0 = id (＇ alpha0)

  idAlpha1 : Coercion
  idAlpha1 = id (＇ alpha1)

  idAlpha0ᶜ : 1 ∣ Store0 ⊢ idAlpha0 ∶ᶜ ＇ alpha0 ⊒ ＇ alpha0
  idAlpha0ᶜ =
    cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

  idAlpha1ᶜSource :
    2 ∣ Store1Source ⊢ idAlpha1 ∶ᶜ ＇ alpha1 ⊒ ＇ alpha1
  idAlpha1ᶜSource =
    cast-id (wfVar (s<s z<s)) refl , cross (id-＇ alpha1)

  idAlpha1⊒Target :
    seal-or-idᵈ ∣ 2 ∣ Store1Target
      ⊢ idAlpha1 ∶ ＇ alpha1 ⊒ ＇ alpha1
  idAlpha1⊒Target =
    cast-id (wfVar (s<s z<s)) refl , cross (id-＇ alpha1)

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
    1 ∣ Sigma0 ⊢
      proj₁ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒)
        ≈ seal0 ∶ NatTy ⊒ ＇ alpha0
  right-seal-compose0 =
    endpointsⁿ refl refl refl refl Sigma0⊒ endpoints0 endpoints0
      (seal-or-idᵈ , proj₂ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒))
      (seal-or-idᵈ , seal0⊒)

  right-seal-compose1 :
    2 ∣ Sigma1 ⊢
      proj₁ (_⨟ⁿ_ {wfΣ = wfStore1Target} idNat⊒ seal1⊒Target)
        ≈ seal1 ∶ NatTy ⊒ ＇ alpha1
  right-seal-compose1 =
    endpointsⁿ refl refl refl refl
      Sigma1⊒
      endpoints1Target
      endpoints1Source
      (seal-or-idᵈ ,
        proj₂ (_⨟ⁿ_ {wfΣ = wfStore1Target} idNat⊒ seal1⊒Target))
      (seal-or-idᵈ , seal1⊒Source)

  left-seal-compose1 :
    2 ∣ Sigma1 ⊢
      seal1
        ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfStore1Target}
            seal1⊒Target idAlpha1⊒Target)
        ∶ NatTy ⊒ ＇ alpha1
  left-seal-compose1 =
    endpointsⁿ refl refl refl refl
      Sigma1⊒
      endpoints1Target
      endpoints1Source
      (seal-or-idᵈ , seal1⊒Target)
      (seal-or-idᵈ , seal1⊒Source)

  right-sealed-constant1 :
    2 ∣ Sigma1 ∣ [] ⊢ $ k0 ⊒ ($ k0) ⟨ seal1 ⟩ ∶ seal1
  right-sealed-constant1 =
    ⊒cast- idNatᶜ wfStore1Target idNat⊒ seal1⊒Target
      right-seal-compose1 (κ⊒κ k0)

  right-unsealed-constant1 :
    2 ∣ Sigma1 ∣ []
      ⊢ $ k0 ⊒ (($ k0) ⟨ seal1 ⟩) ⟨ unseal alpha1 NatTy ⟩
      ∶ id NatTy
  right-unsealed-constant1 =
    ⊒cast+ idNatᶜ wfStore1Target idNat⊒ seal1⊒Target
      right-seal-compose1 right-sealed-constant1

  alpha-var1 :
    2 ∣ Sigma1 ∣ idAlpha1 ∷ [] ⊢ ` zero ⊒ ` zero ∶ idAlpha1
  alpha-var1 =
    x⊒x idAlpha1ᶜSource Z

  left-unsealed-alpha-var1 :
    2 ∣ Sigma1 ∣ idAlpha1 ∷ []
      ⊢ (` zero) ⟨ unseal1 ⟩ ⊒ ` zero ∶ seal1
  left-unsealed-alpha-var1 =
    cast+⊒ idAlpha1ᶜSource wfStore1Target
      seal1⊒Target idAlpha1⊒Target left-seal-compose1 alpha-var1

  right-unsealed-alpha-var1 :
    2 ∣ Sigma1 ∣ idAlpha1 ∷ []
      ⊢ (` zero) ⟨ unseal1 ⟩ ⊒ (` zero) ⟨ unseal1 ⟩ ∶ id NatTy
  right-unsealed-alpha-var1 =
    ⊒cast+ idNatᶜ wfStore1Target idNat⊒ seal1⊒Target
      right-seal-compose1 left-unsealed-alpha-var1

  right-seal-inversion₂-counterexample-premise :
    1 ∣ Sigma0 ∣ []
      ⊢ ν ★ ($ k0) (⇑ᶜ (id NatTy))
        ⊒ (($ k0) ⟨ seal0 ⟩) ⟨ unseal0 ⟩
      ∶ id NatTy
  right-seal-inversion₂-counterexample-premise =
    ν⊒ idNatᶜ right-unsealed-constant1

  right-seal-inversion₂-var-counterexample-premise :
    1 ∣ Sigma0 ∣ idAlpha0 ∷ []
      ⊢ ν ★ ((` zero) ⟨ unseal1 ⟩) (⇑ᶜ (id NatTy))
        ⊒ (` zero) ⟨ unseal0 ⟩
      ∶ id NatTy
  right-seal-inversion₂-var-counterexample-premise =
    ν⊒ idNatᶜ right-unsealed-alpha-var1

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
      wfStore0
      idNat⊒
      seal0⊒
      right-seal-compose0
      (ν⊒ idNatᶜ (κ⊒κ k0))

right-seal-inversion₂-ν-candidate-result :
  ∃[ r ]
    (1 ∣ Sigma0
      ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒)
        ≈ r ∶ src (id NatTy) ⊒ ＇ alpha0) ×
    1 ∣ Sigma0 ∣ []
      ⊢ ν ★ ($ k0) (⇑ᶜ (id NatTy)) ⊒ ($ k0) ⟨ seal0 ⟩ ∶ r
right-seal-inversion₂-ν-candidate-result =
  seal0 ,
  right-seal-compose-endpoints wfStore0 idNat⊒ seal0⊒ right-seal-compose0 ,
  right-seal-inversion₂-ν-candidate-stripped

private
  ν-ann-injective :
    ∀ {A N N′ c c′} →
    ν A N c ≡ ν A N′ c′ →
    c ≡ c′
  ν-ann-injective refl = refl

  ν-body-injective :
    ∀ {A N N′ c c′} →
    ν A N c ≡ ν A N′ c′ →
    N ≡ N′
  ν-body-injective refl = refl

  renamed-idNat-tgt-alpha0⊥ :
    ∀ {r} →
    renameᶜ suc r ≡ id NatTy →
    tgt r ≡ ＇ alpha0 →
    ⊥
  renamed-idNat-tgt-alpha0⊥ {r = id (＇ X)} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = id (‵ `ℕ)} eq ()
  renamed-idNat-tgt-alpha0⊥ {r = id (‵ `𝔹)} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = id ★} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = id (A ⇒ B)} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = id (`∀ A)} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = c ︔ d} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = c ↦ d} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = `∀ c} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = G !} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = G ？} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = seal A α} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = unseal α A} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = gen A c} () tgt-r
  renamed-idNat-tgt-alpha0⊥ {r = inst B c} () tgt-r

  idNat-right-seal-not-idNat :
    1 ∣ Sigma0
      ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒)
        ≈ id NatTy ∶ NatTy ⊒ ＇ alpha0 →
    ⊥
  idNat-right-seal-not-idNat
      (endpointsⁿ src-u tgt-u src-r () σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)

  idNat-right-seal-not-renamed-idNat :
    ∀ {r} →
    renameᶜ suc r ≡ id NatTy →
    1 ∣ Sigma0
      ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒)
        ≈ r ∶ src (id NatTy) ⊒ ＇ alpha0 →
    ⊥
  idNat-right-seal-not-renamed-idNat r≡idNat
      (endpointsⁿ src-u tgt-u src-r tgt-r
        σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒) =
    renamed-idNat-tgt-alpha0⊥ r≡idNat tgt-r

  idNat-target :
    ∀ {r B} →
    r ≡ id NatTy →
    tgt r ≡ B →
    B ≡ NatTy
  idNat-target r≡idNat tgt-r =
    trans (sym tgt-r) (cong tgt r≡idNat)

  inner-cast+⊥ :
    ∀ {Δ σ γ M M′ q p t A B C D E Σ μ} →
    M ⟨ - t ⟩ ≡ (` zero) ⟨ unseal1 ⟩ →
    M′ ≡ ` zero →
    q ≡ id NatTy →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    (wfΣ : StoreDetWf Δ Σ) →
    (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ E) →
    (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ E ⊒ B) →
    Δ ∣ σ ⊢ q ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B →
    Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
    ⊥
  inner-cast+⊥ {t = id A} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = c ︔ d} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = c ↦ d} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = `∀ c} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (＇ β) !} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (‵ ι) !} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = ★ !} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (A ⇒ B) !} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (`∀ A) !} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (＇ β) ？} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (‵ ι) ？} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = ★ ？} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (A ⇒ B) ？} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = (`∀ A) ？} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = seal .NatTy .alpha1} refl eqT q≡id pᶜ
      wfΣ
      (cast-seal hNat α∈Σ seal-ok , sealⁿ .NatTy .alpha1)
      p⊒
      (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒)
      M⊒M′ =
    let
      B≡Nat = idNat-target q≡id tgt-r
      p⊒Nat =
        subst (λ B → _ ∣ _ ∣ _ ⊢ _ ∶ ＇ alpha1 ⊒ B) B≡Nat p⊒
    in
    narrowing-var-to-older⊥ wfΣ wfBase p⊒Nat
  inner-cast+⊥ {t = unseal α A} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = gen A c} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  inner-cast+⊥ {t = inst B c} () eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′

  inner-cast-⊥ :
    ∀ {Δ σ γ M M′ q r t A B C D E Σ μ} →
    M ⟨ t ⟩ ≡ (` zero) ⟨ unseal1 ⟩ →
    M′ ≡ ` zero →
    q ≡ id NatTy →
    Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
    (wfΣ : StoreDetWf Δ Σ) →
    (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ E) →
    (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ E ⊒ B) →
    Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ q⊒) ∶ A ⊒ B →
    Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r →
    ⊥
  inner-cast-⊥ {t = id A} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = c ︔ d} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = c ↦ d} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = `∀ c} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = G !} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = G ？} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = seal A α} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = unseal α A} refl eqT q≡id qᶜ wfΣ
      (cast-unseal hA α∈Σ ok , cross ())
      q⊒
      r≈t⨟q
      M⊒M′
  inner-cast-⊥ {t = gen A c} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′
  inner-cast-⊥ {t = inst B c} () eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′

  right-seal-inversion₂-var-inner⊥ :
    ∀ {A q M T} →
    M ≡ (` zero) ⟨ unseal1 ⟩ →
    T ≡ ` zero →
    q ≡ id NatTy →
    2 ∣ (⊒ zero ꞉=☆) ∷ (alpha1 ꞉= ⇑ᵗ A ⊒) ∷ []
      ∣ idAlpha1 ∷ []
      ⊢ M ⊒ T ∶ q →
    ⊥
  right-seal-inversion₂-var-inner⊥ eqM eqT q≡id
      (cast+⊒ pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′) =
    inner-cast+⊥ eqM eqT q≡id pᶜ wfΣ t⊒ p⊒ q≈t⨟p M⊒M′
  right-seal-inversion₂-var-inner⊥ eqM eqT q≡id
      (cast-⊒ qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′) =
    inner-cast-⊥ eqM eqT q≡id qᶜ wfΣ t⊒ q⊒ r≈t⨟q M⊒M′

  right-seal-inversion₂-var-stripped-source⊥ :
    ∀ {A r M T} →
    M ≡ ν ★ ((` zero) ⟨ unseal1 ⟩) (⇑ᶜ (id NatTy)) →
    T ≡ ` zero →
    1 ∣ (alpha0 ꞉= A ⊒) ∷ [] ∣ idAlpha0 ∷ []
      ⊢ M ⊒ T ∶ r →
    ⊥
  right-seal-inversion₂-var-stripped-source⊥ eqM eqT M⊒T = {!!}

  right-seal-inversion₂-var-stripped-aux⊥ :
    ∀ {r M T} →
    M ≡ ν ★ ((` zero) ⟨ unseal1 ⟩) (⇑ᶜ (id NatTy)) →
    T ≡ ` zero →
    1 ∣ Sigma0
      ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒)
        ≈ r ∶ src (id NatTy) ⊒ ＇ alpha0 →
    1 ∣ Sigma0 ∣ idAlpha0 ∷ []
      ⊢ M ⊒ T ∶ r →
    ⊥
  right-seal-inversion₂-var-stripped-aux⊥ eqM eqT comp M⊒T = {!!}

  right-seal-inversion₂-var-stripped⊥ :
    ∀ {r} →
    1 ∣ Sigma0
      ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒)
        ≈ r ∶ src (id NatTy) ⊒ ＇ alpha0 →
    1 ∣ Sigma0 ∣ idAlpha0 ∷ []
      ⊢ ν ★ ((` zero) ⟨ unseal1 ⟩) (⇑ᶜ (id NatTy))
        ⊒ ` zero ∶ r →
    ⊥
  right-seal-inversion₂-var-stripped⊥ comp M⊒T =
    right-seal-inversion₂-var-stripped-aux⊥ refl refl comp M⊒T

right-seal-inversion₂-var-counterexample :
  GeneralRightSealInversion2 →
  ⊥
right-seal-inversion₂-var-counterexample right-seal-inversion₂′
    with right-seal-inversion₂′
      right-seal-inversion₂-var-counterexample-premise
right-seal-inversion₂-var-counterexample right-seal-inversion₂′
    | r , id⨟seal≈r , stripped =
  right-seal-inversion₂-var-stripped⊥ id⨟seal≈r stripped

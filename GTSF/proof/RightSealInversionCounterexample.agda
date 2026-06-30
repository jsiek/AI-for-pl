module proof.RightSealInversionCounterexample where

-- File Charter:
--   * Counterexample for `right-seal-inversion₁`.
--   * The premise relates the same sealed numeric constant on both sides via
--     a right seal followed by a left cast.
--   * The contradiction is that stripping the right seal requires a relation
--     from the sealed source constant to the bare numeric constant.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; z<s)
open import Data.Product using (_,_; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.NarrowWidenProperties
  using (StoreDetWf; narrowing-var-to-older⊥)

private
  NatTy : Ty
  NatTy = ‵ `ℕ

  alpha0 : TyVar
  alpha0 = 0

  k0 : Const
  k0 = κℕ 0

  Store0 : Store
  Store0 = (alpha0 , NatTy) ∷ []

  Sigma0 : StoreNrw
  Sigma0 = (alpha0 ꞉ id NatTy) ∷ []

  seal0 : Coercion
  seal0 = seal NatTy alpha0

  idAlpha0 : Coercion
  idAlpha0 = id (＇ alpha0)

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

  Sigma0⊒ : 1 ⊢ Sigma0 ꞉ Store0 ⊒ˢ Store0
  Sigma0⊒ =
    ⊒ˢ-both wfBase wfBase
      (id-onlyᵈ , (cast-id wfBase refl , cross (id-‵ `ℕ)))
      ⊒ˢ-nil

  endpoints0 : EndpointWf 1 Store0 NatTy (＇ alpha0)
  endpoints0 = wfBaseˢ , wfVarˢ (here refl)

  idNatᶜ : 1 ∣ Store0 ⊢ id NatTy ∶ᶜ NatTy ⊒ NatTy
  idNatᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

  idNat⊒ : seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ id NatTy ∶ NatTy ⊒ NatTy
  idNat⊒ = cast-id wfBase refl , cross (id-‵ `ℕ)

  idAlphaᶜ : 1 ∣ Store0 ⊢ idAlpha0 ∶ᶜ ＇ alpha0 ⊒ ＇ alpha0
  idAlphaᶜ = cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

  idAlpha⊒ : seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ idAlpha0 ∶ ＇ alpha0 ⊒ ＇ alpha0
  idAlpha⊒ = cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

  seal0⊒ : seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ seal0 ∶ NatTy ⊒ ＇ alpha0
  seal0⊒ = cast-seal wfBase (here refl) refl , sealⁿ NatTy alpha0

  right-seal-compose :
    1 ∣ Sigma0 ⊢ id NatTy ⨾ⁿ seal0 ≈ seal0 ∶ NatTy ⊒ ＇ alpha0
  right-seal-compose =
    compose-leftⁿ wfStore0 idNat⊒ seal0⊒
      (endpointsⁿ refl refl refl refl Sigma0⊒ endpoints0 endpoints0
        (seal-or-idᵈ , proj₂ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒))
        (seal-or-idᵈ , seal0⊒))

  left-seal-compose :
    1 ∣ Sigma0 ⊢ seal0 ≈ seal0 ⨾ⁿ idAlpha0 ∶ NatTy ⊒ ＇ alpha0
  left-seal-compose =
    compose-rightⁿ wfStore0 seal0⊒ idAlpha⊒
      (endpointsⁿ refl refl refl refl Sigma0⊒ endpoints0 endpoints0
        (seal-or-idᵈ , seal0⊒)
        (seal-or-idᵈ , proj₂ (_⨟ⁿ_ {wfΣ = wfStore0} seal0⊒ idAlpha⊒)))

  right-sealed-constant :
    1 ∣ Sigma0 ∣ [] ⊢ $ k0 ⊒ ($ k0) ⟨ seal0 ⟩ ∶ seal0
  right-sealed-constant =
    ⊒cast- idNatᶜ right-seal-compose (κ⊒κ k0)

  bare-constant-index-source :
    ∀ {A q M M′} →
    M ≡ $ k0 →
    M′ ≡ $ k0 →
    1 ∣ (alpha0 ꞉= A ⊒) ∷ [] ∣ [] ⊢ M ⊒ M′ ∶ q →
    q ≡ id NatTy
  bare-constant-index-source refl refl (κ⊒κ (κℕ n)) = refl

  bare-constant-index :
    ∀ {q M M′} →
    M ≡ $ k0 →
    M′ ≡ $ k0 →
    1 ∣ Sigma0 ∣ [] ⊢ M ⊒ M′ ∶ q →
    q ≡ id NatTy
  bare-constant-index eqM eqM′ (extend qᶜ pαᶜ M⊒M′) =
    bare-constant-index-source eqM eqM′ M⊒M′
  bare-constant-index refl refl (κ⊒κ (κℕ n)) = refl

  left-cast-plus-seal⊥ :
    ∀ {μ Δ Σ L t A B} →
    L ⟨ - t ⟩ ≡ ($ k0) ⟨ seal0 ⟩ →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
    ⊥
  left-cast-plus-seal⊥ {t = (＇ α) ？} () (t⊢ , untag (＇ .α))
  left-cast-plus-seal⊥ {t = (‵ ι) ？} () (t⊢ , untag (‵ .ι))
  left-cast-plus-seal⊥ {t = (★ ⇒ ★) ？} () (t⊢ , untag ★⇒★)
  left-cast-plus-seal⊥ {t = unseal α A} refl (t⊢ , cross ())

  idNat-target :
    ∀ {r B} →
    r ≡ id NatTy →
    tgt r ≡ B →
    B ≡ NatTy
  idNat-target r≡idNat tgt-r =
    trans (sym tgt-r) (cong tgt r≡idNat)

  stripped-impossible-source :
    ∀ {A q M M′} →
    M ≡ ($ k0) ⟨ seal0 ⟩ →
    M′ ≡ $ k0 →
    1 ∣ (alpha0 ꞉= A ⊒) ∷ [] ∣ [] ⊢ M ⊒ M′ ∶ q →
    ⊥
  stripped-impossible-source eqM eqM′
      (cast+⊒ pᶜ (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) M⊒M′) =
    left-cast-plus-seal⊥ eqM t⊒
  stripped-impossible-source refl refl
      (cast-⊒ pᶜ
        (compose-rightⁿ wfΣ
          t⊒@(cast-seal hNat α∈Σ seal-ok , sealⁿ .NatTy .alpha0)
          p⊒
          (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒))
        M⊒M′) =
    let
      r≡idNat = bare-constant-index-source refl refl M⊒M′
      B≡Nat = idNat-target r≡idNat tgt-r
      p⊒Nat = subst (λ B → _ ∣ _ ∣ _ ⊢ _ ∶ ＇ alpha0 ⊒ B) B≡Nat p⊒
    in
    narrowing-var-to-older⊥ wfΣ wfBase p⊒Nat

  stripped-impossible-aux :
    ∀ {q M M′} →
    M ≡ ($ k0) ⟨ seal0 ⟩ →
    M′ ≡ $ k0 →
    1 ∣ Sigma0 ∣ [] ⊢ M ⊒ M′ ∶ q →
    ⊥
  stripped-impossible-aux eqM eqM′ (extend qᶜ pαᶜ M⊒M′) =
    stripped-impossible-source eqM eqM′ M⊒M′
  stripped-impossible-aux eqM eqM′
      (cast+⊒ pᶜ (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) M⊒M′) =
    left-cast-plus-seal⊥ eqM t⊒
  stripped-impossible-aux refl refl
      (cast-⊒ pᶜ
        (compose-rightⁿ wfΣ
          t⊒@(cast-seal hNat α∈Σ seal-ok , sealⁿ .NatTy .alpha0)
          p⊒
          (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒))
        M⊒M′) =
    let
      r≡idNat = bare-constant-index refl refl M⊒M′
      B≡Nat = idNat-target r≡idNat tgt-r
      p⊒Nat = subst (λ B → _ ∣ _ ∣ _ ⊢ _ ∶ ＇ alpha0 ⊒ B) B≡Nat p⊒
    in
    narrowing-var-to-older⊥ wfΣ wfBase p⊒Nat

counterexample-premise :
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩
      ⊒ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩
    ∶ id (＇ 0)
counterexample-premise =
  cast-⊒ idAlphaᶜ left-seal-compose right-sealed-constant

stripped-impossible :
  ∀ {q} →
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩ ⊒ $ (κℕ 0) ∶ q →
  ⊥
stripped-impossible M⊒M′ =
  stripped-impossible-aux refl refl M⊒M′

right-seal-inversion₁-counterexample :
  (∀ {Δ σ γ M V r A α} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
    ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q) →
  ⊥
right-seal-inversion₁-counterexample right-seal-inversion₁
    with right-seal-inversion₁ counterexample-premise
right-seal-inversion₁-counterexample right-seal-inversion₁
    | q , M⊒M′ =
  stripped-impossible M⊒M′

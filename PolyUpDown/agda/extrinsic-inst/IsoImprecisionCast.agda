module IsoImprecisionCast where

-- File Charter:
--   * Sketches the isomorphism between indexed type imprecision and `Cast`.
--   * Makes the context correspondence explicit: plain imprecision variables
--   * remain type variables, while ν-bound imprecision variables become seals
--   * equipped with either `cast-seal` or `cast-tag` permission.
--   * The base case carries resources for pre-existing concrete seals; without
--   * them, the `⊑ₒ-★` rule for seal grounds cannot be translated to `Cast`.
--   * States the forward/backward bridge theorems and the key commuting
--   * equations needed for the ν cases.

open import Types
open import UpDown
  using
    ( CastPerm; cast-seal; cast-tag
    ; _∈cast_; _∈tag_
    ; here-cast-only; there-cast; here-tag-only; there-tag
    ; wfTySome
    ; ⊢_ok_
    )
open import Cast
open import ImprecisionIndexed
open import Store using (renameLookupᵗ)
open import TypeProperties
  using
    ( TyRenameWf-suc
    ; renameLookupˢ
    ; renameᵗ-⇑ˢ
    ; renameᵗ-preserves-WfTy
    ; open-renᵗ-suc
    )
open import TypeCheckDec using (raiseVarFrom; raiseVarFrom-≢)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (false; true)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)

------------------------------------------------------------------------
-- The context/resource correspondence
------------------------------------------------------------------------

data SealResource (Σ : Store) (Φ : List CastPerm) : Seal → Set where
  seal-cast :
    ∀ {α} →
    Σ ∋ˢ α ⦂ ★ →
    α ∈cast Φ →
    SealResource Σ Φ α

  seal-tag :
    ∀ {α} →
    α ∈tag Φ →
    SealResource Σ Φ α

data CastCtx : ICtx → Store → List CastPerm → Set where
  cast-base :
    ∀ {Σ Φ} →
    (∀ α → SealResource Σ Φ α) →
    CastCtx [] Σ Φ

  cast-plain :
    ∀ {Γ Σ Φ} →
    CastCtx Γ Σ Φ →
    CastCtx (plain ∷ Γ) (⟰ᵗ Σ) Φ

  cast-ν-seal :
    ∀ {Γ Σ Φ} →
    CastCtx Γ Σ Φ →
    CastCtx (ν-bound ∷ Γ) ((zero , ★) ∷ ⟰ˢ Σ) (cast-seal ∷ Φ)

  cast-ν-tag :
    ∀ {Γ Σ Φ} →
    CastCtx Γ Σ Φ →
    CastCtx (ν-bound ∷ Γ) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) (cast-tag ∷ Φ)

lift-seal-resourceᵗ :
  ∀ {Σ Φ α} →
  SealResource Σ Φ α →
  SealResource (⟰ᵗ Σ) Φ α
lift-seal-resourceᵗ (seal-cast h α∈Φ) =
  seal-cast (renameLookupᵗ suc h) α∈Φ
lift-seal-resourceᵗ (seal-tag α∈Φ) = seal-tag α∈Φ

lift-seal-resourceˢ-seal :
  ∀ {Σ Φ α} →
  SealResource Σ Φ α →
  SealResource ((zero , ★) ∷ ⟰ˢ Σ) (cast-seal ∷ Φ) (suc α)
lift-seal-resourceˢ-seal (seal-cast h α∈Φ) =
  seal-cast (S∋ˢ (renameLookupˢ suc h)) (there-cast α∈Φ)
lift-seal-resourceˢ-seal (seal-tag α∈Φ) =
  seal-tag (there-tag α∈Φ)

lift-seal-resourceˢ-tag :
  ∀ {Σ Φ α} →
  SealResource Σ Φ α →
  SealResource ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) (cast-tag ∷ Φ) (suc α)
lift-seal-resourceˢ-tag (seal-cast h α∈Φ) =
  seal-cast (S∋ˢ (renameLookupˢ suc h)) (there-cast α∈Φ)
lift-seal-resourceˢ-tag (seal-tag α∈Φ) =
  seal-tag (there-tag α∈Φ)

seal-resource :
  ∀ {Γ Σ Φ} →
  CastCtx Γ Σ Φ →
  (α : Seal) →
  SealResource Σ Φ (interpSeal Γ α)
seal-resource (cast-base r) α = r α
seal-resource (cast-plain cΓ) α =
  lift-seal-resourceᵗ (seal-resource cΓ α)
seal-resource (cast-ν-seal cΓ) α =
  lift-seal-resourceˢ-seal (seal-resource cΓ α)
seal-resource (cast-ν-tag cΓ) α =
  lift-seal-resourceˢ-tag (seal-resource cΓ α)

------------------------------------------------------------------------
-- What imprecision variables become under `interp`
------------------------------------------------------------------------

PlainVarImage : ICtx → TyVar → Set
PlainVarImage Γ X = ∃[ Y ] interpVar Γ X ≡ ＇ Y

νVarImage : ICtx → TyVar → Set
νVarImage Γ X = ∃[ α ] interpVar Γ X ≡ ｀ α

plain-var-image :
  ∀ {Γ X} →
  Γ ∋ X ∶ plain →
  PlainVarImage Γ X
plain-var-image here = zero , refl
plain-var-image (there {m′ = plain} x∈) with plain-var-image x∈
plain-var-image (there {m′ = plain} x∈) | Y , eq =
  suc Y , cong ⇑ᵗ eq
plain-var-image (there {m′ = ν-bound} x∈) with plain-var-image x∈
plain-var-image (there {m′ = ν-bound} x∈) | Y , eq =
  Y , cong ⇑ˢ eq

ν-var-image :
  ∀ {Γ X} →
  Γ ∋ X ∶ ν-bound →
  νVarImage Γ X
ν-var-image here = zero , refl
ν-var-image (there {m′ = plain} x∈) with ν-var-image x∈
ν-var-image (there {m′ = plain} x∈) | α , eq =
  α , cong ⇑ᵗ eq
ν-var-image (there {m′ = ν-bound} x∈) with ν-var-image x∈
ν-var-image (there {m′ = ν-bound} x∈) | α , eq =
  suc α , cong ⇑ˢ eq

ν-var-resource :
  ∀ {Γ Σ Φ X} →
  CastCtx Γ Σ Φ →
  Γ ∋ X ∶ ν-bound →
  ∃[ α ] (interpVar Γ X ≡ ｀ α × SealResource Σ Φ α)
ν-var-resource (cast-plain cΓ) (there x∈)
    with ν-var-resource cΓ x∈
ν-var-resource (cast-plain cΓ) (there x∈) | α , eq , r =
  α , cong ⇑ᵗ eq , lift-seal-resourceᵗ r
ν-var-resource (cast-ν-seal cΓ) here =
  zero , refl , seal-cast (Z∋ˢ refl refl) here-cast-only
ν-var-resource (cast-ν-seal cΓ) (there x∈)
    with ν-var-resource cΓ x∈
ν-var-resource (cast-ν-seal cΓ) (there x∈) | α , eq , r =
  suc α , cong ⇑ˢ eq , lift-seal-resourceˢ-seal r
ν-var-resource (cast-ν-tag cΓ) here =
  zero , refl , seal-tag here-tag-only
ν-var-resource (cast-ν-tag cΓ) (there x∈)
    with ν-var-resource cΓ x∈
ν-var-resource (cast-ν-tag cΓ) (there x∈) | α , eq , r =
  suc α , cong ⇑ˢ eq , lift-seal-resourceˢ-tag r

lookup-mode :
  ∀ Γ X →
  X < length Γ →
  ∃[ m ] Γ ∋ X ∶ m
lookup-mode [] X ()
lookup-mode (plain ∷ Γ) zero z<s = plain , here
lookup-mode (plain ∷ Γ) (suc X) (s<s X<Γ) with lookup-mode Γ X X<Γ
lookup-mode (plain ∷ Γ) (suc X) (s<s X<Γ) | m , x∈ =
  m , there x∈
lookup-mode (ν-bound ∷ Γ) zero z<s = ν-bound , here
lookup-mode (ν-bound ∷ Γ) (suc X) (s<s X<Γ) with lookup-mode Γ X X<Γ
lookup-mode (ν-bound ∷ Γ) (suc X) (s<s X<Γ) | m , x∈ =
  m , there x∈

clean-var-plain :
  ∀ {Γ Σ Φ X} →
  CastCtx Γ Σ Φ →
  X < length Γ →
  Clean Φ (interpVar Γ X) →
  Γ ∋ X ∶ plain
clean-var-plain cΓ X< clean with lookup-mode _ _ X<
clean-var-plain cΓ X< clean | plain , x∈ = x∈
clean-var-plain cΓ X< clean | ν-bound , x∈
    with ν-var-resource cΓ x∈
clean-var-plain cΓ X< clean | ν-bound , x∈
    | α , eq , seal-cast h α∈Φ =
  ⊥-elim (let α∉cast , α∉tag = subst (Clean _) eq clean in α∉cast α∈Φ)
clean-var-plain cΓ X< clean | ν-bound , x∈
    | α , eq , seal-tag α∈Φ =
  ⊥-elim (let α∉cast , α∉tag = subst (Clean _) eq clean in α∉tag α∈Φ)

clean-reflᵢ :
  ∀ {Γ Σ Φ Ψ A} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A →
  Clean Φ (interp Γ A) →
  Γ ⊢ A ⊑ᵢ A
clean-reflᵢ cΓ (wfVar X<Γ) clean =
  ⊑ᵢ-＇ (clean-var-plain cΓ X<Γ clean)
clean-reflᵢ cΓ (wfSeal {α = α} α<Ψ) clean = ⊑ᵢ-｀ α
clean-reflᵢ cΓ (wfBase {ι = ι}) clean = ⊑ᵢ-‵ ι
clean-reflᵢ cΓ wf★ clean = ⊑ᵢ-★★
clean-reflᵢ cΓ (wf⇒ {A = A} {B = B} wfA wfB) (cleanA , cleanB) =
  ⊑ᵢ-⇒ A A B B (clean-reflᵢ cΓ wfA cleanA)
                  (clean-reflᵢ cΓ wfB cleanB)
clean-reflᵢ cΓ (wf∀ {A = A} wfA) clean =
  ⊑ᵢ-∀ A A (clean-reflᵢ (cast-plain cΓ) wfA clean)

occurs-raiseVarFrom-false :
  ∀ k A →
  occurs k (renameᵗ (raiseVarFrom k) A) ≡ false
occurs-raiseVarFrom-false k (＇ X) with k ≟ raiseVarFrom k X
occurs-raiseVarFrom-false k (＇ X) | yes eq =
  ⊥-elim (raiseVarFrom-≢ k X (sym eq))
occurs-raiseVarFrom-false k (＇ X) | no neq = refl
occurs-raiseVarFrom-false k (｀ α) = refl
occurs-raiseVarFrom-false k (‵ ι) = refl
occurs-raiseVarFrom-false k ★ = refl
occurs-raiseVarFrom-false k (A ⇒ B)
  rewrite occurs-raiseVarFrom-false k A
        | occurs-raiseVarFrom-false k B = refl
occurs-raiseVarFrom-false k (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raiseVarFrom-false (suc k) A

occurs-zero-⇑ᵗ :
  ∀ A →
  occurs zero (⇑ᵗ A) ≡ false
occurs-zero-⇑ᵗ = occurs-raiseVarFrom-false zero

interpVar-plains-occurs-at :
  ∀ k Γ X →
  occurs k (interpVar (plains (suc k) Γ) X) ≡ occurs k (＇ X)
interpVar-plains-occurs-at zero Γ zero = refl
interpVar-plains-occurs-at zero Γ (suc X) =
  occurs-zero-⇑ᵗ (interpVar Γ X)
interpVar-plains-occurs-at (suc k) Γ zero = refl
interpVar-plains-occurs-at (suc k) Γ (suc X) =
  trans
    (occurs-raise zero k (interpVar (plains (suc k) Γ) X))
    (trans
      (interpVar-plains-occurs-at k Γ X)
      (sym (occurs-raise zero k (＇ X))))

interp-plains-occurs-at :
  ∀ k Γ A →
  occurs k (interp (plains (suc k) Γ) A) ≡ occurs k A
interp-plains-occurs-at k Γ (＇ X) =
  interpVar-plains-occurs-at k Γ X
interp-plains-occurs-at k Γ (｀ α) = refl
interp-plains-occurs-at k Γ (‵ ι) = refl
interp-plains-occurs-at k Γ ★ = refl
interp-plains-occurs-at k Γ (A ⇒ B)
  rewrite interp-plains-occurs-at k Γ A
        | interp-plains-occurs-at k Γ B = refl
interp-plains-occurs-at k Γ (`∀ A) =
  interp-plains-occurs-at (suc k) Γ A

interp-plain-occurs-zero :
  ∀ Γ A →
  occurs zero (interp (plain ∷ Γ) A) ≡ occurs zero A
interp-plain-occurs-zero = interp-plains-occurs-at zero

------------------------------------------------------------------------
-- The top ν-bound variable can cast to/from ★ using either permission.
------------------------------------------------------------------------

ν-zero-⊑ᶜ★ :
  ∀ {Γ Σ Φ} →
  CastCtx (ν-bound ∷ Γ) Σ Φ →
  Σ ∣ Φ ⊢ ｀ zero ⊑ᶜ ★
ν-zero-⊑ᶜ★ (cast-ν-seal cΓ) =
  ⊑ᶜ-unseal★ (⊑ᶜ-id (wfTySome (｀ zero))) (Z∋ˢ refl refl) here-cast-only
ν-zero-⊑ᶜ★ (cast-ν-tag cΓ) =
  ⊑ᶜ-tag (⊑ᶜ-id (wfTySome (｀ zero))) (｀ zero) here-tag-only

ν-zero-⊒ᶜ★ :
  ∀ {Γ Σ Φ} →
  CastCtx (ν-bound ∷ Γ) Σ Φ →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ ｀ zero
ν-zero-⊒ᶜ★ (cast-ν-seal cΓ) =
  ⊒ᶜ-seal★ (⊒ᶜ-id (wfTySome (｀ zero))) (Z∋ˢ refl refl) here-cast-only
ν-zero-⊒ᶜ★ (cast-ν-tag cΓ) =
  ⊒ᶜ-untag (｀ zero) here-tag-only zero (⊒ᶜ-id (wfTySome (｀ zero)))

------------------------------------------------------------------------
-- Cast constructors from resources
------------------------------------------------------------------------

⊑ᶜ-cast :
  ∀ {Σ Φ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ⊢ A ⊑ᶜ B →
  Σ ∣ Φ ⊢ A′ ⊑ᶜ B′
⊑ᶜ-cast refl refl p = p

⊒ᶜ-cast :
  ∀ {Σ Φ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ⊢ A ⊒ᶜ B →
  Σ ∣ Φ ⊢ A′ ⊒ᶜ B′
⊒ᶜ-cast refl refl p = p

resource⇒⊑ᶜ★′ :
  ∀ {Σ Φ A α} →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ A ⊑ᶜ ｀ α →
  Σ ∣ Φ ⊢ A ⊑ᶜ ★
resource⇒⊑ᶜ★′ (seal-cast h α∈Φ) p =
  ⊑ᶜ-unseal★ p h α∈Φ
resource⇒⊑ᶜ★′ (seal-tag α∈Φ) p =
  ⊑ᶜ-tag p (｀ _) α∈Φ

resource⇒⊑ᶜ★ :
  ∀ {Σ Φ α} →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ ｀ α ⊑ᶜ ★
resource⇒⊑ᶜ★ r = resource⇒⊑ᶜ★′ r (⊑ᶜ-id (wfTySome (｀ _)))

resource⇒⊒ᶜ★′ :
  ∀ {Σ Φ A α} →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ ｀ α ⊒ᶜ A →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ A
resource⇒⊒ᶜ★′ (seal-cast h α∈Φ) p =
  ⊒ᶜ-seal★ p h α∈Φ
resource⇒⊒ᶜ★′ (seal-tag α∈Φ) p =
  ⊒ᶜ-untag (｀ _) α∈Φ zero p

resource⇒⊒ᶜ★ :
  ∀ {Σ Φ α} →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ ｀ α
resource⇒⊒ᶜ★ r = resource⇒⊒ᶜ★′ r (⊒ᶜ-id (wfTySome (｀ _)))

ground⇒cast⊑★ :
  ∀ {Γ Σ Φ A G} →
  CastCtx Γ Σ Φ →
  Ground G →
  Σ ∣ Φ ⊢ A ⊑ᶜ interp Γ G →
  Σ ∣ Φ ⊢ A ⊑ᶜ ★
ground⇒cast⊑★ cΓ (｀ α) p =
  resource⇒⊑ᶜ★′ (seal-resource cΓ α) p
ground⇒cast⊑★ cΓ (‵ ι) p =
  ⊑ᶜ-tag p (‵ ι) tt
ground⇒cast⊑★ cΓ ★⇒★ p =
  ⊑ᶜ-tag p ★⇒★ tt

ground⇒cast⊒★ :
  ∀ {Γ Σ Φ A G} →
  CastCtx Γ Σ Φ →
  Ground G →
  Σ ∣ Φ ⊢ interp Γ G ⊒ᶜ A →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ A
ground⇒cast⊒★ cΓ (｀ α) p =
  resource⇒⊒ᶜ★′ (seal-resource cΓ α) p
ground⇒cast⊒★ cΓ (‵ ι) p =
  ⊒ᶜ-untag (‵ ι) tt zero p
ground⇒cast⊒★ cΓ ★⇒★ p =
  ⊒ᶜ-untag ★⇒★ tt zero p

------------------------------------------------------------------------
-- Directional aliases and the intended bridge statement
------------------------------------------------------------------------

infix 4 _⊢_⊒ᵢ_
_⊢_⊒ᵢ_ : ICtx → Ty → Ty → Set
Γ ⊢ A ⊒ᵢ B = Γ ⊢ B ⊑ᵢ A

mutual
  interpSeal-ν-source-at :
    ∀ k Γ α →
    interpSeal (plains k (ν-bound ∷ Γ)) α ≡
    suc (interpSeal (plains k (plain ∷ Γ)) α)
  interpSeal-ν-source-at zero Γ α = refl
  interpSeal-ν-source-at (suc k) Γ α =
    interpSeal-ν-source-at k Γ α

  interpVar-ν-source-at :
    ∀ k Γ X →
    interpVar (plains k (ν-bound ∷ Γ)) X ≡
    substᵗ (substVarFrom k α₀)
      (⇑ˢ (interpVar (plains k (plain ∷ Γ)) X))
  interpVar-ν-source-at zero Γ zero = refl
  interpVar-ν-source-at zero Γ (suc X) =
    sym
      (trans
        (cong
          (λ C → C [ α₀ ]ᵗ)
          (sym (renameᵗ-⇑ˢ suc (interpVar Γ X))))
        (open-renᵗ-suc (⇑ˢ (interpVar Γ X)) α₀))
  interpVar-ν-source-at (suc k) Γ zero = refl
  interpVar-ν-source-at (suc k) Γ (suc X) =
    sym
      (trans
        (cong
          (substᵗ (substVarFrom (suc k) α₀))
          (sym (renameᵗ-⇑ˢ suc
            (interpVar (plains k (plain ∷ Γ)) X))))
        (trans
          (substVarFrom-⇑ᵗ k α₀
            (⇑ˢ (interpVar (plains k (plain ∷ Γ)) X)))
          (cong ⇑ᵗ (sym (interpVar-ν-source-at k Γ X)))))

  interp-ν-source-at :
    ∀ k Γ A →
    interp (plains k (ν-bound ∷ Γ)) A ≡
    substᵗ (substVarFrom k α₀)
      (⇑ˢ (interp (plains k (plain ∷ Γ)) A))
  interp-ν-source-at k Γ (＇ X) = interpVar-ν-source-at k Γ X
  interp-ν-source-at k Γ (｀ α) =
    cong ｀_ (interpSeal-ν-source-at k Γ α)
  interp-ν-source-at k Γ (‵ ι) = refl
  interp-ν-source-at k Γ ★ = refl
  interp-ν-source-at k Γ (A ⇒ B) =
    cong₂ _⇒_ (interp-ν-source-at k Γ A) (interp-ν-source-at k Γ B)
  interp-ν-source-at k Γ (`∀ A) =
    cong `∀ (interp-ν-source-at (suc k) Γ A)

-- Replacing the `∀`-bound plain variable by the ν-introduced seal commutes
-- with the indexed-imprecision interpretation.
interp-ν-source :
  ∀ Γ A →
  interp (ν-bound ∷ Γ) A ≡
  (⇑ˢ (interp (plain ∷ Γ) A)) [ α₀ ]ᵗ
interp-ν-source = interp-ν-source-at zero

mutual
  interpSeal-ν-target-at :
    ∀ k Γ α →
    interpSeal (plains k (ν-bound ∷ Γ)) α ≡
    suc (interpSeal (plains k Γ) α)
  interpSeal-ν-target-at zero Γ α = refl
  interpSeal-ν-target-at (suc k) Γ α =
    interpSeal-ν-target-at k Γ α

  interpVar-ν-target-at :
    ∀ k Γ X →
    interpVar (plains k (ν-bound ∷ Γ)) (raiseVarFrom k X) ≡
    ⇑ˢ (interpVar (plains k Γ) X)
  interpVar-ν-target-at zero Γ X = refl
  interpVar-ν-target-at (suc k) Γ zero = refl
  interpVar-ν-target-at (suc k) Γ (suc X) =
    trans
      (cong ⇑ᵗ (interpVar-ν-target-at k Γ X))
      (renameᵗ-⇑ˢ suc (interpVar (plains k Γ) X))

  interp-ν-target-at :
    ∀ k Γ B →
    interp (plains k (ν-bound ∷ Γ)) (renameᵗ (raiseVarFrom k) B) ≡
    ⇑ˢ (interp (plains k Γ) B)
  interp-ν-target-at k Γ (＇ X) = interpVar-ν-target-at k Γ X
  interp-ν-target-at k Γ (｀ α) =
    cong ｀_ (interpSeal-ν-target-at k Γ α)
  interp-ν-target-at k Γ (‵ ι) = refl
  interp-ν-target-at k Γ ★ = refl
  interp-ν-target-at k Γ (A ⇒ B) =
    cong₂ _⇒_ (interp-ν-target-at k Γ A) (interp-ν-target-at k Γ B)
  interp-ν-target-at k Γ (`∀ A) =
    cong `∀
      (trans
        (cong
          (interp (plains (suc k) (ν-bound ∷ Γ)))
          (renameᵗ-cong (raise-ext k) A))
        (interp-ν-target-at (suc k) Γ A))

-- The right side of an imprecision ν premise is the seal lift of the outer
-- target after interpretation.
interp-ν-target :
  ∀ Γ B →
  interp (ν-bound ∷ Γ) (⇑ᵗ B) ≡ ⇑ˢ (interp Γ B)
interp-ν-target = interp-ν-target-at zero

mutual
  imprecision⇒cast⊑ :
    ∀ {Γ Σ Φ A B} →
    CastCtx Γ Σ Φ →
    Γ ⊢ A ⊑ᵢ B →
    Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B
  imprecision⇒cast⊑ cΓ ⊑ₒ-★★ = ⊑ᶜ-id (wfTySome ★)
  imprecision⇒cast⊑ cΓ (⊑ₒ-★ν xν) with ν-var-resource cΓ xν
  imprecision⇒cast⊑ cΓ (⊑ₒ-★ν xν) | α , eq , r =
    ⊑ᶜ-cast (sym eq) refl (resource⇒⊑ᶜ★ r)
  imprecision⇒cast⊑ cΓ (⊑ₒ-★ A G g p) =
    ground⇒cast⊑★ cΓ g (imprecision⇒cast⊑ cΓ p)
  imprecision⇒cast⊑ cΓ (⊑ₒ-＇ x∈) =
    ⊑ᶜ-id (wfTySome _)
  imprecision⇒cast⊑ cΓ (⊑ₒ-｀ α) =
    ⊑ᶜ-id (wfTySome _)
  imprecision⇒cast⊑ cΓ (⊑ₒ-‵ ι) =
    ⊑ᶜ-id (wfTySome _)
  imprecision⇒cast⊑ cΓ (⊑ₒ-⇒ A A′ B B′ p q) =
    ⊑ᶜ-⇒ (imprecision⇒cast⊒ cΓ p) (imprecision⇒cast⊑ cΓ q)
  imprecision⇒cast⊑ cΓ (⊑ₒ-∀ A B p) =
    ⊑ᶜ-∀ (imprecision⇒cast⊑ (cast-plain cΓ) p)
  imprecision⇒cast⊑ {Γ = Γ} cΓ (⊑ₒ-ν A B occ p) =
    ⊑ᶜ-ν
      (trans (interp-plain-occurs-zero Γ A) occ)
      (⊑ᶜ-cast
        (interp-ν-source Γ A)
        (interp-ν-target Γ B)
        (imprecision⇒cast⊑ (cast-ν-seal cΓ) p))

  imprecision⇒cast⊒ :
    ∀ {Γ Σ Φ A B} →
    CastCtx Γ Σ Φ →
    Γ ⊢ A ⊒ᵢ B →
    Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B
  imprecision⇒cast⊒ cΓ ⊑ₒ-★★ = ⊒ᶜ-id (wfTySome ★)
  imprecision⇒cast⊒ cΓ (⊑ₒ-★ν xν) with ν-var-resource cΓ xν
  imprecision⇒cast⊒ cΓ (⊑ₒ-★ν xν) | α , eq , r =
    ⊒ᶜ-cast refl (sym eq) (resource⇒⊒ᶜ★ r)
  imprecision⇒cast⊒ cΓ (⊑ₒ-★ A G g p) =
    ground⇒cast⊒★ cΓ g (imprecision⇒cast⊒ cΓ p)
  imprecision⇒cast⊒ cΓ (⊑ₒ-＇ x∈) =
    ⊒ᶜ-id (wfTySome _)
  imprecision⇒cast⊒ cΓ (⊑ₒ-｀ α) =
    ⊒ᶜ-id (wfTySome _)
  imprecision⇒cast⊒ cΓ (⊑ₒ-‵ ι) =
    ⊒ᶜ-id (wfTySome _)
  imprecision⇒cast⊒ cΓ (⊑ₒ-⇒ A A′ B B′ p q) =
    ⊒ᶜ-⇒ (imprecision⇒cast⊑ cΓ p) (imprecision⇒cast⊒ cΓ q)
  imprecision⇒cast⊒ cΓ (⊑ₒ-∀ A B p) =
    ⊒ᶜ-∀ (imprecision⇒cast⊒ (cast-plain cΓ) p)
  imprecision⇒cast⊒ {Γ = Γ} cΓ (⊑ₒ-ν A B occ p) =
    ⊒ᶜ-ν
      (trans (interp-plain-occurs-zero Γ A) occ)
      (⊒ᶜ-cast
        (interp-ν-target Γ B)
        (interp-ν-source Γ A)
        (imprecision⇒cast⊒ (cast-ν-tag cΓ) p))

-- The only `⊑ᶜ` rules that can derive `_ ⊑ᶜ ｀ α` are `⊑ᶜ-seal`, `⊑ᶜ-id`,
-- and `⊑ᶜ-ν`. The first two pin the LHS to `｀ α`; the third pins it to a
-- universal. All other rules end at `★`, an arrow, or a `∀`, so are ruled
-- out by the indexed return type.
⊑ᶜ-→｀-shape :
  ∀ {Σ Φ A α} →
  Σ ∣ Φ ⊢ A ⊑ᶜ ｀ α →
  (A ≡ ｀ α) ⊎ (∃[ A′ ] A ≡ `∀ A′)
⊑ᶜ-→｀-shape (⊑ᶜ-seal _) = inj₁ refl
⊑ᶜ-→｀-shape (⊑ᶜ-ν {A = A′} _ _) = inj₂ (A′ , refl)
⊑ᶜ-→｀-shape (⊑ᶜ-id _) = inj₁ refl

-- Cast-shape inversion at base ground `‵ ι`: only `⊑ᶜ-id` (forcing `A ≡ ‵ ι`)
-- and `⊑ᶜ-ν` (forcing `A ≡ `∀ A′`) reach this shape.
⊑ᶜ-→‵-shape :
  ∀ {Σ Φ A ι} →
  Σ ∣ Φ ⊢ A ⊑ᶜ ‵ ι →
  (A ≡ ‵ ι) ⊎ (∃[ A′ ] A ≡ `∀ A′)
⊑ᶜ-→‵-shape (⊑ᶜ-ν {A = A′} _ _) = inj₂ (A′ , refl)
⊑ᶜ-→‵-shape (⊑ᶜ-id _) = inj₁ refl

-- Cast-shape inversion at an arrow type: covered by `⊑ᶜ-id` (forcing
-- `A ≡ B ⇒ C`), `⊑ᶜ-⇒` (any arrow source), or `⊑ᶜ-ν` (`∀ A′`).
⊑ᶜ-→⇒-shape :
  ∀ {Σ Φ A B C} →
  Σ ∣ Φ ⊢ A ⊑ᶜ B ⇒ C →
  (A ≡ B ⇒ C) ⊎ (∃[ A₁ ] ∃[ A₂ ] A ≡ A₁ ⇒ A₂) ⊎ (∃[ A′ ] A ≡ `∀ A′)
⊑ᶜ-→⇒-shape (⊑ᶜ-⇒ {A = A₁} {B = A₂} _ _) = inj₂ (inj₁ (A₁ , A₂ , refl))
⊑ᶜ-→⇒-shape (⊑ᶜ-ν {A = A′} _ _) = inj₂ (inj₂ (A′ , refl))
⊑ᶜ-→⇒-shape (⊑ᶜ-id _) = inj₁ refl

-- `renameᵗ ρ T ≡ ★` forces `T ≡ ★` (similarly for `renameˢ`). Used to push
-- `★` through the lifted-context layers in `interpVar`.
renameᵗ-≡-★ : ∀ {ρ T} → renameᵗ ρ T ≡ ★ → T ≡ ★
renameᵗ-≡-★ {T = ＇ X} ()
renameᵗ-≡-★ {T = ｀ α} ()
renameᵗ-≡-★ {T = ‵ ι} ()
renameᵗ-≡-★ {T = ★} refl = refl
renameᵗ-≡-★ {T = A ⇒ B} ()
renameᵗ-≡-★ {T = `∀ A} ()

renameˢ-≡-★ : ∀ {ρ T} → renameˢ ρ T ≡ ★ → T ≡ ★
renameˢ-≡-★ {T = ＇ X} ()
renameˢ-≡-★ {T = ｀ α} ()
renameˢ-≡-★ {T = ‵ ι} ()
renameˢ-≡-★ {T = ★} refl = refl
renameˢ-≡-★ {T = A ⇒ B} ()
renameˢ-≡-★ {T = `∀ A} ()

-- `interpVar Γ X ≡ ★` is impossible: `interpVar` always returns a `＇`- or
-- `｀`-headed term (after iterated lifting).
interpVar-≢-★ : ∀ Γ X → interpVar Γ X ≡ ★ → ⊥
interpVar-≢-★ [] X ()
interpVar-≢-★ (plain ∷ Γ) zero ()
interpVar-≢-★ (plain ∷ Γ) (suc X) eq =
  interpVar-≢-★ Γ X (renameᵗ-≡-★ eq)
interpVar-≢-★ (ν-bound ∷ Γ) zero ()
interpVar-≢-★ (ν-bound ∷ Γ) (suc X) eq =
  interpVar-≢-★ Γ X (renameˢ-≡-★ eq)

-- Source-shape inversion: if `interp Γ A ≡ ★` then `A ≡ ★`. The `＇ X`
-- case routes through `interpVar-≢-★`; all others are direct.
interp-≡-★ : ∀ {Γ A} → interp Γ A ≡ ★ → A ≡ ★
interp-≡-★ {Γ = Γ} {A = ＇ X} eq = ⊥-elim (interpVar-≢-★ Γ X eq)
interp-≡-★ {A = ｀ α} ()
interp-≡-★ {A = ‵ ι} ()
interp-≡-★ {A = ★} refl = refl
interp-≡-★ {A = A ⇒ B} ()
interp-≡-★ {A = `∀ A} ()

-- Dual cast-shape inversion lemmas for `⊒ᶜ`. For `｀ α ⊒ᶜ A`, only
-- `⊒ᶜ-seal`, `⊒ᶜ-id`, and `⊒ᶜ-ν` (with arbitrary LHS) apply.
⊒ᶜ-｀→-shape :
  ∀ {Σ Φ A α} →
  Σ ∣ Φ ⊢ ｀ α ⊒ᶜ A →
  (A ≡ ｀ α) ⊎ (∃[ A′ ] A ≡ `∀ A′)
⊒ᶜ-｀→-shape (⊒ᶜ-seal _) = inj₁ refl
⊒ᶜ-｀→-shape (⊒ᶜ-ν {A = A′} _ _) = inj₂ (A′ , refl)
⊒ᶜ-｀→-shape (⊒ᶜ-id _) = inj₁ refl

⊒ᶜ-‵→-shape :
  ∀ {Σ Φ A ι} →
  Σ ∣ Φ ⊢ ‵ ι ⊒ᶜ A →
  (A ≡ ‵ ι) ⊎ (∃[ A′ ] A ≡ `∀ A′)
⊒ᶜ-‵→-shape (⊒ᶜ-ν {A = A′} _ _) = inj₂ (A′ , refl)
⊒ᶜ-‵→-shape (⊒ᶜ-id _) = inj₁ refl

⊒ᶜ-⇒→-shape :
  ∀ {Σ Φ A B C} →
  Σ ∣ Φ ⊢ B ⇒ C ⊒ᶜ A →
  (A ≡ B ⇒ C) ⊎ (∃[ A₁ ] ∃[ A₂ ] A ≡ A₁ ⇒ A₂) ⊎ (∃[ A′ ] A ≡ `∀ A′)
⊒ᶜ-⇒→-shape (⊒ᶜ-⇒ {A′ = A₁} {B′ = A₂} _ _) = inj₂ (inj₁ (A₁ , A₂ , refl))
⊒ᶜ-⇒→-shape (⊒ᶜ-ν {A = A′} _ _) = inj₂ (inj₂ (A′ , refl))
⊒ᶜ-⇒→-shape (⊒ᶜ-id _) = inj₁ refl

-- `interpSeal Γ` is injective in its `Seal` argument — it's `α + |ν-bound
-- prefix of Γ|`, so distinct source seals never collide on the cast side.
interpSeal-injective :
  ∀ Γ {α β} → interpSeal Γ α ≡ interpSeal Γ β → α ≡ β
interpSeal-injective [] eq = eq
interpSeal-injective (plain ∷ Γ) eq = interpSeal-injective Γ eq
interpSeal-injective (ν-bound ∷ Γ) {α} {β} eq =
  interpSeal-injective Γ (suc-injective eq)
  where
    suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

-- A `Clean`-marked seal cannot have a `SealResource`: cleanliness asserts
-- the seal has no permission, while a resource provides one.
clean-seal-no-resource :
  ∀ {Σ Φ α} →
  Clean Φ (｀ α) →
  SealResource Σ Φ α →
  ⊥
clean-seal-no-resource (α∉cast , _) (seal-cast _ α∈Φ) = α∉cast α∈Φ
clean-seal-no-resource (_ , α∉tag) (seal-tag α∈Φ) = α∉tag α∈Φ

-- `interpVar Γ X` is always `＇ _` (when X is plain) or `｀ _` (when X is
-- ν-bound), after iterated liftings. Stated as a sum of equalities so it can
-- be used as a `with` dispatch without tripping unification.
interpVar-shape :
  ∀ Γ X →
  (∃[ Y ] interpVar Γ X ≡ ＇ Y) ⊎ (∃[ α ] interpVar Γ X ≡ ｀ α)
interpVar-shape [] X = inj₁ (X , refl)
interpVar-shape (plain ∷ Γ) zero = inj₁ (zero , refl)
interpVar-shape (plain ∷ Γ) (suc X) with interpVar-shape Γ X
... | inj₁ (Y , eq) = inj₁ (suc Y , cong ⇑ᵗ eq)
... | inj₂ (α , eq) = inj₂ (α , cong ⇑ᵗ eq)
interpVar-shape (ν-bound ∷ Γ) zero = inj₂ (zero , refl)
interpVar-shape (ν-bound ∷ Γ) (suc X) with interpVar-shape Γ X
... | inj₁ (Y , eq) = inj₁ (Y , cong ⇑ˢ eq)
... | inj₂ (α , eq) = inj₂ (suc α , cong ⇑ˢ eq)

-- Discriminator function for ruling out cross-constructor `Ty` equalities.
-- Computing it gives the head constructor as a tag; pulling it through `≡`
-- via `cong`/`subst` makes Agda's coverage checker happy in the `interp-≡-_`
-- family, where direct `()` on `＇/｀ ≡ ‵/⇒/∀/｀` gets blocked by metavariable
-- universe inference.
data TyHead : Set where
  hVar hSeal hBase hStar hArrow hAll : TyHead

ty-head : Ty → TyHead
ty-head (＇ _) = hVar
ty-head (｀ _) = hSeal
ty-head (‵ _) = hBase
ty-head ★ = hStar
ty-head (_ ⇒ _) = hArrow
ty-head (`∀ _) = hAll

-- Source-shape inversions for the remaining ground constructors. Each is
-- structurally the same as `interp-≡-★`: source variables route through
-- `interpVar-shape` to derive contradictions; all other branches are
-- absurd-by-constructor.
interp-≡-‵ : ∀ {Γ A ι} → interp Γ A ≡ ‵ ι → A ≡ ‵ ι
interp-≡-‵ {Γ = Γ} {A = ＇ X} eq with interpVar-shape Γ X
... | inj₁ (Y , vEq) =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where
    head-mismatch : hVar ≡ hBase → ⊥
    head-mismatch ()
... | inj₂ (α , vEq) =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where
    head-mismatch : hSeal ≡ hBase → ⊥
    head-mismatch ()
interp-≡-‵ {A = ｀ α} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where
    head-mismatch : hSeal ≡ hBase → ⊥
    head-mismatch ()
interp-≡-‵ {A = ‵ ι} refl = refl
interp-≡-‵ {A = ★} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where
    head-mismatch : hStar ≡ hBase → ⊥
    head-mismatch ()
interp-≡-‵ {A = A ⇒ B} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where
    head-mismatch : hArrow ≡ hBase → ⊥
    head-mismatch ()
interp-≡-‵ {A = `∀ A} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where
    head-mismatch : hAll ≡ hBase → ⊥
    head-mismatch ()

interp-≡-⇒ :
  ∀ {Γ A B C} →
  interp Γ A ≡ B ⇒ C →
  ∃[ A₁ ] ∃[ A₂ ] (A ≡ A₁ ⇒ A₂ × interp Γ A₁ ≡ B × interp Γ A₂ ≡ C)
interp-≡-⇒ {Γ = Γ} {A = ＇ X} eq with interpVar-shape Γ X
... | inj₁ (Y , vEq) =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where
    head-mismatch : hVar ≡ hArrow → ⊥
    head-mismatch ()
... | inj₂ (α , vEq) =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where
    head-mismatch : hSeal ≡ hArrow → ⊥
    head-mismatch ()
interp-≡-⇒ {A = ｀ α} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hSeal ≡ hArrow → ⊥
        head-mismatch ()
interp-≡-⇒ {A = ‵ ι} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hBase ≡ hArrow → ⊥
        head-mismatch ()
interp-≡-⇒ {A = ★} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hStar ≡ hArrow → ⊥
        head-mismatch ()
interp-≡-⇒ {A = A₁ ⇒ A₂} refl = A₁ , A₂ , refl , refl , refl
interp-≡-⇒ {A = `∀ A} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hAll ≡ hArrow → ⊥
        head-mismatch ()

interp-≡-∀ :
  ∀ {Γ A B} →
  interp Γ A ≡ `∀ B →
  ∃[ A′ ] (A ≡ `∀ A′ × interp (plain ∷ Γ) A′ ≡ B)
interp-≡-∀ {Γ = Γ} {A = ＇ X} eq with interpVar-shape Γ X
... | inj₁ (Y , vEq) =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where head-mismatch : hVar ≡ hAll → ⊥
        head-mismatch ()
... | inj₂ (α , vEq) =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where head-mismatch : hSeal ≡ hAll → ⊥
        head-mismatch ()
interp-≡-∀ {A = ｀ α} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hSeal ≡ hAll → ⊥
        head-mismatch ()
interp-≡-∀ {A = ‵ ι} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hBase ≡ hAll → ⊥
        head-mismatch ()
interp-≡-∀ {A = ★} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hStar ≡ hAll → ⊥
        head-mismatch ()
interp-≡-∀ {A = A ⇒ B} eq = ⊥-elim (head-mismatch (cong ty-head eq))
  where head-mismatch : hArrow ≡ hAll → ⊥
        head-mismatch ()
interp-≡-∀ {A = `∀ A} refl = A , refl , refl

-- Source-shape inversion at a seal `｀ α`: source is either a `｀ β` whose
-- `interpSeal` value is `α`, or a ν-bound variable whose `interpVar` is
-- `｀ α` (the latter is ruled out by `Clean Φ (｀ α)` at the call site).
data InterpSealSource (Γ : ICtx) (α : Seal) (A : Ty) : Set where
  isFromSeal : ∀ β → A ≡ ｀ β → interpSeal Γ β ≡ α → InterpSealSource Γ α A
  isFromν    : ∀ X → A ≡ ＇ X → Γ ∋ X ∶ ν-bound → interpVar Γ X ≡ ｀ α →
               InterpSealSource Γ α A

interp-≡-｀ :
  ∀ {Γ Ψ A α} →
  WfTy (length Γ) Ψ A →
  interp Γ A ≡ ｀ α →
  InterpSealSource Γ α A
interp-≡-｀ {Γ = Γ} (wfVar X<Γ) eq with lookup-mode Γ _ X<Γ
... | plain , x∈ with plain-var-image x∈
... | _ , vEq =
  ⊥-elim (head-mismatch (cong ty-head (trans (sym vEq) eq)))
  where head-mismatch : hVar ≡ hSeal → ⊥
        head-mismatch ()
interp-≡-｀ (wfVar X<Γ) eq | ν-bound , x∈ = isFromν _ refl x∈ eq
interp-≡-｀ (wfSeal {α = β} _) refl = isFromSeal β refl refl
interp-≡-｀ wfBase ()
interp-≡-｀ wf★ ()
interp-≡-｀ (wf⇒ _ _) ()
interp-≡-｀ (wf∀ _) ()

-- Left inverse of `interp Γ` on the `Clean`-supported subset. Total in
-- `T : Ty`; the `(ν-bound ∷ Γ) zero` clause for `un-interpSeal` returns
-- garbage that `Clean` rules out reaching at any actual interp image.
un-interpVarPlain : ICtx → TyVar → TyVar
un-interpVarPlain [] Y = Y
un-interpVarPlain (plain ∷ Γ) zero = zero
un-interpVarPlain (plain ∷ Γ) (suc Y) = suc (un-interpVarPlain Γ Y)
un-interpVarPlain (ν-bound ∷ Γ) Y = suc (un-interpVarPlain Γ Y)

un-interpSeal : ICtx → Seal → Seal
un-interpSeal [] α = α
un-interpSeal (plain ∷ Γ) α = un-interpSeal Γ α
un-interpSeal (ν-bound ∷ Γ) zero = zero
un-interpSeal (ν-bound ∷ Γ) (suc α) = un-interpSeal Γ α

un-interp : ICtx → Ty → Ty
un-interp Γ (＇ Y) = ＇ (un-interpVarPlain Γ Y)
un-interp Γ (｀ α) = ｀ (un-interpSeal Γ α)
un-interp Γ (‵ ι) = ‵ ι
un-interp Γ ★ = ★
un-interp Γ (A ⇒ B) = un-interp Γ A ⇒ un-interp Γ B
un-interp Γ (`∀ A) = `∀ (un-interp (plain ∷ Γ) A)

-- Round-trip on the seal layer: `un-interpSeal Γ` undoes `interpSeal Γ`.
un-interpSeal-roundtrip : ∀ Γ β → un-interpSeal Γ (interpSeal Γ β) ≡ β
un-interpSeal-roundtrip [] β = refl
un-interpSeal-roundtrip (plain ∷ Γ) β = un-interpSeal-roundtrip Γ β
un-interpSeal-roundtrip (ν-bound ∷ Γ) β = un-interpSeal-roundtrip Γ β

-- Round-trip on plain variables: `interpVar` lands in `＇ Y` for some `Y`,
-- and `un-interpVarPlain` recovers the original `X`.
un-interpVarPlain-roundtrip :
  ∀ {Γ X} →
  (x∈ : Γ ∋ X ∶ plain) →
  ∃[ Y ] (interpVar Γ X ≡ ＇ Y × un-interpVarPlain Γ Y ≡ X)
un-interpVarPlain-roundtrip here = zero , refl , refl
un-interpVarPlain-roundtrip (there {m′ = plain} x'∈)
    with un-interpVarPlain-roundtrip x'∈
... | Y' , vEq , uEq =
  suc Y' , cong ⇑ᵗ vEq , cong suc uEq
un-interpVarPlain-roundtrip (there {m′ = ν-bound} x'∈)
    with un-interpVarPlain-roundtrip x'∈
... | Y' , vEq , uEq =
  Y' , cong ⇑ˢ vEq , cong suc uEq

-- The main round-trip: `un-interp Γ (interp Γ A) ≡ A` whenever `Clean`
-- holds on the interpretation. The ν-bound `wfVar` subcase is ruled out
-- by `clean-seal-no-resource` because ν-binders inject permissions.
un-interp-correct :
  ∀ {Γ Σ Φ Ψ A} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A →
  Clean Φ (interp Γ A) →
  un-interp Γ (interp Γ A) ≡ A
un-interp-correct {Γ = Γ} cΓ (wfVar X<Γ) cleanA
    with lookup-mode Γ _ X<Γ
... | plain , x∈ with un-interpVarPlain-roundtrip x∈
... | _ , vEq , uEq =
  trans (cong (un-interp Γ) vEq) (cong ＇_ uEq)
un-interp-correct cΓ (wfVar X<Γ) cleanA | ν-bound , x∈
    with ν-var-resource cΓ x∈
... | _ , vEq , r =
  ⊥-elim (clean-seal-no-resource (subst (Clean _) vEq cleanA) r)
un-interp-correct {Γ = Γ} cΓ (wfSeal {α = β} _) _ =
  cong ｀_ (un-interpSeal-roundtrip Γ β)
un-interp-correct cΓ wfBase _ = refl
un-interp-correct cΓ wf★ _ = refl
un-interp-correct cΓ (wf⇒ wfA wfB) (cleanA , cleanB) =
  cong₂ _⇒_
    (un-interp-correct cΓ wfA cleanA)
    (un-interp-correct cΓ wfB cleanB)
un-interp-correct cΓ (wf∀ wfA) cleanA =
  cong `∀ (un-interp-correct (cast-plain cΓ) wfA cleanA)

-- Source-injectivity of `interp` under `Clean`: by sandwiching `interpEq`
-- between two round-trips. The Clean precondition for A is transferred
-- from B's via the equality.
clean-interp-injective :
  ∀ {Γ Σ Φ Ψ A B} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A →
  WfTy (length Γ) Ψ B →
  Clean Φ (interp Γ B) →
  interp Γ A ≡ interp Γ B →
  A ≡ B
clean-interp-injective {Γ = Γ} cΓ wfA wfB cleanB interpEq =
  trans (sym (un-interp-correct cΓ wfA
                (subst (Clean _) (sym interpEq) cleanB)))
        (trans (cong (un-interp Γ) interpEq)
               (un-interp-correct cΓ wfB cleanB))

-- The cast-side endpoint `｀ α` reflects back to a source-side reason for
-- `A ⊑ᵢ ★`. This is the shared subroutine used by both
-- `cast⇒imprecision⊑-seal★-hole` (where `α ∈cast Φ` plus a store witness give
-- `seal-cast`) and the `g = ｀ α` branch of
-- `cast⇒imprecision⊑-ground★-hole` (where `α ∈tag Φ` gives `seal-tag`).
seal-source⊑ᵢ★ :
  ∀ {Γ Σ Φ Ψ A α} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ ｀ α →
  Γ ⊢ A ⊑ᵢ ★
seal-source⊑ᵢ★ cΓ (wfVar X<Γ) r p with lookup-mode _ _ X<Γ
seal-source⊑ᵢ★ cΓ (wfVar X<Γ) r p | plain , x∈
    with plain-var-image x∈
seal-source⊑ᵢ★ cΓ (wfVar X<Γ) r p | plain , x∈ | Y , eq
    with ⊑ᶜ-→｀-shape (subst (λ T → _ ∣ _ ⊢ T ⊑ᶜ _) eq p)
seal-source⊑ᵢ★ cΓ (wfVar X<Γ) r p | plain , x∈ | Y , eq | inj₁ ()
seal-source⊑ᵢ★ cΓ (wfVar X<Γ) r p | plain , x∈ | Y , eq | inj₂ (_ , ())
seal-source⊑ᵢ★ cΓ (wfVar X<Γ) r p | ν-bound , x∈ = ⊑ᵢ-★ν x∈
seal-source⊑ᵢ★ {α = α} cΓ (wfSeal {α = β} _) r p =
  ⊑ᵢ-★ (｀ β) (｀ β) (｀ β) (⊑ᵢ-｀ β)
seal-source⊑ᵢ★ cΓ wfBase r p with ⊑ᶜ-→｀-shape p
seal-source⊑ᵢ★ cΓ wfBase r p | inj₁ ()
seal-source⊑ᵢ★ cΓ wfBase r p | inj₂ (_ , ())
seal-source⊑ᵢ★ cΓ wf★ r p = ⊑ᵢ-★★
seal-source⊑ᵢ★ cΓ (wf⇒ wfA wfB) r p with ⊑ᶜ-→｀-shape p
seal-source⊑ᵢ★ cΓ (wf⇒ wfA wfB) r p | inj₁ ()
seal-source⊑ᵢ★ cΓ (wf⇒ wfA wfB) r p | inj₂ (_ , ())
seal-source⊑ᵢ★ {Γ = Γ} cΓ (wf∀ {A = A} wfA) r (⊑ᶜ-ν occ p′) =
  ⊑ᵢ-ν A ★
    (trans (sym (interp-plain-occurs-zero Γ A)) occ)
    (seal-source⊑ᵢ★
      (cast-ν-seal cΓ)
      wfA
      (lift-seal-resourceˢ-seal r)
      (⊑ᶜ-cast (sym (interp-ν-source Γ A)) refl p′))

-- Dual of `seal-source⊑ᵢ★`: from a cast-side seal `｀ α` reaching the
-- interpreted source via `⊒ᶜ`, recover `Γ ⊢ B ⊑ᵢ ★`. Same case structure;
-- the `wf∀` recursion uses `cast-ν-tag` (matching `⊒ᶜ-ν`'s lifted permission).
seal-source★⊒ᵢ :
  ∀ {Γ Σ Φ Ψ B α} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ B →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ ｀ α ⊒ᶜ interp Γ B →
  Γ ⊢ B ⊑ᵢ ★
seal-source★⊒ᵢ cΓ (wfVar X<Γ) r p with lookup-mode _ _ X<Γ
seal-source★⊒ᵢ cΓ (wfVar X<Γ) r p | plain , x∈
    with plain-var-image x∈
seal-source★⊒ᵢ cΓ (wfVar X<Γ) r p | plain , x∈ | Y , eq
    with ⊒ᶜ-｀→-shape (subst (λ T → _ ∣ _ ⊢ _ ⊒ᶜ T) eq p)
seal-source★⊒ᵢ cΓ (wfVar X<Γ) r p | plain , x∈ | Y , eq | inj₁ ()
seal-source★⊒ᵢ cΓ (wfVar X<Γ) r p | plain , x∈ | Y , eq | inj₂ (_ , ())
seal-source★⊒ᵢ cΓ (wfVar X<Γ) r p | ν-bound , x∈ = ⊑ᵢ-★ν x∈
seal-source★⊒ᵢ cΓ (wfSeal {α = β} _) r p =
  ⊑ᵢ-★ (｀ β) (｀ β) (｀ β) (⊑ᵢ-｀ β)
seal-source★⊒ᵢ cΓ wfBase r p with ⊒ᶜ-｀→-shape p
seal-source★⊒ᵢ cΓ wfBase r p | inj₁ ()
seal-source★⊒ᵢ cΓ wfBase r p | inj₂ (_ , ())
seal-source★⊒ᵢ cΓ wf★ r p = ⊑ᵢ-★★
seal-source★⊒ᵢ cΓ (wf⇒ wfA wfB) r p with ⊒ᶜ-｀→-shape p
seal-source★⊒ᵢ cΓ (wf⇒ wfA wfB) r p | inj₁ ()
seal-source★⊒ᵢ cΓ (wf⇒ wfA wfB) r p | inj₂ (_ , ())
seal-source★⊒ᵢ {Γ = Γ} cΓ (wf∀ {A = B} wfB) r (⊒ᶜ-ν occ p′) =
  ⊑ᵢ-ν B ★
    (trans (sym (interp-plain-occurs-zero Γ B)) occ)
    (seal-source★⊒ᵢ
      (cast-ν-tag cΓ)
      wfB
      (lift-seal-resourceˢ-tag r)
      (⊒ᶜ-cast refl (sym (interp-ν-source Γ B)) p′))

mutual
  cast⇒imprecision⊑ :
    ∀ {Γ Σ Φ Ψ A B A′ B′} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    WfTy (length Γ) Ψ B →
    Clean Φ (interp Γ B) →
    A′ ≡ interp Γ A →
    B′ ≡ interp Γ B →
    Σ ∣ Φ ⊢ A′ ⊑ᶜ B′ →
    Γ ⊢ A ⊑ᵢ B
  -- ⊑ᶜ-tag forces the cast's RHS to ★. By interp-≡-★, the source B = ★
  -- (with eqB and wfB refining accordingly under the `with`-rewrite).
  cast⇒imprecision⊑ {B = B} cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-tag p g ok)
      with interp-≡-★ {A = B} (sym eqB)
  ... | refl =
    cast⇒imprecision⊑-ground★-hole cΓ wfA g ok (⊑ᶜ-cast eqA refl p)
  -- ⊑ᶜ-unseal★ likewise forces RHS = ★.
  cast⇒imprecision⊑ {B = B} cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-unseal★ p h α∈Φ)
      with interp-≡-★ {A = B} (sym eqB)
  ... | refl =
    cast⇒imprecision⊑-seal★-hole cΓ wfA (⊑ᶜ-cast eqA refl p) h α∈Φ
  cast⇒imprecision⊑ cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-seal α) =
    cast⇒imprecision⊑-seal-id-hole cΓ wfA wfB cleanB eqA eqB refl refl
  -- ⊑ᶜ-⇒ forces both sides to be arrows. Use interp-≡-⇒ to refine A and B,
  -- then pattern-match wfA, wfB, cleanB on the arrow shape.
  cast⇒imprecision⊑ {A = A} {B = B} cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-⇒ p q)
      with interp-≡-⇒ {A = A} (sym eqA) | interp-≡-⇒ {A = B} (sym eqB)
  ... | A₁ , A₂ , refl , eqA₁ , eqA₂ | B₁ , B₂ , refl , eqB₁ , eqB₂
      with wfA | wfB | cleanB
  ... | wf⇒ wfA₁ wfA₂ | wf⇒ wfB₁ wfB₂ | cleanB₁ , cleanB₂ =
    ⊑ᵢ-⇒ A₁ B₁ A₂ B₂
      (cast⇒imprecision⊒ cΓ wfB₁ wfA₁ cleanB₁
        (sym eqB₁) (sym eqA₁) p)
      (cast⇒imprecision⊑ cΓ wfA₂ wfB₂ cleanB₂
        (sym eqA₂) (sym eqB₂) q)
  -- ⊑ᶜ-∀ forces both sides `∀-shaped.
  cast⇒imprecision⊑ {A = A} {B = B} cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-∀ p)
      with interp-≡-∀ {A = A} (sym eqA) | interp-≡-∀ {A = B} (sym eqB)
  ... | A_src , refl , eqA' | B_src , refl , eqB'
      with wfA | wfB
  ... | wf∀ wfA_src | wf∀ wfB_src =
    ⊑ᵢ-∀ A_src B_src
      (cast⇒imprecision⊑ (cast-plain cΓ) wfA_src wfB_src cleanB
        (sym eqA') (sym eqB') p)
  -- ⊑ᶜ-ν forces LHS source to be `∀ A_src.
  cast⇒imprecision⊑ {Γ = Γ} {A = A} {B = B} cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-ν occ p)
      with interp-≡-∀ {A = A} (sym eqA)
  ... | A_src , refl , interpA-eq
      with wfA
  ... | wf∀ wfA_src =
    ⊑ᵢ-ν A_src B
      (trans (sym (interp-plain-occurs-zero Γ A_src))
             (subst (λ T → occurs zero T ≡ true) (sym interpA-eq) occ))
      (cast⇒imprecision⊑
        (cast-ν-seal cΓ)
        wfA_src
        (renameᵗ-preserves-WfTy wfB TyRenameWf-suc)
        (subst (Clean _) (sym (interp-ν-target Γ B))
          (Clean-⇑ˢ {A = interp Γ B} {b = cast-seal} cleanB))
        refl refl
        (⊑ᶜ-cast
          (trans (sym (cong (λ T → (⇑ˢ T) [ α₀ ]ᵗ) interpA-eq))
                 (sym (interp-ν-source Γ A_src)))
          (trans (cong ⇑ˢ eqB)
                 (sym (interp-ν-target Γ B)))
          p))
  cast⇒imprecision⊑ cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-id x) =
    cast⇒imprecision⊑-id-hole cΓ wfA wfB cleanB eqA eqB refl

  -- Dual of `cast⇒imprecision⊑`. Carries `A′ B′` equality bridges so the
  -- constructor pattern matches don't get stuck on `interp` applications.
  cast⇒imprecision⊒ :
    ∀ {Γ Σ Φ Ψ A B A′ B′} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    WfTy (length Γ) Ψ B →
    Clean Φ (interp Γ A) →
    A′ ≡ interp Γ A →
    B′ ≡ interp Γ B →
    Σ ∣ Φ ⊢ A′ ⊒ᶜ B′ →
    Γ ⊢ A ⊒ᵢ B
  -- ⊒ᶜ-untag forces the cast's LHS to ★. By interp-≡-★, A = ★.
  cast⇒imprecision⊒ {A = A} cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-untag g ok ℓ p)
      with interp-≡-★ {A = A} (sym eqA)
  ... | refl =
    cast⇒imprecision⊒-ground★-hole cΓ wfB g ok (⊒ᶜ-cast refl eqB p)
  -- ⊒ᶜ-seal★ likewise forces LHS = ★.
  cast⇒imprecision⊒ {A = A} cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-seal★ p h α∈Φ)
      with interp-≡-★ {A = A} (sym eqA)
  ... | refl =
    cast⇒imprecision⊒-seal★-hole cΓ wfB (⊒ᶜ-cast refl eqB p) h α∈Φ
  -- ⊒ᶜ-seal: both sides ｀ α. Reduce to identity via clean-interp-injective.
  cast⇒imprecision⊒ cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-seal α)
      with clean-interp-injective cΓ wfB wfA cleanA (trans (sym eqB) eqA)
  ... | refl = clean-reflᵢ cΓ wfA cleanA
  -- ⊒ᶜ-⇒ forces both sides to be arrows. Mirror of the ⊑ᶜ-⇒ clause; the
  -- arrow's first arg flips to ⊑ direction (cast⇒imprecision⊑).
  cast⇒imprecision⊒ {A = A} {B = B} cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-⇒ p q)
      with interp-≡-⇒ {A = A} (sym eqA) | interp-≡-⇒ {A = B} (sym eqB)
  ... | A₁ , A₂ , refl , eqA₁ , eqA₂ | B₁ , B₂ , refl , eqB₁ , eqB₂
      with wfA | wfB | cleanA
  ... | wf⇒ wfA₁ wfA₂ | wf⇒ wfB₁ wfB₂ | cleanA₁ , cleanA₂ =
    ⊑ᵢ-⇒ B₁ A₁ B₂ A₂
      (cast⇒imprecision⊑ cΓ wfB₁ wfA₁ cleanA₁
        (sym eqB₁) (sym eqA₁) p)
      (cast⇒imprecision⊒ cΓ wfA₂ wfB₂ cleanA₂
        (sym eqA₂) (sym eqB₂) q)
  -- ⊒ᶜ-∀ forces both sides `∀-shaped.
  cast⇒imprecision⊒ {A = A} {B = B} cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-∀ p)
      with interp-≡-∀ {A = A} (sym eqA) | interp-≡-∀ {A = B} (sym eqB)
  ... | A_src , refl , interpA-eq | B_src , refl , interpB-eq
      with wfA | wfB
  ... | wf∀ wfA_src | wf∀ wfB_src =
    ⊑ᵢ-∀ B_src A_src
      (cast⇒imprecision⊒ (cast-plain cΓ) wfA_src wfB_src cleanA
        (sym interpA-eq) (sym interpB-eq) p)
  -- ⊒ᶜ-ν forces RHS source to be `∀ B_src; LHS source A is unconstrained.
  cast⇒imprecision⊒ {Γ = Γ} {A = A} {B = B}
      cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-ν occ p)
      with interp-≡-∀ {A = B} (sym eqB)
  ... | B_src , refl , interpB-eq
      with wfB
  ... | wf∀ wfB_src =
    ⊑ᵢ-ν B_src A
      (trans (sym (interp-plain-occurs-zero Γ B_src))
             (subst (λ T → occurs zero T ≡ true) (sym interpB-eq) occ))
      (cast⇒imprecision⊒
        (cast-ν-tag cΓ)
        (renameᵗ-preserves-WfTy wfA TyRenameWf-suc)
        wfB_src
        (subst (Clean _) (sym (interp-ν-target Γ A))
          (Clean-⇑ˢ {A = interp Γ A} {b = cast-tag} cleanA))
        (trans (cong ⇑ˢ eqA)
               (sym (interp-ν-target Γ A)))
        (trans (sym (cong (λ T → (⇑ˢ T) [ α₀ ]ᵗ) interpB-eq))
               (sym (interp-ν-source Γ B_src)))
        p)
  -- ⊒ᶜ-id: A′ ≡ B′. Combined with eqA, eqB, gives interp Γ A ≡ interp Γ B.
  cast⇒imprecision⊒ cΓ wfA wfB cleanA eqA eqB (⊒ᶜ-id _)
      with clean-interp-injective cΓ wfB wfA cleanA (trans (sym eqB) eqA)
  ... | refl = clean-reflᵢ cΓ wfA cleanA

  -- The `g = ｀ α` case is closed via `seal-source⊑ᵢ★`. The `g = ‵ ι` and
  -- `g = ★⇒★` cases need direct cast-derivation inversion (NOT a recursive
  -- call to `cast⇒imprecision⊑` with the same `p` — that does not decrease
  -- structurally and would loop the termination checker).
  cast⇒imprecision⊑-ground★-hole :
    ∀ {Γ Σ Φ Ψ A G} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    (g : Ground G) →
    ⊢ g ok Φ →
    Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ G →
    Γ ⊢ A ⊑ᵢ ★
  cast⇒imprecision⊑-ground★-hole cΓ wfA (｀ α) ok p =
    seal-source⊑ᵢ★ cΓ wfA (seal-tag ok) p
  -- Base ground `‵ ι`. Only `wfBase` (via `⊑ᶜ-id`) or `wf∀` (via `⊑ᶜ-ν`)
  -- can supply a derivation; all other source shapes give an interpretation
  -- that has no `⊑ᶜ` rule reaching `‵ ι`.
  cast⇒imprecision⊑-ground★-hole cΓ wfBase (‵ ι) tt (⊑ᶜ-id _) =
    ⊑ᵢ-★ (‵ ι) (‵ ι) (‵ ι) (⊑ᵢ-‵ ι)
  cast⇒imprecision⊑-ground★-hole {Γ = Γ}
      cΓ (wf∀ {A = A} wfA) (‵ ι) tt (⊑ᶜ-ν occ p′) =
    ⊑ᵢ-ν A ★
      (trans (sym (interp-plain-occurs-zero Γ A)) occ)
      (cast⇒imprecision⊑-ground★-hole
        (cast-ν-seal cΓ)
        wfA
        (‵ ι)
        tt
        (⊑ᶜ-cast (sym (interp-ν-source Γ A)) refl p′))
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p
      with lookup-mode Γ _ X<Γ
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈
      with plain-var-image x∈
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈ | _ , vEq
      with ⊑ᶜ-→‵-shape (subst (λ T → Σ ∣ Φ ⊢ T ⊑ᶜ ‵ ι) vEq p)
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈ | _ , vEq | inj₂ (_ , ())
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈
      with ν-var-image x∈
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈ | _ , vEq
      with ⊑ᶜ-→‵-shape (subst (λ T → Σ ∣ Φ ⊢ T ⊑ᶜ ‵ ι) vEq p)
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ} cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈ | _ , vEq | inj₂ (_ , ())
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) (‵ ι) tt p with ⊑ᶜ-→‵-shape p
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) (‵ ι) tt p | inj₁ ()
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) (‵ ι) tt p | inj₂ (_ , ())
  cast⇒imprecision⊑-ground★-hole cΓ wf★ (‵ ι) tt p with ⊑ᶜ-→‵-shape p
  cast⇒imprecision⊑-ground★-hole cΓ wf★ (‵ ι) tt p | inj₁ ()
  cast⇒imprecision⊑-ground★-hole cΓ wf★ (‵ ι) tt p | inj₂ (_ , ())
  cast⇒imprecision⊑-ground★-hole cΓ (wf⇒ _ _) (‵ ι) tt p with ⊑ᶜ-→‵-shape p
  cast⇒imprecision⊑-ground★-hole cΓ (wf⇒ _ _) (‵ ι) tt p | inj₁ ()
  cast⇒imprecision⊑-ground★-hole cΓ (wf⇒ _ _) (‵ ι) tt p | inj₂ (_ , ())

  -- Arrow ground `★ ⇒ ★`. To avoid Agda's `--without-K` unifier getting
  -- stuck on `interp Γ A_i ≡ ★`, we abstract the interp calls via
  -- `with ... in ...`, pattern-match the cast on the abstracted shape, then
  -- recover `A_i ≡ ★` via `interp-≡-★`.
  cast⇒imprecision⊑-ground★-hole {Γ = Γ}
      cΓ (wf⇒ {A = A₁} {B = A₂} wfA₁ wfA₂) ★⇒★ tt p
      with interp Γ A₁ in eqA₁ | interp Γ A₂ in eqA₂
  cast⇒imprecision⊑-ground★-hole {Γ = Γ}
      cΓ (wf⇒ {A = A₁} {B = A₂} wfA₁ wfA₂) ★⇒★ tt (⊑ᶜ-⇒ p₁ p₂)
      | A₁′ | A₂′ =
    ⊑ᵢ-★ (A₁ ⇒ A₂) (★ ⇒ ★) ★⇒★
      (⊑ᵢ-⇒ A₁ ★ A₂ ★
        (cast⇒imprecision⊒ cΓ wf★ wfA₁ tt refl (sym eqA₁) p₁)
        (cast⇒imprecision⊑ cΓ wfA₂ wf★ tt refl refl
          (subst (λ T → _ ∣ _ ⊢ T ⊑ᶜ ★) (sym eqA₂) p₂)))
  cast⇒imprecision⊑-ground★-hole {Γ = Γ}
      cΓ (wf⇒ {A = A₁} {B = A₂} wfA₁ wfA₂) ★⇒★ tt (⊑ᶜ-id _)
      | .★ | .★ =
    subst (λ X → _ ⊢ X ⇒ A₂ ⊑ᵢ ★) (sym (interp-≡-★ eqA₁))
      (subst (λ Y → _ ⊢ ★ ⇒ Y ⊑ᵢ ★) (sym (interp-≡-★ eqA₂))
        (⊑ᵢ-★ (★ ⇒ ★) (★ ⇒ ★) ★⇒★ (⊑ᵢ-⇒ ★ ★ ★ ★ ⊑ᵢ-★★ ⊑ᵢ-★★)))
  cast⇒imprecision⊑-ground★-hole {Γ = Γ}
      cΓ (wf∀ {A = A} wfA) ★⇒★ tt (⊑ᶜ-ν occ p′) =
    ⊑ᵢ-ν A ★
      (trans (sym (interp-plain-occurs-zero Γ A)) occ)
      (cast⇒imprecision⊑-ground★-hole
        (cast-ν-seal cΓ)
        wfA
        ★⇒★
        tt
        (⊑ᶜ-cast (sym (interp-ν-source Γ A)) refl p′))
  -- Other `wfA` shapes interpret to `＇/｀/‵/★`, none reach `★ ⇒ ★`.
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p
      with lookup-mode Γ _ X<Γ
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈
      with plain-var-image x∈
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq
      with ⊑ᶜ-→⇒-shape (subst (λ T → Σ ∣ Φ ⊢ T ⊑ᶜ ★ ⇒ ★) vEq p)
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈
      with ν-var-image x∈
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq
      with ⊑ᶜ-→⇒-shape (subst (λ T → Σ ∣ Φ ⊢ T ⊑ᶜ ★ ⇒ ★) vEq p)
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊑-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) ★⇒★ tt p with ⊑ᶜ-→⇒-shape p
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) ★⇒★ tt p | inj₁ ()
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) ★⇒★ tt p | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊑-ground★-hole cΓ (wfSeal _) ★⇒★ tt p | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊑-ground★-hole cΓ wfBase ★⇒★ tt p with ⊑ᶜ-→⇒-shape p
  cast⇒imprecision⊑-ground★-hole cΓ wfBase ★⇒★ tt p | inj₁ ()
  cast⇒imprecision⊑-ground★-hole cΓ wfBase ★⇒★ tt p | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊑-ground★-hole cΓ wfBase ★⇒★ tt p | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊑-ground★-hole cΓ wf★ ★⇒★ tt p with ⊑ᶜ-→⇒-shape p
  cast⇒imprecision⊑-ground★-hole cΓ wf★ ★⇒★ tt p | inj₁ ()
  cast⇒imprecision⊑-ground★-hole cΓ wf★ ★⇒★ tt p | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊑-ground★-hole cΓ wf★ ★⇒★ tt p | inj₂ (inj₂ (_ , ()))

  -- Closed via `seal-source⊑ᵢ★` once the store witness `h : Σ ∋ˢ α ⦂ ★` is
  -- threaded through (it lives in the `⊑ᶜ-unseal★` constructor at the call
  -- site and is now passed as the extra argument).
  cast⇒imprecision⊑-seal★-hole :
    ∀ {Γ Σ Φ Ψ A α} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ ｀ α →
    Σ ∋ˢ α ⦂ ★ →
    α ∈cast Φ →
    Γ ⊢ A ⊑ᵢ ★
  cast⇒imprecision⊑-seal★-hole cΓ wfA p h α∈Φ =
    seal-source⊑ᵢ★ cΓ wfA (seal-cast h α∈Φ) p

  cast⇒imprecision⊑-seal-id-hole :
    ∀ {Γ Σ Φ Ψ A B A′ B′ α} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    WfTy (length Γ) Ψ B →
    Clean Φ (interp Γ B) →
    A′ ≡ interp Γ A →
    B′ ≡ interp Γ B →
    A′ ≡ ｀ α →
    B′ ≡ ｀ α →
    Γ ⊢ A ⊑ᵢ B
  -- Both endpoints are the same seal `｀ α`; delegate to `id-hole` which
  -- needs only the equality `A′ ≡ B′` (here `refl` after `srcSeal/tgtSeal`).
  cast⇒imprecision⊑-seal-id-hole cΓ wfA wfB cleanB eqA eqB refl refl =
    cast⇒imprecision⊑-id-hole cΓ wfA wfB cleanB eqA eqB refl

  cast⇒imprecision⊑-id-hole :
    ∀ {Γ Σ Φ Ψ A B A′ B′} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    WfTy (length Γ) Ψ B →
    Clean Φ (interp Γ B) →
    A′ ≡ interp Γ A →
    B′ ≡ interp Γ B →
    A′ ≡ B′ →
    Γ ⊢ A ⊑ᵢ B
  -- Use `clean-interp-injective` to collapse `A ≡ B`, then close with
  -- `clean-reflᵢ`. Match `eqA refl` and `eqB refl` so `interpEq` has type
  -- `interp Γ A ≡ interp Γ B`, which we feed to the injectivity lemma.
  cast⇒imprecision⊑-id-hole cΓ wfA wfB cleanB refl refl interpEq
      with clean-interp-injective cΓ wfA wfB cleanB interpEq
  ... | refl = clean-reflᵢ cΓ wfA cleanB

  -- Dual of `cast⇒imprecision⊑-ground★-hole`. Same structure: route
  -- `g = ｀ α` through `seal-source★⊒ᵢ`; for `g = ‵ ι` and `g = ★⇒★`,
  -- pattern-match the cast directly to keep recursion structurally founded.
  cast⇒imprecision⊒-ground★-hole :
    ∀ {Γ Σ Φ Ψ B G} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ B →
    (g : Ground G) →
    ⊢ g ok Φ →
    Σ ∣ Φ ⊢ G ⊒ᶜ interp Γ B →
    Γ ⊢ ★ ⊒ᵢ B
  cast⇒imprecision⊒-ground★-hole cΓ wfB (｀ α) ok p =
    seal-source★⊒ᵢ cΓ wfB (seal-tag ok) p
  -- Base ground `‵ ι`.
  cast⇒imprecision⊒-ground★-hole cΓ wfBase (‵ ι) tt (⊒ᶜ-id _) =
    ⊑ᵢ-★ (‵ ι) (‵ ι) (‵ ι) (⊑ᵢ-‵ ι)
  cast⇒imprecision⊒-ground★-hole {Γ = Γ}
      cΓ (wf∀ {A = B} wfB) (‵ ι) tt (⊒ᶜ-ν occ p′) =
    ⊑ᵢ-ν B ★
      (trans (sym (interp-plain-occurs-zero Γ B)) occ)
      (cast⇒imprecision⊒-ground★-hole
        (cast-ν-tag cΓ)
        wfB
        (‵ ι)
        tt
        (⊒ᶜ-cast refl (sym (interp-ν-source Γ B)) p′))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p
      with lookup-mode Γ _ X<Γ
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈
      with plain-var-image x∈
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈ | _ , vEq
      with ⊒ᶜ-‵→-shape (subst (λ T → Σ ∣ Φ ⊢ ‵ ι ⊒ᶜ T) vEq p)
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | plain , x∈ | _ , vEq | inj₂ (_ , ())
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈
      with ν-var-image x∈
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈ | _ , vEq
      with ⊒ᶜ-‵→-shape (subst (λ T → Σ ∣ Φ ⊢ ‵ ι ⊒ᶜ T) vEq p)
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) (‵ ι) tt p | ν-bound , x∈ | _ , vEq | inj₂ (_ , ())
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) (‵ ι) tt p with ⊒ᶜ-‵→-shape p
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) (‵ ι) tt p | inj₁ ()
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) (‵ ι) tt p | inj₂ (_ , ())
  cast⇒imprecision⊒-ground★-hole cΓ wf★ (‵ ι) tt p with ⊒ᶜ-‵→-shape p
  cast⇒imprecision⊒-ground★-hole cΓ wf★ (‵ ι) tt p | inj₁ ()
  cast⇒imprecision⊒-ground★-hole cΓ wf★ (‵ ι) tt p | inj₂ (_ , ())
  cast⇒imprecision⊒-ground★-hole cΓ (wf⇒ _ _) (‵ ι) tt p with ⊒ᶜ-‵→-shape p
  cast⇒imprecision⊒-ground★-hole cΓ (wf⇒ _ _) (‵ ι) tt p | inj₁ ()
  cast⇒imprecision⊒-ground★-hole cΓ (wf⇒ _ _) (‵ ι) tt p | inj₂ (_ , ())
  -- Arrow ground `★ ⇒ ★`. Same `with ... in ...` + `interp-≡-★` workaround
  -- as the ⊑ direction for the `wf⇒ + ⊒ᶜ-id` subcase.
  cast⇒imprecision⊒-ground★-hole {Γ = Γ}
      cΓ (wf⇒ {A = B₁} {B = B₂} wfB₁ wfB₂) ★⇒★ tt p
      with interp Γ B₁ in eqB₁ | interp Γ B₂ in eqB₂
  cast⇒imprecision⊒-ground★-hole {Γ = Γ}
      cΓ (wf⇒ {A = B₁} {B = B₂} wfB₁ wfB₂) ★⇒★ tt (⊒ᶜ-⇒ p₁ p₂)
      | B₁′ | B₂′ =
    ⊑ᵢ-★ (B₁ ⇒ B₂) (★ ⇒ ★) ★⇒★
      (⊑ᵢ-⇒ B₁ ★ B₂ ★
        (cast⇒imprecision⊑ cΓ wfB₁ wf★ tt refl refl
          (subst (λ T → _ ∣ _ ⊢ T ⊑ᶜ ★) (sym eqB₁) p₁))
        (cast⇒imprecision⊒ cΓ wf★ wfB₂ tt refl (sym eqB₂) p₂))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ}
      cΓ (wf⇒ {A = B₁} {B = B₂} wfB₁ wfB₂) ★⇒★ tt (⊒ᶜ-id _)
      | .★ | .★ =
    subst (λ X → _ ⊢ X ⇒ B₂ ⊑ᵢ ★) (sym (interp-≡-★ eqB₁))
      (subst (λ Y → _ ⊢ ★ ⇒ Y ⊑ᵢ ★) (sym (interp-≡-★ eqB₂))
        (⊑ᵢ-★ (★ ⇒ ★) (★ ⇒ ★) ★⇒★ (⊑ᵢ-⇒ ★ ★ ★ ★ ⊑ᵢ-★★ ⊑ᵢ-★★)))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ}
      cΓ (wf∀ {A = B} wfB) ★⇒★ tt (⊒ᶜ-ν occ p′) =
    ⊑ᵢ-ν B ★
      (trans (sym (interp-plain-occurs-zero Γ B)) occ)
      (cast⇒imprecision⊒-ground★-hole
        (cast-ν-tag cΓ)
        wfB
        ★⇒★
        tt
        (⊒ᶜ-cast refl (sym (interp-ν-source Γ B)) p′))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p
      with lookup-mode Γ _ X<Γ
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈
      with plain-var-image x∈
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq
      with ⊒ᶜ-⇒→-shape (subst (λ T → Σ ∣ Φ ⊢ ★ ⇒ ★ ⊒ᶜ T) vEq p)
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | plain , x∈ | _ , vEq | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈
      with ν-var-image x∈
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq
      with ⊒ᶜ-⇒→-shape (subst (λ T → Σ ∣ Φ ⊢ ★ ⇒ ★ ⊒ᶜ T) vEq p)
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq | inj₁ ()
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊒-ground★-hole {Γ = Γ} {Σ = Σ} {Φ = Φ}
      cΓ (wfVar X<Γ) ★⇒★ tt p | ν-bound , x∈ | _ , vEq | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) ★⇒★ tt p with ⊒ᶜ-⇒→-shape p
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) ★⇒★ tt p | inj₁ ()
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) ★⇒★ tt p | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊒-ground★-hole cΓ (wfSeal _) ★⇒★ tt p | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊒-ground★-hole cΓ wfBase ★⇒★ tt p with ⊒ᶜ-⇒→-shape p
  cast⇒imprecision⊒-ground★-hole cΓ wfBase ★⇒★ tt p | inj₁ ()
  cast⇒imprecision⊒-ground★-hole cΓ wfBase ★⇒★ tt p | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊒-ground★-hole cΓ wfBase ★⇒★ tt p | inj₂ (inj₂ (_ , ()))
  cast⇒imprecision⊒-ground★-hole cΓ wf★ ★⇒★ tt p with ⊒ᶜ-⇒→-shape p
  cast⇒imprecision⊒-ground★-hole cΓ wf★ ★⇒★ tt p | inj₁ ()
  cast⇒imprecision⊒-ground★-hole cΓ wf★ ★⇒★ tt p | inj₂ (inj₁ (_ , _ , ()))
  cast⇒imprecision⊒-ground★-hole cΓ wf★ ★⇒★ tt p | inj₂ (inj₂ (_ , ()))

  -- Closed via `seal-source★⊒ᵢ` once the store witness `h : Σ ∋ˢ α ⦂ ★` is
  -- threaded through (it lives in the `⊒ᶜ-seal★` constructor).
  cast⇒imprecision⊒-seal★-hole :
    ∀ {Γ Σ Φ Ψ B α} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ B →
    Σ ∣ Φ ⊢ ｀ α ⊒ᶜ interp Γ B →
    Σ ∋ˢ α ⦂ ★ →
    α ∈cast Φ →
    Γ ⊢ ★ ⊒ᵢ B
  cast⇒imprecision⊒-seal★-hole cΓ wfB p h α∈Φ =
    seal-source★⊒ᵢ cΓ wfB (seal-cast h α∈Φ) p

record ImprecisionCastIso
    (Γ : ICtx) (Σ : Store) (Φ : List CastPerm) (A B : Ty) : Set where
  constructor iso
  field
    ctx-ok : CastCtx Γ Σ Φ
    to-cast-⊑ : Γ ⊢ A ⊑ᵢ B → Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B
    from-cast-⊑ :
      ∀ {Ψ} →
      WfTy (length Γ) Ψ A →
      WfTy (length Γ) Ψ B →
      Clean Φ (interp Γ B) →
      Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B →
      Γ ⊢ A ⊑ᵢ B
    to-cast-⊒ : Γ ⊢ A ⊒ᵢ B → Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B
    from-cast-⊒ :
      ∀ {Ψ} →
      WfTy (length Γ) Ψ A →
      WfTy (length Γ) Ψ B →
      Clean Φ (interp Γ A) →
      Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B →
      Γ ⊢ A ⊒ᵢ B

mkIso :
  ∀ {Γ Σ Φ A B} →
  CastCtx Γ Σ Φ →
  ImprecisionCastIso Γ Σ Φ A B
mkIso cΓ =
  iso
    cΓ
    (imprecision⇒cast⊑ cΓ)
    (λ wfA wfB cleanB p →
      cast⇒imprecision⊑ cΓ wfA wfB cleanB refl refl p)
    (imprecision⇒cast⊒ cΓ)
    (λ wfA wfB cleanA p →
      cast⇒imprecision⊒ cΓ wfA wfB cleanA refl refl p)

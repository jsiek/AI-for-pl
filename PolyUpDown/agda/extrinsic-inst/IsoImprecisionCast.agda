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
    )
open import Cast
open import ImprecisionIndexed
open import Store using (renameLookupᵗ)
open import TypeProperties
  using (renameLookupˢ; renameᵗ-⇑ˢ; open-renᵗ-suc)
open import TypeCheckDec using (raiseVarFrom)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

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

------------------------------------------------------------------------
-- The top ν-bound variable can cast to/from ★ using either permission.
------------------------------------------------------------------------

ν-zero-⊑ᶜ★ :
  ∀ {Γ Σ Φ} →
  CastCtx (ν-bound ∷ Γ) Σ Φ →
  Σ ∣ Φ ⊢ ｀ zero ⊑ᶜ ★
ν-zero-⊑ᶜ★ (cast-ν-seal cΓ) =
  ⊑ᶜ-unseal★ (Z∋ˢ refl refl) here-cast-only
ν-zero-⊑ᶜ★ (cast-ν-tag cΓ) =
  ⊑ᶜ-tag (｀ zero) here-tag-only

ν-zero-⊒ᶜ★ :
  ∀ {Γ Σ Φ} →
  CastCtx (ν-bound ∷ Γ) Σ Φ →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ ｀ zero
ν-zero-⊒ᶜ★ (cast-ν-seal cΓ) =
  ⊒ᶜ-seal★ (Z∋ˢ refl refl) here-cast-only
ν-zero-⊒ᶜ★ (cast-ν-tag cΓ) =
  ⊒ᶜ-untag (｀ zero) here-tag-only zero

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

resource⇒⊑ᶜ★ :
  ∀ {Σ Φ α} →
  SealResource Σ Φ α →
  Σ ∣ Φ ⊢ ｀ α ⊑ᶜ ★
resource⇒⊑ᶜ★ (seal-cast h α∈Φ) = ⊑ᶜ-unseal★ h α∈Φ
resource⇒⊑ᶜ★ (seal-tag α∈Φ) = ⊑ᶜ-tag (｀ _) α∈Φ

ground⇒cast⊑★ :
  ∀ {Γ Σ Φ G} →
  CastCtx Γ Σ Φ →
  Ground G →
  Σ ∣ Φ ⊢ interp Γ G ⊑ᶜ ★
ground⇒cast⊑★ cΓ (｀ α) = resource⇒⊑ᶜ★ (seal-resource cΓ α)
ground⇒cast⊑★ cΓ (‵ ι) = ⊑ᶜ-tag (‵ ι) tt
ground⇒cast⊑★ cΓ ★⇒★ = ⊑ᶜ-tag ★⇒★ tt

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

postulate
  imprecision⇒cast⊒ :
    ∀ {Γ Σ Φ A B} →
    CastCtx Γ Σ Φ →
    Γ ⊢ A ⊒ᵢ B →
    Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B

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
  imprecision⇒cast⊑ cΓ p ；⊑ᶜ ground⇒cast⊑★ cΓ g
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
    (⊑ᶜ-cast
      (interp-ν-source Γ A)
      (interp-ν-target Γ B)
      (imprecision⇒cast⊑ (cast-ν-seal cΓ) p))

postulate
  cast⇒imprecision⊑ :
    ∀ {Γ Σ Φ A B} →
    CastCtx Γ Σ Φ →
    Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B →
    Γ ⊢ A ⊑ᵢ B

  cast⇒imprecision⊒ :
    ∀ {Γ Σ Φ A B} →
    CastCtx Γ Σ Φ →
    Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B →
    Γ ⊢ A ⊒ᵢ B

record ImprecisionCastIso
    (Γ : ICtx) (Σ : Store) (Φ : List CastPerm) (A B : Ty) : Set where
  constructor iso
  field
    ctx-ok : CastCtx Γ Σ Φ
    to-cast-⊑ : Γ ⊢ A ⊑ᵢ B → Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B
    from-cast-⊑ : Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B → Γ ⊢ A ⊑ᵢ B
    to-cast-⊒ : Γ ⊢ A ⊒ᵢ B → Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B
    from-cast-⊒ : Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B → Γ ⊢ A ⊒ᵢ B

mkIso :
  ∀ {Γ Σ Φ A B} →
  CastCtx Γ Σ Φ →
  ImprecisionCastIso Γ Σ Φ A B
mkIso cΓ =
  iso
    cΓ
    (imprecision⇒cast⊑ cΓ)
    (cast⇒imprecision⊑ cΓ)
    (imprecision⇒cast⊒ cΓ)
    (cast⇒imprecision⊒ cΓ)

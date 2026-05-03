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

cast⇒imprecision⊑-ground★-hole :
  ∀ {Γ Σ Φ Ψ A} {G : Ty} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A →
  Ground G →
  Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ G →
  Γ ⊢ A ⊑ᵢ ★
cast⇒imprecision⊑-ground★-hole cΓ wfA g p =
  -- Missing reflection: recover `Gᵢ` and `Ground Gᵢ` from a cast-side ground
  -- `G`, then show `interp Γ Gᵢ ≡ G`.
  {!!}

cast⇒imprecision⊑-seal★-hole :
  ∀ {Γ Σ Φ Ψ A α} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A →
  Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ ｀ α →
  α ∈cast Φ →
  Γ ⊢ A ⊑ᵢ ★
cast⇒imprecision⊑-seal★-hole cΓ wfA p α∈Φ =
  -- Missing reflection: decide whether `｀ α` comes from a ν-bound source
  -- variable, giving `⊑ᵢ-★ν`, or from an ordinary ground seal, giving
  -- `⊑ᵢ-★`.
  {!!}

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
cast⇒imprecision⊑-seal-id-hole cΓ wfA wfB cleanB eqA eqB srcSeal tgtSeal =
  -- Missing reflection: both interpreted endpoints are the same seal.
  -- We need to recover whether the source terms are equal concrete seals,
  -- plain variables, or impossible ν variables ruled out by `Clean`.
  {!!}

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
cast⇒imprecision⊑-id-hole cΓ wfA wfB cleanB eqA eqB interpEq =
  -- Missing equality reflection: clean, well-scoped interpreted equality
  -- should give indexed imprecision between the source types.
  {!!}

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
  cast⇒imprecision⊑ {A = A} {B = ★}
      cΓ wfA wf★ cleanB eqA refl (⊑ᶜ-tag p g ok) =
    cast⇒imprecision⊑-ground★-hole cΓ wfA g (⊑ᶜ-cast eqA refl p)
  cast⇒imprecision⊑ {A = A} {B = ★}
      cΓ wfA wf★ cleanB eqA refl (⊑ᶜ-unseal★ p h α∈Φ) =
    cast⇒imprecision⊑-seal★-hole cΓ wfA (⊑ᶜ-cast eqA refl p) α∈Φ
  cast⇒imprecision⊑ cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-seal α) =
    cast⇒imprecision⊑-seal-id-hole cΓ wfA wfB cleanB eqA eqB refl refl
  cast⇒imprecision⊑ {A = A₁ ⇒ B₁} {B = A₂ ⇒ B₂}
      cΓ (wf⇒ wfA₁ wfB₁) (wf⇒ wfA₂ wfB₂)
      (cleanA₂ , cleanB₂) refl refl (⊑ᶜ-⇒ p q) =
    ⊑ᵢ-⇒ A₁ A₂ B₁ B₂
      (cast⇒imprecision⊒ cΓ wfA₂ wfA₁ cleanA₂ p)
      (cast⇒imprecision⊑ cΓ wfB₁ wfB₂ cleanB₂ refl refl q)
  cast⇒imprecision⊑ {A = `∀ A} {B = `∀ B}
      cΓ (wf∀ wfA) (wf∀ wfB) cleanB refl refl (⊑ᶜ-∀ p) =
    ⊑ᵢ-∀ A B (cast⇒imprecision⊑ (cast-plain cΓ) wfA wfB cleanB refl refl p)
  cast⇒imprecision⊑ {Γ = Γ} {A = `∀ A} {B = B}
      cΓ (wf∀ wfA) wfB cleanB refl refl (⊑ᶜ-ν occ p) =
    ⊑ᵢ-ν A B (trans (sym (interp-plain-occurs-zero Γ A)) occ)
      (cast⇒imprecision⊑
        (cast-ν-seal cΓ)
        wfA
        (renameᵗ-preserves-WfTy wfB TyRenameWf-suc)
        (subst (Clean _) (sym (interp-ν-target Γ B))
          (Clean-⇑ˢ {A = interp Γ B} {b = cast-seal} cleanB))
        refl refl
        (⊑ᶜ-cast
          (sym (interp-ν-source Γ A))
          (sym (interp-ν-target Γ B))
          p))
  cast⇒imprecision⊑ cΓ wfA wfB cleanB eqA eqB (⊑ᶜ-id x) =
    cast⇒imprecision⊑-id-hole cΓ wfA wfB cleanB eqA eqB refl
  cast⇒imprecision⊑ cΓ wfA wfB cleanB eqA eqB p =
    -- Remaining endpoint-reflection cases, including shape mismatches and
    -- interpreted identity/seal cases.
    {!!}

  cast⇒imprecision⊒ :
    ∀ {Γ Σ Φ Ψ A B} →
    CastCtx Γ Σ Φ →
    WfTy (length Γ) Ψ A →
    WfTy (length Γ) Ψ B →
    Clean Φ (interp Γ A) →
    Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B →
    Γ ⊢ A ⊒ᵢ B
  cast⇒imprecision⊒ cΓ wfA wfB cleanA p =
    -- Dual main reflection hole.
    {!!}

cast⇒imprecision⊑-⇒-case :
  ∀ {Γ Σ Φ Ψ A₁ B₁ A₂ B₂} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A₁ →
  WfTy (length Γ) Ψ B₁ →
  WfTy (length Γ) Ψ A₂ →
  WfTy (length Γ) Ψ B₂ →
  Clean Φ (interp Γ A₂) →
  Clean Φ (interp Γ B₂) →
  Σ ∣ Φ ⊢ interp Γ A₂ ⊒ᶜ interp Γ A₁ →
  Σ ∣ Φ ⊢ interp Γ B₁ ⊑ᶜ interp Γ B₂ →
  Γ ⊢ (A₁ ⇒ B₁) ⊑ᵢ (A₂ ⇒ B₂)
cast⇒imprecision⊑-⇒-case cΓ wfA₁ wfB₁ wfA₂ wfB₂ cleanA₂ cleanB₂ p q =
  ⊑ᵢ-⇒ _ _ _ _
    (cast⇒imprecision⊒ cΓ wfA₂ wfA₁ cleanA₂ p)
    (cast⇒imprecision⊑ cΓ wfB₁ wfB₂ cleanB₂ refl refl q)

cast⇒imprecision⊒-⇒-case :
  ∀ {Γ Σ Φ Ψ A₁ B₁ A₂ B₂} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ A₁ →
  WfTy (length Γ) Ψ B₁ →
  WfTy (length Γ) Ψ A₂ →
  WfTy (length Γ) Ψ B₂ →
  Clean Φ (interp Γ A₁) →
  Clean Φ (interp Γ B₁) →
  Σ ∣ Φ ⊢ interp Γ A₂ ⊑ᶜ interp Γ A₁ →
  Σ ∣ Φ ⊢ interp Γ B₁ ⊒ᶜ interp Γ B₂ →
  Γ ⊢ (A₁ ⇒ B₁) ⊒ᵢ (A₂ ⇒ B₂)
cast⇒imprecision⊒-⇒-case cΓ wfA₁ wfB₁ wfA₂ wfB₂ cleanA₁ cleanB₁ p q =
  ⊑ᵢ-⇒ _ _ _ _
    (cast⇒imprecision⊑ cΓ wfA₂ wfA₁ cleanA₁ refl refl p)
    (cast⇒imprecision⊒ cΓ wfB₁ wfB₂ cleanB₁ q)

cast⇒imprecision⊑-∀-case :
  ∀ {Γ Σ Φ Ψ A B} →
  CastCtx Γ Σ Φ →
  WfTy (suc (length Γ)) Ψ A →
  WfTy (suc (length Γ)) Ψ B →
  Clean Φ (interp (plain ∷ Γ) B) →
  ⟰ᵗ Σ ∣ Φ ⊢ interp (plain ∷ Γ) A ⊑ᶜ interp (plain ∷ Γ) B →
  Γ ⊢ `∀ A ⊑ᵢ `∀ B
cast⇒imprecision⊑-∀-case cΓ wfA wfB cleanB p =
  ⊑ᵢ-∀ _ _ (cast⇒imprecision⊑ (cast-plain cΓ) wfA wfB cleanB refl refl p)

cast⇒imprecision⊒-∀-case :
  ∀ {Γ Σ Φ Ψ A B} →
  CastCtx Γ Σ Φ →
  WfTy (suc (length Γ)) Ψ A →
  WfTy (suc (length Γ)) Ψ B →
  Clean Φ (interp (plain ∷ Γ) A) →
  ⟰ᵗ Σ ∣ Φ ⊢ interp (plain ∷ Γ) A ⊒ᶜ interp (plain ∷ Γ) B →
  Γ ⊢ `∀ A ⊒ᵢ `∀ B
cast⇒imprecision⊒-∀-case cΓ wfA wfB cleanA p =
  ⊑ᵢ-∀ _ _ (cast⇒imprecision⊒ (cast-plain cΓ) wfA wfB cleanA p)

cast⇒imprecision⊑-ν-case :
  ∀ {Γ Σ Φ Ψ A B} →
  CastCtx Γ Σ Φ →
  .(occurs zero (interp (plain ∷ Γ) A) ≡ true) →
  WfTy (suc (length Γ)) Ψ A →
  WfTy (length Γ) Ψ B →
  Clean Φ (interp Γ B) →
  ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢
    (⇑ˢ (interp (plain ∷ Γ) A)) [ α₀ ]ᵗ ⊑ᶜ ⇑ˢ (interp Γ B) →
  Γ ⊢ `∀ A ⊑ᵢ B
cast⇒imprecision⊑-ν-case {Γ = Γ} {A = A} {B = B}
    cΓ occ wfA wfB cleanB p =
  ⊑ᵢ-ν A B (trans (sym (interp-plain-occurs-zero Γ A)) occ)
    (cast⇒imprecision⊑
      (cast-ν-seal cΓ)
      wfA
      (renameᵗ-preserves-WfTy wfB TyRenameWf-suc)
      (subst (Clean _) (sym (interp-ν-target Γ B))
        (Clean-⇑ˢ {A = interp Γ B} {b = cast-seal} cleanB))
        refl refl
      (⊑ᶜ-cast
        (sym (interp-ν-source Γ A))
        (sym (interp-ν-target Γ B))
        p))

cast⇒imprecision⊒-ν-case :
  ∀ {Γ Σ Φ Ψ A B} →
  CastCtx Γ Σ Φ →
  .(occurs zero (interp (plain ∷ Γ) A) ≡ true) →
  WfTy (suc (length Γ)) Ψ A →
  WfTy (length Γ) Ψ B →
  Clean Φ (interp Γ B) →
  ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢
    ⇑ˢ (interp Γ B) ⊒ᶜ (⇑ˢ (interp (plain ∷ Γ) A)) [ α₀ ]ᵗ →
  Γ ⊢ B ⊒ᵢ `∀ A
cast⇒imprecision⊒-ν-case {Γ = Γ} {A = A} {B = B}
    cΓ occ wfA wfB cleanB p =
  ⊑ᵢ-ν A B (trans (sym (interp-plain-occurs-zero Γ A)) occ)
    (cast⇒imprecision⊒
      (cast-ν-tag cΓ)
      (renameᵗ-preserves-WfTy wfB TyRenameWf-suc)
      wfA
      (subst (Clean _) (sym (interp-ν-target Γ B))
        (Clean-⇑ˢ {A = interp Γ B} {b = cast-tag} cleanB))
      (⊒ᶜ-cast
        (sym (interp-ν-target Γ B))
        (sym (interp-ν-source Γ A))
        p))

cast⇒imprecision⊒-ground★-hole :
  ∀ {Γ Σ Φ Ψ B} {G : Ty} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ B →
  Ground G →
  Σ ∣ Φ ⊢ G ⊒ᶜ interp Γ B →
  Γ ⊢ ★ ⊒ᵢ B
cast⇒imprecision⊒-ground★-hole cΓ wfB g p =
  -- Dual missing reflection for `⊒ᶜ-untag`: recover a source ground
  -- preimage of the cast-side ground `G`.
  {!!}

cast⇒imprecision⊒-seal★-hole :
  ∀ {Γ Σ Φ Ψ B α} →
  CastCtx Γ Σ Φ →
  WfTy (length Γ) Ψ B →
  Σ ∣ Φ ⊢ ｀ α ⊒ᶜ interp Γ B →
  α ∈cast Φ →
  Γ ⊢ ★ ⊒ᵢ B
cast⇒imprecision⊒-seal★-hole cΓ wfB p α∈Φ =
  -- Dual missing reflection for `⊒ᶜ-seal★`: decide whether the permissioned
  -- seal is a ν-bound variable preimage or an ordinary source seal.
  {!!}

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
    (cast⇒imprecision⊒ cΓ)

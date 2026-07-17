module proof.CastImprecision where

-- File Charter:
--   * Proof boundary for turning typed narrowing/widening casts into
--     duplicated-context `ImprecisionWf` edges.
--   * The local imprecision context is derived from the cast mode environment:
--     every in-scope variable has a reflexive `ˣ⊑ˣ` assumption, and variables
--     that may be introduced/eliminated by tag or seal casts also have a
--     `ˣ⊑★` assumption.
--   * Provides the one-sided transitivity principles needed to compose those
--     local edges with ambient Nu-term imprecision indices.
--   * Records why generic one-sided casts cannot cross a matched fresh-seal
--     boundary: it supplies `zero ˣ⊑ˣ zero`, not `zero ˣ⊑★`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; inspect; [_])
open import Relation.Nullary using (yes; no)

open import Types
open import Store using (bound)
open import Coercions using
  ( Coercion
  ; Mode
  ; ModeEnv
  ; id-only
  ; id-onlyᵈ
  ; tag-or-id
  ; seal-or-id
  ; extᵈ
  ; genᵈ
  ; instᵈ
  ; tagModeAllowed
  ; sealModeAllowed
  )
import Coercions as C
open import Imprecision using
  ( ImpCtx
  ; idᵢ
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import ImprecisionWf
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
import NarrowWiden as NW
open import TermTyping using (SealModeStore★)
open import proof.ImprecisionProperties using
  ( ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  ; ⇑ᴸᵢ-∈
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; un⇑ᴸᵢ-ˣ∈
  ; no-⇑ᴸᵢ-zero-left
  )
open import proof.NarrowWidenProperties as NWP
  using (StoreDetWf; StoreDetWf-⟰ᵗ; StoreDetWf-inst)
open import proof.StoreProperties using (∈-renameStoreᵗ)
open import proof.TypeProperties using (rename-raise-ext)

------------------------------------------------------------------------
-- Mode-derived imprecision context
------------------------------------------------------------------------

tailᵈ : ModeEnv → ModeEnv
tailᵈ μ X = μ (suc X)

modeStarAllowed : Mode → Bool
modeStarAllowed id-only = false
modeStarAllowed tag-or-id = true
modeStarAllowed seal-or-id = true

castᵢ : ModeEnv → TyCtx → ImpCtx
castᵢ μ zero = []
castᵢ μ (suc Δ) with μ zero
castᵢ μ (suc Δ) | id-only =
  (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (castᵢ (tailᵈ μ) Δ)
castᵢ μ (suc Δ) | tag-or-id =
  (zero ˣ⊑ˣ zero) ∷ (zero ˣ⊑★) ∷ ⇑ᵢ (castᵢ (tailᵈ μ) Δ)
castᵢ μ (suc Δ) | seal-or-id =
  (zero ˣ⊑ˣ zero) ∷ (zero ˣ⊑★) ∷ ⇑ᵢ (castᵢ (tailᵈ μ) Δ)

castᵢ-id-only-env :
  ∀ μ Δ →
  (∀ X → μ X ≡ id-only) →
  castᵢ μ Δ ≡ idᵢ Δ
castᵢ-id-only-env μ zero allId = refl
castᵢ-id-only-env μ (suc Δ) allId with μ zero | allId zero
castᵢ-id-only-env μ (suc Δ) allId | id-only | refl =
  cong ((zero ˣ⊑ˣ zero) ∷_)
    (cong ⇑ᵢ
      (castᵢ-id-only-env (tailᵈ μ) Δ (λ X → allId (suc X))))
castᵢ-id-only-env μ (suc Δ) allId | tag-or-id | ()
castᵢ-id-only-env μ (suc Δ) allId | seal-or-id | ()

castᵢ-id-only :
  ∀ Δ →
  castᵢ id-onlyᵈ Δ ≡ idᵢ Δ
castᵢ-id-only Δ = castᵢ-id-only-env id-onlyᵈ Δ (λ X → refl)

tagMode⇒starAllowed :
  ∀ {m} →
  tagModeAllowed m ≡ true →
  modeStarAllowed m ≡ true
tagMode⇒starAllowed {id-only} ()
tagMode⇒starAllowed {tag-or-id} refl = refl
tagMode⇒starAllowed {seal-or-id} ()

sealMode⇒starAllowed :
  ∀ {m} →
  sealModeAllowed m ≡ true →
  modeStarAllowed m ≡ true
sealMode⇒starAllowed {id-only} ()
sealMode⇒starAllowed {tag-or-id} ()
sealMode⇒starAllowed {seal-or-id} refl = refl

castᵢ-id-lookup :
  ∀ {μ Δ X} →
  X < Δ →
  (X ˣ⊑ˣ X) ∈ castᵢ μ Δ
castᵢ-id-lookup {Δ = zero} ()
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s
    with μ zero
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s
    | id-only = here refl
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s
    | tag-or-id = here refl
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s
    | seal-or-id = here refl
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ)
    with μ zero
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ)
    | id-only =
  there (⇑ᵢ-ˣ∈ (castᵢ-id-lookup {μ = tailᵈ μ} X<Δ))
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ)
    | tag-or-id =
  there (there (⇑ᵢ-ˣ∈ (castᵢ-id-lookup {μ = tailᵈ μ} X<Δ)))
castᵢ-id-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ)
    | seal-or-id =
  there (there (⇑ᵢ-ˣ∈ (castᵢ-id-lookup {μ = tailᵈ μ} X<Δ)))

castᵢ-star-lookup :
  ∀ {μ Δ X} →
  X < Δ →
  modeStarAllowed (μ X) ≡ true →
  (X ˣ⊑★) ∈ castᵢ μ Δ
castᵢ-star-lookup {Δ = zero} ()
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s ok
    with μ zero
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s ()
    | id-only
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s ok
    | tag-or-id = there (here refl)
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = zero} z<s ok
    | seal-or-id = there (here refl)
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ) ok
    with μ zero
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ) ok
    | id-only =
  there (⇑ᵢ-★∈ (castᵢ-star-lookup {μ = tailᵈ μ} X<Δ ok))
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ) ok
    | tag-or-id =
  there (there (⇑ᵢ-★∈ (castᵢ-star-lookup {μ = tailᵈ μ} X<Δ ok)))
castᵢ-star-lookup {μ = μ} {Δ = suc Δ} {X = suc X} (s<s X<Δ) ok
    | seal-or-id =
  there (there (⇑ᵢ-★∈ (castᵢ-star-lookup {μ = tailᵈ μ} X<Δ ok)))

castᵢ-var-identity :
  ∀ {μ Δ X Y} →
  (X ˣ⊑ˣ Y) ∈ castᵢ μ Δ →
  X ≡ Y
castᵢ-var-identity {Δ = zero} ()
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero} x∈
    with μ zero
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero}
    (here refl) | id-only = refl
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero}
    (there x∈) | id-only = ⊥-elim (no-⇑ᵢ-zero-left x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero}
    (here refl) | tag-or-id = refl
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero}
    (there (there x∈)) | tag-or-id = ⊥-elim (no-⇑ᵢ-zero-left x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero}
    (here refl) | seal-or-id = refl
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = zero}
    (there (there x∈)) | seal-or-id = ⊥-elim (no-⇑ᵢ-zero-left x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = suc Y} x∈
    with μ zero
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = suc Y}
    (there x∈) | id-only = ⊥-elim (no-⇑ᵢ-zero-left x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = suc Y}
    (there (there x∈)) | tag-or-id = ⊥-elim (no-⇑ᵢ-zero-left x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = zero} {Y = suc Y}
    (there (there x∈)) | seal-or-id = ⊥-elim (no-⇑ᵢ-zero-left x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = zero} x∈
    with μ zero
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = zero}
    (there x∈) | id-only = ⊥-elim (no-⇑ᵢ-zero-right x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = zero}
    (there (there x∈)) | tag-or-id = ⊥-elim (no-⇑ᵢ-zero-right x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = zero}
    (there (there x∈)) | seal-or-id = ⊥-elim (no-⇑ᵢ-zero-right x∈)
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = suc Y} x∈
    with μ zero
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = suc Y}
    (there x∈) | id-only =
  cong suc (castᵢ-var-identity {μ = tailᵈ μ} {Δ = Δ} (un⇑ᵢ-ˣ∈ x∈))
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = suc Y}
    (there (there x∈)) | tag-or-id =
  cong suc (castᵢ-var-identity {μ = tailᵈ μ} {Δ = Δ} (un⇑ᵢ-ˣ∈ x∈))
castᵢ-var-identity {μ = μ} {Δ = suc Δ} {X = suc X} {Y = suc Y}
    (there (there x∈)) | seal-or-id =
  cong suc (castᵢ-var-identity {μ = tailᵈ μ} {Δ = Δ} (un⇑ᵢ-ˣ∈ x∈))

castᵢ-star-allowed :
  ∀ {μ Δ X} →
  (X ˣ⊑★) ∈ castᵢ μ Δ →
  modeStarAllowed (μ X) ≡ true
castᵢ-star-allowed {Δ = zero} ()
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = zero} x∈
    with μ zero
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = zero}
    (there x∈) | id-only = ⊥-elim (no-⇑ᵢ-zero-star x∈)
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = zero}
    (there (here refl)) | tag-or-id = refl
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = zero}
    (there (there x∈)) | tag-or-id = ⊥-elim (no-⇑ᵢ-zero-star x∈)
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = zero}
    (there (here refl)) | seal-or-id = refl
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = zero}
    (there (there x∈)) | seal-or-id = ⊥-elim (no-⇑ᵢ-zero-star x∈)
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = suc X} x∈
    with μ zero
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = suc X}
    (there x∈) | id-only =
  castᵢ-star-allowed {μ = tailᵈ μ} {Δ = Δ} (un⇑ᵢ-★∈ x∈)
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = suc X}
    (there (there x∈)) | tag-or-id =
  castᵢ-star-allowed {μ = tailᵈ μ} {Δ = Δ} (un⇑ᵢ-★∈ x∈)
castᵢ-star-allowed {μ = μ} {Δ = suc Δ} {X = suc X}
    (there (there x∈)) | seal-or-id =
  castᵢ-star-allowed {μ = tailᵈ μ} {Δ = Δ} (un⇑ᵢ-★∈ x∈)

un⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᴸᵢ-★∈ {Φ = []} ()
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)

no-⇑ᴸᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-star {Φ = []} ()
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈

------------------------------------------------------------------------
-- Local helpers
------------------------------------------------------------------------

seal★-ext-shift :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (extᵈ μ) (⟰ᵗ Σ)
seal★-ext-shift seal★ zero ()
seal★-ext-shift seal★ (suc α) ok =
  ∈-renameStoreᵗ suc (seal★ α ok)

seal★-gen-shift :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (genᵈ μ) (⟰ᵗ Σ)
seal★-gen-shift seal★ zero ()
seal★-gen-shift seal★ (suc α) ok =
  ∈-renameStoreᵗ suc (seal★ α ok)

seal★-inst-shift :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ)
seal★-inst-shift seal★ zero ok = here refl
seal★-inst-shift seal★ (suc α) ok =
  there (∈-renameStoreᵗ suc (seal★ α ok))

ground⊑★ :
  ∀ {μ Δ G} →
  WfTy Δ G →
  Ground G →
  C.tagTyAllowed μ G ≡ true →
  castᵢ μ Δ ∣ Δ ⊢ G ⊑ ★ ⊣ Δ
ground⊑★ (wfVar X<Δ) (＇ X) ok =
  tagˣ (castᵢ-star-lookup X<Δ (tagMode⇒starAllowed ok)) X<Δ
ground⊑★ wfBase (‵ ι) ok = tag ι
ground⊑★ (wf⇒ hA hB) ★⇒★ ok = tag_⇛_ id★ id★

seal⊑★ :
  ∀ {μ Δ Σ α} →
  StoreDetWf Δ Σ →
  sealModeAllowed (μ α) ≡ true →
  (α , ★) ∈ Σ →
  castᵢ μ Δ ∣ Δ ⊢ ＇ α ⊑ ★ ⊣ Δ
seal⊑★ {α = α} wfΣ ok α★∈Σ =
  tagˣ (castᵢ-star-lookup α<Δ (sealMode⇒starAllowed ok)) α<Δ
  where
    α<Δ : α < _
    α<Δ = bound (NWP.StoreDetWf.at wfΣ) α★∈Σ

LeftCastCtxCompatible : ModeEnv → TyCtx → ImpCtx → Set
LeftCastCtxCompatible μ Δ Φ =
  ∀ {X} →
  X < Δ →
  modeStarAllowed (μ X) ≡ true →
  (X ˣ⊑★) ∈ Φ

RightCastCtxCompatible : ModeEnv → TyCtx → ImpCtx → Set
RightCastCtxCompatible μ Δ Φ =
  ∀ {X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Y < Δ →
  modeStarAllowed (μ Y) ≡ true →
  (X ˣ⊑★) ∈ Φ

matched-gen-left-incompatible :
  ∀ {μ Δ Φ} →
  LeftCastCtxCompatible (genᵈ μ) (suc Δ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  ⊥
matched-gen-left-incompatible ok with ok z<s refl
matched-gen-left-incompatible ok | there zero★∈ =
  no-⇑ᵢ-zero-star zero★∈

matched-gen-right-incompatible :
  ∀ {μ Δ Φ} →
  RightCastCtxCompatible (genᵈ μ) (suc Δ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  ⊥
matched-gen-right-incompatible ok
    with ok (here refl) z<s refl
matched-gen-right-incompatible ok | there zero★∈ =
  no-⇑ᵢ-zero-star zero★∈

matched-inst-left-incompatible :
  ∀ {μ Δ Φ} →
  LeftCastCtxCompatible (instᵈ μ) (suc Δ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  ⊥
matched-inst-left-incompatible ok with ok z<s refl
matched-inst-left-incompatible ok | there zero★∈ =
  no-⇑ᵢ-zero-star zero★∈

matched-inst-right-incompatible :
  ∀ {μ Δ Φ} →
  RightCastCtxCompatible (instᵈ μ) (suc Δ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  ⊥
matched-inst-right-incompatible ok
    with ok (here refl) z<s refl
matched-inst-right-incompatible ok | there zero★∈ =
  no-⇑ᵢ-zero-star zero★∈

∀ᵢᶜ : ImpCtx → ImpCtx
∀ᵢᶜ Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ

νᵢᶜ : ImpCtx → ImpCtx
νᵢᶜ Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ

νᵣ : Renameᵗ → Renameᵗ
νᵣ ρ X = suc (ρ X)

record ComposeCtx
    (ρ : Renameᵗ) (Δᴸ : TyCtx)
    (Φᴸ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    map-var :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      X ≡ ρ Y

    comp-var-var :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑ˣ Z) ∈ Φᴿ →
      (X ˣ⊑ˣ Z) ∈ Φᴼ

    comp-var-star :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑★) ∈ Φᴿ →
      (X ˣ⊑★) ∈ Φᴼ

    comp-star-left :
      ∀ {X} →
      X < Δᴸ →
      (X ˣ⊑★) ∈ Φᴸ →
      (X ˣ⊑★) ∈ Φᴼ

open ComposeCtx

compose-∀∀ :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtx ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtx (extᵗ ρ) (suc Δᴸ) (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
compose-∀∀ comp .map-var {X = zero} {Y = zero} (here refl) = refl
compose-∀∀ comp .map-var {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ comp .map-var {X = zero} {Y = suc y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ comp .map-var {X = suc x} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ comp .map-var {X = suc x} {Y = suc y} (there x∈) =
  cong suc (map-var comp (un⇑ᵢ-ˣ∈ x∈))
compose-∀∀ comp .comp-var-var (here refl) (here refl) = here refl
compose-∀∀ comp .comp-var-var (here refl) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left y∈)
compose-∀∀ comp .comp-var-var {X = zero} {Y = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ comp .comp-var-var {X = zero} {Y = suc y} (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ comp .comp-var-var {X = suc x} {Y = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ comp .comp-var-var {X = suc x} {Y = suc y} {Z = zero}
    (there x∈) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right y∈)
compose-∀∀ comp .comp-var-var {X = suc x} {Y = suc y} {Z = suc z}
    (there x∈) (there y∈) =
  there (⇑ᵢ-ˣ∈
    (comp-var-var comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-ˣ∈ y∈)))
compose-∀∀ comp .comp-var-star (here refl) (there y★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star y★∈)
compose-∀∀ comp .comp-var-star {X = zero} {Y = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ comp .comp-var-star {X = zero} {Y = suc y} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀∀ comp .comp-var-star {X = suc x} {Y = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀∀ comp .comp-var-star {X = suc x} {Y = suc y}
    (there x∈) (there y★∈) =
  there (⇑ᵢ-★∈
    (comp-var-star comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-★∈ y★∈)))
compose-∀∀ comp .comp-star-left {X = zero} z<s (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
compose-∀∀ comp .comp-star-left {X = suc x} (s<s X<Δ) (there x★∈) =
  there (⇑ᵢ-★∈ (comp-star-left comp X<Δ (un⇑ᵢ-★∈ x★∈)))

compose-∀ν :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtx ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtx (extᵗ ρ) (suc Δᴸ) (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (νᵢᶜ Φᴼ)
compose-∀ν comp .map-var {X = zero} {Y = zero} (here refl) = refl
compose-∀ν comp .map-var {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀ν comp .map-var {X = zero} {Y = suc y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀ν comp .map-var {X = suc x} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀ν comp .map-var {X = suc x} {Y = suc y} (there x∈) =
  cong suc (map-var comp (un⇑ᵢ-ˣ∈ x∈))
compose-∀ν comp .comp-var-var (here refl) (there y∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left y∈)
compose-∀ν comp .comp-var-var {X = zero} {Y = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀ν comp .comp-var-var {X = zero} {Y = suc y} (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀ν comp .comp-var-var {X = suc x} {Y = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀ν comp .comp-var-var {X = suc x} {Y = suc y}
    (there x∈) (there y∈) =
  there (⇑ᴸᵢ-∈
    (comp-var-var comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-ˣ∈ y∈)))
compose-∀ν comp .comp-var-star (here refl) (here refl) = here refl
compose-∀ν comp .comp-var-star (here refl) (there y★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star y★∈)
compose-∀ν comp .comp-var-star {X = zero} {Y = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀ν comp .comp-var-star {X = zero} {Y = suc y} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
compose-∀ν comp .comp-var-star {X = suc x} {Y = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
compose-∀ν comp .comp-var-star {X = suc x} {Y = suc y}
    (there x∈) (there y★∈) =
  there (⇑ᴸᵢ-∈
    (comp-var-star comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-★∈ y★∈)))
compose-∀ν comp .comp-star-left {X = zero} z<s (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
compose-∀ν comp .comp-star-left {X = suc x} (s<s X<Δ) (there x★∈) =
  there (⇑ᴸᵢ-∈ (comp-star-left comp X<Δ (un⇑ᵢ-★∈ x★∈)))

compose-νid :
  ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ} →
  ComposeCtx ρ Δᴸ Φᴸ Φᴿ Φᴼ →
  ComposeCtx (νᵣ ρ) (suc Δᴸ) (νᵢᶜ Φᴸ) Φᴿ (νᵢᶜ Φᴼ)
compose-νid comp .map-var {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νid comp .map-var {X = suc x} (there x∈) =
  cong suc (map-var comp (un⇑ᴸᵢ-ˣ∈ x∈))
compose-νid comp .comp-var-var {X = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νid comp .comp-var-var {X = suc x} (there x∈) y∈ =
  there (⇑ᴸᵢ-∈ (comp-var-var comp (un⇑ᴸᵢ-ˣ∈ x∈) y∈))
compose-νid comp .comp-var-star {X = zero} (there x∈) y★∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
compose-νid comp .comp-var-star {X = suc x} (there x∈) y★∈ =
  there (⇑ᴸᵢ-∈ (comp-var-star comp (un⇑ᴸᵢ-ˣ∈ x∈) y★∈))
compose-νid comp .comp-star-left {X = zero} z<s (here refl) =
  here refl
compose-νid comp .comp-star-left {X = zero} z<s (there x★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x★∈)
compose-νid comp .comp-star-left {X = suc x} (s<s X<Δ) (there x★∈) =
  there (⇑ᴸᵢ-∈ (comp-star-left comp X<Δ (un⇑ᴸᵢ-★∈ x★∈)))

occurs-var-back :
  ∀ (ρ : Renameᵗ) (α : TyVar) {X Y} →
  X ≡ ρ Y →
  occurs α (＇ Y) ≡ true →
  occurs (ρ α) (＇ X) ≡ true
occurs-var-back ρ α {X} {Y} X≡ρY occ with α ≟ Y
occurs-var-back ρ α {X} {.α} X≡ρα occ | yes refl
    rewrite X≡ρα with ρ α ≟ ρ α
occurs-var-back ρ α {X} {.α} X≡ρα occ | yes refl | yes refl = refl
occurs-var-back ρ α {X} {.α} X≡ρα occ | yes refl | no ρα≢ρα =
  ⊥-elim (ρα≢ρα refl)
occurs-var-back ρ α {X} {Y} X≡ρY () | no α≢Y

∨-right-true :
  ∀ b →
  b ∨ true ≡ true
∨-right-true true = refl
∨-right-true false = refl

mutual
  occurs-back :
    ∀ {ρ Δᴸ Φᴸ Φᴿ Φᴼ Δᴹ A B} →
    ComposeCtx ρ Δᴸ Φᴸ Φᴿ Φᴼ →
    (α : TyVar) →
    Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
    occurs α B ≡ true →
    occurs (ρ α) A ≡ true
  occurs-back comp α id★ ()
  occurs-back comp α (idˣ x∈ _ _) occ =
    occurs-var-back _ α (map-var comp x∈) occ
  occurs-back comp α idι ()
  occurs-back {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} comp α (p ↦ q) occ
      with occurs α b₁ | inspect (occurs α) b₁
         | occurs α b₂ | inspect (occurs α) b₂
  occurs-back {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} comp α (p ↦ q) occ
      | true | [ eq₁ ] | b | eq₂
      rewrite occurs-back comp α p eq₁ = refl
  occurs-back {ρ = ρ} {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} comp α (p ↦ q) occ
      | false | eq₁ | true | [ eq₂ ]
      rewrite occurs-back comp α q eq₂ =
    ∨-right-true (occurs (ρ α) a₁)
  occurs-back {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} comp α (p ↦ q) ()
      | false | eq₁ | false | eq₂
  occurs-back comp α (∀ⁱ p) occ =
    occurs-back (compose-∀∀ comp) (suc α) p occ
  occurs-back comp α (tag ι) ()
  occurs-back comp α (tag_⇛_ p q) ()
  occurs-back comp α (tagˣ x∈ _) ()
  occurs-back comp α (ν occA p) occ =
    occurs-back (compose-νid comp) α p occ

  ⊑-trans-compose :
    ∀ {ρ Δᴸ Δᴹ Δᴿ Φᴸ Φᴿ Φᴼ A B C} →
    ComposeCtx ρ Δᴸ Φᴸ Φᴿ Φᴼ →
    Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
    Φᴿ ∣ Δᴹ ⊢ B ⊑ C ⊣ Δᴿ →
    Φᴼ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
  ⊑-trans-compose comp id★ id★ = id★
  ⊑-trans-compose comp (idˣ x∈ X<Δ _) (idˣ y∈ _ Z<Δ) =
    idˣ (comp-var-var comp x∈ y∈) X<Δ Z<Δ
  ⊑-trans-compose comp (idˣ x∈ X<Δ _) (tagˣ y★∈ _) =
    tagˣ (comp-var-star comp x∈ y★∈) X<Δ
  ⊑-trans-compose comp idι idι = idι
  ⊑-trans-compose comp idι (tag ι) = tag ι
  ⊑-trans-compose comp (p₁ ↦ p₂) (q₁ ↦ q₂) =
    ⊑-trans-compose comp p₁ q₁ ↦ ⊑-trans-compose comp p₂ q₂
  ⊑-trans-compose comp (p₁ ↦ p₂) (tag_⇛_ q₁ q₂) =
    tag_⇛_ (⊑-trans-compose comp p₁ q₁)
            (⊑-trans-compose comp p₂ q₂)
  ⊑-trans-compose comp (∀ⁱ p) (∀ⁱ q) =
    ∀ⁱ (⊑-trans-compose (compose-∀∀ comp) p q)
  ⊑-trans-compose comp (∀ⁱ p) (ν occ q) =
    ν (occurs-back (compose-∀∀ comp) zero p occ)
      (⊑-trans-compose (compose-∀ν comp) p q)
  ⊑-trans-compose comp (tag ι) id★ = tag ι
  ⊑-trans-compose comp (tag_⇛_ p q) id★ =
    tag_⇛_ (⊑-trans-compose comp p id★)
            (⊑-trans-compose comp q id★)
  ⊑-trans-compose comp (tagˣ x★∈ X<Δ) id★ =
    tagˣ (comp-star-left comp X<Δ x★∈) X<Δ
  ⊑-trans-compose comp (ν occ p) q =
    ν occ (⊑-trans-compose (compose-νid comp) p q)

compose-cast-left :
  ∀ {μ Δ Φ} →
  LeftCastCtxCompatible μ Δ Φ →
  ComposeCtx (λ X → X) Δ (castᵢ μ Δ) Φ Φ
compose-cast-left {μ = μ} {Δ = Δ} ok .map-var x∈ =
  castᵢ-var-identity {μ = μ} {Δ = Δ} x∈
compose-cast-left {μ = μ} {Δ = Δ} ok .comp-var-var x∈ y∈
    rewrite castᵢ-var-identity {μ = μ} {Δ = Δ} x∈ = y∈
compose-cast-left {μ = μ} {Δ = Δ} ok .comp-var-star x∈ y★∈
    rewrite castᵢ-var-identity {μ = μ} {Δ = Δ} x∈ = y★∈
compose-cast-left {μ = μ} {Δ = Δ} ok .comp-star-left X<Δ x★∈ =
  ok X<Δ (castᵢ-star-allowed {μ = μ} {Δ = Δ} x★∈)

⊑-transˡ-castᵢ :
  ∀ {Φ μ Δ₁ Δ₂ A B C} →
  LeftCastCtxCompatible μ Δ₁ Φ →
  castᵢ μ Δ₁ ∣ Δ₁ ⊢ A ⊑ B ⊣ Δ₁ →
  Φ ∣ Δ₁ ⊢ B ⊑ C ⊣ Δ₂ →
  Φ ∣ Δ₁ ⊢ A ⊑ C ⊣ Δ₂
⊑-transˡ-castᵢ ok =
  ⊑-trans-compose (compose-cast-left ok)

record BoundMapCtx (ρ : Renameᵗ) (δ : TyCtx) (Φ : ImpCtx) : Set where
  field
    map-bound :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φ →
      Y < δ →
      X ≡ ρ Y

open BoundMapCtx

bound-empty :
  ∀ {Φ} →
  BoundMapCtx (λ X → X) zero Φ
bound-empty .map-bound x∈ ()

bound-∀ :
  ∀ {ρ δ Φ} →
  BoundMapCtx ρ δ Φ →
  BoundMapCtx (extᵗ ρ) (suc δ) (∀ᵢᶜ Φ)
bound-∀ bmap .map-bound {X = zero} {Y = zero} (here refl) z<s =
  refl
bound-∀ bmap .map-bound {X = zero} {Y = zero} (there x∈) y<δ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
bound-∀ bmap .map-bound {X = zero} {Y = suc y} (there x∈) y<δ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
bound-∀ bmap .map-bound {X = suc x} {Y = zero} (there x∈) y<δ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
bound-∀ bmap .map-bound {X = suc x} {Y = suc y}
    (there x∈) (s<s y<δ) =
  cong suc (map-bound bmap (un⇑ᵢ-ˣ∈ x∈) y<δ)

bound-ν :
  ∀ {ρ δ Φ} →
  BoundMapCtx ρ δ Φ →
  BoundMapCtx (νᵣ ρ) δ (νᵢᶜ Φ)
bound-ν bmap .map-bound {X = zero} (there x∈) y<δ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
bound-ν bmap .map-bound {X = suc x} (there x∈) y<δ =
  cong suc (map-bound bmap (un⇑ᴸᵢ-ˣ∈ x∈) y<δ)

occurs-back-bound :
  ∀ {ρ δ Φ Δᴸ Δᴿ A B} →
  BoundMapCtx ρ δ Φ →
  (α : TyVar) →
  α < δ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  occurs α B ≡ true →
  occurs (ρ α) A ≡ true
occurs-back-bound bmap α α<δ id★ ()
occurs-back-bound {ρ = ρ} bmap α α<δ (idˣ {Y = y} x∈ _ _) occ
    with α ≟ y
occurs-back-bound {ρ = ρ} bmap α α<δ (idˣ {Y = .α} x∈ _ _) occ
    | yes refl
    rewrite map-bound bmap x∈ α<δ with ρ α ≟ ρ α
occurs-back-bound {ρ = ρ} bmap α α<δ (idˣ {Y = .α} x∈ _ _) occ
    | yes refl | yes refl = refl
occurs-back-bound {ρ = ρ} bmap α α<δ (idˣ {Y = .α} x∈ _ _) occ
    | yes refl | no ρα≢ρα =
  ⊥-elim (ρα≢ρα refl)
occurs-back-bound bmap α α<δ (idˣ {Y = y} x∈ _ _) () | no α≢y
occurs-back-bound bmap α α<δ idι ()
occurs-back-bound {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} bmap α α<δ
    (p ↦ q) occ
    with occurs α b₁ | inspect (occurs α) b₁
       | occurs α b₂ | inspect (occurs α) b₂
occurs-back-bound {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} bmap α α<δ
    (p ↦ q) occ | true | [ eq₁ ] | b | eq₂
    rewrite occurs-back-bound bmap α α<δ p eq₁ = refl
occurs-back-bound {ρ = ρ} {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} bmap α α<δ
    (p ↦ q) occ | false | eq₁ | true | [ eq₂ ]
    rewrite occurs-back-bound bmap α α<δ q eq₂ =
  ∨-right-true (occurs (ρ α) a₁)
occurs-back-bound {A = a₁ ⇒ a₂} {B = b₁ ⇒ b₂} bmap α α<δ
    (p ↦ q) () | false | eq₁ | false | eq₂
occurs-back-bound bmap α α<δ (∀ⁱ p) occ =
  occurs-back-bound (bound-∀ bmap) (suc α) (s<s α<δ) p occ
occurs-back-bound bmap α α<δ (tag ι) ()
occurs-back-bound bmap α α<δ (tag_⇛_ p q) ()
occurs-back-bound bmap α α<δ (tagˣ x∈ _) ()
occurs-back-bound bmap α α<δ (ν occA p) occ =
  occurs-back-bound (bound-ν bmap) α α<δ p occ

record ComposeRightCtx
    (Δᴹ : TyCtx) (Φᴸ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    compʳ-var-var :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (Y ˣ⊑ˣ Z) ∈ Φᴿ →
      (X ˣ⊑ˣ Z) ∈ Φᴼ

    compʳ-var-star :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      Y < Δᴹ →
      (Y ˣ⊑★) ∈ Φᴿ →
      (X ˣ⊑★) ∈ Φᴼ

    compʳ-star :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φᴸ →
      (X ˣ⊑★) ∈ Φᴼ

open ComposeRightCtx

composeʳ-∀∀ :
  ∀ {Δᴹ Φᴸ Φᴿ Φᴼ} →
  ComposeRightCtx Δᴹ Φᴸ Φᴿ Φᴼ →
  ComposeRightCtx (suc Δᴹ) (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᴼ)
composeʳ-∀∀ comp .compʳ-var-var (here refl) (here refl) = here refl
composeʳ-∀∀ comp .compʳ-var-var (here refl) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left y∈)
composeʳ-∀∀ comp .compʳ-var-var {X = zero} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀∀ comp .compʳ-var-var {X = zero} {Y = suc y}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀∀ comp .compʳ-var-var {X = suc x} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
composeʳ-∀∀ comp .compʳ-var-var {X = suc x} {Y = suc y} {Z = zero}
    (there x∈) (there y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right y∈)
composeʳ-∀∀ comp .compʳ-var-var {X = suc x} {Y = suc y} {Z = suc z}
    (there x∈) (there y∈) =
  there (⇑ᵢ-ˣ∈
    (compʳ-var-var comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᵢ-ˣ∈ y∈)))
composeʳ-∀∀ comp .compʳ-var-star (here refl) Y<Δ (there y★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star y★∈)
composeʳ-∀∀ comp .compʳ-var-star {X = zero} {Y = zero}
    (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀∀ comp .compʳ-var-star {X = zero} {Y = suc y}
    (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀∀ comp .compʳ-var-star {X = suc x} {Y = zero}
    (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
composeʳ-∀∀ comp .compʳ-var-star {X = suc x} {Y = suc y}
    (there x∈) (s<s Y<Δ) (there y★∈) =
  there (⇑ᵢ-★∈
    (compʳ-var-star comp (un⇑ᵢ-ˣ∈ x∈) Y<Δ (un⇑ᵢ-★∈ y★∈)))
composeʳ-∀∀ comp .compʳ-star {X = zero} (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
composeʳ-∀∀ comp .compʳ-star {X = suc x} (there x★∈) =
  there (⇑ᵢ-★∈ (compʳ-star comp (un⇑ᵢ-★∈ x★∈)))

composeʳ-∀ν :
  ∀ {Δᴹ Φᴸ Φᴿ Φᴼ} →
  ComposeRightCtx Δᴹ Φᴸ Φᴿ Φᴼ →
  ComposeRightCtx (suc Δᴹ) (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (νᵢᶜ Φᴼ)
composeʳ-∀ν comp .compʳ-var-var (here refl) (there y∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left y∈)
composeʳ-∀ν comp .compʳ-var-var {X = zero} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀ν comp .compʳ-var-var {X = zero} {Y = suc y}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀ν comp .compʳ-var-var {X = suc x} {Y = zero}
    (there x∈) y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
composeʳ-∀ν comp .compʳ-var-var {X = suc x} {Y = suc y}
    (there x∈) (there y∈) =
  there (⇑ᴸᵢ-∈
    (compʳ-var-var comp (un⇑ᵢ-ˣ∈ x∈) (un⇑ᴸᵢ-ˣ∈ y∈)))
composeʳ-∀ν comp .compʳ-var-star (here refl) Y<Δ (here refl) =
  here refl
composeʳ-∀ν comp .compʳ-var-star (here refl) Y<Δ (there y★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star y★∈)
composeʳ-∀ν comp .compʳ-var-star {X = zero} {Y = zero}
    (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀ν comp .compʳ-var-star {X = zero} {Y = suc y}
    (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
composeʳ-∀ν comp .compʳ-var-star {X = suc x} {Y = zero}
    (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
composeʳ-∀ν comp .compʳ-var-star {X = suc x} {Y = suc y}
    (there x∈) (s<s Y<Δ) (there y★∈) =
  there (⇑ᴸᵢ-∈
    (compʳ-var-star comp (un⇑ᵢ-ˣ∈ x∈) Y<Δ (un⇑ᴸᵢ-★∈ y★∈)))
composeʳ-∀ν comp .compʳ-star {X = zero} (there x★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x★∈)
composeʳ-∀ν comp .compʳ-star {X = suc x} (there x★∈) =
  there (⇑ᴸᵢ-∈ (compʳ-star comp (un⇑ᵢ-★∈ x★∈)))

composeʳ-νid :
  ∀ {Δᴹ Φᴸ Φᴿ Φᴼ} →
  ComposeRightCtx Δᴹ Φᴸ Φᴿ Φᴼ →
  ComposeRightCtx Δᴹ (νᵢᶜ Φᴸ) Φᴿ (νᵢᶜ Φᴼ)
composeʳ-νid comp .compʳ-var-var {X = zero} (there x∈) y∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
composeʳ-νid comp .compʳ-var-var {X = suc x} (there x∈) y∈ =
  there (⇑ᴸᵢ-∈ (compʳ-var-var comp (un⇑ᴸᵢ-ˣ∈ x∈) y∈))
composeʳ-νid comp .compʳ-var-star {X = zero} (there x∈) Y<Δ y★∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
composeʳ-νid comp .compʳ-var-star {X = suc x} (there x∈) Y<Δ y★∈ =
  there (⇑ᴸᵢ-∈ (compʳ-var-star comp (un⇑ᴸᵢ-ˣ∈ x∈) Y<Δ y★∈))
composeʳ-νid comp .compʳ-star (here refl) =
  here refl
composeʳ-νid comp .compʳ-star {X = zero} (there x★∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x★∈)
composeʳ-νid comp .compʳ-star {X = suc x} (there x★∈) =
  there (⇑ᴸᵢ-∈ (compʳ-star comp (un⇑ᴸᵢ-★∈ x★∈)))

⊑-trans-compose-right :
  ∀ {ρ δ Δᴸ Δᴹ Δᴿ Φᴸ Φᴿ Φᴼ A B C} →
  ComposeRightCtx Δᴹ Φᴸ Φᴿ Φᴼ →
  BoundMapCtx ρ δ Φᴸ →
  Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ →
  Φᴿ ∣ Δᴹ ⊢ B ⊑ C ⊣ Δᴿ →
  Φᴼ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-compose-right comp bmap id★ id★ = id★
⊑-trans-compose-right comp bmap (idˣ x∈ X<Δ _) (idˣ y∈ _ Z<Δ) =
  idˣ (compʳ-var-var comp x∈ y∈) X<Δ Z<Δ
⊑-trans-compose-right comp bmap (idˣ x∈ X<Δ Y<Δ) (tagˣ y★∈ _) =
  tagˣ (compʳ-var-star comp x∈ Y<Δ y★∈) X<Δ
⊑-trans-compose-right comp bmap idι idι = idι
⊑-trans-compose-right comp bmap idι (tag ι) = tag ι
⊑-trans-compose-right comp bmap (p₁ ↦ p₂) (q₁ ↦ q₂) =
  ⊑-trans-compose-right comp bmap p₁ q₁
    ↦ ⊑-trans-compose-right comp bmap p₂ q₂
⊑-trans-compose-right comp bmap (p₁ ↦ p₂) (tag_⇛_ q₁ q₂) =
  tag_⇛_ (⊑-trans-compose-right comp bmap p₁ q₁)
          (⊑-trans-compose-right comp bmap p₂ q₂)
⊑-trans-compose-right comp bmap (∀ⁱ p) (∀ⁱ q) =
  ∀ⁱ (⊑-trans-compose-right
    (composeʳ-∀∀ comp) (bound-∀ bmap) p q)
⊑-trans-compose-right comp bmap (∀ⁱ p) (ν occ q) =
  ν (occurs-back-bound (bound-∀ bmap) zero z<s p occ)
    (⊑-trans-compose-right
      (composeʳ-∀ν comp) (bound-∀ bmap) p q)
⊑-trans-compose-right comp bmap (tag ι) id★ = tag ι
⊑-trans-compose-right comp bmap (tag_⇛_ p q) id★ =
  tag_⇛_ (⊑-trans-compose-right comp bmap p id★)
          (⊑-trans-compose-right comp bmap q id★)
⊑-trans-compose-right comp bmap (tagˣ x★∈ X<Δ) id★ =
  tagˣ (compʳ-star comp x★∈) X<Δ
⊑-trans-compose-right comp bmap (ν occ p) q =
  ν occ (⊑-trans-compose-right
    (composeʳ-νid comp) (bound-ν bmap) p q)

compose-cast-right :
  ∀ {μ Δ Φ} →
  RightCastCtxCompatible μ Δ Φ →
  ComposeRightCtx Δ Φ (castᵢ μ Δ) Φ
compose-cast-right {μ = μ} {Δ = Δ} ok .compʳ-var-var x∈ y∈
    rewrite castᵢ-var-identity {μ = μ} {Δ = Δ} y∈ = x∈
compose-cast-right {μ = μ} {Δ = Δ} ok .compʳ-var-star x∈ Y<Δ y★∈ =
  ok x∈ Y<Δ (castᵢ-star-allowed {μ = μ} {Δ = Δ} y★∈)
compose-cast-right ok .compʳ-star x★∈ = x★∈

⊑-transʳ-castᵢ :
  ∀ {Φ μ Δ₁ Δ₂ A B C} →
  RightCastCtxCompatible μ Δ₂ Φ →
  Φ ∣ Δ₁ ⊢ A ⊑ B ⊣ Δ₂ →
  castᵢ μ Δ₂ ∣ Δ₂ ⊢ B ⊑ C ⊣ Δ₂ →
  Φ ∣ Δ₁ ⊢ A ⊑ C ⊣ Δ₂
⊑-transʳ-castᵢ ok =
  ⊑-trans-compose-right (compose-cast-right ok) bound-empty

left-castᵢ-compatible :
  ∀ {μ Δ} →
  LeftCastCtxCompatible μ Δ (castᵢ μ Δ)
left-castᵢ-compatible X<Δ ok =
  castᵢ-star-lookup X<Δ ok

⊑-trans-castᵢ :
  ∀ {μ Δ A B C} →
  castᵢ μ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  castᵢ μ Δ ∣ Δ ⊢ B ⊑ C ⊣ Δ →
  castᵢ μ Δ ∣ Δ ⊢ A ⊑ C ⊣ Δ
⊑-trans-castᵢ =
  ⊑-transˡ-castᵢ left-castᵢ-compatible

------------------------------------------------------------------------
-- Strict casts embed in the non-strict grammars
------------------------------------------------------------------------

mutual
  strictNarrowing⇒narrowing :
    ∀ {c} →
    NW.StrictNarrowing c →
    NW.Narrowing c
  strictNarrowing⇒narrowing (NW.strict-crossⁿ g) =
    NW.cross (strictCrossNarrowing⇒crossNarrowing g)
  strictNarrowing⇒narrowing (NW.strict-gen n) = NW.gen n
  strictNarrowing⇒narrowing (NW.strict-untag G) = NW.untag G
  strictNarrowing⇒narrowing (NW.strict-untag-seq G g) =
    G NW.？︔ g
  strictNarrowing⇒narrowing (NW.strict-seal A α) = NW.sealⁿ A α
  strictNarrowing⇒narrowing (NW.strict-seal-seq n α) =
    n NW.︔seal α

  strictWidening⇒widening :
    ∀ {c} →
    NW.StrictWidening c →
    NW.Widening c
  strictWidening⇒widening (NW.strict-crossʷ g) =
    NW.cross (strictCrossWidening⇒crossWidening g)
  strictWidening⇒widening (NW.strict-inst w) = NW.inst w
  strictWidening⇒widening (NW.strict-tag G) = NW.tag G
  strictWidening⇒widening (NW.strict-tag-seq g G) =
    g NW.︔ G !
  strictWidening⇒widening (NW.strict-unseal α A) = NW.unsealʷ α A
  strictWidening⇒widening (NW.strict-unseal-seq α w) =
    NW.unseal︔_ α w

  strictCrossNarrowing⇒crossNarrowing :
    ∀ {c} →
    NW.StrictCrossNarrowing c →
    NW.CrossNarrowing c
  strictCrossNarrowing⇒crossNarrowing (NW.cn-funˡ w n) =
    strictWidening⇒widening w NW.↦ n
  strictCrossNarrowing⇒crossNarrowing (NW.cn-funʳ w n) =
    w NW.↦ strictNarrowing⇒narrowing n
  strictCrossNarrowing⇒crossNarrowing (NW.cn-all n) =
    NW.`∀ (strictNarrowing⇒narrowing n)

  strictCrossWidening⇒crossWidening :
    ∀ {c} →
    NW.StrictCrossWidening c →
    NW.CrossWidening c
  strictCrossWidening⇒crossWidening (NW.cw-funˡ n w) =
    strictNarrowing⇒narrowing n NW.↦ w
  strictCrossWidening⇒crossWidening (NW.cw-funʳ n w) =
    n NW.↦ strictWidening⇒widening w
  strictCrossWidening⇒crossWidening (NW.cw-all w) =
    NW.`∀ (strictWidening⇒widening w)

------------------------------------------------------------------------
-- Duplicated-context cast endpoints
------------------------------------------------------------------------

record DropTargetCtx (k : TyVar) (Φ Ψ : ImpCtx) : Set where
  field
    drop-var :
      ∀ {X Y} →
      (X ˣ⊑ˣ raiseVarFrom k Y) ∈ Φ →
      (X ˣ⊑ˣ Y) ∈ Ψ

    drop-star :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φ →
      (X ˣ⊑★) ∈ Ψ

open DropTargetCtx

drop-target-∀ :
  ∀ {k Φ Ψ} →
  DropTargetCtx k Φ Ψ →
  DropTargetCtx (suc k) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)
drop-target-∀ drop .drop-var {X = zero} {Y = zero} (here refl) =
  here refl
drop-target-∀ drop .drop-var {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-∀ drop .drop-var {X = zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-∀ drop .drop-var {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-target-∀ drop .drop-var {X = suc X} {Y = suc Y} (there x∈) =
  there (⇑ᵢ-ˣ∈ (drop-var drop (un⇑ᵢ-ˣ∈ x∈)))
drop-target-∀ drop .drop-star (here ())
drop-target-∀ drop .drop-star {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-∀ drop .drop-star {X = suc X} (there x∈) =
  there (⇑ᵢ-★∈ (drop-star drop (un⇑ᵢ-★∈ x∈)))

drop-target-ν :
  ∀ {k Φ Ψ} →
  DropTargetCtx k Φ Ψ →
  DropTargetCtx k (νᵢᶜ Φ) (νᵢᶜ Ψ)
drop-target-ν drop .drop-var (here ())
drop-target-ν drop .drop-var {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-target-ν drop .drop-var {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-∈ (drop-var drop (un⇑ᴸᵢ-ˣ∈ x∈)))
drop-target-ν drop .drop-star (here refl) = here refl
drop-target-ν drop .drop-star {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-target-ν drop .drop-star {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-∈ (drop-star drop (un⇑ᴸᵢ-★∈ x∈)))

drop-target-castᵢ-gen :
  ∀ {μ Δ} →
  DropTargetCtx zero
    (castᵢ (genᵈ μ) (suc Δ))
    (νᵢᶜ (castᵢ μ Δ))
drop-target-castᵢ-gen .drop-var (here ())
drop-target-castᵢ-gen .drop-var (there (here ()))
drop-target-castᵢ-gen .drop-var {X = zero} (there (there x∈)) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-castᵢ-gen .drop-var {X = suc X} (there (there x∈)) =
  there (⇑ᴸᵢ-∈ (un⇑ᵢ-ˣ∈ x∈))
drop-target-castᵢ-gen .drop-star (here ())
drop-target-castᵢ-gen .drop-star (there (here refl)) = here refl
drop-target-castᵢ-gen .drop-star {X = zero} (there (there x∈)) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-castᵢ-gen .drop-star {X = suc X} (there (there x∈)) =
  there (⇑ᴸᵢ-∈ (un⇑ᵢ-★∈ x∈))

drop-target-castᵢ-inst :
  ∀ {μ Δ} →
  DropTargetCtx zero
    (castᵢ (instᵈ μ) (suc Δ))
    (νᵢᶜ (castᵢ μ Δ))
drop-target-castᵢ-inst .drop-var (here ())
drop-target-castᵢ-inst .drop-var (there (here ()))
drop-target-castᵢ-inst .drop-var {X = zero} (there (there x∈)) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-castᵢ-inst .drop-var {X = suc X} (there (there x∈)) =
  there (⇑ᴸᵢ-∈ (un⇑ᵢ-ˣ∈ x∈))
drop-target-castᵢ-inst .drop-star (here ())
drop-target-castᵢ-inst .drop-star (there (here refl)) = here refl
drop-target-castᵢ-inst .drop-star {X = zero} (there (there x∈)) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-castᵢ-inst .drop-star {X = suc X} (there (there x∈)) =
  there (⇑ᴸᵢ-∈ (un⇑ᵢ-★∈ x∈))

mutual
  drop-targetᵢ :
    ∀ {k Φ Ψ Δᴸ Δᴿ A B} →
    WfTy Δᴿ B →
    DropTargetCtx k Φ Ψ →
    Φ ∣ Δᴸ ⊢ A ⊑ renameᵗ (raiseVarFrom k) B ⊣ suc Δᴿ →
    Ψ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  drop-targetᵢ wf★ drop id★ = id★
  drop-targetᵢ (wfVar Y<Δ) drop (idˣ x∈ X<Δ _) =
    idˣ (drop-var drop x∈) X<Δ Y<Δ
  drop-targetᵢ wfBase drop idι = idι
  drop-targetᵢ (wf⇒ hA hB) drop (p ↦ q) =
    drop-targetᵢ hA drop p ↦ drop-targetᵢ hB drop q
  drop-targetᵢ {k = k} (wf∀ {A = B} hB) drop (∀ⁱ p)
      rewrite rename-raise-ext k B =
    ∀ⁱ (drop-targetᵢ hB (drop-target-∀ drop) p)
  drop-targetᵢ wf★ drop (tag ι) = tag ι
  drop-targetᵢ wf★ drop (tag_⇛_ p q) =
    tag_⇛_ (drop-targetᵢ wf★ drop p)
            (drop-targetᵢ wf★ drop q)
  drop-targetᵢ wf★ drop (tagˣ x∈ X<Δ) =
    tagˣ (drop-star drop x∈) X<Δ
  drop-targetᵢ hB drop (ν occ p) =
    ν occ (drop-targetᵢ hB (drop-target-ν drop) p)

mutual
  narrowing-gen⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    StoreDetWf Δ Σ →
    SealModeStore★ μ Σ →
    WfTy Δ A →
    occurs zero B ≡ true →
    genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A ⊒ B →
    castᵢ μ Δ ∣ Δ ⊢ `∀ B ⊑ A ⊣ Δ
  narrowing-gen⇒⊑ᵢ {μ = μ} {Δ = Δ} wfΣ seal★ hA occB c⊒ =
    ν occB (drop-targetᵢ hA (drop-target-castᵢ-gen {μ = μ} {Δ = Δ})
      (narrowing⇒⊑ᵢ (StoreDetWf-⟰ᵗ wfΣ)
        (seal★-gen-shift seal★) c⊒))

  widening-inst⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    StoreDetWf Δ Σ →
    SealModeStore★ μ Σ →
    WfTy Δ B →
    occurs zero A ≡ true →
    instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ c ∶ A ⊑ ⇑ᵗ B →
    castᵢ μ Δ ∣ Δ ⊢ `∀ A ⊑ B ⊣ Δ
  widening-inst⇒⊑ᵢ {μ = μ} {Δ = Δ} wfΣ seal★ hB occA c⊑ =
    ν occA (drop-targetᵢ hB (drop-target-castᵢ-inst {μ = μ} {Δ = Δ})
      (widening⇒⊑ᵢ (StoreDetWf-inst wfΣ)
        (seal★-inst-shift seal★) c⊑))

  narrowing⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    StoreDetWf Δ Σ →
    SealModeStore★ μ Σ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    castᵢ μ Δ ∣ Δ ⊢ B ⊑ A ⊣ Δ
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-id (wfVar X<Δ) ok ,
      NW.cross (NW.id-＇ X)) =
    idˣ (castᵢ-id-lookup X<Δ) X<Δ X<Δ
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-id wfBase ok ,
      NW.cross (NW.id-‵ ι)) =
    idι
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-id wf★ ok , NW.id★) =
    id★
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-fun s⊢ t⊢ ,
      NW.cross (sʷ NW.↦ tⁿ)) =
    widening⇒⊑ᵢ wfΣ seal★ (s⊢ , sʷ)
      ↦ narrowing⇒⊑ᵢ wfΣ seal★ (t⊢ , tⁿ)
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-all c⊢ , NW.cross (NW.`∀ cⁿ)) =
    ∀ⁱ (narrowing⇒⊑ᵢ (StoreDetWf-⟰ᵗ wfΣ)
          (seal★-ext-shift seal★) (c⊢ , cⁿ))
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-gen hA occB c⊢ , NW.gen cⁿ) =
    narrowing-gen⇒⊑ᵢ wfΣ seal★ hA occB (c⊢ , cⁿ)
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-untag hG G ok , NW.untag _) =
    ground⊑★ hG G ok
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-seq s⊢ t⊢ , G NW.？︔ gⁿ) =
    ⊑-trans-castᵢ
      (narrowing⇒⊑ᵢ wfΣ seal★
        (t⊢ , NW.cross (strictCrossNarrowing⇒crossNarrowing gⁿ)))
      (narrowing⇒⊑ᵢ wfΣ seal★ (s⊢ , NW.untag G))
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-seal hA α∈Σ ok ,
      NW.sealⁿ A α)
      rewrite NWP.StoreDetWf.unique wfΣ α∈Σ (seal★ α ok) =
    seal⊑★ wfΣ ok (seal★ α ok)
  narrowing⇒⊑ᵢ wfΣ seal★ (C.cast-seq s⊢ t⊢ , n NW.︔seal α) =
    ⊑-trans-castᵢ
      (narrowing⇒⊑ᵢ wfΣ seal★ (t⊢ , NW.sealⁿ _ α))
      (narrowing⇒⊑ᵢ wfΣ seal★
        (s⊢ , strictNarrowing⇒narrowing n))

  widening⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    StoreDetWf Δ Σ →
    SealModeStore★ μ Σ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    castᵢ μ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-id (wfVar X<Δ) ok ,
      NW.cross (NW.id-＇ X)) =
    idˣ (castᵢ-id-lookup X<Δ) X<Δ X<Δ
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-id wfBase ok ,
      NW.cross (NW.id-‵ ι)) =
    idι
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-id wf★ ok , NW.id★) =
    id★
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-fun s⊢ t⊢ ,
      NW.cross (sⁿ NW.↦ tʷ)) =
    narrowing⇒⊑ᵢ wfΣ seal★ (s⊢ , sⁿ)
      ↦ widening⇒⊑ᵢ wfΣ seal★ (t⊢ , tʷ)
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) =
    ∀ⁱ (widening⇒⊑ᵢ (StoreDetWf-⟰ᵗ wfΣ)
          (seal★-ext-shift seal★) (c⊢ , cʷ))
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-inst hB occA c⊢ , NW.inst cʷ) =
    widening-inst⇒⊑ᵢ wfΣ seal★ hB occA (c⊢ , cʷ)
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-tag hG G ok , NW.tag _) =
    ground⊑★ hG G ok
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-seq s⊢ t⊢ , gʷ NW.︔ G !) =
    ⊑-trans-castᵢ
      (widening⇒⊑ᵢ wfΣ seal★
        (s⊢ , NW.cross (strictCrossWidening⇒crossWidening gʷ)))
      (widening⇒⊑ᵢ wfΣ seal★ (t⊢ , NW.tag G))
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-unseal hA α∈Σ ok ,
      NW.unsealʷ α A)
      rewrite NWP.StoreDetWf.unique wfΣ α∈Σ (seal★ α ok) =
    seal⊑★ wfΣ ok (seal★ α ok)
  widening⇒⊑ᵢ wfΣ seal★ (C.cast-seq s⊢ t⊢ , NW.unseal︔_ α w) =
    ⊑-trans-castᵢ
      (widening⇒⊑ᵢ wfΣ seal★ (s⊢ , NW.unsealʷ α _))
      (widening⇒⊑ᵢ wfΣ seal★
        (t⊢ , strictWidening⇒widening w))

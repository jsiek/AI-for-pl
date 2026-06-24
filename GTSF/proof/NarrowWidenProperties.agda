module proof.NarrowWidenProperties where

-- File Charter:
--   * Structural lemmas for narrowing/widening coercion judgments.
--   * Provides proof-level composition witnesses `_⨟ⁿ_` and `_⨟ʷ_`.
--   * Depends on the public definitions in `NarrowWiden`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; _<_; _≤_; zero; suc; z<s; s<s; s≤s)
open import Data.Nat.Properties
  using (_≟_; ≤-refl; ≤-trans; <-irrefl; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; inspect; subst; sym; trans; [_])
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import Coercions
open import NarrowWiden
open import proof.CoercionProperties
  using (coercion-src-tgtᵐ)
open import proof.StoreProperties
  using
    ( StoreWfAt-cons
    ; StoreWfAt-⟰ᵗ
    ; ∈-renameStoreᵗ
    ; renameStoreᵗ-incl
    )
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; WfTy-weakenᵗ
    ; raiseVarFrom-≢
    ; occurs-raise
    ; occurs-raise-fresh
    ; rename-raise-ext
    ; renameᵗ-ground
    ; renameᵗ-compose
    ; renameᵗ-id
    ; renameᵗ-preserves-WfTy
    ; renameᵗ-ext-suc-comm
    ; renameStoreᵗ-ext-suc-comm
    )

------------------------------------------------------------------------
-- Basic structural lemmas
------------------------------------------------------------------------

renameᵗ-atom :
  ∀ ρ {A} →
  Atom A →
  Atom (renameᵗ ρ A)
renameᵗ-atom ρ (＇ α) = ＇ (ρ α)
renameᵗ-atom ρ (‵ ι) = ‵ ι
renameᵗ-atom ρ ★ = ★

------------------------------------------------------------------------
-- Well-typed narrowing/widening projections
------------------------------------------------------------------------

narrowing⇒coercionᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
narrowing⇒coercionᵐ = proj₁

narrowing⇒grammarᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Narrowing c
narrowing⇒grammarᵐ = proj₂

widening⇒coercionᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
widening⇒coercionᵐ = proj₁

widening⇒grammarᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  Widening c
widening⇒grammarᵐ = proj₂

narrowing⇒coercion :
  ∀ {Δ Σ A B c} →
  (∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B) →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
narrowing⇒coercion (μ , c⊢) =
  μ , narrowing⇒coercionᵐ c⊢

widening⇒coercion :
  ∀ {Δ Σ A B c} →
  (∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B) →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
widening⇒coercion (μ , c⊢) =
  μ , widening⇒coercionᵐ c⊢

------------------------------------------------------------------------
-- Store invariant needed by determinacy
------------------------------------------------------------------------

StoreUnique : Store → Set
StoreUnique Σ =
  ∀ {α A B} →
  (α , A) ∈ Σ →
  (α , B) ∈ Σ →
  A ≡ B

record StoreDetWf (Δ : TyCtx) (Σ : Store) : Set₁ where
  field
    at : StoreWfAt Δ Σ
    wfOlder : ∀ {α A} → (α , A) ∈ Σ → WfTy α A
    unique : StoreUnique Σ

open StoreDetWf

StoreWf⇒det :
  ∀ {Δ Σ} →
  StoreWf Δ Σ →
  StoreDetWf Δ Σ
StoreWf⇒det wfΣ =
  record
    { at = Store.at wfΣ
    ; wfOlder = Store.wfOlder wfΣ
    ; unique = Store.unique wfΣ
    }

∈-⟰ᵗ-inv :
  ∀ {Σ α B} →
  (suc α , B) ∈ ⟰ᵗ Σ →
  ∃[ A ] (B ≡ ⇑ᵗ A × (α , A) ∈ Σ)
∈-⟰ᵗ-inv {Σ = (α , A) ∷ Σ} (here refl) =
  A , refl , here refl
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    with ∈-⟰ᵗ-inv h
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    | A , eq , h′ =
  A , eq , there h′

∈-⟰ᵗ-zero :
  ∀ {Σ A} →
  (zero , A) ∈ ⟰ᵗ Σ →
  ⊥
∈-⟰ᵗ-zero {Σ = (α , B) ∷ Σ} (there h) =
  ∈-⟰ᵗ-zero h

StoreUnique-⟰ᵗ :
  ∀ {Σ} →
  StoreUnique Σ →
  StoreUnique (⟰ᵗ Σ)
StoreUnique-⟰ᵗ uniqueΣ {α = zero} h₁ h₂ =
  ⊥-elim (∈-⟰ᵗ-zero h₁)
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    with ∈-⟰ᵗ-inv h₁ | ∈-⟰ᵗ-inv h₂
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    | A , eq₁ , h₁′ | B , eq₂ , h₂′ =
  trans eq₁ (trans (cong ⇑ᵗ (uniqueΣ h₁′ h₂′)) (sym eq₂))

StoreUnique-inst :
  ∀ {Σ} →
  StoreUnique Σ →
  StoreUnique ((zero , ★) ∷ ⟰ᵗ Σ)
StoreUnique-inst uniqueΣ (here refl) (here refl) = refl
StoreUnique-inst uniqueΣ (here refl) (there h) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-inst uniqueΣ (there h) (here refl) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-inst uniqueΣ (there h₁) (there h₂) =
  StoreUnique-⟰ᵗ uniqueΣ h₁ h₂

StoreDetWf-⟰ᵗ :
  ∀ {Δ Σ} →
  StoreDetWf Δ Σ →
  StoreDetWf (suc Δ) (⟰ᵗ Σ)
StoreDetWf-⟰ᵗ wfΣ =
  record
    { at = StoreWfAt-⟰ᵗ (at wfΣ)
    ; wfOlder = wfOlder′
    ; unique = StoreUnique-⟰ᵗ (unique wfΣ)
    }
  where
    wfOlder′ :
      ∀ {α A} →
      (α , A) ∈ ⟰ᵗ _ →
      WfTy α A
    wfOlder′ {zero} h =
      ⊥-elim (∈-⟰ᵗ-zero h)
    wfOlder′ {suc α} h
        with ∈-⟰ᵗ-inv h
    wfOlder′ {suc α} h | A , eq , h′ =
      subst (WfTy (suc α)) (sym eq)
        (renameᵗ-preserves-WfTy (wfOlder wfΣ h′) TyRenameWf-suc)

StoreDetWf-inst :
  ∀ {Δ Σ} →
  StoreDetWf Δ Σ →
  StoreDetWf (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ)
StoreDetWf-inst wfΣ =
  record
    { at = StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ (at wfΣ))
    ; wfOlder = wfOlder′
    ; unique = StoreUnique-inst (unique wfΣ)
    }
  where
    shifted : StoreDetWf _ _
    shifted = StoreDetWf-⟰ᵗ wfΣ

    wfOlder′ :
      ∀ {α A} →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _) →
      WfTy α A
    wfOlder′ (here refl) = wf★
    wfOlder′ (there h) = wfOlder shifted h

≤-from-< :
  ∀ {α β} →
  β < α →
  β ≤ α
≤-from-< {β = β} β<α = ≤-trans (n≤1+n β) β<α

------------------------------------------------------------------------
-- StoreWf-backed replacements for the old id/seal conflicts
------------------------------------------------------------------------

mutual
  narrowing-var-to-older⊥ :
    ∀ {μ Δ Σ c α B} →
    StoreDetWf Δ Σ →
    WfTy α B →
    μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊒ B →
    ⊥
  narrowing-var-to-older⊥ wfΣ (wfVar α<α)
      (cast-id hA id-ok , n-cross cn-id-var) =
    <-irrefl refl α<α
  narrowing-var-to-older⊥ wfΣ wfBase
      (() , n-cross cn-id-base)
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ wfBase
      (c⊢ , n-cross ())
  narrowing-var-to-older⊥ wfΣ wfBase
      (cast-seq () s⊢ , n-untag gG′ sⁿ)
  narrowing-var-to-older⊥ wfΣ wfBase
      (cast-seq s⊢ () , n-seal sⁿ)
  narrowing-var-to-older⊥ wfΣ wf★
      (() , n-id★)
  narrowing-var-to-older⊥ wfΣ wf★
      (() , n-cross cn-id-var)
  narrowing-var-to-older⊥ wfΣ wf★
      (() , n-cross cn-id-base)
  narrowing-var-to-older⊥ wfΣ wf★
      (() , n-cross (cn-fun sʷ tⁿ))
  narrowing-var-to-older⊥ wfΣ wf★
      (() , n-cross (cn-all sⁿ))
  narrowing-var-to-older⊥ wfΣ wf★
      (cast-seq () s⊢ , n-untag gG′ sⁿ)
  narrowing-var-to-older⊥ wfΣ wf★
      (cast-seq s⊢ () , n-seal sⁿ)
  narrowing-var-to-older⊥ wfΣ (wf⇒ hB hC)
      (() , n-cross (cn-fun sʷ tⁿ))
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ (wf⇒ hB hC)
      (c⊢ , n-cross ())
  narrowing-var-to-older⊥ wfΣ (wf⇒ hB hC)
      (cast-seq () s⊢ , n-untag gG′ sⁿ)
  narrowing-var-to-older⊥ wfΣ (wf⇒ hB hC)
      (cast-seq s⊢ () , n-seal sⁿ)
  narrowing-var-to-older⊥ wfΣ (wf∀ hB)
      (() , n-cross (cn-all sⁿ))
  narrowing-var-to-older⊥ wfΣ (wf∀ hB)
      (cast-gen hA occ s⊢ , n-gen sⁿ) =
    narrowing-var-to-older⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      hB
      (s⊢ , sⁿ)
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ (wf∀ hB)
      (c⊢ , n-cross ())
  narrowing-var-to-older⊥ wfΣ (wf∀ hB)
      (cast-seq () s⊢ , n-untag gG′ sⁿ)
  narrowing-var-to-older⊥ wfΣ (wf∀ hB)
      (cast-seq s⊢ () , n-seal sⁿ)
  narrowing-var-to-older⊥ wfΣ (wfVar β<α)
      (cast-seq () s⊢ , n-untag gG′ sⁿ)
  narrowing-var-to-older⊥ wfΣ (wfVar β<α)
      (cast-seq s⊢ (cast-seal hA β∈Σ seal-ok) , n-seal sⁿ) =
    narrowing-var-to-older⊥
      wfΣ
      (WfTy-weakenᵗ (wfOlder wfΣ β∈Σ) (≤-from-< β<α))
      (s⊢ , sⁿ)

  widening-older-to-var⊥ :
    ∀ {μ Δ Σ c α A} →
    StoreDetWf Δ Σ →
    WfTy α A →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ (＇ α) →
    ⊥
  widening-older-to-var⊥ wfΣ (wfVar α<α)
      (cast-id hA id-ok , w-cross cw-id-var) =
    <-irrefl refl α<α
  widening-older-to-var⊥ wfΣ wfBase
      (() , w-cross cw-id-base)
  widening-older-to-var⊥ {c = seal A β} wfΣ wfBase
      (c⊢ , w-cross ())
  widening-older-to-var⊥ wfΣ wfBase
      (cast-seq s⊢ () , w-tag gG′ sʷ)
  widening-older-to-var⊥ wfΣ wfBase
      (cast-seq () s⊢ , w-unseal sʷ)
  widening-older-to-var⊥ wfΣ wf★
      (() , w-id★)
  widening-older-to-var⊥ wfΣ wf★
      (() , w-cross cw-id-var)
  widening-older-to-var⊥ wfΣ wf★
      (() , w-cross cw-id-base)
  widening-older-to-var⊥ wfΣ wf★
      (() , w-cross (cw-fun sⁿ tʷ))
  widening-older-to-var⊥ wfΣ wf★
      (() , w-cross (cw-all sʷ))
  widening-older-to-var⊥ wfΣ wf★
      (cast-seq s⊢ () , w-tag gG′ sʷ)
  widening-older-to-var⊥ wfΣ wf★
      (cast-seq () s⊢ , w-unseal sʷ)
  widening-older-to-var⊥ wfΣ (wf⇒ hA hB)
      (() , w-cross (cw-fun sⁿ tʷ))
  widening-older-to-var⊥ {c = seal A β} wfΣ (wf⇒ hA hB)
      (c⊢ , w-cross ())
  widening-older-to-var⊥ wfΣ (wf⇒ hA hB)
      (cast-seq s⊢ () , w-tag gG′ sʷ)
  widening-older-to-var⊥ wfΣ (wf⇒ hA hB)
      (cast-seq () s⊢ , w-unseal sʷ)
  widening-older-to-var⊥ wfΣ (wf∀ hA)
      (() , w-cross (cw-all sʷ))
  widening-older-to-var⊥ wfΣ (wf∀ hA)
      (cast-inst hB occ s⊢ , w-inst sʷ) =
    widening-older-to-var⊥
      (StoreDetWf-inst wfΣ)
      hA
      (s⊢ , sʷ)
  widening-older-to-var⊥ {c = seal A β} wfΣ (wf∀ hA)
      (c⊢ , w-cross ())
  widening-older-to-var⊥ wfΣ (wf∀ hA)
      (cast-seq s⊢ () , w-tag gG′ sʷ)
  widening-older-to-var⊥ wfΣ (wf∀ hA)
      (cast-seq () s⊢ , w-unseal sʷ)
  widening-older-to-var⊥ wfΣ (wfVar β<α)
      (cast-seq s⊢ () , w-tag gG′ sʷ)
  widening-older-to-var⊥ wfΣ (wfVar β<α)
      (cast-seq (cast-unseal hA β∈Σ seal-ok) s⊢ , w-unseal sʷ) =
    widening-older-to-var⊥
      wfΣ
      (WfTy-weakenᵗ (wfOlder wfΣ β∈Σ) (≤-from-< β<α))
      (s⊢ , sʷ)

------------------------------------------------------------------------
-- Endpoint exclusions used by the expanded determinacy proof
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

tag-seal-conflict :
  ∀ {m} →
  tagModeAllowed m ≡ true →
  sealModeAllowed m ≡ true →
  ⊥
tag-seal-conflict {id-only} () ()
tag-seal-conflict {tag-or-id} tag-ok ()
tag-seal-conflict {seal-or-id} () seal-ok

∨-trueʳ :
  ∀ b →
  b ∨ true ≡ true
∨-trueʳ false = refl
∨-trueʳ true = refl

id-only-tag-conflict :
  ∀ {m} →
  m ≡ id-only →
  tagModeAllowed m ≡ true →
  ⊥
id-only-tag-conflict refl ()

id-only-seal-conflict :
  ∀ {m} →
  m ≡ id-only →
  sealModeAllowed m ≡ true →
  ⊥
id-only-seal-conflict refl ()

id-only-ground-tag-occurs⊥ :
  ∀ {μ : DualEnv} {α : TyVar} {G : Ty} →
  μ α ≡ id-only →
  Ground G →
  tagTyAllowed μ G ≡ true →
  occurs α G ≡ true →
  ⊥
id-only-ground-tag-occurs⊥ {μ = μ} {α = α} α-id (＇ β) tag-ok occ
    with α ≟ β
id-only-ground-tag-occurs⊥ {μ = μ} {α = α} α-id (＇ β)
    tag-ok occ | yes refl =
  id-only-tag-conflict α-id tag-ok
id-only-ground-tag-occurs⊥ α-id (＇ β) tag-ok () | no α≢β
id-only-ground-tag-occurs⊥ α-id (‵ ι) tag-ok ()
id-only-ground-tag-occurs⊥ α-id ★⇒★ tag-ok ()

id-only-seal-var-occurs⊥ :
  ∀ {μ : DualEnv} {α β : TyVar} →
  μ α ≡ id-only →
  sealModeAllowed (μ β) ≡ true →
  occurs α (＇ β) ≡ true →
  ⊥
id-only-seal-var-occurs⊥ {μ = μ} {α = α} {β = β} α-id seal-ok occ
    with α ≟ β
id-only-seal-var-occurs⊥ {μ = μ} {α = α} {β = β}
    α-id seal-ok occ | yes refl =
  id-only-seal-conflict α-id seal-ok
id-only-seal-var-occurs⊥ α-id seal-ok () | no α≢β

data Occurs : TyVar → Ty → Set where
  occ-var :
    ∀ {α} →
    Occurs α (＇ α)

  occ-fun₁ :
    ∀ {α A B} →
    Occurs α A →
    Occurs α (A ⇒ B)

  occ-fun₂ :
    ∀ {α A B} →
    Occurs α B →
    Occurs α (A ⇒ B)

  occ-all :
    ∀ {α A} →
    Occurs (suc α) A →
    Occurs α (`∀ A)

occurs-var-true→≡ :
  ∀ {α β} →
  occurs α (＇ β) ≡ true →
  α ≡ β
occurs-var-true→≡ {α = α} {β = β} occ with α ≟ β
occurs-var-true→≡ {α = α} {β = .α} occ | yes refl = refl
occurs-var-true→≡ occ | no α≢β = ⊥-elim (false≢true occ)

occurs-true→Occurs :
  ∀ {α A} →
  occurs α A ≡ true →
  Occurs α A
occurs-true→Occurs {A = ＇ β} occ
    with occurs-var-true→≡ occ
occurs-true→Occurs {A = ＇ β} occ | refl = occ-var
occurs-true→Occurs {A = ‵ ι} ()
occurs-true→Occurs {A = ★} ()
occurs-true→Occurs {α = α} {A = A ⇒ B} occ
    with occurs α A | inspect (occurs α) A
occurs-true→Occurs {α = α} {A = A ⇒ B} occ
    | true | [ eq ] =
  occ-fun₁ (occurs-true→Occurs eq)
occurs-true→Occurs {α = α} {A = A ⇒ B} occ
    | false | [ eq ] =
  occ-fun₂ (occurs-true→Occurs occ)
occurs-true→Occurs {A = `∀ A} occ =
  occ-all (occurs-true→Occurs occ)

Occurs→occurs-true :
  ∀ {α A} →
  Occurs α A →
  occurs α A ≡ true
Occurs→occurs-true {α = α} occ-var with α ≟ α
Occurs→occurs-true {α = α} occ-var | yes refl = refl
Occurs→occurs-true {α = α} occ-var | no α≢α = ⊥-elim (α≢α refl)
Occurs→occurs-true (occ-fun₁ occ)
    rewrite Occurs→occurs-true occ =
  refl
Occurs→occurs-true {α = α} {A = A ⇒ B} (occ-fun₂ occ)
    with occurs α A
Occurs→occurs-true {α = α} {A = A ⇒ B} (occ-fun₂ occ)
    | false =
  Occurs→occurs-true occ
Occurs→occurs-true {α = α} {A = A ⇒ B} (occ-fun₂ occ)
    | true =
  refl
Occurs→occurs-true (occ-all occ) =
  Occurs→occurs-true occ

mutual
  data NarrowPath (α : TyVar) : Ty → Ty → Set where
    np-var :
      NarrowPath α (＇ α) (＇ α)

    np-fun₁ :
      ∀ {A A′ B B′} →
      WidenPath α A′ A →
      NarrowPath α (A ⇒ B) (A′ ⇒ B′)

    np-fun₂ :
      ∀ {A A′ B B′} →
      NarrowPath α B B′ →
      NarrowPath α (A ⇒ B) (A′ ⇒ B′)

    np-all :
      ∀ {A B} →
      NarrowPath (suc α) A B →
      NarrowPath α (`∀ A) (`∀ B)

    np-gen :
      ∀ {A B} →
      NarrowPath (suc α) (⇑ᵗ A) B →
      NarrowPath α A (`∀ B)

  data WidenPath (α : TyVar) : Ty → Ty → Set where
    wp-var :
      WidenPath α (＇ α) (＇ α)

    wp-fun₁ :
      ∀ {A A′ B B′} →
      NarrowPath α A′ A →
      WidenPath α (A ⇒ B) (A′ ⇒ B′)

    wp-fun₂ :
      ∀ {A A′ B B′} →
      WidenPath α B B′ →
      WidenPath α (A ⇒ B) (A′ ⇒ B′)

    wp-all :
      ∀ {A B} →
      WidenPath (suc α) A B →
      WidenPath α (`∀ A) (`∀ B)

    wp-inst :
      ∀ {A B} →
      WidenPath (suc α) A (⇑ᵗ B) →
      WidenPath α (`∀ A) B

mutual
  narrowing-target-path-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Occurs α B →
    NarrowPath α A B
  narrowing-target-path-id-only α-id (c⊢ , n-cross cⁿ) occ =
    narrowing-cross-target-path-id-only α-id (c⊢ , cⁿ) occ
  narrowing-target-path-id-only α-id (cast-id wf★ ok , n-id★) ()
  narrowing-target-path-id-only {α = α} α-id
      (cast-gen {A = A} hA occB c⊢ , n-gen cⁿ) (occ-all occ) =
    np-gen
      (narrowing-target-path-id-only {α = suc α} α-id (c⊢ , cⁿ) occ)
  narrowing-target-path-id-only α-id
      (cast-seq (cast-untag hG gG tag-ok) c⊢ , n-untag gG′ cⁿ)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (narrowing-cross-target-id-only
          α-id (c⊢ , cⁿ) (Occurs→occurs-true occ)))
  narrowing-target-path-id-only α-id
      (cast-seq c⊢ (cast-seal {α = β} hA β∈Σ seal-ok) ,
       n-seal cⁿ)
      occ =
    ⊥-elim
      (id-only-seal-var-occurs⊥
        α-id seal-ok (Occurs→occurs-true occ))

  narrowing-cross-target-path-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossNarrowing c →
    Occurs α B →
    NarrowPath α A B
  narrowing-cross-target-path-id-only α-id
      (cast-id {A = ＇ β} hA id-ok , cn-id-var) occ-var =
    np-var
  narrowing-cross-target-path-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , cn-id-base) ()
  narrowing-cross-target-path-id-only α-id
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ) (occ-fun₁ occ) =
    np-fun₁ (widening-source-path-id-only α-id (s⊢ , sʷ) occ)
  narrowing-cross-target-path-id-only α-id
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ) (occ-fun₂ occ) =
    np-fun₂ (narrowing-target-path-id-only α-id (t⊢ , tⁿ) occ)
  narrowing-cross-target-path-id-only {α = α} α-id
      (cast-all c⊢ , cn-all cⁿ) (occ-all occ) =
    np-all
      (narrowing-target-path-id-only {α = suc α} α-id (c⊢ , cⁿ) occ)

  widening-source-path-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Occurs α A →
    WidenPath α A B
  widening-source-path-id-only α-id (c⊢ , w-cross cʷ) occ =
    widening-cross-source-path-id-only α-id (c⊢ , cʷ) occ
  widening-source-path-id-only α-id (cast-id wf★ ok , w-id★) ()
  widening-source-path-id-only {α = α} α-id
      (cast-inst {B = B} hB occA c⊢ , w-inst cʷ) (occ-all occ) =
    wp-inst
      (widening-source-path-id-only {α = suc α} α-id (c⊢ , cʷ) occ)
  widening-source-path-id-only α-id
      (cast-seq c⊢ (cast-tag hG gG tag-ok) , w-tag gG′ cʷ)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (widening-cross-source-id-only
          α-id (c⊢ , cʷ) (Occurs→occurs-true occ)))
  widening-source-path-id-only α-id
      (cast-seq (cast-unseal {α = β} hA β∈Σ seal-ok) c⊢ ,
       w-unseal cʷ)
      occ =
    ⊥-elim
      (id-only-seal-var-occurs⊥
        α-id seal-ok (Occurs→occurs-true occ))

  widening-cross-source-path-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossWidening c →
    Occurs α A →
    WidenPath α A B
  widening-cross-source-path-id-only α-id
      (cast-id {A = ＇ β} hA id-ok , cw-id-var) occ-var =
    wp-var
  widening-cross-source-path-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , cw-id-base) ()
  widening-cross-source-path-id-only α-id
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ) (occ-fun₁ occ) =
    wp-fun₁ (narrowing-target-path-id-only α-id (s⊢ , sⁿ) occ)
  widening-cross-source-path-id-only α-id
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ) (occ-fun₂ occ) =
    wp-fun₂ (widening-source-path-id-only α-id (t⊢ , tʷ) occ)
  widening-cross-source-path-id-only {α = α} α-id
      (cast-all c⊢ , cw-all cʷ) (occ-all occ) =
    wp-all
      (widening-source-path-id-only {α = suc α} α-id (c⊢ , cʷ) occ)

  narrowing-target-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    occurs α B ≡ true →
    occurs α A ≡ true
  narrowing-target-id-only α-id (c⊢ , n-cross cⁿ) occ =
    narrowing-cross-target-id-only α-id (c⊢ , cⁿ) occ
  narrowing-target-id-only α-id (cast-id wf★ ok , n-id★) ()
  narrowing-target-id-only {α = α} α-id
      (cast-gen {A = A} hA occB c⊢ , n-gen cⁿ) occ =
    trans
      (sym (occurs-raise zero α A))
      (narrowing-target-id-only {α = suc α} α-id (c⊢ , cⁿ) occ)
  narrowing-target-id-only α-id
      (cast-seq (cast-untag hG gG tag-ok) c⊢ , n-untag gG′ cⁿ)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (narrowing-cross-target-id-only α-id (c⊢ , cⁿ) occ))
  narrowing-target-id-only α-id
      (cast-seq c⊢ (cast-seal {α = β} hA β∈Σ seal-ok) , n-seal cⁿ)
      occ =
    ⊥-elim (id-only-seal-var-occurs⊥ α-id seal-ok occ)

  narrowing-cross-target-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossNarrowing c →
    occurs α B ≡ true →
    occurs α A ≡ true
  narrowing-cross-target-id-only α-id
      (cast-id {A = ＇ β} hA id-ok , cn-id-var) occ =
    occ
  narrowing-cross-target-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , cn-id-base) ()
  narrowing-cross-target-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       cn-fun sʷ tⁿ)
      occ
      with occurs α A′ | inspect (occurs α) A′
  narrowing-cross-target-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       cn-fun sʷ tⁿ)
      occ | true | [ eqA′ ]
      rewrite widening-source-id-only α-id (s⊢ , sʷ) eqA′ =
    refl
  narrowing-cross-target-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       cn-fun sʷ tⁿ)
      occ | false | [ eqA′ ]
      rewrite narrowing-target-id-only α-id (t⊢ , tⁿ) occ =
    ∨-trueʳ (occurs α A)
  narrowing-cross-target-id-only {α = α} α-id
      (cast-all c⊢ , cn-all cⁿ) occ =
    narrowing-target-id-only {α = suc α} α-id (c⊢ , cⁿ) occ

  widening-source-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    occurs α A ≡ true →
    occurs α B ≡ true
  widening-source-id-only α-id (c⊢ , w-cross cʷ) occ =
    widening-cross-source-id-only α-id (c⊢ , cʷ) occ
  widening-source-id-only α-id (cast-id wf★ ok , w-id★) ()
  widening-source-id-only {α = α} α-id
      (cast-inst {B = B} hB occA c⊢ , w-inst cʷ) occ =
    trans
      (sym (occurs-raise zero α B))
      (widening-source-id-only {α = suc α} α-id (c⊢ , cʷ) occ)
  widening-source-id-only α-id
      (cast-seq c⊢ (cast-tag hG gG tag-ok) , w-tag gG′ cʷ)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (widening-cross-source-id-only α-id (c⊢ , cʷ) occ))
  widening-source-id-only α-id
      (cast-seq (cast-unseal {α = β} hA β∈Σ seal-ok) c⊢ ,
       w-unseal cʷ)
      occ =
    ⊥-elim (id-only-seal-var-occurs⊥ α-id seal-ok occ)

  widening-cross-source-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossWidening c →
    occurs α A ≡ true →
    occurs α B ≡ true
  widening-cross-source-id-only α-id
      (cast-id {A = ＇ β} hA id-ok , cw-id-var) occ =
    occ
  widening-cross-source-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , cw-id-base) ()
  widening-cross-source-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       cw-fun sⁿ tʷ)
      occ
      with occurs α A | inspect (occurs α) A
  widening-cross-source-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       cw-fun sⁿ tʷ)
      occ | true | [ eqA ]
      rewrite narrowing-target-id-only α-id (s⊢ , sⁿ) eqA =
    refl
  widening-cross-source-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       cw-fun sⁿ tʷ)
      occ | false | [ eqA ]
      rewrite widening-source-id-only α-id (t⊢ , tʷ) occ =
    ∨-trueʳ (occurs α A′)
  widening-cross-source-id-only {α = α} α-id
      (cast-all c⊢ , cw-all cʷ) occ =
    widening-source-id-only {α = suc α} α-id (c⊢ , cʷ) occ

narrowing-cross-ground-target-star⊥ :
  ∀ {μ Δ Σ G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ ★) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-star⊥ (＇ α)
    (() , cn-id-var)
narrowing-cross-ground-target-star⊥ (‵ ι)
    (() , cn-id-base)
narrowing-cross-ground-target-star⊥ ★⇒★
    (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-star⊥ gG
    (() , cn-all gⁿ)

widening-cross-ground-source-star⊥ :
  ∀ {μ Δ Σ G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ ★ =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-star⊥ (＇ α)
    (() , cw-id-var)
widening-cross-ground-source-star⊥ (‵ ι)
    (() , cw-id-base)
widening-cross-ground-source-star⊥ ★⇒★
    (() , cw-fun sⁿ tʷ)
widening-cross-ground-source-star⊥ gG
    (() , cw-all gʷ)

widening-cross-ground-source-all⊥ :
  ∀ {μ Δ Σ A G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ `∀ A =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-all⊥ (＇ α)
    (() , cw-id-var)
widening-cross-ground-source-all⊥ (‵ ι)
    (() , cw-id-base)
widening-cross-ground-source-all⊥ ★⇒★
    (() , cw-fun sⁿ tʷ)
widening-cross-ground-source-all⊥ (＇ α)
    (() , cw-all gʷ)
widening-cross-ground-source-all⊥ (‵ ι)
    (() , cw-all gʷ)
widening-cross-ground-source-all⊥ ★⇒★
    (() , cw-all gʷ)

narrowing-cross-ground-target-all⊥ :
  ∀ {μ Δ Σ A G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ `∀ A) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-all⊥ (＇ α)
    (() , cn-id-var)
narrowing-cross-ground-target-all⊥ (‵ ι)
    (() , cn-id-base)
narrowing-cross-ground-target-all⊥ ★⇒★
    (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-all⊥ (＇ α)
    (() , cn-all gⁿ)
narrowing-cross-ground-target-all⊥ (‵ ι)
    (() , cn-all gⁿ)
narrowing-cross-ground-target-all⊥ ★⇒★
    (() , cn-all gⁿ)

narrowing-cross-ground-target-seal-var⊥ :
  ∀ {μ Δ Σ G A α g} →
  StoreDetWf Δ Σ →
  Ground G →
  tagTyAllowed μ G ≡ true →
  (α , A) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ (＇ α)) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-seal-var⊥ wfΣ (＇ α) tag-ok
    α∈Σ seal-ok (cast-id hA id-ok , cn-id-var) =
  tag-seal-conflict tag-ok seal-ok
narrowing-cross-ground-target-seal-var⊥ wfΣ (‵ ι) tag-ok
    α∈Σ seal-ok (() , cn-id-base)
narrowing-cross-ground-target-seal-var⊥ wfΣ ★⇒★ tag-ok
    α∈Σ seal-ok (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-seal-var⊥ wfΣ gG tag-ok
    α∈Σ seal-ok (() , cn-all gⁿ)

widening-cross-ground-source-seal-var⊥ :
  ∀ {μ Δ Σ G A α g} →
  StoreDetWf Δ Σ →
  Ground G →
  tagTyAllowed μ G ≡ true →
  (α , A) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (＇ α) =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-seal-var⊥ wfΣ (＇ α) tag-ok
    α∈Σ seal-ok (cast-id hA id-ok , cw-id-var) =
  tag-seal-conflict tag-ok seal-ok
widening-cross-ground-source-seal-var⊥ wfΣ (‵ ι) tag-ok
    α∈Σ seal-ok (() , cw-id-base)
widening-cross-ground-source-seal-var⊥ wfΣ ★⇒★ tag-ok
    α∈Σ seal-ok (() , cw-fun sⁿ tʷ)
widening-cross-ground-source-seal-var⊥ wfΣ gG tag-ok
    α∈Σ seal-ok (() , cw-all gʷ)

tag-or-id-seal-conflict :
  ∀ {μ : DualEnv} {α} →
  μ α ≡ tag-or-id →
  sealModeAllowed (μ α) ≡ true →
  ⊥
tag-or-id-seal-conflict tag-ok seal-ok rewrite tag-ok =
  false≢true seal-ok

seal-or-id-tag-conflict :
  ∀ {μ : DualEnv} {α} →
  μ α ≡ seal-or-id →
  tagModeAllowed (μ α) ≡ true →
  ⊥
seal-or-id-tag-conflict seal-ok tag-ok rewrite seal-ok =
  false≢true tag-ok

narrowing-all-to-var-tag⊥ :
  ∀ {μ Δ Σ A α c} →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ A) ⊒ (＇ α) →
  ⊥
narrowing-all-to-var-tag⊥ tag-ok (() , n-cross cn-id-var)
narrowing-all-to-var-tag⊥ tag-ok (() , n-cross cn-id-base)
narrowing-all-to-var-tag⊥ tag-ok (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-var-tag⊥ tag-ok (() , n-cross (cn-all sⁿ))
narrowing-all-to-var-tag⊥ tag-ok (() , n-id★)
narrowing-all-to-var-tag⊥ tag-ok (() , n-gen sⁿ)
narrowing-all-to-var-tag⊥ tag-ok (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-var-tag⊥ {μ = μ} {α = α} tag-ok
    (cast-seq s⊢ (cast-seal {α = .α} hA α∈Σ seal-ok) ,
     n-seal sⁿ) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok

narrowing-all-to-fun⊥ :
  ∀ {μ Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ A) ⊒ (B ⇒ C) →
  ⊥
narrowing-all-to-fun⊥ (() , n-cross cn-id-var)
narrowing-all-to-fun⊥ (() , n-cross cn-id-base)
narrowing-all-to-fun⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-fun⊥ (() , n-cross (cn-all sⁿ))
narrowing-all-to-fun⊥ (() , n-id★)
narrowing-all-to-fun⊥ (() , n-gen sⁿ)
narrowing-all-to-fun⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-fun⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-all-to-star⊥ :
  ∀ {μ Δ Σ A c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ A) ⊒ ★ →
  ⊥
narrowing-all-to-star⊥ (() , n-cross cn-id-var)
narrowing-all-to-star⊥ (() , n-cross cn-id-base)
narrowing-all-to-star⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-star⊥ (() , n-cross (cn-all sⁿ))
narrowing-all-to-star⊥ (() , n-id★)
narrowing-all-to-star⊥ (() , n-gen sⁿ)
narrowing-all-to-star⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-star⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-var-to-star⊥ :
  ∀ {μ Δ Σ α c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊒ ★ →
  ⊥
narrowing-var-to-star⊥ (() , n-cross cn-id-var)
narrowing-var-to-star⊥ (() , n-cross cn-id-base)
narrowing-var-to-star⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-var-to-star⊥ (() , n-cross (cn-all sⁿ))
narrowing-var-to-star⊥ (() , n-id★)
narrowing-var-to-star⊥ (() , n-gen sⁿ)
narrowing-var-to-star⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-var-to-star⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-var≢-to-var-tag⊥ :
  ∀ {μ Δ Σ α β c} →
  β ≢ α →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ β) ⊒ (＇ α) →
  ⊥
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-id hA id-ok , n-cross cn-id-var) =
  β≢α refl
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (() , n-cross cn-id-base)
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (() , n-cross (cn-fun sʷ tⁿ))
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (() , n-cross (cn-all sⁿ))
narrowing-var≢-to-var-tag⊥ β≢α tag-ok (() , n-id★)
narrowing-var≢-to-var-tag⊥ β≢α tag-ok (() , n-gen sⁿ)
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-var≢-to-var-tag⊥ {μ = μ} {α = α} β≢α tag-ok
    (cast-seq s⊢ (cast-seal {α = .α} hA α∈Σ seal-ok) ,
     n-seal sⁿ) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok

narrowing-skew-var-to-var-tag⊥ :
  ∀ {μ Δ Σ α β c} →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ (raiseVarFrom α β)) ⊒ (＇ α) →
  ⊥
narrowing-skew-var-to-var-tag⊥ {α = α} {β = β} tag-ok t⊒ =
  narrowing-var≢-to-var-tag⊥ {α = α} {β = raiseVarFrom α β}
    (raiseVarFrom-≢ α β)
    tag-ok
    t⊒

widening-var-to-all-tag⊥ :
  ∀ {μ Δ Σ α B c} →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (`∀ B) →
  ⊥
widening-var-to-all-tag⊥ tag-ok (() , w-cross cw-id-var)
widening-var-to-all-tag⊥ tag-ok (() , w-cross cw-id-base)
widening-var-to-all-tag⊥ tag-ok (() , w-cross (cw-fun sⁿ tʷ))
widening-var-to-all-tag⊥ tag-ok (() , w-cross (cw-all sʷ))
widening-var-to-all-tag⊥ tag-ok (() , w-id★)
widening-var-to-all-tag⊥ tag-ok (() , w-inst sʷ)
widening-var-to-all-tag⊥ tag-ok (cast-seq s⊢ () , w-tag gG sʷ)
widening-var-to-all-tag⊥ {μ = μ} {α = α} tag-ok
    (cast-seq (cast-unseal {α = .α} hA α∈Σ seal-ok) s⊢ ,
     w-unseal sʷ) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok

widening-var≢-to-var-tag⊥ :
  ∀ {μ Δ Σ α β c} →
  β ≢ α →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ β) →
  ⊥
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-id hA id-ok , w-cross cw-id-var) =
  β≢α refl
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (() , w-cross cw-id-base)
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (() , w-cross (cw-fun sⁿ tʷ))
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (() , w-cross (cw-all sʷ))
widening-var≢-to-var-tag⊥ β≢α tag-ok (() , w-id★)
widening-var≢-to-var-tag⊥ β≢α tag-ok (() , w-inst sʷ)
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-var≢-to-var-tag⊥ {μ = μ} {α = α} β≢α tag-ok
    (cast-seq (cast-unseal {α = .α} hA α∈Σ seal-ok) s⊢ ,
     w-unseal sʷ) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok

widening-var-to-skew-var-tag⊥ :
  ∀ {μ Δ Σ α β c} →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ (raiseVarFrom α β)) →
  ⊥
widening-var-to-skew-var-tag⊥ {α = α} {β = β} tag-ok t⊑ =
  widening-var≢-to-var-tag⊥ {α = α} {β = raiseVarFrom α β}
    (raiseVarFrom-≢ α β)
    tag-ok
    t⊑

widening-star-to-all⊥ :
  ∀ {μ Δ Σ B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊑ (`∀ B) →
  ⊥
widening-star-to-all⊥ (() , w-cross cw-id-var)
widening-star-to-all⊥ (() , w-cross cw-id-base)
widening-star-to-all⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-star-to-all⊥ (() , w-cross (cw-all sʷ))
widening-star-to-all⊥ (() , w-id★)
widening-star-to-all⊥ (() , w-inst sʷ)
widening-star-to-all⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-star-to-all⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-fun-to-all⊥ :
  ∀ {μ Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) ⊑ (`∀ C) →
  ⊥
widening-fun-to-all⊥ (() , w-cross cw-id-var)
widening-fun-to-all⊥ (() , w-cross cw-id-base)
widening-fun-to-all⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-fun-to-all⊥ (() , w-cross (cw-all sʷ))
widening-fun-to-all⊥ (() , w-id★)
widening-fun-to-all⊥ (() , w-inst sʷ)
widening-fun-to-all⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-fun-to-all⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-star-to-var⊥ :
  ∀ {μ Δ Σ α c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊑ (＇ α) →
  ⊥
widening-star-to-var⊥ (() , w-cross cw-id-var)
widening-star-to-var⊥ (() , w-cross cw-id-base)
widening-star-to-var⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-star-to-var⊥ (() , w-cross (cw-all sʷ))
widening-star-to-var⊥ (() , w-id★)
widening-star-to-var⊥ (() , w-inst sʷ)
widening-star-to-var⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-star-to-var⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-var-to-all-seal⊥ :
  ∀ {μ Δ Σ α B c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (`∀ B) →
  ⊥
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , w-cross cw-id-var)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , w-cross cw-id-base)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , w-cross (cw-fun sⁿ tʷ))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , w-cross (cw-all sʷ))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok (() , w-id★)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok (() , w-inst sʷ)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) t⊢ , w-unseal tʷ)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  widening-star-to-all⊥ (t⊢ , tʷ)

widening-var≢-to-var-seal⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  β ≢ α →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ β) →
  ⊥
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-id hA id-ok , w-cross cw-id-var) =
  β≢α refl
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (() , w-cross cw-id-base)
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (() , w-cross (cw-fun sⁿ tʷ))
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (() , w-cross (cw-all sʷ))
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok (() , w-id★)
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok (() , w-inst sʷ)
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) t⊢ , w-unseal tʷ)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  widening-star-to-var⊥ (t⊢ , tʷ)

widening-var-to-skew-var-seal⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ (raiseVarFrom α β)) →
  ⊥
widening-var-to-skew-var-seal⊥ {α = α} {β = β} wfΣ α↦★
    seal-ok t⊑ =
  widening-var≢-to-var-seal⊥ {α = α} {β = raiseVarFrom α β}
    wfΣ
    α↦★
    (raiseVarFrom-≢ α β)
    seal-ok
    t⊑

narrowing-all-to-var-seal⊥ :
  ∀ {μ Δ Σ A α c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ A) ⊒ (＇ α) →
  ⊥
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , n-cross cn-id-var)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , n-cross cn-id-base)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , n-cross (cn-all sⁿ))
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok (() , n-id★)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok (() , n-gen sⁿ)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  narrowing-all-to-star⊥ (s⊢ , sⁿ)

narrowing-var≢-to-var-seal⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  β ≢ α →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ β) ⊒ (＇ α) →
  ⊥
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-id hA id-ok , n-cross cn-id-var) =
  β≢α refl
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (() , n-cross cn-id-base)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (() , n-cross (cn-fun sʷ tⁿ))
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (() , n-cross (cn-all sⁿ))
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok (() , n-id★)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok (() , n-gen sⁿ)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  narrowing-var-to-star⊥ (s⊢ , sⁿ)

narrowing-skew-var-to-var-seal⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ (raiseVarFrom α β)) ⊒ (＇ α) →
  ⊥
narrowing-skew-var-to-var-seal⊥ {α = α} {β = β} wfΣ α↦★
    seal-ok t⊒ =
  narrowing-var≢-to-var-seal⊥ {α = α} {β = raiseVarFrom α β}
    wfΣ
    α↦★
    (raiseVarFrom-≢ α β)
    seal-ok
    t⊒

data TargetSkew : TyVar → TyVar → Ty → Ty → Set where
  skew-var :
    ∀ {κ α β} →
    TargetSkew κ α
      (＇ (raiseVarFrom κ β))
      (＇ (raiseVarFrom α β))

  skew-base :
    ∀ {κ α ι} →
    TargetSkew κ α (‵ ι) (‵ ι)

  skew-star :
    ∀ {κ α} →
    TargetSkew κ α ★ ★

  skew-fun :
    ∀ {κ α A A′ B B′} →
    TargetSkew κ α A A′ →
    TargetSkew κ α B B′ →
    TargetSkew κ α (A ⇒ B) (A′ ⇒ B′)

  skew-all :
    ∀ {κ α A A′} →
    TargetSkew (suc κ) (suc α) A A′ →
    TargetSkew κ α (`∀ A) (`∀ A′)

target-skew-rename :
  ∀ κ α A →
  TargetSkew κ α
    (renameᵗ (raiseVarFrom κ) A)
    (renameᵗ (raiseVarFrom α) A)
target-skew-rename κ α (＇ β) = skew-var
target-skew-rename κ α (‵ ι) = skew-base
target-skew-rename κ α ★ = skew-star
target-skew-rename κ α (A ⇒ B) =
  skew-fun (target-skew-rename κ α A) (target-skew-rename κ α B)
target-skew-rename κ α (`∀ A) =
  skew-all
    (subst
      (λ T → TargetSkew (suc κ) (suc α)
        (renameᵗ (extᵗ (raiseVarFrom κ)) A)
        T)
      (sym (rename-raise-ext α A))
      (subst
        (λ T → TargetSkew (suc κ) (suc α)
          T
          (renameᵗ (raiseVarFrom (suc α)) A))
        (sym (rename-raise-ext κ A))
        (target-skew-rename (suc κ) (suc α) A)))

data EndpointGap : TyVar → Ty → Ty → Set where
  end-insert :
    ∀ {α B} →
    EndpointGap α B (renameᵗ (raiseVarFrom α) (`∀ B))

  end-skew :
    ∀ {κ α B C} →
    TargetSkew κ α B C →
    EndpointGap α B C

  end-all :
    ∀ {α B C} →
    EndpointGap (suc α) B C →
    EndpointGap α (`∀ B) (`∀ C)

  end-shift :
    ∀ {α B C B′ C′} →
    EndpointGap α B C →
    B′ ≡ ⇑ᵗ B →
    C′ ≡ ⇑ᵗ C →
    EndpointGap (suc α) B′ C′

  end-right-inst-all :
    ∀ {α B C C′} →
    EndpointGap α (`∀ B) C →
    C′ ≡ ⇑ᵗ C →
    EndpointGap (suc α) B C′

  end-left-inst-all :
    ∀ {α B C B′} →
    EndpointGap α B (`∀ C) →
    B′ ≡ ⇑ᵗ B →
    EndpointGap (suc α) B′ C

target-skew-renamed :
  ∀ {κ α B C} →
  TargetSkew κ α B C →
  ∃[ T ] (B ≡ renameᵗ (raiseVarFrom κ) T ×
          C ≡ renameᵗ (raiseVarFrom α) T)
target-skew-renamed {κ = κ} {α = α} skew-var =
  ＇ _ , refl , refl
target-skew-renamed skew-base =
  ‵ _ , refl , refl
target-skew-renamed skew-star =
  ★ , refl , refl
target-skew-renamed (skew-fun sk₁ sk₂)
    with target-skew-renamed sk₁ | target-skew-renamed sk₂
target-skew-renamed (skew-fun sk₁ sk₂)
    | A , eqA₁ , eqA₂ | B , eqB₁ , eqB₂ =
  A ⇒ B , cong₂ _⇒_ eqA₁ eqB₁ , cong₂ _⇒_ eqA₂ eqB₂
target-skew-renamed {κ = κ} {α = α} (skew-all sk)
    with target-skew-renamed sk
target-skew-renamed {κ = κ} {α = α} (skew-all sk)
    | A , eqA₁ , eqA₂ =
  `∀ A ,
  cong `∀ (trans eqA₁ (sym (rename-raise-ext κ A))) ,
  cong `∀ (trans eqA₂ (sym (rename-raise-ext α A)))

data EndpointSpine : Ty → Ty → Set where
  spine-renamed :
    ∀ {L R T ρ τ} →
    L ≡ renameᵗ ρ T →
    R ≡ renameᵗ τ T →
    EndpointSpine L R

  spine-left-all :
    ∀ {L R} →
    EndpointSpine L R →
    EndpointSpine (`∀ L) R

  spine-right-all :
    ∀ {L R} →
    EndpointSpine L R →
    EndpointSpine L (`∀ R)

spine-map-left :
  ∀ ρ {L R} →
  EndpointSpine L R →
  EndpointSpine (renameᵗ ρ L) R
spine-map-left ρ (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = λ X → ρ (σ X)} {τ = τ}
    (renameᵗ-compose σ ρ T)
    refl
spine-map-left ρ (spine-left-all sp) =
  spine-left-all (spine-map-left (extᵗ ρ) sp)
spine-map-left ρ (spine-right-all sp) =
  spine-right-all (spine-map-left ρ sp)

spine-map-right :
  ∀ ρ {L R} →
  EndpointSpine L R →
  EndpointSpine L (renameᵗ ρ R)
spine-map-right ρ (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = σ} {τ = λ X → ρ (τ X)}
    refl
    (renameᵗ-compose τ ρ T)
spine-map-right ρ (spine-left-all sp) =
  spine-left-all (spine-map-right ρ sp)
spine-map-right ρ (spine-right-all sp) =
  spine-right-all (spine-map-right (extᵗ ρ) sp)

spine-peel-right :
  ∀ ρ {L R} →
  EndpointSpine L (`∀ R) →
  EndpointSpine (renameᵗ ρ L) R
spine-peel-right ρ (spine-renamed {T = ＇ β} eqL ())
spine-peel-right ρ (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right ρ (spine-renamed {T = ★} eqL ())
spine-peel-right ρ (spine-renamed {T = T₁ ⇒ T₂} eqL ())
spine-peel-right ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-left-all
    (spine-renamed {T = T}
      {ρ = λ X → extᵗ ρ (extᵗ σ X)}
      {τ = extᵗ τ}
      (renameᵗ-compose (extᵗ σ) (extᵗ ρ) T)
      refl)
spine-peel-right ρ (spine-left-all sp) =
  spine-left-all (spine-peel-right (extᵗ ρ) sp)
spine-peel-right ρ (spine-right-all sp) =
  spine-map-left ρ sp

spine-peel-left :
  ∀ ρ {L R} →
  EndpointSpine (`∀ L) R →
  EndpointSpine L (renameᵗ ρ R)
spine-peel-left ρ (spine-renamed {T = ＇ β} () eqR)
spine-peel-left ρ (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left ρ (spine-renamed {T = ★} () eqR)
spine-peel-left ρ (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-peel-left ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-right-all
    (spine-renamed {T = T}
      {ρ = extᵗ σ}
      {τ = λ X → extᵗ ρ (extᵗ τ X)}
      refl
      (renameᵗ-compose (extᵗ τ) (extᵗ ρ) T))
spine-peel-left ρ (spine-left-all sp) =
  spine-map-right ρ sp
spine-peel-left ρ (spine-right-all sp) =
  spine-right-all (spine-peel-left (extᵗ ρ) sp)

spine-peel-right-id :
  ∀ {L R} →
  EndpointSpine L (`∀ R) →
  EndpointSpine L R
spine-peel-right-id (spine-renamed {T = ＇ β} eqL ())
spine-peel-right-id (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right-id (spine-renamed {T = ★} eqL ())
spine-peel-right-id (spine-renamed {T = T₁ ⇒ T₂} eqL ())
spine-peel-right-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-left-all (spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ}
    refl refl)
spine-peel-right-id (spine-left-all sp) =
  spine-left-all (spine-peel-right-id sp)
spine-peel-right-id (spine-right-all sp) = sp

spine-peel-left-id :
  ∀ {L R} →
  EndpointSpine (`∀ L) R →
  EndpointSpine L R
spine-peel-left-id (spine-renamed {T = ＇ β} () eqR)
spine-peel-left-id (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left-id (spine-renamed {T = ★} () eqR)
spine-peel-left-id (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-peel-left-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-right-all (spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ}
    refl refl)
spine-peel-left-id (spine-left-all sp) = sp
spine-peel-left-id (spine-right-all sp) =
  spine-right-all (spine-peel-left-id sp)

spine-strip-both :
  ∀ {L R} →
  EndpointSpine (`∀ L) (`∀ R) →
  EndpointSpine L R
spine-strip-both (spine-renamed {T = ＇ β} () eqR)
spine-strip-both (spine-renamed {T = ‵ ι} () eqR)
spine-strip-both (spine-renamed {T = ★} () eqR)
spine-strip-both (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-strip-both
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ} refl refl
spine-strip-both (spine-left-all sp) = spine-peel-right-id sp
spine-strip-both (spine-right-all sp) = spine-peel-left-id sp

endpoint-gap-spine :
  ∀ {α B C} →
  EndpointGap α B C →
  EndpointSpine B C
endpoint-gap-spine (end-insert {α = α} {B = B}) =
  spine-right-all
    (spine-renamed {T = B} {ρ = λ X → X}
      {τ = extᵗ (raiseVarFrom α)}
      (sym (renameᵗ-id B)) refl)
endpoint-gap-spine (end-skew sk)
    with target-skew-renamed sk
endpoint-gap-spine (end-skew sk)
    | T , eqL , eqR =
  spine-renamed {T = T} eqL eqR
endpoint-gap-spine (end-all gap) =
  spine-left-all (spine-right-all (endpoint-gap-spine gap))
endpoint-gap-spine (end-shift gap refl refl) =
  spine-map-right suc (spine-map-left suc (endpoint-gap-spine gap))
endpoint-gap-spine (end-right-inst-all gap refl) =
  spine-peel-left suc (endpoint-gap-spine gap)
endpoint-gap-spine (end-left-inst-all gap refl) =
  spine-peel-right suc (endpoint-gap-spine gap)

endpoint-gap-fresh :
  ∀ {α B C} →
  EndpointGap α B C →
  occurs α C ≡ false
endpoint-gap-fresh (end-insert {α = α} {B = B}) =
  occurs-raise-fresh α (`∀ B)
endpoint-gap-fresh {α = α} (end-skew sk)
    with target-skew-renamed sk
endpoint-gap-fresh {α = α} (end-skew sk)
    | T , eqL , eqR
    rewrite eqR =
  occurs-raise-fresh α T
endpoint-gap-fresh (end-all gap) =
  endpoint-gap-fresh gap
endpoint-gap-fresh {α = suc α} (end-shift {α = α} {C = C} gap refl refl) =
  trans (occurs-raise zero α C) (endpoint-gap-fresh gap)
endpoint-gap-fresh {α = suc α}
    (end-right-inst-all {α = α} {C = C} gap refl) =
  trans (occurs-raise zero α C) (endpoint-gap-fresh gap)
endpoint-gap-fresh (end-left-inst-all gap refl) =
  endpoint-gap-fresh gap

∨-falseˡ :
  ∀ {b c} →
  b ∨ c ≡ false →
  b ≡ false
∨-falseˡ {false} eq = refl
∨-falseˡ {true} ()

∨-falseʳ :
  ∀ {b c} →
  b ∨ c ≡ false →
  c ≡ false
∨-falseʳ {b = false} eq = eq
∨-falseʳ {b = true} ()

occurs-var-false≢ :
  ∀ {α β} →
  occurs α (＇ β) ≡ false →
  β ≢ α
occurs-var-false≢ {α = α} fresh refl
    with α ≟ α
occurs-var-false≢ {α = α} fresh refl
    | yes refl =
  false≢true (sym fresh)
occurs-var-false≢ {α = α} fresh refl
    | no α≢α =
  α≢α refl

mutual
  narrowing-tag-spine-overlap⊥ :
    ∀ {μ Δ Σ A B C t α} →
    μ α ≡ tag-or-id →
    NarrowPath α A B →
    EndpointSpine A C →
    occurs α C ≡ false →
    μ ∣ Δ ∣ Σ ⊢ t ∶ C ⊒ B →
    ⊥
  narrowing-tag-spine-overlap⊥ tag-ok np-var
      (spine-renamed {T = ＇ β} refl refl) fresh t⊒ =
    narrowing-var≢-to-var-tag⊥
      (occurs-var-false≢ fresh) tag-ok t⊒
  narrowing-tag-spine-overlap⊥ tag-ok np-var
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-var-tag⊥ tag-ok t⊒
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ)) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sʷ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ)) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , n-cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , n-cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , n-untag gG tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , n-untag gG tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (np-all p)
      sp fresh (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-tag-spine-overlap⊥
      tag-ok p (spine-strip-both sp) fresh (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (np-all p)
      sp fresh (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-tag-spine-overlap⊥
      tag-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-id hA ok , n-cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-unseal hA α∈Σ ok , n-cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-inst hA occ t⊢ , n-cross ())
  narrowing-tag-spine-overlap⊥ {C = `∀ C} {α = α} tag-ok
      (np-gen p) sp fresh
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-tag-spine-overlap⊥
      tag-ok p (spine-peel-right suc sp) fresh (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ {C = C} {α = α} tag-ok
      (np-gen p) sp fresh (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-tag-spine-overlap⊥
      tag-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-id hA ok , n-cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-unseal hA α∈Σ ok , n-cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-inst hA occ t⊢ , n-cross ())

  widening-tag-spine-overlap⊥ :
    ∀ {μ Δ Σ A B C t α} →
    μ α ≡ tag-or-id →
    WidenPath α A B →
    EndpointSpine B C →
    occurs α C ≡ false →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ C →
    ⊥
  widening-tag-spine-overlap⊥ tag-ok wp-var
      (spine-renamed {T = ＇ β} refl refl) fresh t⊑ =
    widening-var≢-to-var-tag⊥
      (occurs-var-false≢ fresh) tag-ok t⊑
  widening-tag-spine-overlap⊥ tag-ok wp-var
      (spine-right-all sp) fresh t⊑ =
    widening-var-to-all-tag⊥ tag-ok t⊑
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ)) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sⁿ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ)) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , w-cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , w-cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , w-tag gG tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , w-tag gG tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (wp-all p)
      sp fresh (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-tag-spine-overlap⊥
      tag-ok p (spine-strip-both sp) fresh (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (wp-all p)
      sp fresh (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-tag-spine-overlap⊥
      tag-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tʷ) =
    widening-cross-ground-source-all⊥ gG (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-id hA ok , w-cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-seal hA α∈Σ ok , w-cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-gen hA occ t⊢ , w-cross ())
  widening-tag-spine-overlap⊥ {C = `∀ C} tag-ok (wp-inst p) sp
      fresh (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-tag-spine-overlap⊥
      tag-ok p (spine-peel-right suc sp) fresh (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ {C = C} {α = α} tag-ok
      (wp-inst p) sp fresh (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-tag-spine-overlap⊥
      tag-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tʷ) =
    widening-cross-ground-source-all⊥ gG (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-id hA ok , w-cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-seal hA α∈Σ ok , w-cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-gen hA occ t⊢ , w-cross ())

  narrowing-seal-spine-overlap⊥ :
    ∀ {μ Δ Σ A B C t α} →
    StoreDetWf Δ Σ →
    (α , ★) ∈ Σ →
    μ α ≡ seal-or-id →
    NarrowPath α A B →
    EndpointSpine A C →
    occurs α C ≡ false →
    μ ∣ Δ ∣ Σ ⊢ t ∶ C ⊒ B →
    ⊥
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok np-var
      (spine-renamed {T = ＇ β} refl refl) fresh t⊒ =
    narrowing-var≢-to-var-seal⊥ wfΣ α↦★
      (occurs-var-false≢ fresh) seal-ok t⊒
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok np-var
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok t⊒
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ)) =
    widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sʷ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ)) =
    narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , n-cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , n-cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , n-untag gG tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , n-untag gG tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-strip-both sp)
      fresh
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (np-all p) sp fresh (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-seq (cast-untag hG gG okG) t⊢ ,
                n-untag gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-id hA ok , n-cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-unseal hA α∈Σ ok , n-cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-inst hA occ t⊢ , n-cross ())
  narrowing-seal-spine-overlap⊥ {C = `∀ C} wfΣ α↦★ seal-ok
      (np-gen p) sp fresh (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-peel-right suc sp)
      fresh
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (np-gen p) sp fresh (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-seq (cast-untag hG gG okG) t⊢ ,
                n-untag gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-id hA ok , n-cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-unseal hA α∈Σ ok , n-cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-inst hA occ t⊢ , n-cross ())

  widening-seal-spine-overlap⊥ :
    ∀ {μ Δ Σ A B C t α} →
    StoreDetWf Δ Σ →
    (α , ★) ∈ Σ →
    μ α ≡ seal-or-id →
    WidenPath α A B →
    EndpointSpine B C →
    occurs α C ≡ false →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ C →
    ⊥
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok wp-var
      (spine-renamed {T = ＇ β} refl refl) fresh t⊑ =
    widening-var≢-to-var-seal⊥ wfΣ α↦★
      (occurs-var-false≢ fresh) seal-ok t⊑
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok wp-var
      (spine-right-all sp) fresh t⊑ =
    widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok t⊑
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ)) =
    narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sⁿ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ)) =
    widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , w-cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , w-cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , w-tag gG tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , w-tag gG tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-strip-both sp)
      fresh
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (wp-all p) sp fresh (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-inst wfΣ)
      (there (∈-renameStoreᵗ suc α↦★))
      seal-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-seq t⊢ (cast-tag hG gG okG) ,
                w-tag gG′ tʷ) =
    widening-cross-ground-source-all⊥ gG (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-id hA ok , w-cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-seal hA α∈Σ ok , w-cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-gen hA occ t⊢ , w-cross ())
  widening-seal-spine-overlap⊥ {C = `∀ C} wfΣ α↦★ seal-ok
      (wp-inst p) sp fresh (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-peel-right suc sp)
      fresh
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (wp-inst p) sp fresh (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-inst wfΣ)
      (there (∈-renameStoreᵗ suc α↦★))
      seal-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-seq t⊢ (cast-tag hG gG okG) ,
                w-tag gG′ tʷ) =
    widening-cross-ground-source-all⊥ gG (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-id hA ok , w-cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-seal hA α∈Σ ok , w-cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-gen hA occ t⊢ , w-cross ())

narrowing-tag-gap-overlap⊥ :
  ∀ {μ Δ Σ A B C t α} →
  μ α ≡ tag-or-id →
  EndpointGap α A C →
  NarrowPath α A B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ C ⊒ B →
  ⊥
narrowing-tag-gap-overlap⊥ tag-ok gap path t⊒ =
  narrowing-tag-spine-overlap⊥
    tag-ok path (endpoint-gap-spine gap) (endpoint-gap-fresh gap) t⊒

widening-seal-gap-overlap⊥ :
  ∀ {μ Δ Σ A B C t α} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  μ α ≡ seal-or-id →
  EndpointGap α B C →
  WidenPath α A B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ C →
  ⊥
widening-seal-gap-overlap⊥ wfΣ α↦★ seal-ok gap path t⊑ =
  widening-seal-spine-overlap⊥
    wfΣ α↦★ seal-ok path
    (endpoint-gap-spine gap)
    (endpoint-gap-fresh gap)
    t⊑

-- Remaining overlap obligations. The first occurrence split is now explicit:
-- if the `extᵈ` side would have to create/remove the bound variable, the
-- id-only occurrence lemmas above close the branch. The nested branch where
-- the occurrence is present on both non-forall endpoints is the part that
-- connects to the smaller all/gen and all/inst endpoint experiment.
narrowing-all-gen-overlap-present⊥ :
  ∀ {μ Δ Σ A B s t} →
  StoreDetWf Δ Σ →
  occurs zero A ≡ true →
  occurs zero B ≡ true →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ t ∶ ⇑ᵗ (`∀ A) ⊒ B →
  ⊥
narrowing-all-gen-overlap-present⊥ wfΣ occA occB s⊒ t⊒ =
  narrowing-tag-gap-overlap⊥
    refl
    end-insert
    (narrowing-target-path-id-only refl s⊒ (occurs-true→Occurs occB))
    t⊒

widening-all-inst-overlap-present⊥ :
  ∀ {μ Δ Σ A B s t} →
  StoreDetWf Δ Σ →
  occurs zero A ≡ true →
  occurs zero B ≡ true →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊑ B →
  instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ t ∶ A ⊑ ⇑ᵗ (`∀ B) →
  ⊥
widening-all-inst-overlap-present⊥ wfΣ occA occB s⊑ t⊑ =
  widening-seal-gap-overlap⊥
    (StoreDetWf-inst wfΣ)
    (here refl)
    refl
    end-insert
    (widening-source-path-id-only refl s⊑ (occurs-true→Occurs occA))
    t⊑

narrowing-all-gen-overlap⊥ :
  ∀ {μ Δ Σ A B s t} →
  StoreDetWf Δ Σ →
  occurs zero B ≡ true →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ t ∶ ⇑ᵗ (`∀ A) ⊒ B →
  ⊥
narrowing-all-gen-overlap⊥ {A = A} wfΣ occB s⊒ t⊒
    with occurs zero A | inspect (occurs zero) A
narrowing-all-gen-overlap⊥ {A = A} wfΣ occB s⊒ t⊒
    | true | [ occA ] =
  narrowing-all-gen-overlap-present⊥ wfΣ occA occB s⊒ t⊒
narrowing-all-gen-overlap⊥ {A = A} wfΣ occB s⊒ t⊒
    | false | [ noA ] =
  false≢true
    (trans (sym noA) (narrowing-target-id-only refl s⊒ occB))

widening-all-inst-overlap-det⊥ :
  ∀ {μ Δ Σ A B s t} →
  StoreDetWf Δ Σ →
  occurs zero A ≡ true →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊑ B →
  instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ t ∶ A ⊑ ⇑ᵗ (`∀ B) →
  ⊥
widening-all-inst-overlap-det⊥ {B = B} wfΣ occA s⊑ t⊑
    with occurs zero B | inspect (occurs zero) B
widening-all-inst-overlap-det⊥ {B = B} wfΣ occA s⊑ t⊑
    | true | [ occB ] =
  widening-all-inst-overlap-present⊥ wfΣ occA occB s⊑ t⊑
widening-all-inst-overlap-det⊥ {B = B} wfΣ occA s⊑ t⊑
    | false | [ noB ] =
  false≢true
    (trans (sym noB) (widening-source-id-only refl s⊑ occA))

------------------------------------------------------------------------
-- Mode-indexed narrowing/widening determinacy under StoreDetWf
------------------------------------------------------------------------

mutual
  narrowing-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
    s ≡ t
  narrowing-determinedᵐ-det wfΣ
      (cast-seal hA α∈Σ ok , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-unseal hA α∈Σ ok , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-tag hG gG ok , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-untag hG gG ok , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-inst hB occ c⊢ , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ t⊢ , n-cross ()) u⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-id {A = A ⇒ B} hA ok , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-id {A = `∀ A} hA ok , n-cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-seal hA α∈Σ ok , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-unseal hA α∈Σ ok , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-tag hG gG ok , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-untag hG gG ok , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-inst hB occ c⊢ , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-seq t⊢ u⊢ , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-id {A = A ⇒ B} hA ok , n-cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-id {A = `∀ A} hA ok , n-cross ())
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , n-cross cn-id-var)
      (cast-id hA′ ok′ , n-cross cn-id-var) =
    refl
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , n-cross cn-id-base)
      (cast-id hA′ ok′ , n-cross cn-id-base) =
    refl
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , n-id★)
      (cast-id hA′ ok′ , n-id★) =
    refl
  narrowing-determinedᵐ-det wfΣ
      (cast-id {A = ＇ α} hA id-ok , n-cross cn-id-var)
      (cast-seq t⊢ (cast-seal hB α∈Σ seal-ok) , n-seal tⁿ) =
    ⊥-elim (narrowing-var-to-older⊥ wfΣ (wfOlder wfΣ α∈Σ) (t⊢ , tⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , n-id★)
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tᶜ) =
    ⊥-elim (narrowing-cross-ground-target-star⊥ gG (t⊢ , tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ′ tⁿ′)) =
    cong₂ _↦_
      (widening-determinedᵐ-det wfΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-det wfΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    cong `∀
      (narrowing-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sⁿ)
        (t⊢ , tⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-gen hA occ t⊢ , n-gen tⁿ) =
    ⊥-elim (narrowing-all-gen-overlap⊥ wfΣ occ (s⊢ , sⁿ) (t⊢ , tⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , n-gen sⁿ)
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    ⊥-elim (narrowing-all-gen-overlap⊥ wfΣ occ (t⊢ , tⁿ) (s⊢ , sⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , n-gen sⁿ)
      (cast-gen hA′ occ′ t⊢ , n-gen tⁿ) =
    cong (gen _)
      (narrowing-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sⁿ)
        (t⊢ , tⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , n-untag gH′ tᶜ)
      with narrowing-cross-ground-source-determinedᵐ-det
             wfΣ gG gH (s⊢ , sᶜ) (t⊢ , tᶜ)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , n-untag gH′ tᶜ)
      | refl , eq =
    cong₂ _︔_ refl eq
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-id hA ok , n-id★) =
    ⊥-elim (narrowing-cross-ground-target-star⊥ gG (s⊢ , sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-gen hA occ t⊢ , n-gen tⁿ) =
    ⊥-elim (narrowing-cross-ground-target-all⊥ gG (s⊢ , sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-seq () t⊢ , n-untag gG′ tᶜ)
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , n-gen sⁿ)
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tᶜ) =
    ⊥-elim (narrowing-cross-ground-target-all⊥ gG (t⊢ , tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , n-gen sⁿ)
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-seq t⊢ (cast-seal hA α∈Σ seal-ok) , n-seal tⁿ) =
    ⊥-elim
      (narrowing-cross-ground-target-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok (s⊢ , sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ α-ok) , n-seal sⁿ)
      (cast-seq t⊢ (cast-seal hB β∈Σ β-ok) , n-seal tⁿ)
      rewrite unique wfΣ α∈Σ β∈Σ =
    cong₂ _︔_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (t⊢ , tⁿ))
      refl
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ)
      (cast-id {A = ＇ α} hB id-ok , n-cross cn-id-var) =
    ⊥-elim (narrowing-var-to-older⊥ wfΣ (wfOlder wfΣ α∈Σ) (s⊢ , sⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ)
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok (t⊢ , tᶜ))

  narrowing-cross-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B) × CrossNarrowing s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ B) × CrossNarrowing t →
    s ≡ t
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , cn-id-var)
      (cast-id hA′ ok′ , cn-id-var) =
    refl
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , cn-id-base)
      (cast-id hA′ ok′ , cn-id-base) =
    refl
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ)
      (cast-fun s⊢′ t⊢′ , cn-fun sʷ′ tⁿ′) =
    cong₂ _↦_
      (widening-determinedᵐ-det wfΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-det wfΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-all s⊢ , cn-all sⁿ)
      (cast-all t⊢ , cn-all tⁿ) =
    cong `∀
      (narrowing-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sⁿ)
        (t⊢ , tⁿ))

  narrowing-cross-ground-source-determinedᵐ-det :
    ∀ {μ Δ Σ G H B s t} →
    StoreDetWf Δ Σ →
    Ground G →
    Ground H →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ G =⇒ B) × CrossNarrowing s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ H =⇒ B) × CrossNarrowing t →
    G ≡ H × s ≡ t
  narrowing-cross-ground-source-determinedᵐ-det wfΣ
      (＇ α) (＇ .α)
      (cast-id hA ok , cn-id-var)
      (cast-id hA′ ok′ , cn-id-var) =
    refl , refl
  narrowing-cross-ground-source-determinedᵐ-det wfΣ
      (‵ ι) (‵ .ι)
      (cast-id hA ok , cn-id-base)
      (cast-id hA′ ok′ , cn-id-base) =
    refl , refl
  narrowing-cross-ground-source-determinedᵐ-det wfΣ
      ★⇒★ ★⇒★
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ)
      (cast-fun s⊢′ t⊢′ , cn-fun sʷ′ tⁿ′) =
    refl ,
    cong₂ _↦_
      (widening-determinedᵐ-det wfΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-det wfΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))

  widening-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
    s ≡ t
  widening-determinedᵐ-det wfΣ
      (cast-seal hA α∈Σ ok , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-unseal hA α∈Σ ok , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-tag hG gG ok , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-untag hG gG ok , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-gen hA occ c⊢ , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ t⊢ , w-cross ()) u⊑
  widening-determinedᵐ-det wfΣ
      (cast-id {A = A ⇒ B} hA ok , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-id {A = `∀ A} hA ok , w-cross ()) t⊑
  widening-determinedᵐ-det wfΣ s⊑
      (cast-seal hA α∈Σ ok , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-unseal hA α∈Σ ok , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-tag hG gG ok , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-untag hG gG ok , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-gen hA occ c⊢ , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-seq t⊢ u⊢ , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-id {A = A ⇒ B} hA ok , w-cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-id {A = `∀ A} hA ok , w-cross ())
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , w-cross cw-id-var)
      (cast-id hA′ ok′ , w-cross cw-id-var) =
    refl
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , w-cross cw-id-base)
      (cast-id hA′ ok′ , w-cross cw-id-base) =
    refl
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , w-id★)
      (cast-id hA′ ok′ , w-id★) =
    refl
  widening-determinedᵐ-det wfΣ
      (cast-id {A = ＇ α} hA id-ok , w-cross cw-id-var)
      (cast-seq (cast-unseal hB α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
    ⊥-elim (widening-older-to-var⊥ wfΣ (wfOlder wfΣ α∈Σ) (t⊢ , tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , w-id★)
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tᶜ) =
    ⊥-elim (widening-cross-ground-source-star⊥ gG (t⊢ , tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ′ tʷ′)) =
    cong₂ _↦_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-det wfΣ (t⊢ , tʷ) (t⊢′ , tʷ′))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    cong `∀
      (widening-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-inst hB occ t⊢ , w-inst tʷ) =
    ⊥-elim
      (widening-all-inst-overlap-det⊥ wfΣ occ (s⊢ , sʷ) (t⊢ , tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-seq t⊢ () , w-tag gG′ tᶜ)
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-inst hB′ occ′ t⊢ , w-inst tʷ) =
    cong (inst _)
      (widening-determinedᵐ-det
        (StoreDetWf-inst wfΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    ⊥-elim
      (widening-all-inst-overlap-det⊥ wfΣ occ (t⊢ , tʷ) (s⊢ , sʷ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-seq t⊢ (cast-tag hH gH okH) , w-tag gH′ tᶜ)
      with widening-cross-ground-target-determinedᵐ-det
             wfΣ gG gH (s⊢ , sᶜ) (t⊢ , tᶜ)
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-seq t⊢ (cast-tag hH gH okH) , w-tag gH′ tᶜ)
      | refl , eq =
    cong₂ _︔_ eq refl
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-id hA ok , w-id★) =
    ⊥-elim (widening-cross-ground-source-star⊥ gG (s⊢ , sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-seq (cast-unseal hA α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
    ⊥-elim
      (widening-cross-ground-source-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok (s⊢ , sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-inst hB occ t⊢ , w-inst tʷ) =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (s⊢ , sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ α-ok) s⊢ , w-unseal sʷ)
      (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ , w-unseal tʷ)
      rewrite unique wfΣ α∈Σ β∈Σ =
    cong₂ _︔_ refl
      (widening-determinedᵐ-det wfΣ (s⊢ , sʷ) (t⊢ , tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , w-unseal sʷ)
      (cast-id {A = ＇ α} hB id-ok , w-cross cw-id-var) =
    ⊥-elim (widening-older-to-var⊥ wfΣ (wfOlder wfΣ α∈Σ) (s⊢ , sʷ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , w-unseal sʷ)
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tᶜ) =
    ⊥-elim
      (widening-cross-ground-source-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok (t⊢ , tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tᶜ) =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (t⊢ , tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-seq () t⊢ , w-unseal tʷ)

  widening-cross-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B) × CrossWidening s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ B) × CrossWidening t →
    s ≡ t
  widening-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , cw-id-var)
      (cast-id hA′ ok′ , cw-id-var) =
    refl
  widening-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , cw-id-base)
      (cast-id hA′ ok′ , cw-id-base) =
    refl
  widening-cross-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ)
      (cast-fun s⊢′ t⊢′ , cw-fun sⁿ′ tʷ′) =
    cong₂ _↦_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-det wfΣ (t⊢ , tʷ) (t⊢′ , tʷ′))
  widening-cross-determinedᵐ-det wfΣ
      (cast-all s⊢ , cw-all sʷ)
      (cast-all t⊢ , cw-all tʷ) =
    cong `∀
      (widening-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))

  widening-cross-ground-target-determinedᵐ-det :
    ∀ {μ Δ Σ A G H s t} →
    StoreDetWf Δ Σ →
    Ground G →
    Ground H →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ G) × CrossWidening s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ H) × CrossWidening t →
    G ≡ H × s ≡ t
  widening-cross-ground-target-determinedᵐ-det wfΣ
      (＇ α) (＇ .α)
      (cast-id hA ok , cw-id-var)
      (cast-id hA′ ok′ , cw-id-var) =
    refl , refl
  widening-cross-ground-target-determinedᵐ-det wfΣ
      (‵ ι) (‵ .ι)
      (cast-id hA ok , cw-id-base)
      (cast-id hA′ ok′ , cw-id-base) =
    refl , refl
  widening-cross-ground-target-determinedᵐ-det wfΣ
      ★⇒★ ★⇒★
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ)
      (cast-fun s⊢′ t⊢′ , cw-fun sⁿ′ tʷ′) =
    refl ,
    cong₂ _↦_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-det wfΣ (t⊢ , tʷ) (t⊢′ , tʷ′))

narrowing-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
narrowing-determinedᵐ wfΣ =
  narrowing-determinedᵐ-det (StoreWf⇒det wfΣ)

widening-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
widening-determinedᵐ wfΣ =
  widening-determinedᵐ-det (StoreWf⇒det wfΣ)
mutual
  narrow-src-wf :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    WfTy Δ A
  narrow-src-wf (nrw-id hA) = hA
  narrow-src-wf (nrw-fun s t) =
    wf⇒ (widen-tgt-wf s) (narrow-src-wf t)
  narrow-src-wf (nrw-all s) = wf∀ (narrow-src-wf s)
  narrow-src-wf (nrw-gen hA s) = hA
  narrow-src-wf (nrw-untag hG gG s) = wf★
  narrow-src-wf (nrw-untagˢ hA α∈Σ s) = wf★
  narrow-src-wf (nrw-seal hA′ α∈Σ s) = narrow-src-wf s

  widen-tgt-wf :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    WfTy Δ B
  widen-tgt-wf (wid-id hA) = hA
  widen-tgt-wf (wid-fun s t) =
    wf⇒ (narrow-src-wf s) (widen-tgt-wf t)
  widen-tgt-wf (wid-all s) = wf∀ (widen-tgt-wf s)
  widen-tgt-wf (wid-inst hB s) = hB
  widen-tgt-wf (wid-tag hG gG s) = wf★
  widen-tgt-wf (wid-tagˢ hA α∈Σ s) = wf★
  widen-tgt-wf (wid-tagˢ-comp hA α∈Σ s t) = wf★
  widen-tgt-wf (wid-unseal hA′ α∈Σ s) = widen-tgt-wf s

mutual
  narrow-weaken :
    ∀ {Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Δ′ ∣ Σ′ ⊢ c ∶ A ⊒ B
  narrow-weaken Δ≤Δ′ incl (nrw-id {aA = aA} hA) =
    nrw-id {aA = aA} (WfTy-weakenᵗ hA Δ≤Δ′)
  narrow-weaken Δ≤Δ′ incl (nrw-fun s t) =
    nrw-fun (widen-weaken Δ≤Δ′ incl s) (narrow-weaken Δ≤Δ′ incl t)
  narrow-weaken Δ≤Δ′ incl (nrw-all s) =
    nrw-all
      (narrow-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  narrow-weaken Δ≤Δ′ incl (nrw-gen hA s) =
    nrw-gen
      (WfTy-weakenᵗ hA Δ≤Δ′)
      (narrow-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  narrow-weaken Δ≤Δ′ incl (nrw-untag hG gG s) =
    nrw-untag (WfTy-weakenᵗ hG Δ≤Δ′) gG
      (narrow-weaken Δ≤Δ′ incl s)
  narrow-weaken Δ≤Δ′ incl (nrw-untagˢ hA α∈Σ s) =
    nrw-untagˢ (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
      (narrow-weaken Δ≤Δ′ incl s)
  narrow-weaken Δ≤Δ′ incl (nrw-seal hA′ α∈Σ s) =
    nrw-seal (WfTy-weakenᵗ hA′ Δ≤Δ′) (incl α∈Σ)
      (narrow-weaken Δ≤Δ′ incl s)

  widen-weaken :
    ∀ {Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Δ′ ∣ Σ′ ⊢ c ∶ A ⊑ B
  widen-weaken Δ≤Δ′ incl (wid-id {aA = aA} hA) =
    wid-id {aA = aA} (WfTy-weakenᵗ hA Δ≤Δ′)
  widen-weaken Δ≤Δ′ incl (wid-fun s t) =
    wid-fun (narrow-weaken Δ≤Δ′ incl s) (widen-weaken Δ≤Δ′ incl t)
  widen-weaken Δ≤Δ′ incl (wid-all s) =
    wid-all
      (widen-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  widen-weaken Δ≤Δ′ incl (wid-inst hB s) =
    wid-inst
      (WfTy-weakenᵗ hB Δ≤Δ′)
      (widen-weaken
        (s≤s Δ≤Δ′)
        (StoreIncl-cons (renameStoreᵗ-incl suc incl))
        s)
  widen-weaken Δ≤Δ′ incl (wid-tag hG gG s) =
    wid-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG
      (widen-weaken Δ≤Δ′ incl s)
  widen-weaken Δ≤Δ′ incl (wid-tagˢ hA α∈Σ s) =
    wid-tagˢ (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)
  widen-weaken Δ≤Δ′ incl (wid-tagˢ-comp hA α∈Σ s t) =
    wid-tagˢ-comp (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)
      (widen-weaken Δ≤Δ′ incl t)
  widen-weaken Δ≤Δ′ incl (wid-unseal hA′ α∈Σ s) =
    wid-unseal (WfTy-weakenᵗ hA′ Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)

mutual
  narrow-renameᵗ :
    ∀ {Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
  narrow-renameᵗ hρ (nrw-id {aA = aA} hA) =
    nrw-id {aA = renameᵗ-atom _ aA}
      (renameᵗ-preserves-WfTy hA hρ)
  narrow-renameᵗ hρ (nrw-fun s t) =
    nrw-fun (widen-renameᵗ hρ s) (narrow-renameᵗ hρ t)
  narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (nrw-all s) =
    nrw-all
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (narrow-renameᵗ (TyRenameWf-ext hρ) s))
  narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {A = A} {ρ = ρ}
      hρ (nrw-gen hA s) =
    nrw-gen
      (renameᵗ-preserves-WfTy hA hρ)
      (subst
        (λ T → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ∶ T ⊒ _)
        (renameᵗ-ext-suc-comm ρ A)
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (narrow-renameᵗ (TyRenameWf-ext hρ) s)))
  narrow-renameᵗ hρ (nrw-untag hG gG s) =
    nrw-untag
      (renameᵗ-preserves-WfTy hG hρ)
      (renameᵗ-ground _ gG)
      (narrow-renameᵗ hρ s)
  narrow-renameᵗ hρ (nrw-untagˢ hA α∈Σ s) =
    nrw-untagˢ
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (narrow-renameᵗ hρ s)
  narrow-renameᵗ hρ (nrw-seal hA′ α∈Σ s) =
    nrw-seal
      (renameᵗ-preserves-WfTy hA′ hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (narrow-renameᵗ hρ s)

  widen-renameᵗ :
    ∀ {Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊑ renameᵗ ρ B
  widen-renameᵗ hρ (wid-id {aA = aA} hA) =
    wid-id {aA = renameᵗ-atom _ aA}
      (renameᵗ-preserves-WfTy hA hρ)
  widen-renameᵗ hρ (wid-fun s t) =
    wid-fun (narrow-renameᵗ hρ s) (widen-renameᵗ hρ t)
  widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (wid-all s) =
    wid-all
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (widen-renameᵗ (TyRenameWf-ext hρ) s))
  widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {B = B} {ρ = ρ}
      hρ (wid-inst hB s) =
    wid-inst
      (renameᵗ-preserves-WfTy hB hρ)
      (subst
        (λ T → suc Δ′
          ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ T)
        (renameᵗ-ext-suc-comm ρ B)
        (subst
          (λ Σ′ → suc Δ′ ∣ (zero , ★) ∷ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (widen-renameᵗ (TyRenameWf-ext hρ) s)))
  widen-renameᵗ hρ (wid-tag hG gG s) =
    wid-tag
      (renameᵗ-preserves-WfTy hG hρ)
      (renameᵗ-ground _ gG)
      (widen-renameᵗ hρ s)
  widen-renameᵗ hρ (wid-tagˢ hA α∈Σ s) =
    wid-tagˢ
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)
  widen-renameᵗ hρ (wid-tagˢ-comp hA α∈Σ s t) =
    wid-tagˢ-comp
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)
      (widen-renameᵗ hρ t)
  widen-renameᵗ hρ (wid-unseal hA′ α∈Σ s) =
    wid-unseal
      (renameᵗ-preserves-WfTy hA′ hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)

narrow-⇑ᵗ :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ = narrow-renameᵗ TyRenameWf-suc

widen-⇑ᵗ :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ = widen-renameᵗ TyRenameWf-suc

widen-⇑ᵗ-cons :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ-cons p =
  widen-weaken ≤-refl StoreIncl-drop (widen-⇑ᵗ p)

------------------------------------------------------------------------
-- Composition (aka. transitivity)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual 
  _⨟ⁿ_ : ∀{Δ Σ A B C}{s t : Coercion} → (Δ ∣ Σ ⊢ s ∶ A ⊒ B) → (Δ ∣ Σ ⊢ t ∶ B ⊒ C)
        → ∃[ u ] (Δ ∣ Σ ⊢ u ∶ A ⊒ C)
  s ⨟ⁿ nrw-id wfB = _ , s
  nrw-fun s t ⨟ⁿ nrw-fun s′ t′
      with s′ ⨟ʷ s | t ⨟ⁿ t′
  ... | _ , s″ | _ , t″ = _ , nrw-fun s″ t″
  nrw-untag wfG gG s ⨟ⁿ q@(nrw-fun s′ t′)
      with s ⨟ⁿ q
  ... | _ , s″ = _ , nrw-untag wfG gG s″
  nrw-all s ⨟ⁿ nrw-all t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-all s′
  nrw-gen wfA s ⨟ⁿ nrw-all t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-gen wfA s′
  nrw-untag wfG gG s ⨟ⁿ q@(nrw-all t)
      with s ⨟ⁿ q
  ... | _ , s′ = _ , nrw-untag wfG gG s′
  s ⨟ⁿ nrw-gen wfB t
      with narrow-⇑ᵗ s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-gen (narrow-src-wf s) s′
  nrw-id wf★ ⨟ⁿ nrw-untag wfG gG t =
    _ , nrw-untag wfG gG t
  nrw-untag wfG′ gG′ s
      ⨟ⁿ q@(nrw-untag wfG gG t)
      with s ⨟ⁿ q
  ... | _ , s′ = _ , nrw-untag wfG′ gG′ s′
  s ⨟ⁿ nrw-untagˢ wfA′ α∈Σ t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-seal wfA′ α∈Σ s′
  s ⨟ⁿ nrw-seal wfA′ ∈Σ t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-seal wfA′ ∈Σ s′

  _⨟ʷ_ : ∀{Δ Σ A B C}{s t : Coercion} → (Δ ∣ Σ ⊢ s ∶ A ⊑ B) → (Δ ∣ Σ ⊢ t ∶ B ⊑ C)
        → ∃[ u ] (Δ ∣ Σ ⊢ u ∶ A ⊑ C)
  s ⨟ʷ wid-id wfB = _ , s
  wid-fun s t ⨟ʷ wid-fun s′ t′
      with s′ ⨟ⁿ s | t ⨟ʷ t′
  ... | _ , s″ | _ , t″ = _ , wid-fun s″ t″
  wid-inst wfB s ⨟ʷ q@(wid-fun s′ t′)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s″ = _ , wid-inst (widen-tgt-wf q) s″
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-fun s′ t′)
      with s ⨟ʷ q
  ... | _ , s″ = _ , wid-unseal wfA′ α∈Σ s″
  wid-all s ⨟ʷ wid-all t
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-all s′
  wid-inst wfB s ⨟ʷ q@(wid-all t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s″ = _ , wid-inst (widen-tgt-wf q) s″
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-all t)
      with s ⨟ʷ q
  ... | _ , s″ = _ , wid-unseal wfA′ α∈Σ s″
  wid-all s ⨟ʷ wid-inst wfC t
      with widen-weaken ≤-refl StoreIncl-drop s ⨟ʷ t
  ... | _ , s′ = _ , wid-inst wfC s′
  wid-inst wfB s ⨟ʷ q@(wid-inst wfC t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s′ = _ , wid-inst wfC s′
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-inst wfC t)
      with s ⨟ʷ q
  ... | _ , s′ = _ , wid-unseal wfA′ α∈Σ s′
  s ⨟ʷ wid-tag wfG gG t
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-tag wfG gG s′
  s ⨟ʷ wid-tagˢ wfA′ α∈Σ t =
    _ , wid-tagˢ-comp wfA′ α∈Σ s t
  s ⨟ʷ wid-tagˢ-comp wfA′ α∈Σ t u
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-tagˢ-comp wfA′ α∈Σ s′ u
  wid-id wfA ⨟ʷ wid-unseal wfA′ α∈Σ t =
    _ , wid-unseal wfA′ α∈Σ t
  wid-inst wfB s ⨟ʷ q@(wid-unseal wfA′ α∈Σ t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s′ = _ , wid-inst (widen-tgt-wf q) s′
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-unseal wfA″ β∈Σ t)
      with s ⨟ʷ q
  ... | _ , s′ = _ , wid-unseal wfA′ α∈Σ s′

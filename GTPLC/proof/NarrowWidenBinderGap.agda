module proof.NarrowWidenBinderGap where

-- File Charter:
--   * Rules out the structural-universal/generalization and
--     structural-universal/instantiation overlaps used by determinism.
--   * Tracks a selected type-variable occurrence through narrowing and
--     widening and compares its endpoints across a binder insertion.

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden
open import proof.TyStore using
  (∈-renameTyStoreᵗ; rename-member-inv; StoreWf-⟰ᵗ;
   StoreWf-bind; unique)
open import proof.TypeInTypeSubst using
  (renameᵗ-compose; renameᵗ-id)

------------------------------------------------------------------------
-- Occurrence paths selected by an id-only variable
------------------------------------------------------------------------

mutual

  data NarrowPath (X : TyVar) : Ty → Ty → Set where

    np-var : NarrowPath X (＇ X) (＇ X)

    np-fun₁ : ∀ {A A′ B B′}
      → WidenPath X A′ A
      → NarrowPath X (A ⇒ B) (A′ ⇒ B′)

    np-fun₂ : ∀ {A A′ B B′}
      → NarrowPath X B B′
      → NarrowPath X (A ⇒ B) (A′ ⇒ B′)

    np-all : ∀ {A B}
      → NarrowPath (suc X) A B
      → NarrowPath X (`∀ A) (`∀ B)

    np-gen : ∀ {A B}
      → NarrowPath (suc X) (⇑ᵗ A) B
      → NarrowPath X A (`∀ B)

  data WidenPath (X : TyVar) : Ty → Ty → Set where

    wp-var : WidenPath X (＇ X) (＇ X)

    wp-fun₁ : ∀ {A A′ B B′}
      → NarrowPath X A′ A
      → WidenPath X (A ⇒ B) (A′ ⇒ B′)

    wp-fun₂ : ∀ {A A′ B B′}
      → WidenPath X B B′
      → WidenPath X (A ⇒ B) (A′ ⇒ B′)

    wp-all : ∀ {A B}
      → WidenPath (suc X) A B
      → WidenPath X (`∀ A) (`∀ B)

    wp-inst : ∀ {A B}
      → WidenPath (suc X) A (⇑ᵗ B)
      → WidenPath X (`∀ A) B

id-tag-exclusive : ∀ {m : Mode}
  → m ≡ id-only
  → tagModeAllowed m ≡ true
  → ⊥
id-tag-exclusive {m} X-id allowed with m
id-tag-exclusive X-id () | id-only
id-tag-exclusive () allowed | tag-or-id
id-tag-exclusive () allowed | seal-or-id

id-seal-exclusive : ∀ {m : Mode}
  → m ≡ id-only
  → sealModeAllowed m ≡ true
  → ⊥
id-seal-exclusive {m} X-id allowed with m
id-seal-exclusive X-id () | id-only
id-seal-exclusive () allowed | tag-or-id
id-seal-exclusive () allowed | seal-or-id

tagged-member-id-only⊥ : ∀ {μ X G A}
  → μ X ≡ id-only
  → tagAllowed μ G ≡ true
  → G ꞉ A
  → X ∈ᵗ A
  → ⊥
tagged-member-id-only⊥ {X = X} X-id allowed (tag-var .X) var-∈ =
  id-tag-exclusive X-id allowed
tagged-member-id-only⊥ X-id allowed (tag-base ι) ()
tagged-member-id-only⊥ X-id allowed tag-fun (∈-fun-left ())
tagged-member-id-only⊥ X-id allowed tag-fun (∈-fun-right ())

shift-member-inv : ∀ {X A}
  → suc X ∈ᵗ ⇑ᵗ A
  → X ∈ᵗ A
shift-member-inv {X = X} {A = A} occ with rename-member-inv suc occ
shift-member-inv {X = X} {A = A} occ | Y , eq , Y∈A =
  subst (_∈ᵗ A) (sym (suc-injective eq)) Y∈A

mutual

  narrowing-target-member-id-only : ∀ {μ Δ Σ c A B X}
    → μ X ≡ id-only
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → X ∈ᵗ B
    → X ∈ᵗ A
  narrowing-target-member-id-only X-id (idᵃ (＇ X) hX) var-∈ = var-∈
  narrowing-target-member-id-only X-id (idᵃ (‵ ι) hA) ()
  narrowing-target-member-id-only X-id (idᵃ ★ hA) ()
  narrowing-target-member-id-only X-id (p ↦ q) (∈-fun-left occ) =
    ∈-fun-left (widening-source-member-id-only X-id p occ)
  narrowing-target-member-id-only X-id (p ↦ q) (∈-fun-right occ) =
    ∈-fun-right (narrowing-target-member-id-only X-id q occ)
  narrowing-target-member-id-only {X = X} X-id (∀ⁿ p) (∈-all occ) =
    ∈-all
      (narrowing-target-member-id-only {X = suc X} X-id p occ)
  narrowing-target-member-id-only X-id
      (untag G hG allowed G꞉B) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉B occ)
  narrowing-target-member-id-only X-id
      (untag-seq G hG allowed G꞉A p nonvarB A≢B) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉A
      (narrowing-target-member-id-only X-id p occ))
  narrowing-target-member-id-only X-id
      (seal X<Δ hA X,A∈Σ allowed) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  narrowing-target-member-id-only X-id
      (seal-seq p X<Δ X,A∈Σ allowed A≢B) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  narrowing-target-member-id-only {X = X} X-id
      (gen nonvarA zero∈A hB p B≢★) (∈-all occ) =
    shift-member-inv
      (narrowing-target-member-id-only {X = suc X} X-id p occ)

  widening-source-member-id-only : ∀ {μ Δ Σ c A B X}
    → μ X ≡ id-only
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → X ∈ᵗ A
    → X ∈ᵗ B
  widening-source-member-id-only X-id (idᵃ (＇ X) hX) var-∈ = var-∈
  widening-source-member-id-only X-id (idᵃ (‵ ι) hA) ()
  widening-source-member-id-only X-id (idᵃ ★ hA) ()
  widening-source-member-id-only X-id (p ↦ q) (∈-fun-left occ) =
    ∈-fun-left (narrowing-target-member-id-only X-id p occ)
  widening-source-member-id-only X-id (p ↦ q) (∈-fun-right occ) =
    ∈-fun-right (widening-source-member-id-only X-id q occ)
  widening-source-member-id-only {X = X} X-id (∀ʷ p) (∈-all occ) =
    ∈-all (widening-source-member-id-only {X = suc X} X-id p occ)
  widening-source-member-id-only X-id (tag G hG allowed G꞉A) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉A occ)
  widening-source-member-id-only X-id
      (tag-seq G p hG allowed G꞉B nonvarA A≢B) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉B
      (widening-source-member-id-only X-id p occ))
  widening-source-member-id-only X-id
      (unseal X<Δ hA X,A∈Σ allowed) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  widening-source-member-id-only X-id
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  widening-source-member-id-only {X = X} X-id
      (inst nonvarA zero∈A hB p B≢★) (∈-all occ) =
    shift-member-inv
      (widening-source-member-id-only {X = suc X} X-id p occ)

mutual

  narrowing-target-path-id-only : ∀ {μ Δ Σ c A B X}
    → μ X ≡ id-only
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → X ∈ᵗ B
    → NarrowPath X A B
  narrowing-target-path-id-only X-id (idᵃ (＇ X) hX) var-∈ = np-var
  narrowing-target-path-id-only X-id (idᵃ (‵ ι) hA) ()
  narrowing-target-path-id-only X-id (idᵃ ★ hA) ()
  narrowing-target-path-id-only X-id (p ↦ q) (∈-fun-left occ) =
    np-fun₁ (widening-source-path-id-only X-id p occ)
  narrowing-target-path-id-only X-id (p ↦ q) (∈-fun-right occ) =
    np-fun₂ (narrowing-target-path-id-only X-id q occ)
  narrowing-target-path-id-only {X = X} X-id (∀ⁿ p) (∈-all occ) =
    np-all (narrowing-target-path-id-only {X = suc X} X-id p occ)
  narrowing-target-path-id-only X-id
      (untag G hG allowed G꞉B) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉B occ)
  narrowing-target-path-id-only X-id
      (untag-seq G hG allowed G꞉A p nonvarB A≢B) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉A
      (narrowing-target-member-id-only X-id p occ))
  narrowing-target-path-id-only X-id
      (seal X<Δ hA X,A∈Σ allowed) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  narrowing-target-path-id-only X-id
      (seal-seq p X<Δ X,A∈Σ allowed A≢B) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  narrowing-target-path-id-only {X = X} X-id
      (gen nonvarA zero∈A hB p B≢★) (∈-all occ) =
    np-gen (narrowing-target-path-id-only {X = suc X} X-id p occ)

  widening-source-path-id-only : ∀ {μ Δ Σ c A B X}
    → μ X ≡ id-only
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → X ∈ᵗ A
    → WidenPath X A B
  widening-source-path-id-only X-id (idᵃ (＇ X) hX) var-∈ = wp-var
  widening-source-path-id-only X-id (idᵃ (‵ ι) hA) ()
  widening-source-path-id-only X-id (idᵃ ★ hA) ()
  widening-source-path-id-only X-id (p ↦ q) (∈-fun-left occ) =
    wp-fun₁ (narrowing-target-path-id-only X-id p occ)
  widening-source-path-id-only X-id (p ↦ q) (∈-fun-right occ) =
    wp-fun₂ (widening-source-path-id-only X-id q occ)
  widening-source-path-id-only {X = X} X-id (∀ʷ p) (∈-all occ) =
    wp-all (widening-source-path-id-only {X = suc X} X-id p occ)
  widening-source-path-id-only X-id (tag G hG allowed G꞉A) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉A occ)
  widening-source-path-id-only X-id
      (tag-seq G p hG allowed G꞉B nonvarA A≢B) occ =
    ⊥-elim (tagged-member-id-only⊥ X-id allowed G꞉B
      (widening-source-member-id-only X-id p occ))
  widening-source-path-id-only X-id
      (unseal X<Δ hA X,A∈Σ allowed) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  widening-source-path-id-only X-id
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B) var-∈ =
    ⊥-elim (id-seal-exclusive X-id allowed)
  widening-source-path-id-only {X = X} X-id
      (inst nonvarA zero∈A hB p B≢★) (∈-all occ) =
    wp-inst (widening-source-path-id-only {X = suc X} X-id p occ)

------------------------------------------------------------------------
-- Endpoint spines and freshness
------------------------------------------------------------------------

Fresh : TyVar → Ty → Set
Fresh X A = X ∈ᵗ A → ⊥

data EndpointSpine : Ty → Ty → Set where

  spine-renamed : ∀ {L R T ρ τ}
    → L ≡ renameᵗ ρ T
    → R ≡ renameᵗ τ T
    → EndpointSpine L R

  spine-left-all : ∀ {L R}
    → EndpointSpine L R
    → EndpointSpine (`∀ L) R

  spine-right-all : ∀ {L R}
    → EndpointSpine L R
    → EndpointSpine L (`∀ R)

spine-map-left : ∀ ρ {L R}
  → EndpointSpine L R
  → EndpointSpine (renameᵗ ρ L) R
spine-map-left ρ (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = λ X → ρ (σ X)} {τ = τ}
    (renameᵗ-compose σ ρ T) refl
spine-map-left ρ (spine-left-all sp) =
  spine-left-all (spine-map-left (extᵗ ρ) sp)
spine-map-left ρ (spine-right-all sp) =
  spine-right-all (spine-map-left ρ sp)

spine-map-right : ∀ ρ {L R}
  → EndpointSpine L R
  → EndpointSpine L (renameᵗ ρ R)
spine-map-right ρ (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = σ} {τ = λ X → ρ (τ X)}
    refl (renameᵗ-compose τ ρ T)
spine-map-right ρ (spine-left-all sp) =
  spine-left-all (spine-map-right ρ sp)
spine-map-right ρ (spine-right-all sp) =
  spine-right-all (spine-map-right (extᵗ ρ) sp)

spine-peel-right : ∀ ρ {L R}
  → EndpointSpine L (`∀ R)
  → EndpointSpine (renameᵗ ρ L) R
spine-peel-right ρ (spine-renamed {T = ＇ X} eqL ())
spine-peel-right ρ (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right ρ (spine-renamed {T = ★} eqL ())
spine-peel-right ρ (spine-renamed {T = A ⇒ B} eqL ())
spine-peel-right ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-left-all
    (spine-renamed {T = T}
      {ρ = λ X → extᵗ ρ (extᵗ σ X)} {τ = extᵗ τ}
      (renameᵗ-compose (extᵗ σ) (extᵗ ρ) T) refl)
spine-peel-right ρ (spine-left-all sp) =
  spine-left-all (spine-peel-right (extᵗ ρ) sp)
spine-peel-right ρ (spine-right-all sp) = spine-map-left ρ sp

spine-peel-left : ∀ ρ {L R}
  → EndpointSpine (`∀ L) R
  → EndpointSpine L (renameᵗ ρ R)
spine-peel-left ρ (spine-renamed {T = ＇ X} () eqR)
spine-peel-left ρ (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left ρ (spine-renamed {T = ★} () eqR)
spine-peel-left ρ (spine-renamed {T = A ⇒ B} () eqR)
spine-peel-left ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-right-all
    (spine-renamed {T = T} {ρ = extᵗ σ}
      {τ = λ X → extᵗ ρ (extᵗ τ X)} refl
      (renameᵗ-compose (extᵗ τ) (extᵗ ρ) T))
spine-peel-left ρ (spine-left-all sp) = spine-map-right ρ sp
spine-peel-left ρ (spine-right-all sp) =
  spine-right-all (spine-peel-left (extᵗ ρ) sp)

spine-peel-right-id : ∀ {L R}
  → EndpointSpine L (`∀ R)
  → EndpointSpine L R
spine-peel-right-id (spine-renamed {T = ＇ X} eqL ())
spine-peel-right-id (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right-id (spine-renamed {T = ★} eqL ())
spine-peel-right-id (spine-renamed {T = A ⇒ B} eqL ())
spine-peel-right-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-left-all
    (spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ} refl refl)
spine-peel-right-id (spine-left-all sp) =
  spine-left-all (spine-peel-right-id sp)
spine-peel-right-id (spine-right-all sp) = sp

spine-peel-left-id : ∀ {L R}
  → EndpointSpine (`∀ L) R
  → EndpointSpine L R
spine-peel-left-id (spine-renamed {T = ＇ X} () eqR)
spine-peel-left-id (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left-id (spine-renamed {T = ★} () eqR)
spine-peel-left-id (spine-renamed {T = A ⇒ B} () eqR)
spine-peel-left-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-right-all
    (spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ} refl refl)
spine-peel-left-id (spine-left-all sp) = sp
spine-peel-left-id (spine-right-all sp) =
  spine-right-all (spine-peel-left-id sp)

spine-strip-both : ∀ {L R}
  → EndpointSpine (`∀ L) (`∀ R)
  → EndpointSpine L R
spine-strip-both (spine-renamed {T = ＇ X} () eqR)
spine-strip-both (spine-renamed {T = ‵ ι} () eqR)
spine-strip-both (spine-renamed {T = ★} () eqR)
spine-strip-both (spine-renamed {T = A ⇒ B} () eqR)
spine-strip-both
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ} refl refl
spine-strip-both (spine-left-all sp) = spine-peel-right-id sp
spine-strip-both (spine-right-all sp) = spine-peel-left-id sp

fresh-fun-left : ∀ {X A B}
  → Fresh X (A ⇒ B)
  → Fresh X A
fresh-fun-left fresh occ = fresh (∈-fun-left occ)

fresh-fun-right : ∀ {X A B}
  → Fresh X (A ⇒ B)
  → Fresh X B
fresh-fun-right fresh occ = fresh (∈-fun-right occ)

fresh-shift : ∀ {X A}
  → Fresh X A
  → Fresh (suc X) (⇑ᵗ A)
fresh-shift fresh occ = fresh (shift-member-inv occ)

------------------------------------------------------------------------
-- A selected path cannot be related across an inserted binder
------------------------------------------------------------------------

tag-seal-exclusive : ∀ {m : Mode}
  → m ≡ tag-or-id
  → sealModeAllowed m ≡ true
  → ⊥
tag-seal-exclusive {m} tag-ok seal-ok with m
tag-seal-exclusive () seal-ok | id-only
tag-seal-exclusive tag-ok () | tag-or-id
tag-seal-exclusive () seal-ok | seal-or-id

narrow-path-star-spine⊥ : ∀ {X A B}
  → NarrowPath X A B
  → EndpointSpine A ★
  → ⊥
narrow-path-star-spine⊥ np-var
    (spine-renamed {T = ＇ Y} refl ())
narrow-path-star-spine⊥ (np-fun₁ p)
    (spine-renamed {T = A ⇒ B} refl ())
narrow-path-star-spine⊥ (np-fun₂ p)
    (spine-renamed {T = A ⇒ B} refl ())
narrow-path-star-spine⊥ (np-all p) (spine-left-all sp) =
  narrow-path-star-spine⊥ p sp
narrow-path-star-spine⊥ (np-all p)
    (spine-renamed {T = `∀ T} refl ())
narrow-path-star-spine⊥ (np-gen p) sp =
  narrow-path-star-spine⊥ p (spine-map-left suc sp)

widen-path-star-spine⊥ : ∀ {X A B}
  → WidenPath X A B
  → EndpointSpine B ★
  → ⊥
widen-path-star-spine⊥ wp-var
    (spine-renamed {T = ＇ Y} refl ())
widen-path-star-spine⊥ (wp-fun₁ p)
    (spine-renamed {T = A ⇒ B} refl ())
widen-path-star-spine⊥ (wp-fun₂ p)
    (spine-renamed {T = A ⇒ B} refl ())
widen-path-star-spine⊥ (wp-all p) (spine-left-all sp) =
  widen-path-star-spine⊥ p sp
widen-path-star-spine⊥ (wp-all p)
    (spine-renamed {T = `∀ T} refl ())
widen-path-star-spine⊥ (wp-inst p) sp =
  widen-path-star-spine⊥ p (spine-map-left suc sp)

narrowing-var-to-var-tag⊥ : ∀ {μ Δ Σ X Y c}
  → μ X ≡ tag-or-id
  → Y ≢ X
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ Y ⊒ ＇ X
  → ⊥
narrowing-var-to-var-tag⊥ tag-ok Y≢X (idᵃ (＇ X) hX) =
  Y≢X refl
narrowing-var-to-var-tag⊥ tag-ok Y≢X
    (seal X<Δ hA X,A∈Σ allowed) =
  tag-seal-exclusive tag-ok allowed
narrowing-var-to-var-tag⊥ tag-ok Y≢X
    (seal-seq p X<Δ X,A∈Σ allowed A≢B) =
  tag-seal-exclusive tag-ok allowed

narrowing-all-to-var-tag⊥ : ∀ {μ Δ Σ X A c}
  → μ X ≡ tag-or-id
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ (`∀ A) ⊒ ＇ X
  → ⊥
narrowing-all-to-var-tag⊥ tag-ok
    (seal X<Δ hA X,A∈Σ allowed) =
  tag-seal-exclusive tag-ok allowed
narrowing-all-to-var-tag⊥ tag-ok
    (seal-seq p X<Δ X,A∈Σ allowed A≢B) =
  tag-seal-exclusive tag-ok allowed

widening-var-to-var-tag⊥ : ∀ {μ Δ Σ X Y c}
  → μ X ≡ tag-or-id
  → Y ≢ X
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ ＇ Y
  → ⊥
widening-var-to-var-tag⊥ tag-ok Y≢X (idᵃ (＇ X) hX) =
  Y≢X refl
widening-var-to-var-tag⊥ tag-ok Y≢X
    (unseal X<Δ hA X,A∈Σ allowed) =
  tag-seal-exclusive tag-ok allowed
widening-var-to-var-tag⊥ tag-ok Y≢X
    (unseal-seq X<Δ X,A∈Σ allowed p A≢B) =
  tag-seal-exclusive tag-ok allowed

widening-var-to-all-tag⊥ : ∀ {μ Δ Σ X A c}
  → μ X ≡ tag-or-id
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ (`∀ A)
  → ⊥
widening-var-to-all-tag⊥ tag-ok
    (unseal X<Δ hA X,A∈Σ allowed) =
  tag-seal-exclusive tag-ok allowed
widening-var-to-all-tag⊥ tag-ok
    (unseal-seq X<Δ X,A∈Σ allowed p A≢B) =
  tag-seal-exclusive tag-ok allowed

fresh-variable-neq : ∀ {X Y}
  → Fresh X (＇ Y)
  → Y ≢ X
fresh-variable-neq fresh refl = fresh var-∈

narrowing-tag-var-spine⊥ : ∀ {μ Δ Σ X C c}
  → μ X ≡ tag-or-id
  → EndpointSpine (＇ X) C
  → Fresh X C
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ C ⊒ ＇ X
  → ⊥
narrowing-tag-var-spine⊥ tag-ok
    (spine-renamed {T = ＇ Y} refl refl) fresh p =
  narrowing-var-to-var-tag⊥ tag-ok (fresh-variable-neq fresh) p
narrowing-tag-var-spine⊥ tag-ok (spine-right-all sp) fresh p =
  narrowing-all-to-var-tag⊥ tag-ok p

widening-tag-var-spine⊥ : ∀ {μ Δ Σ X C c}
  → μ X ≡ tag-or-id
  → EndpointSpine (＇ X) C
  → Fresh X C
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ C
  → ⊥
widening-tag-var-spine⊥ tag-ok
    (spine-renamed {T = ＇ Y} refl refl) fresh p =
  widening-var-to-var-tag⊥ tag-ok (fresh-variable-neq fresh) p
widening-tag-var-spine⊥ tag-ok (spine-right-all sp) fresh p =
  widening-var-to-all-tag⊥ tag-ok p

mutual

  narrowing-tag-spine-overlap⊥ : ∀ {μ Δ Σ A B C c X}
    → μ X ≡ tag-or-id
    → NarrowPath X A B
    → EndpointSpine A C
    → Fresh X C
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ C ⊒ B
    → ⊥
  narrowing-tag-spine-overlap⊥ tag-ok np-var sp fresh p =
    narrowing-tag-var-spine⊥ tag-ok sp fresh p
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = A} refl refl) (fresh-fun-left fresh) q
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = B} refl refl) (fresh-fun-right fresh) r
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-right-all sp) fresh ()
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-right-all sp) fresh ()
  narrowing-tag-spine-overlap⊥ {C = C} {X = X} tag-ok (np-all p)
      sp fresh (∀ⁿ q) =
    narrowing-tag-spine-overlap⊥ tag-ok p (spine-strip-both sp)
      (λ occ → fresh (∈-all occ)) q
  narrowing-tag-spine-overlap⊥ {C = C} {X = X} tag-ok (np-all p)
      sp fresh (gen nonvarA zero∈A hC q C≢★) =
    narrowing-tag-spine-overlap⊥ tag-ok p (spine-peel-left suc sp)
      (fresh-shift fresh) q
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (untag-seq G hG allowed G꞉A q nonvarB A≢B) =
    narrow-path-star-spine⊥ (np-all p) sp
  narrowing-tag-spine-overlap⊥ {C = `∀ C} {X = X} tag-ok
      (np-gen p) sp fresh (∀ⁿ q) =
    narrowing-tag-spine-overlap⊥ tag-ok p (spine-peel-right suc sp)
      (λ occ → fresh (∈-all occ)) q
  narrowing-tag-spine-overlap⊥ {C = C} {X = X} tag-ok (np-gen p)
      sp fresh (gen nonvarA zero∈A hC q C≢★) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-map-right suc (spine-map-left suc sp))
      (fresh-shift fresh) q
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (untag-seq G hG allowed G꞉A q nonvarB A≢B) =
    narrow-path-star-spine⊥ (np-gen p) sp

  widening-tag-spine-overlap⊥ : ∀ {μ Δ Σ A B C c X}
    → μ X ≡ tag-or-id
    → WidenPath X A B
    → EndpointSpine B C
    → Fresh X C
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ C
    → ⊥
  widening-tag-spine-overlap⊥ tag-ok wp-var sp fresh p =
    widening-tag-var-spine⊥ tag-ok sp fresh p
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = A} refl refl) (fresh-fun-left fresh) q
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = B} refl refl) (fresh-fun-right fresh) r
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-right-all sp) fresh ()
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-right-all sp) fresh ()
  widening-tag-spine-overlap⊥ {C = C} {X = X} tag-ok (wp-all p)
      sp fresh (∀ʷ q) =
    widening-tag-spine-overlap⊥ tag-ok p (spine-strip-both sp)
      (λ occ → fresh (∈-all occ)) q
  widening-tag-spine-overlap⊥ {C = C} {X = X} tag-ok (wp-all p)
      sp fresh (inst nonvarA zero∈A hC q C≢★) =
    widening-tag-spine-overlap⊥ tag-ok p (spine-peel-left suc sp)
      (fresh-shift fresh) q
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (tag-seq G q hG allowed G꞉B nonvarA A≢B) =
    widen-path-star-spine⊥ (wp-all p) sp
  widening-tag-spine-overlap⊥ {C = `∀ C} {X = X} tag-ok
      (wp-inst p) sp fresh (∀ʷ q) =
    widening-tag-spine-overlap⊥ tag-ok p (spine-peel-right suc sp)
      (λ occ → fresh (∈-all occ)) q
  widening-tag-spine-overlap⊥ {C = C} {X = X} tag-ok (wp-inst p)
      sp fresh (inst nonvarA zero∈A hC q C≢★) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-map-right suc (spine-map-left suc sp))
      (fresh-shift fresh) q
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (tag-seq G q hG allowed G꞉B nonvarA A≢B) =
    widen-path-star-spine⊥ (wp-inst p) sp

narrowing-variable-to-star⊥ : ∀ {μ Δ Σ X c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊒ ★
  → ⊥
narrowing-variable-to-star⊥ ()

narrowing-all-to-star⊥ : ∀ {μ Δ Σ A c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ (`∀ A) ⊒ ★
  → ⊥
narrowing-all-to-star⊥ ()

widening-star-to-variable⊥ : ∀ {μ Δ Σ X c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ ＇ X
  → ⊥
widening-star-to-variable⊥ ()

widening-star-to-all⊥ : ∀ {μ Δ Σ A c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ (`∀ A)
  → ⊥
widening-star-to-all⊥ ()

narrowing-var-to-var-seal⊥ : ∀ {μ Δ Σ X Y c}
  → StoreWf Δ Σ
  → (X , ★) ∈ Σ
  → μ X ≡ seal-or-id
  → Y ≢ X
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ Y ⊒ ＇ X
  → ⊥
narrowing-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (idᵃ (＇ X) hX) =
  Y≢X refl
narrowing-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (seal X<Δ hY X,Y∈Σ allowed) with unique wfΣ X,★∈Σ X,Y∈Σ
narrowing-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (seal X<Δ hY X,Y∈Σ allowed) | ()
narrowing-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (seal-seq p X<Δ X,A∈Σ allowed Y≢A)
    with unique wfΣ X,★∈Σ X,A∈Σ
narrowing-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (seal-seq p X<Δ X,A∈Σ allowed Y≢A) | refl =
  narrowing-variable-to-star⊥ p

narrowing-all-to-var-seal⊥ : ∀ {μ Δ Σ X A c}
  → StoreWf Δ Σ
  → (X , ★) ∈ Σ
  → μ X ≡ seal-or-id
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ (`∀ A) ⊒ ＇ X
  → ⊥
narrowing-all-to-var-seal⊥ wfΣ X,★∈Σ seal-ok
    (seal X<Δ hA X,A∈Σ allowed) with unique wfΣ X,★∈Σ X,A∈Σ
narrowing-all-to-var-seal⊥ wfΣ X,★∈Σ seal-ok
    (seal X<Δ hA X,A∈Σ allowed) | ()
narrowing-all-to-var-seal⊥ wfΣ X,★∈Σ seal-ok
    (seal-seq p X<Δ X,B∈Σ allowed A≢B)
    with unique wfΣ X,★∈Σ X,B∈Σ
narrowing-all-to-var-seal⊥ wfΣ X,★∈Σ seal-ok
    (seal-seq p X<Δ X,B∈Σ allowed A≢B) | refl =
  narrowing-all-to-star⊥ p

widening-var-to-var-seal⊥ : ∀ {μ Δ Σ X Y c}
  → StoreWf Δ Σ
  → (X , ★) ∈ Σ
  → μ X ≡ seal-or-id
  → Y ≢ X
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ ＇ Y
  → ⊥
widening-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (idᵃ (＇ X) hX) =
  Y≢X refl
widening-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (unseal X<Δ hY X,Y∈Σ allowed) with unique wfΣ X,★∈Σ X,Y∈Σ
widening-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (unseal X<Δ hY X,Y∈Σ allowed) | ()
widening-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (unseal-seq X<Δ X,A∈Σ allowed p A≢Y)
    with unique wfΣ X,★∈Σ X,A∈Σ
widening-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok Y≢X
    (unseal-seq X<Δ X,A∈Σ allowed p A≢Y) | refl =
  widening-star-to-variable⊥ p

widening-var-to-all-seal⊥ : ∀ {μ Δ Σ X A c}
  → StoreWf Δ Σ
  → (X , ★) ∈ Σ
  → μ X ≡ seal-or-id
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ (`∀ A)
  → ⊥
widening-var-to-all-seal⊥ wfΣ X,★∈Σ seal-ok
    (unseal X<Δ hA X,A∈Σ allowed) with unique wfΣ X,★∈Σ X,A∈Σ
widening-var-to-all-seal⊥ wfΣ X,★∈Σ seal-ok
    (unseal X<Δ hA X,A∈Σ allowed) | ()
widening-var-to-all-seal⊥ wfΣ X,★∈Σ seal-ok
    (unseal-seq X<Δ X,B∈Σ allowed p B≢A)
    with unique wfΣ X,★∈Σ X,B∈Σ
widening-var-to-all-seal⊥ wfΣ X,★∈Σ seal-ok
    (unseal-seq X<Δ X,B∈Σ allowed p B≢A) | refl =
  widening-star-to-all⊥ p

narrowing-seal-var-spine⊥ : ∀ {μ Δ Σ X C c}
  → StoreWf Δ Σ
  → (X , ★) ∈ Σ
  → μ X ≡ seal-or-id
  → EndpointSpine (＇ X) C
  → Fresh X C
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ C ⊒ ＇ X
  → ⊥
narrowing-seal-var-spine⊥ wfΣ X,★∈Σ seal-ok
    (spine-renamed {T = ＇ Y} refl refl) fresh p =
  narrowing-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok
    (fresh-variable-neq fresh) p
narrowing-seal-var-spine⊥ wfΣ X,★∈Σ seal-ok
    (spine-right-all sp) fresh p =
  narrowing-all-to-var-seal⊥ wfΣ X,★∈Σ seal-ok p

widening-seal-var-spine⊥ : ∀ {μ Δ Σ X C c}
  → StoreWf Δ Σ
  → (X , ★) ∈ Σ
  → μ X ≡ seal-or-id
  → EndpointSpine (＇ X) C
  → Fresh X C
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ C
  → ⊥
widening-seal-var-spine⊥ wfΣ X,★∈Σ seal-ok
    (spine-renamed {T = ＇ Y} refl refl) fresh p =
  widening-var-to-var-seal⊥ wfΣ X,★∈Σ seal-ok
    (fresh-variable-neq fresh) p
widening-seal-var-spine⊥ wfΣ X,★∈Σ seal-ok
    (spine-right-all sp) fresh p =
  widening-var-to-all-seal⊥ wfΣ X,★∈Σ seal-ok p

mutual

  narrowing-seal-spine-overlap⊥ : ∀ {μ Δ Σ A B C c X}
    → StoreWf Δ Σ
    → (X , ★) ∈ Σ
    → μ X ≡ seal-or-id
    → NarrowPath X A B
    → EndpointSpine A C
    → Fresh X C
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ C ⊒ B
    → ⊥
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok np-var
      sp fresh p =
    narrowing-seal-var-spine⊥ wfΣ X,★∈Σ seal-ok sp fresh p
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (np-fun₁ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok p
      (spine-renamed {T = A} refl refl) (fresh-fun-left fresh) q
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (np-fun₂ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok p
      (spine-renamed {T = B} refl refl) (fresh-fun-right fresh) r
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (np-fun₁ p)
      (spine-right-all sp) fresh ()
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (np-fun₂ p)
      (spine-right-all sp) fresh ()
  narrowing-seal-spine-overlap⊥ {C = C} {X = X} wfΣ X,★∈Σ
      seal-ok (np-all p) sp fresh (∀ⁿ q) =
    narrowing-seal-spine-overlap⊥ (StoreWf-⟰ᵗ wfΣ)
      (∈-renameTyStoreᵗ suc X,★∈Σ) seal-ok p (spine-strip-both sp)
      (λ occ → fresh (∈-all occ)) q
  narrowing-seal-spine-overlap⊥ {C = C} {X = X} wfΣ X,★∈Σ
      seal-ok (np-all p) sp fresh
      (gen nonvarA zero∈A hC q C≢★) =
    narrowing-seal-spine-overlap⊥ (StoreWf-⟰ᵗ wfΣ)
      (∈-renameTyStoreᵗ suc X,★∈Σ) seal-ok p
      (spine-peel-left suc sp) (fresh-shift fresh) q
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (np-all p)
      sp fresh (untag-seq G hG allowed G꞉A q nonvarB A≢B) =
    narrow-path-star-spine⊥ (np-all p) sp
  narrowing-seal-spine-overlap⊥ {C = `∀ C} {X = X} wfΣ X,★∈Σ
      seal-ok (np-gen p) sp fresh (∀ⁿ q) =
    narrowing-seal-spine-overlap⊥ (StoreWf-⟰ᵗ wfΣ)
      (∈-renameTyStoreᵗ suc X,★∈Σ) seal-ok p
      (spine-peel-right suc sp) (λ occ → fresh (∈-all occ)) q
  narrowing-seal-spine-overlap⊥ {C = C} {X = X} wfΣ X,★∈Σ
      seal-ok (np-gen p) sp fresh
      (gen nonvarA zero∈A hC q C≢★) =
    narrowing-seal-spine-overlap⊥ (StoreWf-⟰ᵗ wfΣ)
      (∈-renameTyStoreᵗ suc X,★∈Σ) seal-ok p
      (spine-map-right suc (spine-map-left suc sp))
      (fresh-shift fresh) q
  narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (np-gen p)
      sp fresh (untag-seq G hG allowed G꞉A q nonvarB A≢B) =
    narrow-path-star-spine⊥ (np-gen p) sp

  widening-seal-spine-overlap⊥ : ∀ {μ Δ Σ A B C c X}
    → StoreWf Δ Σ
    → (X , ★) ∈ Σ
    → μ X ≡ seal-or-id
    → WidenPath X A B
    → EndpointSpine B C
    → Fresh X C
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ C
    → ⊥
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok wp-var
      sp fresh p =
    widening-seal-var-spine⊥ wfΣ X,★∈Σ seal-ok sp fresh p
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (wp-fun₁ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    narrowing-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok p
      (spine-renamed {T = A} refl refl) (fresh-fun-left fresh) q
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (wp-fun₂ p)
      (spine-renamed {T = A ⇒ B} refl refl) fresh (q ↦ r) =
    widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok p
      (spine-renamed {T = B} refl refl) (fresh-fun-right fresh) r
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (wp-fun₁ p)
      (spine-right-all sp) fresh ()
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (wp-fun₂ p)
      (spine-right-all sp) fresh ()
  widening-seal-spine-overlap⊥ {C = C} {X = X} wfΣ X,★∈Σ
      seal-ok (wp-all p) sp fresh (∀ʷ q) =
    widening-seal-spine-overlap⊥ (StoreWf-⟰ᵗ wfΣ)
      (∈-renameTyStoreᵗ suc X,★∈Σ) seal-ok p (spine-strip-both sp)
      (λ occ → fresh (∈-all occ)) q
  widening-seal-spine-overlap⊥ {C = C} {X = X} wfΣ X,★∈Σ
      seal-ok (wp-all p) sp fresh
      (inst nonvarA zero∈A hC q C≢★) =
    widening-seal-spine-overlap⊥ (StoreWf-bind wfΣ wf★)
      (there (∈-renameTyStoreᵗ suc X,★∈Σ)) seal-ok p
      (spine-peel-left suc sp) (fresh-shift fresh) q
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (wp-all p)
      sp fresh (tag-seq G q hG allowed G꞉B nonvarA A≢B) =
    widen-path-star-spine⊥ (wp-all p) sp
  widening-seal-spine-overlap⊥ {C = `∀ C} {X = X} wfΣ X,★∈Σ
      seal-ok (wp-inst p) sp fresh (∀ʷ q) =
    widening-seal-spine-overlap⊥ (StoreWf-⟰ᵗ wfΣ)
      (∈-renameTyStoreᵗ suc X,★∈Σ) seal-ok p
      (spine-peel-right suc sp) (λ occ → fresh (∈-all occ)) q
  widening-seal-spine-overlap⊥ {C = C} {X = X} wfΣ X,★∈Σ
      seal-ok (wp-inst p) sp fresh
      (inst nonvarA zero∈A hC q C≢★) =
    widening-seal-spine-overlap⊥ (StoreWf-bind wfΣ wf★)
      (there (∈-renameTyStoreᵗ suc X,★∈Σ)) seal-ok p
      (spine-map-right suc (spine-map-left suc sp))
      (fresh-shift fresh) q
  widening-seal-spine-overlap⊥ wfΣ X,★∈Σ seal-ok (wp-inst p)
      sp fresh (tag-seq G q hG allowed G꞉B nonvarA A≢B) =
    widen-path-star-spine⊥ (wp-inst p) sp

------------------------------------------------------------------------
-- The two binder overlaps
------------------------------------------------------------------------

inserted-binder-spine : ∀ A
  → EndpointSpine A (⇑ᵗ (`∀ A))
inserted-binder-spine A =
  spine-right-all
    (spine-renamed {T = A} {ρ = λ X → X} {τ = extᵗ suc}
      (sym (renameᵗ-id A)) refl)

inserted-binder-fresh : ∀ A
  → Fresh zero (⇑ᵗ (`∀ A))
inserted-binder-fresh A (∈-all occ)
    with rename-member-inv (extᵗ suc) occ
inserted-binder-fresh A (∈-all occ) | zero , () , zero∈A
inserted-binder-fresh A (∈-all occ) | suc X , () , X∈A

narrowing-all-gen-overlap⊥ : ∀ {μ Δ Σ A B c d}
  → StoreWf Δ Σ
  → zero ∈ᵗ B
  → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ⊒ B
  → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ d ⦂ ⇑ᵗ (`∀ A) ⊒ B
  → ⊥
narrowing-all-gen-overlap⊥ {A = A} wfΣ zero∈B p q =
  narrowing-tag-spine-overlap⊥ refl
    (narrowing-target-path-id-only refl p zero∈B)
    (inserted-binder-spine A) (inserted-binder-fresh A) q

widening-all-inst-overlap⊥ : ∀ {μ Δ Σ A B c d}
  → StoreWf Δ Σ
  → zero ∈ᵗ A
  → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ⊑ B
  → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
      ⊢ d ⦂ A ⊑ ⇑ᵗ (`∀ B)
  → ⊥
widening-all-inst-overlap⊥ {B = B} wfΣ zero∈A p q =
  widening-seal-spine-overlap⊥ (StoreWf-bind wfΣ wf★) (here refl) refl
    (widening-source-path-id-only refl p zero∈A)
    (inserted-binder-spine B) (inserted-binder-fresh B) q

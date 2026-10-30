module proof.LR.WorldProps where

-- File Charter:
--   * Properties of worlds (notes/logrel-dgg.md, Section 6.9, lemma 1):
--     renaming descriptors, entries and tags along store embeddings is
--     the identity at the identity embedding and respects composition,
--     so world extension is reflexive and transitive.
--   * Composition of embeddings is associative with the identity as
--     unit; this holds on the nose because embeddings are canonical.

open import Data.List using (List; []; _∷_; map)
import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
import Data.Vec as Vec
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ)
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
open import proof.TypeInTermSubst using (toRename-id-eq; renameᵗ-id)
open import LR.Desc
open import LR.World

------------------------------------------------------------------------
-- Embeddings
------------------------------------------------------------------------

∘↪-idʳ : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) → π ∘↪ id↪ᵗ ≡ π
∘↪-idʳ empty = refl
∘↪-idʳ (keep π) = cong keep (∘↪-idʳ π)
∘↪-idʳ {Δ = zero} (skip π) = refl
∘↪-idʳ {Δ = suc Δ} (skip π) = cong skip (∘↪-idʳ π)

∘↪-idˡ : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) → id↪ᵗ ∘↪ η ≡ η
∘↪-idˡ empty = refl
∘↪-idˡ (keep η) = cong keep (∘↪-idˡ η)
∘↪-idˡ (skip η) = cong skip (∘↪-idˡ η)

∘↪-assoc : ∀ {Δ₁ Δ₂ Δ₃ Δ₄}
    (π : Δ₃ ↪ᵗ Δ₄) (η : Δ₂ ↪ᵗ Δ₃) (θ : Δ₁ ↪ᵗ Δ₂)
  → (π ∘↪ η) ∘↪ θ ≡ π ∘↪ (η ∘↪ θ)
∘↪-assoc π η empty = refl
∘↪-assoc (skip π) (keep η) (keep θ) =
  cong skip (∘↪-assoc π (keep η) (keep θ))
∘↪-assoc (skip π) (keep η) (skip θ) =
  cong skip (∘↪-assoc π (keep η) (skip θ))
∘↪-assoc (skip π) (skip η) (keep θ) =
  cong skip (∘↪-assoc π (skip η) (keep θ))
∘↪-assoc (skip π) (skip η) (skip θ) =
  cong skip (∘↪-assoc π (skip η) (skip θ))
∘↪-assoc (keep π) (keep η) (keep θ) = cong keep (∘↪-assoc π η θ)
∘↪-assoc (keep π) (keep η) (skip θ) = cong skip (∘↪-assoc π η θ)
∘↪-assoc (keep π) (skip η) (keep θ) = cong skip (∘↪-assoc π η (keep θ))
∘↪-assoc (keep π) (skip η) (skip θ) = cong skip (∘↪-assoc π η (skip θ))

------------------------------------------------------------------------
-- Variables, lists and types
------------------------------------------------------------------------

renameVar-id : ∀ {Δ} (X : TyVar Δ) → renameVar id↪ᵗ X ≡ X
renameVar-id = toRename-id-eq

renameVar-∘ : ∀ {Δ₁ Δ₂ Δ₃} (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂) X
  → renameVar π (renameVar η X) ≡ renameVar (π ∘↪ η) X
renameVar-∘ π η X = sym (toRenameᵗ-∘ π η X)

map-renameVar-id : ∀ {Δ} (Xs : List (TyVar Δ))
  → map (renameVar id↪ᵗ) Xs ≡ Xs
map-renameVar-id [] = refl
map-renameVar-id (X ∷ Xs) = cong₂ _∷_ (renameVar-id X) (map-renameVar-id Xs)

map-renameVar-∘ : ∀ {Δ₁ Δ₂ Δ₃} (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂)
    (Xs : List (TyVar Δ₁))
  → map (renameVar π) (map (renameVar η) Xs) ≡ map (renameVar (π ∘↪ η)) Xs
map-renameVar-∘ π η [] = refl
map-renameVar-∘ π η (X ∷ Xs) =
  cong₂ _∷_ (renameVar-∘ π η X) (map-renameVar-∘ π η Xs)

renameTy-id : ∀ {Δ} (A : Ty Δ) → renameᵗ (toRenameᵗ id↪ᵗ) A ≡ A
renameTy-id A = trans (renameᵗ-cong A toRename-id-eq) (renameᵗ-id A)

renameTy-∘ : ∀ {Δ₁ Δ₂ Δ₃} (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂) (A : Ty Δ₁)
  → renameᵗ (toRenameᵗ π) (renameᵗ (toRenameᵗ η) A)
    ≡ renameᵗ (toRenameᵗ (π ∘↪ η)) A
renameTy-∘ π η A =
  trans (renameᵗ-comp (toRenameᵗ η) (toRenameᵗ π) A)
    (renameᵗ-cong A (λ X → sym (toRenameᵗ-∘ π η X)))

map-renameTy-id : ∀ {Δ k} (As : Vec (Ty Δ) k)
  → Vec.map (renameᵗ (toRenameᵗ id↪ᵗ)) As ≡ As
map-renameTy-id []ᵛ = refl
map-renameTy-id (A ∷ᵛ As) = cong₂ _∷ᵛ_ (renameTy-id A) (map-renameTy-id As)

map-renameTy-∘ : ∀ {Δ₁ Δ₂ Δ₃ k} (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂)
    (As : Vec (Ty Δ₁) k)
  → Vec.map (renameᵗ (toRenameᵗ π)) (Vec.map (renameᵗ (toRenameᵗ η)) As)
    ≡ Vec.map (renameᵗ (toRenameᵗ (π ∘↪ η))) As
map-renameTy-∘ π η []ᵛ = refl
map-renameTy-∘ π η (A ∷ᵛ As) =
  cong₂ _∷ᵛ_ (renameTy-∘ π η A) (map-renameTy-∘ π η As)

------------------------------------------------------------------------
-- Descriptors, entries and tags
------------------------------------------------------------------------

mutual
  renameDesc-id : ∀ {ΔL ΔR} (c : Desc ΔL ΔR)
    → renameDesc id↪ᵗ id↪ᵗ c ≡ c
  renameDesc-id (desc p env envR) =
    cong₂ (desc p) (renameEntries-id env) (map-renameTy-id envR)

  renameEntries-id : ∀ {ΔL ΔR k} (es : Vec (Entry ΔL ΔR) k)
    → renameEntries id↪ᵗ id↪ᵗ es ≡ es
  renameEntries-id []ᵛ = refl
  renameEntries-id (e ∷ᵛ es) =
    cong₂ _∷ᵛ_ (renameEntry-id e) (renameEntries-id es)

  renameEntry-id : ∀ {ΔL ΔR} (e : Entry ΔL ΔR)
    → renameEntry id↪ᵗ id↪ᵗ e ≡ e
  renameEntry-id (seals X Xs Ys c)
    rewrite renameVar-id X | map-renameVar-id Xs | map-renameVar-id Ys
          | renameDesc-id c = refl

mutual
  renameDesc-∘ : ∀ {ΔL₁ ΔL₂ ΔL₃ ΔR₁ ΔR₂ ΔR₃}
      (πL : ΔL₂ ↪ᵗ ΔL₃) (ηL : ΔL₁ ↪ᵗ ΔL₂)
      (πR : ΔR₂ ↪ᵗ ΔR₃) (ηR : ΔR₁ ↪ᵗ ΔR₂) (c : Desc ΔL₁ ΔR₁)
    → renameDesc πL πR (renameDesc ηL ηR c)
      ≡ renameDesc (πL ∘↪ ηL) (πR ∘↪ ηR) c
  renameDesc-∘ πL ηL πR ηR (desc p env envR) =
    cong₂ (desc p) (renameEntries-∘ πL ηL πR ηR env)
      (map-renameTy-∘ πR ηR envR)

  renameEntries-∘ : ∀ {ΔL₁ ΔL₂ ΔL₃ ΔR₁ ΔR₂ ΔR₃ k}
      (πL : ΔL₂ ↪ᵗ ΔL₃) (ηL : ΔL₁ ↪ᵗ ΔL₂)
      (πR : ΔR₂ ↪ᵗ ΔR₃) (ηR : ΔR₁ ↪ᵗ ΔR₂) (es : Vec (Entry ΔL₁ ΔR₁) k)
    → renameEntries πL πR (renameEntries ηL ηR es)
      ≡ renameEntries (πL ∘↪ ηL) (πR ∘↪ ηR) es
  renameEntries-∘ πL ηL πR ηR []ᵛ = refl
  renameEntries-∘ πL ηL πR ηR (e ∷ᵛ es) =
    cong₂ _∷ᵛ_ (renameEntry-∘ πL ηL πR ηR e)
      (renameEntries-∘ πL ηL πR ηR es)

  renameEntry-∘ : ∀ {ΔL₁ ΔL₂ ΔL₃ ΔR₁ ΔR₂ ΔR₃}
      (πL : ΔL₂ ↪ᵗ ΔL₃) (ηL : ΔL₁ ↪ᵗ ΔL₂)
      (πR : ΔR₂ ↪ᵗ ΔR₃) (ηR : ΔR₁ ↪ᵗ ΔR₂) (e : Entry ΔL₁ ΔR₁)
    → renameEntry πL πR (renameEntry ηL ηR e)
      ≡ renameEntry (πL ∘↪ ηL) (πR ∘↪ ηR) e
  renameEntry-∘ πL ηL πR ηR (seals X Xs Ys c)
    rewrite renameVar-∘ πL ηL X | map-renameVar-∘ πL ηL Xs
          | map-renameVar-∘ πR ηR Ys | renameDesc-∘ πL ηL πR ηR c = refl

------------------------------------------------------------------------
-- The types a descriptor relates, renamed
------------------------------------------------------------------------

lookup-renameEntries : ∀ {ΔL ΔL′ ΔR ΔR′ k}
    (σL : ΔL ↪ᵗ ΔL′) (σR : ΔR ↪ᵗ ΔR′) (es : Vec (Entry ΔL ΔR) k) X
  → Vec.lookup (renameEntries σL σR es) X
    ≡ renameEntry σL σR (Vec.lookup es X)
lookup-renameEntries σL σR (e ∷ᵛ es) Fin.zero = refl
lookup-renameEntries σL σR (e ∷ᵛ es) (Fin.suc X) =
  lookup-renameEntries σL σR es X

entryTy-rename : ∀ {ΔL ΔL′ ΔR ΔR′} (σL : ΔL ↪ᵗ ΔL′) (σR : ΔR ↪ᵗ ΔR′)
    (e : Entry ΔL ΔR)
  → entryTy (renameEntry σL σR e) ≡ renameᵗ (toRenameᵗ σL) (entryTy e)
entryTy-rename σL σR (seals X Xs Ys c) = refl

leftTy-rename : ∀ {ΔL ΔL′ ΔR ΔR′} (σL : ΔL ↪ᵗ ΔL′) (σR : ΔR ↪ᵗ ΔR′)
    (c : Desc ΔL ΔR)
  → leftTy (renameDesc σL σR c) ≡ renameᵗ (toRenameᵗ σL) (leftTy c)
leftTy-rename σL σR (desc {A = A} p env envR) =
  trans (substᵗ-cong A eq)
    (sym (renameᵗ-subst (toRenameᵗ σL)
      (λ X → entryTy (Vec.lookup env X)) A))
  where
  eq : ∀ X → entryTy (Vec.lookup (renameEntries σL σR env) X)
    ≡ renameᵗ (toRenameᵗ σL) (entryTy (Vec.lookup env X))
  eq X = trans (cong entryTy (lookup-renameEntries σL σR env X))
    (entryTy-rename σL σR (Vec.lookup env X))

rightTy-rename : ∀ {ΔL ΔL′ ΔR ΔR′} (σL : ΔL ↪ᵗ ΔL′) (σR : ΔR ↪ᵗ ΔR′)
    (c : Desc ΔL ΔR)
  → rightTy (renameDesc σL σR c) ≡ renameᵗ (toRenameᵗ σR) (rightTy c)
rightTy-rename σL σR (desc {A′ = A′} p env envR) =
  trans (substᵗ-cong A′ (λ X → lookup-map X (renameᵗ (toRenameᵗ σR)) envR))
    (sym (renameᵗ-subst (toRenameᵗ σR) (Vec.lookup envR) A′))

repL-rename : ∀ {ΔL ΔL′ ΔR ΔR′} (σL : ΔL ↪ᵗ ΔL′) (σR : ΔR ↪ᵗ ΔR′)
    (Xs : List (TyVar ΔL)) (c : Desc ΔL ΔR)
  → repL (map (renameVar σL) Xs) (renameDesc σL σR c)
    ≡ renameᵗ (toRenameᵗ σL) (repL Xs c)
repL-rename σL σR [] c = leftTy-rename σL σR c
repL-rename σL σR (X ∷ Xs) c = refl

repR-rename : ∀ {ΔL ΔL′ ΔR ΔR′} (σL : ΔL ↪ᵗ ΔL′) (σR : ΔR ↪ᵗ ΔR′)
    (Ys : List (TyVar ΔR)) (c : Desc ΔL ΔR)
  → repR (map (renameVar σR) Ys) (renameDesc σL σR c)
    ≡ renameᵗ (toRenameᵗ σR) (repR Ys c)
repR-rename σL σR [] c = rightTy-rename σL σR c
repR-rename σL σR (Y ∷ Ys) c = refl

renameTag-id : ∀ {ΔL ΔR} (t : Tag ΔL ΔR) → renameTag id↪ᵗ id↪ᵗ t ≡ t
renameTag-id (just Y , e)
  rewrite renameVar-id Y | renameEntry-id e = refl
renameTag-id (nothing , e) rewrite renameEntry-id e = refl

renameTag-∘ : ∀ {ΔL₁ ΔL₂ ΔL₃ ΔR₁ ΔR₂ ΔR₃}
    (πL : ΔL₂ ↪ᵗ ΔL₃) (ηL : ΔL₁ ↪ᵗ ΔL₂)
    (πR : ΔR₂ ↪ᵗ ΔR₃) (ηR : ΔR₁ ↪ᵗ ΔR₂) (t : Tag ΔL₁ ΔR₁)
  → renameTag πL πR (renameTag ηL ηR t)
    ≡ renameTag (πL ∘↪ ηL) (πR ∘↪ ηR) t
renameTag-∘ πL ηL πR ηR (just Y , e)
  rewrite renameVar-∘ πR ηR Y | renameEntry-∘ πL ηL πR ηR e = refl
renameTag-∘ πL ηL πR ηR (nothing , e)
  rewrite renameEntry-∘ πL ηL πR ηR e = refl

------------------------------------------------------------------------
-- Extension is reflexive and transitive
------------------------------------------------------------------------

⊒-refl : ∀ (w : World) → w ⊒ w
⊒-refl w = ext id↪ᵗ id↪ᵗ tags≡′
  where
  tags≡′ : ∀ X → tag w (toRenameᵗ id↪ᵗ X) ≡ renameTag id↪ᵗ id↪ᵗ (tag w X)
  tags≡′ X = trans (cong (tag w) (toRename-id-eq X))
                   (sym (renameTag-id (tag w X)))

⊒-trans : ∀ {w w′ w″ : World} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
⊒-trans {w} {w′} {w″} e′ e =
  ext (ρL e′ ∘↪ ρL e) (ρR e′ ∘↪ ρR e) tags≡′
  where
  tags≡′ : ∀ X → tag w″ (toRenameᵗ (ρL e′ ∘↪ ρL e) X)
    ≡ renameTag (ρL e′ ∘↪ ρL e) (ρR e′ ∘↪ ρR e) (tag w X)
  tags≡′ X =
    trans (cong (tag w″) (toRenameᵗ-∘ (ρL e′) (ρL e) X))
      (trans (tags≡ e′ (toRenameᵗ (ρL e) X))
        (trans (cong (renameTag (ρL e′) (ρR e′)) (tags≡ e X))
          (renameTag-∘ (ρL e′) (ρL e) (ρR e′) (ρR e) (tag w X))))

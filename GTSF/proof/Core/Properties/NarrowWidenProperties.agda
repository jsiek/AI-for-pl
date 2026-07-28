module proof.Core.Properties.NarrowWidenProperties where

-- File Charter:
--   * Structural lemmas for mode-indexed narrowing/widening coercion judgments.
--   * Determinacy and dual endpoint-flipping theorems for narrowing/widening.
--   * Depends on the public definitions in `NarrowWiden`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∨_)
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
open import proof.Compilation.GenSafeProperties
  using (genSafe-star-source⊥; instSafe-star-target⊥)
import proof.Core.Properties.CoercionProperties as CoercionProof
open import proof.Core.Properties.CoercionProperties
  using
    ( DualActionOk
    ; DualStoreAt
    ; coercion-mode-relax
    ; coercion-src-tgtᵐ
    ; dma-id
    ; dma-tag
    ; dma-seal
    ; dma-tag-seal
    ; dma-seal-tag
    ; dualActionOk-ext
    ; dualActionOk-gen-inst
    ; dualActionOk-idTyAllowed
    ; dualActionOk-inst-gen
    ; dualActionOk-normal
    ; dualStoreAt-ext
    ; dualStoreAt-gen-inst
    ; dualStoreAt-inst-gen
    ; dualStoreAt-normal
    ; ModeRename
    ; renameᶜ-open-commute
    ; sealModeAllowed-var-seal
    ; single-mode-rename-lower
    ; src-renameᶜ
    ; tagModeAllowed-var-tag
    )
open import proof.Core.Properties.StoreProperties
  using
    ( StoreWfAt-cons
    ; StoreWfAt-⟰ᵗ
    ; ∈-renameStoreᵗ
    ; renameStoreᵗ-incl
    )
open import proof.Core.Properties.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; TyRenameWf-suc-≤
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
    ; renameStoreᵗ-single-suc-cancel
    ; singleRenameᵗ-Wf-<
    )
open import proof.Core.Properties.NarrowWidenStoreInvariantDef
open import proof.Core.Properties.NarrowWidenStoreInvariantProof

------------------------------------------------------------------------
-- Opening typed narrowing and widening at a fresh seal name
------------------------------------------------------------------------

open-narrowing :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊒ B [ α ]ᴿ
open-narrowing {μ = μ} {Σ = Σ} {α = α} α<Δ c⊒ =
  subst
    (λ Σ′ → μ ∣ _ ∣ Σ′ ⊢ _ ∶ _ ⊒ _)
    (renameStoreᵗ-single-suc-cancel α Σ)
    (narrow-renameᵗ
      (singleRenameᵗ-Wf-< α<Δ)
      (single-mode-rename-lower μ α)
      c⊒)

open-widening :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊑ B [ α ]ᴿ
open-widening {μ = μ} {Σ = Σ} {α = α} α<Δ c⊑ =
  subst
    (λ Σ′ → μ ∣ _ ∣ Σ′ ⊢ _ ∶ _ ⊑ _)
    (renameStoreᵗ-single-suc-cancel α Σ)
    (widen-renameᵗ
      (singleRenameᵗ-Wf-< α<Δ)
      (single-mode-rename-lower μ α)
      c⊑)

open-all-narrowing :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊒ `∀ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊒ B [ α ]ᴿ
open-all-narrowing α<Δ (cast-all c⊢ , cross (`∀ cⁿ)) =
  open-narrowing α<Δ (c⊢ , cⁿ)

open-all-widening :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊑ B [ α ]ᴿ
open-all-widening α<Δ (cast-all c⊢ , cross (`∀ cʷ)) =
  open-widening α<Δ (c⊢ , cʷ)

allocate-all-narrowing :
  ∀ {μ Δ Σ Aν c A B} →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊒ `∀ B →
  extᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ ⊢ c ∶ A ⊒ B
allocate-all-narrowing (cast-all c⊢ , cross (`∀ cⁿ)) =
  narrow-weaken ≤-refl StoreIncl-drop (c⊢ , cⁿ)

allocate-all-widening :
  ∀ {μ Δ Σ Aν c A B} →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  extᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ ⊢ c ∶ A ⊑ B
allocate-all-widening (cast-all c⊢ , cross (`∀ cʷ)) =
  widen-weaken ≤-refl StoreIncl-drop (c⊢ , cʷ)

allocate-gen-narrowing :
  ∀ {μ Δ Σ Aν c A B} →
  μ ∣ Δ ∣ Σ ⊢ gen A c ∶ A ⊒ `∀ B →
  genᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ
    ⊢ c ∶ ⇑ᵗ A ⊒ B
allocate-gen-narrowing (cast-gen hA occ c⊢ , gen cᵍ) =
  narrow-weaken ≤-refl StoreIncl-drop
    (c⊢ , genSafe→narrowing cᵍ)

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

idModeAllowed-any :
  ∀ m →
  idModeAllowed m ≡ true
idModeAllowed-any id-only = refl
idModeAllowed-any tag-or-id = refl
idModeAllowed-any seal-or-id = refl

srcStoreⁿ-⊒ˢ :
  ∀ {Δ σ Σ Σ′} →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Σ ≡ srcStoreⁿ σ
srcStoreⁿ-⊒ˢ ⊒ˢ-nil = refl
srcStoreⁿ-⊒ˢ (⊒ˢ-right hA σ⊒) =
  srcStoreⁿ-⊒ˢ σ⊒
srcStoreⁿ-⊒ˢ (⊒ˢ-left {X = X} σ⊒) =
  cong (λ Σ → (X , ★) ∷ Σ) (srcStoreⁿ-⊒ˢ σ⊒)
srcStoreⁿ-⊒ˢ (⊒ˢ-both {X = X} hA hA′ (μ , s⊒) σ⊒) =
  cong₂ _∷_
    (cong (λ A → (X , A))
      (sym (proj₁ (coercion-src-tgtᵐ (proj₁ s⊒)))))
    (srcStoreⁿ-⊒ˢ σ⊒)

tgtStoreⁿ-⊒ˢ :
  ∀ {Δ σ Σ Σ′} →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Σ′ ≡ tgtStoreⁿ σ
tgtStoreⁿ-⊒ˢ ⊒ˢ-nil = refl
tgtStoreⁿ-⊒ˢ (⊒ˢ-right {A = A} {X = X} hA σ⊒) =
  cong (λ Σ′ → (X , A) ∷ Σ′) (tgtStoreⁿ-⊒ˢ σ⊒)
tgtStoreⁿ-⊒ˢ (⊒ˢ-left σ⊒) =
  tgtStoreⁿ-⊒ˢ σ⊒
tgtStoreⁿ-⊒ˢ (⊒ˢ-both {X = X} hA hA′ (μ , s⊒) σ⊒) =
  cong₂ _∷_
    (cong (λ B → (X , B))
      (sym (proj₂ (coercion-src-tgtᵐ (proj₁ s⊒)))))
    (tgtStoreⁿ-⊒ˢ σ⊒)

⊑ˢ-target-unique :
  ∀ {Δ σ Σ Σ′ Π Π′} →
  Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′ →
  Δ ⊢ σ ꞉ Π ⊑ˢ Π′ →
  Σ′ ≡ Π′
⊑ˢ-target-unique ⊑ˢ-nil ⊑ˢ-nil = refl
⊑ˢ-target-unique (⊑ˢ-left hA σ⊑) (⊑ˢ-left hB π⊑) =
  ⊑ˢ-target-unique σ⊑ π⊑
⊑ˢ-target-unique (⊑ˢ-right {X = X} σ⊑) (⊑ˢ-right π⊑) =
  cong (λ Σ′ → (X , ★) ∷ Σ′) (⊑ˢ-target-unique σ⊑ π⊑)
⊑ˢ-target-unique
    (⊑ˢ-both {X = X} hA hA′ (μ , s⊑) σ⊑)
    (⊑ˢ-both hB hB′ (ν , t⊑) π⊑) =
  cong₂ _∷_
    (cong (λ A → (X , A))
      (trans
        (sym (proj₂ (coercion-src-tgtᵐ (proj₁ s⊑))))
        (proj₂ (coercion-src-tgtᵐ (proj₁ t⊑)))))
    (⊑ˢ-target-unique σ⊑ π⊑)

≈ⁿ-trans :
  ∀ {Δ σ r s t A B} →
  Δ ∣ σ ⊢ r ≈ s ∶ A ⊒ B →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ σ ⊢ r ≈ t ∶ A ⊒ B
≈ⁿ-trans {Δ = Δ} {t = t} {A = A} {B = B}
    (endpointsⁿ {Σ = Σ} {Σ′ = Σ′}
      srcr tgtr srcs tgts σ⊒ wfΣ wfΣ′ r⊒ s⊒)
    (endpointsⁿ {Σ = Π} {Σ′ = Π′}
      srcs′ tgts′ srct tgtt π⊒ wfΠ wfΠ′ s⊒′ t⊒) =
  endpointsⁿ srcr tgtr srct tgtt σ⊒ wfΣ wfΣ′ r⊒
    (subst
      (λ Σ₀ → Δ ∣ Σ₀ ⊢ t ∶ A ⊒ B)
      (trans (srcStoreⁿ-⊒ˢ π⊒) (sym (srcStoreⁿ-⊒ˢ σ⊒)))
      t⊒)

≈ʷ-trans :
  ∀ {Δ σ r s t A B} →
  Δ ∣ σ ⊢ r ≈ s ∶ A ⊑ B →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B →
  Δ ∣ σ ⊢ r ≈ t ∶ A ⊑ B
≈ʷ-trans {Δ = Δ} {t = t} {A = A} {B = B}
    (endpoints {Σ = Σ} {Σ′ = Σ′}
      srcr tgtr srcs tgts σ⊑ wfΣ wfΣ′ r⊑ s⊑)
    (endpoints {Σ = Π} {Σ′ = Π′}
      srcs′ tgts′ srct tgtt π⊑ wfΠ wfΠ′ s⊑′ t⊑) =
  endpoints srcr tgtr srct tgtt σ⊑ wfΣ wfΣ′ r⊑
    (subst
      (λ Σ₀ → ∃[ μ ] μ ∣ Δ ∣ Σ₀ ⊢ t ∶ A ⊑ B)
      (⊑ˢ-target-unique π⊑ σ⊑)
      t⊑)

srcStoreⁿ-⇑ˢ :
  ∀ σ →
  srcStoreⁿ (⇑ˢ σ) ≡ ⟰ᵗ (srcStoreⁿ σ)
srcStoreⁿ-⇑ˢ [] = refl
srcStoreⁿ-⇑ˢ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong (λ A → (suc X , A)) (src-renameᶜ suc p))
    (srcStoreⁿ-⇑ˢ σ)
srcStoreⁿ-⇑ˢ ((X ꞉= A ⊒) ∷ σ) = srcStoreⁿ-⇑ˢ σ
srcStoreⁿ-⇑ˢ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_ refl (srcStoreⁿ-⇑ˢ σ)

modeRename-suc-tag-or-id :
  ModeRename suc tag-or-idᵈ tag-or-idᵈ
modeRename-suc-tag-or-id X = refl

narrow-⇑ᵗ-ᶜ≤ :
  ∀ {Δ Δ′ Σ c A B} →
  suc Δ ≤ Δ′ →
  Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B →
  Δ′ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ᶜ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ-ᶜ≤ Δ≤ c⊒ =
  narrow-renameᵗ (TyRenameWf-suc-≤ Δ≤) modeRename-suc-tag-or-id c⊒

narrow-⇑ᵗ-ᶜ :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ᶜ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ-ᶜ = narrow-⇑ᵗ-ᶜ≤ ≤-refl

narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤ :
  ∀ {Δ Δ′ σ c A B} →
  suc Δ ≤ Δ′ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ′ ∣ srcStoreⁿ (⇑ˢ σ) ⊢ ⇑ᶜ c ∶ᶜ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤ {σ = σ} Δ≤ c⊒ =
  subst
    (λ Σ₀ → _ ∣ Σ₀ ⊢ _ ∶ᶜ _ ⊒ _)
    (sym (srcStoreⁿ-⇑ˢ σ))
    (narrow-⇑ᵗ-ᶜ≤ Δ≤ c⊒)

narrow-⇑ᵗ-ᶜ-srcStoreⁿ :
  ∀ {Δ σ c A B} →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  suc Δ ∣ srcStoreⁿ (⇑ˢ σ) ⊢ ⇑ᶜ c ∶ᶜ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} =
  narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤ {σ = σ} ≤-refl

narrow-⇑ᵗ-open-srcStoreⁿ :
  ∀ {Δ σ α q p C D} →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  suc Δ ∣ srcStoreⁿ ((suc α ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ)
    ⊢ renameᶜ (extᵗ suc) p [ suc α ]ᶜ ∶ᶜ ⇑ᵗ C ⊒ ⇑ᵗ D
narrow-⇑ᵗ-open-srcStoreⁿ {σ = σ} {α = α} {q = q} {p = p} pαᶜ =
  subst
    (λ c₀ → _ ∣ srcStoreⁿ ((suc α ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ)
      ⊢ c₀ ∶ᶜ _ ⊒ _)
    (renameᶜ-open-commute suc p α)
    (narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤ {σ = (α ꞉ q) ∷ σ} ≤-refl pαᶜ)

narrow-⇑ᵗ-any :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ-any (μ , c⊒) = genᵈ μ , narrow-⇑ᵗ-gen c⊒

narrow-drop-star-var :
  ∀ X {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Δ ∣ (X , ★) ∷ Σ ⊢ c ∶ A ⊒ B
narrow-drop-star-var X (μ , c⊒) =
  μ , narrow-weaken ≤-refl StoreIncl-drop c⊒

narrow-drop-star :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Δ ∣ (zero , ★) ∷ Σ ⊢ c ∶ A ⊒ B
narrow-drop-star = narrow-drop-star-var zero

srcStoreⁿ-++ :
  ∀ ρ σ →
  srcStoreⁿ (ρ ++ σ) ≡ srcStoreⁿ ρ ++ srcStoreⁿ σ
srcStoreⁿ-++ [] σ = refl
srcStoreⁿ-++ ((X ꞉ p) ∷ ρ) σ =
  cong ((X , src p) ∷_) (srcStoreⁿ-++ ρ σ)
srcStoreⁿ-++ ((X ꞉= A ⊒) ∷ ρ) σ = srcStoreⁿ-++ ρ σ
srcStoreⁿ-++ ((⊒ X ꞉=☆) ∷ ρ) σ =
  cong ((X , ★) ∷_) (srcStoreⁿ-++ ρ σ)

⇑ˢ-++ :
  ∀ ρ σ →
  ⇑ˢ (ρ ++ σ) ≡ ⇑ˢ ρ ++ ⇑ˢ σ
⇑ˢ-++ [] σ = refl
⇑ˢ-++ (entry ∷ ρ) σ =
  cong (⇑ʷ entry ∷_) (⇑ˢ-++ ρ σ)

⊑ˢ-⇑ˢ :
  ∀ {Δ σ Σ Σ′} →
  Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′ →
  suc Δ ⊢ ⇑ˢ σ ꞉ ⟰ᵗ Σ ⊑ˢ ⟰ᵗ Σ′
⊑ˢ-⇑ˢ ⊑ˢ-nil = ⊑ˢ-nil
⊑ˢ-⇑ˢ (⊑ˢ-left hA σ⊑) =
  ⊑ˢ-left (renameᵗ-preserves-WfTy hA TyRenameWf-suc) (⊑ˢ-⇑ˢ σ⊑)
⊑ˢ-⇑ˢ (⊑ˢ-right σ⊑) =
  ⊑ˢ-right (⊑ˢ-⇑ˢ σ⊑)
⊑ˢ-⇑ˢ (⊑ˢ-both hA hA′ (μ , s⊑) σ⊑) =
  ⊑ˢ-both
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc)
    (instᵈ μ , widen-⇑ᵗ-inst s⊑)
    (⊑ˢ-⇑ˢ σ⊑)

⊒ˢ-⇑ˢ :
  ∀ {Δ σ Σ Σ′} →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  suc Δ ⊢ ⇑ˢ σ ꞉ ⟰ᵗ Σ ⊒ˢ ⟰ᵗ Σ′
⊒ˢ-⇑ˢ ⊒ˢ-nil = ⊒ˢ-nil
⊒ˢ-⇑ˢ (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right (renameᵗ-preserves-WfTy hA TyRenameWf-suc) (⊒ˢ-⇑ˢ σ⊒)
⊒ˢ-⇑ˢ (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (⊒ˢ-⇑ˢ σ⊒)
⊒ˢ-⇑ˢ (⊒ˢ-both hA hA′ (μ , s⊒) σ⊒) =
  ⊒ˢ-both
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc)
    (genᵈ μ , narrow-⇑ᵗ-gen s⊒)
    (⊒ˢ-⇑ˢ σ⊒)

⊒ˢ-empty-⇑ˢ :
  ∀ {Δ σ Σ} →
  Δ ⊢ σ ꞉ Σ ⊒ˢ [] →
  Δ ⊢ ⇑ˢ σ ꞉ ⟰ᵗ Σ ⊒ˢ []
⊒ˢ-empty-⇑ˢ ⊒ˢ-nil = ⊒ˢ-nil
⊒ˢ-empty-⇑ˢ (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (⊒ˢ-empty-⇑ˢ σ⊒)

⊒ˢ-empty-anyᵗ :
  ∀ Δ′ {Δ σ Σ} →
  Δ ⊢ σ ꞉ Σ ⊒ˢ [] →
  Δ′ ⊢ σ ꞉ Σ ⊒ˢ []
⊒ˢ-empty-anyᵗ Δ′ ⊒ˢ-nil = ⊒ˢ-nil
⊒ˢ-empty-anyᵗ Δ′ (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (⊒ˢ-empty-anyᵗ Δ′ σ⊒)

WfTyˢ-rename :
  ∀ {Δ Δ′ Σ A ρ} →
  TyRenameWf Δ Δ′ ρ →
  WfTyˢ Δ Σ A →
  WfTyˢ Δ′ (renameStoreᵗ ρ Σ) (renameᵗ ρ A)
WfTyˢ-rename hρ (wfVarᵗ X<Δ) = wfVarᵗ (hρ X<Δ)
WfTyˢ-rename hρ (wfVarˢ α∈Σ) = wfVarˢ (∈-renameStoreᵗ _ α∈Σ)
WfTyˢ-rename hρ wfBaseˢ = wfBaseˢ
WfTyˢ-rename hρ wf★ˢ = wf★ˢ
WfTyˢ-rename hρ (wf⇒ˢ hA hB) =
  wf⇒ˢ (WfTyˢ-rename hρ hA) (WfTyˢ-rename hρ hB)
WfTyˢ-rename {Σ = Σ} {ρ = ρ} hρ (wf∀ˢ hA) =
  wf∀ˢ
    (subst (λ Σ′ → WfTyˢ _ Σ′ _) (renameStoreᵗ-ext-suc-comm ρ Σ)
      (WfTyˢ-rename (TyRenameWf-ext hρ) hA))

WfTyˢ-⇑ᵗ :
  ∀ {Δ Σ A} →
  WfTyˢ Δ Σ A →
  WfTyˢ (suc Δ) (⟰ᵗ Σ) (⇑ᵗ A)
WfTyˢ-⇑ᵗ = WfTyˢ-rename TyRenameWf-suc

WfTyˢ-store-weaken :
  ∀ {Δ Σ Σ′ A} →
  StoreIncl Σ Σ′ →
  WfTyˢ Δ Σ A →
  WfTyˢ Δ Σ′ A
WfTyˢ-store-weaken incl (wfVarᵗ X<Δ) = wfVarᵗ X<Δ
WfTyˢ-store-weaken incl (wfVarˢ α∈Σ) = wfVarˢ (incl α∈Σ)
WfTyˢ-store-weaken incl wfBaseˢ = wfBaseˢ
WfTyˢ-store-weaken incl wf★ˢ = wf★ˢ
WfTyˢ-store-weaken incl (wf⇒ˢ hA hB) =
  wf⇒ˢ (WfTyˢ-store-weaken incl hA) (WfTyˢ-store-weaken incl hB)
WfTyˢ-store-weaken incl (wf∀ˢ hA) =
  wf∀ˢ (WfTyˢ-store-weaken (renameStoreᵗ-incl suc incl) hA)

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
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
narrowing⇒coercion (μ , c⊢) =
  μ , narrowing⇒coercionᵐ c⊢

widening⇒coercion :
  ∀ {Δ Σ A B c} →
  (∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B) →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
widening⇒coercion (μ , c⊢) =
  μ , widening⇒coercionᵐ c⊢

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
      (cast-id hA id-ok , cross (id-＇ _)) =
    <-irrefl refl α<α
  narrowing-var-to-older⊥ wfΣ wfBase
      (() , cross (id-‵ _))
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ wfBase
      (c⊢ , cross ())
  narrowing-var-to-older⊥ {c = G !} wfΣ wf★
      (c⊢ , cross ())
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ wf★
      (c⊢ , cross ())
  narrowing-var-to-older⊥ wfΣ (wf⇒ hB hC)
      (() , cross (_↦_ sʷ tⁿ))
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ (wf⇒ hB hC)
      (c⊢ , cross ())
  narrowing-var-to-older⊥ wfΣ (wf∀ hB)
      (cast-gen hA occ s⊢ , gen sᵍ) =
    narrowing-var-to-older⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      hB
      (s⊢ , genSafe→narrowing sᵍ)
  narrowing-var-to-older⊥ {c = unseal β A} wfΣ (wf∀ hB)
      (c⊢ , cross ())
  narrowing-var-to-older⊥ wfΣ hB
      (cast-seq () s⊢ , _？︔_ gG′ sⁿ)
  narrowing-var-to-older⊥ wfΣ hB
      (cast-seq () s⊢ , fun-untag-gen sᵍ)
  narrowing-var-to-older⊥ {α = α} wfΣ (wfVar β<α)
      (cast-seal {α = β} hA β∈Σ seal-ok , sealⁿ _ _) with
      wfOlder wfΣ β∈Σ
  narrowing-var-to-older⊥ {α = α} wfΣ (wfVar β<α)
      (cast-seal {α = β} hA β∈Σ seal-ok , sealⁿ _ _) |
      wfVar α<β =
    <-irrefl refl (≤-trans α<β (≤-trans (n≤1+n β) β<α))
  narrowing-var-to-older⊥ wfΣ (wfVar β<α)
      (cast-seq s⊢ (cast-seal hA β∈Σ seal-ok) , sⁿ ︔seal _) =
    narrowing-var-to-older⊥
      wfΣ
      (WfTy-weakenᵗ (wfOlder wfΣ β∈Σ) (≤-from-< β<α))
      (s⊢ , strictⁿ→narrow sⁿ)

  widening-older-to-var⊥ :
    ∀ {μ Δ Σ c α A} →
    StoreDetWf Δ Σ →
    WfTy α A →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ (＇ α) →
    ⊥
  widening-older-to-var⊥ wfΣ (wfVar α<α)
      (cast-id hA id-ok , cross (id-＇ _)) =
    <-irrefl refl α<α
  widening-older-to-var⊥ wfΣ wfBase
      (() , cross (id-‵ _))
  widening-older-to-var⊥ {c = seal A β} wfΣ wfBase
      (c⊢ , cross ())
  widening-older-to-var⊥ {c = G ？} wfΣ wf★
      (c⊢ , cross ())
  widening-older-to-var⊥ {c = seal A β} wfΣ wf★
      (c⊢ , cross ())
  widening-older-to-var⊥ wfΣ (wf⇒ hA hB)
      (() , cross (_↦_ sⁿ tʷ))
  widening-older-to-var⊥ {c = seal A β} wfΣ (wf⇒ hA hB)
      (c⊢ , cross ())
  widening-older-to-var⊥ wfΣ (wf∀ hA)
      (cast-inst hB occ s⊢ , inst sᵍ) =
    widening-older-to-var⊥
      (StoreDetWf-inst wfΣ)
      hA
      (s⊢ , instSafe→widening sᵍ)
  widening-older-to-var⊥ {c = seal A β} wfΣ (wf∀ hA)
      (c⊢ , cross ())
  widening-older-to-var⊥ wfΣ hA
      (cast-seq s⊢ () , ((sʷ ︔ gG′ !)))
  widening-older-to-var⊥ wfΣ hA
      (cast-seq s⊢ () , inst-fun-tag sᵍ)
  widening-older-to-var⊥ {α = α} wfΣ (wfVar β<α)
      (cast-unseal {α = β} hA β∈Σ seal-ok , unsealʷ _ _) with
      wfOlder wfΣ β∈Σ
  widening-older-to-var⊥ {α = α} wfΣ (wfVar β<α)
      (cast-unseal {α = β} hA β∈Σ seal-ok , unsealʷ _ _) |
      wfVar α<β =
    <-irrefl refl (≤-trans α<β (≤-trans (n≤1+n β) β<α))
  widening-older-to-var⊥ wfΣ (wfVar β<α)
      (cast-seq (cast-unseal hA β∈Σ seal-ok) s⊢ , unseal︔_ _ sʷ) =
    widening-older-to-var⊥
      wfΣ
      (WfTy-weakenᵗ (wfOlder wfΣ β∈Σ) (≤-from-< β<α))
      (s⊢ , strictʷ→widen sʷ)

------------------------------------------------------------------------
-- Endpoint exclusions used by the expanded determinacy proof
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

star≢all : ∀ {B : Ty} → ★ ≢ `∀ B
star≢all ()

star≢var : ∀ {α : TyVar} → ★ ≢ ＇ α
star≢var {α = α} eq with ★ ≟Ty ＇ α
star≢var {α = α} eq | no neq = neq eq
star≢var {α = α} eq | yes ()

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
  ∀ {μ : ModeEnv} {α : TyVar} {G : Ty} →
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
  ∀ {μ : ModeEnv} {α β : TyVar} →
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
  narrowing-target-path-id-only α-id (c⊢ , cross cⁿ) occ =
    narrowing-cross-target-path-id-only α-id (c⊢ , cⁿ) occ
  narrowing-target-path-id-only α-id (cast-id wf★ ok , id★) ()
  narrowing-target-path-id-only {α = α} α-id
      (cast-gen {A = A} hA occB c⊢ , gen cᵍ) (occ-all occ) =
    np-gen
      (narrowing-target-path-id-only {α = suc α} α-id
        (c⊢ , genSafe→narrowing cᵍ) occ)
  narrowing-target-path-id-only α-id
      (cast-untag hG gG tag-ok , untag gG′)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok (Occurs→occurs-true occ))
  narrowing-target-path-id-only α-id
      (cast-seq (cast-untag hG gG tag-ok) c⊢ , _？︔_ gG′ cⁿ)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (narrowing-cross-target-id-only
          α-id (c⊢ , strictCrossⁿ→cross cⁿ)
          (Occurs→occurs-true occ)))
  narrowing-target-path-id-only α-id
      (cast-seq (cast-untag hG ★⇒★ tag-ok)
                (cast-gen hA occB c⊢) ,
       fun-untag-gen cᵍ)
      occ =
    ⊥-elim
      (false≢true
        (narrowing-target-id-only
          α-id
          (cast-seq (cast-untag hG ★⇒★ tag-ok)
                    (cast-gen hA occB c⊢) ,
           fun-untag-gen cᵍ)
          (Occurs→occurs-true occ)))
  narrowing-target-path-id-only α-id
      (cast-seal hA β∈Σ seal-ok , sealⁿ A β)
      occ =
    ⊥-elim
      (id-only-seal-var-occurs⊥
        α-id seal-ok (Occurs→occurs-true occ))
  narrowing-target-path-id-only α-id
      (cast-seq c⊢ (cast-seal {α = β} hA β∈Σ seal-ok) ,
       cⁿ ︔seal _)
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
      (cast-id {A = ＇ β} hA id-ok , id-＇ _) occ-var =
    np-var
  narrowing-cross-target-path-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , id-‵ _) ()
  narrowing-cross-target-path-id-only α-id
      (cast-fun s⊢ t⊢ , _↦_ sʷ tⁿ) (occ-fun₁ occ) =
    np-fun₁ (widening-source-path-id-only α-id (s⊢ , sʷ) occ)
  narrowing-cross-target-path-id-only α-id
      (cast-fun s⊢ t⊢ , _↦_ sʷ tⁿ) (occ-fun₂ occ) =
    np-fun₂ (narrowing-target-path-id-only α-id (t⊢ , tⁿ) occ)
  narrowing-cross-target-path-id-only {α = α} α-id
      (cast-all c⊢ , `∀ cⁿ) (occ-all occ) =
    np-all
      (narrowing-target-path-id-only {α = suc α} α-id (c⊢ , cⁿ) occ)

  widening-source-path-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Occurs α A →
    WidenPath α A B
  widening-source-path-id-only α-id (c⊢ , cross cʷ) occ =
    widening-cross-source-path-id-only α-id (c⊢ , cʷ) occ
  widening-source-path-id-only α-id (cast-id wf★ ok , id★) ()
  widening-source-path-id-only {α = α} α-id
      (cast-inst {B = B} hB occA c⊢ , inst cᵍ) (occ-all occ) =
    wp-inst
      (widening-source-path-id-only {α = suc α} α-id
        (c⊢ , instSafe→widening cᵍ) occ)
  widening-source-path-id-only α-id
      (cast-tag hG gG tag-ok , tag gG′)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok (Occurs→occurs-true occ))
  widening-source-path-id-only α-id
      (cast-seq c⊢ (cast-tag hG gG tag-ok) , ((cʷ ︔ gG′ !)))
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (widening-cross-source-id-only
          α-id (c⊢ , strictCrossʷ→cross cʷ)
          (Occurs→occurs-true occ)))
  widening-source-path-id-only α-id
      (cast-seq (cast-inst hB occA c⊢)
                (cast-tag hG ★⇒★ tag-ok) ,
       inst-fun-tag cᵍ)
      occ =
    ⊥-elim
      (false≢true
        (widening-source-id-only
          α-id
          (cast-seq (cast-inst hB occA c⊢)
                    (cast-tag hG ★⇒★ tag-ok) ,
           inst-fun-tag cᵍ)
          (Occurs→occurs-true occ)))
  widening-source-path-id-only α-id
      (cast-unseal hA β∈Σ seal-ok , unsealʷ β A)
      occ =
    ⊥-elim
      (id-only-seal-var-occurs⊥
        α-id seal-ok (Occurs→occurs-true occ))
  widening-source-path-id-only α-id
      (cast-seq (cast-unseal {α = β} hA β∈Σ seal-ok) c⊢ ,
       unseal︔_ _ cʷ)
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
      (cast-id {A = ＇ β} hA id-ok , id-＇ _) occ-var =
    wp-var
  widening-cross-source-path-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , id-‵ _) ()
  widening-cross-source-path-id-only α-id
      (cast-fun s⊢ t⊢ , _↦_ sⁿ tʷ) (occ-fun₁ occ) =
    wp-fun₁ (narrowing-target-path-id-only α-id (s⊢ , sⁿ) occ)
  widening-cross-source-path-id-only α-id
      (cast-fun s⊢ t⊢ , _↦_ sⁿ tʷ) (occ-fun₂ occ) =
    wp-fun₂ (widening-source-path-id-only α-id (t⊢ , tʷ) occ)
  widening-cross-source-path-id-only {α = α} α-id
      (cast-all c⊢ , `∀ cʷ) (occ-all occ) =
    wp-all
      (widening-source-path-id-only {α = suc α} α-id (c⊢ , cʷ) occ)

  narrowing-target-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    occurs α B ≡ true →
    occurs α A ≡ true
  narrowing-target-id-only α-id (c⊢ , cross cⁿ) occ =
    narrowing-cross-target-id-only α-id (c⊢ , cⁿ) occ
  narrowing-target-id-only α-id (cast-id wf★ ok , id★) ()
  narrowing-target-id-only {α = α} α-id
      (cast-gen {A = A} hA occB c⊢ , gen cᵍ) occ =
    trans
      (sym (occurs-raise zero α A))
      (narrowing-target-id-only {α = suc α} α-id
        (c⊢ , genSafe→narrowing cᵍ) occ)
  narrowing-target-id-only α-id
      (cast-untag hG gG tag-ok , untag gG′)
      occ =
    ⊥-elim (id-only-ground-tag-occurs⊥ α-id gG tag-ok occ)
  narrowing-target-id-only α-id
      (cast-seq (cast-untag hG gG tag-ok) c⊢ , _？︔_ gG′ cⁿ)
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (narrowing-cross-target-id-only
          α-id (c⊢ , strictCrossⁿ→cross cⁿ) occ))
  narrowing-target-id-only {α = α} α-id
      (cast-seq (cast-untag hG ★⇒★ tag-ok)
                (cast-gen hA occB c⊢) ,
       fun-untag-gen cᵍ)
      occ =
    ⊥-elim
      (false≢true
        (narrowing-target-id-only {α = suc α} α-id
          (c⊢ , genSafe→narrowing cᵍ) occ))
  narrowing-target-id-only α-id
      (cast-seal hA β∈Σ seal-ok , sealⁿ A β)
      occ =
    ⊥-elim (id-only-seal-var-occurs⊥ α-id seal-ok occ)
  narrowing-target-id-only α-id
      (cast-seq c⊢ (cast-seal {α = β} hA β∈Σ seal-ok) , cⁿ ︔seal _)
      occ =
    ⊥-elim (id-only-seal-var-occurs⊥ α-id seal-ok occ)

  narrowing-cross-target-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossNarrowing c →
    occurs α B ≡ true →
    occurs α A ≡ true
  narrowing-cross-target-id-only α-id
      (cast-id {A = ＇ β} hA id-ok , id-＇ _) occ =
    occ
  narrowing-cross-target-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , id-‵ _) ()
  narrowing-cross-target-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       _↦_ sʷ tⁿ)
      occ
      with occurs α A′ | inspect (occurs α) A′
  narrowing-cross-target-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       _↦_ sʷ tⁿ)
      occ | true | [ eqA′ ]
      rewrite widening-source-id-only α-id (s⊢ , sʷ) eqA′ =
    refl
  narrowing-cross-target-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       _↦_ sʷ tⁿ)
      occ | false | [ eqA′ ]
      rewrite narrowing-target-id-only α-id (t⊢ , tⁿ) occ =
    ∨-trueʳ (occurs α A)
  narrowing-cross-target-id-only {α = α} α-id
      (cast-all c⊢ , `∀ cⁿ) occ =
    narrowing-target-id-only {α = suc α} α-id (c⊢ , cⁿ) occ

  widening-source-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    occurs α A ≡ true →
    occurs α B ≡ true
  widening-source-id-only α-id (c⊢ , cross cʷ) occ =
    widening-cross-source-id-only α-id (c⊢ , cʷ) occ
  widening-source-id-only α-id (cast-id wf★ ok , id★) ()
  widening-source-id-only {α = α} α-id
      (cast-inst {B = B} hB occA c⊢ , inst cᵍ) occ =
    trans
      (sym (occurs-raise zero α B))
      (widening-source-id-only {α = suc α} α-id
        (c⊢ , instSafe→widening cᵍ) occ)
  widening-source-id-only α-id
      (cast-tag hG gG tag-ok , tag gG′)
      occ =
    ⊥-elim (id-only-ground-tag-occurs⊥ α-id gG tag-ok occ)
  widening-source-id-only α-id
      (cast-seq c⊢ (cast-tag hG gG tag-ok) , ((cʷ ︔ gG′ !)))
      occ =
    ⊥-elim
      (id-only-ground-tag-occurs⊥
        α-id gG tag-ok
        (widening-cross-source-id-only
          α-id (c⊢ , strictCrossʷ→cross cʷ) occ))
  widening-source-id-only {α = α} α-id
      (cast-seq (cast-inst hB occA c⊢)
                (cast-tag hG ★⇒★ tag-ok) ,
       inst-fun-tag cᵍ)
      occ =
    ⊥-elim
      (false≢true
        (widening-source-id-only {α = suc α} α-id
          (c⊢ , instSafe→widening cᵍ) occ))
  widening-source-id-only α-id
      (cast-unseal hA β∈Σ seal-ok , unsealʷ β A)
      occ =
    ⊥-elim (id-only-seal-var-occurs⊥ α-id seal-ok occ)
  widening-source-id-only α-id
      (cast-seq (cast-unseal {α = β} hA β∈Σ seal-ok) c⊢ ,
       unseal︔_ _ cʷ)
      occ =
    ⊥-elim (id-only-seal-var-occurs⊥ α-id seal-ok occ)

  widening-cross-source-id-only :
    ∀ {μ Δ Σ c A B α} →
    μ α ≡ id-only →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossWidening c →
    occurs α A ≡ true →
    occurs α B ≡ true
  widening-cross-source-id-only α-id
      (cast-id {A = ＇ β} hA id-ok , id-＇ _) occ =
    occ
  widening-cross-source-id-only α-id
      (cast-id {A = ‵ ι} hA id-ok , id-‵ _) ()
  widening-cross-source-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       _↦_ sⁿ tʷ)
      occ
      with occurs α A | inspect (occurs α) A
  widening-cross-source-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       _↦_ sⁿ tʷ)
      occ | true | [ eqA ]
      rewrite narrowing-target-id-only α-id (s⊢ , sⁿ) eqA =
    refl
  widening-cross-source-id-only {α = α} α-id
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′} s⊢ t⊢ ,
       _↦_ sⁿ tʷ)
      occ | false | [ eqA ]
      rewrite widening-source-id-only α-id (t⊢ , tʷ) occ =
    ∨-trueʳ (occurs α A′)
  widening-cross-source-id-only {α = α} α-id
      (cast-all c⊢ , `∀ cʷ) occ =
    widening-source-id-only {α = suc α} α-id (c⊢ , cʷ) occ

narrowing-cross-ground-target-star⊥ :
  ∀ {μ Δ Σ G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ ★) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-star⊥ (＇ α)
    (() , id-＇ _)
narrowing-cross-ground-target-star⊥ (‵ ι)
    (() , id-‵ _)
narrowing-cross-ground-target-star⊥ ★⇒★
    (() , _↦_ sʷ tⁿ)
narrowing-cross-ground-target-star⊥ gG
    (() , `∀ gⁿ)

widening-cross-ground-source-star⊥ :
  ∀ {μ Δ Σ G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ ★ =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-star⊥ (＇ α)
    (() , id-＇ _)
widening-cross-ground-source-star⊥ (‵ ι)
    (() , id-‵ _)
widening-cross-ground-source-star⊥ ★⇒★
    (() , _↦_ sⁿ tʷ)
widening-cross-ground-source-star⊥ gG
    (() , `∀ gʷ)

narrowing-target-star-source-star :
  ∀ {μ Δ Σ c A} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ ★ →
  A ≡ ★
narrowing-target-star-source-star (() , cross (id-＇ _))
narrowing-target-star-source-star (() , cross (id-‵ _))
narrowing-target-star-source-star (() , cross (_↦_ sʷ tⁿ))
narrowing-target-star-source-star (() , cross (`∀ cⁿ))
narrowing-target-star-source-star (cast-id hA ok , id★) = refl
narrowing-target-star-source-star
    (cast-seq (cast-untag hG gG okG) c⊢ , _？︔_ gG′ cⁿ) =
  ⊥-elim
    (narrowing-cross-ground-target-star⊥
      gG (c⊢ , strictCrossⁿ→cross cⁿ))
narrowing-target-star-source-star
    (cast-seq c⊢ () , cⁿ ︔seal _)

widening-source-star-target-star :
  ∀ {μ Δ Σ c B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊑ B →
  B ≡ ★
widening-source-star-target-star (() , cross (id-＇ _))
widening-source-star-target-star (() , cross (id-‵ _))
widening-source-star-target-star (() , cross (_↦_ sⁿ tʷ))
widening-source-star-target-star (() , cross (`∀ cʷ))
widening-source-star-target-star (cast-id hA ok , id★) = refl
widening-source-star-target-star
    (cast-seq c⊢ (cast-tag hG gG okG) , ((cʷ ︔ gG′ !))) =
  ⊥-elim
    (widening-cross-ground-source-star⊥
      gG (c⊢ , strictCrossʷ→cross cʷ))
widening-source-star-target-star
    (cast-seq () c⊢ , unseal︔_ _ cʷ)

narrowing-cross-var-source-target :
  ∀ {μ Δ Σ α B g} →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (＇ α) =⇒ B) × CrossNarrowing g →
  B ≡ ＇ α
narrowing-cross-var-source-target (cast-id hA ok , id-＇ _) = refl

widening-cross-var-target-source :
  ∀ {μ Δ Σ α A g} →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ A =⇒ (＇ α)) × CrossWidening g →
  A ≡ ＇ α
widening-cross-var-target-source (cast-id hA ok , id-＇ _) = refl

mutual
  dualStrictCrossNarrowing-raw :
    ∀ η {c} →
    (g : StrictCrossNarrowing c) →
    proj₁ (dualCrossNarrowing η (strictCrossⁿ→cross g)) ≡
    proj₁ (dualStrictCrossNarrowing η g)
  dualStrictCrossNarrowing-raw η (cn-funˡ sʷ tⁿ) =
    cong₂ _↦_ (dualStrictʷ-raw η sʷ) refl
  dualStrictCrossNarrowing-raw η (cn-funʳ sʷ tⁿ) =
    cong₂ _↦_ refl (dualStrictⁿ-raw η tⁿ)
  dualStrictCrossNarrowing-raw η (cn-all sⁿ) =
    cong `∀ (dualStrictⁿ-raw (extᵃ η) sⁿ)

  dualStrictⁿ-raw :
    ∀ η {c} →
    (s : StrictNarrowing c) →
    proj₁ (dualⁿ η (strictⁿ→narrow s)) ≡
    proj₁ (dualStrictⁿ η s)
  dualStrictⁿ-raw η (strict-crossⁿ gⁿ) =
    dualStrictCrossNarrowing-raw η gⁿ
  dualStrictⁿ-raw η (strict-gen sⁿ) = refl
  dualStrictⁿ-raw η (strict-untag (＇ α)) with η α
  dualStrictⁿ-raw η (strict-untag (＇ α)) | normal = refl
  dualStrictⁿ-raw η (strict-untag (＇ α)) | tag-to-seal = refl
  dualStrictⁿ-raw η (strict-untag (＇ α)) | seal-to-tag = refl
  dualStrictⁿ-raw η (strict-untag (‵ ι)) = refl
  dualStrictⁿ-raw η (strict-untag ★⇒★) = refl
  dualStrictⁿ-raw η (strict-untag-seq (＇ α) gⁿ) with η α
  dualStrictⁿ-raw η (strict-untag-seq (＇ α) gⁿ) | normal = refl
  dualStrictⁿ-raw η (strict-untag-seq (＇ α) gⁿ) | tag-to-seal = refl
  dualStrictⁿ-raw η (strict-untag-seq (＇ α) gⁿ) | seal-to-tag = refl
  dualStrictⁿ-raw η (strict-untag-seq (‵ ι) gⁿ) = refl
  dualStrictⁿ-raw η (strict-untag-seq ★⇒★ gⁿ) = refl
  dualStrictⁿ-raw η (strict-fun-untag-gen sᵍ) = refl
  dualStrictⁿ-raw η (strict-seal A α) with η α
  dualStrictⁿ-raw η (strict-seal A α) | normal = refl
  dualStrictⁿ-raw η (strict-seal A α) | tag-to-seal = refl
  dualStrictⁿ-raw η (strict-seal A α) | seal-to-tag = refl
  dualStrictⁿ-raw η (strict-seal-seq {A = A} sⁿ α) with η α
  dualStrictⁿ-raw η (strict-seal-seq {A = A} sⁿ α) | normal = refl
  dualStrictⁿ-raw η (strict-seal-seq {A = A} sⁿ α) | tag-to-seal = refl
  dualStrictⁿ-raw η (strict-seal-seq {A = A} sⁿ α) | seal-to-tag = refl

  dualStrictCrossWidening-raw :
    ∀ η {c} →
    (g : StrictCrossWidening c) →
    proj₁ (dualCrossWidening η (strictCrossʷ→cross g)) ≡
    proj₁ (dualStrictCrossWidening η g)
  dualStrictCrossWidening-raw η (cw-funˡ sⁿ tʷ) =
    cong₂ _↦_ (dualStrictⁿ-raw η sⁿ) refl
  dualStrictCrossWidening-raw η (cw-funʳ sⁿ tʷ) =
    cong₂ _↦_ refl (dualStrictʷ-raw η tʷ)
  dualStrictCrossWidening-raw η (cw-all sʷ) =
    cong `∀ (dualStrictʷ-raw (extᵃ η) sʷ)

  dualStrictʷ-raw :
    ∀ η {c} →
    (s : StrictWidening c) →
    proj₁ (dualʷ η (strictʷ→widen s)) ≡
    proj₁ (dualStrictʷ η s)
  dualStrictʷ-raw η (strict-crossʷ gʷ) =
    dualStrictCrossWidening-raw η gʷ
  dualStrictʷ-raw η (strict-inst sʷ) = refl
  dualStrictʷ-raw η (strict-tag (＇ α)) with η α
  dualStrictʷ-raw η (strict-tag (＇ α)) | normal = refl
  dualStrictʷ-raw η (strict-tag (＇ α)) | tag-to-seal = refl
  dualStrictʷ-raw η (strict-tag (＇ α)) | seal-to-tag = refl
  dualStrictʷ-raw η (strict-tag (‵ ι)) = refl
  dualStrictʷ-raw η (strict-tag ★⇒★) = refl
  dualStrictʷ-raw η (strict-tag-seq gʷ (＇ α)) with η α
  dualStrictʷ-raw η (strict-tag-seq gʷ (＇ α)) | normal = refl
  dualStrictʷ-raw η (strict-tag-seq gʷ (＇ α)) | tag-to-seal = refl
  dualStrictʷ-raw η (strict-tag-seq gʷ (＇ α)) | seal-to-tag = refl
  dualStrictʷ-raw η (strict-tag-seq gʷ (‵ ι)) = refl
  dualStrictʷ-raw η (strict-tag-seq gʷ ★⇒★) = refl
  dualStrictʷ-raw η (strict-inst-fun-tag sᵍ) = refl
  dualStrictʷ-raw η (strict-unseal α A) with η α
  dualStrictʷ-raw η (strict-unseal α A) | normal = refl
  dualStrictʷ-raw η (strict-unseal α A) | tag-to-seal = refl
  dualStrictʷ-raw η (strict-unseal α A) | seal-to-tag = refl
  dualStrictʷ-raw η (strict-unseal-seq α {A = A} sʷ) with η α
  dualStrictʷ-raw η (strict-unseal-seq α {A = A} sʷ) | normal = refl
  dualStrictʷ-raw η (strict-unseal-seq α {A = A} sʷ) | tag-to-seal = refl
  dualStrictʷ-raw η (strict-unseal-seq α {A = A} sʷ) | seal-to-tag = refl

------------------------------------------------------------------------
-- Grammar duality flips well-typed narrowing/widening endpoints
------------------------------------------------------------------------

mutual
  dualCrossNarrowing-flips-coercionᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossNarrowing c) →
    ν ∣ Δ ∣ Π ⊢ proj₁ (dualCrossNarrowing η (proj₂ p)) ∶ B =⇒ A
  dualCrossNarrowing-flips-coercionᵐ rel ds wfΣ
      (cast-id {A = ＇ α} hA ok , id-＇ .α) =
    cast-id {A = ＇ α} hA
      (dualActionOk-idTyAllowed {A = ＇ α} rel ok)
  dualCrossNarrowing-flips-coercionᵐ rel ds wfΣ
      (cast-id {A = ‵ ι} hA ok , id-‵ .ι) =
    cast-id {A = ‵ ι} hA
      (dualActionOk-idTyAllowed {A = ‵ ι} rel ok)
  dualCrossNarrowing-flips-coercionᵐ rel ds wfΣ
      (cast-fun s⊢ t⊢ , _↦_ sʷ tⁿ) =
    cast-fun
      (proj₁ (dualʷ-flips-typingᵐ rel ds wfΣ (s⊢ , sʷ)))
      (proj₁ (dualⁿ-flips-typingᵐ rel ds wfΣ (t⊢ , tⁿ)))
  dualCrossNarrowing-flips-coercionᵐ rel ds wfΣ
      (cast-all c⊢ , `∀ cⁿ) =
    cast-all
      (proj₁
        (dualⁿ-flips-typingᵐ
          (dualActionOk-ext rel)
          (dualStoreAt-ext ds)
          (StoreWfAt-⟰ᵗ wfΣ)
          (c⊢ , cⁿ)))

  dualStrictCrossNarrowing-flips-coercionᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × StrictCrossNarrowing c) →
    ν ∣ Δ ∣ Π ⊢ proj₁ (dualStrictCrossNarrowing η (proj₂ p)) ∶ B =⇒ A
  dualStrictCrossNarrowing-flips-coercionᵐ
      {η = η} {ν = ν} {Δ = Δ} {Π = Π} {A = A} {B = B}
      rel ds wfΣ (c⊢ , cⁿ) =
    subst
      (λ d → ν ∣ Δ ∣ Π ⊢ d ∶ B =⇒ A)
      (dualStrictCrossNarrowing-raw η cⁿ)
      (dualCrossNarrowing-flips-coercionᵐ
        rel ds wfΣ (c⊢ , strictCrossⁿ→cross cⁿ))

  dualⁿ-flips-typingᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B) →
    ν ∣ Δ ∣ Π ⊢ proj₁ (dualⁿ η (proj₂ p)) ∶ B ⊑ A
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (c⊢ , cross cⁿ) =
    dualCrossNarrowing-flips-coercionᵐ rel ds wfΣ (c⊢ , cⁿ) ,
    cross (proj₂ (dualCrossNarrowing η cⁿ))
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-id {A = ★} hA ok , id★) =
    cast-id {A = ★} hA
      (dualActionOk-idTyAllowed {A = ★} rel ok) ,
    id★
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-gen hA occ c⊢ , gen cᵍ) =
    cast-inst hA occ
      (subst
        (λ d → _ ∣ _ ∣ _ ⊢ d ∶ _ =⇒ _)
        (sym (instSafeⁿ-raw (genᵃ η) cᵍ))
        (proj₁
          (dualⁿ-flips-typingᵐ
            (dualActionOk-gen-inst rel)
            (dualStoreAt-gen-inst ds)
            (StoreWfAt-⟰ᵗ wfΣ)
            (c⊢ , genSafe→narrowing cᵍ)))) ,
    inst (proj₂ (instSafeⁿ (genᵃ η) cᵍ))
  dualⁿ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-untag (wfVar α<Δ) (＇ α) ok , untag (＇ .α))
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-untag (wfVar α<Δ) (＇ α) ok , untag (＇ .α))
      | id-only | normal | id-only | dma-id | ()
  dualⁿ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-untag (wfVar α<Δ) (＇ α) ok , untag (＇ .α))
      | tag-or-id | normal | tag-or-id | dma-tag | refl =
    cast-tag (wfVar α<Δ) (＇ α)
      (tagModeAllowed-var-tag {ν = ν} {α = α} να) ,
    tag (＇ α)
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-untag (wfVar α<Δ) (＇ α) ok , untag (＇ .α))
      | seal-or-id | normal | seal-or-id | dma-seal | ()
  dualⁿ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-untag (wfVar α<Δ) (＇ α) ok , untag (＇ .α))
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl =
    cast-unseal {μ = ν} wf★
      (CoercionProof.DualStoreAt.tag★∈ ds α<Δ ηα)
      (sealModeAllowed-var-seal {ν = ν} {α = α} να) ,
    unsealʷ α ★
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-untag (wfVar α<Δ) (＇ α) ok , untag (＇ .α))
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | ()
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-untag hG (‵ ι) ok , untag (‵ .ι)) =
    cast-tag hG (‵ ι) refl , tag (‵ ι)
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-untag hG ★⇒★ ok , untag ★⇒★) =
    cast-tag hG ★⇒★ refl , tag ★⇒★
  dualⁿ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-seq (cast-untag (wfVar α<Δ) (＇ α) ok) g⊢ ,
       _？︔_ (＇ .α) gⁿ)
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seq (cast-untag (wfVar α<Δ) (＇ α) ok) g⊢ ,
       _？︔_ (＇ .α) gⁿ)
      | id-only | normal | id-only | dma-id | ()
  dualⁿ-flips-typingᵐ {η = η} {ν = ν} rel ds wfΣ
      (cast-seq (cast-untag (wfVar α<Δ) (＇ α) ok) g⊢ ,
       _？︔_ (＇ .α) gⁿ)
      | tag-or-id | normal | tag-or-id | dma-tag | refl =
    cast-seq
      (dualStrictCrossNarrowing-flips-coercionᵐ
        rel ds wfΣ (g⊢ , gⁿ))
      (cast-tag (wfVar α<Δ) (＇ α)
        (tagModeAllowed-var-tag {ν = ν} {α = α} να)) ,
    (proj₂ (dualStrictCrossNarrowing η gⁿ) ︔ (＇ α) !)
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seq (cast-untag (wfVar α<Δ) (＇ α) ok) g⊢ ,
       _？︔_ (＇ .α) gⁿ)
      | seal-or-id | normal | seal-or-id | dma-seal | ()
  dualⁿ-flips-typingᵐ {η = η} {ν = ν} rel ds wfΣ
      (cast-seq (cast-untag (wfVar α<Δ) (＇ α) ok) g⊢ ,
       _？︔_ (＇ .α) gⁿ)
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl
      rewrite narrowing-cross-var-source-target
                (g⊢ , strictCrossⁿ→cross gⁿ) =
    cast-unseal {μ = ν} wf★
      (CoercionProof.DualStoreAt.tag★∈ ds α<Δ ηα)
      (sealModeAllowed-var-seal {ν = ν} {α = α} να) ,
    unsealʷ α ★
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seq (cast-untag (wfVar α<Δ) (＇ α) ok) g⊢ ,
       _？︔_ (＇ .α) gⁿ)
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | ()
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-seq (cast-untag hG (‵ ι) ok) g⊢ ,
       _？︔_ (‵ .ι) gⁿ) =
    cast-seq
      (dualStrictCrossNarrowing-flips-coercionᵐ
        rel ds wfΣ (g⊢ , gⁿ))
      (cast-tag hG (‵ ι) refl) ,
    (proj₂ (dualStrictCrossNarrowing η gⁿ) ︔ (‵ ι) !)
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-seq (cast-untag hG ★⇒★ ok) g⊢ ,
       _？︔_ ★⇒★ gⁿ) =
    cast-seq
      (dualStrictCrossNarrowing-flips-coercionᵐ
        rel ds wfΣ (g⊢ , gⁿ))
      (cast-tag hG ★⇒★ refl) ,
    (proj₂ (dualStrictCrossNarrowing η gⁿ) ︔ ★⇒★ !)
  dualⁿ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-seq (cast-untag hG ★⇒★ ok)
                (cast-gen hA occ c⊢) ,
       fun-untag-gen cᵍ) =
    cast-seq
      (cast-inst hA occ
        (subst
          (λ d → _ ∣ _ ∣ _ ⊢ d ∶ _ =⇒ _)
          (sym (instSafeⁿ-raw (genᵃ η) cᵍ))
          (proj₁
            (dualⁿ-flips-typingᵐ
              (dualActionOk-gen-inst rel)
              (dualStoreAt-gen-inst ds)
              (StoreWfAt-⟰ᵗ wfΣ)
              (c⊢ , genSafe→narrowing cᵍ)))))
      (cast-tag hG ★⇒★ refl) ,
    inst-fun-tag (proj₂ (instSafeⁿ (genᵃ η) cᵍ))
  dualⁿ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-seal {α = α} hA αA∈Σ ok , sealⁿ A .α)
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seal hA αA∈Σ ok , sealⁿ A α)
      | id-only | normal | id-only | dma-id | ()
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seal hA αA∈Σ ok , sealⁿ A α)
      | tag-or-id | normal | tag-or-id | dma-tag | ()
  dualⁿ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-seal {α = α} hA αA∈Σ ok , sealⁿ A .α)
      | seal-or-id | normal | seal-or-id | dma-seal | refl =
    cast-unseal {μ = ν} hA
      (CoercionProof.DualStoreAt.seal∈ ds μα ηα να αA∈Σ)
      (sealModeAllowed-var-seal {ν = ν} {α = α} να) ,
    unsealʷ α A
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seal hA αA∈Σ ok , sealⁿ A α)
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | ()
  dualⁿ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-seal {α = α} hA αA∈Σ ok , sealⁿ A .α)
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl
      rewrite CoercionProof.DualStoreAt.seal★ ds ηα αA∈Σ =
    cast-tag (wfVar (bound wfΣ αA∈Σ)) (＇ α)
      (tagModeAllowed-var-tag {ν = ν} {α = α} να) ,
    tag (＇ α)
  dualⁿ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-seq s⊢ (cast-seal {α = α} hA αA∈Σ ok) ,
       sⁿ ︔seal .α)
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seq s⊢ (cast-seal hA αA∈Σ ok) ,
       sⁿ ︔seal _)
      | id-only | normal | id-only | dma-id | ()
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seq s⊢ (cast-seal hA αA∈Σ ok) ,
       sⁿ ︔seal _)
      | tag-or-id | normal | tag-or-id | dma-tag | ()
  dualⁿ-flips-typingᵐ {η = η} {ν = ν} rel ds wfΣ
      (cast-seq s⊢ (cast-seal {α = α} hA αA∈Σ ok) ,
       sⁿ ︔seal _)
      | seal-or-id | normal | seal-or-id | dma-seal | refl =
    cast-seq
      (cast-unseal {μ = ν} hA
        (CoercionProof.DualStoreAt.seal∈ ds μα ηα να αA∈Σ)
        (sealModeAllowed-var-seal {ν = ν} {α = α} να))
      (proj₁
        (dualStrictⁿ-flips-typingᵐ rel ds wfΣ (s⊢ , sⁿ))) ,
    unseal︔_ α (proj₂ (dualStrictⁿ η sⁿ))
  dualⁿ-flips-typingᵐ rel ds wfΣ
      (cast-seq s⊢ (cast-seal hA αA∈Σ ok) ,
       sⁿ ︔seal _)
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | ()
  dualⁿ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-seq s⊢ (cast-seal {α = α} hA αA∈Σ ok) ,
       sⁿ ︔seal _)
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl
      rewrite CoercionProof.DualStoreAt.seal★ ds ηα αA∈Σ
            | narrowing-target-star-source-star
                (s⊢ , strictⁿ→narrow sⁿ) =
    cast-tag (wfVar (bound wfΣ αA∈Σ)) (＇ α)
      (tagModeAllowed-var-tag {ν = ν} {α = α} να) ,
    tag (＇ α)

  dualStrictⁿ-flips-typingᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × StrictNarrowing c) →
    (ν ∣ Δ ∣ Π ⊢ proj₁ (dualStrictⁿ η (proj₂ p)) ∶ B =⇒ A) ×
    StrictWidening (proj₁ (dualStrictⁿ η (proj₂ p)))
  dualStrictⁿ-flips-typingᵐ
      {η = η} {ν = ν} {Δ = Δ} {Π = Π} {A = A} {B = B}
      rel ds wfΣ (c⊢ , cⁿ) =
    subst
      (λ d → ν ∣ Δ ∣ Π ⊢ d ∶ B =⇒ A)
      (dualStrictⁿ-raw η cⁿ)
      (proj₁
        (dualⁿ-flips-typingᵐ
          rel ds wfΣ (c⊢ , strictⁿ→narrow cⁿ))) ,
    proj₂ (dualStrictⁿ η cⁿ)

  dualCrossWidening-flips-coercionᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossWidening c) →
    ν ∣ Δ ∣ Π ⊢ proj₁ (dualCrossWidening η (proj₂ p)) ∶ B =⇒ A
  dualCrossWidening-flips-coercionᵐ rel ds wfΣ
      (cast-id {A = ＇ α} hA ok , id-＇ .α) =
    cast-id {A = ＇ α} hA
      (dualActionOk-idTyAllowed {A = ＇ α} rel ok)
  dualCrossWidening-flips-coercionᵐ rel ds wfΣ
      (cast-id {A = ‵ ι} hA ok , id-‵ .ι) =
    cast-id {A = ‵ ι} hA
      (dualActionOk-idTyAllowed {A = ‵ ι} rel ok)
  dualCrossWidening-flips-coercionᵐ rel ds wfΣ
      (cast-fun s⊢ t⊢ , _↦_ sⁿ tʷ) =
    cast-fun
      (proj₁ (dualⁿ-flips-typingᵐ rel ds wfΣ (s⊢ , sⁿ)))
      (proj₁ (dualʷ-flips-typingᵐ rel ds wfΣ (t⊢ , tʷ)))
  dualCrossWidening-flips-coercionᵐ rel ds wfΣ
      (cast-all c⊢ , `∀ cʷ) =
    cast-all
      (proj₁
        (dualʷ-flips-typingᵐ
          (dualActionOk-ext rel)
          (dualStoreAt-ext ds)
          (StoreWfAt-⟰ᵗ wfΣ)
          (c⊢ , cʷ)))

  dualStrictCrossWidening-flips-coercionᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × StrictCrossWidening c) →
    ν ∣ Δ ∣ Π ⊢ proj₁ (dualStrictCrossWidening η (proj₂ p)) ∶ B =⇒ A
  dualStrictCrossWidening-flips-coercionᵐ
      {η = η} {ν = ν} {Δ = Δ} {Π = Π} {A = A} {B = B}
      rel ds wfΣ (c⊢ , cʷ) =
    subst
      (λ d → ν ∣ Δ ∣ Π ⊢ d ∶ B =⇒ A)
      (dualStrictCrossWidening-raw η cʷ)
      (dualCrossWidening-flips-coercionᵐ
        rel ds wfΣ (c⊢ , strictCrossʷ→cross cʷ))

  dualʷ-flips-typingᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B) →
    ν ∣ Δ ∣ Π ⊢ proj₁ (dualʷ η (proj₂ p)) ∶ B ⊒ A
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (c⊢ , cross cʷ) =
    dualCrossWidening-flips-coercionᵐ rel ds wfΣ (c⊢ , cʷ) ,
    cross (proj₂ (dualCrossWidening η cʷ))
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-id {A = ★} hA ok , id★) =
    cast-id {A = ★} hA
      (dualActionOk-idTyAllowed {A = ★} rel ok) ,
    id★
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-inst hB occ c⊢ , inst cᵍ) =
    cast-gen hB occ
      (subst
        (λ d → _ ∣ _ ∣ _ ⊢ d ∶ _ =⇒ _)
        (sym (instSafeʷ-raw (instᵃ η) cᵍ))
        (proj₁
          (dualʷ-flips-typingᵐ
            (dualActionOk-inst-gen rel)
            (dualStoreAt-inst-gen ds)
            (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
            (c⊢ , instSafe→widening cᵍ)))) ,
    gen (proj₂ (instSafeʷ (instᵃ η) cᵍ))
  dualʷ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-tag (wfVar α<Δ) (＇ α) ok , tag (＇ .α))
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-tag (wfVar α<Δ) (＇ α) ok , tag (＇ .α))
      | id-only | normal | id-only | dma-id | ()
  dualʷ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-tag (wfVar α<Δ) (＇ α) ok , tag (＇ .α))
      | tag-or-id | normal | tag-or-id | dma-tag | refl =
    cast-untag (wfVar α<Δ) (＇ α)
      (tagModeAllowed-var-tag {ν = ν} {α = α} να) ,
    untag (＇ α)
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-tag (wfVar α<Δ) (＇ α) ok , tag (＇ .α))
      | seal-or-id | normal | seal-or-id | dma-seal | ()
  dualʷ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-tag (wfVar α<Δ) (＇ α) ok , tag (＇ .α))
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl =
    cast-seal {μ = ν} wf★
      (CoercionProof.DualStoreAt.tag★∈ ds α<Δ ηα)
      (sealModeAllowed-var-seal {ν = ν} {α = α} να) ,
    sealⁿ ★ α
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-tag (wfVar α<Δ) (＇ α) ok , tag (＇ .α))
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | ()
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-tag hG (‵ ι) ok , tag (‵ .ι)) =
    cast-untag hG (‵ ι) refl , untag (‵ ι)
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-tag hG ★⇒★ ok , tag ★⇒★) =
    cast-untag hG ★⇒★ refl , untag ★⇒★
  dualʷ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-seq g⊢ (cast-tag (wfVar α<Δ) (＇ α) ok) ,
       (gʷ ︔ (＇ .α) !))
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-seq g⊢ (cast-tag (wfVar α<Δ) (＇ α) ok) ,
       (gʷ ︔ (＇ .α) !))
      | id-only | normal | id-only | dma-id | ()
  dualʷ-flips-typingᵐ {η = η} {ν = ν} rel ds wfΣ
      (cast-seq g⊢ (cast-tag (wfVar α<Δ) (＇ α) ok) ,
       (gʷ ︔ (＇ .α) !))
      | tag-or-id | normal | tag-or-id | dma-tag | refl =
    cast-seq
      (cast-untag (wfVar α<Δ) (＇ α)
        (tagModeAllowed-var-tag {ν = ν} {α = α} να))
      (dualStrictCrossWidening-flips-coercionᵐ rel ds wfΣ (g⊢ , gʷ)) ,
    _？︔_ (＇ α) (proj₂ (dualStrictCrossWidening η gʷ))
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-seq g⊢ (cast-tag (wfVar α<Δ) (＇ α) ok) ,
       (gʷ ︔ (＇ .α) !))
      | seal-or-id | normal | seal-or-id | dma-seal | ()
  dualʷ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-seq g⊢ (cast-tag (wfVar α<Δ) (＇ α) ok) ,
       (gʷ ︔ (＇ .α) !))
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl
      rewrite widening-cross-var-target-source
                (g⊢ , strictCrossʷ→cross gʷ) =
    cast-seal {μ = ν} wf★
      (CoercionProof.DualStoreAt.tag★∈ ds α<Δ ηα)
      (sealModeAllowed-var-seal {ν = ν} {α = α} να) ,
    sealⁿ ★ α
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-seq g⊢ (cast-tag (wfVar α<Δ) (＇ α) ok) ,
       (gʷ ︔ (＇ .α) !))
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | ()
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-seq g⊢ (cast-tag hG (‵ ι) ok) ,
       (gʷ ︔ (‵ .ι) !)) =
    cast-seq
      (cast-untag hG (‵ ι) refl)
      (dualStrictCrossWidening-flips-coercionᵐ rel ds wfΣ (g⊢ , gʷ)) ,
    _？︔_ (‵ ι) (proj₂ (dualStrictCrossWidening η gʷ))
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-seq g⊢ (cast-tag hG ★⇒★ ok) ,
       ((gʷ ︔ ★⇒★ !))) =
    cast-seq
      (cast-untag hG ★⇒★ refl)
      (dualStrictCrossWidening-flips-coercionᵐ rel ds wfΣ (g⊢ , gʷ)) ,
    _？︔_ ★⇒★ (proj₂ (dualStrictCrossWidening η gʷ))
  dualʷ-flips-typingᵐ {η = η} rel ds wfΣ
      (cast-seq (cast-inst hB occ c⊢)
                (cast-tag hG ★⇒★ ok) ,
       inst-fun-tag cᵍ) =
    cast-seq
      (cast-untag hG ★⇒★ refl)
      (cast-gen hB occ
        (subst
          (λ d → _ ∣ _ ∣ _ ⊢ d ∶ _ =⇒ _)
          (sym (instSafeʷ-raw (instᵃ η) cᵍ))
          (proj₁
            (dualʷ-flips-typingᵐ
              (dualActionOk-inst-gen rel)
              (dualStoreAt-inst-gen ds)
              (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
              (c⊢ , instSafe→widening cᵍ))))) ,
    fun-untag-gen (proj₂ (instSafeʷ (instᵃ η) cᵍ))
  dualʷ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-unseal {α = α} hA αA∈Σ ok , unsealʷ .α A)
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-unseal hA αA∈Σ ok , unsealʷ α A)
      | id-only | normal | id-only | dma-id | ()
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-unseal hA αA∈Σ ok , unsealʷ α A)
      | tag-or-id | normal | tag-or-id | dma-tag | ()
  dualʷ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-unseal {α = α} hA αA∈Σ ok , unsealʷ .α A)
      | seal-or-id | normal | seal-or-id | dma-seal | refl =
    cast-seal {μ = ν} hA
      (CoercionProof.DualStoreAt.seal∈ ds μα ηα να αA∈Σ)
      (sealModeAllowed-var-seal {ν = ν} {α = α} να) ,
    sealⁿ A α
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-unseal hA αA∈Σ ok , unsealʷ α A)
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | ()
  dualʷ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-unseal {α = α} hA αA∈Σ ok , unsealʷ .α A)
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl
      rewrite CoercionProof.DualStoreAt.seal★ ds ηα αA∈Σ =
    cast-untag (wfVar (bound wfΣ αA∈Σ)) (＇ α)
      (tagModeAllowed-var-tag {ν = ν} {α = α} να) ,
    untag (＇ α)
  dualʷ-flips-typingᵐ {μ = μ} {η = η} {ν = ν}
      rel ds wfΣ
      (cast-seq (cast-unseal {α = α} hA αA∈Σ ok) s⊢ ,
       unseal︔_ .α sʷ)
      with μ α in μα | η α in ηα | ν α in να | rel α | ok
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-seq (cast-unseal hA αA∈Σ ok) s⊢ ,
       unseal︔_ _ sʷ)
      | id-only | normal | id-only | dma-id | ()
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-seq (cast-unseal hA αA∈Σ ok) s⊢ ,
       unseal︔_ _ sʷ)
      | tag-or-id | normal | tag-or-id | dma-tag | ()
  dualʷ-flips-typingᵐ {η = η} {ν = ν} rel ds wfΣ
      (cast-seq (cast-unseal {α = α} hA αA∈Σ ok) s⊢ ,
       unseal︔_ _ sʷ)
      | seal-or-id | normal | seal-or-id | dma-seal | refl =
    cast-seq
      (proj₁ (dualStrictʷ-flips-typingᵐ rel ds wfΣ (s⊢ , sʷ)))
      (cast-seal {μ = ν} hA
        (CoercionProof.DualStoreAt.seal∈ ds μα ηα να αA∈Σ)
        (sealModeAllowed-var-seal {ν = ν} {α = α} να)) ,
    proj₂ (dualStrictʷ η sʷ) ︔seal α
  dualʷ-flips-typingᵐ rel ds wfΣ
      (cast-seq (cast-unseal hA αA∈Σ ok) s⊢ ,
       unseal︔_ _ sʷ)
      | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | ()
  dualʷ-flips-typingᵐ {ν = ν} rel ds wfΣ
      (cast-seq (cast-unseal {α = α} hA αA∈Σ ok) s⊢ ,
       unseal︔_ _ sʷ)
      | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl
      rewrite CoercionProof.DualStoreAt.seal★ ds ηα αA∈Σ
            | widening-source-star-target-star
                (s⊢ , strictʷ→widen sʷ) =
    cast-untag (wfVar (bound wfΣ αA∈Σ)) (＇ α)
      (tagModeAllowed-var-tag {ν = ν} {α = α} να) ,
    untag (＇ α)

  dualStrictʷ-flips-typingᵐ :
    ∀ {μ η ν Δ Σ Π c A B} →
    DualActionOk μ η ν →
    DualStoreAt Δ μ η ν Σ Π →
    StoreWfAt Δ Σ →
    (p : (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × StrictWidening c) →
    (ν ∣ Δ ∣ Π ⊢ proj₁ (dualStrictʷ η (proj₂ p)) ∶ B =⇒ A) ×
    StrictNarrowing (proj₁ (dualStrictʷ η (proj₂ p)))
  dualStrictʷ-flips-typingᵐ
      {η = η} {ν = ν} {Δ = Δ} {Π = Π} {A = A} {B = B}
      rel ds wfΣ (c⊢ , cʷ) =
    subst
      (λ d → ν ∣ Δ ∣ Π ⊢ d ∶ B =⇒ A)
      (dualStrictʷ-raw η cʷ)
      (proj₁
        (dualʷ-flips-typingᵐ
          rel ds wfΣ (c⊢ , strictʷ→widen cʷ))) ,
    proj₂ (dualStrictʷ η cʷ)

fun-narrow-domain-dual-typingᶜ :
  ∀ {Δ Σ p q A A′ B B′} →
  StoreWfAt Δ Σ →
  (p↦qᶜ : Δ ∣ Σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
  Δ ∣ Σ ⊢ fun-narrow-domain-dualᶜ p↦qᶜ ∶ᶜ A ⊒ A′
fun-narrow-domain-dual-typingᶜ wfΣ
    (cast-fun p⊢ q⊢ , cross (pʷ ↦ qⁿ)) =
  dualʷ-flips-typingᵐ
    {μ = tag-or-idᵈ}
    {η = normalᵃ}
    {ν = tag-or-idᵈ}
    dualActionOk-normal
    dualStoreAt-normal
    wfΣ
    (p⊢ , pʷ)

widening-cross-ground-source-all⊥ :
  ∀ {μ Δ Σ A G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ `∀ A =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-all⊥ (＇ α)
    (() , id-＇ _)
widening-cross-ground-source-all⊥ (‵ ι)
    (() , id-‵ _)
widening-cross-ground-source-all⊥ ★⇒★
    (() , _↦_ sⁿ tʷ)
widening-cross-ground-source-all⊥ (＇ α)
    (() , `∀ gʷ)
widening-cross-ground-source-all⊥ (‵ ι)
    (() , `∀ gʷ)
widening-cross-ground-source-all⊥ ★⇒★
    (() , `∀ gʷ)

narrowing-cross-ground-target-all⊥ :
  ∀ {μ Δ Σ A G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ `∀ A) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-all⊥ (＇ α)
    (() , id-＇ _)
narrowing-cross-ground-target-all⊥ (‵ ι)
    (() , id-‵ _)
narrowing-cross-ground-target-all⊥ ★⇒★
    (() , _↦_ sʷ tⁿ)
narrowing-cross-ground-target-all⊥ (＇ α)
    (() , `∀ gⁿ)
narrowing-cross-ground-target-all⊥ (‵ ι)
    (() , `∀ gⁿ)
narrowing-cross-ground-target-all⊥ ★⇒★
    (() , `∀ gⁿ)

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
    α∈Σ seal-ok (cast-id hA id-ok , id-＇ _) =
  tag-seal-conflict tag-ok seal-ok
narrowing-cross-ground-target-seal-var⊥ wfΣ (‵ ι) tag-ok
    α∈Σ seal-ok (() , id-‵ _)
narrowing-cross-ground-target-seal-var⊥ wfΣ ★⇒★ tag-ok
    α∈Σ seal-ok (() , _↦_ sʷ tⁿ)
narrowing-cross-ground-target-seal-var⊥ wfΣ gG tag-ok
    α∈Σ seal-ok (() , `∀ gⁿ)

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
    α∈Σ seal-ok (cast-id hA id-ok , id-＇ _) =
  tag-seal-conflict tag-ok seal-ok
widening-cross-ground-source-seal-var⊥ wfΣ (‵ ι) tag-ok
    α∈Σ seal-ok (() , id-‵ _)
widening-cross-ground-source-seal-var⊥ wfΣ ★⇒★ tag-ok
    α∈Σ seal-ok (() , _↦_ sⁿ tʷ)
widening-cross-ground-source-seal-var⊥ wfΣ gG tag-ok
    α∈Σ seal-ok (() , `∀ gʷ)

tag-or-id-seal-conflict :
  ∀ {μ : ModeEnv} {α} →
  μ α ≡ tag-or-id →
  sealModeAllowed (μ α) ≡ true →
  ⊥
tag-or-id-seal-conflict tag-ok seal-ok rewrite tag-ok =
  false≢true seal-ok

seal-or-id-tag-conflict :
  ∀ {μ : ModeEnv} {α} →
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
narrowing-all-to-var-tag⊥ tag-ok (() , cross (id-＇ _))
narrowing-all-to-var-tag⊥ tag-ok (() , cross (id-‵ _))
narrowing-all-to-var-tag⊥ tag-ok (() , cross (_↦_ sʷ tⁿ))
narrowing-all-to-var-tag⊥ tag-ok (() , cross (`∀ sⁿ))
narrowing-all-to-var-tag⊥ tag-ok (() , id★)
narrowing-all-to-var-tag⊥ tag-ok (() , gen sⁿ)
narrowing-all-to-var-tag⊥ tag-ok (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-all-to-var-tag⊥ tag-ok
    (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-all-to-var-tag⊥ {μ = μ} {α = α} tag-ok
    (cast-seal {α = .α} hA α∈Σ seal-ok , sealⁿ _ _) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok
narrowing-all-to-var-tag⊥ {μ = μ} {α = α} tag-ok
    (cast-seq s⊢ (cast-seal {α = .α} hA α∈Σ seal-ok) ,
     sⁿ ︔seal _) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok

narrowing-all-to-fun⊥ :
  ∀ {μ Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ A) ⊒ (B ⇒ C) →
  ⊥
narrowing-all-to-fun⊥ (() , cross (id-＇ _))
narrowing-all-to-fun⊥ (() , cross (id-‵ _))
narrowing-all-to-fun⊥ (() , cross (_↦_ sʷ tⁿ))
narrowing-all-to-fun⊥ (() , cross (`∀ sⁿ))
narrowing-all-to-fun⊥ (() , id★)
narrowing-all-to-fun⊥ (() , gen sⁿ)
narrowing-all-to-fun⊥ (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-all-to-fun⊥ (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-all-to-fun⊥ (cast-seq s⊢ () , sⁿ ︔seal _)

narrowing-all-to-star⊥ :
  ∀ {μ Δ Σ A c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ A) ⊒ ★ →
  ⊥
narrowing-all-to-star⊥ (() , cross (id-＇ _))
narrowing-all-to-star⊥ (() , cross (id-‵ _))
narrowing-all-to-star⊥ (() , cross (_↦_ sʷ tⁿ))
narrowing-all-to-star⊥ (() , cross (`∀ sⁿ))
narrowing-all-to-star⊥ (() , id★)
narrowing-all-to-star⊥ (() , gen sⁿ)
narrowing-all-to-star⊥ (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-all-to-star⊥ (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-all-to-star⊥ (cast-seq s⊢ () , sⁿ ︔seal _)

narrowing-var-to-star⊥ :
  ∀ {μ Δ Σ α c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊒ ★ →
  ⊥
narrowing-var-to-star⊥ (() , cross (id-＇ _))
narrowing-var-to-star⊥ (() , cross (id-‵ _))
narrowing-var-to-star⊥ (() , cross (_↦_ sʷ tⁿ))
narrowing-var-to-star⊥ (() , cross (`∀ sⁿ))
narrowing-var-to-star⊥ (() , id★)
narrowing-var-to-star⊥ (() , gen sⁿ)
narrowing-var-to-star⊥ (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-var-to-star⊥ (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-var-to-star⊥ (cast-seq s⊢ () , sⁿ ︔seal _)

narrowing-var≢-to-var-tag⊥ :
  ∀ {μ Δ Σ α β c} →
  β ≢ α →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ β) ⊒ (＇ α) →
  ⊥
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-id hA id-ok , cross (id-＇ _)) =
  β≢α refl
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-var≢-to-var-tag⊥ {μ = μ} {α = α} β≢α tag-ok
    (cast-seal {α = .α} hA α∈Σ seal-ok , sealⁿ _ _) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok
narrowing-var≢-to-var-tag⊥ {μ = μ} {α = α} β≢α tag-ok
    (cast-seq s⊢ (cast-seal {α = .α} hA α∈Σ seal-ok) ,
     sⁿ ︔seal _) =
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
widening-var-to-all-tag⊥ tag-ok (() , cross (id-＇ _))
widening-var-to-all-tag⊥ tag-ok (() , cross (id-‵ _))
widening-var-to-all-tag⊥ tag-ok (() , cross (_↦_ sⁿ tʷ))
widening-var-to-all-tag⊥ tag-ok (() , cross (`∀ sʷ))
widening-var-to-all-tag⊥ tag-ok (() , id★)
widening-var-to-all-tag⊥ tag-ok (() , inst sʷ)
widening-var-to-all-tag⊥ tag-ok (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-var-to-all-tag⊥ tag-ok
    (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-var-to-all-tag⊥ {μ = μ} {α = α} tag-ok
    (cast-unseal {α = .α} hA α∈Σ seal-ok , unsealʷ _ _) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok
widening-var-to-all-tag⊥ {μ = μ} {α = α} tag-ok
    (cast-seq (cast-unseal {α = .α} hA α∈Σ seal-ok) s⊢ ,
     unseal︔_ _ sʷ) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok

widening-var≢-to-var-tag⊥ :
  ∀ {μ Δ Σ α β c} →
  β ≢ α →
  μ α ≡ tag-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ β) →
  ⊥
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-id hA id-ok , cross (id-＇ _)) =
  β≢α refl
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-var≢-to-var-tag⊥ β≢α tag-ok
    (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-var≢-to-var-tag⊥ {μ = μ} {α = α} β≢α tag-ok
    (cast-unseal {α = .α} hA α∈Σ seal-ok , unsealʷ _ _) =
  tag-or-id-seal-conflict {μ = μ} {α = α} tag-ok seal-ok
widening-var≢-to-var-tag⊥ {μ = μ} {α = α} β≢α tag-ok
    (cast-seq (cast-unseal {α = .α} hA α∈Σ seal-ok) s⊢ ,
     unseal︔_ _ sʷ) =
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
widening-star-to-all⊥ (() , cross (id-＇ _))
widening-star-to-all⊥ (() , cross (id-‵ _))
widening-star-to-all⊥ (() , cross (_↦_ sⁿ tʷ))
widening-star-to-all⊥ (() , cross (`∀ sʷ))
widening-star-to-all⊥ (() , id★)
widening-star-to-all⊥ (() , inst sʷ)
widening-star-to-all⊥ (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-star-to-all⊥ (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-star-to-all⊥ (cast-seq () s⊢ , unseal︔_ _ sʷ)

widening-fun-to-all⊥ :
  ∀ {μ Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) ⊑ (`∀ C) →
  ⊥
widening-fun-to-all⊥ (() , cross (id-＇ _))
widening-fun-to-all⊥ (() , cross (id-‵ _))
widening-fun-to-all⊥ (() , cross (_↦_ sⁿ tʷ))
widening-fun-to-all⊥ (() , cross (`∀ sʷ))
widening-fun-to-all⊥ (() , id★)
widening-fun-to-all⊥ (() , inst sʷ)
widening-fun-to-all⊥ (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-fun-to-all⊥ (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-fun-to-all⊥ (cast-seq () s⊢ , unseal︔_ _ sʷ)

widening-star-to-var⊥ :
  ∀ {μ Δ Σ α c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊑ (＇ α) →
  ⊥
widening-star-to-var⊥ (() , cross (id-＇ _))
widening-star-to-var⊥ (() , cross (id-‵ _))
widening-star-to-var⊥ (() , cross (_↦_ sⁿ tʷ))
widening-star-to-var⊥ (() , cross (`∀ sʷ))
widening-star-to-var⊥ (() , id★)
widening-star-to-var⊥ (() , inst sʷ)
widening-star-to-var⊥ (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-star-to-var⊥ (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-star-to-var⊥ (cast-seq () s⊢ , unseal︔_ _ sʷ)

widening-var-to-all-seal⊥ :
  ∀ {μ Δ Σ α B c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (`∀ B) →
  ⊥
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (id-＇ _))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (id-‵ _))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (_↦_ sⁿ tʷ))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (`∀ sʷ))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok (() , id★)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok (() , inst sʷ)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (cast-unseal hA α∈Σ seal-ok′ , unsealʷ _ _) =
  star≢all (unique wfΣ α↦★ α∈Σ)
widening-var-to-all-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) t⊢ , unseal︔_ _ tʷ)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  widening-star-to-all⊥ (t⊢ , strictʷ→widen tʷ)

widening-var≢-to-var-seal⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  β ≢ α →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ β) →
  ⊥
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-id hA id-ok , cross (id-＇ _)) =
  β≢α refl
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq s⊢ () , ((sʷ ︔ gG !)))
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq s⊢ () , inst-fun-tag sᵍ)
widening-var≢-to-var-seal⊥ {β = β} wfΣ α↦★ β≢α seal-ok
    (cast-unseal hA α∈Σ seal-ok′ , unsealʷ _ _) =
  star≢var {α = β} (unique wfΣ α↦★ α∈Σ)
widening-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) t⊢ , unseal︔_ _ tʷ)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  widening-star-to-var⊥ (t⊢ , strictʷ→widen tʷ)

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
    (() , cross (id-＇ _))
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (id-‵ _))
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (_↦_ sʷ tⁿ))
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (() , cross (`∀ sⁿ))
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok (() , id★)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok (() , gen sⁿ)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (cast-seal hA α∈Σ seal-ok′ , sealⁿ _ _) =
  star≢all (unique wfΣ α↦★ α∈Σ)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-all-to-var-seal⊥ wfΣ α↦★ seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , sⁿ ︔seal _)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  narrowing-all-to-star⊥ (s⊢ , strictⁿ→narrow sⁿ)

narrowing-var≢-to-var-seal⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreDetWf Δ Σ →
  (α , ★) ∈ Σ →
  β ≢ α →
  μ α ≡ seal-or-id →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ β) ⊒ (＇ α) →
  ⊥
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-id hA id-ok , cross (id-＇ _)) =
  β≢α refl
narrowing-var≢-to-var-seal⊥ {β = β} wfΣ α↦★ β≢α seal-ok
    (cast-seal hA α∈Σ seal-ok′ , sealⁿ _ _) =
  star≢var {α = β} (unique wfΣ α↦★ α∈Σ)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq () s⊢ , _？︔_ gG sⁿ)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq () s⊢ , fun-untag-gen sᵍ)
narrowing-var≢-to-var-seal⊥ wfΣ α↦★ β≢α seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , sⁿ ︔seal _)
    rewrite sym (unique wfΣ α↦★ α∈Σ) =
  narrowing-var-to-star⊥ (s⊢ , strictⁿ→narrow sⁿ)

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

narrow-path-star-spine⊥ :
  ∀ {α A B} →
  NarrowPath α A B →
  EndpointSpine A ★ →
  ⊥
narrow-path-star-spine⊥ np-var
    (spine-renamed {T = ＇ β} refl ())
narrow-path-star-spine⊥ (np-fun₁ p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
narrow-path-star-spine⊥ (np-fun₂ p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
narrow-path-star-spine⊥ (np-all p) (spine-left-all sp) =
  narrow-path-star-spine⊥ p sp
narrow-path-star-spine⊥ (np-all p)
    (spine-renamed {T = `∀ T} refl ())
narrow-path-star-spine⊥ (np-gen p) sp =
  narrow-path-star-spine⊥ p (spine-map-left suc sp)

widen-path-star-spine⊥ :
  ∀ {α A B} →
  WidenPath α A B →
  EndpointSpine B ★ →
  ⊥
widen-path-star-spine⊥ wp-var
    (spine-renamed {T = ＇ β} refl ())
widen-path-star-spine⊥ (wp-fun₁ p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
widen-path-star-spine⊥ (wp-fun₂ p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
widen-path-star-spine⊥ (wp-all p) (spine-left-all sp) =
  widen-path-star-spine⊥ p sp
widen-path-star-spine⊥ (wp-all p)
    (spine-renamed {T = `∀ T} refl ())
widen-path-star-spine⊥ (wp-inst p) sp =
  widen-path-star-spine⊥ p (spine-map-left suc sp)

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
      (cast-fun s⊢ t⊢ , cross (_↦_ sʷ tⁿ)) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sʷ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , cross (_↦_ sʷ tⁿ)) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , _？︔_ gG tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , _？︔_ gG tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , tⁿ ︔seal _)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , tⁿ ︔seal _)
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₁ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-tag-spine-overlap⊥ tag-ok (np-fun₂ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (np-all p)
      sp fresh (cast-all t⊢ , cross (`∀ tⁿ)) =
    narrowing-tag-spine-overlap⊥
      tag-ok p (spine-strip-both sp) fresh (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (np-all p)
      sp fresh (cast-gen hC occC t⊢ , gen tᵍ) =
    narrowing-tag-spine-overlap⊥
      tag-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , genSafe→narrowing tᵍ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-seq (cast-untag hG gG okG) t⊢ , _？︔_ gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , strictCrossⁿ→cross tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-id hA ok , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-unseal hA α∈Σ ok , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-inst hA occ t⊢ , cross ())
  narrowing-tag-spine-overlap⊥ {C = `∀ C} {α = α} tag-ok
      (np-gen p) sp fresh
      (cast-all t⊢ , cross (`∀ tⁿ)) =
    narrowing-tag-spine-overlap⊥
      tag-ok p (spine-peel-right suc sp) fresh (t⊢ , tⁿ)
  narrowing-tag-spine-overlap⊥ {C = C} {α = α} tag-ok
      (np-gen p) sp fresh (cast-gen hC occC t⊢ , gen tᵍ) =
    narrowing-tag-spine-overlap⊥
      tag-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , genSafe→narrowing tᵍ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-seq (cast-untag hG gG okG) t⊢ , _？︔_ gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , strictCrossⁿ→cross tⁿ)
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-id hA ok , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-unseal hA α∈Σ ok , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-inst hA occ t⊢ , cross ())
  narrowing-tag-spine-overlap⊥ tag-ok (np-all p) sp fresh
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hC occC t⊢) ,
       fun-untag-gen tᵍ) =
    narrow-path-star-spine⊥ (np-all p) sp
  narrowing-tag-spine-overlap⊥ tag-ok (np-gen p) sp fresh
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hC occC t⊢) ,
       fun-untag-gen tᵍ) =
    narrow-path-star-spine⊥ (np-gen p) sp

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
      (cast-fun s⊢ t⊢ , cross (_↦_ sⁿ tʷ)) =
    narrowing-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sⁿ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , cross (_↦_ sⁿ tʷ)) =
    widening-tag-spine-overlap⊥ tag-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , ((tʷ ︔ gG !)))
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , ((tʷ ︔ gG !)))
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , unseal︔_ _ tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , unseal︔_ _ tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₁ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-tag-spine-overlap⊥ tag-ok (wp-fun₂ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (wp-all p)
      sp fresh (cast-all t⊢ , cross (`∀ tʷ)) =
    widening-tag-spine-overlap⊥
      tag-ok p (spine-strip-both sp) fresh (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ {C = C} {α = α} tag-ok (wp-all p)
      sp fresh (cast-inst hC occC t⊢ , inst tᵍ) =
    widening-tag-spine-overlap⊥
      tag-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , instSafe→widening tᵍ)
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-seq t⊢ (cast-tag hG gG okG) , ((tʷ ︔ gG′ !))) =
    widening-cross-ground-source-all⊥ gG (t⊢ , strictCrossʷ→cross tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-id hA ok , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-seal hA α∈Σ ok , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-gen hA occ t⊢ , cross ())
  widening-tag-spine-overlap⊥ {C = `∀ C} tag-ok (wp-inst p) sp
      fresh (cast-all t⊢ , cross (`∀ tʷ)) =
    widening-tag-spine-overlap⊥
      tag-ok p (spine-peel-right suc sp) fresh (t⊢ , tʷ)
  widening-tag-spine-overlap⊥ {C = C} {α = α} tag-ok
      (wp-inst p) sp fresh (cast-inst hC occC t⊢ , inst tᵍ) =
    widening-tag-spine-overlap⊥
      tag-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , instSafe→widening tᵍ)
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-seq t⊢ (cast-tag hG gG okG) , ((tʷ ︔ gG′ !))) =
    widening-cross-ground-source-all⊥ gG (t⊢ , strictCrossʷ→cross tʷ)
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-id hA ok , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-seal hA α∈Σ ok , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-gen hA occ t⊢ , cross ())
  widening-tag-spine-overlap⊥ tag-ok (wp-all p) sp fresh
      (cast-seq (cast-inst hC occC t⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag tᵍ) =
    widen-path-star-spine⊥ (wp-all p) sp
  widening-tag-spine-overlap⊥ tag-ok (wp-inst p) sp fresh
      (cast-seq (cast-inst hC occC t⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag tᵍ) =
    widen-path-star-spine⊥ (wp-inst p) sp

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
      (cast-fun s⊢ t⊢ , cross (_↦_ sʷ tⁿ)) =
    widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sʷ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , cross (_↦_ sʷ tⁿ)) =
    narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , _？︔_ gG tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , _？︔_ gG tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , tⁿ ︔seal _)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , tⁿ ︔seal _)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₁ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-fun₂ p)
      (spine-right-all sp) fresh t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-all t⊢ , cross (`∀ tⁿ)) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-strip-both sp)
      fresh
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (np-all p) sp fresh (cast-gen hC occC t⊢ , gen tᵍ) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , genSafe→narrowing tᵍ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-seq (cast-untag hG gG okG) t⊢ ,
                _？︔_ gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , strictCrossⁿ→cross tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-id hA ok , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-unseal hA α∈Σ ok , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p)
      sp fresh (cast-inst hA occ t⊢ , cross ())
  narrowing-seal-spine-overlap⊥ {C = `∀ C} wfΣ α↦★ seal-ok
      (np-gen p) sp fresh (cast-all t⊢ , cross (`∀ tⁿ)) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-peel-right suc sp)
      fresh
      (t⊢ , tⁿ)
  narrowing-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (np-gen p) sp fresh (cast-gen hC occC t⊢ , gen tᵍ) =
    narrowing-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , genSafe→narrowing tᵍ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-seq (cast-untag hG gG okG) t⊢ ,
                _？︔_ gG′ tⁿ) =
    narrowing-cross-ground-target-all⊥ gG (t⊢ , strictCrossⁿ→cross tⁿ)
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-id hA ok , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-unseal hA α∈Σ ok , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p)
      sp fresh (cast-inst hA occ t⊢ , cross ())
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-all p) sp fresh
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hC occC t⊢) ,
       fun-untag-gen tᵍ) =
    narrow-path-star-spine⊥ (np-all p) sp
  narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (np-gen p) sp fresh
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hC occC t⊢) ,
       fun-untag-gen tᵍ) =
    narrow-path-star-spine⊥ (np-gen p) sp

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
      (cast-fun s⊢ t⊢ , cross (_↦_ sⁿ tʷ)) =
    narrowing-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₁} refl refl)
      (∨-falseˡ fresh)
      (s⊢ , sⁿ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-fun s⊢ t⊢ , cross (_↦_ sⁿ tʷ)) =
    widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok p
      (spine-renamed {T = T₂} refl refl)
      (∨-falseʳ {b = occurs _ (renameᵗ _ T₁)} fresh)
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-id hA ok , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , ((tʷ ︔ gG !)))
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq t⊢ () , ((tʷ ︔ gG !)))
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , unseal︔_ _ tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh
      (cast-seq () t⊢ , unseal︔_ _ tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₁ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-fun₂ p)
      (spine-right-all sp) fresh t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-all t⊢ , cross (`∀ tʷ)) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-strip-both sp)
      fresh
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (wp-all p) sp fresh (cast-inst hC occC t⊢ , inst tᵍ) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-inst wfΣ)
      (there (∈-renameStoreᵗ suc α↦★))
      seal-ok
      p
      (spine-peel-left suc sp)
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , instSafe→widening tᵍ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-seq t⊢ (cast-tag hG gG okG) ,
                ((tʷ ︔ gG′ !))) =
    widening-cross-ground-source-all⊥ gG (t⊢ , strictCrossʷ→cross tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-id hA ok , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-seal hA α∈Σ ok , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p)
      sp fresh (cast-gen hA occ t⊢ , cross ())
  widening-seal-spine-overlap⊥ {C = `∀ C} wfΣ α↦★ seal-ok
      (wp-inst p) sp fresh (cast-all t⊢ , cross (`∀ tʷ)) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-⟰ᵗ wfΣ)
      (∈-renameStoreᵗ suc α↦★)
      seal-ok
      p
      (spine-peel-right suc sp)
      fresh
      (t⊢ , tʷ)
  widening-seal-spine-overlap⊥ {C = C} {α = α} wfΣ α↦★
      seal-ok (wp-inst p) sp fresh (cast-inst hC occC t⊢ , inst tᵍ) =
    widening-seal-spine-overlap⊥
      (StoreDetWf-inst wfΣ)
      (there (∈-renameStoreᵗ suc α↦★))
      seal-ok
      p
      (spine-map-right suc (spine-map-left suc sp))
      (trans (occurs-raise zero α C) fresh)
      (t⊢ , instSafe→widening tᵍ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-seq t⊢ (cast-tag hG gG okG) ,
                ((tʷ ︔ gG′ !))) =
    widening-cross-ground-source-all⊥ gG (t⊢ , strictCrossʷ→cross tʷ)
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-id hA ok , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-seal hA α∈Σ ok , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p)
      sp fresh (cast-gen hA occ t⊢ , cross ())
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-all p) sp fresh
      (cast-seq (cast-inst hC occC t⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag tᵍ) =
    widen-path-star-spine⊥ (wp-all p) sp
  widening-seal-spine-overlap⊥ wfΣ α↦★ seal-ok (wp-inst p) sp fresh
      (cast-seq (cast-inst hC occC t⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag tᵍ) =
    widen-path-star-spine⊥ (wp-inst p) sp

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
-- Canonical identity narrowings/widenings
------------------------------------------------------------------------

idModeAllowed-true : (m : Mode) → idModeAllowed m ≡ true
idModeAllowed-true id-only = refl
idModeAllowed-true tag-or-id = refl
idModeAllowed-true seal-or-id = refl

idTyAllowed-true : (μ : ModeEnv) → (A : Ty) → idTyAllowed μ A ≡ true
idTyAllowed-true μ (＇ α) = idModeAllowed-true (μ α)
idTyAllowed-true μ (‵ ι) = refl
idTyAllowed-true μ ★ = refl
idTyAllowed-true μ (A ⇒ B)
    rewrite idTyAllowed-true μ A | idTyAllowed-true μ B =
  refl
idTyAllowed-true μ (`∀ A) = idTyAllowed-true (extᵈ μ) A

mutual
  id-narrowingᵐ :
    ∀ {μ Δ Σ A} →
    WfTy Δ A →
    ∃[ c ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ A
  id-narrowingᵐ {μ = μ} (wfVar {X = α} α<Δ) =
    id (＇ α) ,
    cast-id (wfVar α<Δ) (idTyAllowed-true μ (＇ α)) ,
    cross (id-＇ α)
  id-narrowingᵐ {μ = μ} (wfBase {ι = ι}) =
    id (‵ ι) , cast-id wfBase refl , cross (id-‵ ι)
  id-narrowingᵐ {μ = μ} wf★ =
    id ★ , cast-id wf★ refl , id★
  id-narrowingᵐ {μ = μ} {Σ = Σ} (wf⇒ hA hB) with
      id-wideningᵐ {μ = μ} {Σ = Σ} hA |
      id-narrowingᵐ {μ = μ} {Σ = Σ} hB
  id-narrowingᵐ {μ = μ} {Σ = Σ} (wf⇒ hA hB) |
      s , s⊑ | t , t⊒ =
    s ↦ t , cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
    cross (proj₂ s⊑ ↦ proj₂ t⊒)
  id-narrowingᵐ {μ = μ} {Σ = Σ} (wf∀ hA) with
      id-narrowingᵐ {μ = extᵈ μ} {Σ = ⟰ᵗ Σ} hA
  id-narrowingᵐ {μ = μ} {Σ = Σ} (wf∀ hA) | s , s⊒ =
    `∀ s , cast-all (proj₁ s⊒) , cross (`∀ (proj₂ s⊒))

  id-wideningᵐ :
    ∀ {μ Δ Σ A} →
    WfTy Δ A →
    ∃[ c ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ A
  id-wideningᵐ {μ = μ} (wfVar {X = α} α<Δ) =
    id (＇ α) ,
    cast-id (wfVar α<Δ) (idTyAllowed-true μ (＇ α)) ,
    cross (id-＇ α)
  id-wideningᵐ {μ = μ} (wfBase {ι = ι}) =
    id (‵ ι) , cast-id wfBase refl , cross (id-‵ ι)
  id-wideningᵐ {μ = μ} wf★ =
    id ★ , cast-id wf★ refl , id★
  id-wideningᵐ {μ = μ} {Σ = Σ} (wf⇒ hA hB) with
      id-narrowingᵐ {μ = μ} {Σ = Σ} hA |
      id-wideningᵐ {μ = μ} {Σ = Σ} hB
  id-wideningᵐ {μ = μ} {Σ = Σ} (wf⇒ hA hB) |
      s , s⊒ | t , t⊑ =
    s ↦ t , cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
    cross (proj₂ s⊒ ↦ proj₂ t⊑)
  id-wideningᵐ {μ = μ} {Σ = Σ} (wf∀ hA) with
      id-wideningᵐ {μ = extᵈ μ} {Σ = ⟰ᵗ Σ} hA
  id-wideningᵐ {μ = μ} {Σ = Σ} (wf∀ hA) | s , s⊑ =
    `∀ s , cast-all (proj₁ s⊑) , cross (`∀ (proj₂ s⊑))

id-cross-narrowingᵐ :
  ∀ {μ Δ Σ G} →
  Ground G →
  WfTy Δ G →
  ∃[ c ] (μ ∣ Δ ∣ Σ ⊢ c ∶ G =⇒ G) × CrossNarrowing c
id-cross-narrowingᵐ {μ = μ} (＇ α) hG =
  id (＇ α) , cast-id hG (idTyAllowed-true μ (＇ α)) , id-＇ α
id-cross-narrowingᵐ (‵ ι) hG =
  id (‵ ι) , cast-id hG refl , id-‵ ι
id-cross-narrowingᵐ ★⇒★ hG =
  id ★ ↦ id ★ ,
  cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
  id★ ↦ id★

id-cross-wideningᵐ :
  ∀ {μ Δ Σ G} →
  Ground G →
  WfTy Δ G →
  ∃[ c ] (μ ∣ Δ ∣ Σ ⊢ c ∶ G =⇒ G) × CrossWidening c
id-cross-wideningᵐ {μ = μ} (＇ α) hG =
  id (＇ α) , cast-id hG (idTyAllowed-true μ (＇ α)) , id-＇ α
id-cross-wideningᵐ (‵ ι) hG =
  id (‵ ι) , cast-id hG refl , id-‵ ι
id-cross-wideningᵐ ★⇒★ hG =
  id ★ ↦ id ★ ,
  cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
  id★ ↦ id★

strictⁿ-id⊥ : ∀ {A} → StrictNarrowing (id A) → ⊥
strictⁿ-id⊥ (strict-crossⁿ ())

strictʷ-id⊥ : ∀ {A} → StrictWidening (id A) → ⊥
strictʷ-id⊥ (strict-crossʷ ())

strictCrossⁿ-id⊥ : ∀ {A} → StrictCrossNarrowing (id A) → ⊥
strictCrossⁿ-id⊥ ()

strictCrossʷ-id⊥ : ∀ {A} → StrictCrossWidening (id A) → ⊥
strictCrossʷ-id⊥ ()

mutual
  strictⁿ≢idⁿ :
    ∀ {μ Δ Σ A c} →
    (hA : WfTy Δ A) →
    StrictNarrowing c →
    c ≢ proj₁ (id-narrowingᵐ {μ = μ} {Σ = Σ} hA)
  strictⁿ≢idⁿ (wfVar α<Δ) sⁿ refl = strictⁿ-id⊥ sⁿ
  strictⁿ≢idⁿ wfBase sⁿ refl = strictⁿ-id⊥ sⁿ
  strictⁿ≢idⁿ wf★ sⁿ refl = strictⁿ-id⊥ sⁿ
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-crossⁿ (cn-funˡ sʷ tⁿ)) refl =
    strictʷ≢idʷ hA sʷ refl
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-crossⁿ (cn-funʳ sʷ tⁿ)) refl =
    strictⁿ≢idⁿ hB tⁿ refl
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-gen sⁿ) ()
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-untag gG) ()
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-untag-seq gG gⁿ) ()
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-seal A α) ()
  strictⁿ≢idⁿ (wf⇒ hA hB) (strict-seal-seq sⁿ α) ()
  strictⁿ≢idⁿ (wf∀ hA) (strict-crossⁿ (cn-all sⁿ)) refl =
    strictⁿ≢idⁿ hA sⁿ refl
  strictⁿ≢idⁿ (wf∀ hA) (strict-gen sⁿ) ()
  strictⁿ≢idⁿ (wf∀ hA) (strict-untag gG) ()
  strictⁿ≢idⁿ (wf∀ hA) (strict-untag-seq gG gⁿ) ()
  strictⁿ≢idⁿ (wf∀ hA) (strict-seal A α) ()
  strictⁿ≢idⁿ (wf∀ hA) (strict-seal-seq sⁿ α) ()

  strictʷ≢idʷ :
    ∀ {μ Δ Σ A c} →
    (hA : WfTy Δ A) →
    StrictWidening c →
    c ≢ proj₁ (id-wideningᵐ {μ = μ} {Σ = Σ} hA)
  strictʷ≢idʷ (wfVar α<Δ) sʷ refl = strictʷ-id⊥ sʷ
  strictʷ≢idʷ wfBase sʷ refl = strictʷ-id⊥ sʷ
  strictʷ≢idʷ wf★ sʷ refl = strictʷ-id⊥ sʷ
  strictʷ≢idʷ (wf⇒ hA hB) (strict-crossʷ (cw-funˡ sⁿ tʷ)) refl =
    strictⁿ≢idⁿ hA sⁿ refl
  strictʷ≢idʷ (wf⇒ hA hB) (strict-crossʷ (cw-funʳ sⁿ tʷ)) refl =
    strictʷ≢idʷ hB tʷ refl
  strictʷ≢idʷ (wf⇒ hA hB) (strict-inst sʷ) ()
  strictʷ≢idʷ (wf⇒ hA hB) (strict-tag gG) ()
  strictʷ≢idʷ (wf⇒ hA hB) (strict-tag-seq gʷ gG) ()
  strictʷ≢idʷ (wf⇒ hA hB) (strict-unseal α A) ()
  strictʷ≢idʷ (wf⇒ hA hB) (strict-unseal-seq α sʷ) ()
  strictʷ≢idʷ (wf∀ hA) (strict-crossʷ (cw-all sʷ)) refl =
    strictʷ≢idʷ hA sʷ refl
  strictʷ≢idʷ (wf∀ hA) (strict-inst sʷ) ()
  strictʷ≢idʷ (wf∀ hA) (strict-tag gG) ()
  strictʷ≢idʷ (wf∀ hA) (strict-tag-seq gʷ gG) ()
  strictʷ≢idʷ (wf∀ hA) (strict-unseal α A) ()
  strictʷ≢idʷ (wf∀ hA) (strict-unseal-seq α sʷ) ()

strictCrossⁿ≢idGroundⁿ :
  ∀ {μ Δ Σ G c} →
  (gG : Ground G) →
  (hG : WfTy Δ G) →
  StrictCrossNarrowing c →
  c ≢ proj₁ (id-cross-narrowingᵐ {μ = μ} {Σ = Σ} gG hG)
strictCrossⁿ≢idGroundⁿ (＇ α) hG cⁿ refl = strictCrossⁿ-id⊥ cⁿ
strictCrossⁿ≢idGroundⁿ (‵ ι) hG cⁿ refl = strictCrossⁿ-id⊥ cⁿ
strictCrossⁿ≢idGroundⁿ {μ = μ} {Δ = Δ} {Σ = Σ} ★⇒★ hG
    (cn-funˡ sʷ tⁿ) refl =
  strictʷ≢idʷ {μ = μ} {Δ = Δ} {Σ = Σ} {A = ★} wf★ sʷ refl
strictCrossⁿ≢idGroundⁿ {μ = μ} {Δ = Δ} {Σ = Σ} ★⇒★ hG
    (cn-funʳ sʷ tⁿ) refl =
  strictⁿ≢idⁿ {μ = μ} {Δ = Δ} {Σ = Σ} {A = ★} wf★ tⁿ refl

strictCrossʷ≢idGroundʷ :
  ∀ {μ Δ Σ G c} →
  (gG : Ground G) →
  (hG : WfTy Δ G) →
  StrictCrossWidening c →
  c ≢ proj₁ (id-cross-wideningᵐ {μ = μ} {Σ = Σ} gG hG)
strictCrossʷ≢idGroundʷ (＇ α) hG cʷ refl = strictCrossʷ-id⊥ cʷ
strictCrossʷ≢idGroundʷ (‵ ι) hG cʷ refl = strictCrossʷ-id⊥ cʷ
strictCrossʷ≢idGroundʷ {μ = μ} {Δ = Δ} {Σ = Σ} ★⇒★ hG
    (cw-funˡ sⁿ tʷ) refl =
  strictⁿ≢idⁿ {μ = μ} {Δ = Δ} {Σ = Σ} {A = ★} wf★ sⁿ refl
strictCrossʷ≢idGroundʷ {μ = μ} {Δ = Δ} {Σ = Σ} ★⇒★ hG
    (cw-funʳ sⁿ tʷ) refl =
  strictʷ≢idʷ {μ = μ} {Δ = Δ} {Σ = Σ} {A = ★} wf★ tʷ refl

------------------------------------------------------------------------
-- Mode-indexed narrowing/widening determinacy under StoreDetWf
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  narrowing-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
    s ≡ t
  narrowing-determinedᵐ-det wfΣ
      (cast-seal hA α∈Σ ok , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-unseal hA α∈Σ ok , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-tag hG gG ok , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-untag hG gG ok , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-inst hB occ c⊢ , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ t⊢ , cross ()) u⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-id {A = A ⇒ B} hA ok , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ
      (cast-id {A = `∀ A} hA ok , cross ()) t⊒
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-seal hA α∈Σ ok , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-unseal hA α∈Σ ok , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-tag hG gG ok , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-untag hG gG ok , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-inst hB occ c⊢ , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-seq t⊢ u⊢ , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-id {A = A ⇒ B} hA ok , cross ())
  narrowing-determinedᵐ-det wfΣ s⊒
      (cast-id {A = `∀ A} hA ok , cross ())
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , cross (id-＇ _))
      (cast-id hA′ ok′ , cross (id-＇ _)) =
    refl
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , cross (id-‵ _))
      (cast-id hA′ ok′ , cross (id-‵ _)) =
    refl
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , id★)
      (cast-id hA′ ok′ , id★) =
    refl
  narrowing-determinedᵐ-det {μ = μ} wfΣ
      (cast-id {A = ＇ α} hA id-ok , cross (id-＇ _))
      (cast-seal hB α∈Σ seal-ok , sealⁿ .(＇ α) .α) =
    ⊥-elim
      (narrowing-var-to-older⊥ {μ = μ} {c = seal (＇ α) α}
        {α = α} {B = ＇ α}
        wfΣ (wfOlder wfΣ α∈Σ)
        (cast-seal {μ = μ} hB α∈Σ seal-ok , sealⁿ (＇ α) α))
  narrowing-determinedᵐ-det {μ = μ} wfΣ
      (cast-seal hA α∈Σ seal-ok , sealⁿ .(＇ α) .α)
      (cast-id {A = ＇ α} hB id-ok , cross (id-＇ _)) =
    ⊥-elim
      (narrowing-var-to-older⊥ {μ = μ} {c = seal (＇ α) α}
        {α = α} {B = ＇ α}
        wfΣ (wfOlder wfΣ α∈Σ)
        (cast-seal {μ = μ} hA α∈Σ seal-ok , sealⁿ (＇ α) α))
  narrowing-determinedᵐ-det wfΣ
      (cast-seal hA α∈Σ seal-ok , sealⁿ _ _)
      (cast-seal hB β∈Σ β-ok , sealⁿ _ _)
      rewrite unique wfΣ α∈Σ β∈Σ =
    refl
  narrowing-determinedᵐ-det wfΣ
      (cast-seal hA α∈Σ seal-ok , sealⁿ _ _)
      (cast-seq (cast-untag hG gG okG) t⊢ , _？︔_ gG′ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (t⊢ , strictCrossⁿ→cross tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-seal hA α∈Σ seal-ok , sealⁿ _ _) =
    ⊥-elim
      (narrowing-cross-ground-target-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (s⊢ , strictCrossⁿ→cross sᶜ))
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seal hA α∈Σ seal-ok , sealⁿ _ _)
      (cast-seq t⊢ (cast-seal hB β∈Σ β-ok) , tⁿ ︔seal _)
      rewrite unique wfΣ α∈Σ β∈Σ
      with narrowing-determinedᵐ-det
             wfΣ
             (t⊢ , strictⁿ→narrow tⁿ)
             (proj₂ (id-narrowingᵐ {μ = μ} {Σ = Σ} hA))
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seal hA α∈Σ seal-ok , sealⁿ _ _)
      (cast-seq t⊢ (cast-seal hB β∈Σ β-ok) , tⁿ ︔seal _)
      | eq =
    ⊥-elim (strictⁿ≢idⁿ {μ = μ} {Σ = Σ} hA tⁿ eq)
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ α-ok) , sⁿ ︔seal _)
      (cast-seal hB β∈Σ β-ok , sealⁿ _ _)
      rewrite unique wfΣ α∈Σ β∈Σ
      with narrowing-determinedᵐ-det
             wfΣ
             (s⊢ , strictⁿ→narrow sⁿ)
             (proj₂ (id-narrowingᵐ {μ = μ} {Σ = Σ} hB))
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ α-ok) , sⁿ ︔seal _)
      (cast-seal hB β∈Σ β-ok , sealⁿ _ _)
      | eq =
    ⊥-elim (strictⁿ≢idⁿ {μ = μ} {Σ = Σ} hB sⁿ eq)
  narrowing-determinedᵐ-det wfΣ
      (cast-seal {α = α} hA α∈Σ seal-ok , sealⁿ .★ .α)
      (cast-untag hG (＇ .α) tag-ok , untag (＇ .α)) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  narrowing-determinedᵐ-det wfΣ
      (cast-untag hG (＇ α) tag-ok , untag (＇ .α))
      (cast-seal {α = .α} hA α∈Σ seal-ok , sealⁿ .★ .α) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  narrowing-determinedᵐ-det wfΣ
      (cast-untag hG gG okG , untag gG′)
      (cast-untag hH gH okH , untag gH′) =
    refl
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-untag hG gG okG , untag gG′)
      (cast-seq (cast-untag hH gH okH) t⊢ , _？︔_ gH′ tᶜ)
      with narrowing-cross-ground-source-determinedᵐ-det
             wfΣ gH gG
             (t⊢ , strictCrossⁿ→cross tᶜ)
             (proj₂ (id-cross-narrowingᵐ {μ = μ} {Σ = Σ} gG hG))
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-untag hG gG okG , untag gG′)
      (cast-seq (cast-untag hH gH okH) t⊢ , _？︔_ gH′ tᶜ)
      | refl , eq =
    ⊥-elim
      (strictCrossⁿ≢idGroundⁿ {μ = μ} {Σ = Σ} gG hG tᶜ eq)
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-untag hH gH okH , untag gH′)
      with narrowing-cross-ground-source-determinedᵐ-det
             wfΣ gG gH
             (s⊢ , strictCrossⁿ→cross sᶜ)
             (proj₂ (id-cross-narrowingᵐ {μ = μ} {Σ = Σ} gH hH))
  narrowing-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-untag hH gH okH , untag gH′)
      | refl , eq =
    ⊥-elim
      (strictCrossⁿ≢idGroundⁿ {μ = μ} {Σ = Σ} gH hH sᶜ eq)
  narrowing-determinedᵐ-det wfΣ
      (cast-untag hG (＇ α) tag-ok , untag (＇ .α))
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , sⁿ ︔seal _) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , sⁿ ︔seal _)
      (cast-untag hG (＇ α) tag-ok , untag (＇ .α)) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  narrowing-determinedᵐ-det wfΣ
      (cast-id {A = ＇ α} hA id-ok , cross (id-＇ _))
      (cast-seq t⊢ (cast-seal hB α∈Σ seal-ok) , tⁿ ︔seal _) =
    ⊥-elim
      (narrowing-var-to-older⊥
        wfΣ (wfOlder wfΣ α∈Σ) (t⊢ , strictⁿ→narrow tⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-id hA ok , id★)
      (cast-seq (cast-untag hG gG okG) t⊢ , _？︔_ gG′ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-star⊥
        gG (t⊢ , strictCrossⁿ→cross tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , cross (_↦_ sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , cross (_↦_ sʷ′ tⁿ′)) =
    cong₂ _↦_
      (widening-determinedᵐ-det wfΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-det wfΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sⁿ))
      (cast-all t⊢ , cross (`∀ tⁿ)) =
    cong `∀
      (narrowing-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sⁿ)
        (t⊢ , tⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sⁿ))
      (cast-gen hA occ t⊢ , gen tᵍ) =
    ⊥-elim
      (narrowing-all-gen-overlap⊥ wfΣ occ (s⊢ , sⁿ)
        (t⊢ , genSafe→narrowing tᵍ))
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , gen sᵍ)
      (cast-all t⊢ , cross (`∀ tⁿ)) =
    ⊥-elim
      (narrowing-all-gen-overlap⊥ wfΣ occ (t⊢ , tⁿ)
        (s⊢ , genSafe→narrowing sᵍ))
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , gen sᵍ)
      (cast-gen hA′ occ′ t⊢ , gen tᵍ) =
    cong (gen _)
      (narrowing-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , genSafe→narrowing sᵍ)
        (t⊢ , genSafe→narrowing tᵍ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , _？︔_ gH′ tᶜ)
      with narrowing-cross-ground-source-determinedᵐ-det
             wfΣ gG gH
             (s⊢ , strictCrossⁿ→cross sᶜ)
             (t⊢ , strictCrossⁿ→cross tᶜ)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , _？︔_ gH′ tᶜ)
      | refl , eq =
    cong₂ _︔_ refl eq
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-id hA ok , id★) =
    ⊥-elim
      (narrowing-cross-ground-target-star⊥
        gG (s⊢ , strictCrossⁿ→cross sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-gen hA occ t⊢ , gen tⁿ) =
    ⊥-elim
      (narrowing-cross-ground-target-all⊥
        gG (s⊢ , strictCrossⁿ→cross sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sⁿ))
      (cast-seq () t⊢ , _？︔_ gG′ tᶜ)
  narrowing-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sⁿ))
      (cast-seq t⊢ () , tⁿ ︔seal _)
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , gen sⁿ)
      (cast-seq (cast-untag hG gG okG) t⊢ , _？︔_ gG′ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-all⊥
        gG (t⊢ , strictCrossⁿ→cross tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , gen sⁿ)
      (cast-seq t⊢ () , tⁿ ︔seal _)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-seq t⊢ (cast-seal hA α∈Σ seal-ok) , tⁿ ︔seal _) =
    ⊥-elim
      (narrowing-cross-ground-target-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (s⊢ , strictCrossⁿ→cross sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ α-ok) , sⁿ ︔seal _)
      (cast-seq t⊢ (cast-seal hB β∈Σ β-ok) , tⁿ ︔seal _)
      rewrite unique wfΣ α∈Σ β∈Σ =
    cong₂ _︔_
      (narrowing-determinedᵐ-det
        wfΣ (s⊢ , strictⁿ→narrow sⁿ) (t⊢ , strictⁿ→narrow tⁿ))
      refl
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , sⁿ ︔seal _)
      (cast-id {A = ＇ α} hB id-ok , cross (id-＇ _)) =
    ⊥-elim
      (narrowing-var-to-older⊥
        wfΣ (wfOlder wfΣ α∈Σ) (s⊢ , strictⁿ→narrow sⁿ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , sⁿ ︔seal _)
      (cast-seq (cast-untag hG gG okG) t⊢ , _？︔_ gG′ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (t⊢ , strictCrossⁿ→cross tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , _？︔_ gG′ sᶜ)
      (cast-seq (cast-untag hH ★⇒★ okH)
                (cast-gen hA occ t⊢) ,
       fun-untag-gen tᵍ) =
    ⊥-elim
      (narrowing-cross-ground-target-all⊥
        gG (s⊢ , strictCrossⁿ→cross sᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hA occ s⊢) ,
       fun-untag-gen sᵍ)
      (cast-gen hB occB t⊢ , gen tᵍ) =
    ⊥-elim (genSafe-star-source⊥ t⊢ tᵍ)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hA occ s⊢) ,
       fun-untag-gen sᵍ)
      (cast-untag hH () okH , untag gH)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hA occ s⊢) ,
       fun-untag-gen sᵍ)
      (cast-seq (cast-untag hH gH okH) t⊢ , _？︔_ gH′ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-all⊥
        gH (t⊢ , strictCrossⁿ→cross tᶜ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hA occ s⊢) ,
       fun-untag-gen sᵍ)
      (cast-seq (cast-untag hH ★⇒★ okH)
                (cast-gen hB occB t⊢) ,
       fun-untag-gen tᵍ) =
    cong (λ c → ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) c)
      (narrowing-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , genSafe→narrowing sᵍ)
        (t⊢ , genSafe→narrowing tᵍ))
  narrowing-determinedᵐ-det wfΣ
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hA occ s⊢) ,
       fun-untag-gen sᵍ)
      (cast-seq t⊢ () , tⁿ ︔seal α)
  narrowing-determinedᵐ-det wfΣ
      (cast-seq s⊢ () , sⁿ ︔seal α)
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hA occ t⊢) ,
       fun-untag-gen tᵍ)
  narrowing-determinedᵐ-det wfΣ
      (cast-untag hG () okG , untag gG)
      (cast-seq (cast-untag hH ★⇒★ okH)
                (cast-gen hA occ t⊢) ,
       fun-untag-gen tᵍ)
  narrowing-determinedᵐ-det wfΣ
      (cast-gen hA occ s⊢ , gen sᵍ)
      (cast-seq (cast-untag hG ★⇒★ okG)
                (cast-gen hB occB t⊢) ,
       fun-untag-gen tᵍ) =
    ⊥-elim (genSafe-star-source⊥ s⊢ sᵍ)

  narrowing-cross-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B) × CrossNarrowing s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ B) × CrossNarrowing t →
    s ≡ t
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , id-＇ _)
      (cast-id hA′ ok′ , id-＇ _) =
    refl
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , id-‵ _)
      (cast-id hA′ ok′ , id-‵ _) =
    refl
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , _↦_ sʷ tⁿ)
      (cast-fun s⊢′ t⊢′ , _↦_ sʷ′ tⁿ′) =
    cong₂ _↦_
      (widening-determinedᵐ-det wfΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-det wfΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))
  narrowing-cross-determinedᵐ-det wfΣ
      (cast-all s⊢ , `∀ sⁿ)
      (cast-all t⊢ , `∀ tⁿ) =
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
      (cast-id hA ok , id-＇ _)
      (cast-id hA′ ok′ , id-＇ _) =
    refl , refl
  narrowing-cross-ground-source-determinedᵐ-det wfΣ
      (‵ ι) (‵ .ι)
      (cast-id hA ok , id-‵ _)
      (cast-id hA′ ok′ , id-‵ _) =
    refl , refl
  narrowing-cross-ground-source-determinedᵐ-det wfΣ
      ★⇒★ ★⇒★
      (cast-fun s⊢ t⊢ , _↦_ sʷ tⁿ)
      (cast-fun s⊢′ t⊢′ , _↦_ sʷ′ tⁿ′) =
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
      (cast-seal hA α∈Σ ok , cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-unseal hA α∈Σ ok , cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-tag hG gG ok , cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-untag hG gG ok , cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-gen hA occ c⊢ , cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ t⊢ , cross ()) u⊑
  widening-determinedᵐ-det wfΣ
      (cast-id {A = A ⇒ B} hA ok , cross ()) t⊑
  widening-determinedᵐ-det wfΣ
      (cast-id {A = `∀ A} hA ok , cross ()) t⊑
  widening-determinedᵐ-det wfΣ s⊑
      (cast-seal hA α∈Σ ok , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-unseal hA α∈Σ ok , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-tag hG gG ok , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-untag hG gG ok , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-gen hA occ c⊢ , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-seq t⊢ u⊢ , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-id {A = A ⇒ B} hA ok , cross ())
  widening-determinedᵐ-det wfΣ s⊑
      (cast-id {A = `∀ A} hA ok , cross ())
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , cross (id-＇ _))
      (cast-id hA′ ok′ , cross (id-＇ _)) =
    refl
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , cross (id-‵ _))
      (cast-id hA′ ok′ , cross (id-‵ _)) =
    refl
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , id★)
      (cast-id hA′ ok′ , id★) =
    refl
  widening-determinedᵐ-det {μ = μ} wfΣ
      (cast-id {A = ＇ α} hA id-ok , cross (id-＇ _))
      (cast-unseal hB α∈Σ seal-ok , unsealʷ .α .(＇ α)) =
    ⊥-elim
      (widening-older-to-var⊥ {μ = μ} {c = id (＇ α)}
        {α = α} {A = ＇ α}
        wfΣ (wfOlder wfΣ α∈Σ)
        (cast-id {μ = μ} hA id-ok , cross (id-＇ _)))
  widening-determinedᵐ-det {μ = μ} wfΣ
      (cast-unseal hA α∈Σ seal-ok , unsealʷ .α .(＇ α))
      (cast-id {A = ＇ α} hB id-ok , cross (id-＇ _)) =
    ⊥-elim
      (widening-older-to-var⊥ {μ = μ} {c = id (＇ α)}
        {α = α} {A = ＇ α}
        wfΣ (wfOlder wfΣ α∈Σ)
        (cast-id {μ = μ} hB id-ok , cross (id-＇ _)))
  widening-determinedᵐ-det wfΣ
      (cast-unseal hA α∈Σ seal-ok , unsealʷ _ _)
      (cast-unseal hB β∈Σ β-ok , unsealʷ _ _)
      rewrite unique wfΣ α∈Σ β∈Σ =
    refl
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-unseal hA α∈Σ seal-ok , unsealʷ _ _)
      (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ , unseal︔_ _ tʷ)
      rewrite unique wfΣ α∈Σ β∈Σ
      with widening-determinedᵐ-det
             wfΣ
             (t⊢ , strictʷ→widen tʷ)
             (proj₂ (id-wideningᵐ {μ = μ} {Σ = Σ} hA))
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-unseal hA α∈Σ seal-ok , unsealʷ _ _)
      (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ , unseal︔_ _ tʷ)
      | eq =
    ⊥-elim (strictʷ≢idʷ {μ = μ} {Σ = Σ} hA tʷ eq)
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq (cast-unseal hA α∈Σ α-ok) s⊢ , unseal︔_ _ sʷ)
      (cast-unseal hB β∈Σ β-ok , unsealʷ _ _)
      rewrite unique wfΣ α∈Σ β∈Σ
      with widening-determinedᵐ-det
             wfΣ
             (s⊢ , strictʷ→widen sʷ)
             (proj₂ (id-wideningᵐ {μ = μ} {Σ = Σ} hB))
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq (cast-unseal hA α∈Σ α-ok) s⊢ , unseal︔_ _ sʷ)
      (cast-unseal hB β∈Σ β-ok , unsealʷ _ _)
      | eq =
    ⊥-elim (strictʷ≢idʷ {μ = μ} {Σ = Σ} hB sʷ eq)
  widening-determinedᵐ-det wfΣ
      (cast-unseal hA α∈Σ seal-ok , unsealʷ _ _)
      (cast-seq t⊢ (cast-tag hG gG okG) , ((tᶜ ︔ gG′ !))) =
    ⊥-elim
      (widening-cross-ground-source-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (t⊢ , strictCrossʷ→cross tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-unseal hA α∈Σ seal-ok , unsealʷ _ _) =
    ⊥-elim
      (widening-cross-ground-source-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (s⊢ , strictCrossʷ→cross sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-unseal {α = α} hA α∈Σ seal-ok , unsealʷ .α .★)
      (cast-tag hG (＇ .α) tag-ok , tag (＇ .α)) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  widening-determinedᵐ-det wfΣ
      (cast-tag hG (＇ α) tag-ok , tag (＇ .α))
      (cast-unseal {α = .α} hA α∈Σ seal-ok , unsealʷ .α .★) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  widening-determinedᵐ-det wfΣ
      (cast-tag hG gG okG , tag gG′)
      (cast-tag hH gH okH , tag gH′) =
    refl
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-tag hG gG okG , tag gG′)
      (cast-seq t⊢ (cast-tag hH gH okH) , ((tᶜ ︔ gH′ !)))
      with widening-cross-ground-target-determinedᵐ-det
             wfΣ gG gH
             (proj₂ (id-cross-wideningᵐ {μ = μ} {Σ = Σ} gG hG))
             (t⊢ , strictCrossʷ→cross tᶜ)
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-tag hG gG okG , tag gG′)
      (cast-seq t⊢ (cast-tag hH gH okH) , ((tᶜ ︔ gH′ !)))
      | refl , eq =
    ⊥-elim
      (strictCrossʷ≢idGroundʷ {μ = μ} {Σ = Σ} gG hG tᶜ (sym eq))
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-tag hH gH okH , tag gH′)
      with widening-cross-ground-target-determinedᵐ-det
             wfΣ gG gH
             (s⊢ , strictCrossʷ→cross sᶜ)
             (proj₂ (id-cross-wideningᵐ {μ = μ} {Σ = Σ} gH hH))
  widening-determinedᵐ-det {μ = μ} {Σ = Σ} wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-tag hH gH okH , tag gH′)
      | refl , eq =
    ⊥-elim
      (strictCrossʷ≢idGroundʷ {μ = μ} {Σ = Σ} gH hH sᶜ eq)
  widening-determinedᵐ-det wfΣ
      (cast-tag hG (＇ α) tag-ok , tag (＇ .α))
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , unseal︔_ _ sʷ) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , unseal︔_ _ sʷ)
      (cast-tag hG (＇ α) tag-ok , tag (＇ .α)) =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  widening-determinedᵐ-det wfΣ
      (cast-id {A = ＇ α} hA id-ok , cross (id-＇ _))
      (cast-seq (cast-unseal hB α∈Σ seal-ok) t⊢ , unseal︔_ _ tʷ) =
    ⊥-elim
      (widening-older-to-var⊥
        wfΣ (wfOlder wfΣ α∈Σ) (t⊢ , strictʷ→widen tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-id hA ok , id★)
      (cast-seq t⊢ (cast-tag hG gG okG) , ((tᶜ ︔ gG′ !))) =
    ⊥-elim
      (widening-cross-ground-source-star⊥
        gG (t⊢ , strictCrossʷ→cross tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , cross (_↦_ sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , cross (_↦_ sⁿ′ tʷ′)) =
    cong₂ _↦_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-det wfΣ (t⊢ , tʷ) (t⊢′ , tʷ′))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-all t⊢ , cross (`∀ tʷ)) =
    cong `∀
      (widening-determinedᵐ-det
        (StoreDetWf-⟰ᵗ wfΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-inst hB occ t⊢ , inst tᵍ) =
    ⊥-elim
      (widening-all-inst-overlap-det⊥ wfΣ occ (s⊢ , sʷ)
        (t⊢ , instSafe→widening tᵍ))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-seq t⊢ () , ((tᶜ ︔ gG′ !)))
  widening-determinedᵐ-det wfΣ
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-seq () t⊢ , unseal︔_ _ tʷ)
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , inst sᵍ)
      (cast-inst hB′ occ′ t⊢ , inst tᵍ) =
    cong (inst _)
      (widening-determinedᵐ-det
        (StoreDetWf-inst wfΣ)
        (s⊢ , instSafe→widening sᵍ)
        (t⊢ , instSafe→widening tᵍ))
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , inst sᵍ)
      (cast-all t⊢ , cross (`∀ tʷ)) =
    ⊥-elim
      (widening-all-inst-overlap-det⊥ wfΣ occ (t⊢ , tʷ)
        (s⊢ , instSafe→widening sᵍ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-seq t⊢ (cast-tag hH gH okH) , ((tᶜ ︔ gH′ !)))
      with widening-cross-ground-target-determinedᵐ-det
             wfΣ gG gH
             (s⊢ , strictCrossʷ→cross sᶜ)
             (t⊢ , strictCrossʷ→cross tᶜ)
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-seq t⊢ (cast-tag hH gH okH) , ((tᶜ ︔ gH′ !)))
      | refl , eq =
    cong₂ _︔_ eq refl
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-id hA ok , id★) =
    ⊥-elim
      (widening-cross-ground-source-star⊥
        gG (s⊢ , strictCrossʷ→cross sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-seq (cast-unseal hA α∈Σ seal-ok) t⊢ , unseal︔_ _ tʷ) =
    ⊥-elim
      (widening-cross-ground-source-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (s⊢ , strictCrossʷ→cross sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-inst hB occ t⊢ , inst tʷ) =
    ⊥-elim
      (widening-cross-ground-source-all⊥
        gG (s⊢ , strictCrossʷ→cross sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ α-ok) s⊢ , unseal︔_ _ sʷ)
      (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ , unseal︔_ _ tʷ)
      rewrite unique wfΣ α∈Σ β∈Σ =
    cong₂ _︔_ refl
      (widening-determinedᵐ-det
        wfΣ (s⊢ , strictʷ→widen sʷ) (t⊢ , strictʷ→widen tʷ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , unseal︔_ _ sʷ)
      (cast-id {A = ＇ α} hB id-ok , cross (id-＇ _)) =
    ⊥-elim
      (widening-older-to-var⊥
        wfΣ (wfOlder wfΣ α∈Σ) (s⊢ , strictʷ→widen sʷ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , unseal︔_ _ sʷ)
      (cast-seq t⊢ (cast-tag hG gG okG) , ((tᶜ ︔ gG′ !))) =
    ⊥-elim
      (widening-cross-ground-source-seal-var⊥
        wfΣ gG okG α∈Σ seal-ok
        (t⊢ , strictCrossʷ→cross tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , inst sʷ)
      (cast-seq t⊢ (cast-tag hG gG okG) , ((tᶜ ︔ gG′ !))) =
    ⊥-elim
      (widening-cross-ground-source-all⊥
        gG (t⊢ , strictCrossʷ→cross tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-inst hB occ s⊢ , inst sʷ)
      (cast-seq () t⊢ , unseal︔_ _ tʷ)
  widening-determinedᵐ-det wfΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , ((sᶜ ︔ gG′ !)))
      (cast-seq (cast-inst hB occ t⊢)
                (cast-tag hH ★⇒★ okH) ,
       inst-fun-tag tᵍ) =
    ⊥-elim
      (widening-cross-ground-source-all⊥
        gG (s⊢ , strictCrossʷ→cross sᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-inst hA occA s⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag sᵍ)
      (cast-inst hB occB t⊢ , inst tᵍ) =
    ⊥-elim (instSafe-star-target⊥ t⊢ tᵍ)
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-inst hA occA s⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag sᵍ)
      (cast-tag hH () okH , tag gH)
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-inst hA occA s⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag sᵍ)
      (cast-seq t⊢ (cast-tag hH gH okH) , ((tᶜ ︔ gH′ !))) =
    ⊥-elim
      (widening-cross-ground-source-all⊥
        gH (t⊢ , strictCrossʷ→cross tᶜ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-inst hA occA s⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag sᵍ)
      (cast-seq (cast-inst hB occB t⊢)
                (cast-tag hH ★⇒★ okH) ,
       inst-fun-tag tᵍ) =
    cong (λ c → inst (★ ⇒ ★) c ︔ ((★ ⇒ ★) !))
      (widening-determinedᵐ-det
        (StoreDetWf-inst wfΣ)
        (s⊢ , instSafe→widening sᵍ)
        (t⊢ , instSafe→widening tᵍ))
  widening-determinedᵐ-det wfΣ
      (cast-seq (cast-inst hA occA s⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag sᵍ)
      (cast-seq () t⊢ , unseal︔_ α tʷ)
  widening-determinedᵐ-det wfΣ
      (cast-seq () s⊢ , unseal︔_ α sʷ)
      (cast-seq (cast-inst hA occA t⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag tᵍ)
  widening-determinedᵐ-det wfΣ
      (cast-tag hG () okG , tag gG)
      (cast-seq (cast-inst hA occA t⊢)
                (cast-tag hH ★⇒★ okH) ,
       inst-fun-tag tᵍ)
  widening-determinedᵐ-det wfΣ
      (cast-inst hA occA s⊢ , inst sᵍ)
      (cast-seq (cast-inst hB occB t⊢)
                (cast-tag hG ★⇒★ okG) ,
       inst-fun-tag tᵍ) =
    ⊥-elim (instSafe-star-target⊥ s⊢ sᵍ)

  widening-cross-determinedᵐ-det :
    ∀ {μ Δ Σ A B s t} →
    StoreDetWf Δ Σ →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B) × CrossWidening s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ B) × CrossWidening t →
    s ≡ t
  widening-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , id-＇ _)
      (cast-id hA′ ok′ , id-＇ _) =
    refl
  widening-cross-determinedᵐ-det wfΣ
      (cast-id hA ok , id-‵ _)
      (cast-id hA′ ok′ , id-‵ _) =
    refl
  widening-cross-determinedᵐ-det wfΣ
      (cast-fun s⊢ t⊢ , _↦_ sⁿ tʷ)
      (cast-fun s⊢′ t⊢′ , _↦_ sⁿ′ tʷ′) =
    cong₂ _↦_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-det wfΣ (t⊢ , tʷ) (t⊢′ , tʷ′))
  widening-cross-determinedᵐ-det wfΣ
      (cast-all s⊢ , `∀ sʷ)
      (cast-all t⊢ , `∀ tʷ) =
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
      (cast-id hA ok , id-＇ _)
      (cast-id hA′ ok′ , id-＇ _) =
    refl , refl
  widening-cross-ground-target-determinedᵐ-det wfΣ
      (‵ ι) (‵ .ι)
      (cast-id hA ok , id-‵ _)
      (cast-id hA′ ok′ , id-‵ _) =
    refl , refl
  widening-cross-ground-target-determinedᵐ-det wfΣ
      ★⇒★ ★⇒★
      (cast-fun s⊢ t⊢ , _↦_ sⁿ tʷ)
      (cast-fun s⊢′ t⊢′ , _↦_ sⁿ′ tʷ′) =
    refl ,
    cong₂ _↦_
      (narrowing-determinedᵐ-det wfΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-det wfΣ (t⊢ , tʷ) (t⊢′ , tʷ′))

store-narrowing-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
store-narrowing-determinedᵐ wfΣ =
  narrowing-determinedᵐ-det (StoreWf⇒det wfΣ)

store-widening-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
store-widening-determinedᵐ wfΣ =
  widening-determinedᵐ-det (StoreWf⇒det wfΣ)

narrowing-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
narrowing-determinedᵐ wfΣ =
  narrowing-determinedᵐ-det wfΣ

widening-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
widening-determinedᵐ wfΣ =
  widening-determinedᵐ-det wfΣ

------------------------------------------------------------------------
-- Cross-mode determinacy for compatible mode environments
------------------------------------------------------------------------

-- Determinacy across two DIFFERENT mode environments is false in
-- general: with Δ = 1 and Σ = (0 , ★) ∷ [], both `＇ 0 ？` (normal in
-- tag-or-idᵈ, by cast-untag and the witness `untag`) and `seal ★ 0`
-- (normal in seal-or-idᵈ, by cast-seal and the witness `sealⁿ`) inhabit
-- the endpoints ★ ⊒ ＇ 0.  The failure requires the two environments to
-- disagree tag-versus-seal at a variable, so we restrict to pointwise
-- compatible environments.  Compatible modes have a join in the mode≤
-- order, both typings relax into the join (`coercion-mode-relax`), and
-- the single-environment determinacy theorem closes the argument.

modeCompat : Mode → Mode → Bool
modeCompat id-only id-only = true
modeCompat id-only tag-or-id = true
modeCompat id-only seal-or-id = true
modeCompat tag-or-id id-only = true
modeCompat tag-or-id tag-or-id = true
modeCompat tag-or-id seal-or-id = false
modeCompat seal-or-id id-only = true
modeCompat seal-or-id tag-or-id = false
modeCompat seal-or-id seal-or-id = true

ModeEnvCompat : ModeEnv → ModeEnv → Set
ModeEnvCompat μ ν = ∀ X → modeCompat (μ X) (ν X) ≡ true

-- The (tag , seal) and (seal , tag) results below are junk values;
-- those inputs are excluded by ModeEnvCompat wherever the join is used.
modeJoin : Mode → Mode → Mode
modeJoin id-only id-only = id-only
modeJoin id-only tag-or-id = tag-or-id
modeJoin id-only seal-or-id = seal-or-id
modeJoin tag-or-id id-only = tag-or-id
modeJoin tag-or-id tag-or-id = tag-or-id
modeJoin tag-or-id seal-or-id = tag-or-id
modeJoin seal-or-id id-only = seal-or-id
modeJoin seal-or-id tag-or-id = seal-or-id
modeJoin seal-or-id seal-or-id = seal-or-id

modeEnvJoin : ModeEnv → ModeEnv → ModeEnv
modeEnvJoin μ ν X = modeJoin (μ X) (ν X)

modeIncl-joinˡ :
  ∀ {μ ν} →
  ModeEnvCompat μ ν →
  ModeIncl μ (modeEnvJoin μ ν)
modeIncl-joinˡ {μ} {ν} compat X with μ X | ν X | compat X
modeIncl-joinˡ {μ} {ν} compat X | id-only | id-only | _ = refl
modeIncl-joinˡ {μ} {ν} compat X | id-only | tag-or-id | _ = refl
modeIncl-joinˡ {μ} {ν} compat X | id-only | seal-or-id | _ = refl
modeIncl-joinˡ {μ} {ν} compat X | tag-or-id | id-only | _ = refl
modeIncl-joinˡ {μ} {ν} compat X | tag-or-id | tag-or-id | _ = refl
modeIncl-joinˡ {μ} {ν} compat X | tag-or-id | seal-or-id | ()
modeIncl-joinˡ {μ} {ν} compat X | seal-or-id | id-only | _ = refl
modeIncl-joinˡ {μ} {ν} compat X | seal-or-id | tag-or-id | ()
modeIncl-joinˡ {μ} {ν} compat X | seal-or-id | seal-or-id | _ = refl

modeIncl-joinʳ :
  ∀ {μ ν} →
  ModeEnvCompat μ ν →
  ModeIncl ν (modeEnvJoin μ ν)
modeIncl-joinʳ {μ} {ν} compat X with μ X | ν X | compat X
modeIncl-joinʳ {μ} {ν} compat X | id-only | id-only | _ = refl
modeIncl-joinʳ {μ} {ν} compat X | id-only | tag-or-id | _ = refl
modeIncl-joinʳ {μ} {ν} compat X | id-only | seal-or-id | _ = refl
modeIncl-joinʳ {μ} {ν} compat X | tag-or-id | id-only | _ = refl
modeIncl-joinʳ {μ} {ν} compat X | tag-or-id | tag-or-id | _ = refl
modeIncl-joinʳ {μ} {ν} compat X | tag-or-id | seal-or-id | ()
modeIncl-joinʳ {μ} {ν} compat X | seal-or-id | id-only | _ = refl
modeIncl-joinʳ {μ} {ν} compat X | seal-or-id | tag-or-id | ()
modeIncl-joinʳ {μ} {ν} compat X | seal-or-id | seal-or-id | _ = refl

compatible-narrowing-determinedᵐ :
  ∀ {μ ν Δ Σ A B s t} →
  ModeEnvCompat μ ν →
  StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  ν ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
compatible-narrowing-determinedᵐ compat wfΣ (s⊢ , sⁿ) (t⊢ , tⁿ) =
  narrowing-determinedᵐ wfΣ
    (coercion-mode-relax (modeIncl-joinˡ compat) s⊢ , sⁿ)
    (coercion-mode-relax (modeIncl-joinʳ compat) t⊢ , tⁿ)

compatible-widening-determinedᵐ :
  ∀ {μ ν Δ Σ A B s t} →
  ModeEnvCompat μ ν →
  StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  ν ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
compatible-widening-determinedᵐ compat wfΣ (s⊢ , sʷ) (t⊢ , tʷ) =
  widening-determinedᵐ wfΣ
    (coercion-mode-relax (modeIncl-joinˡ compat) s⊢ , sʷ)
    (coercion-mode-relax (modeIncl-joinʳ compat) t⊢ , tʷ)

-- The DGG frames compare a coercion typed at an unknown mode
-- environment against one typed at tag-or-idᵈ; seal-freeness of the
-- unknown side is exactly compatibility with tag-or-idᵈ.
seal-free-compat-tagᵈ :
  ∀ {μ} →
  (∀ X → sealModeAllowed (μ X) ≡ false) →
  ModeEnvCompat μ tag-or-idᵈ
seal-free-compat-tagᵈ {μ} seal-free X with μ X | seal-free X
seal-free-compat-tagᵈ {μ} seal-free X | id-only | _ = refl
seal-free-compat-tagᵈ {μ} seal-free X | tag-or-id | _ = refl
seal-free-compat-tagᵈ {μ} seal-free X | seal-or-id | ()

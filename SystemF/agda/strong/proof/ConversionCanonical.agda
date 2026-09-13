module strong.proof.ConversionCanonical where

-- Strong System F v7 — canonical views of typed normal conversions.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; [])
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms using (Applicable; applies-arr; applies-all; applies-var)
open import strong.proof.CtxProperties using (name-unique)
open import strong.proof.ConversionProperties

fuse-seal-unseal : ∀ α → fuse (seal α) (unseal α) ≡ just []
fuse-seal-unseal α with α ≟ α
fuse-seal-unseal α | yes eq = refl
fuse-seal-unseal α | no neq = ⊥-elim (neq refl)

fuse-fun-fun : ∀ c d e f
  → Σ[ hs ∈ List Head ] (fuse (c ↦ d) (e ↦ f) ≡ just hs)
fuse-fun-fun c d e f = _ , refl

fuse-all-all : ∀ c d
  → Σ[ hs ∈ List Head ] (fuse (all c) (all d) ≡ just hs)
fuse-all-all c d = _ , refl

data EndsVar (c : Conv) : Set where
  ends-var : ∀ X → target c ≡ ` X → EndsVar c

after-seal : ∀ {Δ₁ Δ₂ Δ₃ α X A B c}
  → Δ₁ ⊢̂ seal α ∶ A ⇝ ` X ⊣ Δ₂
  → Δ₂ ⊢ c ∶ ` X ⇝ B ⊣ Δ₃
  → NF c
  → IrreducibleAfter (seal α) c
  → EndsVar c
after-seal seal-ty (conv-id same) nf-id irr-id with same-var-right same
after-seal seal-ty (conv-id same) nf-id irr-id | var-shape Y =
  ends-var Y refl
after-seal (conv-seal n₁ rep read) (conv-cons (conv-seal n₂ rep₂ read₂) t)
  (nf-cons nf-seal nft irr₂) (irr-cons outer)
  with after-seal (conv-seal n₂ rep₂ read₂) t nft irr₂
after-seal (conv-seal n₁ rep read) (conv-cons (conv-seal n₂ rep₂ read₂) t)
  (nf-cons nf-seal nft irr₂) (irr-cons outer) | ends-var Y eq =
  ends-var Y eq
after-seal (conv-seal n₁ rep read) (conv-cons (conv-unseal n₂ rep₂ read₂) t)
  (nf-cons nf-unseal nft irr₂) (irr-cons outer)
  with name-unique n₁ n₂
after-seal (conv-seal n₁ rep read) (conv-cons (conv-unseal n₂ rep₂ read₂) t)
  (nf-cons nf-unseal nft irr₂) (irr-cons outer) | refl
  with trans (sym outer) (fuse-seal-unseal _)
after-seal (conv-seal n₁ rep read) (conv-cons (conv-unseal n₂ rep₂ read₂) t)
  (nf-cons nf-unseal nft irr₂) (irr-cons outer) | refl | ()

data GroundReady (c : Conv) : Set where
  ready-applicable : Applicable c → GroundReady c
  ready-ℕ : c ≡ id `ℕ → GroundReady c
  ready-𝔹 : c ≡ id `𝔹 → GroundReady c

canonical-ℕ-conv : ∀ {Δ₁ Δ₂ c B}
  → Δ₁ ⊢ c ∶ `ℕ ⇝ B ⊣ Δ₂
  → NF c
  → GroundReady c
canonical-ℕ-conv (conv-id same) nf-id rewrite same-ℕ-right same =
  ready-ℕ refl
canonical-ℕ-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr)
  with after-seal (conv-seal n rep read) t nft irr
canonical-ℕ-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr)
  | ends-var X eq = ready-applicable (applies-var eq)

canonical-𝔹-conv : ∀ {Δ₁ Δ₂ c B}
  → Δ₁ ⊢ c ∶ `𝔹 ⇝ B ⊣ Δ₂
  → NF c
  → GroundReady c
canonical-𝔹-conv (conv-id same) nf-id rewrite same-𝔹-right same =
  ready-𝔹 refl
canonical-𝔹-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr)
  with after-seal (conv-seal n rep read) t nft irr
canonical-𝔹-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr)
  | ends-var X eq = ready-applicable (applies-var eq)

canonical-⇒-conv : ∀ {Δ₁ Δ₂ c A B C}
  → Δ₁ ⊢ c ∶ A ⇒ B ⇝ C ⊣ Δ₂
  → NF c
  → Applicable c
canonical-⇒-conv (conv-id same) nf-id with same-fun-right same
canonical-⇒-conv (conv-id same) nf-id | fun-shape A B =
  applies-arr refl
canonical-⇒-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr)
  with after-seal (conv-seal n rep read) t nft irr
canonical-⇒-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr) | ends-var X eq = applies-var eq
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d) (conv-id same))
  (nf-cons (nf-fun nfs nfd) nf-id irr-id)
  with same-fun-right same
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d) (conv-id same))
  (nf-cons (nf-fun nfs nfd) nf-id irr-id) | fun-shape A B =
  applies-arr refl
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d)
    (conv-cons (conv-seal n rep read) t))
  (nf-cons (nf-fun nfs nfd) (nf-cons nf-seal nft irr₂)
    (irr-cons outer))
  with after-seal (conv-seal n rep read) t nft irr₂
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d)
    (conv-cons (conv-seal n rep read) t))
  (nf-cons (nf-fun nfs nfd) (nf-cons nf-seal nft irr₂)
    (irr-cons outer)) | ends-var X eq = applies-var eq
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d)
    (conv-cons (conv-fun {s = c₃} {t = c₄} s₂ d₂) t))
  (nf-cons (nf-fun nfs nfd) (nf-cons (nf-fun nfs₂ nfd₂) nft irr₂)
    (irr-cons outer))
  with fuse-fun-fun c₁ c₂ c₃ c₄
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d)
    (conv-cons (conv-fun {s = c₃} {t = c₄} s₂ d₂) t))
  (nf-cons (nf-fun nfs nfd) (nf-cons (nf-fun nfs₂ nfd₂) nft irr₂)
    (irr-cons outer)) | hs , fused
  with trans (sym outer) fused
canonical-⇒-conv
  (conv-cons (conv-fun {s = c₁} {t = c₂} s d)
    (conv-cons (conv-fun {s = c₃} {t = c₄} s₂ d₂) t))
  (nf-cons (nf-fun nfs nfd) (nf-cons (nf-fun nfs₂ nfd₂) nft irr₂)
    (irr-cons outer)) | hs , fused | ()

canonical-∀-conv : ∀ {Δ₁ Δ₂ c A B}
  → Δ₁ ⊢ c ∶ `∀ A ⇝ B ⊣ Δ₂
  → NF c
  → Applicable c
canonical-∀-conv (conv-id same) nf-id with same-all-right same
canonical-∀-conv (conv-id same) nf-id | all-shape A =
  applies-all refl
canonical-∀-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr)
  with after-seal (conv-seal n rep read) t nft irr
canonical-∀-conv (conv-cons (conv-seal n rep read) t)
  (nf-cons nf-seal nft irr) | ends-var X eq = applies-var eq
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s) (conv-id same))
  (nf-cons (nf-all nfs) nf-id irr-id)
  with same-all-right same
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s) (conv-id same))
  (nf-cons (nf-all nfs) nf-id irr-id) | all-shape A =
  applies-all refl
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s) (conv-cons (conv-seal n rep read) t))
  (nf-cons (nf-all nfs) (nf-cons nf-seal nft irr₂) (irr-cons outer))
  with after-seal (conv-seal n rep read) t nft irr₂
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s) (conv-cons (conv-seal n rep read) t))
  (nf-cons (nf-all nfs) (nf-cons nf-seal nft irr₂) (irr-cons outer))
  | ends-var X eq = applies-var eq
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s)
    (conv-cons (conv-all {s = c₂} s₂) t))
  (nf-cons (nf-all nfs) (nf-cons (nf-all nfs₂) nft irr₂)
    (irr-cons outer))
  with fuse-all-all c₁ c₂
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s)
    (conv-cons (conv-all {s = c₂} s₂) t))
  (nf-cons (nf-all nfs) (nf-cons (nf-all nfs₂) nft irr₂)
    (irr-cons outer)) | hs , fused
  with trans (sym outer) fused
canonical-∀-conv
  (conv-cons (conv-all {s = c₁} s)
    (conv-cons (conv-all {s = c₂} s₂) t))
  (nf-cons (nf-all nfs) (nf-cons (nf-all nfs₂) nft irr₂)
    (irr-cons outer)) | hs , fused | ()

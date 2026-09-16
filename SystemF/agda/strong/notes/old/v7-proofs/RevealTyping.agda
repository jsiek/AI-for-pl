module strong.proof.RevealTyping where

-- Strong System F v7 — the conversion builders `revTy` / `concTy` are
-- well-typed and in normal form.
--
-- THE FRAME.  `Reveals X α Δᵢ Δₑ` says that the interior `Δᵢ` is the
-- exterior `Δₑ` with the source name `X := α` revealed, under `X`-many
-- structural `∀` binders pushed onto BOTH sides.  That is exactly the
-- recursion `revTy`/`concTy` perform: each `∀` step raises `X`, raises the
-- anchor `α`, and shifts the reading `S`.
--
-- Note the two contexts carry the SAME anchors — a reveal adds a name, not
-- an anchor.  That is what lets `SameAnchor` (a de Bruijn LEVEL comparison)
-- relate the two indexings of a free variable, and it is why `⊢ν` types its
-- conversion against `ΔΘ` (the store-extended exterior) rather than `Δ`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (_∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.proof.CtxProperties using
  (name-of-tv; named-anchor; tv-of-name; ok-Λ)
open import strong.proof.SameTyProperties
open import strong.proof.CloseTy

private
  variable
    Δ Δ′ Δᵢ Δₑ : Ctxᵗ
    A B S : Ty
    R : RepTy
    X Y k : ℕ
    α β : Anchor
    ρᵗ : Renameᵗ
    ρᴿ : Renameᴿ

------------------------------------------------------------------------
-- Renaming source names, readings and well-formedness
------------------------------------------------------------------------

NameMap : Renameᵗ → Renameᴿ → Ctxᵗ → Ctxᵗ → Set
NameMap ρᵗ ρᴿ Δ Δ′ = ∀ {X α} → Δ ∋n X := α → Δ′ ∋n ρᵗ X := ρᴿ α

nameMap-Λ : NameMap ρᵗ ρᴿ Δ Δ′
  → NameMap (extᵗ ρᵗ) (extᴿ ρᴿ)
      (anch revealed abstA ∷ Δ) (anch revealed abstA ∷ Δ′)
nameMap-Λ f n-here = n-here
nameMap-Λ f (n-revealed h) = n-revealed (f h)

read-rename : NameMap ρᵗ ρᴿ Δ Δ′
  → Δ ⊢ R ⇓ A → Δ′ ⊢ renameᴿ ρᴿ R ⇓ renameᵗ ρᵗ A
read-rename f (read-var n) = read-var (f n)
read-rename f read-ℕ = read-ℕ
read-rename f read-𝔹 = read-𝔹
read-rename f (read-⇒ r s) = read-⇒ (read-rename f r) (read-rename f s)
read-rename f (read-∀ r) = read-∀ (read-rename (nameMap-Λ f) r)

name-Λ : NameMap suc suc Δ (anch revealed abstA ∷ Δ)
name-Λ h = n-revealed h

read-Λ : Δ ⊢ R ⇓ A → (anch revealed abstA ∷ Δ) ⊢ ⇑ᴿ R ⇓ ⇑ᵗ A
read-Λ = read-rename name-Λ

rep-Λ : Δ ∋r α := R → (anch revealed abstA ∷ Δ) ∋r suc α := ⇑ᴿ R
rep-Λ = r-there

TvMap : Renameᵗ → Ctxᵗ → Ctxᵗ → Set
TvMap ρᵗ Δ Δ′ = ∀ {X} → Δ ∋tv X → Δ′ ∋tv ρᵗ X

tvMap-Λ : TvMap ρᵗ Δ Δ′
  → TvMap (extᵗ ρᵗ) (anch revealed abstA ∷ Δ) (anch revealed abstA ∷ Δ′)
tvMap-Λ f tv-here = tv-here
tvMap-Λ f (tv-revealed h) = tv-revealed (f h)

wf-rename : TvMap ρᵗ Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ renameᵗ ρᵗ A
wf-rename f (wf-var x) = wf-var (f x)
wf-rename f wf-ℕ = wf-ℕ
wf-rename f wf-𝔹 = wf-𝔹
wf-rename f (wf-⇒ a b) = wf-⇒ (wf-rename f a) (wf-rename f b)
wf-rename f (wf-∀ a) = wf-∀ (wf-rename (tvMap-Λ f) a)

wf-Λ : Δ ⊢ᵗ A → (anch revealed abstA ∷ Δ) ⊢ᵗ ⇑ᵗ A
wf-Λ = wf-rename tv-revealed

read-wf : Δ ⊢ R ⇓ A → Δ ⊢ᵗ A
read-wf (read-var n) = wf-var (tv-of-name n)
read-wf read-ℕ = wf-ℕ
read-wf read-𝔹 = wf-𝔹
read-wf (read-⇒ r s) = wf-⇒ (read-wf r) (read-wf s)
read-wf (read-∀ r) = wf-∀ (read-wf r)

------------------------------------------------------------------------
-- The reveal frame
------------------------------------------------------------------------

-- `Reveals X α Δᵢ Δₑ`: the interior differs from the exterior in ONE
-- visibility bit, at anchor α, which the interior names X.  `rev-over`
-- passes a concealed anchor (the anchor index rises, the type-variable
-- index does not); `rev-under` descends a structural `∀` (both rise).
data Reveals : ℕ → Anchor → Ctxᵗ → Ctxᵗ → Set where
  rev-at    : ∀ {b} → Reveals zero zero
                (anch revealed b ∷ Δ) (anch concealed b ∷ Δ)
  rev-over  : ∀ {b} → Reveals X α Δᵢ Δₑ
            → Reveals X (suc α)
                (anch concealed b ∷ Δᵢ) (anch concealed b ∷ Δₑ)
  rev-under : Reveals X α Δᵢ Δₑ
            → Reveals (suc X) (suc α)
                (anch revealed abstA ∷ Δᵢ) (anch revealed abstA ∷ Δₑ)

reveals-count : Reveals X α Δᵢ Δₑ → anchorCount Δᵢ ≡ anchorCount Δₑ
reveals-count rev-at = refl
reveals-count (rev-over rev) = cong suc (reveals-count rev)
reveals-count (rev-under rev) = cong suc (reveals-count rev)

-- A `Reveals` frame shares the spine on both sides, carried under the
-- binders the builders descend: exactly `conv-seal`/`conv-unseal`'s
-- premise.
reveals-sb : Reveals X α Δᵢ Δₑ → SameBindings Δᵢ Δₑ
reveals-sb rev-at = sb-∷ sb-refl
reveals-sb (rev-over rev) = sb-∷ (reveals-sb rev)
reveals-sb (rev-under rev) = sb-∷ (reveals-sb rev)

reveals-name : Reveals X α Δᵢ Δₑ → Δᵢ ∋n X := α
reveals-name rev-at = n-here
reveals-name (rev-over rev) = n-concealed (reveals-name rev)
reveals-name (rev-under rev) = n-revealed (reveals-name rev)

-- Every OTHER source variable survives, naming the SAME anchor; only its
-- own index closes up over the one that left.
reveals-other : Reveals X α Δᵢ Δₑ → X ≢ᴺ Y → Δᵢ ∋n Y := β
  → Δₑ ∋n closeIdx X Y := β
reveals-other rev-at ne n-here = ⊥-elim (ne refl)
reveals-other rev-at ne (n-revealed h) = n-concealed h
reveals-other (rev-over rev) ne (n-concealed h) =
  n-concealed (reveals-other rev ne h)
reveals-other (rev-under rev) ne n-here = n-here
reveals-other (rev-under rev) ne (n-revealed h) =
  n-revealed (reveals-other rev (λ eq → ne (cong suc eq)) h)

reveals-same : Reveals X α Δᵢ Δₑ → X ≢ᴺ Y → Δᵢ ∋n Y := β
  → SameTy k Δᵢ (` Y) Δₑ (` (closeIdx X Y))
reveals-same rev ne n =
  same-free n (reveals-other rev ne n)
    (same-anchor (named-anchor n) (named-anchor (reveals-other rev ne n)) refl)

reveals-tv : Reveals X α Δᵢ Δₑ → X ≢ᴺ Y → Δᵢ ∋tv Y → Δₑ ∋tv closeIdx X Y
reveals-tv rev ne tv with name-of-tv tv
reveals-tv rev ne tv | β , n = tv-of-name (reveals-other rev ne n)

------------------------------------------------------------------------
-- Well-formedness of the closed type
------------------------------------------------------------------------

closeAt-wf : Reveals X α Δᵢ Δₑ → Δₑ ⊢ᵗ S → Δᵢ ⊢ᵗ A
  → Δₑ ⊢ᵗ closeAt X S A
closeAt-wf {X = X} {S = S} rev wfS (wf-var {X = Y} tv) = go (X ≟ Y)
  where
  go : Dec (X ≡ Y) → _ ⊢ᵗ closeAt X S (` Y)
  go (yes refl) rewrite closeAt-hit X S = wfS
  go (no ne) rewrite closeAt-miss X S Y ne =
    wf-var (reveals-tv rev ne tv)
closeAt-wf rev wfS wf-ℕ = wf-ℕ
closeAt-wf rev wfS wf-𝔹 = wf-𝔹
closeAt-wf rev wfS (wf-⇒ a b) =
  wf-⇒ (closeAt-wf rev wfS a) (closeAt-wf rev wfS b)
closeAt-wf {X = X} {S = S} rev wfS (wf-∀ {A = A} a)
  rewrite closeAt-∀ X S A =
  wf-∀ (closeAt-wf (rev-under rev) (wf-Λ wfS) a)

------------------------------------------------------------------------
-- The builders at a variable, without exposing their `with`
------------------------------------------------------------------------

revTy-hit : ∀ X α S → revTy X α S (` X) ≡ unseal α ∷ᶜ id S
revTy-hit X α S with X ≟ X
revTy-hit X α S | yes _ = refl
revTy-hit X α S | no ne = ⊥-elim (ne refl)

revTy-miss : ∀ X α S Y → X ≢ᴺ Y
  → revTy X α S (` Y) ≡ id (` (closeIdx X Y))
revTy-miss X α S Y ne with X ≟ Y
revTy-miss X α S Y ne | yes eq = ⊥-elim (ne eq)
revTy-miss X α S Y ne | no _ = cong id (closeEnv-miss X S Y ne)

concTy-hit : ∀ X α S → concTy X α S (` X) ≡ seal α ∷ᶜ id (` X)
concTy-hit X α S with X ≟ X
concTy-hit X α S | yes _ = refl
concTy-hit X α S | no ne = ⊥-elim (ne refl)

concTy-miss : ∀ X α S Y → X ≢ᴺ Y → concTy X α S (` Y) ≡ id (` Y)
concTy-miss X α S Y ne with X ≟ Y
concTy-miss X α S Y ne | yes eq = ⊥-elim (ne eq)
concTy-miss X α S Y ne | no _ = refl

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

mutual
  revTy-typing : Reveals X α Δᵢ Δₑ
    → Δᵢ ∋r α := R → Δₑ ⊢ R ⇓ S → Δᵢ ⊢ᵗ A
    → Δᵢ ⊢ revTy X α S A ∶ A ⇝ closeAt X S A ⊣ Δₑ
  revTy-typing {X = X} {α = α} {S = S} rev rep rd
    (wf-var {X = Y} tv) = go (X ≟ Y)
    where
    go : Dec (X ≡ Y)
       → _ ⊢ revTy X α S (` Y) ∶ ` Y ⇝ closeAt X S (` Y) ⊣ _
    go (yes refl) rewrite revTy-hit X α S | closeAt-hit X S =
      conv-cons (conv-unseal (reveals-name rev) rep rd (reveals-sb rev))
                (tail-id (read-wf rd))
    go (no ne) rewrite revTy-miss X α S Y ne | closeAt-miss X S Y ne
      with name-of-tv tv
    go (no ne) | β , n =
      conv-id (reveals-same rev ne n) (reveals-sb rev)
  revTy-typing rev rep rd wf-ℕ = conv-id same-ℕ (reveals-sb rev)
  revTy-typing rev rep rd wf-𝔹 = conv-id same-𝔹 (reveals-sb rev)
  revTy-typing rev rep rd (wf-⇒ a b) =
    conv-cons
      (conv-fun (concTy-typing rev rep rd a)
                (revTy-typing rev rep rd b))
      (tail-id (wf-⇒ (closeAt-wf rev (read-wf rd) a)
                     (closeAt-wf rev (read-wf rd) b)))
  revTy-typing {X = X} {S = S} rev rep rd (wf-∀ {A = A} a)
    rewrite closeAt-∀ X S A =
    conv-cons
      (conv-all (revTy-typing (rev-under rev) (rep-Λ rep) (read-Λ rd) a))
      (tail-id (wf-∀ (closeAt-wf (rev-under rev) (wf-Λ (read-wf rd)) a)))

  concTy-typing : Reveals X α Δᵢ Δₑ
    → Δᵢ ∋r α := R → Δₑ ⊢ R ⇓ S → Δᵢ ⊢ᵗ A
    → Δₑ ⊢ concTy X α S A ∶ closeAt X S A ⇝ A ⊣ Δᵢ
  concTy-typing {X = X} {α = α} {S = S} rev rep rd
    (wf-var {X = Y} tv) = go (X ≟ Y)
    where
    go : Dec (X ≡ Y)
       → _ ⊢ concTy X α S (` Y) ∶ closeAt X S (` Y) ⇝ ` Y ⊣ _
    go (yes refl) rewrite concTy-hit X α S | closeAt-hit X S =
      conv-cons (conv-seal (reveals-name rev) rep rd
                  (sb-sym (reveals-sb rev)))
                (tail-id (wf-var (tv-of-name (reveals-name rev))))
    go (no ne) rewrite concTy-miss X α S Y ne | closeAt-miss X S Y ne
      with name-of-tv tv
    go (no ne) | β , n =
      conv-id (sameTy-sym (reveals-same rev ne n)) (sb-sym (reveals-sb rev))
  concTy-typing rev rep rd wf-ℕ = conv-id same-ℕ (sb-sym (reveals-sb rev))
  concTy-typing rev rep rd wf-𝔹 = conv-id same-𝔹 (sb-sym (reveals-sb rev))
  concTy-typing rev rep rd (wf-⇒ a b) =
    conv-cons
      (conv-fun (revTy-typing rev rep rd a)
                (concTy-typing rev rep rd b))
      (tail-id (wf-⇒ a b))
  concTy-typing {X = X} {S = S} rev rep rd (wf-∀ {A = A} a)
    rewrite closeAt-∀ X S A =
    conv-cons
      (conv-all (concTy-typing (rev-under rev) (rep-Λ rep) (read-Λ rd) a))
      (tail-id (wf-∀ a))

------------------------------------------------------------------------
-- Normal forms
------------------------------------------------------------------------

mutual
  revTy-NF : ∀ X α S A → NF (revTy X α S A)
  revTy-NF X α S (` Y) = go (X ≟ Y)
    where
    go : Dec (X ≡ Y) → NF (revTy X α S (` Y))
    go (yes refl) rewrite revTy-hit X α S = nf-cons nf-unseal nf-id irr-id
    go (no ne) rewrite revTy-miss X α S Y ne = nf-id
  revTy-NF X α S `ℕ = nf-id
  revTy-NF X α S `𝔹 = nf-id
  revTy-NF X α S (A ⇒ B) =
    nf-cons (nf-fun (concTy-NF X α S A) (revTy-NF X α S B)) nf-id irr-id
  revTy-NF X α S (`∀ A) =
    nf-cons (nf-all (revTy-NF (suc X) (suc α) (⇑ᵗ S) A)) nf-id irr-id

  concTy-NF : ∀ X α S A → NF (concTy X α S A)
  concTy-NF X α S (` Y) = go (X ≟ Y)
    where
    go : Dec (X ≡ Y) → NF (concTy X α S (` Y))
    go (yes refl) rewrite concTy-hit X α S = nf-cons nf-seal nf-id irr-id
    go (no ne) rewrite concTy-miss X α S Y ne = nf-id
  concTy-NF X α S `ℕ = nf-id
  concTy-NF X α S `𝔹 = nf-id
  concTy-NF X α S (A ⇒ B) =
    nf-cons (nf-fun (revTy-NF X α S A) (concTy-NF X α S B)) nf-id irr-id
  concTy-NF X α S (`∀ A) =
    nf-cons (nf-all (concTy-NF (suc X) (suc α) (⇑ᵗ S) A)) nf-id irr-id

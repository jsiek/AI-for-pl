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
open import strong.proof.CtxProperties using (name-of-tv; named-anchor; ok-Λ)
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

tv-of-name : Δ ∋n X := α → Δ ∋tv X
tv-of-name n-here = tv-here
tv-of-name (n-over-name h) = tv-over-name (tv-of-name h)
tv-of-name (n-over-abst h) = tv-over-abst (tv-of-name h)
tv-of-name (n-over-bind h) = tv-over-bind (tv-of-name h)

NameMap : Renameᵗ → Renameᴿ → Ctxᵗ → Ctxᵗ → Set
NameMap ρᵗ ρᴿ Δ Δ′ = ∀ {X α} → Δ ∋n X := α → Δ′ ∋n ρᵗ X := ρᴿ α

nameMap-Λ : NameMap ρᵗ ρᴿ Δ Δ′
  → NameMap (extᵗ ρᵗ) (extᴿ ρᴿ)
      (name zero ∷ abst ∷ Δ) (name zero ∷ abst ∷ Δ′)
nameMap-Λ f n-here = n-here
nameMap-Λ f (n-over-name (n-over-abst h)) =
  n-over-name (n-over-abst (f h))

read-rename : NameMap ρᵗ ρᴿ Δ Δ′
  → Δ ⊢ R ⇓ A → Δ′ ⊢ renameᴿ ρᴿ R ⇓ renameᵗ ρᵗ A
read-rename f (read-var n) = read-var (f n)
read-rename f read-ℕ = read-ℕ
read-rename f read-𝔹 = read-𝔹
read-rename f (read-⇒ r s) = read-⇒ (read-rename f r) (read-rename f s)
read-rename f (read-∀ r) = read-∀ (read-rename (nameMap-Λ f) r)

name-Λ : NameMap suc suc Δ (name zero ∷ abst ∷ Δ)
name-Λ h = n-over-name (n-over-abst h)

read-Λ : Δ ⊢ R ⇓ A → (name zero ∷ abst ∷ Δ) ⊢ ⇑ᴿ R ⇓ ⇑ᵗ A
read-Λ = read-rename name-Λ

rep-Λ : Δ ∋r α := R → (name zero ∷ abst ∷ Δ) ∋r suc α := ⇑ᴿ R
rep-Λ h = r-over-name (r-over-abst h)

TvMap : Renameᵗ → Ctxᵗ → Ctxᵗ → Set
TvMap ρᵗ Δ Δ′ = ∀ {X} → Δ ∋tv X → Δ′ ∋tv ρᵗ X

tvMap-Λ : TvMap ρᵗ Δ Δ′
  → TvMap (extᵗ ρᵗ) (name zero ∷ abst ∷ Δ) (name zero ∷ abst ∷ Δ′)
tvMap-Λ f tv-here = tv-here
tvMap-Λ f (tv-over-name (tv-over-abst h)) =
  tv-over-name (tv-over-abst (f h))

wf-rename : TvMap ρᵗ Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ renameᵗ ρᵗ A
wf-rename f (wf-var x) = wf-var (f x)
wf-rename f wf-ℕ = wf-ℕ
wf-rename f wf-𝔹 = wf-𝔹
wf-rename f (wf-⇒ a b) = wf-⇒ (wf-rename f a) (wf-rename f b)
wf-rename f (wf-∀ a) = wf-∀ (wf-rename (tvMap-Λ f) a)

wf-Λ : Δ ⊢ᵗ A → (name zero ∷ abst ∷ Δ) ⊢ᵗ ⇑ᵗ A
wf-Λ = wf-rename (λ h → tv-over-name (tv-over-abst h))

read-wf : Δ ⊢ R ⇓ A → Δ ⊢ᵗ A
read-wf (read-var n) = wf-var (tv-of-name n)
read-wf read-ℕ = wf-ℕ
read-wf read-𝔹 = wf-𝔹
read-wf (read-⇒ r s) = wf-⇒ (read-wf r) (read-wf s)
read-wf (read-∀ r) = wf-∀ (read-wf r)

------------------------------------------------------------------------
-- The reveal frame
------------------------------------------------------------------------

data Reveals : ℕ → Anchor → Ctxᵗ → Ctxᵗ → Set where
  rev-here  : Reveals zero α (name α ∷ Δ) Δ
  rev-under : Reveals X α Δᵢ Δₑ
            → Reveals (suc X) (suc α)
                (name zero ∷ abst ∷ Δᵢ) (name zero ∷ abst ∷ Δₑ)

reveals-count : Reveals X α Δᵢ Δₑ → anchorCount Δᵢ ≡ anchorCount Δₑ
reveals-count rev-here = refl
reveals-count (rev-under rev) = cong suc (reveals-count rev)

reveals-name : Reveals X α Δᵢ Δₑ → Δᵢ ∋n X := α
reveals-name rev-here = n-here
reveals-name (rev-under rev) = n-over-name (n-over-abst (reveals-name rev))

reveals-tv : Reveals X α Δᵢ Δₑ → X ≢ᴺ Y → Δᵢ ∋tv Y → Δₑ ∋tv closeIdx X Y
reveals-tv rev-here ne tv-here = ⊥-elim (ne refl)
reveals-tv rev-here ne (tv-over-name tv) = tv
reveals-tv (rev-under rev) ne tv-here = tv-here
reveals-tv (rev-under rev) ne (tv-over-name (tv-over-abst tv)) =
  tv-over-name (tv-over-abst
    (reveals-tv rev (λ eq → ne (cong suc eq)) tv))

reveals-other : Reveals X α Δᵢ Δₑ → Δₑ ok → X ≢ᴺ Y → Δᵢ ∋n Y := β
  → Σ[ γ ∈ Anchor ]
      ((Δₑ ∋n closeIdx X Y := γ) × SameAnchor Δᵢ β Δₑ γ)
reveals-other rev-here oke ne n-here = ⊥-elim (ne refl)
reveals-other {β = β} rev-here oke ne (n-over-name h)
  with anchor-binding (named-anchor oke h)
reveals-other {β = β} rev-here oke ne (n-over-name h) | b , ab =
  β , h , same-anchor (ab-over-name ab) ab refl
reveals-other (rev-under rev) oke ne n-here =
  zero , n-here , sameAnchor-Λ-zero (reveals-count rev)
reveals-other (rev-under rev) (ok-name (ok-abst oke) _ _) ne
  (n-over-name (n-over-abst h))
  with reveals-other rev oke (λ eq → ne (cong suc eq)) h
reveals-other (rev-under rev) (ok-name (ok-abst oke) _ _) ne
  (n-over-name (n-over-abst h)) | γ , n , sa =
  suc γ , n-over-name (n-over-abst n) , sameAnchor-Λ sa

------------------------------------------------------------------------
-- Well-formedness of the closed type
------------------------------------------------------------------------

closeAt-wf : Reveals X α Δᵢ Δₑ → Δₑ ok → Δₑ ⊢ᵗ S → Δᵢ ⊢ᵗ A
  → Δₑ ⊢ᵗ closeAt X S A
closeAt-wf {X = X} {S = S} rev oke wfS (wf-var {X = Y} tv) = go (X ≟ Y)
  where
  go : Dec (X ≡ Y) → _ ⊢ᵗ closeAt X S (` Y)
  go (yes refl) rewrite closeAt-hit X S = wfS
  go (no ne) rewrite closeAt-miss X S Y ne =
    wf-var (reveals-tv rev ne tv)
closeAt-wf rev oke wfS wf-ℕ = wf-ℕ
closeAt-wf rev oke wfS wf-𝔹 = wf-𝔹
closeAt-wf rev oke wfS (wf-⇒ a b) =
  wf-⇒ (closeAt-wf rev oke wfS a) (closeAt-wf rev oke wfS b)
closeAt-wf {X = X} {S = S} rev oke wfS (wf-∀ {A = A} a)
  rewrite closeAt-∀ X S A =
  wf-∀ (closeAt-wf (rev-under rev) (ok-Λ oke) (wf-Λ wfS) a)

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
  revTy-typing : Reveals X α Δᵢ Δₑ → Δᵢ ok → Δₑ ok
    → Δᵢ ∋r α := R → Δₑ ⊢ R ⇓ S → Δᵢ ⊢ᵗ A
    → Δᵢ ⊢ revTy X α S A ∶ A ⇝ closeAt X S A ⊣ Δₑ
  revTy-typing {X = X} {α = α} {S = S} rev oki oke rep rd
    (wf-var {X = Y} tv) = go (X ≟ Y)
    where
    go : Dec (X ≡ Y)
       → _ ⊢ revTy X α S (` Y) ∶ ` Y ⇝ closeAt X S (` Y) ⊣ _
    go (yes refl) rewrite revTy-hit X α S | closeAt-hit X S =
      conv-cons (conv-unseal (reveals-name rev) rep rd)
                (conv-id (sameTy-refl oke (read-wf rd)))
    go (no ne) rewrite revTy-miss X α S Y ne | closeAt-miss X S Y ne
      with name-of-tv tv
    go (no ne) | β , n with reveals-other rev oke ne n
    go (no ne) | β , n | γ , m , sa = conv-id (same-free n m sa)
  revTy-typing rev oki oke rep rd wf-ℕ = conv-id same-ℕ
  revTy-typing rev oki oke rep rd wf-𝔹 = conv-id same-𝔹
  revTy-typing rev oki oke rep rd (wf-⇒ a b) =
    conv-cons
      (conv-fun (concTy-typing rev oki oke rep rd a)
                (revTy-typing rev oki oke rep rd b))
      (conv-id (sameTy-refl oke
        (wf-⇒ (closeAt-wf rev oke (read-wf rd) a)
              (closeAt-wf rev oke (read-wf rd) b))))
  revTy-typing {X = X} {S = S} rev oki oke rep rd (wf-∀ {A = A} a)
    rewrite closeAt-∀ X S A =
    conv-cons
      (conv-all (revTy-typing (rev-under rev) (ok-Λ oki) (ok-Λ oke)
                  (rep-Λ rep) (read-Λ rd) a))
      (conv-id (sameTy-refl oke
        (wf-∀ (closeAt-wf (rev-under rev) (ok-Λ oke)
                (wf-Λ (read-wf rd)) a))))

  concTy-typing : Reveals X α Δᵢ Δₑ → Δᵢ ok → Δₑ ok
    → Δᵢ ∋r α := R → Δₑ ⊢ R ⇓ S → Δᵢ ⊢ᵗ A
    → Δₑ ⊢ concTy X α S A ∶ closeAt X S A ⇝ A ⊣ Δᵢ
  concTy-typing {X = X} {α = α} {S = S} rev oki oke rep rd
    (wf-var {X = Y} tv) = go (X ≟ Y)
    where
    go : Dec (X ≡ Y)
       → _ ⊢ concTy X α S (` Y) ∶ closeAt X S (` Y) ⇝ ` Y ⊣ _
    go (yes refl) rewrite concTy-hit X α S | closeAt-hit X S =
      conv-cons (conv-seal (reveals-name rev) rep rd)
                (conv-id (sameTy-refl oki
                  (wf-var (tv-of-name (reveals-name rev)))))
    go (no ne) rewrite concTy-miss X α S Y ne | closeAt-miss X S Y ne
      with name-of-tv tv
    go (no ne) | β , n with reveals-other rev oke ne n
    go (no ne) | β , n | γ , m , sa =
      conv-id (sameTy-sym (same-free n m sa))
  concTy-typing rev oki oke rep rd wf-ℕ = conv-id same-ℕ
  concTy-typing rev oki oke rep rd wf-𝔹 = conv-id same-𝔹
  concTy-typing rev oki oke rep rd (wf-⇒ a b) =
    conv-cons
      (conv-fun (revTy-typing rev oki oke rep rd a)
                (concTy-typing rev oki oke rep rd b))
      (conv-id (sameTy-refl oki (wf-⇒ a b)))
  concTy-typing {X = X} {S = S} rev oki oke rep rd (wf-∀ {A = A} a)
    rewrite closeAt-∀ X S A =
    conv-cons
      (conv-all (concTy-typing (rev-under rev) (ok-Λ oki) (ok-Λ oke)
                  (rep-Λ rep) (read-Λ rd) a))
      (conv-id (sameTy-refl oki (wf-∀ a)))

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

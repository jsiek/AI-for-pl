{-# OPTIONS --allow-unsolved-metas #-}

module proof.Core.Properties.LeftSealNarrowingInversion where

-- File Charter:
--   * Mechanized work on the Left Seal Narrowing Inversion lemma from
--     cambridge25.
--   * Kept separate from the top-down dynamic gradual guarantee skeleton so
--     the local inversion experiments and holes do not obscure the main proof
--     outline.
--   * In the paper notation, `α♯` is the seal coercion; here that is
--     `seal A α`.

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)
open import proof.Core.Properties.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.Core.Properties.NarrowWidenProperties using (srcStoreⁿ-⊒ˢ)
open import proof.Core.Properties.NuTermProperties using (renameᵗᵐ-preserves-Value)

------------------------------------------------------------------------
-- Left Seal Narrowing Inversion
------------------------------------------------------------------------

-- Paper statement:
--
--   If σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ : id_α
--   then σ ⊢ V ⊒ V′ : α♯.
--
-- We state a weaker Agda conclusion: there exists some well-typed narrowing
-- from `★` to `α` relating `V` and `V′`.  This differs from the cambridge25
-- notes, which name the specific seal narrowing `α♯`.  With the current
-- endpoint-based coercion equivalence, inversion can expose any narrowing with
-- those endpoints, not necessarily the literal seal step.  The weakening keeps
-- the endpoint information that later DGG proof steps need; we will check as
-- the proof develops whether losing the specific `α♯` syntax causes trouble.
--
-- The value premise is implicit in the paper's use of `V`; it is explicit
-- here so later proofs can use canonical-value facts when needed.

⇑ᵗ≢＇0 :
  ∀ {A} →
  ⇑ᵗ A ≡ ＇ zero →
  ⊥
⇑ᵗ≢＇0 {A = ＇ X} ()
⇑ᵗ≢＇0 {A = ‵ ι} ()
⇑ᵗ≢＇0 {A = ★} ()
⇑ᵗ≢＇0 {A = A ⇒ B} ()
⇑ᵗ≢＇0 {A = `∀ A} ()

narrowing-open-id-var-endpoints⊥ :
  ∀ {A B p α β} →
  Narrowing p →
  src p ≡ ⇑ᵗ A →
  tgt p ≡ B →
  occurs zero B ≡ true →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
narrowing-open-id-var-endpoints⊥ {A = A}
    (cross (id-＇ zero)) src-p tgt-p occ open-id =
  ⇑ᵗ≢＇0 {A = A} (sym src-p)
narrowing-open-id-var-endpoints⊥
    (cross (id-＇ (suc X))) src-p refl () open-id
narrowing-open-id-var-endpoints⊥
    (cross (id-‵ ι)) src-p tgt-p occ ()
narrowing-open-id-var-endpoints⊥
    (cross (sʷ ↦ tⁿ)) src-p tgt-p occ ()
narrowing-open-id-var-endpoints⊥
    (cross (`∀ sⁿ)) src-p tgt-p occ ()
narrowing-open-id-var-endpoints⊥
    id★ src-p tgt-p occ ()
narrowing-open-id-var-endpoints⊥
    (gen sⁿ) src-p tgt-p occ ()
narrowing-open-id-var-endpoints⊥
    (gG ？︔ sⁿ) src-p tgt-p occ ()
narrowing-open-id-var-endpoints⊥
    (sⁿ ︔seal β) src-p tgt-p occ ()

gen-body-open-id-var⊥ :
  ∀ {μ Δ Σ A B p α β} →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ p ∶ ⇑ᵗ A =⇒ B →
  Narrowing p →
  occurs zero B ≡ true →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
gen-body-open-id-var⊥ p⊢ pⁿ occ open-id =
  narrowing-open-id-var-endpoints⊥ pⁿ
    (proj₁ (coercion-src-tgtᵐ p⊢))
    (proj₂ (coercion-src-tgtᵐ p⊢))
    occ
    open-id

gen-open-id-var⊥ :
  ∀ {μ Δ Σ A C D p α β} →
  μ ∣ Δ ∣ Σ ⊢ gen A p ∶ C ⊒ D →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
gen-open-id-var⊥
    (cast-gen hA occ p⊢ , gen pⁿ) open-id =
  gen-body-open-id-var⊥ p⊢ pⁿ occ open-id

gen-open-id-var∃⊥ :
  ∀ {Δ Σ A C D p α β} →
  Δ ∣ Σ ⊢ gen A p ∶ C ⊒ D →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
gen-open-id-var∃⊥ (μ , p⊒) open-id =
  gen-open-id-var⊥ p⊒ open-id

castLike-gen-open-id-var⊥ :
  ∀ {Δ Σ C D c A p α β} →
  c ≡ gen A p →
  Δ ∣ Σ ⊢ c ∶ᶜ C ⊒ D →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
castLike-gen-open-id-var⊥ refl cᶜ open-id =
  gen-open-id-var⊥ cᶜ open-id

narrowing-gen-open-id-var∃-eq⊥ :
  ∀ {Δ Σ C D c A p α β} →
  c ≡ gen A p →
  Δ ∣ Σ ⊢ c ∶ C ⊒ D →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
narrowing-gen-open-id-var∃-eq⊥ refl c⊒ open-id =
  gen-open-id-var∃⊥ c⊒ open-id

termNarrowing-gen-open-id-var-aux⊥ :
  ∀ {Δ σ γ L L′ c A p α β} →
  c ≡ gen A p →
  Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ c →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
-- Induction on term narrowing: a `gen A p` index whose body opens to an
-- identity variable is impossible.  The endpoint reason is that `cast-gen`
-- types the body from `⇑ᵗ A`; no shifted source can be `＇ zero`, and any
-- shifted variable target has `occurs zero` false.
termNarrowing-gen-open-id-var-aux⊥ c≡gen
    (extend qᶜ pαᶜ M⊒N′) open-id =
  termNarrowing-gen-open-id-var-aux⊥ c≡gen M⊒N′ open-id
termNarrowing-gen-open-id-var-aux⊥ c≡gen
    (split qᶜ pαᶜ N⊒N′) open-id =
  termNarrowing-gen-open-id-var-aux⊥ c≡gen N⊒N′ open-id
termNarrowing-gen-open-id-var-aux⊥ refl (⊒blame pᶜ) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ refl (x⊒x pᶜ x∋p) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ ()
    (ƛ⊒ƛ p↦qᶜ N⊒N′) open-id
termNarrowing-gen-open-id-var-aux⊥ refl
    (·⊒· qᶜ L⊒L′ M⊒M′) open-id =
  gen-open-id-var⊥ qᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ ()
    (Λ⊒Λ allᶜ vV V⊒V′) open-id
termNarrowing-gen-open-id-var-aux⊥ refl (⊒Λ pᶜ N⊒V′) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ refl
    (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ c≡gen
    (α⊒α γ′≡ qᶜ pαᶜ L⊒L′) open-id =
  castLike-gen-open-id-var⊥ c≡gen pαᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ c≡gen
    (⊒α γ′≡ pαᶜ L⊒L′) open-id =
  castLike-gen-open-id-var⊥ c≡gen pαᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ refl
    (ν⊒ν pᶜ qᶜ N⊒N′) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ refl (⊒ν pᶜ N⊒N′) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ refl (ν⊒ pᶜ N⊒N′) open-id =
  gen-open-id-var⊥ pᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ ()
    (κ⊒κ κ) open-id
termNarrowing-gen-open-id-var-aux⊥ ()
    (⊕⊒⊕ M⊒M′ N⊒N′) open-id
termNarrowing-gen-open-id-var-aux⊥ refl (⊒cast+ qᶜ q⨟s≈r M⊒M′)
    open-id =
  gen-open-id-var⊥ qᶜ open-id
termNarrowing-gen-open-id-var-aux⊥ refl
    (⊒cast- qᶜ wfΣ q⊒ s⊒
      (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)
      M⊒M′)
    open-id =
  gen-open-id-var∃⊥ r⊒ open-id
termNarrowing-gen-open-id-var-aux⊥ refl
    (cast+⊒ pᶜ wfΣ t⊒ p⊒
      (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒)
      M⊒M′)
    open-id =
  gen-open-id-var∃⊥ r⊒ open-id
termNarrowing-gen-open-id-var-aux⊥ refl (cast-⊒ pᶜ r≈t⨟p M⊒M′)
    open-id =
  gen-open-id-var⊥ pᶜ open-id

termNarrowing-gen-open-id-var⊥ :
  ∀ {Δ σ γ L L′ A p α β} →
  Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ gen A p →
  p [ β ]ᶜ ≡ id (＇ α) →
  ⊥
termNarrowing-gen-open-id-var⊥ L⊒L′ open-id =
  termNarrowing-gen-open-id-var-aux⊥ refl L⊒L′ open-id

LeftSealNarrowingInversion : Set₁
LeftSealNarrowingInversion =
  ∀ {Δ σ γ V V′ α} →
  Value V →
  Δ ∣ σ ∣ γ ⊢ V ⟨ seal ★ α ⟩ ⊒ V′ ∶ id (＇ α) →
  ∃[ r ] (Δ ∣ srcStoreⁿ σ ⊢ r ∶ ★ ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ V ⊒ V′ ∶ r

termNarrowing-resp-≈ :
  ∀ {Δ σ γ M M′ p q A B} →
  Δ ∣ σ ⊢ p ≈ q ∶ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q
-- This is the natural induction principle needed by the direct cast case.
-- It may need to be weakened or restricted: the `⊒blame` rule currently
-- requires a cast-like index, not merely an endpoint-equivalent narrowing.
termNarrowing-resp-≈ p≈q M⊒M′ = {!!}

termNarrowing-resp-source :
  ∀ {Δ σ γ M M′ p q A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q
-- This is the source-store version needed after applying the recursive
-- inversion under `⊒ν`: the IH witness is typed at `srcStoreⁿ σ`, while the
-- canonical cast-like witness is also typed at that same source store.
termNarrowing-resp-source p⊒ qᶜ M⊒M′ = {!!}

leftSealNarrowingInversion-aux :
  ∀ {Δ σ γ M V V′ p α} →
  M ≡ V ⟨ seal ★ α ⟩ →
  p ≡ id (＇ α) →
  Value V →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V′ ∶ p →
  ∃[ r ] (Δ ∣ srcStoreⁿ σ ⊢ r ∶ ★ ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ V ⊒ V′ ∶ r
-- Store/context-shaping cases: these need inversion through de Bruijn
-- type-variable substitution in both the left term and the coercion index.
leftSealNarrowingInversion-aux eq idx-eq vV
    (extend qᶜ pαᶜ M⊒N′) = {!!}
leftSealNarrowingInversion-aux eq idx-eq vV
    (split qᶜ pαᶜ N⊒N′) = {!!}
-- Type-application/ν-opening cases: `⊒α` is impossible by the gen/open
-- endpoint-shifting lemma above; `⊒ν` still has the substitution issue.
leftSealNarrowingInversion-aux () idx-eq vV
    (α⊒α γ′≡ qᶜ pαᶜ L⊒L′)
leftSealNarrowingInversion-aux eq idx-eq vV
    (⊒α γ′≡ pαᶜ L⊒L′) = {!!}
leftSealNarrowingInversion-aux eq refl vV
    (⊒ν {A = A} (cast-id hα ok , cross (id-＇ α)) N⊒N′)
    with leftSealNarrowingInversion-aux
           (cong ⇑ᵗᵐ eq)
           refl
           (renameᵗᵐ-preserves-Value suc vV)
           N⊒N′
leftSealNarrowingInversion-aux eq refl vV
    (⊒ν {A = A} (cast-id hα ok , cross (id-＇ α)) N⊒N′)
    | r , r⊒ , V⊒N′ =
  -- Reindexing `V⊒N′` to a canonical shifted `★ ⊒ ＇ suc α`
  -- narrowing is not enough: the `⊒ν` conclusion fixes the right ν
  -- annotation to `⇑ᶜ p`.  The actual target term here contains
  -- `⇑ᶜ (id (＇ α))`, so applying `⊒ν` with a canonical `★ ⊒ ＇ α`
  -- index would produce a different right-hand term.
  {!!}
-- Left positive cast: Agda can expose this case with the equality-indexed
-- helper, but the proof still needs inversion of the dual coercion `- t`.
leftSealNarrowingInversion-aux eq refl vV
    (cast+⊒ pᶜ wfΣ t⊒ p⊒
      (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒)
      M⊒M′) = {!!}
leftSealNarrowingInversion-aux refl refl vV
    (⊒blame (cast-id hα ok , cross (id-＇ α))) =
  (＇ α) ？ ,
  (tag-or-idᵈ ,
    (cast-untag hα (＇ α) refl , untag (＇ α))) ,
  ⊒blame
    (cast-untag hα (＇ α) refl , untag (＇ α))
-- Right cast cases: the paper says these recurse because the cast must be
-- identity-like, but endpoint equivalence does not yet give that directly.
leftSealNarrowingInversion-aux refl refl vV
    (⊒cast+ (cast-id hα okα , cross (id-＇ α)) wfΣ q⊒ s⊒
      (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)
      M⊒M′) = {!!}
leftSealNarrowingInversion-aux refl refl vV
    (⊒cast- qᶜ wfΣ q⊒ s⊒
      (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)
      M⊒M′) = {!!}
leftSealNarrowingInversion-aux refl refl vV
    (cast-⊒ {r = r} pᶜ wfΣ
      t⊒@(cast-seal h★′ α∈Σ seal-ok , sealⁿ ★ α)
      p⊒@(cast-id hα okα , cross (id-＇ α))
      (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒)
      M⊒M′) =
  -- Direct left negative cast: the typed `★`-to-`α` witness comes from the
  -- composed coercion at the source endpoint store.  The remaining work is
  -- reindexing the premise from `r` to that composed coercion.
  proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ,
  subst
    (λ Σ → _ ∣ Σ ⊢
      proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ ★ ⊒ _)
    (srcStoreⁿ-⊒ˢ σ⊒)
    u⊒ ,
  termNarrowing-resp-≈
    (endpointsⁿ src-r tgt-r src-u tgt-u σ⊒ wfΣ₁ wfΣ₂ r⊒ u⊒)
    M⊒M′

leftSealNarrowingInversion : LeftSealNarrowingInversion
leftSealNarrowingInversion vV M⊒V′ =
  leftSealNarrowingInversion-aux refl refl vV M⊒V′

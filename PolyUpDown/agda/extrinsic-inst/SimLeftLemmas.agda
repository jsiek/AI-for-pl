{-# OPTIONS --allow-unsolved-metas #-}
module SimLeftLemmas where

-- File Charter:
--   * Local helper lemmas for the left-to-right simulation proof in
--   * `DGGSim.agda`.
--   * Provides the beta-family lemmas used by `sim-left`: ordinary beta,
--     left-up function casts, and left-down function casts.
--   * Keeps the catchup and substitution proof obligations owned by these
--     lemmas next to the lemmas that use them.

open import Data.List using ([]; List; length; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import UpDown using
  ( Up
  ; Down
  ; CastPerm
  ; wt-tag
  ; wt-unseal
  ; wt-unseal★
  ; wt-↦
  ; wt-∀
  ; wt-ν
  ; wt-id
  ; wt-untag
  ; wt-seal
  ; wt-seal★
  ; cast-tag
  ; _∣_∣_∣_⊢_⦂_⊑_
  ; _∣_∣_∣_⊢_⦂_⊒_
  )
open import Store using (StoreWf; _⊆ˢ_; lookup-unique; storeWf-unique)
open import ImprecisionIndexed
open import Terms using (Term; ƛ_⇒_; _·_; _⦂∀_[_]; _up_; _down_; wk⊒)
open import TermProperties using (_[_])
open import TermImprecisionIndexed
open import ReductionFresh
open import PreservationFresh using (length-append-tag; wkΨ-cast-tag-⊒)
open import ProgressFresh
  using (StarView; sv-up-tag; canonical-★; SealView; sv-down-seal; canonical-｀)

-- Bridge lemmas: canonical-forms inversion lifted from typing to imprecision.
-- The catchup-residual cases (`wt-untag` at type ★, and `wt-unseal`/
-- `wt-unseal★` at type `｀ α`) need to learn V′'s shape from `Value V′`
-- plus a relation `V ⊑ V′ ⦂ A ⊑ ★` (resp. `⦂ A ⊑ ｀ α`). Routing through
-- `⊑-right-typed` recovers a typing of V′ at the right-side type, after
-- which `canonical-★` / `canonical-｀` from `ProgressFresh` apply.

canonical-★-imprecision :
  ∀ {Ψˡ Σˡ V V′ A} →
  Value V′ →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ ★ →
  StarView V′
canonical-★-imprecision vV′ rel = canonical-★ vV′ (⊑-right-typed rel)

canonical-｀-imprecision :
  ∀ {Ψˡ Σˡ V V′ A α} →
  Value V′ →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ ｀ α →
  SealView {α = α} V′
canonical-｀-imprecision vV′ rel = canonical-｀ vV′ (⊑-right-typed rel)

{-
   If V ⊑ N′ then N′ —↠ V′ and V ⊑ V′.
-}
mutual
  right-extra-up-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ u′} →
    {pB : [] ⊢ A ⊑ᵢ B′} →
    (Φ : List CastPerm) →
    length Φ ≡ Ψˡ →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
    0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
      Σ[ W′ ∈ Term ]
        (Value W′ ×
         (Σʳ ∣ (V′ up u′) —↠ Σʳ′ ∣ W′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ W′ ⦂ A ⊑ B′))
  right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-tag p g ok) =
    Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up tag , (V′ up u′ ∎) ,
    ⊑upR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-tag p g ok)
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ (_down_ vV vd) (_down_ vV′ seal)
    (⊑down {pA = pA} Φd lenΦd rel hd (wt-seal d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    with right-extra-down-catchup-left {pB = {!!}} Φd lenΦd wfΣˡ wfΣʳ
           vV vV′ rel hd d⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ (_down_ vV vd) (_down_ vV′ seal)
    (⊑down {pA = pA} Φd lenΦd rel hd (wt-seal d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
      rewrite lookup-unique (storeWf-unique wfΣˡ) h h′
      with right-extra-up-catchup {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ
           (vV down vd) vV′ᵥ V⊑V′ᵥ u⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ (_down_ vV vd) (_down_ vV′ seal)
    (⊑down {pA = pA} Φd lenΦd rel hd (wt-seal d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′ᵥup↠W′ , V⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    (_ —→⟨ id-step (seal-unseal vV′) ⟩
     multi-trans (up-↠ V′↠V′ᵥ) V′ᵥup↠W′) ,
    V⊑W′
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ (_down_ vV vd) (_down_ vV′ seal)
    (⊑down {pA = pA} Φd lenΦd rel hd (wt-seal★ d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    with right-extra-down-catchup-left {pB = {!!}} Φd lenΦd wfΣˡ wfΣʳ
           vV vV′ rel hd d⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ (_down_ vV vd) (_down_ vV′ seal)
    (⊑down {pA = pA} Φd lenΦd rel hd (wt-seal★ d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
      rewrite lookup-unique (storeWf-unique wfΣˡ) h h′
      with right-extra-up-catchup {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ
           (vV down vd) vV′ᵥ V⊑V′ᵥ u⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ (_down_ vV vd) (_down_ vV′ seal)
    (⊑down {pA = pA} Φd lenΦd rel hd (wt-seal★ d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′ᵥup↠W′ , V⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    (_ —→⟨ id-step (seal-unseal vV′) ⟩
     multi-trans (up-↠ V′↠V′ᵥ) V′ᵥup↠W′) ,
    V⊑W′
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV (_down_ vV′ seal)
    (⊑downR {pA = pA} Φd lenΦd rel (wt-seal d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    with right-extra-down-catchup {pB = {!!}} Φd lenΦd wfΣˡ wfΣʳ
           vV vV′ rel d⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV (_down_ vV′ seal)
    (⊑downR {pA = pA} Φd lenΦd rel (wt-seal d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
      rewrite lookup-unique (storeWf-unique wfΣˡ) h h′
      with right-extra-up-catchup {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ
             vV vV′ᵥ V⊑V′ᵥ u⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV (_down_ vV′ seal)
    (⊑downR {pA = pA} Φd lenΦd rel (wt-seal d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′ᵥup↠W′ , V⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    (_ —→⟨ id-step (seal-unseal vV′) ⟩
     multi-trans (up-↠ V′↠V′ᵥ) V′ᵥup↠W′) ,
    V⊑W′
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV (_down_ vV′ seal)
    (⊑downR {pA = pA} Φd lenΦd rel (wt-seal★ d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
      with right-extra-down-catchup {pB = {!!}} Φd lenΦd wfΣˡ wfΣʳ
             vV vV′ rel d⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV (_down_ vV′ seal)
    (⊑downR {pA = pA} Φd lenΦd rel (wt-seal★ d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
      rewrite lookup-unique (storeWf-unique wfΣˡ) h h′
      with right-extra-up-catchup {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ
             vV vV′ᵥ V⊑V′ᵥ u⊢
  right-extra-up-catchup
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV (_down_ vV′ seal)
    (⊑downR {pA = pA} Φd lenΦd rel (wt-seal★ d⊢ h′ α∈Φ′))
    (wt-unseal h α∈Φ u⊢)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , V′↠V′ᵥ , V⊑V′ᵥ
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′ᵥup↠W′ , V⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    (_ —→⟨ id-step (seal-unseal vV′) ⟩
     multi-trans (up-↠ V′↠V′ᵥ) V′ᵥup↠W′) ,
    V⊑W′
  right-extra-up-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel
    (wt-unseal h α∈Φ u⊢) = {!!}
  {- BLOCKED[Wclaude-C][catchup-unseal]:
     The right-side cast is `unseal α p` whose source type is ｀ α, so
     the hypothesis `rel : V ⊑ V′ ⦂ A ⊑ ｀ α` constrains V′ to a value at
     the abstract-name type ｀ α.  By `canonical-｀` (ProgressFresh.agda
     :176) the only such value shape is `V′ = (W′ down (seal q α))`.
     Twelve explicit clauses above (lines 73–180) cover the subcases
     where `rel` itself names this outer down with `⊑down`/`⊑downR`
     paired with `wt-seal`/`wt-seal★`; those clauses fire `seal-unseal`
     on the right and recurse with the inner up cast `u⊢`.

     The residual case is reachable when `rel` does NOT syntactically
     expose the outer `down seal` on V′.  Specifically:
       (a) `rel = ⊑upL …` — V = (M up u), V′ = M′ where M′ is the
           value-of-type-｀α and so canonicalizes to (W down seal q α)
           only after inverting the inner relation `M ⊑ M′ ⦂ ? ⊑ ｀ α`.
       (b) `rel = ⊑downL …` — V = (M down d), V′ = M′ similarly an
           outer-down value only via canonical inversion.

     Both shapes need a canonical-forms inversion (or a new helper that
     fires `seal-unseal` on V′ then composes the recursive answer with
     the extra `⊑upL`/`⊑downL` outer wrapper).  No such bridge lemma
     yet exists in this file; the parallel `right-extra-up-catchup-
     left` residual at line 281 is BLOCKED for the analogous reason.
  -}
  right-extra-up-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel
    (wt-unseal★ h α∈Φ p) = {!!}
  {- BLOCKED[Wclaude-C][catchup-unseal-star]:
     Same obstruction as `catchup-unseal` above, except the right-side
     cast is `unseal α p` typed by `wt-unseal★` (α sealed at ★ instead
     of at a richer source type).  The hypothesis `rel` still has
     shape V ⊑ V′ ⦂ A ⊑ ｀ α and V′ still canonicalizes via
     `canonical-｀` to `(W′ down (seal q α))`.  The reachable residual
     `rel`-shapes — `⊑upL` and `⊑downL` — both need a canonical-forms
     inversion plus an outer-cast composition lemma that does not yet
     exist here; the parallel `right-extra-up-catchup-left` residual
     at line 301 is BLOCKED for the analogous reason.
  -}
  right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-↦ hp hq) =
    Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up _↦_ , (V′ up u′ ∎) ,
    ⊑upR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-↦ hp hq)
  right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-∀ hp) =
    Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up ∀ᵖ , (V′ up u′ ∎) ,
    ⊑upR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-∀ hp)
  right-extra-up-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel
    (wt-ν hp) = {!!}
  right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-id wfA) =
    Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
    ((V′ up u′) —→⟨ id-step (id-up vV′) ⟩ V′ ∎) ,
    rel
  
  right-extra-down-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ d′} →
    {pB : [] ⊢ A ⊑ᵢ B′} →
    (Φ : List CastPerm) →
    length Φ ≡ Ψˡ →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
    0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
      Σ[ W′ ∈ Term ]
        (Value W′ ×
         (Σʳ ∣ (V′ down d′) —↠ Σʳ′ ∣ W′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ W′ ⦂ A ⊑ B′))
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel
    (wt-untag {G = G} g ok ℓ p)
    with canonical-★-imprecision vV′ rel
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = G′} {g = g′} vW′ refl
      with g ≟Ground g′
  ... | yes refl with rel
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑⦂∀-ν Aν Bν pν rel wfAν hTν instν =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑up {pB = pB′} Φu lenΦu rel hu (wt-tag q⊢ gq okq)
      with pB′
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑up Φu lenΦu rel hu (wt-tag q⊢ gq okq)
      | ⊑ᵢ-★★ =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑up Φu lenΦu rel hu (wt-tag q⊢ gq okq)
      | ⊑ᵢ-★ν xν =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑up Φu lenΦu rel hu (wt-tag q⊢ gq okq)
      | ⊑ᵢ-★ B H h pBH
      with ground-target-uniqueᵢ h g pBH {!!}
  ... | refl =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑up Φu lenΦu rel hu (wt-tag q⊢ gq okq)
      | ⊑ᵢ-ν B ★ occ pν =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑upL {pB = pB′} Φu lenΦu rel hu =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑upR {pB = pB′} Φu lenΦu rel (wt-tag q⊢ gq okq) =
    -- Tags match: V′ down (untag G ℓ p) —→ (W′ up q′) down p via
    -- tag-untag-ok. The result `(W′ up q′) down p` is not yet a value:
    -- need a recursive catchup that drives `up q′` then `down p`.
    -- That recursion requires inverting `rel` (case-split on ⊑upR/⊑up
    -- constructors) to extract a sub-relation `V ⊑ W′ ⦂ A ⊑ A_W`, then
    -- supplying `pB : [] ⊢ A ⊑ᵢ G` for the inner `right-extra-up-catchup`
    -- — currently no helper extracts this `A ⊑ᵢ G` from the cast typing
    -- `q′ ⦂ A_W ⊑ G` plus the outer `pA : A ⊑ᵢ ★`.
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑downL {pB = pB′} Φd lenΦd rel hd =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel₀
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = .G} {g = g′} vW′ refl
      | yes refl
      | ⊑blameR M⊢ =
    {!!}
  right-extra-down-catchup Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel
    (wt-untag {G = G} g ok ℓ p)
      | sv-up-tag {W = W′} {p = q′} {G = G′} {g = g′} vW′ refl
      | no  G≢G′ =
    -- Tags mismatch: V′ down (untag G ℓ p) —→ blame ℓ via tag-untag-bad.
    -- BUT the lemma's contract requires `Value W′` and blame is not a
    -- value, so producing the right outcome here violates the return
    -- type. Filling this case cleanly likely needs the catchup lemma's
    -- return type relaxed to (Value W′ ⊎ ∃ ℓ. W′ ≡ blame ℓ), or a new
    -- variant lemma for blame-producing catchups.
    {!!}
  right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-seal p h α∈Φ) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
    ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-seal p h α∈Φ)
  right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-seal★ p h α∈Φ) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
    ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-seal★ p h α∈Φ)
  right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-↦ hp hq) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down _↦_ , (V′ down d′ ∎) ,
    ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-↦ hp hq)
  right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-∀ hp) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ∀ᵖ , (V′ down d′ ∎) ,
    ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-∀ hp)
  right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
    {pB = pB} Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-ν hp) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ν_ , (V′ down d′ ∎) ,
    ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel (wt-ν hp)
  right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-id wfA) =
    Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
    ((V′ down d′) —→⟨ id-step (id-down vV′) ⟩ V′ ∎) ,
    rel
  
  right-extra-up-catchup-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ u u′} →
    {pB : [] ⊢ B ⊑ᵢ B′} →
    (Φ : List CastPerm) →
    length Φ ≡ Ψˡ →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
    0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ u ⦂ A ⊑ B →
    0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
      Σ[ W′ ∈ Term ]
        (Value W′ ×
         (Σʳ ∣ (V′ up u′) —↠ Σʳ′ ∣ W′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
            (V up u) ⊑ W′ ⦂ B ⊑ B′))
  right-extra-up-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu (wt-tag p g ok) =
    Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up tag , (V′ up u′ ∎) ,
    ⊑up {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hu (wt-tag p g ok)
  right-extra-up-catchup-left Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu
    (wt-unseal h α∈Φ p) = {!!}
  {- BLOCKED[Wclaude-D][catchup-left-unseal]:
     The right-side cast is `unseal α p` with source type ｀ α, so the
     relation `rel : V ⊑ V′ ⦂ A ⊑ ｀ α` constrains V′ to a canonical form
     at the abstract-name type ｀ α.  In the parallel non-`-left` lemma
     `right-extra-up-catchup`, twelve explicit clauses (lines 73–180)
     handle the case `V′ = V′₀ down seal` with relation `⊑down`/`⊑downR`
     by reducing right via `seal-unseal` and recursing — but that residual
     hole at line 182 is also unfilled because no helper inverts the
     relation to rule out other shapes (e.g. `V′ = V′₀ up id` at type ｀ α
     via `wt-id`, or yet other ⊑downL/⊑upL forms).  The `-left` variant
     adds an extra left-side cast `u` that must additionally be preserved
     or composed in the result, requiring `⊑up` (two-sided) instead of
     `⊑upR`.  Even if we fired the matching `seal-unseal` step on the
     right, no existing lemma constructs `(V up u) ⊑ W′ ⦂ B ⊑ B′` from
     the recursive answer plus the left cast `hu`.  This needs a
     canonical-forms-at-｀ α lemma plus a left-cast-composition bridge
     analogous to the `wt-untag` BLOCKED at line 327.
  -}
  right-extra-up-catchup-left Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu
    (wt-unseal★ h α∈Φ p) = {!!}
  {- BLOCKED[Wclaude-D][catchup-left-unseal-star]:
     Same obstruction as `catchup-left-unseal` above: the right-side cast
     is `unseal α p` with `wt-unseal★` (α sealed at ★), so the relation
     `rel : V ⊑ V′ ⦂ A ⊑ ｀ α` again requires a canonical-forms inversion
     at type ｀ α plus a bridge lemma to compose the extra left cast `u`
     with the recursive result.  The parallel `right-extra-up-catchup`
     residual at line 184 is also unfilled.
  -}
  right-extra-up-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu (wt-↦ hp hq) =
    Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up _↦_ , (V′ up u′ ∎) ,
    ⊑up {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hu (wt-↦ hp hq)
  right-extra-up-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu (wt-∀ hp) =
    Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up ∀ᵖ , (V′ up u′ ∎) ,
    ⊑up {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hu (wt-∀ hp)
  right-extra-up-catchup-left Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu
    (wt-ν hp) = {!!}
  right-extra-up-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hu (wt-id wfA) =
    Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
    ((V′ up u′) —→⟨ id-step (id-up vV′) ⟩ V′ ∎) ,
    ⊑upL {pA = ⊑-type-imprecision rel} {pB = pB} Φ lenΦ rel hu
  
  right-extra-down-catchup-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ d d′} →
    {pB : [] ⊢ B ⊑ᵢ B′} →
    (Φ : List CastPerm) →
    length Φ ≡ Ψˡ →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
    0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ d ⦂ A ⊒ B →
    0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
      Σ[ W′ ∈ Term ]
        (Value W′ ×
         (Σʳ ∣ (V′ down d′) —↠ Σʳ′ ∣ W′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
            (V down d) ⊑ W′ ⦂ B ⊑ B′))
  right-extra-down-catchup-left Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd
    (wt-untag {G = G} g ok ℓ p)
    with canonical-★-imprecision vV′ rel
  ... | sv-up-tag {W = W′} {p = q′} {G = G′} {g = g′} vW′ refl
    with g ≟Ground g′
  ... | yes refl =
    -- Tags match: V′ down (untag G ℓ p) —→ (W′ up q′) down p via
    -- tag-untag-ok. Same recursive obstruction as the non-`-left`
    -- variant, plus the `-left` form additionally needs to compose the
    -- left cast `d` (from `hd`) with the recursive answer — neither
    -- bridge lemma is available yet.
    {!!}
  ... | no  G≢G′ =
    -- Tags mismatch: blame ℓ result violates the lemma's `Value W′`
    -- contract (same issue as `right-extra-down-catchup`'s wt-untag);
    -- a relaxed return type is needed before this case can land.
    {!!}
  {- BLOCKED[Wclaude-B][catchup-left-untag]:
     The other wt-* clauses below (wt-seal / wt-seal★ / wt-↦ / wt-∀ /
     wt-ν) take ZERO right-side reductions and return `V′ down d′`
     because each of those cast-tag forms is a DownValue.  But
     `untag G ℓ p` is NOT a DownValue (Terms.agda:119), so
     `V′ down (untag G ℓ p)` is not a value and the template pattern
     does not apply — the right side genuinely must reduce.

     A real reduction is required: by canonical forms at ★, V′ must be
     `W up (tag p′ G′)`, so the right reduces via tag-untag-ok (G ≡ G′)
     to `(W up p′) down p` or via tag-untag-bad to `blame ℓ`.  The
     natural delegation is:

         right-extra-down-catchup {pB = ???}
           Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel (wt-untag g ok ℓ p)

     yielding `V ⊑ W′ ⦂ A ⊑ B′`, then wrap with `⊑downL` to add the
     left-side `d` cast.  But that helper expects a witness
     `pB : [] ⊢ A ⊑ᵢ B′` relating the LEFT source A (from hd : d ⦂ A ⊒ B)
     to the RIGHT target B′ (from wt-untag : ★ ⊒ B′).  The only
     in-scope type-imprecision facts are `[] ⊢ A ⊑ᵢ ★` (from rel) and
     `[] ⊢ B ⊑ᵢ B′` (the input pB), and there is no general inversion
     `A ⊑ᵢ ★` + `★ ⊒ B′` ⇒ `A ⊑ᵢ B′`.  The analogous wt-untag clause
     of right-extra-down-catchup (line ~222) and the wt-unseal /
     wt-unseal★ clauses of right-extra-up-catchup-left (lines ~281,
     ~283) are also unfilled, suggesting this whole family needs a new
     canonical-forms-at-★ + matched-tag-untag bridge lemma before any
     of them can be discharged.
  -}
  right-extra-down-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd (wt-seal p h α∈Φ) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
    ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hd (wt-seal p h α∈Φ)
  right-extra-down-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd (wt-seal★ p h α∈Φ) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
    ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hd (wt-seal★ p h α∈Φ)
  right-extra-down-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd (wt-↦ hp hq) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down _↦_ , (V′ down d′ ∎) ,
    ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hd (wt-↦ hp hq)
  right-extra-down-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd (wt-∀ hp) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ∀ᵖ , (V′ down d′ ∎) ,
    ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hd (wt-∀ hp)
  right-extra-down-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd (wt-ν hp) =
    Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ν_ , (V′ down d′ ∎) ,
    ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
      Φ lenΦ rel hd (wt-ν hp)
  right-extra-down-catchup-left
    {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
    Φ lenΦ wfΣˡ wfΣʳ vV vV′ rel hd (wt-id wfA) =
    Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
    ((V′ down d′) —→⟨ id-step (id-down vV′) ⟩ V′ ∎) ,
    ⊑downL {pA = ⊑-type-imprecision rel} {pB = pB} Φ lenΦ rel hd
  
  left-value-right-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ N′ ⦂ A ⊑ B →
    Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ Σʳ′ ∈ Store ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
      Σ[ V′ ∈ Term ]
        (Value V′ ×
         (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
         (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ B))
  left-value-right-catchup wfΣˡ wfΣʳ vV (⊑` ())
  left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (ƛ A ⇒ N)
    (⊑ƛ {A′ = A′} {M′ = N′} {pA = pA} {pB = pB} hA hA′ rel) =
    Ψʳ , Σʳ , wfΣʳ , ƛ A′ ⇒ N′ , ƛ A′ ⇒ N′ , (ƛ A′ ⇒ N′ ∎) ,
    ⊑ƛ {pA = pA} {pB = pB} hA hA′ rel
  left-value-right-catchup wfΣˡ wfΣʳ () (⊑· L⊑L′ M⊑M′)
  left-value-right-catchup wfΣˡ wfΣʳ () (⊑⦂∀ rel wfA wfB hT)
  left-value-right-catchup wfΣˡ wfΣʳ () (⊑⦂∀-ν A B p rel wfA hT inst)
  left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} wfΣˡ wfΣʳ ($ κ) ⊑$ =
    Ψʳ , Σʳ , wfΣʳ , $ κ , $ κ , ($ κ ∎) , ⊑$
  left-value-right-catchup wfΣˡ wfΣʳ () (⊑⊕ L⊑L′ M⊑M′)
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_up_ {V = V} {p = u} vV vu)
    (⊑up {B = B} {B′ = B′} {pB = pB} {u′ = u′} Φ lenΦ rel hu hu′)
      with left-value-right-catchup wfΣˡ wfΣʳ vV rel
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_up_ {V = V} {p = u} vV vu)
    (⊑up {B = B} {B′ = B′} {pB = pB} {u′ = u′} Φ lenΦ rel hu hu′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , M′↠V′ᵥ , V⊑V′ᵥ
      with right-extra-up-catchup-left {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ
             vV vV′ᵥ V⊑V′ᵥ hu hu′
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_up_ {V = V} {p = u} vV vu)
    (⊑up {B = B} {B′ = B′} {pB = pB} {u′ = u′} Φ lenΦ rel hu hu′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , M′↠V′ᵥ , V⊑V′ᵥ
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′ᵥup↠W′ , Vup⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    multi-trans (up-↠ M′↠V′ᵥ) V′ᵥup↠W′ ,
    Vup⊑W′
  {-
      Case E ⊢ (V up p) ⊑ (M′ up u′) ⦂ B ⊑ B′
                                       ^^
                                       |  \
               V        ⊑ M′         ⦂ A₁ ⊑ A′

      have:
        V ⊑ M′ ⦂ A₁ ⊑ A′
        u′ ⦂ A′ ⊑ B
        p ⦂ A₁ ⊑ A
        pB : [] ⊢ A ⊑ᵢ B   (not in scope)
        pA : [] ⊢ A₁ ⊑ᵢ A′   (not in scope)
      nts:
        M′ up u′ —↠ V′
        V up p ⊑ V′     for some V′
  -}
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_up_ vV vu) (⊑upL {pB = pB} Φ lenΦ rel hu)
      with left-value-right-catchup wfΣˡ wfΣʳ vV rel
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_up_ vV vu) (⊑upL {pB = pB} Φ lenΦ rel hu)
    | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
    Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
    ⊑upL {pA = ⊑-type-imprecision V⊑V′} {pB = pB} Φ lenΦ V⊑V′ hu
  left-value-right-catchup
    {Σʳ = Σʳ} wfΣˡ wfΣʳ vV (⊑upR {pB = pB} Φ lenΦ rel hu′)
      with left-value-right-catchup wfΣˡ wfΣʳ vV rel
  left-value-right-catchup
    {Σʳ = Σʳ} wfΣˡ wfΣʳ vV (⊑upR {pB = pB} Φ lenΦ rel hu′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
      with right-extra-up-catchup {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ vV vV′ V⊑V′ hu′
  left-value-right-catchup
    {Σʳ = Σʳ} wfΣˡ wfΣʳ vV (⊑upR {pB = pB} Φ lenΦ rel hu′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′up↠W′ , V⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    multi-trans (up-↠ M′↠V′) V′up↠W′ ,
    V⊑W′
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_down_ vV vd) (⊑down {pB = pB} Φ lenΦ rel hd hd′)
      with left-value-right-catchup wfΣˡ wfΣʳ vV rel
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_down_ vV vd) (⊑down {pB = pB} Φ lenΦ rel hd hd′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
      with right-extra-down-catchup-left {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ
             vV vV′ V⊑V′ hd hd′
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_down_ vV vd) (⊑down {pB = pB} Φ lenΦ rel hd hd′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′down↠W′ , Vdown⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    multi-trans (down-↠ M′↠V′) V′down↠W′ ,
    Vdown⊑W′
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_down_ vV vd) (⊑downL {pB = pB} Φ lenΦ rel hd)
      with left-value-right-catchup wfΣˡ wfΣʳ vV rel
  left-value-right-catchup
    {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (_down_ vV vd) (⊑downL {pB = pB} Φ lenΦ rel hd)
    | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
    Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
    ⊑downL {pA = ⊑-type-imprecision V⊑V′} {pB = pB}
      Φ lenΦ V⊑V′ hd
  left-value-right-catchup
    {Σʳ = Σʳ} wfΣˡ wfΣʳ vV (⊑downR {pB = pB} Φ lenΦ rel hd′)
      with left-value-right-catchup wfΣˡ wfΣʳ vV rel
  left-value-right-catchup
    {Σʳ = Σʳ} wfΣˡ wfΣʳ vV (⊑downR {pB = pB} Φ lenΦ rel hd′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
      with right-extra-down-catchup {pB = pB} Φ lenΦ wfΣˡ wfΣʳᵃ vV vV′ V⊑V′ hd′
  left-value-right-catchup
    {Σʳ = Σʳ} wfΣˡ wfΣʳ vV (⊑downR {pB = pB} Φ lenΦ rel hd′)
    | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
    | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′down↠W′ , V⊑W′ =
    Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
    multi-trans (down-↠ M′↠V′) V′down↠W′ ,
    V⊑W′
  left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
    wfΣˡ wfΣʳ (Λ N) (⊑Λ {M′ = N′} {p = p} vM vM′ wfA wfB rel) =
    Ψʳ , Σʳ , wfΣʳ , Λ N′ , Λ N′ , (Λ N′ ∎) ,
    ⊑Λ {p = p} vM vM′ wfA wfB rel
  left-value-right-catchup wfΣˡ wfΣʳ () (⊑blameR M⊢)

--------------------------------------------------------------------------------
-- GTLC `sim-beta`, adapted to imprecision orientation.

sim-left-beta :
  ∀ {Ψ Ψʳ Σˡ Σʳ V′ W W′ N A A′ A₂ B B′} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (ƛ A₂ ⇒ N) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  StoreWf 0 Ψ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ N [ W ] ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta
  {Σʳ = Σʳ} {W′ = W′}
  (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel)
  wfΣˡ wfΣʳ (ƛ A′ ⇒ N′) W⊑W′ vW vW′ =
  Σʳ , N′ [ W′ ] ,
  (((ƛ A′ ⇒ N′) · W′) —→⟨ id-step (β vW′) ⟩
   (N′ [ W′ ]) ∎) ,
  []-⊑ {pA = pA} {pB = pB} rel W⊑W′
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣˡ wfΣʳ vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ}
           rel wfΣˡ wfΣʳᵃ vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N[W]⊑N′} {pB = pCod′}
    Φ lenΦ N[W]⊑N′ hq
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣˡ wfΣʳ vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ}
           rel wfΣˡ wfΣʳᵃ vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N[W]⊑N′} {pB = pCod′}
    Φ lenΦ N[W]⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `up` function casts.
sim-left-beta-up :
  ∀ {Ψ Ψʳ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {p : Down} {q : Up} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (V up (Up._↦_ p q)) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  StoreWf 0 Ψ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V · (W down p)) up q) ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta-up
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑upL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑upL {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑downL {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp))
    hq
sim-left-beta-up
  {Σʳ = Σʳ} {W′ = W′}
  (⊑up {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-up-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑up {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑down {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp hp′))
    hq hq′
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣˡ wfΣʳ vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣˡ
           wfΣʳᵃ vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣˡ wfΣʳ vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣˡ
           wfΣʳᵃ vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `down` function casts.
sim-left-beta-down :
  ∀ {Ψ Ψʳ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {p : Up} {q : Down} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (V down (Down._↦_ p q)) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  StoreWf 0 Ψ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V · (W up p)) down q) ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta-down
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
    (⊑downL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑downL {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑upL {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp))
    hq
sim-left-beta-down
  {Σʳ = Σʳ} {W′ = W′}
    (⊑down {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-down-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑down {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑up {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp hp′))
    hq hq′
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣˡ wfΣʳ vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣˡ
           wfΣʳᵃ vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣˡ wfΣʳ vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣˡ
           wfΣʳᵃ vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
    (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣˡ wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-left` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-left-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `DGGSim.agda` hole lines it supports.

-- Worker W01 helper slot

-- Worker W02 helper slot

-- Worker W03 helper slot

-- Supports DGGSim.agda H42 (line 528): eliminate a left identity-down cast,
-- commuting through right-only casts.
sim-left-w03-id-down :
  ∀ {Ψ Σˡ Σʳ V M′ C A B} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ (V down Down.id C) ⊑ M′ ⦂ A ⊑ B →
  Σ[ N′ ∈ Term ]
    ((Σʳ ∣ M′ —↠ Σʳ ∣ N′) ×
     (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ N′ ⦂ A ⊑ B))
sim-left-w03-id-down (⊑upR {pB = pB} Φ lenΦ rel hu′)
    with sim-left-w03-id-down rel
sim-left-w03-id-down (⊑upR {pB = pB} Φ lenΦ rel hu′)
  | N′ , M′↠N′ , V⊑N′ =
  N′ up _ , up-↠ M′↠N′ ,
  ⊑upR {pA = ⊑-type-imprecision V⊑N′} {pB = pB}
    Φ lenΦ V⊑N′ hu′
sim-left-w03-id-down (⊑down {pB = pB} Φ lenΦ rel (UpDown.wt-id wfA) hd′) =
  _ , (_ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd′
sim-left-w03-id-down (⊑downL Φ lenΦ rel (UpDown.wt-id wfA)) =
  _ , (_ ∎) , rel
sim-left-w03-id-down (⊑downR {pB = pB} Φ lenΦ rel hd′)
    with sim-left-w03-id-down rel
sim-left-w03-id-down (⊑downR {pB = pB} Φ lenΦ rel hd′)
  | N′ , M′↠N′ , V⊑N′ =
  N′ down _ , down-↠ M′↠N′ ,
  ⊑downR {pA = ⊑-type-imprecision V⊑N′} {pB = pB}
    Φ lenΦ V⊑N′ hd′

-- Worker W04 helper slot

-- Worker W05 helper slot

postulate
  -- Supports SimLeft.agda H28: eliminate a left seal/unseal redex,
  -- commuting through right-only casts.
  sim-left-w05-seal-unseal :
    ∀ {Ψ Σˡ Σʳ V M′ A B}
      {d : Down} {u : Up} {α : Seal} →
    Value V →
    ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
      ((V down (UpDown.seal d α)) up (UpDown.unseal α u)) ⊑ M′ ⦂ A ⊑ B →
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V down d) up u) ⊑ N′ ⦂ A ⊑ B))

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

postulate
  -- Supports SimLeft.agda H41: left `β-up-ν` allocation step.
  sim-left-w09-H41 :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ V M′ N A B} {u : Up} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
      (V up (UpDown.ν u)) ⊑ M′ ⦂ A ⊑ B →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Σˡ ∣ (V up (UpDown.ν u)) —→ Σˡ′ ∣ N →
    Value V →
    (Σ[ Ψˡ″ ∈ SealCtx ]
      Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
      Σ[ Σʳ′ ∈ Store ]
      Σ[ N′ ∈ Term ]
        ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
         (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] , plain-[] , refl ⟫ ⊢ N ⊑ N′ ⦂ A ⊑ B)))

-- Supports DGGSim.agda H09 (line 215): lift right multi-steps through
-- type application.
sim-left-w09-tyapp-↠ :
  ∀ {Σ Σ′ L L′ B T} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L ⦂∀ B [ T ]) —↠ Σ′ ∣ (L′ ⦂∀ B [ T ])
sim-left-w09-tyapp-↠ (L ∎) = (L ⦂∀ _ [ _ ]) ∎
sim-left-w09-tyapp-↠ (L —→⟨ L→M ⟩ M↠N) =
  (L ⦂∀ _ [ _ ]) —→⟨ ξ-·α L→M ⟩ sim-left-w09-tyapp-↠ M↠N

-- Supports DGGSim.agda H17 (line 275): weaken both down-cast typings
-- through the same seal-context extension and store growth.
sim-left-w09-down-casts-+ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}
    {d d′ : Down} →
  (k : ℕ) →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     ((Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) ×
      (Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)))
sim-left-w09-down-casts-+ zero w lenΦ hd hd′ =
  _ , lenΦ , wk⊒ w hd , wk⊒ w hd′
sim-left-w09-down-casts-+ (suc k) w lenΦ hd hd′
    with sim-left-w09-down-casts-+ k w lenΦ hd hd′
sim-left-w09-down-casts-+ (suc k) w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊒ hdᵣ ,
  wkΨ-cast-tag-⊒ hdᵣ′

sim-left-w09-down-casts-≤ :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}
    {d d′ : Down} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     ((Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)))
sim-left-w09-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
    with sim-left-w09-down-casts-+ (Ψ′ ∸ Ψ) w lenΦ hd hd′
sim-left-w09-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) eq hdᵣ ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′) eq hdᵣ′

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot

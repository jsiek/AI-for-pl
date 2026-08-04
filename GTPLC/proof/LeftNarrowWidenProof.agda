module proof.LeftNarrowWidenProof where

-- File Charter:
--   * Proves Left Narrowing and Left Widening for values.
--   * Uses one-context narrowing equations on the changing left factor.
--   * Delegates active tag and seal cancellation to inversion lemmas.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans)

open import Coercions
open import Terms
open import Reduction
open import TypeRelocate
open import NarrowWiden
open import FactoredTypeNarrowing
open import EnvironmentNarrowing
open import ImprecisionTheorems using (dualʷ; _⨟ⁿ_)
open import TermNarrowing
open import proof.LeftNarrowWiden
open import proof.LeftEnvironmentChange
open import proof.LeftWideningSealInversion
open import proof.LeftWideningTagInversion
open import proof.ImprecisionComposition using (untag-seq-composeⁿ)
open import proof.NarrowWidenDeterminism using (narrowing-determined)
open import proof.Progress using
  ( canonical-★
  ; canonical-tyvar
  ; DynValue
  ; SealValue
  ; sv-tag
  ; sv-seal
  )
open import proof.TermNarrowingTyping using
  (term-narrowing-source-typing)

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

left-narrowing : LeftNarrowing
left-narrowing {V = V} {ρ = ρ}
    {pᴸ = pᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = idᵃ a hA} wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  (keep ∷ []) , V ,
  ↠-step (pure-step (β-id vV)) ↠-refl ,
  vV , wfΣᴸ , ρ , left-keep left-done ,
  pᴸ , relocation , pᴿ , V⊒V′
left-narrowing {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = _↦_ {c = c} {d = d} c⊑ d⊒}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ c ↦ d ⟩ , ↠-refl , (vV ⟨ c ↦ d ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castⁿ⊒ {s⦂ = c⊑ ↦ d⊒} V⊒V′ eq
left-narrowing {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = ∀ⁿ_ {c = c} c⊒} wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ `∀ c ⟩ , ↠-refl , (vV ⟨ `∀ c ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castⁿ⊒ {s⦂ = ∀ⁿ c⊒} V⊒V′ eq
left-narrowing
    {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag G hG allowed G꞉B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    with canonical-★ vV (term-narrowing-source-typing V⊒V′)
left-narrowing
    {ρ = ρ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag G hG allowed G꞉B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-tag {W = W} {G = H} vW refl
    with left-widening-tag-inversion-match
      {H = G} {v⊑ = tag G hG allowed G꞉B} {pᴸ = qᴸ}
      wfΣᴸ vW vV′ V⊒V′ eq
left-narrowing
    {ρ = ρ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag G hG allowed G꞉B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-tag {W = W} {.G} vW refl
    | refl , qᴸ′ , qᴸ′≐qᴸ , W⊒V′ =
  (keep ∷ []) , W ,
  ↠-step (pure-step (tag-untag-ok vW)) ↠-refl ,
  vW , wfΣᴸ , ρ , left-keep left-done ,
  qᴸ′ , relocation , pᴿ , W⊒V′
left-narrowing
    {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag-seq {c = c} G hG allowed G꞉A c⊒ nonvarB A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    with canonical-★ vV (term-narrowing-source-typing V⊒V′)
left-narrowing
    {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag-seq {c = c} G hG allowed G꞉A c⊒ nonvarB A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-tag {W = W} {G = H} vW refl
    with left-widening-tag-inversion-match
      {H = G} {v⊑ = tag G hG allowed G꞉A}
      {pᴸ = (c , c⊒) ⨟ⁿ qᴸ} {qᴸ = pᴸ}
      wfΣᴸ vW vV′ V⊒V′
      (trans
        (sym (untag-seq-composeⁿ
          {G = G} {c = c} {d = proj₁ qᴸ}
          {hG = hG} {allowed = allowed} {G꞉A = G꞉A}
          {p = c⊒} {nonvarB = nonvarB}
          {A≢B = A≢B} {q = proj₂ qᴸ}))
        eq)
left-narrowing
    {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag-seq {c = c} G hG allowed G꞉A c⊒ nonvarB A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-tag {W = W} {.G} vW refl
    | refl , rᴸ , rᴸ≐c⨟qᴸ , W⊒V′
    with left-narrowing
      {ρ = ρ} {pᴸ = rᴸ} {qᴸ = qᴸ}
      {relocation = relocation} {pᴿ = pᴿ} {d⊒ = c⊒}
      wfΣᴸ wfΣᴿ vW vV′ W⊒V′ (sym rᴸ≐c⨟qᴸ)
left-narrowing
    {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = untag-seq {c = c} G hG allowed G꞉A c⊒ nonvarB A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-tag {W = W} {.G} vW refl
    | refl , rᴸ , rᴸ≐c⨟qᴸ , W⊒V′
    | χs , Z , Wc—↠Z , vZ , wfΣᴸ′ , ρ′ , changes ,
      qᴸ′ , relocation′ , pᴿ′ , Z⊒V′ =
  (keep ∷ keep ∷ χs) , Z ,
  ↠-step (pure-step (β-seq vV))
    (↠-step
      (ξ-⟨⟩ (pure-step (tag-untag-ok vW)))
      Wc—↠Z) ,
  vZ , wfΣᴸ′ , ρ′ , left-keep (left-keep changes) ,
  qᴸ′ , relocation′ , pᴿ′ , Z⊒V′
left-narrowing {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = seal {X = X} X<Δ hA X,A∈Σ allowed}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ seal X ⟩ , ↠-refl , (vV ⟨ seal X ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castⁿ⊒ {s⦂ = seal X<Δ hA X,A∈Σ allowed} V⊒V′ eq
left-narrowing
    {V = V} {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = seal-seq {X = X} {c = c}
      c⊒ X<Δ X,B∈Σ allowed A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    with left-narrowing
      {ρ = ρ} {pᴸ = pᴸ} {qᴸ = seal-bundle ⨟ⁿ qᴸ}
      {relocation = relocation} {pᴿ = pᴿ} {d⊒ = c⊒}
      wfΣᴸ wfΣᴿ vV vV′ V⊒V′
      (narrowing-determined wfΣᴸ
        ((c , c⊒) ⨟ⁿ (seal-bundle ⨟ⁿ qᴸ)) pᴸ)
  where
  seal-bundle = seal X , seal X<Δ (⊒-tgt-wf c⊒) X,B∈Σ allowed
left-narrowing
    {V = V} {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = seal-seq {X = X} {c = c}
      c⊒ X<Δ X,B∈Σ allowed A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | χs , Z , Vc—↠Z , vZ , wfΣᴸ′ , ρ′ , changes ,
      rᴸ , relocation′ , rᴿ , Z⊒V′ =
  (keep ∷ χs) ,
  Z ⟨ proj₁ (left-changeⁿ changes seal-bundle) ⟩ ,
  ↠-step (pure-step (β-seq vV))
    (Relation.Binary.PropositionalEquality.subst
      (λ d → V ⟨ c ⟩ ⟨ seal X ⟩ —↠[ χs ] Z ⟨ d ⟩)
      (sym (left-changeⁿ-coercion changes seal-bundle))
      (cast-trace Vc—↠Z)) ,
  Relation.Binary.PropositionalEquality.subst
    (λ d → Value (Z ⟨ d ⟩))
    (sym (left-changeⁿ-coercion changes seal-bundle))
    (vZ ⟨ leftChanges-preserves-Inert χs (seal X) ⟩) ,
  wfΣᴸ′ , ρ′ , left-keep changes ,
  left-changeⁿ changes qᴸ , relocation′ , rᴿ ,
  castⁿ⊒ {s⦂ = proj₂ (left-changeⁿ changes seal-bundle)} Z⊒V′
    (narrowing-determined wfΣᴸ′
      (left-changeⁿ changes seal-bundle ⨟ⁿ left-changeⁿ changes qᴸ)
      rᴸ)
  where
  seal-bundle = seal X , seal X<Δ (⊒-tgt-wf c⊒) X,B∈Σ allowed
left-narrowing {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {d⊒ = gen {c = c} nonvarA zero∈A hB c⊒ B≢★}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ gen c ⟩ , ↠-refl , (vV ⟨ gen c ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castⁿ⊒
    {s⦂ = gen nonvarA zero∈A hB c⊒ B≢★}
    V⊒V′ eq

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

left-widening : LeftWidening
left-widening {V = V} {ρ = ρ}
    {pᴸ = pᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = idᵃ a hA} wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  (keep ∷ []) , V ,
  ↠-step (pure-step (β-id vV)) ↠-refl ,
  vV , wfΣᴸ , ρ , left-keep left-done ,
  pᴸ , relocation , pᴿ , V⊒V′
left-widening {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = _↦_ {c = c} {d = d} c⊒ d⊑}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ c ↦ d ⟩ , ↠-refl , (vV ⟨ c ↦ d ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castʷ⊒ {s⦂ = c⊒ ↦ d⊑} V⊒V′ eq
left-widening {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = ∀ʷ_ {c = c} c⊑} wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ `∀ c ⟩ , ↠-refl , (vV ⟨ `∀ c ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castʷ⊒ {s⦂ = ∀ʷ c⊑} V⊒V′ eq
left-widening {V = V} {ρ = ρ}
    {qᴸ = qᴸ} {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = tag G hG allowed G꞉A}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  [] , V ⟨ G ! ⟩ , ↠-refl , (vV ⟨ G ! ⟩) ,
  wfΣᴸ , ρ , left-done ,
  qᴸ , relocation , pᴿ ,
  castʷ⊒ {s⦂ = tag G hG allowed G꞉A} V⊒V′ eq
left-widening
    {V = V} {ρ = ρ} {pᴸ = pᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = tag-seq {c = c} G c⊑ hG allowed G꞉B nonvarA A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    with left-widening
      {ρ = ρ} {pᴸ = pᴸ}
      {qᴸ = dualʷ (c , c⊑) ⨟ⁿ pᴸ}
      {relocation = relocation} {pᴿ = pᴿ} {u⊑ = c⊑}
      wfΣᴸ wfΣᴿ vV vV′ V⊒V′ refl
left-widening
    {V = V} {ρ = ρ} {pᴸ = pᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = tag-seq {c = c} G c⊑ hG allowed G꞉B nonvarA A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | χs , Z , Vc—↠Z , vZ , wfΣᴸ′ , ρ′ , changes ,
      rᴸ , relocation′ , rᴿ , Z⊒V′
    =
  (keep ∷ χs) ,
  Z ⟨ proj₁ (left-changeʷ changes tag-bundle) ⟩ ,
  ↠-step (pure-step (β-seq vV))
    (Relation.Binary.PropositionalEquality.subst
      (λ d → V ⟨ c ⟩ ⟨ G ! ⟩ —↠[ χs ] Z ⟨ d ⟩)
      (sym (left-changeʷ-coercion changes tag-bundle))
      (cast-trace Vc—↠Z)) ,
  Relation.Binary.PropositionalEquality.subst
    (λ d → Value (Z ⟨ d ⟩))
    (sym (left-changeʷ-coercion changes tag-bundle))
    (vZ ⟨ leftChanges-preserves-Inert χs (G !) ⟩) ,
  wfΣᴸ′ , ρ′ , left-keep changes ,
  (dualʷ (left-changeʷ changes tag-bundle) ⨟ⁿ rᴸ) ,
  relocation′ , rᴿ ,
  castʷ⊒
    {s⦂ = proj₂ (left-changeʷ changes tag-bundle)}
    Z⊒V′ refl
  where
  tag-bundle = G ! , tag G hG allowed G꞉B
left-widening
    {V = V} {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal X<Δ hA X,A∈Σ allowed}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    with canonical-tyvar vV (term-narrowing-source-typing V⊒V′)
left-widening
    {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal X<Δ hA X,A∈Σ allowed}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-seal {W = W} vW refl
    with left-widening-seal-inversion
      {u⊑ = unseal X<Δ hA X,A∈Σ allowed}
      {pᴸ = pᴸ} {qᴸ = qᴸ}
      wfΣᴸ vW vV′ V⊒V′ eq
left-widening
    {ρ = ρ} {pᴸ = pᴸ} {qᴸ = qᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal X<Δ hA X,A∈Σ allowed}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-seal {W = W} vW refl
    | qᴸ′ , qᴸ′≐qᴸ , W⊒V′ =
  (keep ∷ []) , W ,
  ↠-step (pure-step (seal-unseal vW)) ↠-refl ,
  vW , wfΣᴸ , ρ , left-keep left-done ,
  qᴸ′ , relocation , pᴿ , W⊒V′
left-widening
    {V = V} {ρ = ρ} {pᴸ = pᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal-seq {X = X} {c = c}
      X<Δ X,A∈Σ allowed c⊑ A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    with canonical-tyvar vV (term-narrowing-source-typing V⊒V′)
left-widening
    {ρ = ρ} {pᴸ = pᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal-seq {X = X} {c = c}
      X<Δ X,A∈Σ allowed c⊑ A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-seal {W = W} vW refl
    with left-widening-seal-inversion
      {u⊑ = unseal X<Δ (⊑-src-wf c⊑) X,A∈Σ allowed}
      {pᴸ = pᴸ}
      {qᴸ = dualʷ
        (unseal X , unseal X<Δ (⊑-src-wf c⊑) X,A∈Σ allowed)
        ⨟ⁿ pᴸ}
      wfΣᴸ vW vV′ V⊒V′ refl
left-widening
    {ρ = ρ} {pᴸ = pᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal-seq {X = X} {c = c}
      X<Δ X,A∈Σ allowed c⊑ A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-seal {W = W} vW refl
    | rᴸ , rᴸ≐unseal⨟pᴸ , W⊒V′
    with left-widening
      {ρ = ρ} {pᴸ = rᴸ}
      {qᴸ = dualʷ (c , c⊑) ⨟ⁿ rᴸ}
      {relocation = relocation} {pᴿ = pᴿ} {u⊑ = c⊑}
      wfΣᴸ wfΣᴿ vW vV′ W⊒V′ refl
left-widening
    {ρ = ρ} {pᴸ = pᴸ}
    {relocation = relocation} {pᴿ = pᴿ}
    {u⊑ = unseal-seq {c = c} X<Δ X,A∈Σ allowed c⊑ A≢B}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq
    | sv-seal {W = W} vW refl
    | rᴸ , rᴸ≐unseal⨟pᴸ , W⊒V′
    | χs , Z , Wc—↠Z , vZ , wfΣᴸ′ , ρ′ , changes ,
      qᴸ′ , relocation′ , pᴿ′ , Z⊒V′ =
  (keep ∷ keep ∷ χs) , Z ,
  ↠-step (pure-step (β-seq vV))
    (↠-step
      (ξ-⟨⟩ (pure-step (seal-unseal vW)))
      Wc—↠Z) ,
  vZ , wfΣᴸ′ , ρ′ , left-keep (left-keep changes) ,
  qᴸ′ , relocation′ , pᴿ′ , Z⊒V′
left-widening
    {u⊑ = inst nonvarA zero∈A hB c⊑ B≢★}
    wfΣᴸ wfΣᴿ vV vV′ V⊒V′ eq =
  {!!}

{-# OPTIONS --safe #-}

module proof.DGG.SimPairedAllValuesProof where

-- File Charter:
--   * Proves value-level forward simulation for paired type applications.
--   * Splits exhaustively over the five source universal roots and the target
--     value layers before discharging individual root squares.
--   * Is parameterized only by genuine lower semantic inductions.

open import Data.List using ([])
open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym; trans)

open import Types using
  (Ty; TyCtx; ★; `∀; ＇_; _[_]ᵗ; ⇑ᵗ; extᵗ; renameᵗ; singleSubᵗ)
open import TyStore using (TyStore; store-bind; Z∋)
open import Consistency using (_↪ᵗ_; wk↪ᵗ; _[_]ᶜ)
open import Conversion using (replaceTy; 〖_,_↑_〗)
open import CastTerms using
  ( Term
  ; Value
  ; ⟨_,_,_⟩
  ; Λ_
  ; _⦂∀_[_]
  ; _⟨_⟩
  ; _《_》
  ; _↑_
  ; _↓_
  ; fun
  ; all
  ; inj
  ; genᵥ
  ; renameᵗᵐ
  ; _⊢_⦂_
  )
open import Reduction
import Imprecision as I
import Primitives
open import proof.DGG.CastTermImprecision
open import proof.DGG.CastTermImprecisionTyping using (source-typing)
open import proof.DGG.ClosePairedTypeBinderDef using
  (ClosePairedTypeBinderᵀ)
open import proof.DGG.SimPairedAllValuesDef using
  (SimPairedAllValuesᵀ)
open import proof.DGG.SimSourceLambdaApplicationDef using
  (SimSourceLambdaApplicationᵀ)
open import proof.DGG.Inversion.UniversalImprecisionInversionLemma using
  (universal-imprecision-inversion)
open import proof.DGG.PairedValueFreshGeneratorPositionDef using
  (PairedValueFreshGeneratorPositionᵀ)
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.SourceRebase using
  (open-source-rebase-nonempty)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (evolution-keep; evolution-bind-both)
open import proof.DGG.WorldEvolutionSequence
open import proof.ImprecisionConsistency using
  (ext-injective; renameᵗ-injective; subst₂-⊑)
open import proof.Reduction
open import proof.Reduction.ValueIrreducibleProof using (value-no-step)
open import proof.TypeInTermSubst using (rename-openᵗ)
open import proof.TypeSafety.Preservation using
  (replace-zero-open; structural-reveal-typing)
open import proof.TypeSafety.Progress using (no-bot-value)


private
  targetUniversalLayers : ∀ {Δ} → Term Δ → Nat.ℕ
  targetUniversalLayers (CastTerms.` x) = Nat.zero
  targetUniversalLayers (CastTerms.ƛ M) = Nat.zero
  targetUniversalLayers (L CastTerms.· M) = Nat.zero
  targetUniversalLayers (Λ V) = Nat.zero
  targetUniversalLayers (M ⦂∀ C [ A ]) = Nat.zero
  targetUniversalLayers (CastTerms.$ κ) = Nat.zero
  targetUniversalLayers (L CastTerms.⊕[ op ] M) = Nat.zero
  targetUniversalLayers (M ⟨ c ⟩) = Nat.suc (targetUniversalLayers M)
  targetUniversalLayers (M ↑ c) = Nat.suc (targetUniversalLayers M)
  targetUniversalLayers (M ↓ c) = Nat.suc (targetUniversalLayers M)
  targetUniversalLayers CastTerms.blame = Nat.zero

  targetUniversalLayers-rename : ∀ {Δ Δ′}
      (ρ : Δ ↪ᵗ Δ′) (M : Term Δ)
    → targetUniversalLayers (renameᵗᵐ ρ M) ≡ targetUniversalLayers M
  targetUniversalLayers-rename ρ (CastTerms.` x) = refl
  targetUniversalLayers-rename ρ (CastTerms.ƛ M) = refl
  targetUniversalLayers-rename ρ (L CastTerms.· M) = refl
  targetUniversalLayers-rename ρ (Λ V) = refl
  targetUniversalLayers-rename ρ (M ⦂∀ C [ A ]) = refl
  targetUniversalLayers-rename ρ (CastTerms.$ κ) = refl
  targetUniversalLayers-rename ρ (L CastTerms.⊕[ op ] M) = refl
  targetUniversalLayers-rename ρ (M ⟨ c ⟩) =
    cong Nat.suc (targetUniversalLayers-rename ρ M)
  targetUniversalLayers-rename ρ (M ↑ c) =
    cong Nat.suc (targetUniversalLayers-rename ρ M)
  targetUniversalLayers-rename ρ (M ↓ c) =
    cong Nat.suc (targetUniversalLayers-rename ρ M)
  targetUniversalLayers-rename ρ CastTerms.blame = refl

  structural-open : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {C : Ty (Nat.suc (CastTerms.Δᵉ Γᴸ))}
      {C′ : Ty (Nat.suc (CastTerms.Δᵉ Γᴿ))}
      {A : Ty (CastTerms.Δᵉ Γᴸ)}
      {A′ : Ty (CastTerms.Δᵉ Γᴿ)}
    → I._⊢_⊑_ (I.extᵐ (marksᶜ γ))
        (renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) C)
        (renameᵗ (extᵗ (toRenameⁱ (ηᴿᶜ γ))) C′)
    → A ⊑ᵀ⟨ γ ⟩ A′
    → C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ
  structural-open {γ = γ} {C = C} {C′ = C′} {A = A} {A′ = A′}
      body argument =
    subst
      (λ L → I._⊢_⊑_ (marksᶜ γ) L
        (renameᵗ (toRenameⁱ (ηᴿᶜ γ)) (C′ [ A′ ]ᵗ)))
      (sym (rename-openᵗ (toRenameⁱ (ηᴸᶜ γ)) C A))
      (subst
        (λ R → I._⊢_⊑_ (marksᶜ γ)
          (renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) C
            [ renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A ]ᵗ) R)
        (sym (rename-openᵗ (toRenameⁱ (ηᴿᶜ γ)) C′ A′))
        (subst₂-⊑ same star body))
    where
    same : ∀ X → I._⊢_⊑_ (marksᶜ γ)
        (singleSubᵗ (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A) X)
        (singleSubᵗ (renameᵗ (toRenameⁱ (ηᴿᶜ γ)) A′) X)
    same zero = argument
    same (suc X) = I.X⊑X

    star : ∀ X → I.extᵐ (marksᶜ γ) X ≡ I.X⊑★
      → I._⊢_⊑_ (marksᶜ γ)
          (singleSubᵗ (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A) X) ★
    star zero ()
    star (suc X) marked = I.X⊑★ marked

  left-extended-rename-injective : ∀ {Γᴸ Γᴿ}
      {γ : Γᴸ ⊑ᶜ Γᴿ}
      {A B : Ty (Nat.suc (CastTerms.Δᵉ Γᴸ))}
    → renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) A
        ≡ renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) B
    → A ≡ B
  left-extended-rename-injective {γ = γ} =
    renameᵗ-injective
      (ext-injective (toRenameⁱ-injective (ηᴸᶜ γ)))

  left-universal-not-bottom : ∀ {Γᴸ Γᴿ}
      {γ : Γᴸ ⊑ᶜ Γᴿ}
      {V : Term (CastTerms.Δᵉ Γᴸ)}
      {V′ : Term (CastTerms.Δᵉ Γᴿ)}
      {C : Ty (Nat.suc (CastTerms.Δᵉ Γᴸ))}
      {C′ : Ty (Nat.suc (CastTerms.Δᵉ Γᴿ))}
      {p : `∀ C ⊑ᵀ⟨ γ ⟩ `∀ C′}
    → Value V
    → γ ⊢² V ⊑ V′ ∶ p
    → renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) C ≡ ＇ zero
    → Data.Empty.⊥
  left-universal-not-bottom {Γᴸ = Γᴸ} {γ = γ} {V = V}
      source-value related source-bot =
    no-bot-value source-value
      (subst (λ D → Γᴸ ⊢ V ⦂ `∀ D)
        (left-extended-rename-injective {γ = γ} source-bot)
        (source-typing related))


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (sim-source-lambda-application : SimSourceLambdaApplicationᵀ)
    (close-paired-type-binder : ClosePairedTypeBinderᵀ)
    (paired-value-fresh-generator-position :
      PairedValueFreshGeneratorPositionᵀ)
    (sim-target-reveal-rebase-closing :
      SimTargetRevealRebaseClosingᵀ)
  where

  worker : ∀ {Δᴸ Δᴿ Δᴸ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
      {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
      {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
      {p∀ : `∀ C ⊑ᵀ⟨ γ ⟩ `∀ C′}
    → openFramesᶜ γ ≡ []
    → (fuel : Nat.ℕ)
    → targetUniversalLayers V′ < fuel
    → γ ⊢² V ⊑ V′ ∶ p∀
    → (q : A ⊑ᵀ⟨ γ ⟩ A′)
    → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
    → Value V
    → Value V′
    → V ⦂∀ C [ A ] —→[ χᴸ ] N
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩
          applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
        (V′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (χᴸ ∷ []) χsᴿ
        × (γ′ ⊢² N ⊑ N′ ∶ s)

  worker no-rebase Nat.zero ()
  worker {Σᴿ = Σᴿ} {γ = γ} {A = A} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² {p = inner-universal}
        (Consistency.∀ᶜ c) (Consistency.∀ᶜ c′) related q₁)
      q r source-value (target-body-value 《 all 》)
      root@(pure-step (β-∀ value instantiated))
      with universal-imprecision-inversion inner-universal
  worker {Σᴿ = Σᴿ} {γ = γ} {A = A} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² {M = M} {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c) (Consistency.∀ᶜ c′) related q₁)
      q r source-value (target-body-value 《 all 》)
      (pure-step (β-∀ value instantiated))
    | inj₁ body rewrite instantiated =
      _ , Σᴿ , keep ∷ [] ,
      (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩ , γ , r ,
      (((M′ ⟨ Consistency.∀ᶜ c′ ⟩) ⦂∀ _ [ A′ ]
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩ ∎[])) ,
      evolutions-step-both refl refl evolution-keep evolutions-refl ,
      cast⊑cast² (c [ A ]ᶜ) (c′ [ A′ ]ᶜ)
        (•⊑•² inner-universal related q
          (structural-open {γ = γ} body q)) r
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² {p = inner-universal}
        (Consistency.∀ᶜ c) (Consistency.∀ᶜ c′) related q₁)
      q r source-value (target-body-value 《 all 》)
      (pure-step (β-∀ value instantiated))
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² {p = inner-universal}
        (Consistency.∀ᶜ c) (Consistency.∀ᶜ c′) related q₁)
      q r source-value (target-body-value 《 all 》)
      (pure-step (β-∀ value instantiated))
    | inj₂ (inj₂ (source-bot , target-star))
      = ⊥-elim (left-universal-not-bottom value related source-bot)
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² c c′ related q₁) q r source-value
      (target-body-value 《 genᵥ target-not-star target-safe 》)
      (pure-step (β-∀ value instantiated)) = {!!}
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(pure-step (β-∀ value instantiated))
      with universal-imprecision-inversion inner-universal
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(pure-step (β-∀ value instantiated))
    | inj₁ body
      with worker no-rebase fuel smaller related q
        (structural-open {γ = γ} body q)
        source-value target-body-value root
  worker {γ = γ} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c′) related q₁)
      q r source-value
      (target-body-value 《 all 》)
      root@(pure-step (β-∀ value instantiated))
    | inj₁ body
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel , result-steps , result-evolution , result-rel =
    let total-evolution =
          evolutions-step-right refl evolution-keep result-evolution
    in
      result-Δ , result-store , keep ∷ result-changes ,
      result ⟨ applyConsistencies result-changes (c′ [ A′ ]ᶜ) ⟩ ,
      result-world , multi-⊑ᵀ total-evolution r ,
      ((M′ ⟨ Consistency.∀ᶜ c′ ⟩) ⦂∀ C′ [ A′ ]
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩
        —↠[ result-changes ]⟨ cast-↠ (c′ [ A′ ]ᶜ) result-steps ⟩
       result ⟨ applyConsistencies result-changes
         (c′ [ A′ ]ᶜ) ⟩ ∎[]) ,
      total-evolution ,
      ⊑cast²
        (applyConsistencies result-changes (c′ [ A′ ]ᶜ))
        result-rel (multi-⊑ᵀ total-evolution r)
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(pure-step (β-∀ value instantiated))
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(pure-step (β-∀ value instantiated))
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim
        (left-universal-not-bottom source-value related source-bot)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² c′ related q₁) q r source-value
      (target-body-value 《 genᵥ not-star safe 》)
      (pure-step (β-∀ value instantiated)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-identity c′⊢ absent related q₁) q r
      source-value target-value
      (pure-step (β-∀ value instantiated)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-identity c′⊢ absent related q₁) q r
      source-value target-value
      (pure-step (β-∀ value instantiated)) = {!!}
  worker {γ = γ} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (cast⊑² {p = inner-universal}
        (Consistency.∀ᶜ c) related q₁)
      q r source-value target-value
      root@(pure-step (β-∀ value instantiated))
      with universal-imprecision-inversion inner-universal
  worker {γ = γ} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (cast⊑² {M = M} {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c) related q₁)
      q r source-value target-value
      (pure-step (β-∀ value instantiated))
    | inj₁ body rewrite instantiated =
      _ , _ , [] , M′ ⦂∀ C′ [ A′ ] , γ , r ,
      ((M′ ⦂∀ C′ [ A′ ]) ∎[]) ,
      evolutions-step-left refl evolution-keep evolutions-refl ,
      cast⊑² (c [ A ]ᶜ)
        (•⊑•² inner-universal related q
          (structural-open {γ = γ} body q)) r
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑² {p = inner-universal}
        (Consistency.∀ᶜ c) related q₁)
      q r source-value target-value
      (pure-step (β-∀ value instantiated))
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑² {p = inner-universal}
        (Consistency.∀ᶜ c) related q₁)
      q r source-value target-value
      (pure-step (β-∀ value instantiated))
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim (left-universal-not-bottom value related source-bot)
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value
      (pure-step (β-∀ value instantiated)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value
      (pure-step (β-∀ value instantiated)) =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  worker {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {γ = γ} {V = Λ V} {V′ = Λ V′}
      {C = C} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑Λ² source-value₁ target-value₁ related q₁) q r
      source-value target-value (β-Λ value) =
    _ , store-bind Σᴿ A′ , bind A′ ∷ [] ,
    V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 , bindBothᶜ γ q ,
    proj₁ result-package ,
    (((Λ V′) ⦂∀ C′ [ A′ ])
      —→[ bind A′ ]⟨ β-Λ target-value₁ ⟩
     (V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗) ∎[]) ,
    evolution ,
    proj₂ result-package
    where
    evolution : MultiWorldEvolution
        {W = γ} {W′ = bindBothᶜ γ q}
        (bind A ∷ []) (bind A′ ∷ [])
    evolution = evolutions-step-both refl refl
      (evolution-bind-both q refl refl) evolutions-refl

    result-related :
      replaceTy zero (⇑ᵗ A) C ⊑ᵀ⟨ bindBothᶜ γ q ⟩
      replaceTy zero (⇑ᵗ A′) C′
    result-related =
      subst
        (λ L → L ⊑ᵀ⟨ bindBothᶜ γ q ⟩
          replaceTy zero (⇑ᵗ A′) C′)
        (sym (replace-zero-open C A))
        (subst
          (λ R → ⇑ᵗ (C [ A ]ᵗ) ⊑ᵀ⟨ bindBothᶜ γ q ⟩ R)
          (sym (replace-zero-open C′ A′))
          (multi-⊑ᵀ evolution r))

    raw-result :
      bindBothᶜ γ q ⊢²
      V ↑ 〖 zero , ⇑ᵗ A ↑ C 〗 ⊑
      V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∶ result-related
    raw-result =
      reveal⊑reveal²
        (structural-reveal-typing C (Z∋ refl))
        (structural-reveal-typing C′ (Z∋ refl))
        (paired-value-fresh-generator-position
          source-value₁ target-value₁ related)
        refl (multi-⊑ᵀ evolution q)
        (close-paired-type-binder q related)
        result-related

    result-package :
      Σ[ s ∈ ⇑ᵗ (C [ A ]ᵗ) ⊑ᵀ⟨ bindBothᶜ γ q ⟩
        ⇑ᵗ (C′ [ A′ ]ᵗ) ]
      bindBothᶜ γ q ⊢²
        V ↑ 〖 zero , ⇑ᵗ A ↑ C 〗 ⊑
        V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∶ s
    result-package =
      subst
        (λ L →
          Σ[ s ∈ L ⊑ᵀ⟨ bindBothᶜ γ q ⟩ ⇑ᵗ (C′ [ A′ ]ᵗ) ]
          bindBothᶜ γ q ⊢²
            V ↑ 〖 zero , ⇑ᵗ A ↑ C 〗 ⊑
            V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∶ s)
        (replace-zero-open C A)
        (subst
          (λ R →
            Σ[ s ∈ replaceTy zero (⇑ᵗ A) C
              ⊑ᵀ⟨ bindBothᶜ γ q ⟩ R ]
            bindBothᶜ γ q ⊢²
              V ↑ 〖 zero , ⇑ᵗ A ↑ C 〗 ⊑
              V′ ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∶ s)
          (replace-zero-open C′ A′)
          (result-related , raw-result))
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (CastTerms.ƛ target-body) (β-Λ value)
  worker {Σᴿ = Σᴿ} {γ = γ} {V′ = Λ target-body}
      {C = C} {A = A}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢Λ target-typing-value target-body⊢) related q₁)
      q r source-value target-value@(CastTerms.Λ target-body-value)
      (β-Λ value)
      with sim-source-lambda-application no-rebase non-var occurs
        source-value₁ related q r target-value
        (β-Λ target-body-value)
  worker {Σᴿ = Σᴿ} {γ = γ} {V′ = Λ target-body}
      {C = C} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢Λ target-typing-value target-body⊢) related q₁)
      q r source-value target-value@(CastTerms.Λ target-body-value)
      (β-Λ value)
    | result-world , result-type-rel , result-evolution , result-rel =
      _ , store-bind Σᴿ A′ , bind A′ ∷ [] ,
      target-body ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 , result-world ,
      result-type-rel ,
      (((Λ target-body) ⦂∀ C′ [ A′ ])
        —→[ bind A′ ]⟨ β-Λ target-body-value ⟩
       target-body ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∎[]) ,
      result-evolution , result-rel
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (CastTerms.$ (Primitives.κℕ n)) (β-Λ value)
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (CastTerms.$ (Primitives.κ𝔹 b)) (β-Λ value)
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (target-body-value 《 fun 》) (β-Λ value)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ⟨ Consistency.∀ᶜ target-c ⟩}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢⟨⟩ {A = `∀ target-source-body} target-body⊢
          .(Consistency.∀ᶜ target-c)) related q₁)
      q r source-value target-value@(target-body-value 《 all 》)
      (β-Λ value)
      with sim-source-lambda-application no-rebase non-var occurs
        source-value₁ related q r target-value
        (pure-step (β-∀ target-body-value refl))
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ⟨ Consistency.∀ᶜ target-c ⟩}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢⟨⟩ {A = `∀ target-source-body} target-body⊢
          .(Consistency.∀ᶜ target-c)) related q₁)
      q r source-value target-value@(target-body-value 《 all 》)
      (β-Λ value)
    | result-world , result-type-rel , result-evolution , result-rel =
      _ , Σᴿ , keep ∷ [] ,
      (target-body ⦂∀ target-source-body [ A′ ])
        ⟨ target-c [ A′ ]ᶜ ⟩ ,
      result-world , result-type-rel ,
      (((target-body ⟨ Consistency.∀ᶜ target-c ⟩) ⦂∀ C′ [ A′ ])
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (target-body ⦂∀ target-source-body [ A′ ])
         ⟨ target-c [ A′ ]ᶜ ⟩ ∎[]) ,
      result-evolution , result-rel
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (target-body-value 《 inj 》) (β-Λ value)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ⟨
        (Consistency.gen target-c) target-not-star ⟩}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢⟨⟩ target-body⊢
          .((Consistency.gen target-c) target-not-star)) related q₁)
      q r source-value
      target-value@(target-body-value 《
        genᵥ .target-not-star target-safe 》)
      (β-Λ value)
      with sim-source-lambda-application no-rebase non-var occurs
        source-value₁ related q r target-value
        (β-gen target-body-value target-not-star target-safe)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ⟨
        (Consistency.gen target-c) target-not-star ⟩}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢⟨⟩ target-body⊢
          .((Consistency.gen target-c) target-not-star)) related q₁)
      q r source-value
      target-value@(target-body-value 《
        genᵥ .target-not-star target-safe 》)
      (β-Λ value)
    | result-world , result-type-rel , result-evolution , result-rel =
      _ , store-bind Σᴿ A′ , bind A′ ∷ [] ,
      CastTerms.⇑ᵗᵐ target-body ⟨ target-c ⟩
        ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ,
      result-world , result-type-rel ,
      (((target-body ⟨
          (Consistency.gen target-c) target-not-star ⟩)
          ⦂∀ C′ [ A′ ])
        —→[ bind A′ ]⟨
          β-gen target-body-value target-not-star target-safe ⟩
       CastTerms.⇑ᵗᵐ target-body ⟨ target-c ⟩
         ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∎[]) ,
      result-evolution , result-rel
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (target-body-value ↑ fun) (β-Λ value)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ↑ Conversion.`∀↑ target-c}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢reveal
          (Conversion.⊢↑-∀ {A = target-inner-body}
            target-representation target-inner-conversion⊢)
          target-body⊢) related q₁)
      q r source-value target-value@(target-body-value ↑ all)
      (β-Λ value)
      with sim-source-lambda-application no-rebase non-var occurs
        source-value₁ related q r target-value
        (β-reveal-∀ target-body-value)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ↑ Conversion.`∀↑ target-c}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢reveal
          (Conversion.⊢↑-∀ {A = target-inner-body}
            target-representation target-inner-conversion⊢)
          target-body⊢) related q₁)
      q r source-value target-value@(target-body-value ↑ all)
      (β-Λ value)
    | result-world , result-type-rel , result-evolution , result-rel =
      _ , store-bind Σᴿ A′ , bind A′ ∷ [] ,
      ((CastTerms.⇑ᵗᵐ target-body
          ⦂∀ applyBody (bind A′) target-inner-body [ ＇ zero ])
        ↑ target-c) ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ,
      result-world , result-type-rel ,
      (((target-body ↑ Conversion.`∀↑ target-c) ⦂∀ C′ [ A′ ])
        —→[ bind A′ ]⟨ β-reveal-∀ target-body-value ⟩
       ((CastTerms.⇑ᵗᵐ target-body
           ⦂∀ applyBody (bind A′) target-inner-body [ ＇ zero ])
         ↑ target-c) ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∎[]) ,
      result-evolution , result-rel
  worker no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁ () related q₁)
      q r source-value (target-body-value ↓ fun) (β-Λ value)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ↓ Conversion.`∀↓ target-c}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢conceal
          (Conversion.⊢↓-∀ {A = target-inner-body}
            target-representation target-inner-conversion⊢)
          target-body⊢) related q₁)
      q r source-value target-value@(target-body-value ↓ all)
      (β-Λ value)
      with sim-source-lambda-application no-rebase non-var occurs
        source-value₁ related q r target-value
        (β-conceal-∀ target-body-value)
  worker {Σᴿ = Σᴿ}
      {V′ = target-body ↓ Conversion.`∀↓ target-c}
      {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (Λ⊑² non-var occurs source-value₁
        (CastTerms.⊢conceal
          (Conversion.⊢↓-∀ {A = target-inner-body}
            target-representation target-inner-conversion⊢)
          target-body⊢) related q₁)
      q r source-value target-value@(target-body-value ↓ all)
      (β-Λ value)
    | result-world , result-type-rel , result-evolution , result-rel =
      _ , store-bind Σᴿ A′ , bind A′ ∷ [] ,
      (CastTerms.⇑ᵗᵐ target-body
        ⦂∀ applyBody (bind A′) target-inner-body [ ＇ zero ]
        ↓ target-c) ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ,
      result-world , result-type-rel ,
      (((target-body ↓ Conversion.`∀↓ target-c) ⦂∀ C′ [ A′ ])
        —→[ bind A′ ]⟨ β-conceal-∀ target-body-value ⟩
       (CastTerms.⇑ᵗᵐ target-body
         ⦂∀ applyBody (bind A′) target-inner-body [ ＇ zero ]
         ↓ target-c) ↑ 〖 zero , ⇑ᵗ A′ ↑ C′ 〗 ∎[]) ,
      result-evolution , result-rel
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》) root@(β-Λ value)
      with universal-imprecision-inversion inner-universal
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》) root@(β-Λ value)
    | inj₁ body
      with worker no-rebase fuel smaller related q
        (structural-open {γ = γ} body q)
        source-value target-body-value root
  worker {γ = γ} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c′) related q₁)
      q r source-value
      (target-body-value 《 all 》) root@(β-Λ value)
    | inj₁ body
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel , result-steps , result-evolution , result-rel =
    let total-evolution =
          evolutions-step-right refl evolution-keep result-evolution
    in
      result-Δ , result-store , keep ∷ result-changes ,
      result ⟨ applyConsistencies result-changes (c′ [ A′ ]ᶜ) ⟩ ,
      result-world , multi-⊑ᵀ total-evolution r ,
      ((M′ ⟨ Consistency.∀ᶜ c′ ⟩) ⦂∀ C′ [ A′ ]
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩
        —↠[ result-changes ]⟨ cast-↠ (c′ [ A′ ]ᶜ) result-steps ⟩
       result ⟨ applyConsistencies result-changes
         (c′ [ A′ ]ᶜ) ⟩ ∎[]) ,
      total-evolution ,
      ⊑cast²
        (applyConsistencies result-changes (c′ [ A′ ]ᶜ))
        result-rel (multi-⊑ᵀ total-evolution r)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》) root@(β-Λ value)
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》) root@(β-Λ value)
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim
        (left-universal-not-bottom source-value related source-bot)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² c′ related q₁) q r source-value
      (target-body-value 《 genᵥ target-not-star target-safe 》)
      (β-Λ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-Λ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-Λ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-Λ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-Λ value) =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² c c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      (β-gen value not-star safe) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² c c′ related q₁) q r source-value
      (target-body-value 《 genᵥ target-not-star target-safe 》)
      (β-gen value not-star safe) = {!!}
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-gen value not-star safe)
      with universal-imprecision-inversion inner-universal
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-gen value not-star safe)
    | inj₁ body
      with worker no-rebase fuel smaller related q
        (structural-open {γ = γ} body q)
        source-value target-body-value root
  worker {γ = γ} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c′) related q₁)
      q r source-value
      (target-body-value 《 all 》)
      root@(β-gen value not-star safe)
    | inj₁ body
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel , result-steps , result-evolution , result-rel =
    let total-evolution =
          evolutions-step-right refl evolution-keep result-evolution
    in
      result-Δ , result-store , keep ∷ result-changes ,
      result ⟨ applyConsistencies result-changes (c′ [ A′ ]ᶜ) ⟩ ,
      result-world , multi-⊑ᵀ total-evolution r ,
      ((M′ ⟨ Consistency.∀ᶜ c′ ⟩) ⦂∀ C′ [ A′ ]
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩
        —↠[ result-changes ]⟨ cast-↠ (c′ [ A′ ]ᶜ) result-steps ⟩
       result ⟨ applyConsistencies result-changes
         (c′ [ A′ ]ᶜ) ⟩ ∎[]) ,
      total-evolution ,
      ⊑cast²
        (applyConsistencies result-changes (c′ [ A′ ]ᶜ))
        result-rel (multi-⊑ᵀ total-evolution r)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-gen value not-star safe)
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-gen value not-star safe)
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim
        (left-universal-not-bottom source-value related source-bot)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² c′ related q₁) q r source-value
      (target-body-value 《 genᵥ target-not-star target-safe 》)
      (β-gen value not-star safe) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-gen value not-star safe) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-gen value not-star safe) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (cast⊑² c related q₁) q r source-value target-value
      (β-gen value not-star safe) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-gen value not-star safe) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-gen value not-star safe) =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-reveal-∀ value)
      with universal-imprecision-inversion inner-universal
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-reveal-∀ value)
    | inj₁ body
      with worker no-rebase fuel smaller related q
        (structural-open {γ = γ} body q)
        source-value target-body-value root
  worker {γ = γ} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c′) related q₁)
      q r source-value
      (target-body-value 《 all 》)
      root@(β-reveal-∀ value)
    | inj₁ body
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel , result-steps , result-evolution , result-rel =
    let total-evolution =
          evolutions-step-right refl evolution-keep result-evolution
    in
      result-Δ , result-store , keep ∷ result-changes ,
      result ⟨ applyConsistencies result-changes (c′ [ A′ ]ᶜ) ⟩ ,
      result-world , multi-⊑ᵀ total-evolution r ,
      ((M′ ⟨ Consistency.∀ᶜ c′ ⟩) ⦂∀ C′ [ A′ ]
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩
        —↠[ result-changes ]⟨ cast-↠ (c′ [ A′ ]ᶜ) result-steps ⟩
       result ⟨ applyConsistencies result-changes
         (c′ [ A′ ]ᶜ) ⟩ ∎[]) ,
      total-evolution ,
      ⊑cast²
        (applyConsistencies result-changes (c′ [ A′ ]ᶜ))
        result-rel (multi-⊑ᵀ total-evolution r)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-reveal-∀ value)
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-reveal-∀ value)
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim
        (left-universal-not-bottom source-value related source-bot)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² c′ related q₁) q r source-value
      (target-body-value 《 genᵥ target-not-star target-safe 》)
      (β-reveal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-reveal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-reveal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (reveal⊑-identity c⊢ absent related q₁) q r
      source-value target-value (β-reveal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (reveal⊑-only² c⊢ present marked unoccupied represented
        related q₁)
      q r source-value target-value (β-reveal-∀ value) = {!!}
  worker {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {γ = γ}
      {C = C} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (reveal⊑reveal²
        (Conversion.⊢↑-∀ source-representation source-conversion⊢)
        (Conversion.⊢↑-∀ target-representation target-conversion⊢)
        same-position same-pivot represented {p = inner-universal} related q₁)
      q r source-value (target-value ↑ all) (β-reveal-∀ value)
      with universal-imprecision-inversion inner-universal
  worker {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {γ = γ}
      {C = C} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (reveal⊑reveal² {M = M} {M′ = M′}
        (Conversion.⊢↑-∀ source-representation source-conversion⊢)
        (Conversion.⊢↑-∀ target-representation target-conversion⊢)
        same-position same-pivot represented {p = inner-universal} related q₁)
      q r source-value (target-value ↑ all) (β-reveal-∀ value)
    | inj₁ body = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (reveal⊑reveal²
        (Conversion.⊢↑-∀ source-representation source-conversion⊢)
        (Conversion.⊢↑-∀ target-representation target-conversion⊢)
        same-position same-pivot represented {p = inner-universal} related q₁)
      q r source-value (target-value ↑ all) (β-reveal-∀ value)
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (reveal⊑reveal²
        (Conversion.⊢↑-∀ source-representation source-conversion⊢)
        (Conversion.⊢↑-∀ target-representation target-conversion⊢)
        same-position same-pivot represented {p = inner-universal} related q₁)
      q r source-value (target-value ↑ all) (β-reveal-∀ value)
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim (left-universal-not-bottom value related source-bot)
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-reveal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-reveal-∀ value) =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-conceal-∀ value)
      with universal-imprecision-inversion inner-universal
  worker {γ = γ} no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-conceal-∀ value)
    | inj₁ body
      with worker no-rebase fuel smaller related q
        (structural-open {γ = γ} body q)
        source-value target-body-value root
  worker {γ = γ} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {M′ = M′} {p = inner-universal}
        (Consistency.∀ᶜ c′) related q₁)
      q r source-value
      (target-body-value 《 all 》)
      root@(β-conceal-∀ value)
    | inj₁ body
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel , result-steps , result-evolution , result-rel =
    let total-evolution =
          evolutions-step-right refl evolution-keep result-evolution
    in
      result-Δ , result-store , keep ∷ result-changes ,
      result ⟨ applyConsistencies result-changes (c′ [ A′ ]ᶜ) ⟩ ,
      result-world , multi-⊑ᵀ total-evolution r ,
      ((M′ ⟨ Consistency.∀ᶜ c′ ⟩) ⦂∀ C′ [ A′ ]
        —→[ keep ]⟨ pure-step (β-∀ target-body-value refl) ⟩
       (M′ ⦂∀ _ [ A′ ]) ⟨ c′ [ A′ ]ᶜ ⟩
        —↠[ result-changes ]⟨ cast-↠ (c′ [ A′ ]ᶜ) result-steps ⟩
       result ⟨ applyConsistencies result-changes
         (c′ [ A′ ]ᶜ) ⟩ ∎[]) ,
      total-evolution ,
      ⊑cast²
        (applyConsistencies result-changes (c′ [ A′ ]ᶜ))
        result-rel (multi-⊑ᵀ total-evolution r)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-conceal-∀ value)
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² {p = inner-universal} c′ related q₁) q r source-value
      (target-body-value 《 all 》)
      root@(β-conceal-∀ value)
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim
        (left-universal-not-bottom source-value related source-bot)
  worker no-rebase (Nat.suc fuel) (s≤s smaller)
      (⊑cast² c′ related q₁) q r source-value
      (target-body-value 《 genᵥ target-not-star target-safe 》)
      (β-conceal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-conceal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-identity c′⊢ absent related q₁) q r
      source-value target-value (β-conceal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (conceal⊑-identity c⊢ absent related q₁) q r
      source-value target-value (β-conceal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (conceal⊑-only² c⊢ present marked unoccupied represented
        related q₁)
      q r source-value target-value (β-conceal-∀ value) = {!!}
  worker {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {γ = γ}
      {C = C} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (conceal⊑conceal² {p = inner-universal}
        (Conversion.⊢↓-∀ source-representation source-conversion⊢)
        (Conversion.⊢↓-∀ target-representation target-conversion⊢)
        same-position same-pivot represented related q₁)
      q r source-value (target-value ↓ all) (β-conceal-∀ value)
      with universal-imprecision-inversion inner-universal
  worker {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {γ = γ}
      {C = C} {A = A} {C′ = C′} {A′ = A′}
      no-rebase (Nat.suc fuel) size-bound
      (conceal⊑conceal² {M = M} {M′ = M′}
        {p = inner-universal}
        (Conversion.⊢↓-∀ source-representation source-conversion⊢)
        (Conversion.⊢↓-∀ target-representation target-conversion⊢)
        same-position same-pivot represented related q₁)
      q r source-value (target-value ↓ all) (β-conceal-∀ value)
    | inj₁ body = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (conceal⊑conceal² {p = inner-universal}
        (Conversion.⊢↓-∀ source-representation source-conversion⊢)
        (Conversion.⊢↓-∀ target-representation target-conversion⊢)
        same-position same-pivot represented related q₁)
      q r source-value (target-value ↓ all) (β-conceal-∀ value)
    | inj₂ (inj₁ (non-var , occurs , body)) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (conceal⊑conceal² {p = inner-universal}
        (Conversion.⊢↓-∀ source-representation source-conversion⊢)
        (Conversion.⊢↓-∀ target-representation target-conversion⊢)
        same-position same-pivot represented related q₁)
      q r source-value (target-value ↓ all) (β-conceal-∀ value)
    | inj₂ (inj₂ (source-bot , target-star)) =
      ⊥-elim (left-universal-not-bottom value related source-bot)
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-conceal-∀ value) = {!!}
  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-rebase² c′⊢ rebase related q₁) q r
      source-value target-value (β-conceal-∀ value) =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  worker no-rebase (Nat.suc fuel) size-bound related q r
      () target-value (pure-step blame-•)

  worker no-rebase (Nat.suc fuel) size-bound related q r
      source-value target-value (ξ-• source-step refl refl) =
    ⊥-elim (value-no-step source-value source-step)

  sim-paired-all-values : SimPairedAllValuesᵀ
  sim-paired-all-values {V′ = V′} no-rebase related q r
      source-value target-value source-step =
    worker no-rebase
      (Nat.suc (targetUniversalLayers V′))
      (n<1+n (targetUniversalLayers V′))
      related q r source-value target-value source-step

{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareLemma where

-- File Charter:
--   * Proves the general GenSafe target ground-cast square.
--   * The proof simultaneously follows injection and projection geometry,
--     using castSize only to justify recursive calls through symmetry.
--   * Exports the closed implementation of
--     MorePreciseGenSafeTargetGroundCastSquareᵀ.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (Acc; acc)
import Data.Nat.Induction as NatInduction
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym; trans)

open import Types
import Imprecision as I
open import Consistency using
  ( Env∼; _⊢_∼_; _↦_; ∀ᶜ_; inst_; gen_; bot-elim; bot-intro
  ; extᵐ; genᵐ
  )
import Consistency as C
open import CastTerms using
  (GenSafe; safe-⇒; safe-∀; safe-inst; safe-gen)
open import proof.Consistency using
  ( castSize; castSize-sym∼; castSize-transport-env∼
  ; ext-safe; gen-safe
  )
open import proof.ImprecisionConsistency using
  ( shift-ground; rename-⊑; unshift-⊑; fin-suc-injective
  ; source-occurs-target; target-occurs-source
  ; imp-env-weaken; ext-to-inst-star-map
  ; consistency-source-occurs-target; consistency-target-occurs-source
  ; nonvar-occurs-nonstar; source-nonvar-from-target
  )
open import proof.Imprecision using (imprecision-to-fresh)
open import proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareDef
  using (MorePreciseGenSafeTargetGroundCastSquareᵀ)
private
  absent-occurs⊥ : ∀ {Δ : TyCtx} {X : TyVar Δ} {A : Ty Δ}
    → X ∉ᵗ A
    → X ∈ᵗ A
    → ⊥
  absent-occurs⊥ (∉-var X≠Y) var-∈ = ≢ᶠ→≢ X≠Y refl
  absent-occurs⊥ ∉-base ()
  absent-occurs⊥ ∉-star ()
  absent-occurs⊥ (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
    absent-occurs⊥ X∉A X∈A
  absent-occurs⊥ (∉-fun X∉A X∉B)
      (∈-fun-right X∉A′ X∈B) =
    absent-occurs⊥ X∉B X∈B
  absent-occurs⊥ (∉-all X∉A) (∈-all X∈A) =
    absent-occurs⊥ X∉A X∈A

  consistency-source-absent : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → ν X ≡ C.X∼X
    → ν ⊢ A ∼ B
    → X ∉ᵗ B
    → X ∉ᵗ A
  consistency-source-absent same c X∉B with occurs? _ _
  consistency-source-absent same c X∉B | present X∈A =
    ⊥-elim (absent-occurs⊥ X∉B
      (consistency-source-occurs-target same c X∈A))
  consistency-source-absent same c X∉B | absent X∉A = X∉A

  consistency-target-absent : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → ν X ≡ C.X∼X
    → ν ⊢ A ∼ B
    → X ∉ᵗ A
    → X ∉ᵗ B
  consistency-target-absent same c X∉A with occurs? _ _
  consistency-target-absent same c X∉A | present X∈B =
    ⊥-elim (absent-occurs⊥ X∉A
      (consistency-target-occurs-source same c X∈B))
  consistency-target-absent same c X∉A | absent X∉B = X∉B

  imprecision-source-absent : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → μ X ≡ I.X⊑X
    → μ I.⊢ A ⊑ B
    → X ∉ᵗ B
    → X ∉ᵗ A
  imprecision-source-absent same p X∉B with occurs? _ _
  imprecision-source-absent same p X∉B | present X∈A =
    ⊥-elim (absent-occurs⊥ X∉B
      (source-occurs-target same p X∈A))
  imprecision-source-absent same p X∉B | absent X∉A = X∉A

  imprecision-target-absent : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → μ X ≡ I.X⊑X
    → μ I.⊢ A ⊑ B
    → X ∉ᵗ A
    → X ∉ᵗ B
  imprecision-target-absent same p X∉A with occurs? _ _
  imprecision-target-absent same p X∉A | present X∈B =
    ⊥-elim (absent-occurs⊥ X∉A
      (target-occurs-source p X∈B))
  imprecision-target-absent same p X∉A | absent X∉B = X∉B

  consistency-no-to-distinct-variable : ∀ {Δ : TyCtx}
      {ν : Env∼ Δ} {A : Ty Δ} {X Y : TyVar Δ}
    → ν Y ≡ C.X∼★
    → ν X ≡ C.X∼X
    → ν ⊢ A ∼ ＇ X
    → Y ∈ᵗ A
    → ⊥
  consistency-no-to-distinct-variable Y★ XX
      (C.id (＇ X)) var-∈ with trans (sym Y★) XX
  consistency-no-to-distinct-variable Y★ XX
      (C.id (＇ X)) var-∈ | ()
  consistency-no-to-distinct-variable Y★ XX
      (C.？_ ⦃ g ⦄ c ⦃ Bns ⦄) ()
  consistency-no-to-distinct-variable Y★ XX
      (inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★) (∈-all Y∈A) =
    consistency-no-to-distinct-variable Y★ XX c Y∈A

  consistency-to-fresh : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {A : Ty (suc Δ)}
    → C.extᵐ ν ⊢ A ∼ ＇ Fin.zero
    → A ≡ ＇ Fin.zero
  consistency-to-fresh (C.id (＇ Fin.zero)) = refl
  consistency-to-fresh
      (C.？_ ⦃ Gᵍ = ★⇒★ ⦄ ())
  consistency-to-fresh
      (C.？_ ⦃ Gᵍ = ‵ ι ⦄ ())
  consistency-to-fresh
      (C.？_ ⦃ Gᵍ = ＇ Fin.zero ⦄
        ⦃ ★∼G = C.★∼Xᵍ () ⦄ c)
  consistency-to-fresh
      (C.？_ ⦃ Gᵍ = ＇ Fin.suc X ⦄ ())
  consistency-to-fresh
      (C.？_ ⦃ Gᵍ = ∀★ ⦄
        (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≢★))
  consistency-to-fresh
      (inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★) =
    ⊥-elim
      (consistency-no-to-distinct-variable refl refl c zero∈A)

  consistency-from-fresh : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {A : Ty (suc Δ)}
    → C.extᵐ ν ⊢ ＇ Fin.zero ∼ A
    → A ≡ ＇ Fin.zero
  consistency-from-fresh c =
    consistency-to-fresh
      (C.transport-env∼ C.flip-extᵐ (C.sym∼ c))

  imprecision-from-fresh : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ}
      {B : Ty (suc Δ)}
    → I.extᵐ μ I.⊢ ＇ Fin.zero ⊑ B
    → B ≡ ＇ Fin.zero
  imprecision-from-fresh I.X⊑X = refl
  imprecision-from-fresh (I.X⊑★ ())

  bottom-ground-shape : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {G : Ty Δ}
    → Ground G
    → ν ⊢ `∀ (＇ Fin.zero) ∼ G
    → G ≡ `∀ ★
  bottom-ground-shape ∀★ (∀ᶜ c) =
    ⊥-elim (absent-occurs⊥
      (consistency-source-absent refl c ∉-star) var-∈)
  bottom-ground-shape Gᵍ
      (inst_ ⦃ () ⦄ ⦃ zero∈A ⦄ c G≢★)
  bottom-ground-shape ∀★
      (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★)
  bottom-ground-shape ∀★ bot-elim = refl

  ground-bottom-shape : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {G : Ty Δ}
    → Ground G
    → ν ⊢ G ∼ `∀ (＇ Fin.zero)
    → G ≡ `∀ ★
  ground-bottom-shape ∀★ (∀ᶜ c) =
    ⊥-elim (absent-occurs⊥
      (consistency-target-absent refl c ∉-star) var-∈)
  ground-bottom-shape ∀★
      (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≢★)
  ground-bottom-shape Gᵍ
      (gen_ ⦃ () ⦄ ⦃ zero∈B ⦄ c G≢★)
  ground-bottom-shape ∀★ bot-intro = refl

  sym-gen-safe : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {A B : Ty Δ}
      {c : ν ⊢ A ∼ B}
    → GenSafe c
    → GenSafe (C.sym∼ c)
  sym-gen-safe safe-⇒ = safe-⇒
  sym-gen-safe safe-∀ = safe-∀
  sym-gen-safe (safe-inst {c = c} ⦃ Anv ⦄ ⦃ zero∈A ⦄ B≢★) =
    safe-gen B≢★
      (gen-safe (C.transport-env∼ C.flip-instᵐ (C.sym∼ c))
        B≢★ Anv zero∈A)
  sym-gen-safe (safe-gen A≢★ safe) = safe-inst A≢★

  transformed-child-size : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {A B : Ty (suc Δ)} (c : C.instᵐ ν ⊢ A ∼ B)
    → castSize (C.transport-env∼ C.flip-instᵐ (C.sym∼ c))
        ≡ castSize c
  transformed-child-size c =
    trans (castSize-transport-env∼ C.flip-instᵐ (C.sym∼ c))
      (castSize-sym∼ c)

  universal-ground-without-zero : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {A : Ty (suc Δ)} {G : Ty Δ}
    → Ground G
    → ν ⊢ `∀ A ∼ G
    → Fin.zero ∉ᵗ A
    → G ≡ `∀ ★
  universal-ground-without-zero ∀★ (∀ᶜ c) zero∉A = refl
  universal-ground-without-zero Gᵍ
      (inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c G≢★) zero∉A =
    ⊥-elim (absent-occurs⊥ zero∉A zero∈A)
  universal-ground-without-zero ∀★
      (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★) zero∉A
  universal-ground-without-zero ∀★ bot-elim zero∉A =
    ⊥-elim (absent-occurs⊥ zero∉A var-∈)

  ground-universal-without-zero : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {G : Ty Δ} {A : Ty (suc Δ)}
    → Ground G
    → ν ⊢ G ∼ `∀ A
    → Fin.zero ∉ᵗ A
    → G ≡ `∀ ★
  ground-universal-without-zero ∀★ (∀ᶜ c) zero∉A = refl
  ground-universal-without-zero ∀★
      (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≢★) zero∉A
  ground-universal-without-zero Gᵍ
      (gen_ ⦃ Bnv ⦄ ⦃ zero∈A ⦄ c G≢★) zero∉A =
    ⊥-elim (absent-occurs⊥ zero∉A zero∈A)
  ground-universal-without-zero ∀★ bot-intro zero∉A =
    ⊥-elim (absent-occurs⊥ zero∉A var-∈)

  mutual
    paired-ground-injection-core : ∀ {Δ : TyCtx}
        {μ : I.ImpEnv Δ} {νᴸ νᴿ : Env∼ Δ}
        {C A B G : Ty Δ}
      → (cᴸ : νᴸ ⊢ C ∼ A)
      → GenSafe cᴸ
      → Ground G
      → NonStar B
      → νᴿ ⊢ B ∼ G
      → μ I.⊢ C ⊑ B
      → μ I.⊢ A ⊑ ★
      → Acc _<_ (castSize cᴸ)
      → μ I.⊢ A ⊑ G
    paired-ground-injection-core (cᴸ ↦ dᴸ) safe-⇒ ★⇒★ Bns
        (cᴿ ↦ dᴿ) (I.⇒⊑⇒ pC pD) (I.⇒⊑★ qA qA′) access =
      I.⇒⊑⇒ qA qA′
    paired-ground-injection-core (cᴸ ↦ dᴸ) safe-⇒ ∀★ Bns
        (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ cᴿ B≠★)
        (I.⇒⊑⇒ pC pD) (I.⇒⊑★ qA qA′) access

    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑ Cnv zero∈C pC) (I.∀⊑ Anv zero∈A qA)
        (acc smaller) =
      I.∀⊑ Anv zero∈A
        (paired-ground-injection-core cᴸ (ext-safe cᴸ Anv zero∈A)
          (shift-ground Gᵍ) (C.renameNonStar Fin.suc Bns)
          (C.renameEnvᶜ {ν = C.extᵐ _} Fin.suc (λ X → refl) cᴿ)
          pC qA (smaller (n<1+n (castSize cᴸ))))
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) (I.∀⊑ Anv zero∈A qA) access
        with consistency-target-occurs-source refl cᴸ zero∈A
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) (I.∀⊑ Anv zero∈A qA) access
        | zero∈C with source-occurs-target refl pC zero∈C
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) (I.∀⊑ Anv zero∈A qA) access
        | zero∈C | zero∈D
        with consistency-source-occurs-target refl cᴿ zero∈D
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) (I.∀⊑ Anv zero∈A qA) access
        | zero∈C | zero∈D | ()
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns
        (inst_ ⦃ Dnv ⦄ ⦃ zero∈D ⦄ cᴿ G≢★)
        (I.∀⊑∀ pC) (I.∀⊑ Anv zero∈A qA) (acc smaller) =
      I.∀⊑ Anv zero∈A
        (paired-ground-injection-core cᴸ (ext-safe cᴸ Anv zero∈A)
          (shift-ground Gᵍ) (nonvar-occurs-nonstar Dnv zero∈D) cᴿ
          (imp-env-weaken ext-to-inst-star-map pC) qA
          (smaller (n<1+n (castSize cᴸ))))
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns
        bot-elim (I.∀⊑∀ pC) (I.∀⊑ Anv zero∈A qA) access =
      ⊥-elim
        (C.var-to-nonstar-nonvar-impossible
          (C.subst-left-∼ (imprecision-to-fresh pC) cᴸ)
          Anv (nonvar-occurs-nonstar Anv zero∈A))
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.bot-elim (I.∀⊑ Anv zero∈A qA) access =
      ⊥-elim
        (C.var-to-nonstar-nonvar-impossible cᴸ Anv
          (nonvar-occurs-nonstar Anv zero∈A))
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑∀ pC) I.∀★⊑★ access =
      subst (λ H → _ I.⊢ `∀ ★ ⊑ H) (sym G≡∀★)
        (I.∀⊑∀ I.★⊑★)
      where
      C∉zero = consistency-source-absent refl cᴸ ∉-star
      D∉zero = imprecision-target-absent refl pC C∉zero
      G≡∀★ = universal-ground-without-zero Gᵍ cᴿ D∉zero
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑ Cnv zero∈C pC) I.∀★⊑★ access =
      ⊥-elim (absent-occurs⊥
        (consistency-source-absent refl cᴸ ∉-star) zero∈C)
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.∀★⊑★ I.∀★⊑★ access
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        (I.∀⊑★ Cns pC) I.∀★⊑★ access
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.bot-elim I.∀★⊑★ access =
      ⊥-elim (absent-occurs⊥
        (consistency-source-absent refl cᴸ ∉-star) var-∈)
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.bot⊑★ I.∀★⊑★ access
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑∀ pC) (I.∀⊑★ Ans qA) access =
      subst (λ H → _ I.⊢ `∀ _ ⊑ H) (sym G≡∀★)
        (I.∀⊑∀ qA)
      where
      A∉zero = imprecision-source-absent refl qA ∉-star
      C∉zero = consistency-source-absent refl cᴸ A∉zero
      D∉zero = imprecision-target-absent refl pC C∉zero
      G≡∀★ = universal-ground-without-zero Gᵍ cᴿ D∉zero
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑ Cnv zero∈C pC) (I.∀⊑★ Ans qA) access =
      ⊥-elim (absent-occurs⊥ C∉zero zero∈C)
      where
      A∉zero = imprecision-source-absent refl qA ∉-star
      C∉zero = consistency-source-absent refl cᴸ A∉zero
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.∀★⊑★ (I.∀⊑★ Ans qA) access
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        (I.∀⊑★ Cns pC) (I.∀⊑★ Ans qA) access
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.bot-elim (I.∀⊑★ Ans qA) access =
      ⊥-elim (absent-occurs⊥ C∉zero var-∈)
      where
      A∉zero = imprecision-source-absent refl qA ∉-star
      C∉zero = consistency-source-absent refl cᴸ A∉zero
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.bot⊑★ (I.∀⊑★ Ans qA) access
    paired-ground-injection-core {μ = μ} {νᴿ = νᴿ}
        (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ (I.∀⊑∀ pC)
        I.bot⊑★ access =
      subst (λ H → μ I.⊢ `∀ (＇ Fin.zero) ⊑ H) (sym G≡∀★)
        I.bot-elim
      where
      C≡zero = consistency-to-fresh cᴸ
      pC′ : I.extᵐ μ I.⊢ ＇ Fin.zero ⊑ _
      pC′ = subst (λ C → I.extᵐ μ I.⊢ C ⊑ _) C≡zero pC
      D≡zero = imprecision-from-fresh pC′
      cᴿ′ : νᴿ ⊢ `∀ (＇ Fin.zero) ∼ _
      cᴿ′ = subst (λ D → νᴿ ⊢ `∀ D ∼ _) D≡zero cᴿ
      G≡∀★ = bottom-ground-shape Gᵍ cᴿ′
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑ Cnv zero∈C pC) I.bot⊑★ access =
      ⊥-elim
        (C.nonstar-nonvar-to-var-impossible cᴸ Cnv
          (nonvar-occurs-nonstar Cnv zero∈C))
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.∀★⊑★ I.bot⊑★ access
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        (I.∀⊑★ Cns pC) I.bot⊑★ access
    paired-ground-injection-core {μ = μ} (∀ᶜ cᴸ) safe-∀ Gᵍ Bns
        cᴿ I.bot-elim I.bot⊑★ access =
      subst (λ H → μ I.⊢ `∀ (＇ Fin.zero) ⊑ H) (sym G≡∀★)
        I.bot-elim
      where
      G≡∀★ = universal-ground-without-zero Gᵍ cᴿ ∉-star
    paired-ground-injection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.bot⊑★ I.bot⊑★ access

    paired-ground-injection-core {μ = μ} {νᴿ = νᴿ}
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) Gᵍ Bns cᴿ
        (I.∀⊑ Cnv′ zero∈C′ pC) qA (acc smaller) =
      unshift-⊑
        (paired-ground-projection-core cᴸˢ
          (gen-safe cᴸˢ A≢★ Cnv zero∈C)
          (shift-ground Gᵍ) (C.renameNonStar Fin.suc Bns)
          (C.renameEnvᶜ {ν = C.extᵐ (C.flipᵐ νᴿ)}
            Fin.suc (λ X → refl) (C.sym∼ cᴿ))
          (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) qA) pC
          (smaller child<outer))
      where
      cᴸˢ = C.transport-env∼ C.flip-instᵐ (C.sym∼ cᴸ)
      child<outer : castSize cᴸˢ <
          castSize ((inst cᴸ) A≢★)
      child<outer = subst (λ n → n < suc (castSize cᴸ))
        (sym (transformed-child-size cᴸ))
        (n<1+n (castSize cᴸ))
    paired-ground-injection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) qA access
        with source-occurs-target refl pC zero∈C
    paired-ground-injection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) qA access | zero∈D
        with consistency-source-occurs-target refl cᴿ zero∈D
    paired-ground-injection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑∀ pC) qA access | zero∈D | ()
    paired-ground-injection-core {μ = μ}
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) Gᵍ Bns
        (inst_ ⦃ Dnv ⦄ ⦃ zero∈D ⦄ cᴿ G≢★)
        (I.∀⊑∀ pC) qA (acc smaller) =
      unshift-⊑
        (paired-ground-projection-core cᴸˢ
          (gen-safe cᴸˢ A≢★ Cnv zero∈C)
          (shift-ground Gᵍ) (nonvar-occurs-nonstar Dnv zero∈D)
          (C.sym∼ cᴿ)
          (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) qA)
          (imp-env-weaken ext-to-inst-star-map pC)
          (smaller child<outer))
      where
      cᴸˢ = C.transport-env∼ C.flip-instᵐ (C.sym∼ cᴸ)
      child<outer : castSize cᴸˢ < castSize ((inst cᴸ) A≢★)
      child<outer = subst (λ n → n < suc (castSize cᴸ))
        (sym (transformed-child-size cᴸ))
        (n<1+n (castSize cᴸ))
    paired-ground-injection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) ∀★ Bns bot-elim
        (I.∀⊑∀ pC) qA access
        with subst NonVar (imprecision-to-fresh pC) Cnv
    paired-ground-injection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) ∀★ Bns bot-elim
        (I.∀⊑∀ pC) qA access | ()

    paired-ground-injection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★ safe) Gᵍ Bns cᴿ pC
        (I.∀⊑ Anv′ zero∈A′ qA) (acc smaller) =
      I.∀⊑ Anv′ zero∈A′
        (paired-ground-injection-core cᴸ safe
          (shift-ground Gᵍ) (C.renameNonStar Fin.suc Bns)
          (C.renameEnvᶜ {ν = C.extᵐ _} Fin.suc (λ X → refl) cᴿ)
          (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) pC) qA
          (smaller (n<1+n (castSize cᴸ))))
    paired-ground-injection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★ safe) Gᵍ Bns cᴿ pC (I.∀⊑★ Ans qA)
        access with source-occurs-target refl qA zero∈A
    paired-ground-injection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★ safe) Gᵍ Bns cᴿ pC (I.∀⊑★ Ans qA)
        access | ()

    paired-ground-projection-core : ∀ {Δ : TyCtx}
        {μ : I.ImpEnv Δ} {νᴸ νᴿ : Env∼ Δ}
        {C A G B : Ty Δ}
      → (cᴸ : νᴸ ⊢ C ∼ A)
      → GenSafe cᴸ
      → Ground G
      → NonStar B
      → νᴿ ⊢ G ∼ B
      → μ I.⊢ C ⊑ ★
      → μ I.⊢ A ⊑ B
      → Acc _<_ (castSize cᴸ)
      → μ I.⊢ C ⊑ G
    paired-ground-projection-core (cᴸ ↦ dᴸ) safe-⇒ ★⇒★ Bns
        (cᴿ ↦ dᴿ) (I.⇒⊑★ pC pD) (I.⇒⊑⇒ qA qA′) access =
      I.⇒⊑⇒ pC pD
    paired-ground-projection-core (cᴸ ↦ dᴸ) safe-⇒ (＇ X) Bns ()
        (I.⇒⊑★ pC pD) (I.⇒⊑⇒ qA qA′) access
    paired-ground-projection-core (cᴸ ↦ dᴸ) safe-⇒ (‵ ι) Bns ()
        (I.⇒⊑★ pC pD) (I.⇒⊑⇒ qA qA′) access
    paired-ground-projection-core (cᴸ ↦ dᴸ) safe-⇒ ∀★ Bns
        (inst_ ⦃ Anv ⦄ ⦃ () ⦄ cᴿ B≢★)
        (I.⇒⊑★ pC pD) (I.⇒⊑⇒ qA qA′) access

    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑ Anv zero∈A pC) (I.∀⊑ Bnv zero∈B qA)
        (acc smaller) =
      I.∀⊑ Anv zero∈A
        (paired-ground-projection-core cᴸ
          (ext-safe cᴸ Bnv zero∈B)
          (shift-ground Gᵍ) (C.renameNonStar Fin.suc Bns)
          (C.renameEnvᶜ {ν = C.extᵐ _} Fin.suc (λ X → refl) cᴿ)
          pC qA (smaller (n<1+n (castSize cᴸ))))
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑ Anv zero∈A pC) (I.∀⊑∀ qA) access
        with consistency-source-occurs-target refl cᴸ zero∈A
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑ Anv zero∈A pC) (I.∀⊑∀ qA) access
        | zero∈B with source-occurs-target refl qA zero∈B
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑ Anv zero∈A pC) (I.∀⊑∀ qA) access
        | zero∈B | zero∈D
        with consistency-target-occurs-source refl cᴿ zero∈D
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns (∀ᶜ cᴿ)
        (I.∀⊑ Anv zero∈A pC) (I.∀⊑∀ qA) access
        | zero∈B | zero∈D | ()
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns
        (gen_ ⦃ Dnv ⦄ ⦃ zero∈D ⦄ cᴿ G≢★)
        (I.∀⊑ Anv zero∈A pC) (I.∀⊑∀ qA) (acc smaller) =
      I.∀⊑ Anv zero∈A
        (paired-ground-projection-core cᴸ
          (ext-safe cᴸ Bnv zero∈B)
          (shift-ground Gᵍ) (nonvar-occurs-nonstar Dnv zero∈D) cᴿ
          pC (imp-env-weaken ext-to-inst-star-map qA)
          (smaller (n<1+n (castSize cᴸ))))
      where
      Bnv = source-nonvar-from-target qA Dnv zero∈D
      zero∈B = target-occurs-source qA zero∈D
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ ∀★ Bns
        bot-intro (I.∀⊑ Anv zero∈A pC) (I.∀⊑∀ qA) access =
      ⊥-elim
        (C.nonstar-nonvar-to-var-impossible
          (C.subst-right-∼ (imprecision-to-fresh qA) cᴸ)
          Anv (nonvar-occurs-nonstar Anv zero∈A))
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑ Anv zero∈A pC) I.bot-elim access =
      ⊥-elim
        (C.nonstar-nonvar-to-var-impossible cᴸ Anv
          (nonvar-occurs-nonstar Anv zero∈A))
    paired-ground-projection-core {μ = μ} (∀ᶜ cᴸ) safe-∀ Gᵍ
        Bns cᴿ I.∀★⊑★ (I.∀⊑∀ qA) access =
      subst (λ H → μ I.⊢ `∀ ★ ⊑ H) (sym G≡∀★)
        (I.∀⊑∀ I.★⊑★)
      where
      A∉zero = consistency-target-absent refl cᴸ ∉-star
      D∉zero = imprecision-target-absent refl qA A∉zero
      G≡∀★ = ground-universal-without-zero Gᵍ cᴿ D∉zero
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.∀★⊑★ (I.∀⊑ Anv zero∈A qA) access =
      ⊥-elim (absent-occurs⊥
        (consistency-target-absent refl cᴸ ∉-star) zero∈A)
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.∀★⊑★ I.∀★⊑★ access
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.∀★⊑★ (I.∀⊑★ Ans qA) access
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.∀★⊑★ I.bot-elim access =
      ⊥-elim (absent-occurs⊥
        (consistency-target-absent refl cᴸ ∉-star) var-∈)
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.∀★⊑★ I.bot⊑★ access
    paired-ground-projection-core {μ = μ} (∀ᶜ cᴸ) safe-∀ Gᵍ
        Bns cᴿ (I.∀⊑★ Ans pC) (I.∀⊑∀ qA) access =
      subst (λ H → μ I.⊢ `∀ _ ⊑ H) (sym G≡∀★)
        (I.∀⊑∀ pC)
      where
      C∉zero = imprecision-source-absent refl pC ∉-star
      A∉zero = consistency-target-absent refl cᴸ C∉zero
      D∉zero = imprecision-target-absent refl qA A∉zero
      G≡∀★ = ground-universal-without-zero Gᵍ cᴿ D∉zero
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑★ Ans pC) (I.∀⊑ Anv zero∈A qA) access =
      ⊥-elim (absent-occurs⊥ A∉zero zero∈A)
      where
      C∉zero = imprecision-source-absent refl pC ∉-star
      A∉zero = consistency-target-absent refl cᴸ C∉zero
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        (I.∀⊑★ Ans pC) I.∀★⊑★ access
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        (I.∀⊑★ Ans pC) (I.∀⊑★ Bns′ qA) access
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        (I.∀⊑★ Ans pC) I.bot-elim access =
      ⊥-elim (absent-occurs⊥ A∉zero var-∈)
      where
      C∉zero = imprecision-source-absent refl pC ∉-star
      A∉zero = consistency-target-absent refl cᴸ C∉zero
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        (I.∀⊑★ Ans pC) I.bot⊑★ access
    paired-ground-projection-core {μ = μ} {νᴿ = νᴿ}
        (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ I.bot⊑★
        (I.∀⊑∀ qA) access =
      subst (λ H → μ I.⊢ `∀ (＇ Fin.zero) ⊑ H) (sym G≡∀★)
        I.bot-elim
      where
      A≡zero = consistency-from-fresh cᴸ
      qA′ : I.extᵐ μ I.⊢ ＇ Fin.zero ⊑ _
      qA′ = subst (λ A → I.extᵐ μ I.⊢ A ⊑ _) A≡zero qA
      D≡zero = imprecision-from-fresh qA′
      cᴿ′ : νᴿ ⊢ _ ∼ `∀ (＇ Fin.zero)
      cᴿ′ = subst (λ D → νᴿ ⊢ _ ∼ `∀ D) D≡zero cᴿ
      G≡∀★ = ground-bottom-shape Gᵍ cᴿ′
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.bot⊑★ (I.∀⊑ Anv zero∈A qA) access
        with subst NonVar (consistency-from-fresh cᴸ) Anv
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ Bns cᴿ
        I.bot⊑★ (I.∀⊑ Anv zero∈A qA) access | ()
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.bot⊑★ I.∀★⊑★ access
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.bot⊑★ (I.∀⊑★ Bns′ qA) access
    paired-ground-projection-core {μ = μ} (∀ᶜ cᴸ) safe-∀ Gᵍ Bns
        cᴿ I.bot⊑★ I.bot-elim access =
      subst (λ H → μ I.⊢ `∀ (＇ Fin.zero) ⊑ H) (sym G≡∀★)
        I.bot-elim
      where
      G≡∀★ = ground-universal-without-zero Gᵍ cᴿ ∉-star
    paired-ground-projection-core (∀ᶜ cᴸ) safe-∀ Gᵍ () cᴿ
        I.bot⊑★ I.bot⊑★ access

    paired-ground-projection-core {μ = μ} {νᴿ = νᴿ}
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) Gᵍ Bns cᴿ
        (I.∀⊑ Cnv′ zero∈C′ pC) qA (acc smaller) =
      I.∀⊑ Cnv′ zero∈C′
        (paired-ground-injection-core cᴸˢ
          (gen-safe cᴸˢ A≢★ Cnv zero∈C)
          (shift-ground Gᵍ) (C.renameNonStar Fin.suc Bns)
          (C.renameEnvᶜ {ν = C.extᵐ (C.flipᵐ νᴿ)}
            Fin.suc (λ X → refl) (C.sym∼ cᴿ))
          (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) qA) pC
          (smaller child<outer))
      where
      cᴸˢ = C.transport-env∼ C.flip-instᵐ (C.sym∼ cᴸ)
      child<outer : castSize cᴸˢ < castSize ((inst cᴸ) A≢★)
      child<outer = subst (λ n → n < suc (castSize cᴸ))
        (sym (transformed-child-size cᴸ))
        (n<1+n (castSize cᴸ))
    paired-ground-projection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) Gᵍ Bns cᴿ
        (I.∀⊑★ Cns pC) qA access
        with source-occurs-target refl pC zero∈C
    paired-ground-projection-core
        ((inst_ ⦃ Cnv ⦄ ⦃ zero∈C ⦄ cᴸ) A≢★)
        (safe-inst A≢★′) Gᵍ Bns cᴿ
        (I.∀⊑★ Cns pC) qA access | ()

    paired-ground-projection-core {νᴿ = νᴿ}
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) Gᵍ Bns cᴿ pC
        (I.∀⊑ Anv′ zero∈A′ qA) (acc smaller) =
      unshift-⊑
        (paired-ground-projection-core cᴸ safe
          (shift-ground Gᵍ) (C.renameNonStar Fin.suc Bns)
          (C.renameEnvᶜ {ν = C.extᵐ νᴿ}
            Fin.suc (λ X → refl) cᴿ)
          (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) pC) qA
          (smaller (n<1+n (castSize cᴸ))))
    paired-ground-projection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) ∀★ Bns (∀ᶜ cᴿ) pC
        (I.∀⊑∀ qA) access
        with source-occurs-target refl qA zero∈A
    paired-ground-projection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) ∀★ Bns (∀ᶜ cᴿ) pC
        (I.∀⊑∀ qA) access | zero∈D
        with consistency-target-occurs-source refl cᴿ zero∈D
    paired-ground-projection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) ∀★ Bns (∀ᶜ cᴿ) pC
        (I.∀⊑∀ qA) access | zero∈D | ()
    paired-ground-projection-core {μ = μ}
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) Gᵍ Bns
        (gen_ ⦃ Dnv ⦄ ⦃ zero∈D ⦄ cᴿ G≢★) pC
        (I.∀⊑∀ qA) (acc smaller) =
      unshift-⊑
        (paired-ground-projection-core cᴸ safe
          (shift-ground Gᵍ) (nonvar-occurs-nonstar Dnv zero∈D) cᴿ
          (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) pC)
          (imp-env-weaken ext-to-inst-star-map qA)
          (smaller (n<1+n (castSize cᴸ))))
    paired-ground-projection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) ∀★ Bns bot-intro pC
        (I.∀⊑∀ qA) access
        with subst NonVar (imprecision-to-fresh qA) Anv
    paired-ground-projection-core
        ((gen_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ cᴸ) C≠★)
        (safe-gen C≠★′ safe) ∀★ Bns bot-intro pC
        (I.∀⊑∀ qA) access | ()


more-precise-gen-safe-target-ground-cast-square :
  MorePreciseGenSafeTargetGroundCastSquareᵀ
more-precise-gen-safe-target-ground-cast-square {cᴸ = cᴸ}
    safe Gᵍ Bns cᴿ pC qA =
  paired-ground-injection-core cᴸ safe Gᵍ Bns cᴿ pC qA
    (NatInduction.<-wellFounded (castSize cᴸ))

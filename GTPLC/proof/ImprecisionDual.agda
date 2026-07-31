module proof.ImprecisionDual where

-- File Charter:
--   * Defines duality for one-context GTPLC narrowing and widening.
--   * Changes tag mediation to seal mediation across `gen`/`inst`.
--   * Tracks the corresponding change to the type store.
--   * Exposes the ordinary same-mode, same-store dual operators.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden

------------------------------------------------------------------------
-- Mode and store changes performed by duality
------------------------------------------------------------------------

data ModeAction : Mode → DualAction → Mode → Set where
  normal-id : ModeAction id-only normal id-only
  normal-tag : ModeAction tag-or-id normal tag-or-id
  normal-seal : ModeAction seal-or-id normal seal-or-id
  tag-seal : ModeAction tag-or-id tag-to-seal seal-or-id
  seal-tag : ModeAction seal-or-id seal-to-tag tag-or-id

DualActionOk : ModeEnv → DualActionEnv → ModeEnv → Set
DualActionOk μ η ν = ∀ X → ModeAction (μ X) (η X) (ν X)

normal-action : ∀ {μ} → DualActionOk μ normalᵃ μ
normal-action {μ} X with μ X
normal-action X | id-only = normal-id
normal-action X | tag-or-id = normal-tag
normal-action X | seal-or-id = normal-seal

ext-action : ∀ {μ η ν}
  → DualActionOk μ η ν
  → DualActionOk (extᵈ μ) (extᵃ η) (extᵈ ν)
ext-action rel zero = normal-id
ext-action rel (suc X) = rel X

gen-inst-action : ∀ {μ η ν}
  → DualActionOk μ η ν
  → DualActionOk (genᵈ μ) (genᵃ η) (instᵈ ν)
gen-inst-action rel zero = tag-seal
gen-inst-action rel (suc X) = rel X

inst-gen-action : ∀ {μ η ν}
  → DualActionOk μ η ν
  → DualActionOk (instᵈ μ) (instᵃ η) (genᵈ ν)
inst-gen-action rel zero = seal-tag
inst-gen-action rel (suc X) = rel X

tag-var-allowed : ∀ (ν : ModeEnv) (X : TyVar)
  → ν X ≡ tag-or-id
  → tagAllowed ν (＇ X) ≡ true
tag-var-allowed ν X eq =
  subst (λ mode → tagModeAllowed mode ≡ true) (sym eq) refl

seal-var-allowed : ∀ (ν : ModeEnv) (X : TyVar)
  → ν X ≡ seal-or-id
  → sealModeAllowed (ν X) ≡ true
seal-var-allowed ν X eq =
  subst (λ mode → sealModeAllowed mode ≡ true) (sym eq) refl

∈-⟰ᵗ : ∀ {Σ X A}
  → (X , A) ∈ Σ
  → (suc X , ⇑ᵗ A) ∈ ⟰ᵗ Σ
∈-⟰ᵗ (here refl) = here refl
∈-⟰ᵗ (there X,A∈Σ) = there (∈-⟰ᵗ X,A∈Σ)

zero∉-⟰ᵗ : ∀ {Σ A}
  → (zero , A) ∈ ⟰ᵗ Σ
  → ⊥
zero∉-⟰ᵗ {Σ = []} ()
zero∉-⟰ᵗ {Σ = _ ∷ Σ} (here ())
zero∉-⟰ᵗ {Σ = _ ∷ Σ} (there X,A∈Σ) =
  zero∉-⟰ᵗ X,A∈Σ

suc∈-tail : ∀ {Σ X A C}
  → (suc X , A) ∈ ((zero , C) ∷ ⟰ᵗ Σ)
  → (suc X , A) ∈ ⟰ᵗ Σ
suc∈-tail (here ())
suc∈-tail (there X,A∈Σ) = X,A∈Σ

∈-⟰ᵗ-inv : ∀ {Σ X A}
  → (suc X , A) ∈ ⟰ᵗ Σ
  → ∃[ B ] ((X , B) ∈ Σ × A ≡ ⇑ᵗ B)
∈-⟰ᵗ-inv {Σ = []} ()
∈-⟰ᵗ-inv {Σ = _ ∷ Σ} (here refl) =
  _ , here refl , refl
∈-⟰ᵗ-inv {Σ = _ ∷ Σ} (there X,A∈Σ)
    with ∈-⟰ᵗ-inv X,A∈Σ
∈-⟰ᵗ-inv {Σ = _ ∷ Σ} (there X,A∈Σ)
    | B , X,B∈Σ , refl =
  B , there X,B∈Σ , refl

record DualStoreAt
    (Δ : TyCtx) (μ : ModeEnv) (η : DualActionEnv) (ν : ModeEnv)
    (Σ Π : TyStore) : Set where
  field
    tag★∈ : ∀ {X}
      → X < Δ
      → η X ≡ tag-to-seal
      → (X , ★) ∈ Π
    seal∈ : ∀ {X A}
      → μ X ≡ seal-or-id
      → η X ≡ normal
      → ν X ≡ seal-or-id
      → (X , A) ∈ Σ
      → (X , A) ∈ Π
    seal★ : ∀ {X A}
      → η X ≡ seal-to-tag
      → (X , A) ∈ Σ
      → A ≡ ★

open DualStoreAt

normal-store : ∀ Δ μ Σ
  → DualStoreAt Δ μ normalᵃ μ Σ Σ
normal-store Δ μ Σ .tag★∈ X<Δ ()
normal-store Δ μ Σ .seal∈ μα ηα να X,A∈Σ = X,A∈Σ
normal-store Δ μ Σ .seal★ () X,A∈Σ

ext-store : ∀ {Δ μ η ν Σ Π}
  → DualStoreAt Δ μ η ν Σ Π
  → DualStoreAt (suc Δ) (extᵈ μ) (extᵃ η) (extᵈ ν)
      (⟰ᵗ Σ) (⟰ᵗ Π)
ext-store ds .tag★∈ {zero} z<s ()
ext-store ds .tag★∈ {suc X} (s<s X<Δ) action =
  ∈-⟰ᵗ (tag★∈ ds X<Δ action)
ext-store ds .seal∈ {zero} () action να X,A∈Σ
ext-store ds .seal∈ {suc X} {A} μα action να X,A∈Σ
    with ∈-⟰ᵗ-inv X,A∈Σ
ext-store ds .seal∈ {suc X} μα action να X,A∈Σ
    | B , X,B∈Σ , refl =
  ∈-⟰ᵗ (seal∈ ds μα action να X,B∈Σ)
ext-store ds .seal★ {zero} () X,A∈Σ
ext-store ds .seal★ {suc X} {A} action X,A∈Σ
    with ∈-⟰ᵗ-inv X,A∈Σ
ext-store ds .seal★ {suc X} action X,A∈Σ
    | B , X,B∈Σ , refl
    rewrite seal★ ds action X,B∈Σ =
  refl

gen-inst-store : ∀ {Δ μ η ν Σ Π}
  → DualStoreAt Δ μ η ν Σ Π
  → DualStoreAt (suc Δ) (genᵈ μ) (genᵃ η) (instᵈ ν)
      (⟰ᵗ Σ) ((zero , ★) ∷ ⟰ᵗ Π)
gen-inst-store ds .tag★∈ {zero} z<s action = here refl
gen-inst-store ds .tag★∈ {suc X} (s<s X<Δ) action =
  there (∈-⟰ᵗ (tag★∈ ds X<Δ action))
gen-inst-store ds .seal∈ {zero} () action να X,A∈Σ
gen-inst-store ds .seal∈ {suc X} {A} μα action να X,A∈Σ
    with ∈-⟰ᵗ-inv X,A∈Σ
gen-inst-store ds .seal∈ {suc X} μα action να X,A∈Σ
    | B , X,B∈Σ , refl =
  there (∈-⟰ᵗ (seal∈ ds μα action να X,B∈Σ))
gen-inst-store ds .seal★ {zero} () X,A∈Σ
gen-inst-store ds .seal★ {suc X} {A} action X,A∈Σ
    with ∈-⟰ᵗ-inv X,A∈Σ
gen-inst-store ds .seal★ {suc X} action X,A∈Σ
    | B , X,B∈Σ , refl
    rewrite seal★ ds action X,B∈Σ =
  refl

inst-gen-store : ∀ {Δ μ η ν Σ Π}
  → DualStoreAt Δ μ η ν Σ Π
  → DualStoreAt (suc Δ) (instᵈ μ) (instᵃ η) (genᵈ ν)
      ((zero , ★) ∷ ⟰ᵗ Σ) (⟰ᵗ Π)
inst-gen-store ds .tag★∈ {zero} z<s ()
inst-gen-store ds .tag★∈ {suc X} (s<s X<Δ) action =
  ∈-⟰ᵗ (tag★∈ ds X<Δ action)
inst-gen-store ds .seal∈ {zero} μα () να X,A∈Σ
inst-gen-store ds .seal∈ {suc X} {A} μα action να X,A∈Σ
    with ∈-⟰ᵗ-inv (suc∈-tail X,A∈Σ)
inst-gen-store ds .seal∈ {suc X} μα action να X,A∈Σ
    | B , X,B∈Σ , refl =
  ∈-⟰ᵗ (seal∈ ds μα action να X,B∈Σ)
inst-gen-store ds .seal★ {zero} action (here refl) = refl
inst-gen-store ds .seal★ {zero} action (there X,A∈Σ) =
  ⊥-elim (zero∉-⟰ᵗ X,A∈Σ)
inst-gen-store ds .seal★ {suc X} {A} action X,A∈Σ
    with ∈-⟰ᵗ-inv (suc∈-tail X,A∈Σ)
inst-gen-store ds .seal★ {suc X} action X,A∈Σ
    | B , X,B∈Σ , refl
    rewrite seal★ ds action X,B∈Σ =
  refl

------------------------------------------------------------------------
-- Atomic duals
------------------------------------------------------------------------

dual-untag : ∀ {μ η ν Δ Σ Π G A}
  → DualActionOk μ η ν
  → DualStoreAt Δ μ η ν Σ Π
  → WfTag Δ G
  → tagAllowed μ G ≡ true
  → G ꞉ A
  → ν ∣ Δ ∣ Π ⊢ A ⊑ ★
dual-untag {μ = μ} {η = η} {ν = ν} {G = ＇ X}
    rel ds (wfTagVar X<Δ) allowed (tag-var .X)
    with μ X in μα | η X in ηα | ν X in να | rel X | allowed
dual-untag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | id-only | normal | id-only | normal-id | ()
dual-untag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | tag-or-id | normal | tag-or-id | normal-tag | refl =
  (＇ X) ! ,
  tag (＇ X) (wfTagVar X<Δ) (tag-var-allowed ν X να) (tag-var X)
dual-untag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | seal-or-id | normal | seal-or-id | normal-seal | ()
dual-untag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | tag-or-id | tag-to-seal | seal-or-id | tag-seal | refl =
  unseal X ,
  unseal X<Δ wf★ (tag★∈ ds X<Δ ηα) (seal-var-allowed ν X να)
dual-untag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | seal-or-id | seal-to-tag | tag-or-id | seal-tag | ()
dual-untag rel ds wfTagBase allowed (tag-base ι) =
  (‵ ι) ! , tag (‵ ι) wfTagBase refl (tag-base ι)
dual-untag rel ds wf★⇒★ allowed tag-fun =
  ★⇒★ ! , tag ★⇒★ wf★⇒★ refl tag-fun

dual-tag : ∀ {μ η ν Δ Σ Π G A}
  → DualActionOk μ η ν
  → DualStoreAt Δ μ η ν Σ Π
  → WfTag Δ G
  → tagAllowed μ G ≡ true
  → G ꞉ A
  → ν ∣ Δ ∣ Π ⊢ ★ ⊒ A
dual-tag {μ = μ} {η = η} {ν = ν} {G = ＇ X}
    rel ds (wfTagVar X<Δ) allowed (tag-var .X)
    with μ X in μα | η X in ηα | ν X in να | rel X | allowed
dual-tag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | id-only | normal | id-only | normal-id | ()
dual-tag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | tag-or-id | normal | tag-or-id | normal-tag | refl =
  (＇ X) ？ ,
  untag (＇ X) (wfTagVar X<Δ) (tag-var-allowed ν X να) (tag-var X)
dual-tag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | seal-or-id | normal | seal-or-id | normal-seal | ()
dual-tag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | tag-or-id | tag-to-seal | seal-or-id | tag-seal | refl =
  seal X ,
  seal X<Δ wf★ (tag★∈ ds X<Δ ηα) (seal-var-allowed ν X να)
dual-tag {ν = ν} {G = ＇ X} rel ds
    (wfTagVar X<Δ) allowed (tag-var .X)
    | seal-or-id | seal-to-tag | tag-or-id | seal-tag | ()
dual-tag rel ds wfTagBase allowed (tag-base ι) =
  (‵ ι) ？ , untag (‵ ι) wfTagBase refl (tag-base ι)
dual-tag rel ds wf★⇒★ allowed tag-fun =
  ★⇒★ ？ , untag ★⇒★ wf★⇒★ refl tag-fun

dual-seal : ∀ {μ η ν Δ Σ Π X A}
  → DualActionOk μ η ν
  → DualStoreAt Δ μ η ν Σ Π
  → X < Δ
  → WfTy Δ A
  → (X , A) ∈ Σ
  → sealModeAllowed (μ X) ≡ true
  → ν ∣ Δ ∣ Π ⊢ ＇ X ⊑ A
dual-seal {μ = μ} {η = η} {ν = ν} {X = X}
    rel ds X<Δ hA X,A∈Σ allowed
    with μ X in μα | η X in ηα | ν X in να | rel X | allowed
dual-seal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | id-only | normal | id-only | normal-id | ()
dual-seal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | tag-or-id | normal | tag-or-id | normal-tag | ()
dual-seal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | seal-or-id | normal | seal-or-id | normal-seal | refl =
  unseal X ,
  unseal X<Δ hA (seal∈ ds μα ηα να X,A∈Σ)
    (seal-var-allowed ν X να)
dual-seal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | tag-or-id | tag-to-seal | seal-or-id | tag-seal | ()
dual-seal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | seal-or-id | seal-to-tag | tag-or-id | seal-tag | refl
    rewrite seal★ ds ηα X,A∈Σ =
  (＇ X) ! ,
  tag (＇ X) (wfTagVar X<Δ) (tag-var-allowed ν X να) (tag-var X)

dual-unseal : ∀ {μ η ν Δ Σ Π X A}
  → DualActionOk μ η ν
  → DualStoreAt Δ μ η ν Σ Π
  → X < Δ
  → WfTy Δ A
  → (X , A) ∈ Σ
  → sealModeAllowed (μ X) ≡ true
  → ν ∣ Δ ∣ Π ⊢ A ⊒ ＇ X
dual-unseal {μ = μ} {η = η} {ν = ν} {X = X}
    rel ds X<Δ hA X,A∈Σ allowed
    with μ X in μα | η X in ηα | ν X in να | rel X | allowed
dual-unseal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | id-only | normal | id-only | normal-id | ()
dual-unseal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | tag-or-id | normal | tag-or-id | normal-tag | ()
dual-unseal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | seal-or-id | normal | seal-or-id | normal-seal | refl =
  seal X ,
  seal X<Δ hA (seal∈ ds μα ηα να X,A∈Σ)
    (seal-var-allowed ν X να)
dual-unseal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | tag-or-id | tag-to-seal | seal-or-id | tag-seal | ()
dual-unseal {ν = ν} {X = X} rel ds X<Δ hA X,A∈Σ allowed
    | seal-or-id | seal-to-tag | tag-or-id | seal-tag | refl
    rewrite seal★ ds ηα X,A∈Σ =
  (＇ X) ？ ,
  untag (＇ X) (wfTagVar X<Δ) (tag-var-allowed ν X να) (tag-var X)

------------------------------------------------------------------------
-- Duality
------------------------------------------------------------------------

mutual

  narrowing-dualᵐ : ∀ {μ η ν Δ Σ Π c A B}
    → DualActionOk μ η ν
    → DualStoreAt Δ μ η ν Σ Π
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → ν ∣ Δ ∣ Π ⊢ B ⊑ A
  narrowing-dualᵐ rel ds (idᵃ a hA) =
    id , idᵃ a hA
  narrowing-dualᵐ rel ds (p ↦ q)
      with widening-dualᵐ rel ds p | narrowing-dualᵐ rel ds q
  narrowing-dualᵐ rel ds (p ↦ q)
      | c , p′ | d , q′ =
    (c ↦ d) , (p′ ↦ q′)
  narrowing-dualᵐ rel ds (∀ⁿ p)
      with narrowing-dualᵐ (ext-action rel) (ext-store ds) p
  narrowing-dualᵐ rel ds (∀ⁿ p) | c , p′ =
    `∀ c , ∀ʷ p′
  narrowing-dualᵐ rel ds (seqⁿ p q)
      with narrowing-dualᵐ rel ds q | narrowing-dualᵐ rel ds p
  narrowing-dualᵐ rel ds (seqⁿ p q)
      | d , q′ | c , p′ =
    (d ︔ c) , seqʷ q′ p′
  narrowing-dualᵐ rel ds (untag G hG allowed G꞉A) =
    dual-untag rel ds hG allowed G꞉A
  narrowing-dualᵐ rel ds
      (untag-seq G hG allowed G꞉A p A≢B)
      with narrowing-dualᵐ rel ds p
  narrowing-dualᵐ {μ = μ} {η = η} {ν = ν} rel ds
      (untag-seq (＇ X) hG allowed G꞉A p A≢B)
      | d , p′
      with μ X in μα | η X in ηα | ν X in να | rel X | allowed
  narrowing-dualᵐ {ν = ν} rel ds
      (untag-seq (＇ X) hG allowed G꞉A p A≢B)
      | d , p′ | id-only | normal | id-only | normal-id | ()
  narrowing-dualᵐ {ν = ν} rel ds
      (untag-seq (＇ X) hG allowed G꞉A p A≢B)
      | d , p′ | tag-or-id | normal | tag-or-id | normal-tag | refl =
    wrap-tag p′ hG (tag-var-allowed ν X να) G꞉A
  narrowing-dualᵐ {ν = ν} rel ds
      (untag-seq (＇ X) (wfTagVar X<Δ) allowed G꞉A p A≢B)
      | d , p′
      | seal-or-id | normal | seal-or-id | normal-seal | ()
  narrowing-dualᵐ {ν = ν} rel ds
      (untag-seq (＇ X) (wfTagVar X<Δ) allowed (tag-var .X) p A≢B)
      | d , p′
      | tag-or-id | tag-to-seal | seal-or-id | tag-seal | refl =
    wrap-unseal-tail p′ X<Δ wf★ (tag★∈ ds X<Δ ηα)
      (seal-var-allowed ν X να)
  narrowing-dualᵐ {ν = ν} rel ds
      (untag-seq (＇ X) hG allowed G꞉A p A≢B)
      | d , p′
      | seal-or-id | seal-to-tag | tag-or-id | seal-tag | ()
  narrowing-dualᵐ rel ds
      (untag-seq (‵ ι) hG allowed G꞉A p A≢B)
      | d , p′ =
    wrap-tag p′ hG refl G꞉A
  narrowing-dualᵐ rel ds
      (untag-seq ★⇒★ hG allowed G꞉A p A≢B)
      | d , p′ =
    wrap-tag p′ hG refl G꞉A
  narrowing-dualᵐ rel ds (seal X<Δ hA X,A∈Σ allowed) =
    dual-seal rel ds X<Δ hA X,A∈Σ allowed
  narrowing-dualᵐ {ν = ν} {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      with narrowing-dualᵐ rel ds p
  narrowing-dualᵐ {μ = μ} {η = η} {ν = ν} {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      | d , p′
      with μ X in μα | η X in ηα | ν X in να | rel X | allowed
  narrowing-dualᵐ {ν = ν} {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      | d , p′ | id-only | normal | id-only | normal-id | ()
  narrowing-dualᵐ {ν = ν} {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      | d , p′ | tag-or-id | normal | tag-or-id | normal-tag | ()
  narrowing-dualᵐ {ν = ν} {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      | d , p′ | seal-or-id | normal | seal-or-id | normal-seal | refl =
    wrap-unseal X<Δ (seal∈ ds μα ηα να X,B∈Σ)
      (seal-var-allowed ν X να) p′
  narrowing-dualᵐ {ν = ν} {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      | d , p′ | tag-or-id | tag-to-seal | seal-or-id | tag-seal | ()
  narrowing-dualᵐ {B = ＇ X} rel ds
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      | d , p′ | seal-or-id | seal-to-tag | tag-or-id | seal-tag | refl
      rewrite seal★ ds ηα X,B∈Σ =
    ⊥-elim (A≢B (narrowing-to-star p))
  narrowing-dualᵐ {ν = ν} {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      with narrowing-dualᵐ rel ds p
  narrowing-dualᵐ {μ = μ} {η = η} {ν = ν}
      {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      | d , p′
      with μ X in μα | η X in ηα | ν X in να | rel X | allowed
  narrowing-dualᵐ {ν = ν} {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      | d , p′ | id-only | normal | id-only | normal-id | ()
  narrowing-dualᵐ {ν = ν} {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      | d , p′ | tag-or-id | normal | tag-or-id | normal-tag | ()
  narrowing-dualᵐ {ν = ν} {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      | d , p′ | seal-or-id | normal | seal-or-id | normal-seal | refl =
    wrap-unseal-tail p′ X<Δ hA
      (seal∈ ds μα ηα να X,A∈Σ) (seal-var-allowed ν X να)
  narrowing-dualᵐ {ν = ν} {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      | d , p′ | tag-or-id | tag-to-seal | seal-or-id | tag-seal | ()
  narrowing-dualᵐ {ν = ν} {c = seal X ︔ c} rel ds
      (seal-head X<Δ hA X,A∈Σ allowed p X≢B)
      | d , p′ | seal-or-id | seal-to-tag | tag-or-id | seal-tag | refl
      rewrite seal★ ds ηα X,A∈Σ =
    wrap-tag p′ (wfTagVar X<Δ) (tag-var-allowed ν X να) (tag-var X)
  narrowing-dualᵐ rel ds (gen nonvarA zero∈A hB p B≢★)
      with narrowing-dualᵐ
        (gen-inst-action rel) (gen-inst-store ds) p
  narrowing-dualᵐ rel ds (gen nonvarA zero∈A hB p B≢★)
      | c , p′ =
    inst c , inst nonvarA zero∈A hB p′ B≢★

  widening-dualᵐ : ∀ {μ η ν Δ Σ Π c A B}
    → DualActionOk μ η ν
    → DualStoreAt Δ μ η ν Σ Π
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → ν ∣ Δ ∣ Π ⊢ B ⊒ A
  widening-dualᵐ rel ds (idᵃ a hA) =
    id , idᵃ a hA
  widening-dualᵐ rel ds (p ↦ q)
      with narrowing-dualᵐ rel ds p | widening-dualᵐ rel ds q
  widening-dualᵐ rel ds (p ↦ q)
      | c , p′ | d , q′ =
    (c ↦ d) , (p′ ↦ q′)
  widening-dualᵐ rel ds (∀ʷ p)
      with widening-dualᵐ (ext-action rel) (ext-store ds) p
  widening-dualᵐ rel ds (∀ʷ p) | c , p′ =
    `∀ c , ∀ⁿ p′
  widening-dualᵐ rel ds (seqʷ p q)
      with widening-dualᵐ rel ds q | widening-dualᵐ rel ds p
  widening-dualᵐ rel ds (seqʷ p q)
      | d , q′ | c , p′ =
    (d ︔ c) , seqⁿ q′ p′
  widening-dualᵐ rel ds (tag G hG allowed G꞉A) =
    dual-tag rel ds hG allowed G꞉A
  widening-dualᵐ rel ds (tag-seq G p hG allowed G꞉B A≢B)
      with widening-dualᵐ rel ds p
  widening-dualᵐ {μ = μ} {η = η} {ν = ν} rel ds
      (tag-seq (＇ X) p hG allowed G꞉B A≢B)
      | d , p′
      with μ X in μα | η X in ηα | ν X in να | rel X | allowed
  widening-dualᵐ {ν = ν} rel ds
      (tag-seq (＇ X) p hG allowed G꞉B A≢B)
      | d , p′ | id-only | normal | id-only | normal-id | ()
  widening-dualᵐ {ν = ν} rel ds
      (tag-seq (＇ X) p hG allowed G꞉B A≢B)
      | d , p′ | tag-or-id | normal | tag-or-id | normal-tag | refl =
    wrap-untag hG (tag-var-allowed ν X να) G꞉B p′
  widening-dualᵐ {ν = ν} rel ds
      (tag-seq (＇ X) p (wfTagVar X<Δ) allowed G꞉B A≢B)
      | d , p′
      | seal-or-id | normal | seal-or-id | normal-seal | ()
  widening-dualᵐ {ν = ν} rel ds
      (tag-seq (＇ X) p (wfTagVar X<Δ) allowed (tag-var .X) A≢B)
      | d , p′
      | tag-or-id | tag-to-seal | seal-or-id | tag-seal | refl =
    wrap-seal-head X<Δ wf★ (tag★∈ ds X<Δ ηα)
      (seal-var-allowed ν X να) p′
  widening-dualᵐ {ν = ν} rel ds
      (tag-seq (＇ X) p hG allowed G꞉B A≢B)
      | d , p′
      | seal-or-id | seal-to-tag | tag-or-id | seal-tag | ()
  widening-dualᵐ rel ds
      (tag-seq (‵ ι) p hG allowed G꞉B A≢B)
      | d , p′ =
    wrap-untag hG refl G꞉B p′
  widening-dualᵐ rel ds
      (tag-seq ★⇒★ p hG allowed G꞉B A≢B)
      | d , p′ =
    wrap-untag hG refl G꞉B p′
  widening-dualᵐ rel ds (unseal X<Δ hA X,A∈Σ allowed) =
    dual-unseal rel ds X<Δ hA X,A∈Σ allowed
  widening-dualᵐ {ν = ν} {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      with widening-dualᵐ rel ds p
  widening-dualᵐ {μ = μ} {η = η} {ν = ν} {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      | d , p′
      with μ X in μα | η X in ηα | ν X in να | rel X | allowed
  widening-dualᵐ {ν = ν} {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      | d , p′ | id-only | normal | id-only | normal-id | ()
  widening-dualᵐ {ν = ν} {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      | d , p′ | tag-or-id | normal | tag-or-id | normal-tag | ()
  widening-dualᵐ {ν = ν} {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      | d , p′ | seal-or-id | normal | seal-or-id | normal-seal | refl =
    wrap-seal p′ X<Δ (seal∈ ds μα ηα να X,A∈Σ)
      (seal-var-allowed ν X να)
  widening-dualᵐ {ν = ν} {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      | d , p′ | tag-or-id | tag-to-seal | seal-or-id | tag-seal | ()
  widening-dualᵐ {A = ＇ X} rel ds
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B)
      | d , p′ | seal-or-id | seal-to-tag | tag-or-id | seal-tag | refl
      rewrite seal★ ds ηα X,A∈Σ =
    ⊥-elim (A≢B (sym (widening-from-star p)))
  widening-dualᵐ {ν = ν} {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      with widening-dualᵐ rel ds p
  widening-dualᵐ {μ = μ} {η = η} {ν = ν}
      {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      | d , p′
      with μ X in μα | η X in ηα | ν X in να | rel X | allowed
  widening-dualᵐ {ν = ν} {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      | d , p′ | id-only | normal | id-only | normal-id | ()
  widening-dualᵐ {ν = ν} {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      | d , p′ | tag-or-id | normal | tag-or-id | normal-tag | ()
  widening-dualᵐ {ν = ν} {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      | d , p′ | seal-or-id | normal | seal-or-id | normal-seal | refl =
    wrap-seal-head X<Δ hB (seal∈ ds μα ηα να X,B∈Σ)
      (seal-var-allowed ν X να) p′
  widening-dualᵐ {ν = ν} {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      | d , p′ | tag-or-id | tag-to-seal | seal-or-id | tag-seal | ()
  widening-dualᵐ {ν = ν} {c = c ︔ unseal X} rel ds
      (unseal-tail p X<Δ hB X,B∈Σ allowed A≢X)
      | d , p′ | seal-or-id | seal-to-tag | tag-or-id | seal-tag | refl
      rewrite seal★ ds ηα X,B∈Σ =
    wrap-untag (wfTagVar X<Δ) (tag-var-allowed ν X να)
      (tag-var X) p′
  widening-dualᵐ rel ds (inst nonvarA zero∈A hB p B≢★)
      with widening-dualᵐ
        (inst-gen-action rel) (inst-gen-store ds) p
  widening-dualᵐ rel ds (inst nonvarA zero∈A hB p B≢★)
      | c , p′ =
    gen c , gen nonvarA zero∈A hB p′ B≢★

  narrowing-to-star : ∀ {μ Δ Σ c A}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ ★
    → A ≡ ★
  narrowing-to-star (idᵃ ★ hA) = refl
  narrowing-to-star (seqⁿ p q)
      with narrowing-to-star q
  narrowing-to-star (seqⁿ p q) | refl =
    narrowing-to-star p
  narrowing-to-star
      (untag-seq G hG allowed G꞉A p A≢★)
      with narrowing-to-star p
  narrowing-to-star
      (untag-seq G hG allowed () p A≢★) | refl
  narrowing-to-star
      (seal-head X<Δ hA X,A∈Σ allowed p X≢★)
      with narrowing-to-star p
  narrowing-to-star
      (seal-head X<Δ hA X,A∈Σ allowed p X≢★) | ()

  widening-from-star : ∀ {μ Δ Σ c B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ B
    → B ≡ ★
  widening-from-star (idᵃ ★ hA) = refl
  widening-from-star (seqʷ p q)
      with widening-from-star p
  widening-from-star (seqʷ p q) | refl =
    widening-from-star q
  widening-from-star
      (tag-seq G p hG allowed G꞉A ★≢A)
      with widening-from-star p
  widening-from-star
      (tag-seq G p hG allowed () ★≢A) | refl
  widening-from-star
      (unseal-tail p X<Δ hB X,B∈Σ allowed ★≢X)
      with widening-from-star p
  widening-from-star
      (unseal-tail p X<Δ hB X,B∈Σ allowed ★≢X) | ()

------------------------------------------------------------------------
-- Public same-world duals
------------------------------------------------------------------------

narrowing-dual : ∀ {μ Δ Σ c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊑ A
narrowing-dual {μ = μ} {Δ = Δ} {Σ = Σ} =
  narrowing-dualᵐ normal-action (normal-store Δ μ Σ)

widening-dual : ∀ {μ Δ Σ c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊒ A
widening-dual {μ = μ} {Δ = Δ} {Σ = Σ} =
  widening-dualᵐ normal-action (normal-store Δ μ Σ)

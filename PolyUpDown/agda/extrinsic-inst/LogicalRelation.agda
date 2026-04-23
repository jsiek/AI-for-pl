{-# OPTIONS --allow-unsolved-metas #-}

module LogicalRelation where

-- File Charter:
--   * Defines the step-indexed logical relation for `PolyUpDown`.
--   * Introduces direction/index/world/precision indices and `𝒱`/`ℰ` clauses.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; z<s; _<_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types
open import Store using (_⊆ˢ_; done; keep; drop; ⊆ˢ-refl; StoreWf)
open import Imprecision
open import TypeProperties
  using (liftSubstˢ; substᵗ-ν-src; substᵗ-⇑ˢ; substᵗ-id; renameᵗ-substᵗ;
         substᵗ-ground; renameᵗ-preserves-WfTy; renameˢ-preserves-WfTy;
         TyRenameWf-suc; SealRenameWf-suc)
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermPrecision using (Prec; PCtx)
open import TermProperties using (Substˣ; substˣ-term; _[_]; _[_]ᵀ)
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)

------------------------------------------------------------------------
-- Direction, world, and precision index
------------------------------------------------------------------------

data Dir : Set where
  ≼ : Dir
  ≽ : Dir

Rel : Set₁
Rel = ℕ → Dir → Term → Term → Set

record SealRel : Set₁ where
  constructor ηentry
  field
    αˡ : Seal
    αʳ : Seal
    Rη : Rel
open SealRel public

infix 4 _∋η_↔_∶_

data _∋η_↔_∶_ : List SealRel → Seal → Seal → Rel → Set₁ where
  hereη :
    ∀ {η αˡ αʳ R} →
    (ηentry αˡ αʳ R ∷ η) ∋η αˡ ↔ αʳ ∶ R

  thereη :
    ∀ {η αˡ αʳ R βˡ βʳ R′} →
    η ∋η αˡ ↔ αʳ ∶ R →
    (ηentry βˡ βʳ R′ ∷ η) ∋η αˡ ↔ αʳ ∶ R

infix 4 _⊆η_

data _⊆η_ : List SealRel → List SealRel → Set₁ where
  η-done : ∀ {η} → [] ⊆η η
  η-keep : ∀ {η η′ e} → η ⊆η η′ → (e ∷ η) ⊆η (e ∷ η′)
  η-drop : ∀ {η η′ e} → η ⊆η η′ → η ⊆η (e ∷ η′)

⊆η-refl : ∀ {η} → η ⊆η η
⊆η-refl {η = []} = η-done
⊆η-refl {η = e ∷ η} = η-keep ⊆η-refl

record World : Set₁ where
  constructor mkWorld
  field
    Δ : TyCtx
    Ψ : SealCtx
    Σˡ : Store
    Σʳ : Store
    wfΣˡ : StoreWf Δ Ψ Σˡ
    wfΣʳ : StoreWf Δ Ψ Σʳ
    η : List SealRel
open World public

record _⪰_ (w′ w : World) : Set₁ where
  field
    growΔ : Δ w′ ≡ Δ w
    growΨ : Ψ w′ ≡ Ψ w
    growˡ : Σˡ w ⊆ˢ Σˡ w′
    growʳ : Σʳ w ⊆ˢ Σʳ w′
    growη : η w ⊆η η w′

extendWorld : World → Rel → World
extendWorld w R =
  mkWorld (Δ w) (Ψ w) (Σˡ w) (Σʳ w) (wfΣˡ w) (wfΣʳ w)
    (ηentry (length (Σˡ w)) (length (Σʳ w)) R ∷ η w)

mkWorldˡ :
  (w : World) →
  (Σˡ′ : Store) →
  StoreWf (Δ w) (Ψ w) Σˡ′ →
  World
mkWorldˡ w Σˡ′ wfΣˡ′ =
  mkWorld (Δ w) (Ψ w) Σˡ′ (Σʳ w) wfΣˡ′ (wfΣʳ w) (η w)

mkWorldʳ :
  (w : World) →
  (Σʳ′ : Store) →
  StoreWf (Δ w) (Ψ w) Σʳ′ →
  World
mkWorldʳ w Σʳ′ wfΣʳ′ =
  mkWorld (Δ w) (Ψ w) (Σˡ w) Σʳ′ (wfΣˡ w) wfΣʳ′ (η w)

extendWorld-⪰ : ∀ {w} (R : Rel) → extendWorld w R ⪰ w
extendWorld-⪰ {w} R ._⪰_.growΔ = refl
extendWorld-⪰ {w} R ._⪰_.growΨ = refl
extendWorld-⪰ {w} R ._⪰_.growˡ = ⊆ˢ-refl
extendWorld-⪰ {w} R ._⪰_.growʳ = ⊆ˢ-refl
extendWorld-⪰ {w} R ._⪰_.growη = η-drop ⊆η-refl

--------------------------------------------------------------------------------
-- Logical relation core
--------------------------------------------------------------------------------

mutual
  𝒱payload : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱payload {A = ‵ `ℕ} {B = ‵ `ℕ} ⊑-‵ n dir w V W = nat-rel V W
    where
    nat-rel : Term → Term → Set₁
    nat-rel ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)
    nat-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱payload {A = ‵ `𝔹} {B = ‵ `𝔹} ⊑-‵ n dir w V W = Lift (lsuc 0ℓ) ⊥

  𝒱payload {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} (⊑-⇒ pA pB) n dir w V W =
    ∀ {V′ W′} →
      𝒱 pA n dir w V′ W′ →
      ℰ pB n dir w (V · V′) (W · W′)

  𝒱payload {A = `∀ Aˡ} {B = `∀ Aʳ} (⊑-∀ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (T U : Ty) →
      ℰ p n dir (extendWorld w′ R) (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])

  𝒱payload {A = `∀ Aˡ} {B = Bʳ} (⊑-ν p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) →
      ℰ p n dir (extendWorld w′ R) (V ⦂∀ Aˡ [ ｀ length (Σˡ w′) ]) W

  𝒱payload {A = ★} {B = ★} ⊑-★★ 0 dir w V W = Lift (lsuc 0ℓ) ⊤
  𝒱payload {A = ★} {B = ★} ⊑-★★ (suc n) dir w V W = star-rel V W
    where
    star-rel : Term → Term → Set₁
    star-rel (V up tag G) (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H)  ×  𝒱 (⊑-refl {A = G}) n dir w V W
    star-rel (V down seal αˡ) (W down seal αʳ) =
      Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × R n dir V W
    star-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱payload {A = A} {B = ★} (⊑-★ {G = G} g p) 0 ≼ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱payload {A = A} {B = ★} (⊑-★ {G = G} g p) (suc n) ≼ w V W =
    star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) = Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 p n ≼ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥

  𝒱payload {A = A} {B = ★} (⊑-★ {G = G} g p) 0 ≽ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱payload {A = A} {B = ★} (⊑-★ {G = G} g p) (suc n) ≽ w V W =
    star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) = Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 p n ≽ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥

  𝒱payload {A = ｀ α} {B = ｀ α} (⊑-｀ {α = α}) n dir w V W =
    seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R n dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱payload {A = ＇ X} {B = ＇ X} ⊑-＇ n dir w V W = Lift (lsuc 0ℓ) ⊥

  -- Intended invariant:
  --   each related pair is value-level, well-typed, and closed with respect
  --   to term variables.
  𝒱 : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱 {A = A} {B = B} p n dir w V W =
    Value V × Value W ×
    ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ V ⦂ A) × (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ W ⦂ B)) ×
    𝒱payload p n dir w V W

  -- This follows PeterLogRel.
  ℰ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  ℰ {A = A} {B = B} p zero dir w Mˡ Mʳ =
    ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
     (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
    Lift (lsuc 0ℓ) ⊤
  
  ℰ {A = A} {B = B} p (suc n) ≼ w Mˡ Mʳ =
    ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
     (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
    ((Σ[ Σˡ′ ∈ Store ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) (Ψ w) Σˡ′ ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      ℰ p n ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ]
      Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      𝒱 p n ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ))
  
  ℰ {A = A} {B = B} p (suc n) ≽ w Mˡ Mʳ =
    ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
     (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
    ((Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      ℰ p n ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) (Ψ w) Σˡ′ ]
      Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      𝒱 p n ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ))

𝒱-left-value :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 p k dir w V W →
  Value V
𝒱-left-value {k = zero} Vrel = proj₁ Vrel
𝒱-left-value {k = suc n} Vrel = proj₁ Vrel

𝒱-right-value :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 p k dir w V W →
  Value W
𝒱-right-value {k = zero} Vrel = proj₁ (proj₂ Vrel)
𝒱-right-value {k = suc n} Vrel = proj₁ (proj₂ Vrel)

------------------------------------------------------------------------
-- Environment interpretation for open terms
------------------------------------------------------------------------

WfTyClosedᵗ : TyCtx → Ty → Set
WfTyClosedᵗ Δ A = Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

record RelSub (Δ : TyCtx) : Set₁ where
  field
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ Δ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ Δ (rightᵗ X)
    precᵗ : (X : TyVar) → leftᵗ X ⊑ rightᵗ X
open RelSub public

∅ρ : RelSub 0
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑-‵

shift-substᵗ : (A : Ty) → substᵗ (λ X → ＇ suc X) A ≡ renameᵗ suc A
shift-substᵗ A = trans (sym (renameᵗ-substᵗ suc (λ X → ＇ X) A))
                        (cong (renameᵗ suc) (substᵗ-id A))

⇑ᵗρ : ∀ {Δ} → RelSub Δ → RelSub (suc Δ)
(⇑ᵗρ ρ .leftᵗ) = extsᵗ (leftᵗ ρ)
(⇑ᵗρ ρ .rightᵗ) = extsᵗ (rightᵗ ρ)
(⇑ᵗρ ρ .left-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .left-closed) (suc X) =
  let Ψ , wfA = left-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .right-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .right-closed) (suc X) =
  let Ψ , wfA = right-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .precᵗ) zero = ⊑-＇
(⇑ᵗρ ρ .precᵗ) (suc X) =
  cast-⊑ (shift-substᵗ (leftᵗ ρ X))
          (shift-substᵗ (rightᵗ ρ X))
          (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) (precᵗ ρ X))

⇑ˢρ : ∀ {Δ} → RelSub Δ → RelSub Δ
(⇑ˢρ ρ .leftᵗ) = liftSubstˢ (leftᵗ ρ)
(⇑ˢρ ρ .rightᵗ) = liftSubstˢ (rightᵗ ρ)
(⇑ˢρ ρ .left-closed) X =
  let Ψ , wfA = left-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .right-closed) X =
  let Ψ , wfA = right-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .precᵗ) X = renameˢ-⊑ suc (precᵗ ρ X)

substᴿ-⊑ : ∀ {Δ} → (ρ : RelSub Δ) → ∀ {A B} → A ⊑ B → substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) B
substᴿ-⊑ ρ ⊑-★★ = ⊑-★★
substᴿ-⊑ ρ (⊑-★ g p) = ⊑-★ (substᵗ-ground (rightᵗ ρ) g) (substᴿ-⊑ ρ p)
substᴿ-⊑ ρ (⊑-＇ {X}) = precᵗ ρ X
substᴿ-⊑ ρ ⊑-｀ = ⊑-｀
substᴿ-⊑ ρ ⊑-‵ = ⊑-‵
substᴿ-⊑ ρ (⊑-⇒ p q) = ⊑-⇒ (substᴿ-⊑ ρ p) (substᴿ-⊑ ρ q)
substᴿ-⊑ ρ (⊑-∀ p) = ⊑-∀ (substᴿ-⊑ (⇑ᵗρ ρ) p)
substᴿ-⊑ ρ (⊑-ν {A = A} {B = B} p) =
  ⊑-ν (cast-⊑ (substᵗ-ν-src (leftᵗ ρ) A)
               (substᵗ-⇑ˢ (rightᵗ ρ) B)
               (substᴿ-⊑ (⇑ˢρ ρ) p))

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

∅γ : RelEnv
(∅γ .leftˣ) x = ` x
(∅γ .rightˣ) x = ` x

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

𝒢 : PCtx → ℕ → Dir → World → RelSub 0 → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) n dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  𝒢 Γ n dir w ρ (⇓γ γ)

_∣_⊨_⊑_⦂_ : PCtx → Dir → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub 0) (γ : RelEnv) →
  𝒢 Γ n dir w ρ γ →
  ℰ (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
    (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))

_⊨_⊑_⦂_ : PCtx → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ⊨ M ⊑ M′ ⦂ p = (Γ ∣ ≼ ⊨ M ⊑ M′ ⦂ p) × (Γ ∣ ≽ ⊨ M ⊑ M′ ⦂ p)

proj⊨ :
  ∀ {Γ M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  Γ ⊨ M ⊑ M′ ⦂ p →
  Γ ∣ dir ⊨ M ⊑ M′ ⦂ p
proj⊨ ≼ rel = proj₁ rel
proj⊨ ≽ rel = proj₂ rel


postulate
  𝒱-monotone : ∀ A B (p : A ⊑ B) k dir w V W
    → 𝒱 p (suc k) dir w V W
    → 𝒱 p k dir w V W

  ℰ-monotone : ∀ A B (p : A ⊑ B) k dir w Mˡ Mʳ
    → ℰ p (suc k) dir w Mˡ Mʳ
    → ℰ p k dir w Mˡ Mʳ

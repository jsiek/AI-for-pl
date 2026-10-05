module proof.DGG.notes.PushTypePremise where

-- File Charter:
--   * A TYPE PREMISE ON THE PUSH of `⊑⟪⟫` (design.md D27), checked as
--     a local copy of HEAD's term relation (TermImprecision.agda):
--     §1 the premise `PushTy` (the push's own index, re-read with
--     each NEWLY pushed name at X⊑X instead of X⊑★); §2 the relation,
--     HEAD's 15 rules verbatim except that `⊑⟪⟫` takes `PushTy`;
--     §3 carry-over `lift` of every HEAD derivation whose pushes meet
--     the premise (`PushOK`); §4 the corpus and K; §5 C4 and C4g:
--     their related pairs are NOT derivable, in any world; §6 the
--     preservation lemma (the premise from the pre-Inst `∀⊑∀`
--     index); §7 the conversion-premise comparison; §8 the hunt.
--     Notes: PushTypePremise.md.  NOT a Def module, not imported by
--     All.agda.  LEFT is the more precise side.  `_⊢_⊑_` (type
--     imprecision), `World`, `Interior`, `WfWorld` and the pending-name
--     side relations are HEAD's, imported unchanged.
--   * NO HIDDEN-NAMES MACHINERY (HiddenNames.agda is a separate
--     question); the base is git HEAD 0da8f5ec.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_; head; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; nu-ty;
         BdyTy; bdy-ty; NuConversionImp; BdyConversionImp;
         Claim; claim-fresh; claim-pop; CastClaim; cc-plain; cc-∀; cc-gen;
         ForallConv; fc-[]; fc-∷; BdyClaim; bc-plain; bc-∀;
         Carried; ca-[]; ca-∷; Push; push; push-none;
         cast-inv; ν-inv; ⟪⟫-inv)
import TermImprecision as HT

private
  variable
    Δ Δ′ Δᵢ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The premise
------------------------------------------------------------------------

-- the mark of center name c set to X⊑X
relaxAt : ImpEnv → ℕ → ImpEnv
relaxAt []      c       = []
relaxAt (m ∷ μ) zero    = X⊑X ∷ μ
relaxAt (m ∷ μ) (suc c) = m ∷ relaxAt μ c

relax : ImpEnv → List ℕ → ImpEnv
relax μ []       = μ
relax μ (c ∷ cs) = relax (relaxAt μ c) cs

-- `PushTy Wᵢ pu A A′ᵢ`: THE TYPE PREMISE of a push.  When the push
-- introduces new pending names (`new ≠ []`), the push's own index
-- `A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ` (the left ∀-type A opened at every pending name,
-- against the boundary's interior type A′ᵢ) must also hold with the
-- NEW names' centers at X⊑X.  The left binder that will pop a new name
-- is then matched with that name as by `∀⊑∀`: this is
-- `∀A ⊑ ∀A′ᵢ` with the pushed name abstracted (§6, `push-ty⇔∀⊑∀`).
-- Carried names keep X⊑★: their own push already checked them.  A push
-- of nothing has no premise.
PushTy : ∀ {Δ Δ′ᵢ Θ′ M π πᵢ} (Wᵢ : World Δ Δ′ᵢ)
  → Push Θ′ M π πᵢ → Ty → Ty → Set
PushTy Wᵢ (push {new = []} _ _ _) A A′ᵢ = ⊤
PushTy Wᵢ (push {π′ = π′} {new = k ∷ ks} _ _ _) A A′ᵢ =
  OpenImp (relax (μʷ Wᵢ) (map (emb (ηᴿʷ Wᵢ)) (k ∷ ks)))
          (map (emb (ηᴿʷ Wᵢ)) (π′ ++ k ∷ ks)) (emb (ηᴸʷ Wᵢ)) A
          (embᴿ Wᵢ A′ᵢ)

-- a relaxed center has mark X⊑X
relaxAt-here : ∀ {μ c m} → relaxAt μ c ∋ˡ c := m → m ≡ X⊑X
relaxAt-here {_ ∷ μ} {zero}  here      = refl
relaxAt-here {_ ∷ μ} {suc c} (there h) = relaxAt-here h

------------------------------------------------------------------------
-- 2. The relation: HEAD's, with `PushTy` on `⊑⟪⟫`
------------------------------------------------------------------------

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ}
    : (W : World Δ Δ′) → CtxImp W → Term → Term
    → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ k ι}
    → Lit k ι
    → (p : ι ⊑ᵂ⟨ W ⟩ ι)
    → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ L L′ M M′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {W : World Δ Δ′} {πₚ γ M M′ μ c B A A′}
      {p : B ⊑ᵂ⟨ record W { πʷ = πₚ } ⟩ A′}
    → CastClaim M c (πʷ W) πₚ
    → record W { πʷ = πₚ } ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {W : World Δ Δ′} {γ M M′ μ′ c′ A B′ A′}
      {p : A ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′
    → Value V
    → Value V′
    → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {γ γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W₁ ⟩ B′}
    → Claim W W₁
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  ν⊑ν : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {Δᵢ Δ′ᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ}
    → let Wᵢ = world {Δᵢ} {Δ′ᵢ} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ [] in
      ∀ {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ
    → BdyClaim M c (πʷ W) (πʷ Wᵢ)
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  -- THE CHANGED RULE: the push carries `PushTy`
  ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → (pu : Push Θ′ M (πʷ W) (πʷ Wᵢ))
    → PushTy Wᵢ pu A A′ᵢ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

infix 3 _∣_⊢_⊑_∶⟨_,_⟩_
_∣_⊢_⊑_∶⟨_,_⟩_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
  → (A A′ : Ty) → A ⊑ᵂ⟨ W ⟩ A′ → Set
W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p = _∣_⊢_⊑_∶_ W γ M M′ {A} {A′} p

------------------------------------------------------------------------
-- 3. Carry-over: a HEAD derivation whose pushes meet the premise
------------------------------------------------------------------------

PushOK : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W HT.∣ γ ⊢ M ⊑ M′ ∶ p → Set
PushOK (HT.x⊑x _)                 = ⊤
PushOK (HT.κ⊑κ _ _)               = ⊤
PushOK (HT.ƛ⊑ƛ _ _ d)             = PushOK d
PushOK (HT.·⊑· d e)               = PushOK d × PushOK e
PushOK (HT.blame⊑ _ _ _)          = ⊤
PushOK (HT.cast⊑cast d _ _ _)     = PushOK d
PushOK (HT.cast⊑ _ d _ _)         = PushOK d
PushOK (HT.⊑cast d _ _)           = PushOK d
PushOK (HT.Λ⊑Λ _ _ _ d _)         = PushOK d
PushOK (HT.Λ⊑ _ _ _ _ _ d _)      = PushOK d
PushOK (HT.ν⊑ν d _ _ _ _ _)       = PushOK d
PushOK (HT.ν⊑ d _ _ _)            = PushOK d
PushOK (HT.⟪⟫⊑⟪⟫ _ _ d _ _ _ _)   = PushOK d
PushOK (HT.⟪⟫⊑ _ _ _ d _ _)       = PushOK d
PushOK (HT.⊑⟪⟫ {Wᵢ = Wᵢ} {A = A} {A′ᵢ = A′ᵢ} _ pu _ d _ _) =
  PushTy Wᵢ pu A A′ᵢ × PushOK d

lift : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → (d : W HT.∣ γ ⊢ M ⊑ M′ ∶ p) → PushOK d → W ∣ γ ⊢ M ⊑ M′ ∶ p
lift (HT.x⊑x x) _                    = x⊑x x
lift (HT.κ⊑κ l p) _                  = κ⊑κ l p
lift (HT.ƛ⊑ƛ a a′ d) ok              = ƛ⊑ƛ a a′ (lift d ok)
lift (HT.·⊑· d e) (ok , ok′)         = ·⊑· (lift d ok) (lift e ok′)
lift (HT.blame⊑ a t p) _             = blame⊑ a t p
lift (HT.cast⊑cast d c c′ q) ok      = cast⊑cast (lift d ok) c c′ q
lift (HT.cast⊑ cc d c q) ok          = cast⊑ cc (lift d ok) c q
lift (HT.⊑cast d c q) ok             = ⊑cast (lift d ok) c q
lift (HT.Λ⊑Λ l v v′ d q) ok          = Λ⊑Λ l v v′ (lift d ok) q
lift (HT.Λ⊑ cl nv o l v d q) ok      = Λ⊑ cl nv o l v (lift d ok) q
lift (HT.ν⊑ν d a n n′ nc q) ok       = ν⊑ν (lift d ok) a n n′ nc q
lift (HT.ν⊑ d a n q) ok              = ν⊑ (lift d ok) a n q
lift (HT.⟪⟫⊑⟪⟫ i wf d b b′ bc q) ok  = ⟪⟫⊑⟪⟫ i wf (lift d ok) b b′ bc q
lift (HT.⟪⟫⊑ i bc wf d b q) ok       = ⟪⟫⊑ i bc wf (lift d ok) b q
lift (HT.⊑⟪⟫ i pu wf d b q) (pt , ok) = ⊑⟪⟫ i pu pt wf (lift d ok) b q

-- and back: forgetting the premise gives HEAD's relation
forget : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → W HT.∣ γ ⊢ M ⊑ M′ ∶ p
forget (x⊑x x)                    = HT.x⊑x x
forget (κ⊑κ l p)                  = HT.κ⊑κ l p
forget (ƛ⊑ƛ a a′ d)               = HT.ƛ⊑ƛ a a′ (forget d)
forget (·⊑· d e)                  = HT.·⊑· (forget d) (forget e)
forget (blame⊑ a t p)             = HT.blame⊑ a t p
forget (cast⊑cast d c c′ q)       = HT.cast⊑cast (forget d) c c′ q
forget (cast⊑ cc d c q)           = HT.cast⊑ cc (forget d) c q
forget (⊑cast d c q)              = HT.⊑cast (forget d) c q
forget (Λ⊑Λ l v v′ d q)           = HT.Λ⊑Λ l v v′ (forget d) q
forget (Λ⊑ cl nv o l v d q)       = HT.Λ⊑ cl nv o l v (forget d) q
forget (ν⊑ν d a n n′ nc q)        = HT.ν⊑ν (forget d) a n n′ nc q
forget (ν⊑ d a n q)               = HT.ν⊑ (forget d) a n q
forget (⟪⟫⊑⟪⟫ i wf d b b′ bc q)   = HT.⟪⟫⊑⟪⟫ i wf (forget d) b b′ bc q
forget (⟪⟫⊑ i bc wf d b q)        = HT.⟪⟫⊑ i bc wf (forget d) b q
forget (⊑⟪⟫ i pu pt wf d b q)     = HT.⊑⟪⟫ i pu wf (forget d) b q

------------------------------------------------------------------------
-- 4. The corpus and K
------------------------------------------------------------------------

module Corpus where
  import examples.TermImprecisionExamples as TIE
  import examples.TermImprecisionRebaseExamples as RB
  import examples.TermImprecisionRegressionExamples as RG
  open import examples.ImprecisionExamples using (L1)
  open import examples.CambridgeExamples
    using (Ch-L; Cg-L; Cg-R; C2-L; C2-R; C12-L; C12-R; instI)

  -- push-free blocks: the premise is vacuous (`PushOK` is all ⊤)
  p1-init   = lift TIE.p1-init _
  p1-tybeta = lift TIE.p1-tybeta _
  p2-tybeta = lift TIE.p2-tybeta _
  p6-init-ν = lift TIE.p6-init-ν _
  p6-tybeta = lift TIE.p6-tybeta _
  ch-b0  = lift RB.ch-b0 _
  ch-b1  = lift RB.ch-b1 _
  cg-b0  = lift RB.cg-b0 _
  c2-b0  = lift RB.c2-b0 _
  c2-b6  = lift RB.c2-b6 _
  c2-b7  = lift RB.c2-b7 _
  c12-b0 = lift RB.c12-b0 _
  c12-b1 = lift RB.c12-b1 _
  c13-b1 = lift RB.c13-b1 _
  c14-b1 = lift RB.c14-b1 _
  lk⊑rk   = lift RG.lk⊑rk _
  lk₁⊑rk₁ = lift RG.lk₁⊑rk₁ _

  -- the blocks that push: each push's premise is `X→X ⊑ X→X` with
  -- the pushed name at X⊑X (the interior type is the left ∀'s body)
  idX⊑idX : ∀ {μ X} → μ ⊢ ` X ⇒ ` X ⊑ ` X ⇒ ` X
  idX⊑idX = ⇒⊑⇒ X⊑X X⊑X

  p3-inst = lift TIE.p3-inst ((idX⊑idX , _) , _)
  cg-x0   = lift RB.cg-x0 ((idX⊑idX , _) , _)
  c2-x0   = lift RB.c2-x0 ((idX⊑idX , _) , _)
  c12-x0  = lift RB.c12-x0 ((idX⊑idX , _) , _)
  VL⊑RF   = lift RG.VL⊑RF (idX⊑idX , _)
  lk₁⊑rk₄ = lift RG.lk₁⊑rk₄ (_ , idX⊑idX , _)
  lk₁⊑rk₃ = lift RG.lk₁⊑rk₃ (_ , idX⊑idX , _)

  ---------------------------------------------------------------------
  -- K's obligations (examples/TermImprecisionRegressionExamples §5),
  -- on the lifted VL⊑RF: unchanged

  open import Reduction using (_⊢_-→*_; done; _then_)
  open import proof.DGG.Evolve
    using (_⟿[_∣_]_; ev-done; ev-R; ev-noneᴸ; ev-noneᴿ; applyˢ; allocs)
  open import Ctx using (wfᴿ-★)

  sim-K :
    ∃[ N′ ] Σ[ r′ ∈ TIE.ΔL ⊢ RG.RK₁ -→* N′ ]
      Σ[ W′ ∈ World TIE.ΔL (applyˢ (allocs r′) TIE.ΔL) ]
        (RG.Wk1 ⟿[ none ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
        × Σ[ q ∈ TIE.∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ RG.VL ⊑ N′ ∶ q)
  sim-K =
    RG.RF , (RG.st₁ then RG.st₂ then RG.st₃ then RG.st₄ then done) , RG.Wk ,
    ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done)))) ,
    RG.Wk-wf , RB.∀id⊑★ RG.Wk , VL⊑RF

  dgg1-K :
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RG.RK -→* V′ ] Value V′
      × Σ[ W′ ∈ World TIE.ΔL (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ TIE.∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ RG.VL ⊑ V′ ∶ q)
  dgg1-K =
    RG.RF , (RG.st₀ then RG.st₁ then RG.st₂ then RG.st₃ then RG.st₄ then done) ,
    RG.vRF , RG.Wk , RB.∀id⊑★ RG.Wk , VL⊑RF

  ---------------------------------------------------------------------
  -- THE CORE, generic over the left store (L3c, L3d use it at W₁): a
  -- left Λ against the right Inst boundary `[+X^β] λx:X.x` (β:=★);
  -- the push's premise is `X→X ⊑ X→X` at X⊑X

  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open TIE using (idX; revX; Θ₀; ΔR; ΔL; int₀; bR-ty; vΛidX; W₁; W₃;
                  five⊑; ℕ⊑★; L1′; R3′; Wi₃-wf)
  open import proof.ImprecisionWorld using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])

  Wo : ∀ {Ξ} → RepRel → World (Ξ ∣ []) ΔR
  Wo ϱ = world [] []↪ []↪ ϱ [] []

  IntRo : ∀ {Ξ ϱ m}
    → Interior (Wo {Ξ} ϱ) [] Θ₀ (record (Wo ϱ ⊕ʳ m ^ 0) { πʷ = 0 ∷ [] })
  IntRo = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  core : ∀ {Ξ ϱ} {γ : CtxImp (Wo {Ξ} ϱ)}
    → WfWorld (record (Wo {Ξ} ϱ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] })
    → Wo ϱ ∣ γ ⊢ Λ idX ⊑ idX ⟪ Θ₀ , revX ⟫ ∶ RB.∀id⊑★ (Wo {Ξ} ϱ)
  core {Ξ} {ϱ = ϱ} wf =
    ⊑⟪⟫ IntRo (push ca-[] (refl ∷ []) (inj₂ vΛidX)) idX⊑idX wf
      (Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[]
        (V-simple S-ƛ) (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (⇒⊑⇒ X⊑X X⊑X))
      bR-ty (RB.∀id⊑★ (Wo {Ξ} ϱ))

  Wi₁-wf : WfWorld (record (W₁ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] })
  Wi₁-wf = wf-world (right-only joint[]) agree
    (namedᴸ-≤1 (W₁ ⊕ʳ X⊑★ ^ 0) ≤1-[]) (namedᴿ-≤1 (W₁ ⊕ʳ X⊑★ ^ 0) ≤1-∷[])
    ((0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })) ∷ [])
    ([] ∷ [])
    where
    Wi : World ΔL (reps ΔR ∣ (0 ∷ []))
    Wi = record (W₁ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] }
    agree : ∀ {α β} → Paired Wi α β → Agree Wi α β
    agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  -- L3c (ForallBoundaryRisks §3; the right's Inst boundary duplicated
  -- by Beta, the left instantiates copy 1):
  --   L  (λf:∀X.X→X. (λy:ℕ. f) (f[ℕ] 5)) (ΛX.λx:X.x)
  --   R  (λf:★→★.    (λy:★. f) (f 5))    (ΛX.λx:X.x)⟨inst⟩
  L3c R3c L3c₁ L3c₂ R3c₃ B⟨id⟩ : Term
  L3c = (ƛ TIE.∀X⇒X ∙ ((ƛ `ℕ ∙ ` 1) · ((ν `ℕ · ` 0 ⟨ revX ⟩) · $ 5)))
      · Λ idX
  R3c = (ƛ (★ ⇒ ★) ∙ ((ƛ ★ ∙ ` 1) · (` 0 · ($ 5 ⟨ [] ∣ `ℕ ! ⟩))))
      · (Λ idX ⟨ [] ∣ instI ⟩)
  B⟨id⟩ = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ RB.id★↦ ⟩
  L3c₁ = (ƛ `ℕ ∙ Λ idX) · L1
  L3c₂ = (ƛ `ℕ ∙ Λ idX) · L1′
  R3c₃ = (ƛ ★ ∙ B⟨id⟩) · R3′

  L3c-⊢ : empty ∣ [] ⊢ L3c ⦂ TIE.∀X⇒X
  L3c-⊢ = tc

  R3c-⊢ : empty ∣ [] ⊢ R3c ⦂ (★ ⇒ ★)
  R3c-⊢ = tc

  L3c₁-state : head (drop 1 (evalTerms 20 L3c-⊢)) ≡ just L3c₁
  L3c₁-state = refl

  L3c₂-state : head (drop 2 (evalTerms 20 L3c-⊢)) ≡ just L3c₂
  L3c₂-state = refl

  R3c₃-state : head (drop 3 (evalTerms 25 R3c-⊢)) ≡ just R3c₃
  R3c₃-state = refl

  copy2 : ∀ {Ξ ϱ}
    → WfWorld (record (Wo {Ξ} ϱ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] })
    → Wo ϱ ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ Λ idX ⊑ B⟨id⟩ ∶ RB.∀id⊑★ (Wo {Ξ} ϱ)
  copy2 {Ξ} {ϱ = ϱ} wf = ⊑cast (core wf) RB.id★↦ᴿ-ty (RB.∀id⊑★ (Wo {Ξ} ϱ))

  l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ RB.∀id⊑★ W₃
  l3c-pre = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 Wi₃-wf)) p3-inst

  l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ RB.∀id⊑★ W₁
  l3c-post = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 Wi₁-wf)) ch-b1

  -- L3d (ForallBoundaryFixes §7; both copies instantiated on the left):
  -- the left's second copy meets the right's copy 2 at W₁
  νLₗ-ty : NuTy ΔL `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νLₗ-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔL} {M = ν `ℕ · Λ idX ⟨ revX ⟩})))

  l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  l3d-before =
    ·⊑· (ν⊑ (⊑cast (core Wi₁-wf) RB.id★↦ᴿ-ty (RB.∀id⊑★ W₁))
            ℕ⊑★ νLₗ-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        (lift five⊑ _)

------------------------------------------------------------------------
-- 5. C4 and C4g: NOT derivable with the premise, in any world
------------------------------------------------------------------------

-- 5a. General facts: the left type of `idX` and `Λ idX`, a tag's
-- target, the premise against a `★` codomain, unpaired left-only names

module Facts where
  open import examples.TermImprecisionExamples using (idX)

  lty-var : ∀ {Δ Δ′} {W : World Δ Δ′} {γ x N′ B B′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ ` x ⊑ N′ ∶ p
    → Σ[ e ∈ CtxImpEntry (μʷ W) (ηᴸʷ W) (ηᴿʷ W) ] (γ ∋ʷ x ⦂ e) × (B ≡ tyᴸ e)
  lty-var (x⊑x h) = _ , h , refl
  lty-var (⊑cast d _ _) = lty-var d
  lty-var (⊑⟪⟫ _ _ _ _ d _ _) with lty-var d
  ... | _ , () , _

  lty-idX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ idX ⊑ M′ ∶ p → A ≡ ` 0 ⇒ ` 0
  lty-idX (ƛ⊑ƛ _ _ d) with lty-var d
  ... | _ , Zʷ , eq = cong (` 0 ⇒_) eq
  lty-idX (⊑cast d _ _) = lty-idX d
  lty-idX (⊑⟪⟫ _ _ _ _ d _ _) = lty-idX d

  lty-ΛidX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ Λ idX ⊑ M′ ∶ p → A ≡ `∀ (` 0 ⇒ ` 0)
  lty-ΛidX (Λ⊑Λ _ _ _ d _) = cong `∀ (lty-idX d)
  lty-ΛidX (Λ⊑ _ _ _ _ _ d _) = cong `∀ (lty-idX d)
  lty-ΛidX (⊑cast d _ _) = lty-ΛidX d
  lty-ΛidX (⊑⟪⟫ _ _ _ _ d _ _) = lty-ΛidX d

  -- the right type of a right cast
  rty-cast : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ μ′ c′ A A′}
      {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q → Σ[ B′ ∈ Ty ] CastTy Δ′ μ′ c′ B′ A′
  rty-cast (cast⊑cast _ _ ct′ _) = _ , ct′
  rty-cast (⊑cast _ ct _)        = _ , ct
  rty-cast (cast⊑ _ d _ _)       = rty-cast d
  rty-cast (⟪⟫⊑ _ _ _ d _ _)     = rty-cast d
  rty-cast (Λ⊑ _ _ _ _ _ d _)    = rty-cast d
  rty-cast (ν⊑ d _ _ _)          = rty-cast d
  rty-cast (blame⊑ _ ⊢M′ _) with cast-inv ⊢M′
  ... | _ , _ , ct = _ , ct

  tag-trg : ∀ {Δ μ X B A} → CastTy Δ μ ((` X) !) B A → A ≡ ★
  tag-trg (cast-ty (⊢tag-var _ _ _) _) = refl

  -- THE KILL: `∀X.X→X` opened at a pushed center c that is RELAXED to
  -- X⊑X cannot meet a right codomain ★ (`X ⊑ ★` needs X⊑★); with more
  -- pushed names than ∀s the index is ⊥
  kill : ∀ {μ c cs ρ R}
    → OpenImp (relax (relaxAt μ c) cs) (c ∷ cs) ρ (`∀ (` 0 ⇒ ` 0)) (R ⇒ ★)
    → ⊥
  kill {cs = []} (⇒⊑⇒ _ (X⊑★ h)) with relaxAt-here h
  ... | ()
  kill {cs = _ ∷ _} ()

  -- a left-only (claim-fresh) binder is unpaired
  shiftᴸ-0 : ∀ {ϱ β} → ¬ (shiftᴸ ϱ ∋ᵨ 0 ⇔ β)
  shiftᴸ-0 {(_ , _) ∷ ϱ} (there⇔ h) = shiftᴸ-0 {ϱ} h

  var⊑var : ∀ {μ a b} → μ ⊢ ` a ⊑ ` b → a ≡ b
  var⊑var X⊑X = refl

  NotRel : ∀ {Δ Δ′} → World Δ Δ′ → Term → Term → Set
  NotRel W M M′ = ∀ {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W ∣ γ ⊢ M ⊑ M′ ∶ p)

  open-⇒ : ∀ {μ c cs ρ A B B′} → ¬ OpenImp μ (c ∷ cs) ρ (A ⇒ B) B′
  open-⇒ ()

  -- under a pending name the left `idX` has no index (its type is no ∀)
  pend-idX : ∀ {Δ Δ′} {W : World Δ Δ′} {k ks M′}
    → πʷ W ≡ k ∷ ks → NotRel W idX M′
  pend-idX {W = world _ _ _ _ _ (_ ∷ _)} refl {p = p} d with lty-idX d
  ... | refl = p

  -- the fresh right name 0 of `Θ₀ = +X^β` joins no unpaired left name
  -- (Interior's join-fresh)
  no-join : ∀ {Δ Δ′ Δ′ᵢ α β} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    → Interior W [] (bind 0 0 ∷ []) Wᵢ
    → Δ ∋ᵗ 0 := α → Δ′ᵢ ∋ᵗ 0 := β → ¬ Paired W α β
    → ¬ Joins Wᵢ 0 0
  no-join i l r np j = np (proj₁ (join-fresh i l r (inj₂ refl)) j)

-- 5b. C4 (HiddenNames §5): the initial programs, the run, and the
-- related pair of HEAD, NOT derivable here
--   sources  L: ((ΛX. λx:X. x)         : ★→★) 5 : ℕ
--            R: ((ΛX. λx:X. (x : ★))  : ★→★) 5 : ℕ
--   (∀X.X→X ⋢ ∀X.X→★: the sources are unrelated, `source-unrelated`)

module C4 where
  open Facts
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.TermImprecisionExamples using (idX)
  import examples.TermImprecisionRegressionExamples as RG
  import examples.TermImprecisionRebaseExamples as RB
  import examples.TermImprecisionExamples as TIE

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? instL instR : Coercion
  ℕ?    = `ℕ ？ 0
  instL = instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !))
  instR = instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★)

  F L₀ bodyR RB Rf R₀ R₂ : Term
  F     = Λ idX ⟨ [] ∣ instL ⟩
  L₀    = (F · 5★) ⟨ [] ∣ ℕ? ⟩
  bodyR = ƛ (` 0) ∙ RG.CX-tagY
  RB    = RG.CX-BdY
  Rf    = RB ⟨ [] ∣ RB.id★↦ ⟩
  R₀    = RG.CX-R
  R₂    = (Rf · 5★) ⟨ [] ∣ ℕ? ⟩

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
  L₀-⊢ = tc

  R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
  R₀-⊢ = tc

  -- R₂ is the right's state 2 (after Inst, TyBeta)
  R₂-state : head (drop 2 (evalTerms 30 R₀-⊢)) ≡ just R₂
  R₂-state = refl

  source-unrelated : ∀ {μ} → ¬ (μ ⊢ `∀ (` 0 ⇒ ` 0) ⊑ `∀ (` 0 ⇒ ★))
  source-unrelated (∀⊑∀ (⇒⊑⇒ _ (X⊑★ ())))
  source-unrelated (∀⊑ _ _ ())

  -- the right type of the Inst boundary's interior
  rty-bodyR : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ bodyR ∶ q → A′ ≡ ` 0 ⇒ ★
  rty-bodyR (ƛ⊑ƛ _ _ d) = cong (` 0 ⇒_) (tag-trg (proj₂ (rty-cast d)))
  rty-bodyR (cast⊑ _ d _ _) = rty-bodyR d
  rty-bodyR (Λ⊑ _ _ _ _ _ d _) = rty-bodyR d
  rty-bodyR (ν⊑ d _ _ _) = rty-bodyR d
  rty-bodyR (⟪⟫⊑ _ _ _ d _ _) = rty-bodyR d
  rty-bodyR (blame⊑ _ (⊢ƛ _ ⊢N) _) with cast-inv ⊢N
  ... | _ , _ , ct = cong (` 0 ⇒_) (tag-trg ct)

  -- inside the Inst boundary, no pending name: a fresh left binder
  -- never joins the right's fresh X
  int-Λ : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) bodyR
  int-Λ {W = world _ _ _ _ _ []} refl
    (Λ⊑ claim-fresh _ _ _ _ (ƛ⊑ƛ {pA = pA} _ _ _) _) with var⊑var pA
  ... | ()

  int-F : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F bodyR
  int-F {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = int-Λ refl d

  -- `idX` against the boundary, after a fresh left binder (unpaired)
  idRB : ∀ {Δ₀ Δ′} {W : World (underΛ Δ₀) Δ′}
    → (∀ {β} → ¬ Paired W 0 β) → NotRel W idX RB
  idRB np (⊑⟪⟫ i (push ca-[] [] _) _ _
      (ƛ⊑ƛ {pA = pA} _ (wf-var (_ , r)) _) _ _) =
    no-join i here r np (var⊑var pA)
  idRB np (⊑⟪⟫ i (push ca-[] (_ ∷ _) _) _ _ d _ _) = pend-idX refl d

  idRf : ∀ {Δ₀ Δ′} {W : World (underΛ Δ₀) Δ′}
    → (∀ {β} → ¬ Paired W 0 β) → NotRel W idX Rf
  idRf np (⊑cast d _ _) = idRB np d

  -- `Λ idX` against the boundary: THE PUSH, killed by its premise
  ΛRB : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) RB
  ΛRB {W = world _ _ _ ϱᵍ ϱˡ []} refl (Λ⊑ claim-fresh _ _ _ _ d _) =
    idRB (λ { (inj₁ h) → shiftᴸ-0 {ϱᵍ} h ; (inj₂ h) → shiftᴸ-0 {ϱˡ} h }) d
  ΛRB {W = world _ _ _ _ _ []} refl (⊑⟪⟫ i (push ca-[] [] _) _ _ d _ _) =
    int-Λ refl d
  ΛRB {W = world _ _ _ _ _ []} refl
    (⊑⟪⟫ {Wᵢ = Wᵢ} i (push {new = _ ∷ ks} ca-[] (_ ∷ _) _) pt _ d _ _)
    with lty-ΛidX d | rty-bodyR d
  ... | refl | refl = kill {cs = map (emb (ηᴿʷ Wᵢ)) ks} pt

  ΛRf : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) Rf
  ΛRf {W = world _ _ _ ϱᵍ ϱˡ []} refl (Λ⊑ claim-fresh _ _ _ _ d _) =
    idRf (λ { (inj₁ h) → shiftᴸ-0 {ϱᵍ} h ; (inj₂ h) → shiftᴸ-0 {ϱˡ} h }) d
  ΛRf {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = ΛRB refl d

  FRB : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F RB
  FRB {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = ΛRB refl d
  FRB {W = world _ _ _ _ _ []} refl (⊑⟪⟫ i (push ca-[] [] _) _ _ d _ _) =
    int-F refl d
  FRB {W = world _ _ _ _ _ []} refl
    (⊑⟪⟫ i (push ca-[] (_ ∷ _) (inj₂ (V-simple (S-cast _ ())))) _ _ _ _ _)

  fn : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F Rf
  fn {W = world _ _ _ _ _ []} refl (cast⊑cast d _ _ _) = ΛRB refl d
  fn {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = ΛRf refl d
  fn {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = FRB refl d

  app : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W (F · 5★) (Rf · 5★)
  app (·⊑· d _) = fn refl d

  -- THE RESULT: C4's related pair of HEAD is not derivable, in any
  -- world, at any index, in any term context
  c4-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W L₀ R₂
  c4-unrelated (cast⊑cast d _ _ _) = app d
  c4-unrelated (cast⊑ cc-plain (⊑cast d _ _) _ _) = app d
  c4-unrelated (⊑cast (cast⊑ cc-plain d _ _) _ _) = app d

  -- the initial pair is unrelated too (a HEAD fact: R₀ has no right
  -- boundary, so no push; Λ⊑Λ fixes X⊑X and `x ⊑ x⟨X!⟩` needs X⊑★)
  FR : Term
  FR = Λ bodyR ⟨ [] ∣ instR ⟩

  i-ΛΛ : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) (Λ bodyR)
  i-ΛΛ {W = world _ _ _ _ _ []} refl
    (Λ⊑Λ _ _ _ (ƛ⊑ƛ _ _ (⊑cast (x⊑x Zʷ) (cast-ty (⊢tag-var _ _ _) _)
      (X⊑★ ()))) _)
  i-ΛΛ {W = world _ _ _ _ _ []} refl (Λ⊑ claim-fresh _ _ _ _ () _)

  i-ΛFR : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) FR
  i-ΛFR {W = world _ _ _ _ _ []} refl (Λ⊑ claim-fresh _ _ _ _ (⊑cast () _ _) _)
  i-ΛFR {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = i-ΛΛ refl d

  i-fn : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F FR
  i-fn {W = world _ _ _ _ _ []} refl (cast⊑cast d _ _ _) = i-ΛΛ refl d
  i-fn {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = i-ΛFR refl d
  i-fn {W = world _ _ _ _ _ []} refl (⊑cast (cast⊑ cc-plain d _ _) _ _) =
    i-ΛΛ refl d

  i-app : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W (F · 5★) (FR · 5★)
  i-app (·⊑· d _) = i-fn refl d

  R₀-is : R₀ ≡ (FR · 5★) ⟨ [] ∣ ℕ? ⟩
  R₀-is = refl

  initial-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W L₀ R₀
  initial-unrelated (cast⊑cast d _ _ _) = i-app d
  initial-unrelated (cast⊑ cc-plain (⊑cast d _ _) _ _) = i-app d
  initial-unrelated (⊑cast (cast⊑ cc-plain d _ _) _ _) = i-app d

  -- and HEAD relates (L₀, R₂) (HiddenNames `C4InHEAD.C4-HEAD`, copied
  -- here): its push premise is exactly what fails
  C4-HEAD-push-fails :
    ¬ PushTy {Θ′ = TIE.Θ₀} {M = Λ idX} {π = []}
        (record (TIE.W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] })
        (push {new = 0 ∷ []} ca-[] (refl ∷ []) (inj₂ TIE.vΛidX))
        (`∀ (` 0 ⇒ ` 0)) (` 0 ⇒ ★)
  C4-HEAD-push-fails (⇒⊑⇒ _ (X⊑★ ()))

-- 5c. A walk generic in the Inst boundary's interior Mi (any interior
-- at type `X → ★` whose right context names X): the pair
--   L₀ ⊑ ((Mi ⟪ +X^β , cB ⟫ ⟨id(★) → id(★)⟩) 5⟨ℕ!⟩)⟨ℕ?⟩
-- is not derivable.  C4g instantiates it; C4 too (a cross-check of
-- §5b).

module Walk (Mi : Term) (cB : Conv)
    (rty : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → W ∣ γ ⊢ M ⊑ Mi ∶ q → (A′ ≡ ` 0 ⇒ ★) × (Δ′ ∋tv 0)) where
  open Facts
  open C4 using (5★; ℕ?; instL; F; L₀)
  open import examples.TermImprecisionExamples using (idX; Θ₀)
  import examples.TermImprecisionRebaseExamples as RB

  RBx Rfx R2x : Term
  RBx = Mi ⟪ Θ₀ , cB ⟫
  Rfx = RBx ⟨ [] ∣ RB.id★↦ ⟩
  R2x = (Rfx · 5★) ⟨ [] ∣ ℕ? ⟩

  -- the left type of the left Inst cast F
  lty-cast : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ μ c A A′}
      {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q → Σ[ B ∈ Ty ] CastTy Δ μ c B A
  lty-cast (cast⊑cast _ ct _ _)  = _ , ct
  lty-cast (cast⊑ _ _ ct _)      = _ , ct
  lty-cast (⊑cast d _ _)         = lty-cast d
  lty-cast (⊑⟪⟫ _ _ _ _ d _ _)   = lty-cast d

  instL-body : ∀ {Δ μ S T}
    → Δ ∣ μ ⊢ᵖ ((` 0) ？ 0) ↦ᵖ ((` 0) !) ∶ S ⟹ T → T ≡ ★ ⇒ ★
  instL-body (⊢fun (⊢check-var _ _ _) (⊢tag-var _ _ _)) = refl

  ⇑-★⇒★ : ∀ {B} → ⇑ᵗ B ≡ ★ ⇒ ★ → B ≡ ★ ⇒ ★
  ⇑-★⇒★ {★ ⇒ ★} refl = refl
  ⇑-★⇒★ {` _ ⇒ _} ()
  ⇑-★⇒★ {★ ⇒ ` _} ()

  lty-F : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ F ⊑ M′ ∶ q → A ≡ ★ ⇒ ★
  lty-F d with lty-cast d
  ... | _ , cast-ty (⊢inst ⊢p _ _ _ _) _ = ⇑-★⇒★ (instL-body ⊢p)

  noΛ⇒ : ∀ {μ c} → ¬ (μ ⊢ `∀ (` 0 ⇒ ` 0) ⊑ ` c ⇒ ★)
  noΛ⇒ (∀⊑ _ _ (⇒⊑⇒ p _)) with var⊑var p
  ... | ()

  dom-join : ∀ {μ a b} → μ ⊢ ` a ⇒ ` a ⊑ ` b ⇒ ★ → a ≡ b
  dom-join (⇒⊑⇒ p _) = var⊑var p

  -- inside the Inst boundary with no pending name
  int-Λ : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) Mi
  int-Λ {W = world _ _ _ _ _ []} refl {p = p} d
    with lty-ΛidX d | proj₁ (rty d)
  ... | refl | refl = noΛ⇒ p

  int-F : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F Mi
  int-F {W = world _ _ _ _ _ []} refl {p = p} d with lty-F d | proj₁ (rty d)
  ... | refl | refl with p
  ... | ⇒⊑⇒ () _

  idRB : ∀ {Δ₀ Δ′} {W : World (underΛ Δ₀) Δ′}
    → (∀ {β} → ¬ Paired W 0 β) → NotRel W idX RBx
  idRB np (⊑⟪⟫ {r = r} i (push ca-[] [] _) _ _ d _ _)
    with lty-idX d | rty d
  ... | refl | refl , (_ , rr) = no-join i here rr np (dom-join r)
  idRB np (⊑⟪⟫ i (push ca-[] (_ ∷ _) _) _ _ d _ _) = pend-idX refl d
  idRB np (⊑⟪⟫ i (push (ca-∷ _ _) _ _) _ _ d _ _) = pend-idX refl d

  idRf : ∀ {Δ₀ Δ′} {W : World (underΛ Δ₀) Δ′}
    → (∀ {β} → ¬ Paired W 0 β) → NotRel W idX Rfx
  idRf np (⊑cast d _ _) = idRB np d

  -- THE PUSH of `Λ idX`, killed by its premise
  ΛRB : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) RBx
  ΛRB {W = world _ _ _ ϱᵍ ϱˡ []} refl (Λ⊑ claim-fresh _ _ _ _ d _) =
    idRB (λ { (inj₁ h) → shiftᴸ-0 {ϱᵍ} h ; (inj₂ h) → shiftᴸ-0 {ϱˡ} h }) d
  ΛRB {W = world _ _ _ _ _ []} refl
    (⊑⟪⟫ i (push ca-[] [] _) _ _ d _ _) =
    int-Λ refl d
  ΛRB {W = world _ _ _ _ _ []} refl
    (⊑⟪⟫ {Wᵢ = Wᵢ} i (push {new = _ ∷ ks} ca-[] (_ ∷ _) _) pt _ d _ _)
    with lty-ΛidX d | proj₁ (rty d)
  ... | refl | refl = kill {cs = map (emb (ηᴿʷ Wᵢ)) ks} pt

  ΛRf : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) Rfx
  ΛRf {W = world _ _ _ ϱᵍ ϱˡ []} refl (Λ⊑ claim-fresh _ _ _ _ d _) =
    idRf (λ { (inj₁ h) → shiftᴸ-0 {ϱᵍ} h ; (inj₂ h) → shiftᴸ-0 {ϱˡ} h }) d
  ΛRf {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = ΛRB refl d

  FRB : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F RBx
  FRB {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = ΛRB refl d
  FRB {W = world _ _ _ _ _ []} refl
    (⊑⟪⟫ i (push ca-[] [] _) _ _ d _ _) =
    int-F refl d
  FRB {W = world _ _ _ _ _ []} refl
    (⊑⟪⟫ i (push ca-[] (_ ∷ _) (inj₂ (V-simple (S-cast _ ())))) _ _ _ _ _)

  fn : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F Rfx
  fn {W = world _ _ _ _ _ []} refl (cast⊑cast d _ _ _) = ΛRB refl d
  fn {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = ΛRf refl d
  fn {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = FRB refl d

  app : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W (F · 5★) (Rfx · 5★)
  app (·⊑· d _) = fn refl d

  unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W L₀ R2x
  unrelated (cast⊑cast d _ _ _) = app d
  unrelated (cast⊑ cc-plain (⊑cast d _ _) _ _) = app d
  unrelated (⊑cast (cast⊑ cc-plain d _ _) _ _) = app d

-- 5d. C4g (HiddenNames §19): a gen-built right value
--   sources  L: ((ΛX. λx:X. x)                       : ★→★) 5 : ℕ
--            R: (((λx:★. x) : ∀X. X→★ by gen) : ★→★) 5 : ℕ
--   (the right's gen cast `gen X.(X! → id(★))` gives ∀X.X→★; again
--   ∀X.X→X ⋢ ∀X.X→★)

module C4g where
  open Facts
  open C4 using (5★; ℕ?; instR; F; L₀; L₀-⊢; source-unrelated)
  open import examples.TypeCheck using (tc)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import examples.TermImprecisionExamples using (idX; Θ₀)
  import examples.TermImprecisionRebaseExamples as RB

  genE-body genE : Coercion
  genE-body = ((` 0) !) ↦ᵖ idᵖ ★
  genE      = genᵖ genE-body

  cE : Conv
  cE = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))

  Gv Gi R0g : Term
  Gv  = I★ ⟨ [] ∣ genE ⟩
  Gi  = RB.I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩
  R0g = ((Gv ⟨ [] ∣ instR ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  R0g-⊢ : empty ∣ [] ⊢ R0g ⦂ `ℕ
  R0g-⊢ = tc

  rty-Gi : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ Gi ∶ q → (A′ ≡ ` 0 ⇒ ★) × (Δ′ ∋tv 0)
  rty-Gi d with rty-cast d
  ... | _ , cast-ty (⊢fun (⊢tag-var tv _ _) (⊢id _ _)) _ = refl , tv

  open Walk Gi cE rty-Gi public
    using (R2x; unrelated; lty-F; noΛ⇒)

  -- R2x is the right's state 2 (after Inst, TyBeta)
  R2g-state : head (drop 2 (evalTerms 30 R0g-⊢)) ≡ just R2x
  R2g-state = refl

  -- THE RESULT for C4g
  c4g-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W L₀ R2x
  c4g-unrelated = unrelated

  -- the initial pair is unrelated (index facts only)
  rty-Gv : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ Gv ∶ q → A′ ≡ `∀ (` 0 ⇒ ★)
  rty-Gv d with rty-cast d
  ... | _ , cast-ty (⊢gen ⊢p _ _ _ _ _) _ = cong `∀ (body-trg ⊢p)
    where
    body-trg : ∀ {Δ μ S T} → Δ ∣ μ ⊢ᵖ genE-body ∶ S ⟹ T → T ≡ ` 0 ⇒ ★
    body-trg (⊢fun (⊢tag-var _ _ _) (⊢id _ _)) = refl

  g-ΛGv : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ idX) Gv
  g-ΛGv {W = world _ _ _ _ _ []} refl {p = p} d with lty-ΛidX d | rty-Gv d
  ... | refl | refl = source-unrelated p

  g-idGv : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W idX Gv
  g-idGv {W = world _ _ _ _ _ []} refl {p = p} d with lty-idX d | rty-Gv d
  ... | refl | refl with p
  ... | ()

  g-FGv : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W F Gv
  g-FGv {W = world _ _ _ _ _ []} refl {p = p} d with lty-F d | rty-Gv d
  ... | refl | refl with p
  ... | ()

  g-idGvI : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ []
    → NotRel W idX (Gv ⟨ [] ∣ instR ⟩)
  g-idGvI {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = g-idGv refl d

  g-ΛGvI : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ []
    → NotRel W (Λ idX) (Gv ⟨ [] ∣ instR ⟩)
  g-ΛGvI {W = world _ _ _ _ _ []} refl (Λ⊑ claim-fresh _ _ _ _ d _) =
    g-idGvI refl d
  g-ΛGvI {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = g-ΛGv refl d

  g-fn : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ []
    → NotRel W F (Gv ⟨ [] ∣ instR ⟩)
  g-fn {W = world _ _ _ _ _ []} refl (cast⊑cast d _ _ _) = g-ΛGv refl d
  g-fn {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = g-ΛGvI refl d
  g-fn {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = g-FGv refl d

  g-app : ∀ {Δ Δ′} {W : World Δ Δ′}
    → NotRel W (F · 5★) ((Gv ⟨ [] ∣ instR ⟩) · 5★)
  g-app (·⊑· d _) = g-fn refl d

  initial-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W L₀ R0g
  initial-unrelated (cast⊑cast d _ _ _) = g-app d
  initial-unrelated (cast⊑ cc-plain (⊑cast d _ _) _ _) = g-app d
  initial-unrelated (⊑cast (cast⊑ cc-plain d _ _) _ _) = g-app d

-- the cross-check: §5b's C4 through the generic walk
module C4′ where
  open Facts
  open C4 using (bodyR; R₂; L₀)
  import examples.TermImprecisionRegressionExamples as RG

  rty-bodyR′ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ bodyR ∶ q → (A′ ≡ ` 0 ⇒ ★) × (Δ′ ∋tv 0)
  rty-bodyR′ (ƛ⊑ƛ _ (wf-var tv) d) =
    cong (` 0 ⇒_) (tag-trg (proj₂ (rty-cast d))) , tv
  rty-bodyR′ (cast⊑ _ d _ _) = rty-bodyR′ d
  rty-bodyR′ (Λ⊑ _ _ _ _ _ d _) = rty-bodyR′ d
  rty-bodyR′ (ν⊑ d _ _ _) = rty-bodyR′ d
  rty-bodyR′ (⟪⟫⊑ _ _ _ d _ _) = rty-bodyR′ d
  rty-bodyR′ (blame⊑ _ (⊢ƛ (wf-var tv) ⊢N) _) with cast-inv ⊢N
  ... | _ , _ , ct = cong (` 0 ⇒_) (tag-trg ct) , tv

  open Walk bodyR (reveal 0 (` 0 ⇒ ★)) rty-bodyR′ using (R2x; unrelated)

  same-pair : R2x ≡ R₂
  same-pair = refl

  c4-unrelated′ : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W L₀ R₂
  c4-unrelated′ = unrelated

-- 5e. The runs: the right blames, the left never does (determinism
-- along the evalTerms trace; helpers copied from HiddenNames §11,
-- relation-free)

module Runs where
  open import examples.Eval
    using (eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed;
           no-redex; out-of-fuel; evalTerms; traceTerms; step; StepResult)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  import Data.List.Relation.Unary.All as All

  justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
    → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
  justStep {r = r} _ = proj₂ (proj₂ r)

  EndsVB : ∀ {Δ A M} → Trace Δ A M → Set
  EndsVB (stop (value _))   = ⊤
  EndsVB (stop (blamed _))  = ⊤
  EndsVB (stop no-redex)    = ⊥
  EndsVB (stop out-of-fuel) = ⊥
  EndsVB (illtyped _)       = ⊥
  EndsVB (_ ◅⟨ _ ⟩ tr)      = EndsVB tr

  in-trace : ∀ {Δ A M N} (tr : Trace Δ A M) → Δ ∣ [] ⊢ M ⦂ A
    → EndsVB tr → Δ ⊢ M -→* N → N ∈ traceTerms tr
  in-trace (stop f) ⊢M e done = here refl
  in-trace (illtyped _) ⊢M e done = here refl
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e done = here refl
  in-trace (stop (value v)) ⊢M e (st then r) =
    ⊥-elim (proj₁ irreducible v st)
  in-trace (stop (blamed refl)) ⊢M e (st then r) =
    ⊥-elim (proj₂ irreducible st)
  in-trace (stop no-redex) ⊢M () (st then r)
  in-trace (stop out-of-fuel) ⊢M () (st then r)
  in-trace (illtyped _) ⊢M () (st then r)
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) with det ⊢M st st′
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) | refl , refl =
    there (in-trace tr ⊢M′ e r)

  all-reach : ∀ {Δ A M N} {P : Term → Set} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
    → EndsVB (eval k M ⊢M) → All P (evalTerms k ⊢M)
    → Δ ⊢ M -→* N → P N
  all-reach k ⊢M e a r = All.lookup a (in-trace (eval k _ ⊢M) ⊢M e r)

  NotBlame : Term → Set
  NotBlame N = ∀ {ℓ} → N ≡ blame ℓ → ⊥

  last : List Term → Term
  last []           = $ 0
  last (x ∷ [])     = x
  last (x ∷ y ∷ xs) = last (y ∷ xs)

------------------------------------------------------------------------
-- 12. C1 = the SimBackBlame counterexample L₆ ⊑ R₇ (PendingOpenings
-- §5d; SidedMarks/ModeCondition `Cex`): NOT DERIVABLE, in any world

module C4Runs where
  open Runs
  open import examples.TypeCheck using (tc)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open C4 using (L₀; L₀-⊢; R₂)
  open import examples.TermImprecisionExamples using (ΔR)
  open C4g using (R2x)

  R₂-⊢ : ΔR ∣ [] ⊢ R₂ ⦂ `ℕ
  R₂-⊢ = tc

  R₂-blames : last (evalTerms 20 R₂-⊢) ≡ blame 0
  R₂-blames = refl

  R2g-⊢ : ΔR ∣ [] ⊢ R2x ⦂ `ℕ
  R2g-⊢ = tc

  R2g-blames : last (evalTerms 30 R2g-⊢) ≡ blame 0
  R2g-blames = refl

  L₀-never-blames : ∀ {ℓ} → ¬ (empty ⊢ L₀ -→* blame ℓ)
  L₀-never-blames r = all-reach {P = NotBlame} 30 L₀-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

------------------------------------------------------------------------
-- 6. Preservation: the premise of the push that the right's
-- Inst + TyBeta creates IS the body of the pre-Inst `∀⊑∀` index
------------------------------------------------------------------------

module Preservation where
  open import proof.TypeSubst using (rename-cong)

  ⊳≗ext : ∀ {ns Ω m} (η : ns ↪ Ω) (X : ℕ)
    → (0 ⊳ emb (skip {m = m} η)) X ≡ extᵗ (emb η) X
  ⊳≗ext η zero    = refl
  ⊳≗ext η (suc X) = refl

  keep≗ext : ∀ {ns Ω α m} (η : ns ↪ Ω) (X : ℕ)
    → emb (keep {α = α} {m = m} η) X ≡ extᵗ (emb η) X
  keep≗ext η zero    = refl
  keep≗ext η (suc X) = refl

  -- The interior world of the right's Inst boundary `+X^β` (a single
  -- bind entry, no older pending name): X right-only at X⊑★, pushed.
  -- The push's premise is EXACTLY `∀⊑∀`'s premise for `∀A ⊑ ∀A′`
  -- at the exterior world (A′ is the interior type: the right's body
  -- type, its bound variable now the boundary's name 0).
  push-ty⇔∀⊑∀ : ∀ {Δ Δ′ μ ϱᵍ ϱˡ β Θ′ M A A′}
      {η : names Δ ↪ μ} {η′ : names Δ′ ↪ μ}
      {fr : Fresh Θ′ 0} {v : Value M}
    → let W  = world {Δ} {Δ′} μ η η′ ϱᵍ ϱˡ []
          Wᵢ = record (W ⊕ʳ X⊑★ ^ β) { πʷ = 0 ∷ [] }
          pu = push {Θ′ = Θ′} {M = M} {π = []} {new = 0 ∷ []} ca-[] (fr ∷ []) (inj₂ v)
          ∀⊑∀-premise = extᵐ μ ⊢ renameᵗ (extᵗ (emb η)) A
                                ⊑ renameᵗ (extᵗ (emb η′)) A′
      in (PushTy Wᵢ pu (`∀ A) A′ → ∀⊑∀-premise)
       × (∀⊑∀-premise → PushTy Wᵢ pu (`∀ A) A′)
  push-ty⇔∀⊑∀ {μ = μ} {β = β} {Θ′ = Θ′} {M = M} {A = A} {A′ = A′}
    {η = η} {η′ = η′} =
    (λ p → subst₂ (rename-cong (⊳≗ext {m = X⊑★} η) A)
                  (rename-cong (keep≗ext {α = β} {m = X⊑★} η′) A′) p)
    , (λ p → subst₂ (sym (rename-cong (⊳≗ext {m = X⊑★} η) A))
                    (sym (rename-cong (keep≗ext {α = β} {m = X⊑★} η′) A′)) p)
    where
    subst₂ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′
      → extᵐ μ ⊢ a ⊑ b → extᵐ μ ⊢ a′ ⊑ b′
    subst₂ refl refl p = p

  -- hence, from a pre-Inst index built by `∀⊑∀`, the premise of the
  -- post-Inst push holds
  preserve : ∀ {Δ Δ′ μ ϱᵍ ϱˡ β Θ′ M A A′}
      {η : names Δ ↪ μ} {η′ : names Δ′ ↪ μ}
      {fr : Fresh Θ′ 0} {v : Value M}
    → let W = world {Δ} {Δ′} μ η η′ ϱᵍ ϱˡ [] in
      (p : extᵐ μ ⊢ renameᵗ (extᵗ (emb η)) A ⊑ renameᵗ (extᵗ (emb η′)) A′)
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′) → q ≡ ∀⊑∀ p
    → PushTy (record (W ⊕ʳ X⊑★ ^ β) { πʷ = 0 ∷ [] })
        (push {Θ′ = Θ′} {M = M} {π = []} {new = 0 ∷ []} ca-[] (fr ∷ []) (inj₂ v)) (`∀ A) A′
  preserve {Δ} {Δ′} {μ} {ϱᵍ} {ϱˡ} {β} {Θ′} {M} {A} {A′} {η} {η′}
    {fr} {v} p _ refl =
    proj₂ (push-ty⇔∀⊑∀ {Δ} {Δ′} {μ} {ϱᵍ} {ϱˡ} {β} {Θ′} {M} {A} {A′}
             {η} {η′} {fr} {v}) p

  -- K: the pre-Inst pair lk₁⊑rk₁ sits at `∀id⊑∀id` (∀⊑∀); its body
  -- gives the premise of VL⊑Rarg₃'s push at Θ₀ (WiY★, after the Inst's
  -- allocation: the index reads no rep. var, so it is the same proof)
  import examples.TermImprecisionRegressionExamples as RG
  import examples.TermImprecisionRebaseExamples as RB
  import examples.TermImprecisionExamples as TIE

  k-preserve = preserve {Δ = TIE.ΔL} {Δ′ = RG.ΔRk} {μ = []}
    {ϱᵍ = (0 , 1) ∷ []} {ϱˡ = []} {β = 0} {Θ′ = TIE.Θ₀} {M = RG.VL}
    {A = ` 0 ⇒ ` 0} {A′ = ` 0 ⇒ ` 0} {η = []↪} {η′ = []↪}
    {fr = refl} {v = RG.vVL} (⇒⊑⇒ X⊑X X⊑X) (RB.∀id⊑∀id RG.Wk) refl

  k-is-used : Corpus.lk₁⊑rk₃ ≡ lift RG.lk₁⊑rk₃ (_ , k-preserve , _)
  k-is-used = refl

  -- Cg: the pre-Inst pair cg-b0 meets the right's gen value at
  -- `∀id⊑∀id ∅ʷ` (∀⊑∀); the same body is cg-x0's push premise
  cg-preserve = preserve {Δ = empty} {Δ′ = TIE.ΔR} {μ = []}
    {ϱᵍ = []} {ϱˡ = []} {β = 0} {Θ′ = TIE.Θ₀} {M = Λ TIE.idX}
    {A = ` 0 ⇒ ` 0} {A′ = ` 0 ⇒ ` 0} {η = []↪} {η′ = []↪}
    {fr = refl} {v = TIE.vΛidX} (⇒⊑⇒ X⊑X X⊑X) (RB.∀id⊑∀id TIE.W₃) refl

  cg-is-used : Corpus.cg-x0 ≡ lift RB.cg-x0 ((cg-preserve , _) , _)
  cg-is-used = refl

------------------------------------------------------------------------
-- 7. The alternative CONVERSION premise (compare the left's would-be
-- reveal `−X → +X` with the right boundary's conversion) needs the
-- same X⊑X ingredient: with HEAD's ConvImp and the joined name at
-- X⊑★ it ACCEPTS C4's `−X → id(★)`; at X⊑X it rejects it
------------------------------------------------------------------------

module ConvPremise where
  open import examples.TermImprecisionExamples using (revX; ConvCtx₀; revX⊑revX)
  open C4g using (cE)

  lookup-unique : ∀ {μ : ImpEnv} {i a b} → μ ∋ˡ i := a → μ ∋ˡ i := b → a ≡ b
  lookup-unique here here = refl
  lookup-unique (there h) (there h′) = lookup-unique h h′

  -- the pushed name joined (as after the pop), at the pending mark
  Wc★ : World (ConvCtx₀ ★) (ConvCtx₀ ★)
  Wc★ = world (X⊑★ ∷ []) (keep []↪) (keep []↪) [] [] []

  accepts-C4 : ConvImp Wc★ revX cE
  accepts-C4 =
    conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
      (conv-tail⊑tail (conv-seal⊑seal refl)) (conv-unseal⊑id★ here)))

  -- at X⊑X (the relaxed mark): rejected, in any conversion world
  rejects-C4 : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂}
    → μʷ W ∋ˡ emb (ηᴸʷ W) 0 := X⊑X → ¬ ConvImp W revX cE
  rejects-C4 m (conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ _
      (conv-unseal⊑id★ h)))) with lookup-unique m h
  ... | ()

  -- the corpus pushes (P3, Cg, C2, C12, L3c, L3d, K) all have
  -- `c′ = −X → +X` against a left ∀X.X→X: accepted at any mark
  accepts-corpus : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂} → Joins W 0 0
    → ConvImp W revX revX
  accepts-corpus = revX⊑revX

------------------------------------------------------------------------
-- 8. Hunt: relatedness GAINED through a push from an unrelated start,
-- with no blame difference (H2).  The left keeps `y:X`, the right
-- has `y:★` and tags x; the pre-Inst Λ⊑Λ needs `X ⊑ ★` at X⊑X, the
-- post-Inst pop gives X⊑★.  The interior type X→X passes the premise.
--   sources  L: ((ΛX. λx:X. (λy:X. x) x)        : ★→★) 5 : ℕ
--            R: ((ΛX. λx:X. (λy:★. x) (x : ★))  : ★→★) 5 : ℕ
------------------------------------------------------------------------

module H2 where
  open Facts
  open C4 using (5★; ℕ?; instL)
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.TermImprecisionExamples
    using (revX; Θ₀; ΔR; ΔRᵢ; W₃; int-ro₃; Wi₃-wf)
  import examples.TermImprecisionRebaseExamples as RB
  open Runs

  tagX : Term
  tagX = ` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩

  bodyL bodyR Fh Lh Rh Rh₂ RBh : Term
  bodyL = ƛ (` 0) ∙ ((ƛ (` 0) ∙ ` 1) · ` 0)
  bodyR = ƛ (` 0) ∙ ((ƛ ★ ∙ ` 1) · tagX)
  Fh    = Λ bodyL ⟨ [] ∣ instL ⟩
  Lh    = (Fh · 5★) ⟨ [] ∣ ℕ? ⟩
  Rh    = ((Λ bodyR ⟨ [] ∣ instL ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  RBh   = bodyR ⟪ Θ₀ , revX ⟫
  Rh₂   = ((RBh ⟨ [] ∣ RB.id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  Lh-⊢ : empty ∣ [] ⊢ Lh ⦂ `ℕ
  Lh-⊢ = tc

  Rh-⊢ : empty ∣ [] ⊢ Rh ⦂ `ℕ
  Rh-⊢ = tc

  Rh₂-state : head (drop 2 (evalTerms 30 Rh-⊢)) ≡ just Rh₂
  Rh₂-state = refl

  -- both reach 5
  Lh-5 : last (evalTerms 30 Lh-⊢) ≡ $ 5
  Lh-5 = refl

  Rh-5 : last (evalTerms 30 Rh-⊢) ≡ $ 5
  Rh-5 = refl

  -- the initial pair: unrelated in every world (Λ⊑Λ fixes X⊑X, and
  -- `λy:X ⊑ λy:★` needs X⊑★; the right has no boundary, so no push)
  i-ΛΛ : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ []
    → NotRel W (Λ bodyL) (Λ bodyR)
  i-ΛΛ {W = world _ _ _ _ _ []} refl
    (Λ⊑Λ _ _ _ (ƛ⊑ƛ _ _ (·⊑· (ƛ⊑ƛ {pA = X⊑★ ()} _ _ _) _)) _)
  i-ΛΛ {W = world _ _ _ _ _ []} refl (Λ⊑ claim-fresh _ _ _ _ () _)

  FR : Term
  FR = Λ bodyR ⟨ [] ∣ instL ⟩

  i-ΛFR : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W (Λ bodyL) FR
  i-ΛFR {W = world _ _ _ _ _ []} refl (Λ⊑ claim-fresh _ _ _ _ (⊑cast () _ _) _)
  i-ΛFR {W = world _ _ _ _ _ []} refl (⊑cast d _ _) = i-ΛΛ refl d

  i-fn : ∀ {Δ Δ′} {W : World Δ Δ′} → πʷ W ≡ [] → NotRel W Fh FR
  i-fn {W = world _ _ _ _ _ []} refl (cast⊑cast d _ _ _) = i-ΛΛ refl d
  i-fn {W = world _ _ _ _ _ []} refl (cast⊑ cc-plain d _ _) = i-ΛFR refl d
  i-fn {W = world _ _ _ _ _ []} refl (⊑cast (cast⊑ cc-plain d _ _) _ _) =
    i-ΛΛ refl d

  i-app : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W (Fh · 5★) (FR · 5★)
  i-app (·⊑· d _) = i-fn refl d

  initial-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} → NotRel W Lh Rh
  initial-unrelated (cast⊑cast d _ _ _) = i-app d
  initial-unrelated (cast⊑ cc-plain (⊑cast d _ _) _ _) = i-app d
  initial-unrelated (⊑cast (cast⊑ cc-plain d _ _) _ _) = i-app d

  -- after the right's Inst + TyBeta: RELATED, push premise X→X ⊑ X→X
  bRBh : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bRBh = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = RBh}))))

  tagX-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
  tagX-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  instL-ty : CastTy empty [] instL (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instL-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = Fh})))

  pop-body : record (W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ Λ bodyL ⊑ bodyR
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  pop-body =
    Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (ƛ⊑ƛ {pA = X⊑X} tf tf
        (·⊑· {pA = X⊑★ here}
          (ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑X} tf wf-★ (x⊑x (Sʷ Zʷ)))
          (⊑cast (x⊑x Zʷ) tagX-ty (X⊑★ here))))
      (⇒⊑⇒ X⊑X X⊑X)

  related-after-Inst : W₃ ∣ [] ⊢ Lh ⊑ Rh₂ ∶ ι⊑ι base-ℕ
  related-after-Inst =
    cast⊑cast
      (·⊑·
        (cast⊑cast
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ (V-simple (S-Λ (V-simple S-ƛ)))))
            (⇒⊑⇒ X⊑X X⊑X) Wi₃-wf pop-body bRBh (RB.∀id⊑★ W₃))
          instL-ty (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl)
          (⇒⊑⇒ ★⊑★ ★⊑★))
        (cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
          (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★))
      (cast-ty (⊢check g-ℕ) refl) (cast-ty (⊢check g-ℕ) refl) (ι⊑ι base-ℕ)

-- H1 (argued, with its type-level facts mechanized): TWO right
-- instantiations of a left ∀X.∀Y.X→Y→X value.  The right's second
-- Inst nests its boundary OUTSIDE the first: [+Y^β]([+X^α] …), so the
-- outer push puts Y at the head of the pending list (`Push`: carried
-- names first, then new), and the left's OUTER binder X pops Y.  The
-- premise at the outer push therefore compares the left X with the
-- right Y (and the interior type, the inner boundary's exterior
-- `★ → Y → ★`), and fails; HEAD's relation (no premise) also fails
-- (the bodies then need `Y ⊑ X`).  After the right's Merge the single
-- boundary [+Y^β, +X^α] may push [X, Y] in either order, and the
-- natural one passes.

module H1 where
  K2 : Ty
  K2 = `∀ (`∀ (` 1 ⇒ (` 0 ⇒ ` 1)))

  ΔR2 ΔR2ʸ ΔR2ˣʸ : Ctxᵗ
  ΔR2   = (bindR ★ ∷ bindR ★ ∷ []) ∣ []
  ΔR2ʸ  = (bindR ★ ∷ bindR ★ ∷ []) ∣ (0 ∷ [])
  ΔR2ˣʸ = (bindR ★ ∷ bindR ★ ∷ []) ∣ (0 ∷ 1 ∷ [])

  KL : Term
  KL = Λ (Λ (ƛ (` 1) ∙ (ƛ (` 0) ∙ ` 1)))

  vKL : Value KL
  vKL = V-simple (S-Λ (V-simple (S-Λ (V-simple S-ƛ))))

  W0 : World empty ΔR2
  W0 = world [] []↪ []↪ [] [] []

  -- the outer `+Y^β` alone (before the Merge): Y pushed at the head
  Wʸ : World empty ΔR2ʸ
  Wʸ = world (X⊑★ ∷ []) (skip []↪) (keep []↪) [] [] (0 ∷ [])

  outer-push-fails :
    ¬ PushTy {Θ′ = bind 0 0 ∷ []} {M = KL} {π = []} Wʸ
        (push {new = 0 ∷ []} ca-[] (refl ∷ []) (inj₂ vKL))
        K2 (★ ⇒ (` 0 ⇒ ★))
  outer-push-fails (∀⊑ _ _ (⇒⊑⇒ (X⊑★ (there ())) _))

  -- after the Merge, inside [+Y^β, +X^α] (Y at 0, X at 1): push X
  -- first (the natural order) — passes; Y first — fails
  Wˣʸ : List ℕ → World empty ΔR2ˣʸ
  Wˣʸ π = world (X⊑★ ∷ X⊑★ ∷ []) (skip (skip []↪)) (keep (keep []↪))
            [] [] π

  Θm : Boundary
  Θm = bind 1 1 ∷ bind 0 0 ∷ []

  merged-natural :
    PushTy {Θ′ = Θm} {M = KL} {π = []} (Wˣʸ (1 ∷ 0 ∷ []))
      (push {new = 1 ∷ 0 ∷ []} ca-[] (refl ∷ refl ∷ []) (inj₂ vKL))
      K2 (` 1 ⇒ (` 0 ⇒ ` 1))
  merged-natural = ⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)

  merged-crossed-fails :
    ¬ PushTy {Θ′ = Θm} {M = KL} {π = []} (Wˣʸ (0 ∷ 1 ∷ []))
        (push {new = 0 ∷ 1 ∷ []} ca-[] (refl ∷ refl ∷ []) (inj₂ vKL))
        K2 (` 1 ⇒ (` 0 ⇒ ` 1))
  merged-crossed-fails (⇒⊑⇒ () _)

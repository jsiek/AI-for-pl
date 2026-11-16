module proof.PrecisionProps where

-- File Charter:
--   * Facts about type precision derivations n ⊢ p ⦂ A ⊑ B of PolyCν
--     (thesis Sec. 10.6.1): renaming (weakening), well-formedness of both
--     sides, the reflexive and dynamic derivations idᵖ and dynᵖ,
--     uniqueness (Lemma 219), transitivity (Lemma 221), and the meet
--     derivations meetL/meetR of Compile.agda with the greatest lower
--     bound property (Lemma 222).
--   * Also the corresponding renaming lemmas for WfTy.
--   * Consumed by proof/CompileTyping.agda and proof/CompilePrecision.agda.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Types
open import GradualTerms using (Meet; m★L; m★R; m‵; m𝔹; m⇒; m∀)
open import Compile using (meetL; meetR)

------------------------------------------------------------------------
-- Renamings that preserve well-formedness
------------------------------------------------------------------------

WfRen : NSubst → ℕ → ℕ → Set
WfRen σ n m = ∀ {i} → i < n → WfName m (σ i)

⇑ₙ-wf : ∀ {m α} → WfName m α → WfName (suc m) (⇑ₙ α)
⇑ₙ-wf {α = tvar i} i<m = s≤s i<m
⇑ₙ-wf {α = tseal s} tt = tt

extₙ-wf : ∀ {σ n m} → WfRen σ n m → WfRen (extₙ σ) (suc n) (suc m)
extₙ-wf σwf {zero} i<n = s≤s z≤n
extₙ-wf σwf {suc i} (s≤s i<n) = ⇑ₙ-wf (σwf i<n)

↑ₙ-wf : ∀ {n} → WfRen ↑ₙ n (suc n)
↑ₙ-wf i<n = s≤s i<n

substₙ-wf : ∀ {σ n m} α → WfRen σ n m → WfName n α → WfName m (substₙ σ α)
substₙ-wf (tvar i) σwf i<n = σwf i<n
substₙ-wf (tseal s) σwf tt = tt

substG-wf : ∀ {σ n m G} → WfRen σ n m → WfGround n G
  → WfGround m (substG σ G)
substG-wf {G = G‵ α} σwf (wfG‵ wfα) = wfG‵ (substₙ-wf α σwf wfα)
substG-wf σwf wfG𝔹 = wfG𝔹
substG-wf σwf wfG⇒ = wfG⇒
substG-wf σwf wfG∀ = wfG∀

substᵗ-wf : ∀ {σ n m A} → WfRen σ n m → WfTy n A → WfTy m (substᵗ σ A)
substᵗ-wf {A = ‵ α} σwf (wf‵ wfα) = wf‵ (substₙ-wf α σwf wfα)
substᵗ-wf σwf wf𝔹 = wf𝔹
substᵗ-wf σwf wf★ = wf★
substᵗ-wf σwf (wf⇒ wfA wfB) = wf⇒ (substᵗ-wf σwf wfA) (substᵗ-wf σwf wfB)
substᵗ-wf σwf (wf∀ wfA) = wf∀ (substᵗ-wf (extₙ-wf σwf) wfA)

⇑ᵗ-wf : ∀ {n A} → WfTy n A → WfTy (suc n) (⇑ᵗ A)
⇑ᵗ-wf = substᵗ-wf ↑ₙ-wf

------------------------------------------------------------------------
-- Renaming precision derivations
------------------------------------------------------------------------

substᵖ-⊢ : ∀ {σ n m p A B} → WfRen σ n m
  → n ⊢ p ⦂ A ⊑ B
  → m ⊢ substᵖ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
substᵖ-⊢ σwf ⊑★ = ⊑★
substᵖ-⊢ σwf (⊑tag {G = G‵ α} wfG p⊢) =
  ⊑tag (substG-wf σwf wfG) (substᵖ-⊢ σwf p⊢)
substᵖ-⊢ σwf (⊑tag {G = G𝔹} wfG p⊢) = ⊑tag wfG𝔹 (substᵖ-⊢ σwf p⊢)
substᵖ-⊢ σwf (⊑tag {G = G⇒} wfG p⊢) = ⊑tag wfG⇒ (substᵖ-⊢ σwf p⊢)
substᵖ-⊢ σwf (⊑tag {G = G∀} wfG p⊢) = ⊑tag wfG∀ (substᵖ-⊢ σwf p⊢)
substᵖ-⊢ σwf (⊑‵ {α = α} wfα) = ⊑‵ (substₙ-wf α σwf wfα)
substᵖ-⊢ σwf ⊑𝔹 = ⊑𝔹
substᵖ-⊢ σwf (⊑⇒ p⊢ q⊢) = ⊑⇒ (substᵖ-⊢ σwf p⊢) (substᵖ-⊢ σwf q⊢)
substᵖ-⊢ σwf (⊑∀ p⊢) = ⊑∀ (substᵖ-⊢ (extₙ-wf σwf) p⊢)

⇑ᵖ-⊢ : ∀ {n p A B} → n ⊢ p ⦂ A ⊑ B
  → suc n ⊢ substᵖ ↑ₙ p ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
⇑ᵖ-⊢ = substᵖ-⊢ ↑ₙ-wf

------------------------------------------------------------------------
-- Both sides of a precision derivation are well formed
------------------------------------------------------------------------

groundTy-wf : ∀ {n G} → WfGround n G → WfTy n (groundTy G)
groundTy-wf (wfG‵ wfα) = wf‵ wfα
groundTy-wf wfG𝔹 = wf𝔹
groundTy-wf wfG⇒ = wf⇒ wf★ wf★
groundTy-wf wfG∀ = wf∀ wf★

⊑-wfL : ∀ {n p A B} → n ⊢ p ⦂ A ⊑ B → WfTy n A
⊑-wfL ⊑★ = wf★
⊑-wfL (⊑tag wfG p⊢) = ⊑-wfL p⊢
⊑-wfL (⊑‵ wfα) = wf‵ wfα
⊑-wfL ⊑𝔹 = wf𝔹
⊑-wfL (⊑⇒ p⊢ q⊢) = wf⇒ (⊑-wfL p⊢) (⊑-wfL q⊢)
⊑-wfL (⊑∀ p⊢) = wf∀ (⊑-wfL p⊢)

⊑-wfR : ∀ {n p A B} → n ⊢ p ⦂ A ⊑ B → WfTy n B
⊑-wfR ⊑★ = wf★
⊑-wfR (⊑tag wfG p⊢) = wf★
⊑-wfR (⊑‵ wfα) = wf‵ wfα
⊑-wfR ⊑𝔹 = wf𝔹
⊑-wfR (⊑⇒ p⊢ q⊢) = wf⇒ (⊑-wfR p⊢) (⊑-wfR q⊢)
⊑-wfR (⊑∀ p⊢) = wf∀ (⊑-wfR p⊢)

------------------------------------------------------------------------
-- Reflexivity (Lemma 220) and the dynamic derivation A? : A ⊑ ?
------------------------------------------------------------------------

idᵖ-⊢ : ∀ {n A} → WfTy n A → n ⊢ idᵖ A ⦂ A ⊑ A
idᵖ-⊢ (wf‵ wfα) = ⊑‵ wfα
idᵖ-⊢ wf𝔹 = ⊑𝔹
idᵖ-⊢ wf★ = ⊑★
idᵖ-⊢ (wf⇒ wfA wfB) = ⊑⇒ (idᵖ-⊢ wfA) (idᵖ-⊢ wfB)
idᵖ-⊢ (wf∀ wfA) = ⊑∀ (idᵖ-⊢ wfA)

dynᵖ-⊢ : ∀ {n A} → WfTy n A → n ⊢ dynᵖ A ⦂ A ⊑ ★
dynᵖ-⊢ (wf‵ wfα) = ⊑tag (wfG‵ wfα) (⊑‵ wfα)
dynᵖ-⊢ wf𝔹 = ⊑tag wfG𝔹 ⊑𝔹
dynᵖ-⊢ wf★ = ⊑★
dynᵖ-⊢ (wf⇒ wfA wfB) = ⊑tag wfG⇒ (⊑⇒ (dynᵖ-⊢ wfA) (dynᵖ-⊢ wfB))
dynᵖ-⊢ (wf∀ wfA) = ⊑tag wfG∀ (⊑∀ (dynᵖ-⊢ wfA))

------------------------------------------------------------------------
-- Uniqueness (Lemma 219)
------------------------------------------------------------------------

★⋢ground : ∀ {n p} G → n ⊢ p ⦂ ★ ⊑ groundTy G → ⊥
★⋢ground (G‵ α) ()
★⋢ground G𝔹 ()
★⋢ground G⇒ ()
★⋢ground G∀ ()

-- ? is only below ?
★⊑-inv : ∀ {n p B} → n ⊢ p ⦂ ★ ⊑ B → B ≡ ★
★⊑-inv ⊑★ = refl
★⊑-inv (⊑tag wfG p⊢) = refl

ground-unique : ∀ {n p q A} G H
  → n ⊢ p ⦂ A ⊑ groundTy G
  → n ⊢ q ⦂ A ⊑ groundTy H
  → G ≡ H
ground-unique (G‵ α) (G‵ β) (⊑‵ wfα) (⊑‵ wfβ) = refl
ground-unique (G‵ α) G𝔹 (⊑‵ wfα) ()
ground-unique (G‵ α) G⇒ (⊑‵ wfα) ()
ground-unique (G‵ α) G∀ (⊑‵ wfα) ()
ground-unique G𝔹 (G‵ β) ⊑𝔹 ()
ground-unique G𝔹 G𝔹 ⊑𝔹 ⊑𝔹 = refl
ground-unique G𝔹 G⇒ ⊑𝔹 ()
ground-unique G𝔹 G∀ ⊑𝔹 ()
ground-unique G⇒ (G‵ β) (⊑⇒ p⊢ q⊢) ()
ground-unique G⇒ G𝔹 (⊑⇒ p⊢ q⊢) ()
ground-unique G⇒ G⇒ (⊑⇒ p⊢ q⊢) (⊑⇒ p⊢′ q⊢′) = refl
ground-unique G⇒ G∀ (⊑⇒ p⊢ q⊢) ()
ground-unique G∀ (G‵ β) (⊑∀ p⊢) ()
ground-unique G∀ G𝔹 (⊑∀ p⊢) ()
ground-unique G∀ G⇒ (⊑∀ p⊢) ()
ground-unique G∀ G∀ (⊑∀ p⊢) (⊑∀ p⊢′) = refl

⊑-unique : ∀ {n p q A B} → n ⊢ p ⦂ A ⊑ B → n ⊢ q ⦂ A ⊑ B → p ≡ q
⊑-unique ⊑★ ⊑★ = refl
⊑-unique ⊑★ (⊑tag {G = G} wfG q⊢) with ★⋢ground G q⊢
⊑-unique ⊑★ (⊑tag {G = G} wfG q⊢) | ()
⊑-unique (⊑tag {G = G} wfG p⊢) ⊑★ with ★⋢ground G p⊢
⊑-unique (⊑tag {G = G} wfG p⊢) ⊑★ | ()
⊑-unique (⊑tag {G = G} wfG p⊢) (⊑tag {G = H} wfH q⊢)
  with ground-unique G H p⊢ q⊢
⊑-unique (⊑tag {G = G} wfG p⊢) (⊑tag {G = G} wfH q⊢) | refl =
  cong (tag G) (⊑-unique p⊢ q⊢)
⊑-unique (⊑‵ wfα) (⊑‵ wfα′) = refl
⊑-unique ⊑𝔹 ⊑𝔹 = refl
⊑-unique (⊑⇒ p⊢ q⊢) (⊑⇒ p⊢′ q⊢′) =
  cong₂ _⇒⊑_ (⊑-unique p⊢ p⊢′) (⊑-unique q⊢ q⊢′)
⊑-unique (⊑∀ p⊢) (⊑∀ p⊢′) = cong ∀⊑ (⊑-unique p⊢ p⊢′)

------------------------------------------------------------------------
-- Transitivity (Lemma 221), by induction on the second derivation
------------------------------------------------------------------------

⊑-trans : ∀ {n p q A B C}
  → n ⊢ p ⦂ A ⊑ B
  → n ⊢ q ⦂ B ⊑ C
  → ∃[ r ] (n ⊢ r ⦂ A ⊑ C)
⊑-trans p⊢ ⊑★ = _ , p⊢
⊑-trans p⊢ (⊑tag {G = G} wfG q⊢) with ⊑-trans p⊢ q⊢
⊑-trans p⊢ (⊑tag {G = G} wfG q⊢) | r , r⊢ = tag G r , ⊑tag wfG r⊢
⊑-trans p⊢ (⊑‵ wfα) = _ , p⊢
⊑-trans p⊢ ⊑𝔹 = _ , p⊢
⊑-trans (⊑⇒ p₁⊢ p₂⊢) (⊑⇒ q₁⊢ q₂⊢) with ⊑-trans p₁⊢ q₁⊢ | ⊑-trans p₂⊢ q₂⊢
⊑-trans (⊑⇒ p₁⊢ p₂⊢) (⊑⇒ q₁⊢ q₂⊢) | r₁ , r₁⊢ | r₂ , r₂⊢ =
  r₁ ⇒⊑ r₂ , ⊑⇒ r₁⊢ r₂⊢
⊑-trans (⊑∀ p⊢) (⊑∀ q⊢) with ⊑-trans p⊢ q⊢
⊑-trans (⊑∀ p⊢) (⊑∀ q⊢) | r , r⊢ = ∀⊑ r , ⊑∀ r⊢

------------------------------------------------------------------------
-- The gradual meet (Lemma 222)
------------------------------------------------------------------------

meetL-⊢ : ∀ {n A B C} (m : Meet A B C) → WfTy n A → WfTy n B
  → n ⊢ meetL m ⦂ C ⊑ A
meetL-⊢ m★L wfA wfB = dynᵖ-⊢ wfB
meetL-⊢ m★R wfA wfB = idᵖ-⊢ wfA
meetL-⊢ m‵ (wf‵ wfα) wfB = ⊑‵ wfα
meetL-⊢ m𝔹 wfA wfB = ⊑𝔹
meetL-⊢ (m⇒ m₁ m₂) (wf⇒ wfA₁ wfA₂) (wf⇒ wfB₁ wfB₂) =
  ⊑⇒ (meetL-⊢ m₁ wfA₁ wfB₁) (meetL-⊢ m₂ wfA₂ wfB₂)
meetL-⊢ (m∀ m) (wf∀ wfA) (wf∀ wfB) = ⊑∀ (meetL-⊢ m wfA wfB)

meetR-⊢ : ∀ {n A B C} (m : Meet A B C) → WfTy n A → WfTy n B
  → n ⊢ meetR m ⦂ C ⊑ B
meetR-⊢ m★L wfA wfB = idᵖ-⊢ wfB
meetR-⊢ m★R wfA wfB = dynᵖ-⊢ wfA
meetR-⊢ m‵ wfA (wf‵ wfα) = ⊑‵ wfα
meetR-⊢ m𝔹 wfA wfB = ⊑𝔹
meetR-⊢ (m⇒ m₁ m₂) (wf⇒ wfA₁ wfA₂) (wf⇒ wfB₁ wfB₂) =
  ⊑⇒ (meetR-⊢ m₁ wfA₁ wfB₁) (meetR-⊢ m₂ wfA₂ wfB₂)
meetR-⊢ (m∀ m) (wf∀ wfA) (wf∀ wfB) = ⊑∀ (meetR-⊢ m wfA wfB)

meet-wf : ∀ {n A B C} → Meet A B C → WfTy n A → WfTy n B → WfTy n C
meet-wf m wfA wfB = ⊑-wfL (meetL-⊢ m wfA wfB)

-- the meet is a greatest lower bound
meet-glb : ∀ {n p q A B C D}
  → Meet A B C
  → n ⊢ p ⦂ D ⊑ A
  → n ⊢ q ⦂ D ⊑ B
  → ∃[ r ] (n ⊢ r ⦂ D ⊑ C)
meet-glb m★L p⊢ q⊢ = _ , q⊢
meet-glb m★R p⊢ q⊢ = _ , p⊢
meet-glb m‵ p⊢ q⊢ = _ , p⊢
meet-glb m𝔹 p⊢ q⊢ = _ , p⊢
meet-glb (m⇒ m₁ m₂) (⊑⇒ p₁⊢ p₂⊢) (⊑⇒ q₁⊢ q₂⊢)
  with meet-glb m₁ p₁⊢ q₁⊢ | meet-glb m₂ p₂⊢ q₂⊢
meet-glb (m⇒ m₁ m₂) (⊑⇒ p₁⊢ p₂⊢) (⊑⇒ q₁⊢ q₂⊢) | r₁ , r₁⊢ | r₂ , r₂⊢ =
  r₁ ⇒⊑ r₂ , ⊑⇒ r₁⊢ r₂⊢
meet-glb (m∀ m) (⊑∀ p⊢) (⊑∀ q⊢) with meet-glb m p⊢ q⊢
meet-glb (m∀ m) (⊑∀ p⊢) (⊑∀ q⊢) | r , r⊢ = ∀⊑ r , ⊑∀ r⊢

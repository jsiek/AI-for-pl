module proof.CompilePrecision where

-- File Charter:
--   * Elaboration of PolyGν into PolyCν preserves term precision (thesis
--     Lemma 218): if Δ⊑ ⦂ Δ ⊑ᵉ Δ′, psize Δ⊑ ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′, and
--     Δ⊑ ∣ Γ⊑ ⊢ d ⊑ᴳ d′ ⦂ p, then Δ⊑ ∣ Γ⊑ ⊢ elab d ⊑ elab d′ ⦂ p.
--   * Supporting facts: the precision derivation of a surface precision
--     judgment relates the two sides' types (⊑ᴳ-types), casts are
--     monotone (Lemma 223), and so are ascription and the elimination
--     helper ⇓.
--   * Exported through CompileMeta.agda.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Types
open import Terms using (Term; cast; up; down)
open import Typing using (Ctx; _∋_⦂_; Z; S; ⤊)
open import GradualTerms
open import Compile
open import TermPrecision
open import GradualTermPrecision
open import CompileInvariants
open import proof.PrecisionProps
open import proof.CompileTyping
  using (Heads; hd★; hd‵; hd𝔹; hd⇒; hd∀; ≅-<; ∼‵-heads; ∼𝔹-heads;
         asFun-heads; asForall-heads)

------------------------------------------------------------------------
-- Lookups in related contexts
------------------------------------------------------------------------

⊑ᵉ-size : ∀ {Δ⊑ Δ Δ′} → Δ⊑ ⦂ Δ ⊑ᵉ Δ′ → tsize Δ ≡ psize Δ⊑
⊑ᵉ-size ⊑ᵉ[] = refl
⊑ᵉ-size (⊑ᵉabs ΔΔ′) rewrite ⊑ᵉ-size ΔΔ′ = refl
⊑ᵉ-size (⊑ᵉknown q⊢ ΔΔ′) rewrite ⊑ᵉ-size ΔΔ′ = refl

≅ᵖ-< : ∀ {Δ⊑ X q} → Δ⊑ ∋ X ≅ᵖ q → X < psize Δ⊑
≅ᵖ-< Z≅ᵖ = s≤s z≤n
≅ᵖ-< (S≅ᵖ X≅q) = s≤s (≅ᵖ-< X≅q)

≅ᵖ-⊢ : ∀ {Δ⊑ Δ Δ′ X q A A′} → Δ⊑ ⦂ Δ ⊑ᵉ Δ′
  → Δ⊑ ∋ X ≅ᵖ q → Δ ∋ X ≅ A → Δ′ ∋ X ≅ A′
  → psize Δ⊑ ⊢ q ⦂ A ⊑ A′
≅ᵖ-⊢ (⊑ᵉknown q⊢ ΔΔ′) Z≅ᵖ Z≅ Z≅ = ⇑ᵖ-⊢ q⊢
≅ᵖ-⊢ (⊑ᵉabs ΔΔ′) (S≅ᵖ X≅q) (S≅ X≅A) (S≅ X≅A′) =
  ⇑ᵖ-⊢ (≅ᵖ-⊢ ΔΔ′ X≅q X≅A X≅A′)
≅ᵖ-⊢ (⊑ᵉknown r⊢ ΔΔ′) (S≅ᵖ X≅q) (S≅ X≅A) (S≅ X≅A′) =
  ⇑ᵖ-⊢ (≅ᵖ-⊢ ΔΔ′ X≅q X≅A X≅A′)

∋ᵖ-⊢ : ∀ {n Γ⊑ Γ Γ′ x p A A′} → n ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′
  → Γ⊑ ∋ x ⦂ᵖ p → Γ ∋ x ⦂ A → Γ′ ∋ x ⦂ A′
  → n ⊢ p ⦂ A ⊑ A′
∋ᵖ-⊢ (⊑ᶜ∷ p⊢ ΓΓ′) Zᵖ Z Z = p⊢
∋ᵖ-⊢ (⊑ᶜ∷ q⊢ ΓΓ′) (Sᵖ x∈) (S x∈ₗ) (S x∈ᵣ) = ∋ᵖ-⊢ ΓΓ′ x∈ x∈ₗ x∈ᵣ

⤊ᶜ : ∀ {n Γ⊑ Γ Γ′} → n ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′
  → suc n ⊢ ⤊ᵖ Γ⊑ ⦂ ⤊ Γ ⊑ᶜ ⤊ Γ′
⤊ᶜ ⊑ᶜ[] = ⊑ᶜ[]
⤊ᶜ (⊑ᶜ∷ p⊢ ΓΓ′) = ⊑ᶜ∷ (⇑ᵖ-⊢ p⊢) (⤊ᶜ ΓΓ′)

------------------------------------------------------------------------
-- The precision of a surface precision judgment relates the two types
------------------------------------------------------------------------

asFun-dom : ∀ {n p A A′ A₁ A₁′ A₂ A₂′}
  → AsFun A A₁ A₂ → AsFun A′ A₁′ A₂′
  → n ⊢ p ⦂ A ⊑ A′
  → ∃[ p₁ ] (n ⊢ p₁ ⦂ A₁ ⊑ A₁′)
asFun-dom as-fun as-fun (⊑⇒ p₁⊢ p₂⊢) = _ , p₁⊢
asFun-dom as-fun as-fun★ (⊑tag {G = G⇒} wfG (⊑⇒ p₁⊢ p₂⊢)) = _ , p₁⊢
asFun-dom as-fun as-fun★ (⊑tag {G = G‵ α} wfG ())
asFun-dom as-fun as-fun★ (⊑tag {G = G𝔹} wfG ())
asFun-dom as-fun as-fun★ (⊑tag {G = G∀} wfG ())
asFun-dom as-fun★ as-fun ()
asFun-dom as-fun★ as-fun★ p⊢ = _ , ⊑★

⊑ᴳ-types : ∀ {Δ⊑ Γ⊑ Δ Δ′ Γ Γ′ M M′ A A′ p}
  {d : Δ ∣ Γ ⊢ᴳ M ⦂ A} {d′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
  → Δ⊑ ⦂ Δ ⊑ᵉ Δ′
  → psize Δ⊑ ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′
  → Δ⊑ ∣ Γ⊑ ⊢ d ⊑ᴳ d′ ⦂ p
  → psize Δ⊑ ⊢ p ⦂ A ⊑ A′
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑` {x∈ = x∈} {x∈′ = x∈′} x⊑) = ∋ᵖ-⊢ ΓΓ′ x⊑ x∈ x∈′
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑⦂⦂ M⊑ q⊢) = q⊢
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑seal X≅q M⊑) = ⊑‵ (≅ᵖ-< X≅q)
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑unseal {X≅A = X≅A} {X≅A′ = X≅A′} X≅q M⊑) =
  ≅ᵖ-⊢ ΔΔ′ X≅q X≅A X≅A′
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑is M⊑) = ⊑𝔹
⊑ᴳ-types ΔΔ′ ΓΓ′ ⊑true = ⊑𝔹
⊑ᴳ-types ΔΔ′ ΓΓ′ ⊑false = ⊑𝔹
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑if L⊑ M⊑ N⊑ r⊢) = r⊢
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑ƛ p⊢ M⊑) = ⊑⇒ p⊢ (⊑ᴳ-types ΔΔ′ (⊑ᶜ∷ p⊢ ΓΓ′) M⊑)
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑· L⊑ M⊑ r⊢) = r⊢
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑letv M⊑ N⊑) =
  ⊑ᴳ-types ΔΔ′ (⊑ᶜ∷ (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) ΓΓ′) N⊑
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑Λν M⊑) = ⊑∀ (⊑ᴳ-types (⊑ᵉabs ΔΔ′) (⤊ᶜ ΓΓ′) M⊑)
⊑ᴳ-types ΔΔ′ ΓΓ′ (⊑inst M⊑ q⊢ pX⊢ N⊑ r⊢) = r⊢

------------------------------------------------------------------------
-- Casts are monotone (Lemma 223)
------------------------------------------------------------------------

up-mono : ∀ {Δ⊑ Γ⊑ M M′ p ABl ABr q Al Ar Bl Br}
  → psize Δ⊑ ⊢ p ⦂ Al ⊑ Ar
  → psize Δ⊑ ⊢ ABl ⦂ Al ⊑ Bl
  → psize Δ⊑ ⊢ ABr ⦂ Ar ⊑ Br
  → psize Δ⊑ ⊢ q ⦂ Bl ⊑ Br
  → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p
  → Δ⊑ ∣ Γ⊑ ⊢ cast up ABl M ⊑ cast up ABr M′ ⦂ q
up-mono p⊢ ABl⊢ ABr⊢ q⊢ M⊑ with ⊑-trans p⊢ ABr⊢
up-mono p⊢ ABl⊢ ABr⊢ q⊢ M⊑ | r , r⊢ =
  ⊑upL (⊑upR M⊑ p⊢ ABr⊢ r⊢) ABl⊢ q⊢ r⊢

down-mono : ∀ {Δ⊑ Γ⊑ M M′ p ABl ABr q Al Ar Bl Br}
  → psize Δ⊑ ⊢ p ⦂ Al ⊑ Ar
  → psize Δ⊑ ⊢ ABl ⦂ Al ⊑ Bl
  → psize Δ⊑ ⊢ ABr ⦂ Ar ⊑ Br
  → psize Δ⊑ ⊢ q ⦂ Bl ⊑ Br
  → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ q
  → Δ⊑ ∣ Γ⊑ ⊢ cast down ABl M ⊑ cast down ABr M′ ⦂ p
down-mono p⊢ ABl⊢ ABr⊢ q⊢ M⊑ with ⊑-trans p⊢ ABr⊢
down-mono p⊢ ABl⊢ ABr⊢ q⊢ M⊑ | r , r⊢ =
  ⊑downR (⊑downL M⊑ ABl⊢ q⊢ r⊢) p⊢ ABr⊢ r⊢

ascribe-mono : ∀ {Δ⊑ Γ⊑ M M′ p q A A′ B B′}
  → psize Δ⊑ ⊢ p ⦂ A ⊑ A′
  → psize Δ⊑ ⊢ q ⦂ B ⊑ B′
  → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p
  → Δ⊑ ∣ Γ⊑ ⊢ ascribe A B M ⊑ ascribe A′ B′ M′ ⦂ q
ascribe-mono p⊢ q⊢ M⊑ =
  down-mono q⊢ (dynᵖ-⊢ (⊑-wfL q⊢)) (dynᵖ-⊢ (⊑-wfR q⊢)) ⊑★
    (up-mono p⊢ (dynᵖ-⊢ (⊑-wfL p⊢)) (dynᵖ-⊢ (⊑-wfR p⊢)) ⊑★ M⊑)

-- the elimination helper ⇓ is monotone
⇓-mono : ∀ {Δ⊑ Γ⊑ G A A′ A↓ A′↓ M M′ p p↓}
  → Heads G A A↓
  → Heads G A′ A′↓
  → WfGround (psize Δ⊑) G
  → psize Δ⊑ ⊢ p ⦂ A ⊑ A′
  → psize Δ⊑ ⊢ p↓ ⦂ A↓ ⊑ A′↓
  → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p
  → Δ⊑ ∣ Γ⊑ ⊢ ⇓ G A M ⊑ ⇓ G A′ M′ ⦂ p↓
⇓-mono hd★ hd★ wfG p⊢ p↓⊢ M⊑ = down-mono p↓⊢ G⊢ G⊢ p⊢ M⊑
  where G⊢ = ⊑tag wfG (idᵖ-⊢ (groundTy-wf wfG))
⇓-mono hd★ hd‵ wfG () p↓⊢ M⊑
⇓-mono hd★ hd𝔹 wfG () p↓⊢ M⊑
⇓-mono hd★ hd⇒ wfG () p↓⊢ M⊑
⇓-mono hd★ hd∀ wfG () p↓⊢ M⊑
⇓-mono hd‵ hd★ wfG p⊢ p↓⊢ M⊑ =
  ⊑downR M⊑ p↓⊢ (⊑tag wfG (idᵖ-⊢ (groundTy-wf wfG))) p⊢
⇓-mono hd𝔹 hd★ wfG p⊢ p↓⊢ M⊑ =
  ⊑downR M⊑ p↓⊢ (⊑tag wfG (idᵖ-⊢ (groundTy-wf wfG))) p⊢
⇓-mono hd⇒ hd★ wfG p⊢ p↓⊢ M⊑ =
  ⊑downR M⊑ p↓⊢ (⊑tag wfG (idᵖ-⊢ (groundTy-wf wfG))) p⊢
⇓-mono hd∀ hd★ wfG p⊢ p↓⊢ M⊑ =
  ⊑downR M⊑ p↓⊢ (⊑tag wfG (idᵖ-⊢ (groundTy-wf wfG))) p⊢
⇓-mono hd‵ hd‵ wfG p⊢ p↓⊢ M⊑ rewrite ⊑-unique p↓⊢ p⊢ = M⊑
⇓-mono hd𝔹 hd𝔹 wfG p⊢ p↓⊢ M⊑ rewrite ⊑-unique p↓⊢ p⊢ = M⊑
⇓-mono hd⇒ hd⇒ wfG p⊢ p↓⊢ M⊑ rewrite ⊑-unique p↓⊢ p⊢ = M⊑
⇓-mono hd∀ hd∀ wfG p⊢ p↓⊢ M⊑ rewrite ⊑-unique p↓⊢ p⊢ = M⊑

------------------------------------------------------------------------
-- Elaboration preserves precision (Lemma 218)
------------------------------------------------------------------------

elab-⊑ : ∀ {Δ⊑ Γ⊑ Δ Δ′ Γ Γ′ M M′ A A′ p}
  {d : Δ ∣ Γ ⊢ᴳ M ⦂ A} {d′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
  → Δ⊑ ⦂ Δ ⊑ᵉ Δ′
  → psize Δ⊑ ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′
  → Δ⊑ ∣ Γ⊑ ⊢ d ⊑ᴳ d′ ⦂ p
  → Δ⊑ ∣ Γ⊑ ⊢ elab d ⊑ elab d′ ⦂ p
elab-⊑ ΔΔ′ ΓΓ′ (⊑` x⊑) = ⊑` x⊑
elab-⊑ ΔΔ′ ΓΓ′ (⊑⦂⦂ M⊑ q⊢) =
  ascribe-mono (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) q⊢ (elab-⊑ ΔΔ′ ΓΓ′ M⊑)
elab-⊑ ΔΔ′ ΓΓ′ (⊑seal {X≅A = X≅A} {X≅A′ = X≅A′} X≅q M⊑) =
  ⊑seal X≅q
    (ascribe-mono (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) (≅ᵖ-⊢ ΔΔ′ X≅q X≅A X≅A′)
      (elab-⊑ ΔΔ′ ΓΓ′ M⊑))
elab-⊑ ΔΔ′ ΓΓ′ (⊑unseal {B∼X = B∼X} {B′∼X = B′∼X} X≅q M⊑) =
  ⊑unseal X≅q
    (⇓-mono (∼‵-heads B∼X) (∼‵-heads B′∼X) (wfG‵ X<n)
      (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) (⊑‵ X<n) (elab-⊑ ΔΔ′ ΓΓ′ M⊑))
  where X<n = ≅ᵖ-< X≅q
elab-⊑ ΔΔ′ ΓΓ′ (⊑is {wfG = wfG} M⊑) =
  ⊑is (subst (λ n → WfGround n _) (⊑ᵉ-size ΔΔ′) wfG)
    (up-mono p⊢ (dynᵖ-⊢ (⊑-wfL p⊢)) (dynᵖ-⊢ (⊑-wfR p⊢)) ⊑★
      (elab-⊑ ΔΔ′ ΓΓ′ M⊑))
  where p⊢ = ⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑
elab-⊑ ΔΔ′ ΓΓ′ ⊑true = ⊑true
elab-⊑ ΔΔ′ ΓΓ′ ⊑false = ⊑false
elab-⊑ ΔΔ′ ΓΓ′
  (⊑if {A∼𝔹 = A∼𝔹} {A′∼𝔹 = A′∼𝔹} {m = m} {m′ = m′} L⊑ M⊑ N⊑ r⊢) =
  ⊑if (⇓-mono (∼𝔹-heads A∼𝔹) (∼𝔹-heads A′∼𝔹) wfG𝔹
         (⊑ᴳ-types ΔΔ′ ΓΓ′ L⊑) ⊑𝔹 (elab-⊑ ΔΔ′ ΓΓ′ L⊑))
      (down-mono r⊢ (meetL-⊢ m wfBt wfBf) (meetL-⊢ m′ wfBt′ wfBf′) pM⊢
         (elab-⊑ ΔΔ′ ΓΓ′ M⊑))
      (down-mono r⊢ (meetR-⊢ m wfBt wfBf) (meetR-⊢ m′ wfBt′ wfBf′) pN⊢
         (elab-⊑ ΔΔ′ ΓΓ′ N⊑))
  where
  pM⊢ = ⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑
  pN⊢ = ⊑ᴳ-types ΔΔ′ ΓΓ′ N⊑
  wfBt = ⊑-wfL pM⊢
  wfBt′ = ⊑-wfR pM⊢
  wfBf = ⊑-wfL pN⊢
  wfBf′ = ⊑-wfR pN⊢
elab-⊑ ΔΔ′ ΓΓ′ (⊑ƛ p⊢ M⊑) = ⊑ƛ p⊢ (elab-⊑ ΔΔ′ (⊑ᶜ∷ p⊢ ΓΓ′) M⊑)
elab-⊑ ΔΔ′ ΓΓ′ (⊑· {shp = shp} {shp′ = shp′} L⊑ M⊑ r⊢)
  with asFun-dom shp shp′ (⊑ᴳ-types ΔΔ′ ΓΓ′ L⊑)
elab-⊑ ΔΔ′ ΓΓ′ (⊑· {shp = shp} {shp′ = shp′} L⊑ M⊑ r⊢) | p₁ , p₁⊢ =
  ⊑· (⇓-mono (asFun-heads shp) (asFun-heads shp′) wfG⇒
        (⊑ᴳ-types ΔΔ′ ΓΓ′ L⊑) (⊑⇒ p₁⊢ r⊢) (elab-⊑ ΔΔ′ ΓΓ′ L⊑))
     (ascribe-mono (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) p₁⊢ (elab-⊑ ΔΔ′ ΓΓ′ M⊑))
elab-⊑ ΔΔ′ ΓΓ′ (⊑letv M⊑ N⊑) =
  ⊑letv (elab-⊑ ΔΔ′ ΓΓ′ M⊑)
        (elab-⊑ ΔΔ′ (⊑ᶜ∷ (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) ΓΓ′) N⊑)
elab-⊑ ΔΔ′ ΓΓ′ (⊑Λν M⊑) = ⊑Λν (elab-⊑ (⊑ᵉabs ΔΔ′) (⤊ᶜ ΓΓ′) M⊑)
elab-⊑ ΔΔ′ ΓΓ′ (⊑inst {shp = shp} {shp′ = shp′} M⊑ q⊢ pX⊢ N⊑ r⊢) =
  ⊑inst (⇓-mono (asForall-heads shp) (asForall-heads shp′) wfG∀
           (⊑ᴳ-types ΔΔ′ ΓΓ′ M⊑) (⊑∀ pX⊢) (elab-⊑ ΔΔ′ ΓΓ′ M⊑))
        q⊢
        (elab-⊑ (⊑ᵉknown q⊢ ΔΔ′) (⊑ᶜ∷ pX⊢ (⤊ᶜ ΓΓ′)) N⊑)

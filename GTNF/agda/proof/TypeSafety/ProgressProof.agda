module proof.TypeSafety.ProgressProof where

-- File Charter:
--   * Gives the complete typing-derivation case skeleton for GTNF progress.
--   * Recursive calls are made only on immediate typing premises.
--   * The remaining holes are value-closing arguments: canonical forms and
--     active coercion or conversion classification.

open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Terms
open import Boundary
open import TermSubst
open import Reduction
open import proof.TypeSafety.ProgressDef
open import proof.TypeSafety.Canonical
open import proof.TypeSafety.NoBotValue using (no-bot-value)

private
  variable
    Δ Δᵢ Δᶜ : Ctxᵗ
    A B : Ty
    M : Term

------------------------------------------------------------------------
-- Boundary support
------------------------------------------------------------------------

conv-split : ∀ {Ξ Δ Δ″} (χ₁ : List Change) {χ₂ : List Change}
  → Ξ ∣ Δ ⊢χᶜ χ₁ ++ χ₂ ⇒ Δ″
  → Σ[ Δ′ ∈ TyCtx ] ((Ξ ∣ Δ ⊢χᶜ χ₂ ⇒ Δ′)
      × (Ξ ∣ Δ′ ⊢χᶜ χ₁ ⇒ Δ″))
conv-split [] cs = _ , cs , conv[]
conv-split (unbind X α ∷ χ₁) (conv-unbind v cs) with conv-split χ₁ cs
conv-split (unbind X α ∷ χ₁) (conv-unbind v cs)
    | Δ′ , cs₂ , cs₁ = Δ′ , cs₂ , conv-unbind v cs₁
conv-split (bind X α ∷ χ₁) (conv-bind v cs fr i) with conv-split χ₁ cs
conv-split (bind X α ∷ χ₁) (conv-bind v cs fr i)
    | Δ′ , cs₂ , cs₁ = Δ′ , cs₂ , conv-bind v cs₁ fr i
conv-split (bind X α ∷ χ₁) (conv-bind-live v cs d)
    with conv-split χ₁ cs
conv-split (bind X α ∷ χ₁) (conv-bind-live v cs d)
    | Δ′ , cs₂ , cs₁ = Δ′ , cs₂ , conv-bind-live v cs₁ d

merged-keeps₂ : ∀ {Δ Δ₂ᶜ Δ⋉ᶜ : Ctxᵗ} {Θ₁ Θ₂ : Boundary}
  → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → names Δ₂ᶜ ⊆ᵃ names Δ⋉ᶜ
merged-keeps₂ {Θ₁ = Θ₁} (conversion cs₂) (conversion cs⋉)
    with conv-split Θ₁ cs⋉
merged-keeps₂ {Θ₁ = Θ₁} (conversion cs₂) (conversion cs⋉)
    | Δ′ , cs₂′ , cs₁ with conv-changes-functional cs₂ cs₂′
merged-keeps₂ {Θ₁ = Θ₁} (conversion cs₂) (conversion cs⋉)
    | Δ′ , cs₂′ , cs₁ | refl = conv-mono cs₁

interior-live-conversion : ∀ {Ξ Δ Δᵢ Δᶜ χ α}
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Δᵢ ∋ᵅ α
  → Δᶜ ∋ᵅ α
interior-live-conversion changes[] conv[] lv = lv
interior-live-conversion (changes∷ cs (step-unbind v dl fr))
    (conv-unbind v′ csᶜ) lv =
  interior-live-conversion cs csᶜ (del-inv dl lv)
interior-live-conversion (changes∷ cs (step-bind v fr i))
    (conv-bind v′ csᶜ fr′ i′) lv with ins-inv i lv
interior-live-conversion (changes∷ cs (step-bind v fr i))
    (conv-bind v′ csᶜ fr′ i′) lv | inj₁ refl = ins-live i′
interior-live-conversion (changes∷ cs (step-bind v fr i))
    (conv-bind v′ csᶜ fr′ i′) lv | inj₂ lv′ =
  ins-mono i′ (interior-live-conversion cs csᶜ lv′)
interior-live-conversion (changes∷ cs (step-bind v fr i))
    (conv-bind-live v′ csᶜ d) lv with ins-inv i lv
interior-live-conversion (changes∷ cs (step-bind v fr i))
    (conv-bind-live v′ csᶜ d) lv | inj₁ refl = _ , d
interior-live-conversion (changes∷ cs (step-bind v fr i))
    (conv-bind-live v′ csᶜ d) lv | inj₂ lv′ =
  interior-live-conversion cs csᶜ lv′

same-interior-conversion : ∀ {Δ Δᵢ Δᶜ Θ X}
  → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → Δᵢ ∋tv X
  → Σ[ Xᶜ ∈ ℕ ] (Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ)
same-interior-conversion {X = X} (interior cs) (conversion csᶜ) (α , d)
    with interior-live-conversion cs csᶜ (X , d)
same-interior-conversion {X = X} (interior cs) (conversion csᶜ) (α , d)
    | Xᶜ , dᶜ = Xᶜ , ` α , same-var d , same-var dᶜ

merge-redex : ∀ {Δ Δᵢ Δ₂ᶜ U Θ₁ Θ₂ t₁ c₂ B C D}
  → Value (U ⟪ Θ₁ , tail t₁ ⟫)
  → BoundaryWf Δ Θ₂ Δᵢ Δ₂ᶜ
  → Δᵢ ∣ [] ⊢ U ⟪ Θ₁ , tail t₁ ⟫ ⦂ B
  → Δ₂ᶜ ⊢ c₂ ∶ C ⇝ D
  → Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
      (Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ -→ M′ ∣ δ)
merge-redex v mw₂
    (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
    with merged-conversion-exists mw₂ mw₁
merge-redex v mw₂
    (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
    | Δ⋉ᶜ , r⋉ , keep₁ with readableᵀ ⊢t₁ | readable ⊢c₂
merge-redex v mw₂
    (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
    | Δ⋉ᶜ , r⋉ , keep₁ | r₁ , rd₁ | r₂ , rd₂
    with weakenᵀ keep₁ rd₁
       | weaken (merged-keeps₂ (bw-conversion mw₂) r⋉) rd₂
merge-redex v mw₂
    (boundary mw₁ ⊢U (conv-tail ⊢t₁) sm₁ se₁ wB) ⊢c₂
    | Δ⋉ᶜ , r⋉ , keep₁ | r₁ , rd₁ | r₂ , rd₂
    | t₁′ , rd₁′ | c₂′ , rd₂′ =
  _ , none , Merge v (bw-interior mw₂) (bw-conversion mw₁)
    (bw-conversion mw₂) r⋉
    (tail r₁ , sameᶜ-tail rd₁′ , sameᶜ-tail rd₁)
    (r₂ , rd₂′ , rd₂)

progress-id★ : ∀ {Δ Δᵢ Δᶜ U Θ}
  → Simple U
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → Δᵢ ∣ [] ⊢ U ⦂ ★
  → Value (U ⟪ Θ , ⌞ id ★ ⌟ ⟫)
    ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
         (Δ ⊢ U ⟪ Θ , ⌞ id ★ ⌟ ⟫ -→ M′ ∣ δ))
progress-id★ S-$ mw ()
progress-id★ S-true mw ()
progress-id★ S-false mw ()
progress-id★ S-ƛ mw ()
progress-id★ (S-Λ v) mw ()
progress-id★ (S-cast v I-tag) mw (⊢cast ⊢V (⊢tag g) len) =
  inj₂ (_ , none , IdDyn v g)
progress-id★ {Θ = Θ} (S-cast v I-tag) mw
    (⊢cast ⊢V (⊢tag-var {X = X} tv mode ok) len)
    with toExt Θ X in eq
progress-id★ {Θ = Θ} (S-cast v I-tag) mw
    (⊢cast ⊢V (⊢tag-var {X = X} tv mode ok) len)
    | nothing = inj₁ (V-fresh v eq)
progress-id★ {Θ = Θ} (S-cast v I-tag) mw
    (⊢cast ⊢V (⊢tag-var {X = X} tv mode ok) len)
    | just X′ with same-interior-conversion
        (bw-interior mw) (bw-conversion mw) tv
progress-id★ {Θ = Θ} (S-cast v I-tag) mw
    (⊢cast ⊢V (⊢tag-var {X = X} tv mode ok) len)
    | just X′ | Xᶜ , same =
  inj₂ (_ , none , IdDyn-var v eq (bw-interior mw)
    (bw-conversion mw) same)
progress-id★ (S-cast v I-↦) mw (⊢cast _ () _)
progress-id★ (S-cast v I-∀ᵖ) mw (⊢cast _ () _)
progress-id★ (S-cast v I-gen) mw (⊢cast _ () _)

progress-boundary : ∀ {Δ Δᵢ Δᶜ Θ c M Bᵢ Cᵢ Cₑ}
  → Value M
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
  → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
  → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
  → Value (M ⟪ Θ , c ⟫)
    ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
         (Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ∣ δ))
progress-boundary v@(V-⟪⟫ u it) mw ⊢M ⊢c same =
  inj₂ (merge-redex v mw ⊢M ⊢c)
progress-boundary v@(V-fresh w fresh) mw ⊢M ⊢c same =
  inj₂ (merge-redex v mw ⊢M ⊢c)
progress-boundary (V-simple u) mw ⊢M ⊢c same with act-or-inert ⊢c
progress-boundary (V-simple u) mw ⊢M ⊢c same | inj₂ (I-tail it) =
  inj₁ (V-⟪⟫ u it)
progress-boundary (V-simple u) mw ⊢M ⊢c same | inj₁ (A-idb b) =
  inj₂ (_ , none , Id u b)
progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mw ⊢M
    (conv-tail (conv-mid conv-id★)) same | inj₁ A-id★
    with ≈-★-source {Δ = Δᵢ} {Δ′ = Δᶜ} same
progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mw ⊢M
    (conv-tail (conv-mid conv-id★)) same | inj₁ A-id★ | refl =
  progress-id★ u mw ⊢M
progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mw ⊢M
    (conv-unseal d) same | inj₁ A-unseal
    with ≈-var-source {Δ = Δᵢ} {Δ′ = Δᶜ} same
progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mw ⊢M
    (conv-unseal d) same | inj₁ A-unseal | Y , refl =
  ⊥-elim (simple-¬var u ⊢M)
progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mw ⊢M
    (conv-unseal-seq d ⊢c n m) same | inj₁ A-unseal-seq
    with ≈-var-source {Δ = Δᵢ} {Δ′ = Δᶜ} same
progress-boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} (V-simple u) mw ⊢M
    (conv-unseal-seq d ⊢c n m) same | inj₁ A-unseal-seq | Y , refl =
  ⊥-elim (simple-¬var u ⊢M)

progress-wrap : ∀ {Δ U M Θ s t A B}
  → Simple U
  → Value M
  → Δ ∣ [] ⊢ U ⟪ Θ , ⌞ s ↦ t ⌟ ⟫ ⦂ (A ⇒ B)
  → Σ[ N ∈ Term ] Σ[ δ ∈ Alloc ]
      (Δ ⊢ (U ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · M -→ N ∣ δ)
progress-wrap u vM
    (boundary mwΘ ⊢U
      (conv-tail (conv-mid (conv-fun ⊢s ⊢t))) sameᵢ sameₑ wE)
    with wrap-premises-boundary mwΘ ⊢s
progress-wrap u vM
    (boundary mwΘ ⊢U
      (conv-tail (conv-mid (conv-fun ⊢s ⊢t))) sameᵢ sameₑ wE)
    | Δᵈ , s′ , rd , sc =
  _ , _ , Wrap u vM (bw-conversion mwΘ) (bw-interior mwΘ) rd sc

------------------------------------------------------------------------
-- Cast support
------------------------------------------------------------------------

progress-check : ∀ {Δ V μ H ℓ}
  → Value V
  → Δ ∣ [] ⊢ V ⦂ ★
  → Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
      (Δ ⊢ V ⟨ μ ∣ H ？ ℓ ⟩ -→ M′ ∣ δ)
progress-check {H = H} vV V⊢ with canonical-★ vV V⊢
progress-check {H = H} vV V⊢ | star-tag {G = G} vW refl
    with G ≟ᵗ H
progress-check {H = H} vV V⊢ | star-tag {G = .H} vW refl | yes refl =
  _ , none , TagUntag vW
progress-check {H = H} vV V⊢ | star-tag {G = G} vW refl | no G≢H =
  _ , none , TagUntagBad vW G≢H
progress-check {H = H} vV V⊢ | star-fresh vW fresh refl =
  _ , none , TagUntagBad-⟪⟫ vW fresh

progress-cast : ∀ {Δ V μ p A B}
  → Δ ∣ [] ⊢ V ⦂ A
  → Value V
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
  → length μ ≡ length (names Δ)
  → Value (V ⟨ μ ∣ p ⟩)
    ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
         (Δ ⊢ V ⟨ μ ∣ p ⟩ -→ M′ ∣ δ))
progress-cast V⊢ vV (⊢id wA) len = inj₂ (_ , none , CastId vV)
progress-cast V⊢ vV (⊢tag g) len = inj₁ (V-simple (S-cast vV I-tag))
progress-cast V⊢ vV (⊢tag-var tv mode ok) len =
  inj₁ (V-simple (S-cast vV I-tag))
progress-cast V⊢ vV (⊢check g) len = inj₂ (progress-check vV V⊢)
progress-cast V⊢ vV (⊢check-var tv mode ok) len =
  inj₂ (progress-check vV V⊢)
progress-cast V⊢ vV (⊢fun ⊢p ⊢q) len =
  inj₁ (V-simple (S-cast vV I-↦))
progress-cast V⊢ vV (⊢all ⊢p) len =
  inj₁ (V-simple (S-cast vV I-∀ᵖ))
progress-cast V⊢ vV (⊢inst ⊢p wB nvA z∈A nsB) len =
  inj₂ (_ , none , Inst vV)
progress-cast V⊢ vV (⊢gen ⊢p wA nvB z∈B nsA safe) len =
  inj₁ (V-simple (S-cast vV I-gen))
progress-cast V⊢ vV (⊢seq-tag ⊢p tg ns) len =
  inj₂ (_ , none , CastSeq vV)
progress-cast V⊢ vV (⊢seq-check cg ⊢p ns) len =
  inj₂ (_ , none , CastSeq? vV)
progress-cast V⊢ vV ⊢bot-elim len = ⊥-elim (no-bot-value vV V⊢)
progress-cast V⊢ vV ⊢bot-intro len =
  inj₂ (_ , none , BlameBotIntro vV)

progress : Progress-Statement
progress (⊢` ())
progress ⊢$ = inj₁ (V-simple S-$)
progress ⊢true = inj₁ (V-simple S-true)
progress ⊢false = inj₁ (V-simple S-false)
progress (⊢ƛ _ _) = inj₁ (V-simple S-ƛ)
progress (⊢Λ vN _) = inj₁ (V-simple (S-Λ vN))
progress {M = L · M} (⊢· ⊢L ⊢M) with progress ⊢L
progress {M = L · M} (⊢· ⊢L ⊢M) | inj₁ vL with progress ⊢M
progress {M = L · M} (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM
    with canonical-⇒ vL ⊢L
progress {M = (ƛ A ∙ N) · M} (⊢· ⊢L ⊢M)
    | inj₁ vL | inj₁ vM | fun-ƛ refl =
  inj₂ (inj₂ (_ , none , Beta vM))
progress {M = L · M} (⊢· ⊢L ⊢M)
    | inj₁ vL | inj₁ vM | fun-boundary u refl =
  inj₂ (inj₂ (progress-wrap u vM ⊢L))
progress {M = (V ⟨ μ ∣ p ↦ᵖ q ⟩) · M} (⊢· ⊢L ⊢M)
    | inj₁ vL | inj₁ vM | fun-cast vV refl =
  inj₂ (inj₂ (_ , none , CastFun vV vM))
progress {M = L · M} (⊢· ⊢L ⊢M)
    | inj₁ vL | inj₂ (inj₁ (ℓ , refl)) =
  inj₂ (inj₂ (blame ℓ , none , Blame-·₂ vL))
progress {M = L · M} (⊢· ⊢L ⊢M)
    | inj₁ vL | inj₂ (inj₂ (M′ , δ , st)) =
  inj₂ (inj₂ (((↑ᴹ[ δ ] L) · M′) , δ , ξ-·₂ vL st))
progress {M = L · M} (⊢· ⊢L ⊢M) | inj₂ (inj₁ (ℓ , refl)) =
  inj₂ (inj₂ (blame ℓ , none , Blame-·₁))
progress {M = L · M} (⊢· ⊢L ⊢M) | inj₂ (inj₂ (L′ , δ , st)) =
  inj₂ (inj₂ ((L′ · (↑ᴹ[ δ ] M)) , δ , ξ-·₁ st))
progress {M = ν A · L ⟨ c ⟩} (⊢ν wA rA ⊢L mw ⊢c same wB)
    with progress ⊢L
progress {M = ν A · L ⟨ c ⟩} (⊢ν wA rA ⊢L mw ⊢c same wB)
    | inj₁ vL with canonical-∀ vL ⊢L
progress {M = ν A · L ⟨ c ⟩} (⊢ν wA rA ⊢L mw ⊢c same wB)
    | inj₁ vL | N , inst =
  inj₂ (inj₂ (_ , new _ , TyBeta vL inst rA))
progress {M = ν A · L ⟨ c ⟩} (⊢ν wA rA ⊢L mw ⊢c same wB)
    | inj₂ (inj₁ (ℓ , refl)) =
  inj₂ (inj₂ (blame ℓ , none , Blame-ν))
progress {M = ν A · L ⟨ c ⟩} (⊢ν wA rA ⊢L mw ⊢c same wB)
    | inj₂ (inj₂ (L′ , δ , st)) =
  inj₂ (inj₂ (ν A · L′ ⟨ c ⟩ , δ , ξ-ν st))
progress {M = M ⟪ Θ , c ⟫}
    (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) with progress ⊢M
progress {M = M ⟪ Θ , c ⟫}
    (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₁ vM
    with progress-boundary vM mwΘ ⊢M ⊢c sameᵢ
progress {M = M ⟪ Θ , c ⟫}
    (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₁ vM | inj₁ v = inj₁ v
progress {M = M ⟪ Θ , c ⟫}
    (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
    | inj₁ vM | inj₂ step = inj₂ (inj₂ step)
progress {M = M ⟪ Θ , c ⟫}
    (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
    | inj₂ (inj₁ (ℓ , refl)) =
  inj₂ (inj₂ (blame ℓ , none , Blame-⟪⟫))
progress {M = M ⟪ Θ , c ⟫}
    (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
    | inj₂ (inj₂ (M′ , δ , st)) =
  inj₂ (inj₂ ((M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫) , δ ,
    ξ-⟪⟫ (bw-interior mwΘ) st))
progress {M = M ⟨ μ ∣ p ⟩} (⊢cast ⊢M ⊢p len) with progress ⊢M
progress {M = M ⟨ μ ∣ p ⟩} (⊢cast ⊢M ⊢p len) | inj₁ vM
    with progress-cast ⊢M vM ⊢p len
progress {M = M ⟨ μ ∣ p ⟩} (⊢cast ⊢M ⊢p len)
    | inj₁ vM | inj₁ v = inj₁ v
progress {M = M ⟨ μ ∣ p ⟩} (⊢cast ⊢M ⊢p len)
    | inj₁ vM | inj₂ step = inj₂ (inj₂ step)
progress {M = M ⟨ μ ∣ p ⟩} (⊢cast ⊢M ⊢p len)
    | inj₂ (inj₁ (ℓ , refl)) =
  inj₂ (inj₂ (blame ℓ , none , Blame-cast))
progress {M = M ⟨ μ ∣ p ⟩} (⊢cast ⊢M ⊢p len)
    | inj₂ (inj₂ (M′ , δ , st)) =
  inj₂ (inj₂ ((M′ ⟨ μ ∣ p ⟩) , δ , ξ-cast st))
progress (⊢blame {ℓ = ℓ} _) = inj₂ (inj₁ (ℓ , refl))

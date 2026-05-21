module proof.ImprecisionConsistent where

-- File Charter:
--   * Properties that involve Imprecisoin and Consistency

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Imprecision
open import Consistency
open import Types
open import proof.ConsistencyProperties
  using
    ( length-leftICtx
    ; length-rightICtx
    ; length-extend-X~X[]
    ; drop-neither-~
    )
open import proof.ImprecisionProperties
  using
    ( _≤ᵢ_
    ; []≤ᵢ
    ; _∷≤ᵢ_
    ; X⊑X≤X⊑X
    ; X⊑X≤ν
    ; trans-ctx-⊑
    )

leftICtx-extend-X~X[] : ∀ Δ → leftICtx (extend-X~X Δ []) ≡ extend-X⊑X Δ []
leftICtx-extend-X~X[] zero = refl
leftICtx-extend-X~X[] (suc Δ) = cong (X⊑X ∷_) (leftICtx-extend-X~X[] Δ)

rightICtx-extend-X~X[] : ∀ Δ → rightICtx (extend-X~X Δ []) ≡ extend-X⊑X Δ []
rightICtx-extend-X~X[] zero = refl
rightICtx-extend-X~X[] (suc Δ) = cong (X⊑X ∷_) (rightICtx-extend-X~X[] Δ)

wf-leftICtx :
  ∀ {Γ A} →
  WfTy (length Γ) 0 A →
  WfTy (length (leftICtx Γ)) 0 A
wf-leftICtx {Γ = Γ} wfA =
  subst (λ Δ → WfTy Δ 0 _) (sym (length-leftICtx Γ)) wfA

wf-rightICtx :
  ∀ {Γ A} →
  WfTy (length Γ) 0 A →
  WfTy (length (rightICtx Γ)) 0 A
wf-rightICtx {Γ = Γ} wfA =
  subst (λ Δ → WfTy Δ 0 _) (sym (length-rightICtx Γ)) wfA

left-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~★ →
  leftICtx Γ ∋ X ∶ X⊑X
left-lookup-left here = here
left-lookup-left (there x∈) = there (left-lookup-left x∈)

right-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~★ →
  rightICtx Γ ∋ X ∶ X⊑★
right-lookup-left here = here
right-lookup-left (there x∈) = there (right-lookup-left x∈)

left-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ ★~X →
  leftICtx Γ ∋ X ∶ X⊑★
left-lookup-right here = here
left-lookup-right (there x∈) = there (left-lookup-right x∈)

right-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ ★~X →
  rightICtx Γ ∋ X ∶ X⊑X
right-lookup-right here = here
right-lookup-right (there x∈) = there (right-lookup-right x∈)

left-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~X →
  leftICtx Γ ∋ X ∶ X⊑X
left-lookup-both here = here
left-lookup-both (there x∈) = there (left-lookup-both x∈)

right-lookup-both : 
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~X →
  rightICtx Γ ∋ X ∶ X⊑X
right-lookup-both here = here
right-lookup-both (there x∈) = there (right-lookup-both x∈)

coerce-wt : ∀ {Γ A C} →
  (A~C : Γ ⊢ A ~ C) →
  ∃[ B ]
    (0 ∣ leftICtx Γ ⊢ proj₁ (coerce A~C) ⦂ A ⊒ B) ×
    (0 ∣ rightICtx Γ ⊢ proj₂ (coerce A~C) ⦂ B ⊑ C)
coerce-wt ★-~-★ =
  ★ , ⊢★-⊑-★ , ⊢★-⊑-★
coerce-wt (X-~-X {X} x∈) =
  ＇ X ,
  ⊢X-⊑-X (left-lookup-both x∈) ,
  ⊢X-⊑-X (right-lookup-both x∈)
coerce-wt ι-~-ι =
  ‵ _ , ⊢ι-⊑-ι , ⊢ι-⊑-ι
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    with coerce A~A′ | coerce B~B′ | coerce-wt A~A′ | coerce-wt B~B′
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    | pA⊒ , pA⊑
    | pB⊒ , pB⊑
    | Aₘ , pA⊒⊢ , pA⊑⊢
    | Bₘ , pB⊒⊢ , pB⊑⊢ =
  Aₘ ⇒ Bₘ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊒⊢ pB⊒⊢ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊑⊢ pB⊑⊢
coerce-wt (∀-~-∀ A~B) with coerce A~B | coerce-wt A~B
coerce-wt (∀-~-∀ A~B) | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-∀B p⊒⊢ , ⊢∀A-⊑-∀B p⊑⊢
coerce-wt (A-~-★ n★ n∀ g A~G) with coerce A~G | coerce-wt A~G
coerce-wt (A-~-★ n★ n∀ g A~G) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  p⊒⊢ , ⊢A-⊑-★ g p⊑⊢
coerce-wt (★-~-B n★ n∀ h H~B) with coerce H~B | coerce-wt H~B
coerce-wt (★-~-B n★ n∀ h H~B) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  ⊢A-⊑-★ h p⊒⊢ , p⊑⊢
coerce-wt (νX-~-★ {X} x∈) =
  ＇ X ,
  ⊢X-⊑-X (left-lookup-left x∈) ,
  ⊢X-⊑-★ (right-lookup-left x∈)
coerce-wt (★-~-νX {X} x∈) =
  ＇ X ,
  ⊢X-⊑-★ (left-lookup-right x∈) ,
  ⊢X-⊑-X (right-lookup-right x∈)
coerce-wt {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B)
    with coerce A~⇑B | coerce-wt A~⇑B
coerce-wt {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-∀B p⊒⊢ , ⊢∀A-⊑-B (wf-rightICtx {Γ = Γ} wfB) p⊑⊢
coerce-wt {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B)
    with coerce ⇑A~B | coerce-wt ⇑A~B
coerce-wt {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-B (wf-leftICtx {Γ = Γ} wfA) p⊒⊢ , ⊢∀A-⊑-∀B p⊑⊢

coerce-wt-extend-X⊑X :
  ∀ {Δ A C} →
  (A~C : extend-X~X Δ [] ⊢ A ~ C) →
  ∃[ B ]
    ((0 ∣ extend-X⊑X Δ [] ⊢ coerce-⊒ A~C ⦂ A ⊒ B) ×
     (0 ∣ extend-X⊑X Δ [] ⊢ coerce-⊑ A~C ⦂ B ⊑ C))
coerce-wt-extend-X⊑X {Δ = Δ} A~C with coerce-wt A~C
coerce-wt-extend-X⊑X {Δ = Δ} A~C | B , p⊒⊢ , p⊑⊢
  rewrite leftICtx-extend-X~X[] Δ | rightICtx-extend-X~X[] Δ =
  B , p⊒⊢ , p⊑⊢

postulate
  coerce-glbᶜ :
    ∀ {Γ Φ A C B B′ p⊒ p⊑ pA pC} →
    (A~C : Γ ⊢ A ~ C) →
    leftICtx Γ ≤ᵢ Φ →
    rightICtx Γ ≤ᵢ Φ →
    0 ∣ leftICtx Γ ⊢ p⊒ ⦂ B ⊑ A →
    0 ∣ rightICtx Γ ⊢ p⊑ ⦂ B ⊑ C →
    0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A →
    0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C →
    p⊒ ≡ coerce-⊒ A~C →
    p⊑ ≡ coerce-⊑ A~C →
    ∃[ r ] 0 ∣ Φ ⊢ r ⦂ B′ ⊑ B

left-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑X →
  rightICtx Γ ∋ X ∶ X⊑X →
  Γ ∋ᶜ X ∶ X~X
left-right-plain {Γ = X~★ ∷ Γ} here ()
left-right-plain {Γ = X~★ ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = ★~X ∷ Γ} () here
left-right-plain {Γ = ★~X ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = X~X ∷ Γ} here here = here
left-right-plain {Γ = X~X ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = neither ∷ Γ} {X = zero} () ()
left-right-plain {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)

left-ν-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑★ →
  rightICtx Γ ∋ X ∶ X⊑X →
  Γ ∋ᶜ X ∶ ★~X
left-ν-right-plain {Γ = X~★ ∷ Γ} {X = zero} ()
left-ν-right-plain {Γ = X~★ ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = ★~X ∷ Γ} here here = here
left-ν-right-plain {Γ = ★~X ∷ Γ} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = X~X ∷ Γ} {X = zero} () here
left-ν-right-plain {Γ = X~X ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = neither ∷ Γ} {X = zero} here ()
left-ν-right-plain {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)

left-plain-right-ν :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑X →
  rightICtx Γ ∋ X ∶ X⊑★ →
  Γ ∋ᶜ X ∶ X~★
left-plain-right-ν {Γ = X~★ ∷ Γ} here here = here
left-plain-right-ν {Γ = X~★ ∷ Γ} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = ★~X ∷ Γ} {X = zero} () ()
left-plain-right-ν {Γ = ★~X ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = X~X ∷ Γ} {X = zero} here ()
left-plain-right-ν {Γ = X~X ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = neither ∷ Γ} {X = zero} () here
left-plain-right-ν {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)

postulate
  lower-bounds-star-leftᶜ :
    ∀ {Γ A C p q G} →
    Ground G →
    0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ G →
    0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ C →
    Γ ⊢ ★ ~ C

  lower-bounds-star-rightᶜ :
    ∀ {Γ A B p q G} →
    Ground G →
    0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ B →
    0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ G →
    Γ ⊢ B ~ ★

lower-bounds-consistentᶜ :
  ∀ {Γ A B C p q} →
  0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ B →
  0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ C →
  Γ ⊢ B ~ C
lower-bounds-consistentᶜ (⊢A-⊑-★ g p⊢) q⊢ =
  lower-bounds-star-leftᶜ g p⊢ q⊢
lower-bounds-consistentᶜ p⊢ (⊢A-⊑-★ g q⊢) =
  lower-bounds-star-rightᶜ g p⊢ q⊢
lower-bounds-consistentᶜ ⊢★-⊑-★ ⊢★-⊑-★ = ★-~-★
lower-bounds-consistentᶜ (⊢X-⊑-★ xν) (⊢X-⊑-★ yν) = ★-~-★
lower-bounds-consistentᶜ (⊢X-⊑-★ xν) (⊢X-⊑-X y∈) =
  ★-~-νX (left-ν-right-plain xν y∈)
lower-bounds-consistentᶜ (⊢X-⊑-X x∈) (⊢X-⊑-★ yν) =
  νX-~-★ (left-plain-right-ν x∈ yν)
lower-bounds-consistentᶜ (⊢X-⊑-X x∈) (⊢X-⊑-X y∈) =
  X-~-X (left-right-plain x∈ y∈)
lower-bounds-consistentᶜ (⊢α-⊑-α (wfSeal ())) q⊢
lower-bounds-consistentᶜ ⊢ι-⊑-ι ⊢ι-⊑-ι = ι-~-ι
lower-bounds-consistentᶜ (⊢A⇒B-⊑-A′⇒B′ p₁⊢ p₂⊢) (⊢A⇒B-⊑-A′⇒B′ q₁⊢ q₂⊢) =
  ⇒-~-⇒ (lower-bounds-consistentᶜ p₁⊢ q₁⊢)
         (lower-bounds-consistentᶜ p₂⊢ q₂⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢) =
  ∀-~-∀ (lower-bounds-consistentᶜ {Γ = X~X ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {C = C} (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-B wfC q⊢) =
  ∀-~-B
    (subst (λ n → WfTy n 0 C) (length-rightICtx Γ) wfC)
    (lower-bounds-consistentᶜ {Γ = X~★ ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {B = B} (⊢∀A-⊑-B wfB p⊢) (⊢∀A-⊑-∀B q⊢) =
  A-~-∀
    (subst (λ n → WfTy n 0 B) (length-leftICtx Γ) wfB)
    (lower-bounds-consistentᶜ {Γ = ★~X ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊢∀A-⊑-B wfB p⊢) (⊢∀A-⊑-B wfC q⊢) =
  drop-neither-~ (lower-bounds-consistentᶜ {Γ = neither ∷ Γ} p⊢ q⊢)

lower-bounds-consistent :
  ∀ {Δ A B C p q} →
  0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ extend-X⊑X Δ [] ⊢ q ⦂ A ⊑ C →
  extend-X~X Δ [] ⊢ B ~ C
lower-bounds-consistent
    {Δ = Δ} {A = A} {B = B} {C = C} {p = p} {q = q} p⊢ q⊢ =
  lower-bounds-consistentᶜ {Γ = extend-X~X Δ []}
    (subst (λ Φ → 0 ∣ Φ ⊢ p ⦂ A ⊑ B) (sym (leftICtx-extend-X~X[] Δ)) p⊢)
    (subst (λ Φ → 0 ∣ Φ ⊢ q ⦂ A ⊑ C) (sym (rightICtx-extend-X~X[] Δ)) q⊢)

sameCCtx : VarPrecCtx → CCtx
sameCCtx [] = []
sameCCtx (X⊑X ∷ Φ) = X~X ∷ sameCCtx Φ
sameCCtx (X⊑★ ∷ Φ) = neither ∷ sameCCtx Φ

leftICtx-sameCCtx : ∀ Φ → leftICtx (sameCCtx Φ) ≡ Φ
leftICtx-sameCCtx [] = refl
leftICtx-sameCCtx (X⊑X ∷ Φ) = cong (X⊑X ∷_) (leftICtx-sameCCtx Φ)
leftICtx-sameCCtx (X⊑★ ∷ Φ) = cong (X⊑★ ∷_) (leftICtx-sameCCtx Φ)

rightICtx-sameCCtx : ∀ Φ → rightICtx (sameCCtx Φ) ≡ Φ
rightICtx-sameCCtx [] = refl
rightICtx-sameCCtx (X⊑X ∷ Φ) = cong (X⊑X ∷_) (rightICtx-sameCCtx Φ)
rightICtx-sameCCtx (X⊑★ ∷ Φ) = cong (X⊑★ ∷_) (rightICtx-sameCCtx Φ)

length-sameCCtx : ∀ Φ → length (sameCCtx Φ) ≡ length Φ
length-sameCCtx [] = refl
length-sameCCtx (X⊑X ∷ Φ) = cong suc (length-sameCCtx Φ)
length-sameCCtx (X⊑★ ∷ Φ) = cong suc (length-sameCCtx Φ)

length-same-to-plain :
  ∀ Ω Φ →
  length (Ω ++ sameCCtx Φ) ≡
  length (Ω ++ extend-X~X (length Φ) [])
length-same-to-plain [] Φ =
  trans (length-sameCCtx Φ) (sym (length-extend-X~X[] (length Φ)))
length-same-to-plain (d ∷ Ω) Φ = cong suc (length-same-to-plain Ω Φ)

same-to-plain-X~X∋ᶜ :
  ∀ {Ω Φ X} →
  Ω ++ sameCCtx Φ ∋ᶜ X ∶ X~X →
  Ω ++ extend-X~X (length Φ) [] ∋ᶜ X ∶ X~X
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = []} ()
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} here = here
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} (there x∈) =
  there (same-to-plain-X~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = X⊑★ ∷ Φ} (there x∈) =
  there (same-to-plain-X~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~X∋ᶜ {Ω = d ∷ Ω} here = here
same-to-plain-X~X∋ᶜ {Ω = d ∷ Ω} (there x∈) =
  there (same-to-plain-X~X∋ᶜ {Ω = Ω} x∈)

same-to-plain-X~★∋ᶜ :
  ∀ {Ω Φ X} →
  Ω ++ sameCCtx Φ ∋ᶜ X ∶ X~★ →
  Ω ++ extend-X~X (length Φ) [] ∋ᶜ X ∶ X~★
same-to-plain-X~★∋ᶜ {Ω = []} {Φ = []} ()
same-to-plain-X~★∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} (there x∈) =
  there (same-to-plain-X~★∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~★∋ᶜ {Ω = []} {Φ = X⊑★ ∷ Φ} (there x∈) =
  there (same-to-plain-X~★∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~★∋ᶜ {Ω = d ∷ Ω} here = here
same-to-plain-X~★∋ᶜ {Ω = d ∷ Ω} (there x∈) =
  there (same-to-plain-X~★∋ᶜ {Ω = Ω} x∈)

same-to-plain-★~X∋ᶜ :
  ∀ {Ω Φ X} →
  Ω ++ sameCCtx Φ ∋ᶜ X ∶ ★~X →
  Ω ++ extend-X~X (length Φ) [] ∋ᶜ X ∶ ★~X
same-to-plain-★~X∋ᶜ {Ω = []} {Φ = []} ()
same-to-plain-★~X∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} (there x∈) =
  there (same-to-plain-★~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-★~X∋ᶜ {Ω = []} {Φ = X⊑★ ∷ Φ} (there x∈) =
  there (same-to-plain-★~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-★~X∋ᶜ {Ω = d ∷ Ω} here = here
same-to-plain-★~X∋ᶜ {Ω = d ∷ Ω} (there x∈) =
  there (same-to-plain-★~X∋ᶜ {Ω = Ω} x∈)

same-to-plain-WfTy :
  ∀ {Ω Φ A} →
  WfTy (length (Ω ++ sameCCtx Φ)) 0 A →
  WfTy (length (Ω ++ extend-X~X (length Φ) [])) 0 A
same-to-plain-WfTy {Ω = Ω} {Φ = Φ} wfA =
  subst (λ n → WfTy n 0 _) (length-same-to-plain Ω Φ) wfA

same-to-plain-~ :
  ∀ {Ω Φ A B} →
  Ω ++ sameCCtx Φ ⊢ A ~ B →
  Ω ++ extend-X~X (length Φ) [] ⊢ A ~ B
same-to-plain-~ ★-~-★ = ★-~-★
same-to-plain-~ {Ω = Ω} {Φ = Φ} (X-~-X x∈) =
  X-~-X (same-to-plain-X~X∋ᶜ {Ω = Ω} {Φ = Φ} x∈)
same-to-plain-~ ι-~-ι = ι-~-ι
same-to-plain-~ {Ω = Ω} {Φ = Φ} (⇒-~-⇒ A~A′ B~B′) =
  ⇒-~-⇒ (same-to-plain-~ {Ω = Ω} {Φ = Φ} A~A′)
         (same-to-plain-~ {Ω = Ω} {Φ = Φ} B~B′)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (∀-~-∀ A~B) =
  ∀-~-∀ (same-to-plain-~ {Ω = X~X ∷ Ω} {Φ = Φ} A~B)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (A-~-★ n★ n∀ g A~G) =
  A-~-★ n★ n∀ g (same-to-plain-~ {Ω = Ω} {Φ = Φ} A~G)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (★-~-B n★ n∀ g G~B) =
  ★-~-B n★ n∀ g (same-to-plain-~ {Ω = Ω} {Φ = Φ} G~B)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (νX-~-★ x∈) =
  νX-~-★ (same-to-plain-X~★∋ᶜ {Ω = Ω} {Φ = Φ} x∈)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (★-~-νX x∈) =
  ★-~-νX (same-to-plain-★~X∋ᶜ {Ω = Ω} {Φ = Φ} x∈)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (∀-~-B wfB A~⇑B) =
  ∀-~-B (same-to-plain-WfTy {Ω = Ω} {Φ = Φ} wfB)
    (same-to-plain-~ {Ω = X~★ ∷ Ω} {Φ = Φ} A~⇑B)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (A-~-∀ wfA ⇑A~B) =
  A-~-∀ (same-to-plain-WfTy {Ω = Ω} {Φ = Φ} wfA)
    (same-to-plain-~ {Ω = ★~X ∷ Ω} {Φ = Φ} ⇑A~B)

lower-bounds-consistentᵢ :
  ∀ {Φ A B C p q} →
  0 ∣ Φ ⊢ p ⦂ A ⊑ B →
  0 ∣ Φ ⊢ q ⦂ A ⊑ C →
  extend-X~X (length Φ) [] ⊢ B ~ C
lower-bounds-consistentᵢ {Φ = Φ} {A = A} {B = B} {C = C} {p = p} {q = q} p⊢ q⊢ =
  same-to-plain-~ {Ω = []} {Φ = Φ}
    (lower-bounds-consistentᶜ {Γ = sameCCtx Φ}
      (subst (λ Ψ → 0 ∣ Ψ ⊢ p ⦂ A ⊑ B) (sym (leftICtx-sameCCtx Φ)) p⊢)
      (subst (λ Ψ → 0 ∣ Ψ ⊢ q ⦂ A ⊑ C) (sym (rightICtx-sameCCtx Φ)) q⊢))

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

plain≤ᵢ :
  ∀ {Δ Φ} →
  length Φ ≡ Δ →
  extend-X⊑X Δ [] ≤ᵢ Φ
plain≤ᵢ {Δ = zero} {Φ = []} refl = []≤ᵢ
plain≤ᵢ {Δ = zero} {Φ = X⊑X ∷ Φ} ()
plain≤ᵢ {Δ = zero} {Φ = X⊑★ ∷ Φ} ()
plain≤ᵢ {Δ = suc Δ} {Φ = []} ()
plain≤ᵢ {Δ = suc Δ} {Φ = X⊑X ∷ Φ} len =
  X⊑X≤X⊑X ∷≤ᵢ plain≤ᵢ (suc-injective len)
plain≤ᵢ {Δ = suc Δ} {Φ = X⊑★ ∷ Φ} len =
  X⊑X≤ν ∷≤ᵢ plain≤ᵢ (suc-injective len)

coerce-glbᵢ :
  ∀ {Φ A C B B′ p⊒ p⊑ pA pC} →
  (A~C : extend-X~X (length Φ) [] ⊢ A ~ C) →
  0 ∣ extend-X⊑X (length Φ) [] ⊢ p⊒ ⦂ B ⊑ A →
  0 ∣ extend-X⊑X (length Φ) [] ⊢ p⊑ ⦂ B ⊑ C →
  0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A →
  0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C →
  p⊒ ≡ coerce-⊒ A~C →
  p⊑ ≡ coerce-⊑ A~C →
  ∃[ r ] 0 ∣ Φ ⊢ r ⦂ B′ ⊑ B
coerce-glbᵢ {Φ = Φ} {A = A} {C = C} {B = B}
    {B′ = B′} {p⊒ = p⊒} {p⊑ = p⊑} A~C p⊒⊢ p⊑⊢ pA⊢ pC⊢
    eq⊒ eq⊑ =
  coerce-glbᶜ {Γ = extend-X~X (length Φ) []} {Φ = Φ}
    A~C
    (subst (λ Ψ → Ψ ≤ᵢ Φ)
      (sym (leftICtx-extend-X~X[] (length Φ))) (plain≤ᵢ refl))
    (subst (λ Ψ → Ψ ≤ᵢ Φ)
      (sym (rightICtx-extend-X~X[] (length Φ))) (plain≤ᵢ refl))
    (subst (λ Ψ → 0 ∣ Ψ ⊢ p⊒ ⦂ B ⊑ A)
      (sym (leftICtx-extend-X~X[] (length Φ))) p⊒⊢)
    (subst (λ Ψ → 0 ∣ Ψ ⊢ p⊑ ⦂ B ⊑ C)
      (sym (rightICtx-extend-X~X[] (length Φ))) p⊑⊢)
    pA⊢ pC⊢ eq⊒ eq⊑

app-consistencyᵢ :
  ∀ {Δ Φ A A′ B B′ p q} →
  length Φ ≡ Δ →
  0 ∣ Φ ⊢ p ⦂ A ⊑ B →
  extend-X~X Δ [] ⊢ A ~ A′ →
  0 ∣ Φ ⊢ q ⦂ A′ ⊑ B′ →
  extend-X~X Δ [] ⊢ B ~ B′
app-consistencyᵢ {Δ = Δ} {Φ = Φ} len p⊢ A~A′ q⊢
    with coerce-wt-extend-X⊑X A~A′
app-consistencyᵢ {Δ = Δ} {Φ = Φ} len p⊢ A~A′ q⊢ | C , C⊑A , C⊑A′
    with trans-ctx-⊑ (plain≤ᵢ len) C⊑A p⊢
       | trans-ctx-⊑ (plain≤ᵢ len) C⊑A′ q⊢
app-consistencyᵢ {Φ = Φ} len p⊢ A~A′ q⊢ | C , C⊑A , C⊑A′
    | r , C⊑B | s , C⊑B′ =
  subst (λ n → extend-X~X n [] ⊢ _ ~ _) len
    (lower-bounds-consistentᵢ C⊑B C⊑B′)

module proof.DenotCast where

-- File Charter:
--   * The eight cast lemmas of the denotational proof of graduality
--     (PolyG/notes/denotational-graduality.md, Section 8), one per cast
--     rule of TermPrecision.agda (⊑upL, ⊑downL, ⊑upR, ⊑downR) and per
--     relation (reflection ▹, preservation ◃ of proof/DenotRelation.agda).
--     The derivations satisfy AB : A ⊑ B, BC : B ⊑ C, AC : A ⊑ C at n
--     type variables, interpreted by the seal environment θ.
--       upL▹, downL▹   a cast on the left: the left values are any finite
--                      list of outputs of the cast applied to a related
--                      list L;
--       upR▹, downR▹   a cast on the right: a related list is related to
--                      the cast's outputs;
--       upL◃, downL◃   a cast on the left: the left errs, or the cast's
--                      outputs are related (the left set is consistent);
--       upR◃, downR◃   a cast on the right: the cast does not err, and any
--                      finite list of its outputs is related.
--   * By induction on the derivations.  When BC ends in tag, the tag is
--     peeled off BC and AC (AC is the composite of AB and BC by
--     uniqueness of derivations).  The function and ∀ cases are generic
--     in the direction (L▹⇒, L▹∀, R▹⇒, R▹∀, L◃⇒, L◃∀, R◃⇒, R◃∀): the
--     arguments go through the flipped lemma, the original entries are
--     applied jointly to a sublist selected by finite support, and the
--     results go through the lemma itself.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Sublist.Propositional
  using ([]; _∷_; _∷ʳ_) renaming (_⊆_ to _⊑ˢ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Function.Bundles using (Equivalence)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Terms using (Dir; up; down; flip)
open import GraphModel
open import Denotation
open import proof.PrecisionProps
  using (⊑-unique; ⊑-trans; idᵖ-⊢; groundTy-wf)
open import proof.DenotRelation
open import proof.DenotCastProps
open import proof.DenotRelationProps

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- AC is the composite of AB and BC, so it ends in the tag of BC
tag-split : ∀ {n AB BC₀ AC A B G}
  → n ⊢ AB ⦂ A ⊑ B → WfGround n G → n ⊢ BC₀ ⦂ B ⊑ groundTy G
  → n ⊢ AC ⦂ A ⊑ ★
  → Σ[ AC′ ∈ Prec ] (n ⊢ AC′ ⦂ A ⊑ groundTy G × AC ≡ tag G AC′)
tag-split AB⊢ wfG BC₀⊢ AC⊢ with ⊑-trans AB⊢ BC₀⊢
tag-split AB⊢ wfG BC₀⊢ AC⊢ | AC′ , AC′⊢ =
  AC′ , AC′⊢ , ⊑-unique AC⊢ (⊑tag wfG AC′⊢)

▹-tag-in : ∀ {θ W G p D′} L → W ∣ θ ⊢ p ⊢ L ▹ untag (⟦ G ⟧ᴳ θ) D′
  → W ∣ θ ⊢ tag G p ⊢ L ▹ D′
▹-tag-in [] rel = tt₁
▹-tag-in (v ∷ L) rel = rel

▹-tag-out : ∀ {θ W G p D′} L → W ∣ θ ⊢ tag G p ⊢ L ▹ D′
  → W ∣ θ ⊢ p ⊢ L ▹ untag (⟦ G ⟧ᴳ θ) D′
▹-tag-out [] rel = tt₁
▹-tag-out (v ∷ L) rel = rel

▹-empty : ∀ {k W θ p L D′} → (∀ x → x ⋵ L → ⊥) → sizeᴸ L < k
  → Rel▹ k W θ p L D′
▹-empty {k} {L = L} none sL =
  ▹-⊆ 0 1 k {L = []} {L₂ = L} (λ v ()) (s≤s z≤n) sL
    (λ x x∈ → ⊥-elim (none x x∈)) tt₁

◃-empty : ∀ {k W θ p D L} → (∀ x → x ⋵ L → ⊥) → sizeᴸ L < k
  → Rel◃ k W θ p D L
◃-empty {k} {L = L} none sL =
  ◃-⊆ 0 1 k {L = []} {L₂ = L} (λ v ()) (s≤s z≤n) sL
    (λ x x∈ → ⊥-elim (none x x∈)) tt₁

All-tab : ∀ {P : Val → Set} L → (∀ x → x ⋵ L → P x) → All P L
All-tab [] h = []
All-tab (x ∷ L) h = h x (here refl) ∷ All-tab L (λ y y∈ → h y (there y∈))

fun-out : ∀ d p q θ E {m m′} x → x ∈ ⌊ ⟦ d , p ⇒⊑ q ⟧ᶜ θ E m ⌋ m′
  → νλ ∈ E × x ∈ Λ (c-⇒F d p q θ E)
fun-out d p q θ E x (w∈ , eq , x∈) = w∈ , x∈

poly-out : ∀ d p θ E {m m′} x → x ∈ ⌊ ⟦ d , ∀⊑ p ⟧ᶜ θ E m ⌋ m′
  → ν∀ ∈ E × x ∈ Λᴾ (c-∀F d p θ E)
poly-out d p θ E x (w∈ , eq , x∈) = w∈ , x∈

Λ-IsFun : ∀ {F} x → x ∈ Λ F → IsFun x
Λ-IsFun vtrue ()
Λ-IsFun vfalse ()
Λ-IsFun (sealᵛ σ u) ()
Λ-IsFun (injᵛ G u) ()
Λ-IsFun (U ⟼ r at m) x∈ = is-entry
Λ-IsFun (σ ⟼∀ r) ()
Λ-IsFun νλ x∈ = is-νλ
Λ-IsFun ν∀ ()

Λᴾ-IsPoly : ∀ {F} x → x ∈ Λᴾ F → IsPoly x
Λᴾ-IsPoly vtrue ()
Λᴾ-IsPoly vfalse ()
Λᴾ-IsPoly (sealᵛ σ u) ()
Λᴾ-IsPoly (injᵛ G u) ()
Λᴾ-IsPoly (U ⟼ r at m) ()
Λᴾ-IsPoly (σ ⟼∀ r) x∈ = is-pentry
Λᴾ-IsPoly νλ ()
Λᴾ-IsPoly ν∀ x∈ = is-ν∀

●-arg-conv : ∀ {D E m} r → r ∈ᴿ (D ●[ m ] E) → Conv E
●-arg-conv r ([] , e∈ , U⊆ , U≢) = ⊥-elim (U≢ refl)
●-arg-conv r ((u ∷ U) , e∈ , U⊆ , U≢) = u , U⊆ u (here refl)

-- the values of a function cast's body at counter m₃
⇒F-inv : ∀ d p q θ X Y m′ {y m₃} → ret y m₃ ∈ᴿ c-⇒F d p q θ X Y m′
  → ret y m₃ ∈ᴿ
    ⟦ d , q ⟧ᶜ θ (⌊ X ●[ m′ ] ⌊ ⟦ flip d , p ⟧ᶜ θ Y m′ ⌋ m′ ⌋ m₃) m₃
⇒F-inv d p q θ X Y m′ (inj₁ (() , e∈))
⇒F-inv d p q θ X Y m′ (inj₂ (m₂ , (c , c∈) , r∈))
  with c-ctr (flip d) p θ c∈
⇒F-inv d p q θ X Y m′ (inj₂ (m₂ , (c , c∈) , inj₁ (() , e∈))) | refl
⇒F-inv d p q θ X Y m′ (inj₂ (m₂ , (c , c∈) , inj₂ (m₄ , c₄ , y∈)))
  | refl with c-ctr d q θ y∈
... | refl = y∈

-- the errors of a function cast's body
⇒F-err : ∀ d p q θ X Y m′ → err ∈ᴿ c-⇒F d p q θ X Y m′
  → err ∈ᴿ ⟦ flip d , p ⟧ᶜ θ Y m′
    ⊎ (err ∈ᴿ (X ●[ m′ ] ⌊ ⟦ flip d , p ⟧ᶜ θ Y m′ ⌋ m′)
       ⊎ Σ[ m₃ ∈ ℕ ] (Conv (⌊ X ●[ m′ ] ⌊ ⟦ flip d , p ⟧ᶜ θ Y m′ ⌋ m′ ⌋ m₃)
         × err ∈ᴿ ⟦ d , q ⟧ᶜ θ
                    (⌊ X ●[ m′ ] ⌊ ⟦ flip d , p ⟧ᶜ θ Y m′ ⌋ m′ ⌋ m₃) m₃))
⇒F-err d p q θ X Y m′ (inj₁ (refl , e∈)) = inj₁ e∈
⇒F-err d p q θ X Y m′ (inj₂ (m₂ , (c , c∈) , r∈))
  with c-ctr (flip d) p θ c∈
⇒F-err d p q θ X Y m′ (inj₂ (m₂ , (c , c∈) , inj₁ (refl , e∈))) | refl =
  inj₂ (inj₁ e∈)
⇒F-err d p q θ X Y m′ (inj₂ (m₂ , (c , c∈) , inj₂ (m₄ , c₄ , e∈)))
  | refl = inj₂ (inj₂ (m₄ , c₄ , e∈))

∀F-inv : ∀ d p θ X σ {y m₃} → ret y m₃ ∈ᴿ c-∀F d p θ X σ
  → ret y m₃ ∈ᴿ ⟦ d , p ⟧ᶜ (σ •ᵗ θ) (⌊ X ◆ σ ⌋ m₃) m₃
∀F-inv d p θ X σ (inj₁ (() , e∈))
∀F-inv d p θ X σ (inj₂ (m₄ , c , y∈)) with c-ctr d p (σ •ᵗ θ) y∈
... | refl = y∈

-- the entries of D used by a finite list of values of D ●[ m′ ] E at m₃
entries : ∀ {D E m′ m₃} Z → mem Z ⊆ ⌊ D ●[ m′ ] E ⌋ m₃
  → Σ[ P ∈ List Val ]
      (mem P ⊆ D
       × (∀ e → e ⋵ P → Σ[ V ∈ List Val ] Σ[ z ∈ Val ]
            (e ≡ (V ⟼ ret z m₃ at m′) × mem V ⊆ E))
       × (∀ z → z ⋵ Z → Σ[ V ∈ List Val ] ((V ⟼ ret z m₃ at m′) ⋵ P)))
entries [] Z⊆ = [] , c-[]-⊆ , (λ e ()) , (λ z ())
entries {m′ = m′} {m₃} (z ∷ Z) Z⊆ with Z⊆ z (here refl)
  | entries Z (λ y y∈ → Z⊆ y (there y∈))
entries {m′ = m′} {m₃} (z ∷ Z) Z⊆ | V , e∈ , V⊆ , V≢ | P , P⊆ , Pg , Pc =
  (V ⟼ ret z m₃ at m′) ∷ P , c-∷-⊆ e∈ P⊆ , good , cov
  where
  good : ∀ e → e ⋵ ((V ⟼ ret z m₃ at m′) ∷ P)
    → Σ[ V′ ∈ List Val ] Σ[ z′ ∈ Val ]
        (e ≡ (V′ ⟼ ret z′ m₃ at m′) × mem V′ ⊆ _)
  good e (here refl) = V , z , refl , V⊆
  good e (there e∈′) = Pg e e∈′
  cov : ∀ y → y ⋵ (z ∷ Z)
    → Σ[ V′ ∈ List Val ] ((V′ ⟼ ret y m₃ at m′) ⋵
                           ((V ⟼ ret z m₃ at m′) ∷ P))
  cov y (here refl) = V , here refl
  cov y (there y∈) with Pc y y∈
  cov y (there y∈) | V′ , e∈′ = V′ , there e∈′

entry-args : ∀ {U V r s m m′ E} → (U ⟼ r at m) ≡ (V ⟼ s at m′)
  → mem V ⊆ E → mem U ⊆ E
entry-args refl V⊆ = V⊆

-- converting between fuels
▹-in : ∀ {k W θ p} L {D′} → sizeᴸ L < k → W ∣ θ ⊢ p ⊢ L ▹ D′
  → Rel▹ k W θ p L D′
▹-in {k} {W} {θ} {p} L {D′} sk =
  ▹-fuel (suc (sizeᴸ L)) k {W} {θ} {p} {L} {D′} ≤-refl sk

▹-out : ∀ {k W θ p} L {D′} → sizeᴸ L < k → Rel▹ k W θ p L D′
  → W ∣ θ ⊢ p ⊢ L ▹ D′
▹-out {k} {W} {θ} {p} L {D′} sk =
  ▹-fuel k (suc (sizeᴸ L)) {W} {θ} {p} {L} {D′} sk ≤-refl

◃-in : ∀ {k W θ p D} L → sizeᴸ L < k → W ∣ θ ⊢ p ⊢ D ◃ L
  → Rel◃ k W θ p D L
◃-in {k} {W} {θ} {p} {D} L sk =
  ◃-fuel (suc (sizeᴸ L)) k {W} {θ} {p} {D} {L} ≤-refl sk

◃-out : ∀ {k W θ p D} L → sizeᴸ L < k → Rel◃ k W θ p D L
  → W ∣ θ ⊢ p ⊢ D ◃ L
◃-out {k} {W} {θ} {p} {D} L sk =
  ◃-fuel k (suc (sizeᴸ L)) {W} {θ} {p} {D} {L} sk ≤-refl

-- the values at m₃ of the results of a sublist are smaller than the list
values-results-< : ∀ m₃ m′ {L₀} v L → L₀ ⊑ˢ (v ∷ L)
  → sizeᴸ (valuesAt m₃ (resultsAt m′ L₀)) < sizeᴸ (v ∷ L)
values-results-< m₃ m′ {L₀} v L s =
  ≤-<-trans (values-≤ m₃ (resultsAt m′ L₀)) (results-sub-< m′ v L s)

values-bodies-< : ∀ m₃ σ v L
  → sizeᴸ (valuesAt m₃ (bodiesAt σ (v ∷ L))) < sizeᴸ (v ∷ L)
values-bodies-< m₃ σ v L =
  ≤-<-trans (values-≤ m₃ (bodiesAt σ (v ∷ L))) (bodies-< σ v L)

------------------------------------------------------------------------
-- Reflection, a cast on the left
------------------------------------------------------------------------

id▹L : ∀ {θ W p L D′ m} → W ∣ θ ⊢ p ⊢ L ▹ D′
  → ∀ L₁ → mem L₁ ⊆ ⌊ retᴿ (mem L) m ⌋ m → W ∣ θ ⊢ p ⊢ L₁ ▹ D′
id▹L rel L₁ L₁⊆ = ▹-sub⊆ (λ x x∈ → proj₂ (L₁⊆ x x∈)) rel

L▹⇒ : ∀ d {θ W AB₁ AB₂ H₁ H₂ K₁ K₂ L D′ m}
  → (∀ {W′ A E′ k} → W′ ∣ θ ⊢ K₁ ⊢ A ▹ E′
       → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ flip d , AB₁ ⟧ᶜ θ (mem A) k ⌋ k
       → W′ ∣ θ ⊢ H₁ ⊢ L₁ ▹ E′)
  → (∀ {W′ X E′ k} → W′ ∣ θ ⊢ H₂ ⊢ X ▹ E′
       → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ d , AB₂ ⟧ᶜ θ (mem X) k ⌋ k
       → W′ ∣ θ ⊢ K₂ ⊢ L₁ ▹ E′)
  → W ∣ θ ⊢ H₁ ⇒⊑ H₂ ⊢ L ▹ D′
  → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ d , AB₁ ⇒⊑ AB₂ ⟧ᶜ θ (mem L) m ⌋ m
  → W ∣ θ ⊢ K₁ ⇒⊑ K₂ ⊢ L₁ ▹ D′
L▹⇒ d argIH resIH rel [] L₁⊆ = tt₁
L▹⇒ d {θ} {AB₁ = AB₁} {AB₂} {L = []} argIH resIH rel (v₁ ∷ L₁) L₁⊆ =
  ⊥-elim (∉[] (proj₁ (fun-out d AB₁ AB₂ θ (mem []) v₁ (L₁⊆ v₁ (here refl)))))
L▹⇒ d {θ} {W} {AB₁} {AB₂} {H₁} {H₂} {K₁} {K₂} {v ∷ L} {D′} {m}
    argIH resIH (lift all , lift ν∈ , f) (v₁ ∷ L₁) L₁⊆ =
  lift (All-tab (v₁ ∷ L₁)
          (λ x x∈ → Λ-IsFun {F = c-⇒F d AB₁ AB₂ θ (mem (v ∷ L))} x
             (proj₂ (fun-out d AB₁ AB₂ θ (mem (v ∷ L)) x (L₁⊆ x x∈))))) ,
  lift ν∈ , g
  where
  g : ∀ L₁₀ → L₁₀ ⊑ˢ (v₁ ∷ L₁) → ∀ m′ W′ → W ⊑ʷ W′ → length W′ ≡ m′
    → ∀ E′ → Consistent E′
    → Rel▹ (sizeᴸ (v₁ ∷ L₁)) W′ θ K₁ (argsAt m′ L₁₀) E′
    → Rel▹ᶜ (sizeᴸ (v₁ ∷ L₁)) W′ θ K₂ (resultsAt m′ L₁₀) (D′ ●[ m′ ] E′)
  g L₁₀ s m′ W′ ext len E′ CE′ relA m₃ ne₃ = result
    where
    A = argsAt m′ L₁₀
    E₁ = ⌊ ⟦ flip d , AB₁ ⟧ᶜ θ (mem A) m′ ⌋ m′
    S = ⌊ mem (v ∷ L) ●[ m′ ] E₁ ⌋ m₃
    Rs = resultsAt m′ L₁₀
    Ys = valuesAt m₃ Rs
    relA′ : W′ ∣ θ ⊢ K₁ ⊢ A ▹ E′
    relA′ = ▹-out A (args-sub-< m′ v₁ L₁ s) relA
    hY : ∀ y → y ⋵ Ys → ret y m₃ ∈ᴿ ⟦ d , AB₂ ⟧ᶜ θ S m₃
    hY y y∈ with results-∈⁻ L₁₀ (values-∈⁻ Rs y∈)
    hY y y∈ | U , e∈
      with fun-out d AB₁ AB₂ θ (mem (v ∷ L)) (U ⟼ ret y m₃ at m′)
             (L₁⊆ _ (sub-mem s _ e∈))
    hY y y∈ | U , e∈ | ν∈L , (r∈ , U≢ , U≈) =
      ⇒F-inv d AB₁ AB₂ θ (mem (v ∷ L)) (mem A) m′
        (c-⇒body-mono d AB₁ AB₂ θ (mem (v ∷ L)) m′ {mem U} {mem A}
           (λ u u∈ → args-∈⁺ e∈ u∈) (ret y m₃) r∈)
    col = c-collect {Φ = λ X → ⟦ d , AB₂ ⟧ᶜ θ X m₃} {X = S} {m = m₃}
            (c-fin d AB₂ θ m₃) (c-mono d AB₂ θ m₃) Ys hY
    Z = proj₁ col
    ent = entries {D = mem (v ∷ L)} {E = E₁} {m′ = m′} {m₃ = m₃} Z
            (proj₁ (proj₂ col))
    P = proj₁ ent
    sel = select (v ∷ L) P (proj₁ (proj₂ ent))
    L₀ = proj₁ sel
    s₀ = proj₁ (proj₂ sel)
    argsOK : mem (argsAt m′ L₀) ⊆ E₁
    argsOK u u∈ with args-∈⁻ L₀ u∈
    argsOK u u∈ | U , r , e∈ , u∈U
      with proj₁ (proj₂ (proj₂ ent)) _ (proj₁ (proj₂ (proj₂ sel)) _ e∈)
    argsOK u u∈ | U , r , e∈ , u∈U | V , z , eq , V⊆ =
      entry-args eq V⊆ u u∈U
    X₃ = valuesAt m₃ (resultsAt m′ L₀)
    Z⊆X : mem Z ⊆ mem X₃
    Z⊆X z z∈ with proj₂ (proj₂ (proj₂ ent)) z z∈
    Z⊆X z z∈ | V , e∈P =
      values-∈⁺ (results-∈⁺ (proj₂ (proj₂ (proj₂ sel)) _ e∈P))
    neX : X₃ ≢ []
    neX with ne-head Ys ne₃
    neX | y₀ , y₀∈ with c-nonempty d AB₂ θ (ret y₀ m₃)
                         (proj₂ (proj₂ col) y₀ y₀∈)
    neX | y₀ , y₀∈ | z₀ , z₀∈ = nonempty (Z⊆X z₀ z₀∈)
    hyp : Rel▹ᶜ (sizeᴸ (v ∷ L)) W′ θ H₂ (resultsAt m′ L₀) (D′ ●[ m′ ] E′)
    hyp = f L₀ s₀ m′ W′ ext len E′ CE′
            (▹-in (argsAt m′ L₀) (args-sub-< m′ v L s₀)
               (argIH {W′} {A} {E′} {m′} relA′ (argsAt m′ L₀) argsOK))
    result : Σ[ W₃ ∈ World ] (Lift₁ (W′ ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m₃)
               × Rel▹ (sizeᴸ (v₁ ∷ L₁)) W₃ θ K₂ Ys (⌊ D′ ●[ m′ ] E′ ⌋ m₃))
    result with hyp m₃ neX
    result | W₃ , ext₃ , len₃ , rel₃ =
      W₃ , ext₃ , len₃ ,
      ▹-in Ys (values-results-< m₃ m′ v₁ L₁ s)
        (resIH {W₃} {X₃} {⌊ D′ ●[ m′ ] E′ ⌋ m₃} {m₃}
           (▹-out X₃ (values-results-< m₃ m′ v L s₀) rel₃) Ys
           (λ y y∈ → c-mono d AB₂ θ m₃ Z⊆X (ret y m₃)
                       (proj₂ (proj₂ col) y y∈)))

L▹∀ : ∀ d {θ W AB₀ H₀ K₀ L D′ m}
  → (∀ σ {W′ X E′ k} → W′ ∣ σ •ᵗ θ ⊢ H₀ ⊢ X ▹ E′
       → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ) (mem X) k ⌋ k
       → W′ ∣ σ •ᵗ θ ⊢ K₀ ⊢ L₁ ▹ E′)
  → W ∣ θ ⊢ ∀⊑ H₀ ⊢ L ▹ D′
  → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ d , ∀⊑ AB₀ ⟧ᶜ θ (mem L) m ⌋ m
  → W ∣ θ ⊢ ∀⊑ K₀ ⊢ L₁ ▹ D′
L▹∀ d bodyIH rel [] L₁⊆ = tt₁
L▹∀ d {θ} {AB₀ = AB₀} {L = []} bodyIH rel (v₁ ∷ L₁) L₁⊆ =
  ⊥-elim (∉[] (proj₁ (poly-out d AB₀ θ (mem []) v₁ (L₁⊆ v₁ (here refl)))))
L▹∀ d {θ} {W} {AB₀} {H₀} {K₀} {v ∷ L} {D′} {m}
    bodyIH (lift all , lift ν∈ , f) (v₁ ∷ L₁) L₁⊆ =
  lift (All-tab (v₁ ∷ L₁)
          (λ x x∈ → Λᴾ-IsPoly {F = c-∀F d AB₀ θ (mem (v ∷ L))} x
             (proj₂ (poly-out d AB₀ θ (mem (v ∷ L)) x (L₁⊆ x x∈))))) ,
  lift ν∈ , g
  where
  g : ∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
    → Rel▹ᶜ (sizeᴸ (v₁ ∷ L₁)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) K₀
        (bodiesAt σ (v₁ ∷ L₁)) (D′ ◆ σ)
  g σ W′ q′ ext len m₃ ne₃ = result
    where
    Ys = valuesAt m₃ (bodiesAt σ (v₁ ∷ L₁))
    X₃ = valuesAt m₃ (bodiesAt σ (v ∷ L))
    S⊆X : ⌊ mem (v ∷ L) ◆ σ ⌋ m₃ ⊆ mem X₃
    S⊆X x x∈ = values-∈⁺ (bodies-∈⁺ x∈)
    hY : ∀ y → y ⋵ Ys
      → ret y m₃ ∈ᴿ ⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ) (⌊ mem (v ∷ L) ◆ σ ⌋ m₃) m₃
    hY y y∈ =
      ∀F-inv d AB₀ θ (mem (v ∷ L)) σ
        (proj₂ (poly-out d AB₀ θ (mem (v ∷ L)) (σ ⟼∀ ret y m₃)
           (L₁⊆ _ (bodies-∈⁻ (v₁ ∷ L₁)
                    (values-∈⁻ (bodiesAt σ (v₁ ∷ L₁)) y∈)))))
    neX : X₃ ≢ []
    neX with ne-head Ys ne₃
    neX | y₀ , y₀∈ with c-nonempty d AB₀ (σ •ᵗ θ) (ret y₀ m₃) (hY y₀ y₀∈)
    neX | y₀ , y₀∈ | x₀ , x₀∈ = nonempty (S⊆X x₀ x₀∈)
    result : Σ[ W₃ ∈ World ] (Lift₁ (W′ ++ (q′ ∷ []) ⊑ʷ W₃)
               × Lift₁ (length W₃ ≡ m₃)
               × Rel▹ (sizeᴸ (v₁ ∷ L₁)) W₃ (σ •ᵗ θ) K₀ Ys (⌊ D′ ◆ σ ⌋ m₃))
    result with f σ W′ q′ ext len m₃ neX
    result | W₃ , ext₃ , len₃ , rel₃ =
      W₃ , ext₃ , len₃ ,
      ▹-in Ys (values-bodies-< m₃ σ v₁ L₁)
        (bodyIH σ {W₃} {X₃} {⌊ D′ ◆ σ ⌋ m₃} {m₃}
           (▹-out X₃ (values-bodies-< m₃ σ v L) rel₃) Ys
           (λ y y∈ → c-mono d AB₀ (σ •ᵗ θ) m₃ S⊆X (ret y m₃) (hY y y∈)))

-- an up cast through tag G on the left, landing in ★
up-tag▹L : ∀ {θ W G AB₀ L D′ m}
  → (W ∣ θ ⊢ AB₀ ⊢ L ▹ untag (⟦ G ⟧ᴳ θ) D′
     → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ up , AB₀ ⟧ᶜ θ (mem L) m ⌋ m
     → W ∣ θ ⊢ idᵖ (groundTy G) ⊢ L₁ ▹ untag (⟦ G ⟧ᴳ θ) D′)
  → W ∣ θ ⊢ tag G AB₀ ⊢ L ▹ D′
  → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ up , tag G AB₀ ⟧ᶜ θ (mem L) m ⌋ m
  → W ∣ θ ⊢ ★⊑ ⊢ L₁ ▹ D′
up-tag▹L IH rel [] L₁⊆ = tt₁
up-tag▹L {θ} {W} {G} {AB₀} {L} {D′} {m} IH rel (v₁ ∷ L₁) L₁⊆ =
  lift (All-tab (v₁ ∷ L₁) isInj) , pay
  where
  G′ = ⟦ G ⟧ᴳ θ
  out : ∀ x → x ⋵ (v₁ ∷ L₁)
    → Σ[ u ∈ Val ] (x ≡ injᵛ G′ u × u ∈ ⌊ ⟦ up , AB₀ ⟧ᶜ θ (mem L) m ⌋ m)
  out x x∈ with L₁⊆ x x∈
  out x x∈ | inj₁ (() , e∈)
  out x x∈ | inj₂ (m₁ , c , x∈′) with c-inj-ret-inv (ret x m) x∈′
  out x x∈ | inj₂ (m₁ , c , x∈′) | u , refl , u∈ = u , refl , u∈
  isInj : ∀ x → x ⋵ (v₁ ∷ L₁) → IsInj x
  isInj x x∈ with out x x∈
  isInj x x∈ | u , refl , u∈ = is-inj
  pay : ∀ H → Rel▹ (sizeᴸ (v₁ ∷ L₁)) W θ₀ (gp H)
                (untagᴸ H (v₁ ∷ L₁)) (untag H D′)
  pay H with H ≟G G′
  pay H | yes refl =
    ▹-fuel (suc (sizeᴸ P)) (sizeᴸ (v₁ ∷ L₁))
      {W} {θ₀} {gp G′} {P} {untag G′ D′} ≤-refl (untag-< G′ v₁ L₁)
      (from (gp-▹ (suc (sizeᴸ P)) θ G {W} {P} {untag G′ D′})
        (IH (▹-tag-out {θ} {W} {G} {AB₀} {D′} L rel) P P⊆))
    where
    P = untagᴸ G′ (v₁ ∷ L₁)
    P⊆ : mem P ⊆ ⌊ ⟦ up , AB₀ ⟧ᶜ θ (mem L) m ⌋ m
    P⊆ u u∈ with out _ (untag-∈⁻ (v₁ ∷ L₁) u∈)
    P⊆ u u∈ | u′ , refl , u′∈ = u′∈
  pay H | no H≢ =
    ▹-empty (λ u u∈ → none u (untag-∈⁻ (v₁ ∷ L₁) u∈)) (untag-< H v₁ L₁)
    where
    none : ∀ u → injᵛ H u ⋵ (v₁ ∷ L₁) → ⊥
    none u u∈ with out _ u∈
    none u u∈ | u′ , refl , u′∈ = H≢ refl

-- the payloads tagged ⟦ G ⟧ᴳ θ of a list related at ★
★-payloads : ∀ {θ W D′} G L → W ∣ θ ⊢ ★⊑ ⊢ L ▹ D′
  → W ∣ θ ⊢ idᵖ (groundTy G) ⊢ untagᴸ (⟦ G ⟧ᴳ θ) L ▹ untag (⟦ G ⟧ᴳ θ) D′
★-payloads G [] rel = tt₁
★-payloads {θ} {W} {D′} G (v ∷ L) rel =
  to (gp-▹ (suc (sizeᴸ (untagᴸ G′ (v ∷ L)))) θ G
        {W} {untagᴸ G′ (v ∷ L)} {untag G′ D′})
    (▹-fuel (sizeᴸ (v ∷ L)) (suc (sizeᴸ (untagᴸ G′ (v ∷ L))))
       {W} {θ₀} {gp G′} {untagᴸ G′ (v ∷ L)} {untag G′ D′}
       (untag-< G′ v L) ≤-refl (proj₂ rel G′))
  where
  G′ = ⟦ G ⟧ᴳ θ

-- a down cast through tag G on the left, from ★
down-tag▹L : ∀ {θ W G AB₀ L D′ m}
  → (W ∣ θ ⊢ idᵖ (groundTy G) ⊢ untagᴸ (⟦ G ⟧ᴳ θ) L ▹ untag (⟦ G ⟧ᴳ θ) D′
     → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ down , AB₀ ⟧ᶜ θ
                            (mem (untagᴸ (⟦ G ⟧ᴳ θ) L)) m ⌋ m
     → W ∣ θ ⊢ AB₀ ⊢ L₁ ▹ untag (⟦ G ⟧ᴳ θ) D′)
  → W ∣ θ ⊢ ★⊑ ⊢ L ▹ D′
  → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ down , tag G AB₀ ⟧ᶜ θ (mem L) m ⌋ m
  → W ∣ θ ⊢ tag G AB₀ ⊢ L₁ ▹ D′
down-tag▹L IH rel [] L₁⊆ = tt₁
down-tag▹L {θ} {W} {G} {AB₀} {L} {D′} {m} IH rel (v₁ ∷ L₁) L₁⊆ =
  ▹-tag-in {θ} {W} {G} {AB₀} {D′} (v₁ ∷ L₁) (IH hyp (v₁ ∷ L₁) out)
  where
  G′ = ⟦ G ⟧ᴳ θ
  out : mem (v₁ ∷ L₁) ⊆ ⌊ ⟦ down , AB₀ ⟧ᶜ θ (mem (untagᴸ G′ L)) m ⌋ m
  out x x∈ with L₁⊆ x x∈
  out x x∈ | inj₁ (() , e∈)
  out x x∈ | inj₂ (m₁ , (c , refl , c∈) , x∈′) =
    c-mono down AB₀ θ m (λ y y∈ → untag-∈⁺ (proj₂ y∈)) (ret x m) x∈′
  hyp : W ∣ θ ⊢ idᵖ (groundTy G) ⊢ untagᴸ G′ L ▹ untag G′ D′
  hyp = ★-payloads {θ} {W} {D′} G L rel

mutual
  upL▹ : ∀ {n θ W AB BC AC A B C L D′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → W ∣ θ ⊢ AC ⊢ L ▹ D′
    → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ up , AB ⟧ᶜ θ (mem L) m ⌋ m
    → W ∣ θ ⊢ BC ⊢ L₁ ▹ D′
  upL▹ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ rel L₁ L₁⊆ with tag-split AB⊢ wfG BC₀⊢ AC⊢
  upL▹ {θ = θ} {W} {L = L} {D′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢) AC⊢
      rel L₁ L₁⊆ | AC′ , AC′⊢ , refl =
    ▹-tag-in {θ} {W} {G} {BC₀} {D′} L₁
      (upL▹ {θ = θ} {W} {L = L} {untag (⟦ G ⟧ᴳ θ) D′} {m} AB⊢ BC₀⊢ AC′⊢
         (▹-tag-out {θ} {W} {G} {AC′} {D′} L rel) L₁ L₁⊆)
  upL▹ ⊑★ ⊑★ AC⊢ rel L₁ L₁⊆ with ⊑-unique AC⊢ ⊑★
  upL▹ ⊑★ ⊑★ AC⊢ rel L₁ L₁⊆ | refl = id▹L rel L₁ L₁⊆
  upL▹ (⊑tag wfG AB₀⊢) ⊑★ AC⊢ rel L₁ L₁⊆
    with ⊑-unique AC⊢ (⊑tag wfG AB₀⊢)
  upL▹ {θ = θ} {W} {L = L} {D′} {m} (⊑tag {G} {AB₀} wfG AB₀⊢) ⊑★ AC⊢
      rel L₁ L₁⊆ | refl =
    up-tag▹L {θ} {W} {G} {AB₀} {L} {D′} {m}
      (upL▹ {θ = θ} {W} {L = L} {untag (⟦ G ⟧ᴳ θ) D′} {m}
         AB₀⊢ (idᵖ-⊢ (groundTy-wf wfG)) AB₀⊢)
      rel L₁ L₁⊆
  upL▹ (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) rel L₁ L₁⊆ = id▹L rel L₁ L₁⊆
  upL▹ ⊑𝔹 ⊑𝔹 ⊑𝔹 rel L₁ L₁⊆ = id▹L rel L₁ L₁⊆
  upL▹ (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢) (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢)
      (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) rel L₁ L₁⊆ =
    L▹⇒ up {AB₁ = AB₁} {AB₂} {AC₁} {AC₂} {BC₁} {BC₂}
      (λ {W′} {A} {E′} {k} →
         downL▹ {W = W′} {L = A} {D′ = E′} {m = k} AB₁⊢ BC₁⊢ AC₁⊢)
      (λ {W′} {X} {E′} {k} →
         upL▹ {W = W′} {L = X} {D′ = E′} {m = k} AB₂⊢ BC₂⊢ AC₂⊢)
      rel L₁ L₁⊆
  upL▹ {θ = θ} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢) (⊑∀ {AC₀} AC₀⊢)
      rel L₁ L₁⊆ =
    L▹∀ up {AB₀ = AB₀} {AC₀} {BC₀}
      (λ σ {W′} {X} {E′} {k} →
         upL▹ {θ = σ •ᵗ θ} {W = W′} {L = X} {D′ = E′} {m = k}
           AB₀⊢ BC₀⊢ AC₀⊢)
      rel L₁ L₁⊆

  downL▹ : ∀ {n θ W AB BC AC A B C L D′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → W ∣ θ ⊢ BC ⊢ L ▹ D′
    → ∀ L₁ → mem L₁ ⊆ ⌊ ⟦ down , AB ⟧ᶜ θ (mem L) m ⌋ m
    → W ∣ θ ⊢ AC ⊢ L₁ ▹ D′
  downL▹ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ rel L₁ L₁⊆
    with tag-split AB⊢ wfG BC₀⊢ AC⊢
  downL▹ {θ = θ} {W} {L = L} {D′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢) AC⊢
      rel L₁ L₁⊆ | AC′ , AC′⊢ , refl =
    ▹-tag-in {θ} {W} {G} {AC′} {D′} L₁
      (downL▹ {θ = θ} {W} {L = L} {untag (⟦ G ⟧ᴳ θ) D′} {m} AB⊢ BC₀⊢ AC′⊢
         (▹-tag-out {θ} {W} {G} {BC₀} {D′} L rel) L₁ L₁⊆)
  downL▹ ⊑★ ⊑★ AC⊢ rel L₁ L₁⊆ with ⊑-unique AC⊢ ⊑★
  downL▹ ⊑★ ⊑★ AC⊢ rel L₁ L₁⊆ | refl = id▹L rel L₁ L₁⊆
  downL▹ (⊑tag wfG AB₀⊢) ⊑★ AC⊢ rel L₁ L₁⊆
    with ⊑-unique AC⊢ (⊑tag wfG AB₀⊢)
  downL▹ {θ = θ} {W} {L = L} {D′} {m} (⊑tag {G} {AB₀} wfG AB₀⊢) ⊑★ AC⊢
      rel L₁ L₁⊆ | refl =
    down-tag▹L {θ} {W} {G} {AB₀} {L} {D′} {m}
      (downL▹ {θ = θ} {W} {L = untagᴸ (⟦ G ⟧ᴳ θ) L}
         {untag (⟦ G ⟧ᴳ θ) D′} {m} AB₀⊢ (idᵖ-⊢ (groundTy-wf wfG)) AB₀⊢)
      rel L₁ L₁⊆
  downL▹ (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) rel L₁ L₁⊆ = id▹L rel L₁ L₁⊆
  downL▹ ⊑𝔹 ⊑𝔹 ⊑𝔹 rel L₁ L₁⊆ = id▹L rel L₁ L₁⊆
  downL▹ (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢) (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢)
      (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) rel L₁ L₁⊆ =
    L▹⇒ down {AB₁ = AB₁} {AB₂} {BC₁} {BC₂} {AC₁} {AC₂}
      (λ {W′} {A} {E′} {k} →
         upL▹ {W = W′} {L = A} {D′ = E′} {m = k} AB₁⊢ BC₁⊢ AC₁⊢)
      (λ {W′} {X} {E′} {k} →
         downL▹ {W = W′} {L = X} {D′ = E′} {m = k} AB₂⊢ BC₂⊢ AC₂⊢)
      rel L₁ L₁⊆
  downL▹ {θ = θ} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢) (⊑∀ {AC₀} AC₀⊢)
      rel L₁ L₁⊆ =
    L▹∀ down {AB₀ = AB₀} {BC₀} {AC₀}
      (λ σ {W′} {X} {E′} {k} →
         downL▹ {θ = σ •ᵗ θ} {W = W′} {L = X} {D′ = E′} {m = k}
           AB₀⊢ BC₀⊢ AC₀⊢)
      rel L₁ L₁⊆

------------------------------------------------------------------------
-- Reflection, a cast on the right
------------------------------------------------------------------------

▹-mono′ : ∀ {W θ p} L {D′ D″} → D′ ⊆ D″
  → W ∣ θ ⊢ p ⊢ L ▹ D′ → W ∣ θ ⊢ p ⊢ L ▹ D″
▹-mono′ {W} {θ} {p} L {D′} {D″} =
  ▹-mono (suc (sizeᴸ L)) {W} {θ} {p} {L} {D′} {D″}

id▹R : ∀ {θ W p} L {D′ m} → W ∣ θ ⊢ p ⊢ L ▹ D′
  → W ∣ θ ⊢ p ⊢ L ▹ ⌊ retᴿ D′ m ⌋ m
id▹R L rel = ▹-mono′ L c-⊆⌊retᴿ⌋ rel

R▹⇒ : ∀ d {θ W BC₁ BC₂ H₁ H₂ K₁ K₂ L D′ m}
  → (∀ {W′ X E k} → W′ ∣ θ ⊢ K₁ ⊢ X ▹ E
       → W′ ∣ θ ⊢ H₁ ⊢ X ▹ ⌊ ⟦ flip d , BC₁ ⟧ᶜ θ E k ⌋ k)
  → (∀ {W′ X E k} → W′ ∣ θ ⊢ H₂ ⊢ X ▹ E
       → W′ ∣ θ ⊢ K₂ ⊢ X ▹ ⌊ ⟦ d , BC₂ ⟧ᶜ θ E k ⌋ k)
  → W ∣ θ ⊢ H₁ ⇒⊑ H₂ ⊢ L ▹ D′
  → W ∣ θ ⊢ K₁ ⇒⊑ K₂ ⊢ L ▹ ⌊ ⟦ d , BC₁ ⇒⊑ BC₂ ⟧ᶜ θ D′ m ⌋ m
R▹⇒ d {L = []} argIH resIH rel = tt₁
R▹⇒ d {θ} {W} {BC₁} {BC₂} {H₁} {H₂} {K₁} {K₂} {v ∷ L} {D′} {m}
    argIH resIH (all , lift ν∈ , f) =
  all , lift (ν∈ , refl , tt) , g
  where
  D″ = ⌊ ⟦ d , BC₁ ⇒⊑ BC₂ ⟧ᶜ θ D′ m ⌋ m
  g : ∀ L₀ → L₀ ⊑ˢ (v ∷ L) → ∀ m′ W′ → W ⊑ʷ W′ → length W′ ≡ m′
    → ∀ E″ → Consistent E″
    → Rel▹ (sizeᴸ (v ∷ L)) W′ θ K₁ (argsAt m′ L₀) E″
    → Rel▹ᶜ (sizeᴸ (v ∷ L)) W′ θ K₂ (resultsAt m′ L₀) (D″ ●[ m′ ] E″)
  g L₀ s m′ W′ ext len E″ CE″ relA m₃ ne₃ = result
    where
    A = argsAt m′ L₀
    E₁ = ⌊ ⟦ flip d , BC₁ ⟧ᶜ θ E″ m′ ⌋ m′
    CE₁ : Consistent E₁
    CE₁ = c-cons⌊⌋ (flip d) BC₁ θ m′ m′ CE″
    relA₁ : W′ ∣ θ ⊢ H₁ ⊢ A ▹ E₁
    relA₁ = argIH {W′} {A} {E″} {m′} (▹-out A (args-sub-< m′ v L s) relA)
    hyp : Rel▹ᶜ (sizeᴸ (v ∷ L)) W′ θ H₂ (resultsAt m′ L₀) (D′ ●[ m′ ] E₁)
    hyp = f L₀ s m′ W′ ext len E₁ CE₁ (▹-in A (args-sub-< m′ v L s) relA₁)
    Xs = valuesAt m₃ (resultsAt m′ L₀)
    incl : ⌊ ⟦ d , BC₂ ⟧ᶜ θ (⌊ D′ ●[ m′ ] E₁ ⌋ m₃) m₃ ⌋ m₃
           ⊆ ⌊ D″ ●[ m′ ] E″ ⌋ m₃
    incl x x∈ =
      c-app⇒ d BC₁ BC₂ θ {D′} {m} {E″} {m′} ν∈ cE″ CE″ (ret x m₃)
        (inj₂ (m′ , cE₁ , inj₂ (m₃ , cS , x∈)))
      where
      cS : Conv (⌊ D′ ●[ m′ ] E₁ ⌋ m₃)
      cS = c-nonempty d BC₂ θ (ret x m₃) x∈
      cE₁ : Conv E₁
      cE₁ = ●-arg-conv {D′} {E₁} {m′} (ret (proj₁ cS) m₃) (proj₂ cS)
      cE″ : Conv E″
      cE″ = c-nonempty (flip d) BC₁ θ (ret (proj₁ cE₁) m′) (proj₂ cE₁)
    result : Σ[ W₃ ∈ World ] (Lift₁ (W′ ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m₃)
               × Rel▹ (sizeᴸ (v ∷ L)) W₃ θ K₂ Xs (⌊ D″ ●[ m′ ] E″ ⌋ m₃))
    result with hyp m₃ ne₃
    result | W₃ , ext₃ , len₃ , rel₃ =
      W₃ , ext₃ , len₃ ,
      ▹-in Xs (values-results-< m₃ m′ v L s)
        (▹-mono′ Xs incl
           (resIH {W₃} {Xs} {⌊ D′ ●[ m′ ] E₁ ⌋ m₃} {m₃}
              (▹-out Xs (values-results-< m₃ m′ v L s) rel₃)))

R▹∀ : ∀ d {θ W BC₀ H₀ K₀ L D′ m}
  → (∀ σ {W′ X E k} → W′ ∣ σ •ᵗ θ ⊢ H₀ ⊢ X ▹ E
       → W′ ∣ σ •ᵗ θ ⊢ K₀ ⊢ X ▹ ⌊ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) E k ⌋ k)
  → W ∣ θ ⊢ ∀⊑ H₀ ⊢ L ▹ D′
  → W ∣ θ ⊢ ∀⊑ K₀ ⊢ L ▹ ⌊ ⟦ d , ∀⊑ BC₀ ⟧ᶜ θ D′ m ⌋ m
R▹∀ d {L = []} bodyIH rel = tt₁
R▹∀ d {θ} {W} {BC₀} {H₀} {K₀} {v ∷ L} {D′} {m}
    bodyIH (all , lift ν∈ , f) =
  all , lift (ν∈ , refl , tt) , g
  where
  D″ = ⌊ ⟦ d , ∀⊑ BC₀ ⟧ᶜ θ D′ m ⌋ m
  g : ∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
    → Rel▹ᶜ (sizeᴸ (v ∷ L)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) K₀
        (bodiesAt σ (v ∷ L)) (D″ ◆ σ)
  g σ W′ q′ ext len m₃ ne₃ = result
    where
    Xs = valuesAt m₃ (bodiesAt σ (v ∷ L))
    incl : ⌊ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) (⌊ D′ ◆ σ ⌋ m₃) m₃ ⌋ m₃
           ⊆ ⌊ D″ ◆ σ ⌋ m₃
    incl x x∈ =
      c-inst∀ d BC₀ θ {D′} {m} {σ} ν∈ (ret x m₃)
        (inj₂ (m₃ , c-nonempty d BC₀ (σ •ᵗ θ) (ret x m₃) x∈ , x∈))
    result : Σ[ W₃ ∈ World ] (Lift₁ (W′ ++ (q′ ∷ []) ⊑ʷ W₃)
               × Lift₁ (length W₃ ≡ m₃)
               × Rel▹ (sizeᴸ (v ∷ L)) W₃ (σ •ᵗ θ) K₀ Xs (⌊ D″ ◆ σ ⌋ m₃))
    result with f σ W′ q′ ext len m₃ ne₃
    result | W₃ , ext₃ , len₃ , rel₃ =
      W₃ , ext₃ , len₃ ,
      ▹-in Xs (values-bodies-< m₃ σ v L)
        (▹-mono′ Xs incl
           (bodyIH σ {W₃} {Xs} {⌊ D′ ◆ σ ⌋ m₃} {m₃}
              (▹-out Xs (values-bodies-< m₃ σ v L) rel₃)))

mutual
  upR▹ : ∀ {n θ W AB BC AC A B C L D′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → W ∣ θ ⊢ AB ⊢ L ▹ D′
    → W ∣ θ ⊢ AC ⊢ L ▹ ⌊ ⟦ up , BC ⟧ᶜ θ D′ m ⌋ m
  upR▹ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ rel with tag-split AB⊢ wfG BC₀⊢ AC⊢
  upR▹ {θ = θ} {W} {L = L} {D′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢) AC⊢ rel
      | AC′ , AC′⊢ , refl =
    ▹-tag-in {θ} {W} {G} {AC′} {⌊ ⟦ up , tag G BC₀ ⟧ᶜ θ D′ m ⌋ m} L
      (▹-mono′ L incl
         (upR▹ {θ = θ} {W} {L = L} {D′} {m} AB⊢ BC₀⊢ AC′⊢ rel))
    where
    incl : ⌊ ⟦ up , BC₀ ⟧ᶜ θ D′ m ⌋ m
           ⊆ untag (⟦ G ⟧ᴳ θ) (⌊ ⟦ up , tag G BC₀ ⟧ᶜ θ D′ m ⌋ m)
    incl x x∈ = inj₂ (m , (x , x∈) , refl , refl , x∈)
  upR▹ AB⊢ ⊑★ AC⊢ rel with ⊑-unique AB⊢ AC⊢
  upR▹ {L = L} AB⊢ ⊑★ AC⊢ rel | refl = id▹R L rel
  upR▹ {L = L} (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) rel = id▹R L rel
  upR▹ {L = L} ⊑𝔹 ⊑𝔹 ⊑𝔹 rel = id▹R L rel
  upR▹ {θ = θ} {W} {L = L} {D′} {m} (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢)
      (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢) (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) rel =
    R▹⇒ up {θ} {W} {BC₁} {BC₂} {AB₁} {AB₂} {AC₁} {AC₂} {L} {D′} {m}
      (λ {W′} {X} {E} {k} →
         downR▹ {W = W′} {L = X} {D′ = E} {m = k} AB₁⊢ BC₁⊢ AC₁⊢)
      (λ {W′} {X} {E} {k} →
         upR▹ {W = W′} {L = X} {D′ = E} {m = k} AB₂⊢ BC₂⊢ AC₂⊢)
      rel
  upR▹ {θ = θ} {W} {L = L} {D′} {m} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢)
      (⊑∀ {AC₀} AC₀⊢) rel =
    R▹∀ up {θ} {W} {BC₀} {AB₀} {AC₀} {L} {D′} {m}
      (λ σ {W′} {X} {E} {k} →
         upR▹ {θ = σ •ᵗ θ} {W = W′} {L = X} {D′ = E} {m = k}
           AB₀⊢ BC₀⊢ AC₀⊢)
      rel

  downR▹ : ∀ {n θ W AB BC AC A B C L D′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → W ∣ θ ⊢ AC ⊢ L ▹ D′
    → W ∣ θ ⊢ AB ⊢ L ▹ ⌊ ⟦ down , BC ⟧ᶜ θ D′ m ⌋ m
  downR▹ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ rel with tag-split AB⊢ wfG BC₀⊢ AC⊢
  downR▹ {θ = θ} {W} {L = L} {D′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢) AC⊢
      rel | AC′ , AC′⊢ , refl =
    ▹-mono′ L incl
      (downR▹ {θ = θ} {W} {L = L} {untag (⟦ G ⟧ᴳ θ) D′} {m} AB⊢ BC₀⊢ AC′⊢
         (▹-tag-out {θ} {W} {G} {AC′} {D′} L rel))
    where
    incl : ⌊ ⟦ down , BC₀ ⟧ᶜ θ (untag (⟦ G ⟧ᴳ θ) D′) m ⌋ m
           ⊆ ⌊ ⟦ down , tag G BC₀ ⟧ᶜ θ D′ m ⌋ m
    incl x x∈ with c-nonempty down BC₀ θ (ret x m) x∈
    incl x x∈ | y , y∈ =
      inj₂ (m , (y , refl , y∈) ,
            c-mono down BC₀ θ m (λ z z∈ → refl , z∈) (ret x m) x∈)
  downR▹ AB⊢ ⊑★ AC⊢ rel with ⊑-unique AC⊢ AB⊢
  downR▹ {L = L} AB⊢ ⊑★ AC⊢ rel | refl = id▹R L rel
  downR▹ {L = L} (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) rel = id▹R L rel
  downR▹ {L = L} ⊑𝔹 ⊑𝔹 ⊑𝔹 rel = id▹R L rel
  downR▹ {θ = θ} {W} {L = L} {D′} {m} (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢)
      (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢) (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) rel =
    R▹⇒ down {θ} {W} {BC₁} {BC₂} {AC₁} {AC₂} {AB₁} {AB₂} {L} {D′} {m}
      (λ {W′} {X} {E} {k} →
         upR▹ {W = W′} {L = X} {D′ = E} {m = k} AB₁⊢ BC₁⊢ AC₁⊢)
      (λ {W′} {X} {E} {k} →
         downR▹ {W = W′} {L = X} {D′ = E} {m = k} AB₂⊢ BC₂⊢ AC₂⊢)
      rel
  downR▹ {θ = θ} {W} {L = L} {D′} {m} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢)
      (⊑∀ {AC₀} AC₀⊢) rel =
    R▹∀ down {θ} {W} {BC₀} {AC₀} {AB₀} {L} {D′} {m}
      (λ σ {W′} {X} {E} {k} →
         downR▹ {θ = σ •ᵗ θ} {W = W′} {L = X} {D′ = E} {m = k}
           AB₀⊢ BC₀⊢ AC₀⊢)
      rel

------------------------------------------------------------------------
-- Preservation, a cast on the left
------------------------------------------------------------------------

◃-mono′ : ∀ {W θ p} L {D D″} → D ⊆ D″
  → W ∣ θ ⊢ p ⊢ D ◃ L → W ∣ θ ⊢ p ⊢ D″ ◃ L
◃-mono′ {W} {θ} {p} L {D} {D″} =
  ◃-mono (suc (sizeᴸ L)) {W} {θ} {p} {D} {D″} {L}

◃-tag-out : ∀ {θ W G p D} L → W ∣ θ ⊢ tag G p ⊢ D ◃ L
  → Lift₁ (All (IsInjAt (⟦ G ⟧ᴳ θ)) L)
    × W ∣ θ ⊢ p ⊢ D ◃ untagᴸ (⟦ G ⟧ᴳ θ) L
◃-tag-out [] rel = lift [] , tt₁
◃-tag-out {θ} {W} {G} {p} {D} (v ∷ L) (all , rel) =
  all , ◃-out {sizeᴸ (v ∷ L)} {W} {θ} {p} {D} (untagᴸ (⟦ G ⟧ᴳ θ) (v ∷ L))
          (untag-< (⟦ G ⟧ᴳ θ) v L) rel

◃-tag-in : ∀ {θ W G p D} L → Lift₁ (All (IsInjAt (⟦ G ⟧ᴳ θ)) L)
  → W ∣ θ ⊢ p ⊢ D ◃ untagᴸ (⟦ G ⟧ᴳ θ) L
  → W ∣ θ ⊢ tag G p ⊢ D ◃ L
◃-tag-in [] all rel = tt₁
◃-tag-in {θ} {W} {G} {p} {D} (v ∷ L) all rel =
  all , ◃-in {sizeᴸ (v ∷ L)} {W} {θ} {p} {D} (untagᴸ (⟦ G ⟧ᴳ θ) (v ∷ L))
          (untag-< (⟦ G ⟧ᴳ θ) v L) rel

id◃L : ∀ {θ W p E} L {m} → W ∣ θ ⊢ p ⊢ E ◃ L
  → Lift₁ (err ∈ᴿ retᴿ E m) ⊎ W ∣ θ ⊢ p ⊢ ⌊ retᴿ E m ⌋ m ◃ L
id◃L L rel = inj₂ (◃-mono′ L c-⊆⌊retᴿ⌋ rel)

map⊎ : ∀ {A A′ : Set₁} {B B′ : Set₁} → (A → A′) → (B → B′)
  → A ⊎ B → A′ ⊎ B′
map⊎ f g (inj₁ a) = inj₁ (f a)
map⊎ f g (inj₂ b) = inj₂ (g b)

-- the counters at which a list of results returns values
ctrs : List Res → List ℕ
ctrs [] = []
ctrs (ret v m ∷ Rs) = m ∷ ctrs Rs
ctrs (err ∷ Rs) = ctrs Rs

ret-ctr : ∀ {v m Rs} → ret v m ⋵ Rs → m ⋵ ctrs Rs
ret-ctr {Rs = ret w k ∷ Rs} (here refl) = here refl
ret-ctr {Rs = ret w k ∷ Rs} (there p) = there (ret-ctr p)
ret-ctr {Rs = err ∷ Rs} (there p) = ret-ctr p

ctr-ret : ∀ {m} Rs → m ⋵ ctrs Rs → Σ[ v ∈ Val ] (ret v m ⋵ Rs)
ctr-ret (ret w k ∷ Rs) (here refl) = w , here refl
ctr-ret (ret w k ∷ Rs) (there p) with ctr-ret Rs p
ctr-ret (ret w k ∷ Rs) (there p) | v , v∈ = v , there v∈
ctr-ret (err ∷ Rs) p with ctr-ret Rs p
ctr-ret (err ∷ Rs) p | v , v∈ = v , there v∈

allℕ : ∀ {P : Set} {Q : ℕ → Set₁} Cs
  → (∀ c → c ⋵ Cs → Lift₁ P ⊎ Q c)
  → Lift₁ P ⊎ (∀ c → c ⋵ Cs → Q c)
allℕ [] h = inj₂ (λ c ())
allℕ (c ∷ Cs) h with h c (here refl)
allℕ (c ∷ Cs) h | inj₁ e = inj₁ e
allℕ (c ∷ Cs) h | inj₂ qc with allℕ Cs (λ c′ c′∈ → h c′ (there c′∈))
allℕ (c ∷ Cs) h | inj₂ qc | inj₁ e = inj₁ e
allℕ {Q = Q} (c ∷ Cs) h | inj₂ qc | inj₂ qs = inj₂ all
  where
  all : ∀ c′ → c′ ⋵ (c ∷ Cs) → Q c′
  all c′ (here refl) = qc
  all c′ (there c′∈) = qs c′ c′∈

-- decide, over the finitely many counters of a list of results
decide-ctrs : ∀ {P : Set} {Q : ℕ → Set₁} Rs
  → (∀ m → valuesAt m Rs ≢ [] → Lift₁ P ⊎ Q m)
  → Lift₁ P ⊎ (∀ m → valuesAt m Rs ≢ [] → Q m)
decide-ctrs Rs step
  with allℕ (ctrs Rs)
         (λ c c∈ → step c (nonempty (values-∈⁺ {Rs = Rs}
                                       (proj₂ (ctr-ret Rs c∈)))))
decide-ctrs Rs step | inj₁ e = inj₁ e
decide-ctrs Rs step | inj₂ all =
  inj₂ (λ m ne → all m (ret-ctr (values-∈⁻ Rs (proj₂ (ne-head _ ne)))))

L◃⇒ : ∀ d {θ W AB₁ AB₂ H₁ H₂ K₁ K₂ E L′ m}
  → (∀ {W′ X Y k} → Consistent X → W′ ∣ θ ⊢ K₁ ⊢ X ◃ Y
       → Lift₁ (err ∈ᴿ ⟦ flip d , AB₁ ⟧ᶜ θ X k)
         ⊎ W′ ∣ θ ⊢ H₁ ⊢ ⌊ ⟦ flip d , AB₁ ⟧ᶜ θ X k ⌋ k ◃ Y)
  → (∀ {W′ X Y k} → Consistent X → W′ ∣ θ ⊢ H₂ ⊢ X ◃ Y
       → Lift₁ (err ∈ᴿ ⟦ d , AB₂ ⟧ᶜ θ X k)
         ⊎ W′ ∣ θ ⊢ K₂ ⊢ ⌊ ⟦ d , AB₂ ⟧ᶜ θ X k ⌋ k ◃ Y)
  → Consistent E → W ∣ θ ⊢ H₁ ⇒⊑ H₂ ⊢ E ◃ L′
  → Lift₁ (err ∈ᴿ ⟦ d , AB₁ ⇒⊑ AB₂ ⟧ᶜ θ E m)
    ⊎ W ∣ θ ⊢ K₁ ⇒⊑ K₂ ⊢ ⌊ ⟦ d , AB₁ ⇒⊑ AB₂ ⟧ᶜ θ E m ⌋ m ◃ L′
L◃⇒ d {L′ = []} argIH resIH CE rel = inj₂ tt₁
L◃⇒ d {θ} {W} {AB₁} {AB₂} {H₁} {H₂} {K₁} {K₂} {E} {v′ ∷ L′} {m}
    argIH resIH CE (all , lift ν∈ , f) =
  inj₂ (all , lift (ν∈ , refl , tt) , g)
  where
  D₁ = ⌊ ⟦ d , AB₁ ⇒⊑ AB₂ ⟧ᶜ θ E m ⌋ m
  g : ∀ L₀′ → L₀′ ⊑ˢ (v′ ∷ L′) → ∀ m′ W′ → W ⊑ʷ W′ → length W′ ≡ m′
    → ∀ E₁ → Consistent E₁
    → Rel◃ (sizeᴸ (v′ ∷ L′)) W′ θ K₁ E₁ (argsAt m′ L₀′)
    → Rel◃ᶜ (sizeᴸ (v′ ∷ L′)) W′ θ K₂ (D₁ ●[ m′ ] E₁) (resultsAt m′ L₀′)
  g L₀′ s m′ W′ ext len E₁ CE₁ relA = body
    where
    A′ = argsAt m′ L₀′
    Rs′ = resultsAt m′ L₀′
    sA : sizeᴸ A′ < sizeᴸ (v′ ∷ L′)
    sA = args-sub-< m′ v′ L′ s
    app : ∀ r → r ∈ᴿ c-⇒F d AB₁ AB₂ θ E E₁ m′ → Conv E₁
      → r ∈ᴿ (D₁ ●[ m′ ] E₁)
    app r r∈ cE₁ = c-app⇒ d AB₁ AB₂ θ {E} {m} {E₁} {m′} ν∈ cE₁ CE₁ r r∈
    E₂ = ⌊ ⟦ flip d , AB₁ ⟧ᶜ θ E₁ m′ ⌋ m′
    R₁′ = ⟦ flip d , AB₁ ⟧ᶜ θ E₁ m′
    K₁′ : 𝒱 → ℕ → ℛ
    K₁′ E₂′ m₁ = (E ●[ m₁ ] E₂′) ≫= ⟦ d , AB₂ ⟧ᶜ θ
    CE₂ : Consistent E₂
    CE₂ = c-cons⌊⌋ (flip d) AB₁ θ m′ m′ CE₁
    conv₁ : Conv E₂ → Conv E₁
    conv₁ (x , x∈) = c-nonempty (flip d) AB₁ θ (ret x m′) x∈
    -- a value of E ●[ m′ ] E₂ at m₃, cast by AB₂, is a result on the left
    chain : ∀ m₃ → Conv (⌊ E ●[ m′ ] E₂ ⌋ m₃)
      → ∀ r → r ∈ᴿ ⟦ d , AB₂ ⟧ᶜ θ (⌊ E ●[ m′ ] E₂ ⌋ m₃) m₃
      → r ∈ᴿ (D₁ ●[ m′ ] E₁)
    chain m₃ cS r r∈ =
      app r (c-≫=-group {R₁′} {K₁′} {m′} cE₂ r
               (c-≫=-group {E ●[ m′ ] E₂} {⟦ d , AB₂ ⟧ᶜ θ} {m₃} cS r r∈))
        (conv₁ cE₂)
      where
      cE₂ : Conv E₂
      cE₂ = ●-arg-conv {E} {E₂} {m′} (ret (proj₁ cS) m₃) (proj₂ cS)
    body : Rel◃ᶜ (sizeᴸ (v′ ∷ L′)) W′ θ K₂ (D₁ ●[ m′ ] E₁) Rs′
    body with argIH {W′} {E₁} {A′} {m′} CE₁ (◃-out A′ sA relA)
    body | inj₁ (lift e) =
      inj₁ (lift (app err (c-≫=-err {R₁′} {K₁′} e)
                    (c-nonempty (flip d) AB₁ θ err e)))
    body | inj₂ rel₂ with f L₀′ s m′ W′ ext len E₂ CE₂ (◃-in A′ sA rel₂)
    body | inj₂ rel₂ | inj₁ (lift e) =
      inj₁ (lift (app err (c-≫=-group {R₁′} {K₁′} {m′} cE₂ err
                             (c-≫=-err {E ●[ m′ ] E₂} {⟦ d , AB₂ ⟧ᶜ θ} e))
                    (conv₁ cE₂)))
      where
      cE₂ : Conv E₂
      cE₂ = ●-arg-conv {E} {E₂} {m′} err e
    body | inj₂ rel₂ | inj₂ (lift ne , h) with decide-ctrs Rs′ step
      where
      step : ∀ m₃ → valuesAt m₃ Rs′ ≢ []
        → Lift₁ (err ∈ᴿ (D₁ ●[ m′ ] E₁))
          ⊎ Σ[ W₃ ∈ World ] (Lift₁ (W′ ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m₃)
              × Rel◃ (sizeᴸ (v′ ∷ L′)) W₃ θ K₂ (⌊ D₁ ●[ m′ ] E₁ ⌋ m₃)
                  (valuesAt m₃ Rs′))
      step m₃ ne₃ with h m₃ ne₃
      step m₃ ne₃ | W₃ , ext₃ , len₃ , rel₃
        with resIH {W₃} {⌊ E ●[ m′ ] E₂ ⌋ m₃} {valuesAt m₃ Rs′} {m₃}
               (c-⌊⌋-cons (c-●-cons CE CE₂))
               (◃-out (valuesAt m₃ Rs′) (values-results-< m₃ m′ v′ L′ s)
                  rel₃)
      step m₃ ne₃ | W₃ , ext₃ , len₃ , rel₃ | inj₁ (lift e) =
        inj₁ (lift (chain m₃ cS err e))
        where
        cS : Conv (⌊ E ●[ m′ ] E₂ ⌋ m₃)
        cS = ◃-conv (sizeᴸ (v′ ∷ L′)) (proj₂ (ne-head _ ne₃)) rel₃
      step m₃ ne₃ | W₃ , ext₃ , len₃ , rel₃ | inj₂ rel₄ =
        inj₂ (W₃ , ext₃ , len₃ ,
              ◃-in (valuesAt m₃ Rs′) (values-results-< m₃ m′ v′ L′ s)
                (◃-mono′ (valuesAt m₃ Rs′)
                   (λ x x∈ → chain m₃ cS (ret x m₃) x∈) rel₄))
        where
        cS : Conv (⌊ E ●[ m′ ] E₂ ⌋ m₃)
        cS = ◃-conv (sizeᴸ (v′ ∷ L′)) (proj₂ (ne-head _ ne₃)) rel₃
    body | inj₂ rel₂ | inj₂ (lift ne , h) | inj₁ e = inj₁ e
    body | inj₂ rel₂ | inj₂ (lift ne , h) | inj₂ all =
      inj₂ (lift ne , all)

L◃∀ : ∀ d {θ W AB₀ H₀ K₀ E L′ m}
  → (∀ σ {W′ X Y k} → Consistent X → W′ ∣ σ •ᵗ θ ⊢ H₀ ⊢ X ◃ Y
       → Lift₁ (err ∈ᴿ ⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ) X k)
         ⊎ W′ ∣ σ •ᵗ θ ⊢ K₀ ⊢ ⌊ ⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ) X k ⌋ k ◃ Y)
  → Consistent E → W ∣ θ ⊢ ∀⊑ H₀ ⊢ E ◃ L′
  → Lift₁ (err ∈ᴿ ⟦ d , ∀⊑ AB₀ ⟧ᶜ θ E m)
    ⊎ W ∣ θ ⊢ ∀⊑ K₀ ⊢ ⌊ ⟦ d , ∀⊑ AB₀ ⟧ᶜ θ E m ⌋ m ◃ L′
L◃∀ d {L′ = []} bodyIH CE rel = inj₂ tt₁
L◃∀ d {θ} {W} {AB₀} {H₀} {K₀} {E} {v′ ∷ L′} {m}
    bodyIH CE (all , lift ν∈ , f) =
  inj₂ (all , lift (ν∈ , refl , tt) , g)
  where
  D₁ = ⌊ ⟦ d , ∀⊑ AB₀ ⟧ᶜ θ E m ⌋ m
  g : ∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
    → Rel◃ᶜ (sizeᴸ (v′ ∷ L′)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) K₀ (D₁ ◆ σ)
        (bodiesAt σ (v′ ∷ L′))
  g σ W′ q′ ext len = body
    where
    Bs = bodiesAt σ (v′ ∷ L′)
    inst : ∀ r → r ∈ᴿ c-∀F d AB₀ θ E σ → r ∈ᴿ (D₁ ◆ σ)
    inst = c-inst∀ d AB₀ θ {E} {m} {σ} ν∈
    chain : ∀ m₃ → Conv (⌊ E ◆ σ ⌋ m₃)
      → ∀ r → r ∈ᴿ ⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ) (⌊ E ◆ σ ⌋ m₃) m₃
      → r ∈ᴿ (D₁ ◆ σ)
    chain m₃ cS r r∈ =
      inst r (c-≫=-group {E ◆ σ} {⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ)} {m₃} cS r r∈)
    body : Rel◃ᶜ (sizeᴸ (v′ ∷ L′)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) K₀ (D₁ ◆ σ) Bs
    body with f σ W′ q′ ext len
    body | inj₁ (lift e) =
      inj₁ (lift (inst err (c-≫=-err {E ◆ σ} {⟦ d , AB₀ ⟧ᶜ (σ •ᵗ θ)} e)))
    body | inj₂ (lift ne , h) with decide-ctrs Bs step
      where
      step : ∀ m₃ → valuesAt m₃ Bs ≢ []
        → Lift₁ (err ∈ᴿ (D₁ ◆ σ))
          ⊎ Σ[ W₃ ∈ World ] (Lift₁ (W′ ++ (q′ ∷ []) ⊑ʷ W₃)
              × Lift₁ (length W₃ ≡ m₃)
              × Rel◃ (sizeᴸ (v′ ∷ L′)) W₃ (σ •ᵗ θ) K₀ (⌊ D₁ ◆ σ ⌋ m₃)
                  (valuesAt m₃ Bs))
      step m₃ ne₃ with h m₃ ne₃
      step m₃ ne₃ | W₃ , ext₃ , len₃ , rel₃
        with bodyIH σ {W₃} {⌊ E ◆ σ ⌋ m₃} {valuesAt m₃ Bs} {m₃}
               (c-⌊⌋-cons (c-◆-cons CE))
               (◃-out (valuesAt m₃ Bs) (values-bodies-< m₃ σ v′ L′) rel₃)
      step m₃ ne₃ | W₃ , ext₃ , len₃ , rel₃ | inj₁ (lift e) =
        inj₁ (lift (chain m₃ cS err e))
        where
        cS : Conv (⌊ E ◆ σ ⌋ m₃)
        cS = ◃-conv (sizeᴸ (v′ ∷ L′)) (proj₂ (ne-head _ ne₃)) rel₃
      step m₃ ne₃ | W₃ , ext₃ , len₃ , rel₃ | inj₂ rel₄ =
        inj₂ (W₃ , ext₃ , len₃ ,
              ◃-in (valuesAt m₃ Bs) (values-bodies-< m₃ σ v′ L′)
                (◃-mono′ (valuesAt m₃ Bs)
                   (λ x x∈ → chain m₃ cS (ret x m₃) x∈) rel₄))
        where
        cS : Conv (⌊ E ◆ σ ⌋ m₃)
        cS = ◃-conv (sizeᴸ (v′ ∷ L′)) (proj₂ (ne-head _ ne₃)) rel₃
    body | inj₂ (lift ne , h) | inj₁ e = inj₁ e
    body | inj₂ (lift ne , h) | inj₂ all = inj₂ (lift ne , all)

-- an up cast through tag G on the left, landing in ★
up-tag◃L : ∀ {θ W G AB₀ E L′ m}
  → (Lift₁ (err ∈ᴿ ⟦ up , AB₀ ⟧ᶜ θ E m)
     ⊎ W ∣ θ ⊢ idᵖ (groundTy G) ⊢ ⌊ ⟦ up , AB₀ ⟧ᶜ θ E m ⌋ m
         ◃ untagᴸ (⟦ G ⟧ᴳ θ) L′)
  → Lift₁ (All (IsInjAt (⟦ G ⟧ᴳ θ)) L′)
  → Lift₁ (err ∈ᴿ ⟦ up , tag G AB₀ ⟧ᶜ θ E m)
    ⊎ W ∣ θ ⊢ ★⊑ ⊢ ⌊ ⟦ up , tag G AB₀ ⟧ᶜ θ E m ⌋ m ◃ L′
up-tag◃L {θ} {W} {G} {AB₀} {E} {L′} {m} (inj₁ (lift e)) all =
  inj₁ (lift (c-≫=-err {⟦ up , AB₀ ⟧ᶜ θ E m}
                {λ E₁ m₁ → retᴿ (injᴾ (⟦ G ⟧ᴳ θ) E₁) m₁} e))
up-tag◃L {L′ = []} (inj₂ rel) all = inj₂ tt₁
up-tag◃L {θ} {W} {G} {AB₀} {E} {v′ ∷ L′} {m} (inj₂ rel) (lift all) =
  inj₂ (lift (All-map (λ { x is-inj-at → is-inj }) all) , pay)
  where
  G′ = ⟦ G ⟧ᴳ θ
  D₁ = ⌊ ⟦ up , tag G AB₀ ⟧ᶜ θ E m ⌋ m
  pay : ∀ H → Rel◃ (sizeᴸ (v′ ∷ L′)) W θ₀ (gp H) (untag H D₁)
                (untagᴸ H (v′ ∷ L′))
  pay H with H ≟G G′
  pay H | yes refl =
    ◃-in P (untag-< G′ v′ L′)
      (◃-out P ≤-refl
        (from (gp-◃ (suc (sizeᴸ P)) θ G {W} {untag G′ D₁} {P})
          (◃-in P ≤-refl (◃-mono′ P incl rel))))
    where
    P = untagᴸ G′ (v′ ∷ L′)
    incl : ⌊ ⟦ up , AB₀ ⟧ᶜ θ E m ⌋ m ⊆ untag G′ D₁
    incl x x∈ = inj₂ (m , (x , x∈) , refl , refl , x∈)
  pay H | no H≢ =
    ◃-empty (λ u u∈ → none u (untag-∈⁻ (v′ ∷ L′) u∈)) (untag-< H v′ L′)
    where
    none : ∀ u → injᵛ H u ⋵ (v′ ∷ L′) → ⊥
    none u u∈ with All-lookup all u∈
    none u u∈ | is-inj-at = H≢ refl

-- are all tags G, or is there another one?
tags-dec : ∀ G L → All IsInj L
  → All (IsInjAt G) L
    ⊎ Σ[ H ∈ Ground ] Σ[ u ∈ Val ] (injᵛ H u ⋵ L × H ≢ G)
tags-dec G [] [] = inj₁ []
tags-dec G (injᵛ H u ∷ L) (is-inj ∷ all) with H ≟G G
tags-dec G (injᵛ H u ∷ L) (is-inj ∷ all) | yes refl
  with tags-dec G L all
tags-dec G (injᵛ H u ∷ L) (is-inj ∷ all) | yes refl | inj₁ all′ =
  inj₁ (is-inj-at ∷ all′)
tags-dec G (injᵛ H u ∷ L) (is-inj ∷ all) | yes refl
  | inj₂ (H′ , u′ , u′∈ , H′≢) = inj₂ (H′ , u′ , there u′∈ , H′≢)
tags-dec G (injᵛ H u ∷ L) (is-inj ∷ all) | no H≢ =
  inj₂ (H , u , here refl , H≢)

untag-cons : ∀ {G E} → Consistent E → Consistent (untag G E)
untag-cons CE u v u∈ v∈ = proj₂ (CE _ _ u∈ v∈)

-- the payloads tagged ⟦ G ⟧ᴳ θ of a list related at ★ (preservation)
★-payloads◃ : ∀ {θ W E} G L → W ∣ θ ⊢ ★⊑ ⊢ E ◃ L
  → W ∣ θ ⊢ idᵖ (groundTy G) ⊢ untag (⟦ G ⟧ᴳ θ) E ◃ untagᴸ (⟦ G ⟧ᴳ θ) L
★-payloads◃ G [] rel = tt₁
★-payloads◃ {θ} {W} {E} G (v ∷ L) rel =
  to (gp-◃ (suc (sizeᴸ (untagᴸ G′ (v ∷ L)))) θ G
        {W} {untag G′ E} {untagᴸ G′ (v ∷ L)})
    (◃-fuel (sizeᴸ (v ∷ L)) (suc (sizeᴸ (untagᴸ G′ (v ∷ L))))
       {W} {θ₀} {gp G′} {untag G′ E} {untagᴸ G′ (v ∷ L)}
       (untag-< G′ v L) ≤-refl (proj₂ rel G′))
  where
  G′ = ⟦ G ⟧ᴳ θ

payload∈ : ∀ {G} v L → All (IsInjAt G) (v ∷ L)
  → Σ[ u ∈ Val ] (u ⋵ untagᴸ G (v ∷ L))
payload∈ (injᵛ G u) L (is-inj-at ∷ all) =
  u , untag-∈⁺ {L = injᵛ G u ∷ L} (here refl)

-- the last step of a down cast through tag G when all tags are G
down-tag◃L′ : ∀ {θ W G AB₀ E} v′ L′ {m}
  → All (IsInjAt (⟦ G ⟧ᴳ θ)) (v′ ∷ L′)
  → W ∣ θ ⊢ idᵖ (groundTy G) ⊢ untag (⟦ G ⟧ᴳ θ) E
      ◃ untagᴸ (⟦ G ⟧ᴳ θ) (v′ ∷ L′)
  → Lift₁ (err ∈ᴿ ⟦ down , AB₀ ⟧ᶜ θ (untag (⟦ G ⟧ᴳ θ) E) m)
    ⊎ W ∣ θ ⊢ AB₀ ⊢ ⌊ ⟦ down , AB₀ ⟧ᶜ θ (untag (⟦ G ⟧ᴳ θ) E) m ⌋ m
        ◃ untagᴸ (⟦ G ⟧ᴳ θ) (v′ ∷ L′)
  → Lift₁ (err ∈ᴿ ⟦ down , tag G AB₀ ⟧ᶜ θ E m)
    ⊎ W ∣ θ ⊢ tag G AB₀ ⊢ ⌊ ⟦ down , tag G AB₀ ⟧ᶜ θ E m ⌋ m ◃ (v′ ∷ L′)
down-tag◃L′ {θ} {W} {G} {AB₀} {E} v′ L′ {m} allAt rel₀ res = out res
  where
  G′ = ⟦ G ⟧ᴳ θ
  P = untagᴸ G′ (v′ ∷ L′)
  conv : Conv (⌊ proj G′ E m ⌋ m)
  conv with ◃-conv (suc (sizeᴸ P)) (proj₂ (payload∈ v′ L′ allAt)) rel₀
  conv | y , y∈ = y , refl , y∈
  incl : ⌊ ⟦ down , AB₀ ⟧ᶜ θ (untag G′ E) m ⌋ m
         ⊆ ⌊ ⟦ down , tag G AB₀ ⟧ᶜ θ E m ⌋ m
  incl x x∈ =
    inj₂ (m , conv , c-mono down AB₀ θ m (λ y y∈ → refl , y∈) (ret x m) x∈)
  out : Lift₁ (err ∈ᴿ ⟦ down , AB₀ ⟧ᶜ θ (untag G′ E) m)
        ⊎ W ∣ θ ⊢ AB₀ ⊢ ⌊ ⟦ down , AB₀ ⟧ᶜ θ (untag G′ E) m ⌋ m ◃ P
    → Lift₁ (err ∈ᴿ ⟦ down , tag G AB₀ ⟧ᶜ θ E m)
      ⊎ W ∣ θ ⊢ tag G AB₀ ⊢ ⌊ ⟦ down , tag G AB₀ ⟧ᶜ θ E m ⌋ m ◃ (v′ ∷ L′)
  out (inj₁ (lift e)) =
    inj₁ (lift (c-≫=-group {proj G′ E m} {⟦ down , AB₀ ⟧ᶜ θ} {m} conv err
                  (c-mono down AB₀ θ m (λ y y∈ → refl , y∈) err e)))
  out (inj₂ rel) =
    inj₂ (◃-tag-in {θ} {W} {G} {AB₀} (v′ ∷ L′) (lift allAt)
            (◃-mono′ P incl rel))

-- a down cast through tag G on the left, from ★
down-tag◃L : ∀ {θ W G AB₀ E L′ m}
  → (Consistent (untag (⟦ G ⟧ᴳ θ) E)
     → W ∣ θ ⊢ idᵖ (groundTy G) ⊢ untag (⟦ G ⟧ᴳ θ) E
         ◃ untagᴸ (⟦ G ⟧ᴳ θ) L′
     → Lift₁ (err ∈ᴿ ⟦ down , AB₀ ⟧ᶜ θ (untag (⟦ G ⟧ᴳ θ) E) m)
       ⊎ W ∣ θ ⊢ AB₀ ⊢ ⌊ ⟦ down , AB₀ ⟧ᶜ θ (untag (⟦ G ⟧ᴳ θ) E) m ⌋ m
           ◃ untagᴸ (⟦ G ⟧ᴳ θ) L′)
  → Consistent E → W ∣ θ ⊢ ★⊑ ⊢ E ◃ L′
  → Lift₁ (err ∈ᴿ ⟦ down , tag G AB₀ ⟧ᶜ θ E m)
    ⊎ W ∣ θ ⊢ tag G AB₀ ⊢ ⌊ ⟦ down , tag G AB₀ ⟧ᶜ θ E m ⌋ m ◃ L′
down-tag◃L {L′ = []} IH CE rel = inj₂ tt₁
down-tag◃L {θ} {W} {G} {AB₀} {E} {v′ ∷ L′} {m} IH CE (lift allI , f)
  with tags-dec (⟦ G ⟧ᴳ θ) (v′ ∷ L′) allI
down-tag◃L {θ} {W} {G} {AB₀} {E} {v′ ∷ L′} {m} IH CE (lift allI , f)
  | inj₂ (H , u , u∈ , H≢)
  with ◃-conv (sizeᴸ (v′ ∷ L′)) (untag-∈⁺ u∈) (f H)
... | b , b∈ =
  inj₁ (lift (c-≫=-err {proj (⟦ G ⟧ᴳ θ) E m} {⟦ down , AB₀ ⟧ᶜ θ}
                (H , b , b∈ , H≢)))
down-tag◃L {θ} {W} {G} {AB₀} {E} {v′ ∷ L′} {m} IH CE (lift allI , f)
  | inj₁ allAt =
  down-tag◃L′ {θ} {W} {G} {AB₀} {E} v′ L′ {m} allAt rel₀
    (IH (untag-cons CE) rel₀)
  where
  rel₀ = ★-payloads◃ {θ} {W} {E} G (v′ ∷ L′) (lift allI , f)

mutual
  upL◃ : ∀ {n θ W AB BC AC A B C E L′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → Consistent E → W ∣ θ ⊢ AC ⊢ E ◃ L′
    → Lift₁ (err ∈ᴿ ⟦ up , AB ⟧ᶜ θ E m)
      ⊎ W ∣ θ ⊢ BC ⊢ ⌊ ⟦ up , AB ⟧ᶜ θ E m ⌋ m ◃ L′
  upL◃ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ CE rel with tag-split AB⊢ wfG BC₀⊢ AC⊢
  upL◃ {θ = θ} {W} {AB} {E = E} {L′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢)
      AC⊢ CE rel | AC′ , AC′⊢ , refl
    with ◃-tag-out {θ} {W} {G} {AC′} {E} L′ rel
  ... | all , rel₀ =
    map⊎ (λ e → e)
      (◃-tag-in {θ} {W} {G} {BC₀} {⌊ ⟦ up , AB ⟧ᶜ θ E m ⌋ m} L′ all)
      (upL◃ {θ = θ} {W} {E = E} {L′ = untagᴸ (⟦ G ⟧ᴳ θ) L′} {m}
         AB⊢ BC₀⊢ AC′⊢ CE rel₀)
  upL◃ ⊑★ ⊑★ AC⊢ CE rel with ⊑-unique AC⊢ ⊑★
  upL◃ {L′ = L′} ⊑★ ⊑★ AC⊢ CE rel | refl = id◃L L′ rel
  upL◃ (⊑tag wfG AB₀⊢) ⊑★ AC⊢ CE rel with ⊑-unique AC⊢ (⊑tag wfG AB₀⊢)
  upL◃ {θ = θ} {W} {E = E} {L′} {m} (⊑tag {G} {AB₀} wfG AB₀⊢) ⊑★ AC⊢
      CE rel | refl
    with ◃-tag-out {θ} {W} {G} {AB₀} {E} L′ rel
  ... | all , rel₀ =
    up-tag◃L {θ} {W} {G} {AB₀} {E} {L′} {m}
      (upL◃ {θ = θ} {W} {E = E} {L′ = untagᴸ (⟦ G ⟧ᴳ θ) L′} {m}
         AB₀⊢ (idᵖ-⊢ (groundTy-wf wfG)) AB₀⊢ CE rel₀)
      all
  upL◃ {L′ = L′} (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) CE rel = id◃L L′ rel
  upL◃ {L′ = L′} ⊑𝔹 ⊑𝔹 ⊑𝔹 CE rel = id◃L L′ rel
  upL◃ {θ = θ} {W} {E = E} {L′} {m} (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢)
      (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢) (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) CE rel =
    L◃⇒ up {θ} {W} {AB₁} {AB₂} {AC₁} {AC₂} {BC₁} {BC₂} {E} {L′} {m}
      (λ {W′} {X} {Y} {k} CX →
         downL◃ {θ = θ} {W′} {E = X} {L′ = Y} {k} AB₁⊢ BC₁⊢ AC₁⊢ CX)
      (λ {W′} {X} {Y} {k} CX →
         upL◃ {θ = θ} {W′} {E = X} {L′ = Y} {k} AB₂⊢ BC₂⊢ AC₂⊢ CX)
      CE rel
  upL◃ {θ = θ} {W} {E = E} {L′} {m} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢)
      (⊑∀ {AC₀} AC₀⊢) CE rel =
    L◃∀ up {θ} {W} {AB₀} {AC₀} {BC₀} {E} {L′} {m}
      (λ σ {W′} {X} {Y} {k} CX →
         upL◃ {θ = σ •ᵗ θ} {W′} {E = X} {L′ = Y} {k} AB₀⊢ BC₀⊢ AC₀⊢ CX)
      CE rel

  downL◃ : ∀ {n θ W AB BC AC A B C E L′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → Consistent E → W ∣ θ ⊢ BC ⊢ E ◃ L′
    → Lift₁ (err ∈ᴿ ⟦ down , AB ⟧ᶜ θ E m)
      ⊎ W ∣ θ ⊢ AC ⊢ ⌊ ⟦ down , AB ⟧ᶜ θ E m ⌋ m ◃ L′
  downL◃ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ CE rel with tag-split AB⊢ wfG BC₀⊢ AC⊢
  downL◃ {θ = θ} {W} {AB} {E = E} {L′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢)
      AC⊢ CE rel | AC′ , AC′⊢ , refl
    with ◃-tag-out {θ} {W} {G} {BC₀} {E} L′ rel
  ... | all , rel₀ =
    map⊎ (λ e → e)
      (◃-tag-in {θ} {W} {G} {AC′} {⌊ ⟦ down , AB ⟧ᶜ θ E m ⌋ m} L′ all)
      (downL◃ {θ = θ} {W} {E = E} {L′ = untagᴸ (⟦ G ⟧ᴳ θ) L′} {m}
         AB⊢ BC₀⊢ AC′⊢ CE rel₀)
  downL◃ ⊑★ ⊑★ AC⊢ CE rel with ⊑-unique AC⊢ ⊑★
  downL◃ {L′ = L′} ⊑★ ⊑★ AC⊢ CE rel | refl = id◃L L′ rel
  downL◃ (⊑tag wfG AB₀⊢) ⊑★ AC⊢ CE rel with ⊑-unique AC⊢ (⊑tag wfG AB₀⊢)
  downL◃ {θ = θ} {W} {E = E} {L′} {m} (⊑tag {G} {AB₀} wfG AB₀⊢) ⊑★ AC⊢
      CE rel | refl =
    down-tag◃L {θ} {W} {G} {AB₀} {E} {L′} {m}
      (λ CX r →
         downL◃ {θ = θ} {W} {E = untag (⟦ G ⟧ᴳ θ) E}
           {L′ = untagᴸ (⟦ G ⟧ᴳ θ) L′} {m}
           AB₀⊢ (idᵖ-⊢ (groundTy-wf wfG)) AB₀⊢ CX r)
      CE rel
  downL◃ {L′ = L′} (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) CE rel = id◃L L′ rel
  downL◃ {L′ = L′} ⊑𝔹 ⊑𝔹 ⊑𝔹 CE rel = id◃L L′ rel
  downL◃ {θ = θ} {W} {E = E} {L′} {m} (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢)
      (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢) (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) CE rel =
    L◃⇒ down {θ} {W} {AB₁} {AB₂} {BC₁} {BC₂} {AC₁} {AC₂} {E} {L′} {m}
      (λ {W′} {X} {Y} {k} CX →
         upL◃ {θ = θ} {W′} {E = X} {L′ = Y} {k} AB₁⊢ BC₁⊢ AC₁⊢ CX)
      (λ {W′} {X} {Y} {k} CX →
         downL◃ {θ = θ} {W′} {E = X} {L′ = Y} {k} AB₂⊢ BC₂⊢ AC₂⊢ CX)
      CE rel
  downL◃ {θ = θ} {W} {E = E} {L′} {m} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢)
      (⊑∀ {AC₀} AC₀⊢) CE rel =
    L◃∀ down {θ} {W} {AB₀} {BC₀} {AC₀} {E} {L′} {m}
      (λ σ {W′} {X} {Y} {k} CX →
         downL◃ {θ = σ •ᵗ θ} {W′} {E = X} {L′ = Y} {k} AB₀⊢ BC₀⊢ AC₀⊢ CX)
      CE rel

------------------------------------------------------------------------
-- Preservation, a cast on the right
------------------------------------------------------------------------

∀F-err : ∀ d p θ X σ → err ∈ᴿ c-∀F d p θ X σ
  → (σ ⟼∀ err) ∈ X
    ⊎ Σ[ m₃ ∈ ℕ ] (Conv (⌊ X ◆ σ ⌋ m₃)
        × err ∈ᴿ ⟦ d , p ⟧ᶜ (σ •ᵗ θ) (⌊ X ◆ σ ⌋ m₃) m₃)
∀F-err d p θ X σ (inj₁ (refl , e)) = inj₁ e
∀F-err d p θ X σ (inj₂ (m₃ , c , e)) = inj₂ (m₃ , c , e)

id◃R : ∀ {θ W p D} L′ {m} → W ∣ θ ⊢ p ⊢ D ◃ L′
  → (¬ err ∈ᴿ retᴿ (mem L′) m)
    × (∀ L₁′ → mem L₁′ ⊆ ⌊ retᴿ (mem L′) m ⌋ m → W ∣ θ ⊢ p ⊢ D ◃ L₁′)
id◃R {θ} {W} {p} {D} L′ rel =
  (λ ()) ,
  λ L₁′ L₁⊆ → ◃-sub⊆ {W} {θ} {p} {D} {L′} {L₁′}
                 (λ x x∈ → proj₂ (L₁⊆ x x∈)) rel

R◃⇒ : ∀ d {θ W BC₁ BC₂ H₁ H₂ K₁ K₂ D L′ m}
  → (∀ {W′ X Y k} → W′ ∣ θ ⊢ K₁ ⊢ X ◃ Y
       → (¬ err ∈ᴿ ⟦ flip d , BC₁ ⟧ᶜ θ (mem Y) k)
         × (∀ Y₁ → mem Y₁ ⊆ ⌊ ⟦ flip d , BC₁ ⟧ᶜ θ (mem Y) k ⌋ k
              → W′ ∣ θ ⊢ H₁ ⊢ X ◃ Y₁))
  → (∀ {W′ X Y k} → W′ ∣ θ ⊢ H₂ ⊢ X ◃ Y
       → (¬ err ∈ᴿ ⟦ d , BC₂ ⟧ᶜ θ (mem Y) k)
         × (∀ Y₁ → mem Y₁ ⊆ ⌊ ⟦ d , BC₂ ⟧ᶜ θ (mem Y) k ⌋ k
              → W′ ∣ θ ⊢ K₂ ⊢ X ◃ Y₁))
  → W ∣ θ ⊢ H₁ ⇒⊑ H₂ ⊢ D ◃ L′
  → (¬ err ∈ᴿ ⟦ d , BC₁ ⇒⊑ BC₂ ⟧ᶜ θ (mem L′) m)
    × (∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ d , BC₁ ⇒⊑ BC₂ ⟧ᶜ θ (mem L′) m ⌋ m
         → W ∣ θ ⊢ K₁ ⇒⊑ K₂ ⊢ D ◃ L₁′)
R◃⇒ d {θ} {BC₁ = BC₁} {BC₂} {L′ = []} argIH resIH rel =
  (λ { (w∈ , ()) }) , out
  where
  out : ∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ d , BC₁ ⇒⊑ BC₂ ⟧ᶜ θ (mem []) _ ⌋ _ → _
  out [] L₁⊆ = tt₁
  out (v₁ ∷ L₁) L₁⊆ =
    ⊥-elim (∉[] (proj₁ (fun-out d BC₁ BC₂ θ (mem []) v₁ (L₁⊆ v₁ (here refl)))))
R◃⇒ d {θ} {W} {BC₁} {BC₂} {H₁} {H₂} {K₁} {K₂} {D} {v′ ∷ L″} {m}
    argIH resIH (all , lift ν∈ , f) =
  (λ { (w∈ , ()) }) , out
  where
  Lr0 = v′ ∷ L″
  out : ∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ d , BC₁ ⇒⊑ BC₂ ⟧ᶜ θ (mem Lr0) m ⌋ m
    → W ∣ θ ⊢ K₁ ⇒⊑ K₂ ⊢ D ◃ L₁′
  out [] L₁⊆ = tt₁
  out (v₁ ∷ L₁) L₁⊆ =
    lift (All-tab (v₁ ∷ L₁)
            (λ x x∈ → Λ-IsFun {F = c-⇒F d BC₁ BC₂ θ (mem Lr0)} x
               (proj₂ (fun-out d BC₁ BC₂ θ (mem Lr0) x (L₁⊆ x x∈))))) ,
    lift ν∈ , g
    where
    g : ∀ L₁₀ → L₁₀ ⊑ˢ (v₁ ∷ L₁) → ∀ m′ W′ → W ⊑ʷ W′ → length W′ ≡ m′
      → ∀ E → Consistent E
      → Rel◃ (sizeᴸ (v₁ ∷ L₁)) W′ θ K₁ E (argsAt m′ L₁₀)
      → Rel◃ᶜ (sizeᴸ (v₁ ∷ L₁)) W′ θ K₂ (D ●[ m′ ] E) (resultsAt m′ L₁₀)
    g L₁₀ s m′ W′ ext len E CE relA = body
      where
      A = argsAt m′ L₁₀
      IHA = argIH {W′} {E} {A} {m′} (◃-out A (args-sub-< m′ v₁ L₁ s) relA)
      E₁ = ⌊ ⟦ flip d , BC₁ ⟧ᶜ θ (mem A) m′ ⌋ m′
      Rs′ = resultsAt m′ L₁₀
      F′ = c-⇒F d BC₁ BC₂ θ (mem Lr0) (mem A) m′
      inF : ∀ r′ → r′ ⋵ Rs′ → r′ ∈ᴿ F′
      inF r′ r′∈ with results-∈⁻ L₁₀ r′∈
      inF r′ r′∈ | U , e∈
        with fun-out d BC₁ BC₂ θ (mem Lr0) (U ⟼ r′ at m′)
               (L₁⊆ _ (sub-mem s _ e∈))
      inF r′ r′∈ | U , e∈ | w∈ , (r∈ , U≢ , U≈) =
        c-⇒body-mono d BC₁ BC₂ θ (mem Lr0) m′ {mem U} {mem A}
          (λ u u∈ → args-∈⁺ e∈ u∈) r′ r∈
      -- the entries of the original list that the results use
      Good : Val → Set
      Good e = Σ[ V ∈ List Val ] Σ[ s′ ∈ Res ]
                 (e ≡ (V ⟼ s′ at m′) × mem V ⊆ E₁)
      GoodP : List Val → Set
      GoodP P = ∀ e → e ⋵ P → e ⋵ Lr0 × Good e
      Supp : List Val → Res → Set
      Supp P r′ =
        (r′ ≡ err × Σ[ V ∈ List Val ] ((V ⟼ err at m′) ⋵ P))
        ⊎ Σ[ m₃ ∈ ℕ ] Σ[ Lr ∈ List Val ]
            (r′ ∈ᴿ ⟦ d , BC₂ ⟧ᶜ θ (mem Lr) m₃
             × (∀ z → z ⋵ Lr
                  → Σ[ V ∈ List Val ] ((V ⟼ ret z m₃ at m′) ⋵ P)))
      Supp-mono : ∀ {P P′} → mem P ⊆ mem P′ → ∀ r′ → Supp P r′ → Supp P′ r′
      Supp-mono P⊆ r′ (inj₁ (eq , V , e∈)) = inj₁ (eq , V , P⊆ _ e∈)
      Supp-mono P⊆ r′ (inj₂ (m₃ , Lr , r∈ , cov)) =
        inj₂ (m₃ , Lr , r∈ ,
              λ z z∈ → proj₁ (cov z z∈) , P⊆ _ (proj₂ (cov z z∈)))
      fromCast : ∀ m₃ r′
        → r′ ∈ᴿ ⟦ d , BC₂ ⟧ᶜ θ (⌊ mem Lr0 ●[ m′ ] E₁ ⌋ m₃) m₃
        → Σ[ P ∈ List Val ] (GoodP P × Supp P r′)
      fromCast m₃ r′ r∈
        with c-fin d BC₂ θ m₃ (⌊ mem Lr0 ●[ m′ ] E₁ ⌋ m₃) r′ r∈
      fromCast m₃ r′ r∈ | Lr , Lr⊆ , r∈′
        with entries {D = mem Lr0} {E = E₁} {m′ = m′} {m₃ = m₃} Lr Lr⊆
      fromCast m₃ r′ r∈ | Lr , Lr⊆ , r∈′ | P , P⊆ , Pg , Pc =
        P , good , inj₂ (m₃ , Lr , r∈′ , Pc)
        where
        good : GoodP P
        good e e∈ with Pg e e∈
        good e e∈ | V , z , eq , V⊆ = P⊆ e e∈ , V , ret z m₃ , eq , V⊆
      supp1 : ∀ r′ → r′ ∈ᴿ F′ → Σ[ P ∈ List Val ] (GoodP P × Supp P r′)
      supp1 err r∈ with ⇒F-err d BC₁ BC₂ θ (mem Lr0) (mem A) m′ r∈
      supp1 err r∈ | inj₁ e₁ = ⊥-elim (proj₁ IHA e₁)
      supp1 err r∈ | inj₂ (inj₁ (V , e∈ , V⊆ , V≢)) =
        (V ⟼ err at m′) ∷ [] , good , inj₁ (refl , V , here refl)
        where
        good : GoodP ((V ⟼ err at m′) ∷ [])
        good e (here refl) = e∈ , V , err , refl , V⊆
      supp1 err r∈ | inj₂ (inj₂ (m₃ , c , e)) = fromCast m₃ err e
      supp1 (ret y m₃) r∈ =
        fromCast m₃ (ret y m₃) (⇒F-inv d BC₁ BC₂ θ (mem Lr0) (mem A) m′ r∈)
      collectS : ∀ Rs → (∀ r → r ⋵ Rs → r ∈ᴿ F′)
        → Σ[ P ∈ List Val ] (GoodP P × (∀ r → r ⋵ Rs → Supp P r))
      collectS [] h = [] , (λ e ()) , (λ r ())
      collectS (r ∷ Rs) h
        with supp1 r (h r (here refl))
           | collectS Rs (λ r′ r′∈ → h r′ (there r′∈))
      collectS (r ∷ Rs) h | P₁ , G₁ , S₁ | P₂ , G₂ , S₂ =
        P₁ ++ P₂ , goodcat , suppcat
        where
        goodcat : GoodP (P₁ ++ P₂)
        goodcat e e∈ with ∈-++⁻ P₁ e∈
        goodcat e e∈ | inj₁ e∈₁ = G₁ e e∈₁
        goodcat e e∈ | inj₂ e∈₂ = G₂ e e∈₂
        suppcat : ∀ r′ → r′ ⋵ (r ∷ Rs) → Supp (P₁ ++ P₂) r′
        suppcat r′ (here refl) = Supp-mono (c-mem-++ˡ {P₁} {P₂}) r′ S₁
        suppcat r′ (there r′∈) =
          Supp-mono (c-mem-++ʳ {P₁} {P₂}) r′ (S₂ r′ r′∈)
      col = collectS Rs′ inF
      P = proj₁ col
      GP = proj₁ (proj₂ col)
      SP = proj₂ (proj₂ col)
      sel = select Lr0 P (λ e e∈ → proj₁ (GP e e∈))
      L₀′ = proj₁ sel
      s₀ = proj₁ (proj₂ sel)
      L₀⊆P = proj₁ (proj₂ (proj₂ sel))
      P⊆L₀ = proj₂ (proj₂ (proj₂ sel))
      argsOK : mem (argsAt m′ L₀′) ⊆ E₁
      argsOK u u∈ with args-∈⁻ L₀′ u∈
      argsOK u u∈ | U , r , e∈ , u∈U with proj₂ (GP _ (L₀⊆P _ e∈))
      argsOK u u∈ | U , r , e∈ , u∈U | V , s′ , eq , V⊆ =
        entry-args eq V⊆ u u∈U
      hyp : Rel◃ᶜ (sizeᴸ Lr0) W′ θ H₂ (D ●[ m′ ] E) (resultsAt m′ L₀′)
      hyp = f L₀′ s₀ m′ W′ ext len E CE
              (◃-in (argsAt m′ L₀′) (args-sub-< m′ v′ L″ s₀)
                 (proj₂ IHA (argsAt m′ L₀′) argsOK))
      X₃ : ℕ → List Val
      X₃ m₃ = valuesAt m₃ (resultsAt m′ L₀′)
      Lr⊆X : ∀ m₃ Lr
        → (∀ z → z ⋵ Lr → Σ[ V ∈ List Val ] ((V ⟼ ret z m₃ at m′) ⋵ P))
        → mem Lr ⊆ mem (X₃ m₃)
      Lr⊆X m₃ Lr cov z z∈ =
        values-∈⁺ (results-∈⁺ (P⊆L₀ _ (proj₂ (cov z z∈))))
      body : Rel◃ᶜ (sizeᴸ (v₁ ∷ L₁)) W′ θ K₂ (D ●[ m′ ] E) Rs′
      body with hyp
      body | inj₁ e = inj₁ e
      body | inj₂ (lift ne₀ , h₀) = inj₂ (lift ne , h′)
        where
        res₃ : ∀ m₃ → X₃ m₃ ≢ []
          → Σ[ W₃ ∈ World ] (Lift₁ (W′ ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m₃)
              × ((¬ err ∈ᴿ ⟦ d , BC₂ ⟧ᶜ θ (mem (X₃ m₃)) m₃)
                 × (∀ Y₁ → mem Y₁ ⊆ ⌊ ⟦ d , BC₂ ⟧ᶜ θ (mem (X₃ m₃)) m₃ ⌋ m₃
                      → W₃ ∣ θ ⊢ K₂ ⊢ ⌊ D ●[ m′ ] E ⌋ m₃ ◃ Y₁)))
        res₃ m₃ neX with h₀ m₃ neX
        res₃ m₃ neX | W₃ , ext₃ , len₃ , rel₃ =
          W₃ , ext₃ , len₃ ,
          resIH {W₃} {⌊ D ●[ m′ ] E ⌋ m₃} {X₃ m₃} {m₃}
            (◃-out (X₃ m₃) (values-results-< m₃ m′ v′ L″ s₀) rel₃)
        ne : ¬ HasErr Rs′
        ne h with SP err (HasErr→∈ h)
        ne h | inj₁ (refl , V , e∈P) =
          ne₀ (∈→HasErr (results-∈⁺ (P⊆L₀ _ e∈P)))
        ne h | inj₂ (m₃ , Lr , e , cov) with c-nonempty d BC₂ θ err e
        ne h | inj₂ (m₃ , Lr , e , cov) | z₀ , z₀∈ =
          proj₁ (proj₂ (proj₂ (proj₂
            (res₃ m₃ (nonempty (Lr⊆X m₃ Lr cov z₀ z₀∈))))))
            (c-mono d BC₂ θ m₃ (Lr⊆X m₃ Lr cov) err e)
        Ys⊆ : ∀ m₃ → mem (valuesAt m₃ Rs′)
          ⊆ ⌊ ⟦ d , BC₂ ⟧ᶜ θ (mem (X₃ m₃)) m₃ ⌋ m₃
        Ys⊆ m₃ y y∈ with SP (ret y m₃) (values-∈⁻ Rs′ y∈)
        Ys⊆ m₃ y y∈ | inj₁ (() , _)
        Ys⊆ m₃ y y∈ | inj₂ (m₄ , Lr , y∈′ , cov) with c-ctr d BC₂ θ y∈′
        Ys⊆ m₃ y y∈ | inj₂ (m₄ , Lr , y∈′ , cov) | refl =
          c-mono d BC₂ θ m₃ (Lr⊆X m₃ Lr cov) (ret y m₃) y∈′
        h′ : ∀ m₃ → valuesAt m₃ Rs′ ≢ []
          → Σ[ W₃ ∈ World ] (Lift₁ (W′ ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m₃)
              × Rel◃ (sizeᴸ (v₁ ∷ L₁)) W₃ θ K₂ (⌊ D ●[ m′ ] E ⌋ m₃)
                  (valuesAt m₃ Rs′))
        h′ m₃ ne₃ with ne-head (valuesAt m₃ Rs′) ne₃
        h′ m₃ ne₃ | y₀ , y₀∈
          with c-nonempty d BC₂ θ (ret y₀ m₃) (Ys⊆ m₃ y₀ y₀∈)
        h′ m₃ ne₃ | y₀ , y₀∈ | z₀ , z₀∈ with res₃ m₃ (nonempty z₀∈)
        h′ m₃ ne₃ | y₀ , y₀∈ | z₀ , z₀∈ | W₃ , ext₃ , len₃ , noerr , rel₄ =
          W₃ , ext₃ , len₃ ,
          ◃-in (valuesAt m₃ Rs′) (values-results-< m₃ m′ v₁ L₁ s)
            (rel₄ (valuesAt m₃ Rs′) (Ys⊆ m₃))

R◃∀ : ∀ d {θ W BC₀ H₀ K₀ D L′ m}
  → (∀ σ {W′ X Y k} → W′ ∣ σ •ᵗ θ ⊢ H₀ ⊢ X ◃ Y
       → (¬ err ∈ᴿ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) (mem Y) k)
         × (∀ Y₁ → mem Y₁ ⊆ ⌊ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) (mem Y) k ⌋ k
              → W′ ∣ σ •ᵗ θ ⊢ K₀ ⊢ X ◃ Y₁))
  → W ∣ θ ⊢ ∀⊑ H₀ ⊢ D ◃ L′
  → (¬ err ∈ᴿ ⟦ d , ∀⊑ BC₀ ⟧ᶜ θ (mem L′) m)
    × (∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ d , ∀⊑ BC₀ ⟧ᶜ θ (mem L′) m ⌋ m
         → W ∣ θ ⊢ ∀⊑ K₀ ⊢ D ◃ L₁′)
R◃∀ d {θ} {BC₀ = BC₀} {L′ = []} bodyIH rel =
  (λ { (w∈ , ()) }) , out
  where
  out : ∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ d , ∀⊑ BC₀ ⟧ᶜ θ (mem []) _ ⌋ _ → _
  out [] L₁⊆ = tt₁
  out (v₁ ∷ L₁) L₁⊆ =
    ⊥-elim (∉[] (proj₁ (poly-out d BC₀ θ (mem []) v₁ (L₁⊆ v₁ (here refl)))))
R◃∀ d {θ} {W} {BC₀} {H₀} {K₀} {D} {v′ ∷ L″} {m}
    bodyIH (all , lift ν∈ , f) =
  (λ { (w∈ , ()) }) , out
  where
  Lr0 = v′ ∷ L″
  out : ∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ d , ∀⊑ BC₀ ⟧ᶜ θ (mem Lr0) m ⌋ m
    → W ∣ θ ⊢ ∀⊑ K₀ ⊢ D ◃ L₁′
  out [] L₁⊆ = tt₁
  out (v₁ ∷ L₁) L₁⊆ =
    lift (All-tab (v₁ ∷ L₁)
            (λ x x∈ → Λᴾ-IsPoly {F = c-∀F d BC₀ θ (mem Lr0)} x
               (proj₂ (poly-out d BC₀ θ (mem Lr0) x (L₁⊆ x x∈))))) ,
    lift ν∈ , g
    where
    g : ∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
      → Rel◃ᶜ (sizeᴸ (v₁ ∷ L₁)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) K₀ (D ◆ σ)
          (bodiesAt σ (v₁ ∷ L₁))
    g σ W′ q′ ext len = body
      where
      Bs₁ = bodiesAt σ (v₁ ∷ L₁)
      inF : ∀ r′ → r′ ⋵ Bs₁ → r′ ∈ᴿ c-∀F d BC₀ θ (mem Lr0) σ
      inF r′ r′∈ =
        proj₂ (poly-out d BC₀ θ (mem Lr0) (σ ⟼∀ r′)
                 (L₁⊆ _ (bodies-∈⁻ (v₁ ∷ L₁) r′∈)))
      X₃ : ℕ → List Val
      X₃ m₃ = valuesAt m₃ (bodiesAt σ Lr0)
      S⊆X : ∀ m₃ → ⌊ mem Lr0 ◆ σ ⌋ m₃ ⊆ mem (X₃ m₃)
      S⊆X m₃ x x∈ = values-∈⁺ (bodies-∈⁺ x∈)
      body : Rel◃ᶜ (sizeᴸ (v₁ ∷ L₁)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) K₀
               (D ◆ σ) Bs₁
      body with f σ W′ q′ ext len
      body | inj₁ e = inj₁ e
      body | inj₂ (lift ne₀ , h₀) = inj₂ (lift ne , h′)
        where
        res₃ : ∀ m₃ → X₃ m₃ ≢ []
          → Σ[ W₃ ∈ World ] (Lift₁ (W′ ++ (q′ ∷ []) ⊑ʷ W₃)
              × Lift₁ (length W₃ ≡ m₃)
              × ((¬ err ∈ᴿ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) (mem (X₃ m₃)) m₃)
                 × (∀ Y₁ → mem Y₁
                        ⊆ ⌊ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) (mem (X₃ m₃)) m₃ ⌋ m₃
                      → W₃ ∣ σ •ᵗ θ ⊢ K₀ ⊢ ⌊ D ◆ σ ⌋ m₃ ◃ Y₁)))
        res₃ m₃ neX with h₀ m₃ neX
        res₃ m₃ neX | W₃ , ext₃ , len₃ , rel₃ =
          W₃ , ext₃ , len₃ ,
          bodyIH σ {W₃} {⌊ D ◆ σ ⌋ m₃} {X₃ m₃} {m₃}
            (◃-out (X₃ m₃) (values-bodies-< m₃ σ v′ L″) rel₃)
        ne : ¬ HasErr Bs₁
        ne h with ∀F-err d BC₀ θ (mem Lr0) σ (inF err (HasErr→∈ h))
        ne h | inj₁ e = ne₀ (∈→HasErr (bodies-∈⁺ e))
        ne h | inj₂ (m₃ , (x , x∈) , e) =
          proj₁ (proj₂ (proj₂ (proj₂ (res₃ m₃ (nonempty (S⊆X m₃ x x∈))))))
            (c-mono d BC₀ (σ •ᵗ θ) m₃ (S⊆X m₃) err e)
        Ys⊆ : ∀ m₃ → mem (valuesAt m₃ Bs₁)
          ⊆ ⌊ ⟦ d , BC₀ ⟧ᶜ (σ •ᵗ θ) (mem (X₃ m₃)) m₃ ⌋ m₃
        Ys⊆ m₃ y y∈ =
          c-mono d BC₀ (σ •ᵗ θ) m₃ (S⊆X m₃) (ret y m₃)
            (∀F-inv d BC₀ θ (mem Lr0) σ (inF _ (values-∈⁻ Bs₁ y∈)))
        h′ : ∀ m₃ → valuesAt m₃ Bs₁ ≢ []
          → Σ[ W₃ ∈ World ] (Lift₁ (W′ ++ (q′ ∷ []) ⊑ʷ W₃)
              × Lift₁ (length W₃ ≡ m₃)
              × Rel◃ (sizeᴸ (v₁ ∷ L₁)) W₃ (σ •ᵗ θ) K₀ (⌊ D ◆ σ ⌋ m₃)
                  (valuesAt m₃ Bs₁))
        h′ m₃ ne₃ with ne-head (valuesAt m₃ Bs₁) ne₃
        h′ m₃ ne₃ | y₀ , y₀∈
          with c-nonempty d BC₀ (σ •ᵗ θ) (ret y₀ m₃) (Ys⊆ m₃ y₀ y₀∈)
        h′ m₃ ne₃ | y₀ , y₀∈ | z₀ , z₀∈ with res₃ m₃ (nonempty z₀∈)
        h′ m₃ ne₃ | y₀ , y₀∈ | z₀ , z₀∈ | W₃ , ext₃ , len₃ , noerr , rel₄ =
          W₃ , ext₃ , len₃ ,
          ◃-in (valuesAt m₃ Bs₁) (values-bodies-< m₃ σ v₁ L₁)
            (rel₄ (valuesAt m₃ Bs₁) (Ys⊆ m₃))

-- the outputs of an up cast through tag G
up-tag-out : ∀ {θ G BC₀ X m} x
  → x ∈ ⌊ ⟦ up , tag G BC₀ ⟧ᶜ θ X m ⌋ m
  → Σ[ u ∈ Val ] (x ≡ injᵛ (⟦ G ⟧ᴳ θ) u × u ∈ ⌊ ⟦ up , BC₀ ⟧ᶜ θ X m ⌋ m)
up-tag-out x (inj₁ (() , e∈))
up-tag-out {m = m} x (inj₂ (m₁ , c , x∈)) with c-inj-ret-inv (ret x m) x∈
up-tag-out {m = m} x (inj₂ (m₁ , c , x∈)) | u , refl , u∈ = u , refl , u∈

mutual
  upR◃ : ∀ {n θ W AB BC AC A B C D L′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → W ∣ θ ⊢ AB ⊢ D ◃ L′
    → (¬ err ∈ᴿ ⟦ up , BC ⟧ᶜ θ (mem L′) m)
      × (∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ up , BC ⟧ᶜ θ (mem L′) m ⌋ m
           → W ∣ θ ⊢ AC ⊢ D ◃ L₁′)
  upR◃ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ rel with tag-split AB⊢ wfG BC₀⊢ AC⊢
  upR◃ {θ = θ} {W} {D = D} {L′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢) AC⊢
      rel | AC′ , AC′⊢ , refl =
    c-up-noerr (tag G BC₀) θ , out
    where
    G′ = ⟦ G ⟧ᴳ θ
    IH = upR◃ {θ = θ} {W} {D = D} {L′} {m} AB⊢ BC₀⊢ AC′⊢ rel
    out : ∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ up , tag G BC₀ ⟧ᶜ θ (mem L′) m ⌋ m
      → W ∣ θ ⊢ tag G AC′ ⊢ D ◃ L₁′
    out L₁′ L₁⊆ =
      ◃-tag-in {θ} {W} {G} {AC′} {D} L₁′ (lift (All-tab L₁′ atG))
        (proj₂ IH (untagᴸ G′ L₁′) P⊆)
      where
      atG : ∀ x → x ⋵ L₁′ → IsInjAt G′ x
      atG x x∈ with up-tag-out {θ} {G} {BC₀} {mem L′} {m} x (L₁⊆ x x∈)
      atG x x∈ | u , refl , u∈ = is-inj-at
      P⊆ : mem (untagᴸ G′ L₁′) ⊆ ⌊ ⟦ up , BC₀ ⟧ᶜ θ (mem L′) m ⌋ m
      P⊆ u u∈ with up-tag-out {θ} {G} {BC₀} {mem L′} {m} _
                     (L₁⊆ _ (untag-∈⁻ L₁′ u∈))
      P⊆ u u∈ | u′ , refl , u′∈ = u′∈
  upR◃ AB⊢ ⊑★ AC⊢ rel with ⊑-unique AB⊢ AC⊢
  upR◃ {L′ = L′} AB⊢ ⊑★ AC⊢ rel | refl = id◃R L′ rel
  upR◃ {L′ = L′} (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) rel = id◃R L′ rel
  upR◃ {L′ = L′} ⊑𝔹 ⊑𝔹 ⊑𝔹 rel = id◃R L′ rel
  upR◃ {θ = θ} {W} {D = D} {L′} {m} (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢)
      (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢) (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) rel =
    R◃⇒ up {θ} {W} {BC₁} {BC₂} {AB₁} {AB₂} {AC₁} {AC₂} {D} {L′} {m}
      (λ {W′} {X} {Y} {k} r →
         downR◃ {θ = θ} {W′} {D = X} {L′ = Y} {k} AB₁⊢ BC₁⊢ AC₁⊢ r)
      (λ {W′} {X} {Y} {k} r →
         upR◃ {θ = θ} {W′} {D = X} {L′ = Y} {k} AB₂⊢ BC₂⊢ AC₂⊢ r)
      rel
  upR◃ {θ = θ} {W} {D = D} {L′} {m} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢)
      (⊑∀ {AC₀} AC₀⊢) rel =
    R◃∀ up {θ} {W} {BC₀} {AB₀} {AC₀} {D} {L′} {m}
      (λ σ {W′} {X} {Y} {k} r →
         upR◃ {θ = σ •ᵗ θ} {W′} {D = X} {L′ = Y} {k} AB₀⊢ BC₀⊢ AC₀⊢ r)
      rel

  downR◃ : ∀ {n θ W AB BC AC A B C D L′ m}
    → n ⊢ AB ⦂ A ⊑ B → n ⊢ BC ⦂ B ⊑ C → n ⊢ AC ⦂ A ⊑ C
    → W ∣ θ ⊢ AC ⊢ D ◃ L′
    → (¬ err ∈ᴿ ⟦ down , BC ⟧ᶜ θ (mem L′) m)
      × (∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ down , BC ⟧ᶜ θ (mem L′) m ⌋ m
           → W ∣ θ ⊢ AB ⊢ D ◃ L₁′)
  downR◃ AB⊢ (⊑tag wfG BC₀⊢) AC⊢ rel with tag-split AB⊢ wfG BC₀⊢ AC⊢
  downR◃ {θ = θ} {W} {D = D} {L′} {m} AB⊢ (⊑tag {G} {BC₀} wfG BC₀⊢) AC⊢
      rel | AC′ , AC′⊢ , refl
    with ◃-tag-out {θ} {W} {G} {AC′} {D} L′ rel
  ... | lift allAt , rel₀ = noerr , out
    where
    G′ = ⟦ G ⟧ᴳ θ
    IH = downR◃ {θ = θ} {W} {D = D} {untagᴸ G′ L′} {m} AB⊢ BC₀⊢ AC′⊢ rel₀
    grp⊆ : ∀ {m₁} → ⌊ proj G′ (mem L′) m ⌋ m₁ ⊆ mem (untagᴸ G′ L′)
    grp⊆ y (eq , i∈) = untag-∈⁺ i∈
    noerr : ¬ err ∈ᴿ ⟦ down , tag G BC₀ ⟧ᶜ θ (mem L′) m
    noerr (inj₁ (refl , H , v , i∈ , H≢)) with All-lookup allAt i∈
    noerr (inj₁ (refl , H , v , i∈ , H≢)) | is-inj-at = H≢ refl
    noerr (inj₂ (m₁ , (c , refl , c∈) , e)) =
      proj₁ IH (c-mono down BC₀ θ m grp⊆ err e)
    out : ∀ L₁′ → mem L₁′ ⊆ ⌊ ⟦ down , tag G BC₀ ⟧ᶜ θ (mem L′) m ⌋ m
      → W ∣ θ ⊢ _ ⊢ D ◃ L₁′
    out L₁′ L₁⊆ = proj₂ IH L₁′ sub
      where
      sub : mem L₁′ ⊆ ⌊ ⟦ down , BC₀ ⟧ᶜ θ (mem (untagᴸ G′ L′)) m ⌋ m
      sub x x∈ with L₁⊆ x x∈
      sub x x∈ | inj₁ (() , e)
      sub x x∈ | inj₂ (m₁ , (c , refl , c∈) , x∈′) =
        c-mono down BC₀ θ m grp⊆ (ret x m) x∈′
  downR◃ AB⊢ ⊑★ AC⊢ rel with ⊑-unique AC⊢ AB⊢
  downR◃ {L′ = L′} AB⊢ ⊑★ AC⊢ rel | refl = id◃R L′ rel
  downR◃ {L′ = L′} (⊑‵ w₁) (⊑‵ w₂) (⊑‵ w₃) rel = id◃R L′ rel
  downR◃ {L′ = L′} ⊑𝔹 ⊑𝔹 ⊑𝔹 rel = id◃R L′ rel
  downR◃ {θ = θ} {W} {D = D} {L′} {m} (⊑⇒ {AB₁} {AB₂} AB₁⊢ AB₂⊢)
      (⊑⇒ {BC₁} {BC₂} BC₁⊢ BC₂⊢) (⊑⇒ {AC₁} {AC₂} AC₁⊢ AC₂⊢) rel =
    R◃⇒ down {θ} {W} {BC₁} {BC₂} {AC₁} {AC₂} {AB₁} {AB₂} {D} {L′} {m}
      (λ {W′} {X} {Y} {k} r →
         upR◃ {θ = θ} {W′} {D = X} {L′ = Y} {k} AB₁⊢ BC₁⊢ AC₁⊢ r)
      (λ {W′} {X} {Y} {k} r →
         downR◃ {θ = θ} {W′} {D = X} {L′ = Y} {k} AB₂⊢ BC₂⊢ AC₂⊢ r)
      rel
  downR◃ {θ = θ} {W} {D = D} {L′} {m} (⊑∀ {AB₀} AB₀⊢) (⊑∀ {BC₀} BC₀⊢)
      (⊑∀ {AC₀} AC₀⊢) rel =
    R◃∀ down {θ} {W} {BC₀} {AC₀} {AB₀} {D} {L′} {m}
      (λ σ {W′} {X} {Y} {k} r →
         downR◃ {θ = σ •ᵗ θ} {W′} {D = X} {L′ = Y} {k} AB₀⊢ BC₀⊢ AC₀⊢ r)
      rel

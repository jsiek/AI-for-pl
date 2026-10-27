module proof.DenotSoundness where

-- File Charter:
--   * Soundness of the denotation (Denotation.agda) for the reduction of the
--     cast calculus: subject expansion (M —→ N implies ⟦ N ⟧ ⊆ ⟦ M ⟧ for a
--     well-typed closed M), via the substitution lemma and the β law of Λ.
--   * Consequences: a program that reduces to a value denotes a set with a
--     value of the same observation; one that reduces to blame denotes a set
--     holding ω.

open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import Coercions
open import CastCalculus
open import DynamicGradualGuaranteeDefinitions using (observe)
open import GraphModel
open import Denotation
open import proof.CastCalculusMeta using (preserveᶜ; preserveᶜ*)
open import proof.DenotProps

------------------------------------------------------------------------
-- The error monad
------------------------------------------------------------------------

ω? : ∀ d → d ≡ ω ⊎ d ≢ ω
ω? (nat n) = inj₂ (λ ())
ω? (V ⟼ w) = inj₂ (λ ())
ω? ν = inj₂ (λ ())
ω? ω = inj₁ refl
ω? (tag t d) = inj₂ (λ ())

valset-⌊⌋ : ∀ {D} → ValSet D → D ⊆ ⌊ D ⌋
valset-⌊⌋ noω d d∈ = d∈ , λ { refl → noω d∈ }

Conv-⌊⌋ : ∀ {D} → Conv D → Conv ⌊ D ⌋
Conv-⌊⌋ (d , d∈ , d≢) = d , (d∈ , d≢) , d≢

⌊⌋-valset : ∀ {D} → ValSet ⌊ D ⌋
⌊⌋-valset (ω∈ , ω≢) = ω≢ refl

Λ-valset : ∀ {F} → ValSet (Λ F)
Λ-valset ()

Λ-≢ : ∀ {F e} → e ∈ Λ F → e ≢ ω
Λ-≢ e∈ refl = e∈

≫=-conv : ∀ {D F} → Conv D → F ⌊ D ⌋ ⊆ (D ≫= F)
≫=-conv c w w∈ = inj₂ (c , w∈)

≫=-val : ∀ {D F} → ValSet D → (D ≫= F) ⊆ F ⌊ D ⌋
≫=-val noω w (inj₁ (eq , ω∈)) = ⊥-elim (noω ω∈)
≫=-val noω w (inj₂ (c , w∈)) = w∈

≫=-unit : ∀ {D} → D ⊆ (D ≫= λ X → X)
≫=-unit w w∈ with ω? w
≫=-unit w w∈ | inj₁ refl = inj₁ (refl , w∈)
≫=-unit w w∈ | inj₂ w≢ = inj₂ ((w , w∈ , w≢) , (w∈ , w≢))

≫=-assoc : ∀ {D f g} → (∀ {X Y} → X ⊆ Y → g X ⊆ g Y)
  → ((D ≫= f) ≫= g) ⊆ (D ≫= λ X → f X ≫= g)
≫=-assoc gm w (inj₁ (eq , inj₁ (_ , ω∈D))) = inj₁ (eq , ω∈D)
≫=-assoc gm w (inj₁ (eq , inj₂ (cD , ω∈f))) = inj₂ (cD , inj₁ (eq , ω∈f))
≫=-assoc gm w (inj₂ ((e , inj₁ (eq , _) , e≢) , w∈)) = ⊥-elim (e≢ eq)
≫=-assoc {D = D} {f = f} gm w (inj₂ ((e , inj₂ (cD , e∈) , e≢) , w∈)) =
  inj₂ (cD , inj₂ ((e , e∈ , e≢) , gm sub w w∈))
  where
  sub : ⌊ D ≫= f ⌋ ⊆ ⌊ f ⌊ D ⌋ ⌋
  sub x (inj₁ (eq , _) , x≢) = ⊥-elim (x≢ eq)
  sub x (inj₂ (_ , x∈) , x≢) = x∈ , x≢

app-⊆ : ∀ {D D′ E E′} → D ⊆ D′ → E ⊆ E′
  → (D ≫= λ F → E ≫= λ X → F ● X) ⊆ (D′ ≫= λ F → E′ ≫= λ X → F ● X)
app-⊆ D⊆ E⊆ = ≫=-mono D⊆ (λ F⊆ → ≫=-mono E⊆ (λ X⊆ → ●-mono F⊆ X⊆))

cast-⊆ : ∀ {D D′} c → D ⊆ D′ → (D ≫= ⟦ c ⟧ᶜ) ⊆ (D′ ≫= ⟦ c ⟧ᶜ)
cast-⊆ c D⊆ = ≫=-mono D⊆ (⟦⟧ᶜ-mono c)

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

ground-tag : ∀ {G} → Ground G → Σ[ t ∈ Tag ] (tagTy t ≡ G)
ground-tag G-ℕ = ℕᵗ , refl
ground-tag G-⇒ = ⇒ᵗ , refl

-- a well-typed closed value denotes a set of values with one of its
-- observation
value-denot : ∀ {V A} ρ → [] ⊢ᶜ V ⦂ A → (v : Valueᶜ V)
  → ValSet (⟦ V ⟧ ρ)
    × Σ[ d ∈ Val ] (d ∈ ⟦ V ⟧ ρ × d ≢ ω × obs d ≡ observe v)
value-denot ρ ⊢$ (V-$ {n = n}) = (λ ()) , nat n , refl , (λ ()) , refl
value-denot ρ (⊢ƛ {N = N} N⦂) V-ƛ =
  Λ-valset {F = λ Y → ⟦ N ⟧ (Y • ρ)} , ν , tt , (λ ()) , refl
value-denot ρ (⊢cast {M = W} W⦂ (⊢! {G = G} g)) (V-cast! vW) =
  noω , tag t d , inj₂ ((d , d∈ , d≢) , eq , d∈ , d≢) , (λ ()) , obs≡
  where
  r = value-denot ρ W⦂ vW
  t = proj₁ (ground-tag g)
  eq = proj₂ (ground-tag g)
  d = proj₁ (proj₂ r)
  d∈ = proj₁ (proj₂ (proj₂ r))
  d≢ = proj₁ (proj₂ (proj₂ (proj₂ r)))
  obs≡ = proj₂ (proj₂ (proj₂ (proj₂ r)))
  noω : ValSet (⟦ W ⟧ ρ ≫= inj G)
  noω (inj₁ (_ , ω∈)) = proj₁ r ω∈
  noω (inj₂ (_ , ()))
value-denot ρ (⊢cast {M = W} W⦂ (⊢↦ {c = c} {d = d} c⦂ d⦂)) (V-cast↦ vW) =
  noω , ν , inj₂ (cW , Conv-⌊⌋ cW , tt) , (λ ()) , refl
  where
  r = value-denot ρ W⦂ vW
  cW : Conv (⟦ W ⟧ ρ)
  cW = proj₁ (proj₂ r) , proj₁ (proj₂ (proj₂ r)) ,
       proj₁ (proj₂ (proj₂ (proj₂ r)))
  noω : ValSet (⟦ W ⟧ ρ ≫= ⟦ c ↦ d ⟧ᶜ)
  noω (inj₁ (_ , ω∈)) = proj₁ r ω∈
  noω (inj₂ (_ , _ , ()))

value-conv : ∀ {V A} ρ → [] ⊢ᶜ V ⦂ A → Valueᶜ V → Conv (⟦ V ⟧ ρ)
value-conv ρ V⦂ v =
  proj₁ (proj₂ r) , proj₁ (proj₂ (proj₂ r)) ,
  proj₁ (proj₂ (proj₂ (proj₂ r)))
  where
  r = value-denot ρ V⦂ v

value-valset : ∀ {V A} ρ → [] ⊢ᶜ V ⦂ A → Valueᶜ V → ValSet (⟦ V ⟧ ρ)
value-valset ρ V⦂ v = proj₁ (value-denot ρ V⦂ v)

------------------------------------------------------------------------
-- Renaming and substitution
------------------------------------------------------------------------

ren-⊆ : ∀ M r ρ → ⟦ renameᶜ r M ⟧ ρ ⊆ ⟦ M ⟧ (λ x → ρ (r x))
ren-⊆ (` x) r ρ = ⊆-refl
ren-⊆ ($ n) r ρ = ⊆-refl
ren-⊆ (ƛ A ⇒ N) r ρ =
  Λ-mono (λ Y → ⊆-trans {E = ⟦ N ⟧ (λ x → (Y • ρ) (extᶜ r x))}
    (ren-⊆ N (extᶜ r) (Y • ρ)) (⟦⟧-mono N (incl Y)))
  where
  incl : ∀ Y → (λ x → (Y • ρ) (extᶜ r x)) ⊆ₑ (Y • (λ x → ρ (r x)))
  incl Y zero = ⊆-refl
  incl Y (suc x) = ⊆-refl
ren-⊆ (L · M) r ρ = app-⊆ (ren-⊆ L r ρ) (ren-⊆ M r ρ)
ren-⊆ (cast M [ c ]) r ρ = cast-⊆ c (ren-⊆ M r ρ)
ren-⊆ blame r ρ = ⊆-refl

sub-⊆ : ∀ M σ ρ → ⟦ substᶜ σ M ⟧ ρ ⊆ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
sub-⊆ (` x) σ ρ = ⊆-refl
sub-⊆ ($ n) σ ρ = ⊆-refl
sub-⊆ (ƛ A ⇒ N) σ ρ =
  Λ-mono (λ Y → ⊆-trans {E = ⟦ N ⟧ (λ x → ⟦ extsᶜ σ x ⟧ (Y • ρ))}
    (sub-⊆ N (extsᶜ σ) (Y • ρ)) (⟦⟧-mono N (incl Y)))
  where
  incl : ∀ Y → (λ x → ⟦ extsᶜ σ x ⟧ (Y • ρ))
               ⊆ₑ (Y • (λ x → ⟦ σ x ⟧ ρ))
  incl Y zero = ⊆-refl
  incl Y (suc x) = ren-⊆ (σ x) suc (Y • ρ)
sub-⊆ (L · M) σ ρ = app-⊆ (sub-⊆ L σ ρ) (sub-⊆ M σ ρ)
sub-⊆ (cast M [ c ]) σ ρ = cast-⊆ c (sub-⊆ M σ ρ)
sub-⊆ blame σ ρ = ⊆-refl

------------------------------------------------------------------------
-- Subject expansion
------------------------------------------------------------------------

expand : ∀ {M N A} ρ → [] ⊢ᶜ M ⦂ A → M —→ N → ⟦ N ⟧ ρ ⊆ ⟦ M ⟧ ρ
expand ρ (⊢· L⦂ M⦂) (ξξ {F = □· M} refl refl L→L′) =
  app-⊆ (expand ρ L⦂ L→L′) ⊆-refl
expand ρ (⊢· V⦂ M⦂) (ξξ {F = V ·□ vV} refl refl M→M′) =
  app-⊆ ⊆-refl (expand ρ M⦂ M→M′)
expand ρ (⊢cast M⦂ c⦂) (ξξ {F = cast□[ c ]} refl refl M→M′) =
  cast-⊆ c (expand ρ M⦂ M→M′)
expand ρ (⊢· (⊢ƛ {A = A} {N = N} N⦂) V⦂) (β-ƛ {V = V} vV) w w∈ =
  ≫=-conv {D = ⟦ ƛ A ⇒ N ⟧ ρ} {F = λ F → ⟦ V ⟧ ρ ≫= λ X → F ● X}
    (ν , tt , (λ ())) w
    (≫=-conv {F = λ X → ⌊ ⟦ ƛ A ⇒ N ⟧ ρ ⌋ ● X} (value-conv ρ V⦂ vV) w
      (●-mono (valset-⌊⌋ {D = ⟦ ƛ A ⇒ N ⟧ ρ}
                 (Λ-valset {F = λ Y → ⟦ N ⟧ (Y • ρ)}))
              (valset-⌊⌋ {D = ⟦ V ⟧ ρ} (value-valset ρ V⦂ vV)) w
        (Λ-β N ρ (value-valset ρ V⦂ vV) (value-conv ρ V⦂ vV) w
          (⟦⟧-mono N incl w (sub-⊆ N (singleEnvᶜ V) ρ w w∈)))))
  where
  incl : (λ x → ⟦ singleEnvᶜ V x ⟧ ρ) ⊆ₑ (⟦ V ⟧ ρ • ρ)
  incl zero = ⊆-refl
  incl (suc x) = ⊆-refl
expand ρ (⊢cast V⦂ ⊢idᶜ) (β-id {V = V} vV) = ≫=-unit {D = ⟦ V ⟧ ρ}
expand ρ (⊢cast M⦂ (⊢⨟ {c = c} {d = d} c⦂ d⦂)) (β-seq {V = V} vV) =
  ≫=-assoc {D = ⟦ V ⟧ ρ} {f = ⟦ c ⟧ᶜ} (⟦⟧ᶜ-mono d)
expand ρ (⊢· (⊢cast V⦂ (⊢↦ {c = c} {d = d} c⦂ d⦂)) W⦂)
    (β-↦ {V = V} {W = W} vV vW) w w∈ =
  ≫=-conv {F = λ F → DW ≫= λ X → F ● X} convCast w
    (≫=-conv {F = λ X → ⌊ DV ≫= ⟦ c ↦ d ⟧ᶜ ⌋ ● X} convW w
      (●-mono incl ⊆-refl w
        (Λ-βᶜ c d ⌊ DV ⌋ (⌊⌋-valset {D = DW}) (Conv-⌊⌋ {D = DW} convW) w
          (≫=-assoc {D = ⟦ c ⟧ᶜ ⌊ DW ⌋} {f = λ X → ⌊ DV ⌋ ● X}
             (⟦⟧ᶜ-mono d) w
            (≫=-mono s₁ (⟦⟧ᶜ-mono d) w w∈)))))
  where
  DV = ⟦ V ⟧ ρ
  DW = ⟦ W ⟧ ρ
  noωV = value-valset ρ V⦂ vV
  noωW = value-valset ρ W⦂ vW
  convV = value-conv ρ V⦂ vV
  convW = value-conv ρ W⦂ vW
  s₁ : (DV ≫= λ F → (DW ≫= ⟦ c ⟧ᶜ) ≫= λ X → F ● X)
       ⊆ (⟦ c ⟧ᶜ ⌊ DW ⌋ ≫= λ X → ⌊ DV ⌋ ● X)
  s₁ = ⊆-trans
         (≫=-val {D = DV} {F = λ F → (DW ≫= ⟦ c ⟧ᶜ) ≫= λ X → F ● X} noωV)
         (≫=-mono {D = DW ≫= ⟦ c ⟧ᶜ} {D′ = ⟦ c ⟧ᶜ ⌊ DW ⌋}
            {F = λ X → ⌊ DV ⌋ ● X} {F′ = λ X → ⌊ DV ⌋ ● X}
            (≫=-val {D = DW} {F = ⟦ c ⟧ᶜ} noωW)
            (λ X⊆ → ●-mono {D = ⌊ DV ⌋} ⊆-refl X⊆))
  convCast : Conv (DV ≫= ⟦ c ↦ d ⟧ᶜ)
  convCast = ν , inj₂ (convV , Conv-⌊⌋ {D = DV} convV , tt) , (λ ())
  incl : Λ (λ Y → ⟦ c ⟧ᶜ Y ≫= λ Y₁ → (⌊ DV ⌋ ● Y₁) ≫= ⟦ d ⟧ᶜ)
         ⊆ ⌊ DV ≫= ⟦ c ↦ d ⟧ᶜ ⌋
  incl e e∈ = inj₂ (convV , Conv-⌊⌋ {D = DV} convV , e∈) , Λ-≢ e∈
expand ρ (⊢cast V⦂ ⊢⊥) (β-⊥ vV) w refl =
  inj₂ (value-conv ρ V⦂ vV , Conv-⌊⌋ (value-conv ρ V⦂ vV) , refl)
expand ρ (⊢cast (⊢cast V⦂ (⊢! g)) (⊢? g′))
    (β-proj-inj-ok {V = V} {G = G} vV) w w∈ =
  inj₂ (convI , inj₁ (t , eq , inI , (λ ())))
  where
  t = proj₁ (ground-tag g)
  eq = proj₂ (ground-tag g)
  w≢ = proj₂ (valset-⌊⌋ {D = ⟦ V ⟧ ρ} (value-valset ρ V⦂ vV) w w∈)
  inI : tag t w ∈ (⟦ V ⟧ ρ ≫= inj G)
  inI = inj₂ (value-conv ρ V⦂ vV , eq , w∈ , w≢)
  convI : Conv (⟦ V ⟧ ρ ≫= inj G)
  convI = tag t w , inI , (λ ())
expand ρ (⊢cast (⊢cast V⦂ (⊢! g)) (⊢? g′))
    (β-proj-inj-bad {V = V} {G = G} {H = H} vV G≢H) w refl =
  inj₂ (convI , inj₂ (refl , t , d , (inI , (λ ())) ,
        (λ tH → G≢H (trans (sym eq) tH))))
  where
  t = proj₁ (ground-tag g)
  eq = proj₂ (ground-tag g)
  convV = value-conv ρ V⦂ vV
  d = proj₁ convV
  inI : tag t d ∈ (⟦ V ⟧ ρ ≫= inj G)
  inI = inj₂ (convV , eq , proj₂ convV)
  convI : Conv (⟦ V ⟧ ρ ≫= inj G)
  convI = tag t d , inI , (λ ())
expand ρ (⊢· L⦂ M⦂) (ξξ-blame {F = □· M} refl) w refl = inj₁ (refl , refl)
expand ρ (⊢· V⦂ M⦂) (ξξ-blame {F = V ·□ vV} refl) w refl =
  inj₂ (value-conv ρ V⦂ vV , inj₁ (refl , refl))
expand ρ (⊢cast M⦂ c⦂) (ξξ-blame {F = cast□[ c ]} refl) w refl =
  inj₁ (refl , refl)

expand* : ∀ {M N A} ρ → [] ⊢ᶜ M ⦂ A → M —↠ N → ⟦ N ⟧ ρ ⊆ ⟦ M ⟧ ρ
expand* ρ M⦂ (ms-refl M) = ⊆-refl
expand* ρ M⦂ (ms-step L L→M M↠N) =
  ⊆-trans (expand* ρ (preserveᶜ M⦂ L→M) M↠N) (expand ρ M⦂ L→M)

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

sound-val : ∀ {M V A} → [] ⊢ᶜ M ⦂ A → (v : Valueᶜ V) → M —↠ V
  → Σ[ d ∈ Val ] (d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω × obs d ≡ observe v)
sound-val M⦂ v M↠V =
  proj₁ (proj₂ r) ,
  expand* ρ₀ M⦂ M↠V _ (proj₁ (proj₂ (proj₂ r))) ,
  proj₂ (proj₂ (proj₂ r))
  where
  r = value-denot ρ₀ (preserveᶜ* M⦂ M↠V) v

sound-blame : ∀ {M A ℓ} → [] ⊢ᶜ M ⦂ A → M —↠ blame {ℓ = ℓ}
  → ω ∈ ⟦ M ⟧ ρ₀
sound-blame M⦂ M↠b = expand* ρ₀ M⦂ M↠b ω refl

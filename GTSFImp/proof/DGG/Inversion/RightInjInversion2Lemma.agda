module proof.DGG.Inversion.RightInjInversion2Lemma where

-- File Charter:
--   * Proves the right-injection inversion statement without parameters.
--   * Recurses directly through source-only spine constructors in the
--     canonical cast-term imprecision relation.
--   * Uses only type-level tag transport as a separate induction boundary.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using
  (TyStore; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; keep; skip; toRenameᵗ;
   id; _!; ∀ᶜ_; gen_; inst_)
import Consistency as C
import proof.Consistency as PC
open import Conversion using
  (Conv↑; Conv↓; `∀↑_; `∀↓_; _↦↑_; _↦↓_;
   ⊢↓-seal)
open import Imprecision
open import Primitives using (Const; κℕ; κ𝔹)
open import CastTerms
open import Reduction
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.TagTransport as TT
open import proof.DGG.World
open CTI2 using (_⊢²_⊑_∶_)
open SVD using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all;
   variable-obligation-aligns)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; source-occurs-target; rename-occurs;
   ext-injective; toRenameᵗ-injective; nonstar-from-≢★; rename-⊑;
   fin-suc-injective; nonvar-occurs-nonstar; all-ground-body)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using
  (toRename-keep-eq; renameᵗ-skip-eq)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)

------------------------------------------------------------------------
-- Higher-order right-injection inversion for spine values
------------------------------------------------------------------------

module _ where

  lift-left-body : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {A : Ty (suc (Δᵉ Γᴸ))} {B : Ty (Δᵉ Γᴿ)}
    → instᵐ (marksᶜ γ) ⊢
        renameᵗ (extᵗ (toRenameᵗ (ηᴸᶜ γ))) A
          ⊑ ⇑ᵗ (renameᵗ (toRenameᵗ (ηᴿᶜ γ)) B)
    → A ⊑ᵀ⟨ liftLeftᶜ γ ⟩ B
  lift-left-body {γ = γ} {A = A} body =
    subst≡ (λ Bᶜ → _ ⊢ _ ⊑ Bᶜ)
      (sym (renameᵗ-skip-eq (ηᴿᶜ γ) _))
      (subst≡ (λ Aᶜ → _ ⊢ Aᶜ ⊑ _)
        (sym (renameᵗ-cong A (toRename-keep-eq (ηᴸᶜ γ)))) body)

  right-inj-inversion² : RightInjInversion²

  -- Target-only cast: the premise already carries the tag obligation.
  right-inj-inversion² sv vN
      (CTI2.⊑cast² {p = p₀} c′ prem q₀) q =
    subst≡ (λ r → _ ⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p₀ q) prem

  -- Paired cast: keep the source cast as a source-only cast.
  right-inj-inversion² sv vN
      (CTI2.cast⊑cast² c c′ prem q₀) q =
    CTI2.cast⊑² c prem q

  -- Source-only cast around an injection value: no obligation matches.
  right-inj-inversion² {gH = ＇ Y} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ‵ ι} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ★⇒★} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ∀★} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()

  -- Source-only function cast: the premise components rebuild the
  -- premise-level tag obligation.
  right-inj-inversion² {gH = ★⇒★} (sv-cast sv fun)
      vN (CTI2.cast⊑² {p = ⇒⊑★ pA pB} c prem q₀) (⇒⊑⇒ qA qB) =
    CTI2.cast⊑² c
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ＇ Y} (sv-cast sv fun)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ‵ ι} (sv-cast sv fun)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ∀★} (sv-cast sv fun)
    vN (CTI2.cast⊑² c prem q₀) ()

  -- Source-only universal cast: chase the tag through the cast with the
  -- embedded consistency evidence.
  right-inj-inversion² {γ = γ} {gH = gH}
      (sv-cast sv (all {c = c₁}))
      vN (CTI2.cast⊑² {p = p₀} .(∀ᶜ c₁) prem q₀) q =
    CTI2.cast⊑² (∀ᶜ c₁)
      (right-inj-inversion² sv vN prem
        (ground-cast-source⊑ (PC.renameGroundᵐ (ηᴿᶜ γ) gH) nonstar-∀
          (C.renameᵐᶜ (ηᴸᶜ γ) (∀ᶜ c₁)) p₀ q₀ q))
      q

  -- Source-only generalization cast: same, with the gen tag's source.
  right-inj-inversion² {γ = γ} {gH = gH}
      (sv-cast sv (genᵥ A≢★ safe))
      vN (CTI2.cast⊑² {p = p₀} c prem q₀) q =
    CTI2.cast⊑² c
      (right-inj-inversion² sv vN prem
        (ground-cast-source⊑ (PC.renameGroundᵐ (ηᴿᶜ γ) gH)
          (C.renameNonStar (toRenameᵗ (ηᴸᶜ γ))
            (nonstar-from-≢★ A≢★))
          (C.renameᵐᶜ (ηᴸᶜ γ) c) p₀ q₀ q))
      q


  -- A source-only type abstraction recurses under the canonical left lift.
  right-inj-inversion² {γ = γ} {A = `∀ A} {H = H} {gH = gH}
      (sv-Λ sv) vN
      (CTI2.Λ⊑² Anv zero∈A vV (⊢⟨⟩ N⊢ _) prem q₀) q =
    CTI2.Λ⊑² {γ = γ} Anv zero∈A vV N⊢
      (right-inj-inversion² sv vN prem
        (lift-left-body {γ = γ} {A = A} {B = H}
          (all-ground-body
            (renameNonVar (extᵗ (toRenameᵗ (ηᴸᶜ γ))) Anv)
            (rename-occurs (extᵗ (toRenameᵗ (ηᴸᶜ γ)))
              (ext-injective (toRenameᵗ-injective (ηᴸᶜ γ))) zero∈A)
            (PC.renameGroundᵐ (ηᴿᶜ γ) gH) q)))
      q

  -- Function-shaped reveal: the premise's ⇒⊑★ components rebuild the
  -- premise-level tag obligation, and by ⊑-unique it does not matter
  -- that this inhabitant differs from any other.
  right-inj-inversion² {gH = ★⇒★} (sv-reveal-fun sv)
      vN (CTI2.reveal⊑-identity {p = ⇒⊑★ pA pB}
        c⊢ position≡absent prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.reveal⊑-identity c⊢ position≡absent
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ★⇒★} (sv-reveal-fun sv)
      vN (CTI2.reveal⊑-only² {p = ⇒⊑★ pA pB}
        c⊢ position≠absent dynamic no-target represented prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.reveal⊑-only² c⊢ position≠absent dynamic no-target
      represented
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ＇ Y} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑-identity _ _ _ _) ()
  right-inj-inversion² {gH = ‵ ι} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑-identity _ _ _ _) ()
  right-inj-inversion² {gH = ∀★} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑-identity _ _ _ _) ()
  right-inj-inversion² {gH = ＇ Y} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑-only² _ _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ‵ ι} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑-only² _ _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ∀★} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑-only² _ _ _ _ _ _ _) ()

  -- Function-shaped conceal: same construction.
  right-inj-inversion² {gH = ★⇒★} (sv-conceal-fun sv)
      vN (CTI2.conceal⊑-identity {p = ⇒⊑★ pA pB}
        c⊢ position≡absent prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.conceal⊑-identity c⊢ position≡absent
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ★⇒★} (sv-conceal-fun sv)
      vN (CTI2.conceal⊑-only² {p = ⇒⊑★ pA pB}
        c⊢ position≠absent dynamic no-target represented prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.conceal⊑-only² c⊢ position≠absent dynamic no-target
      represented
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ＇ Y} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑-identity _ _ _ _) ()
  right-inj-inversion² {gH = ‵ ι} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑-identity _ _ _ _) ()
  right-inj-inversion² {gH = ∀★} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑-identity _ _ _ _) ()
  right-inj-inversion² {gH = ＇ Y} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑-only² _ _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ‵ ι} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑-only² _ _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ∀★} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑-only² _ _ _ _ _ _ _) ()

  -- Universal reveal: transport the requested tag obligation through the
  -- body conversion.  Variable rebases recurse in the honestified world.
  right-inj-inversion² {γ = γ} {gH = ★⇒★}
      (sv-reveal-all sv) vN
      (CTI2.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≡absent prem q₀) q =
    CTI2.reveal⊑-identity (Conv.⊢↑-∀ refl c⊢)
      position≡absent
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ∀★} (sv-reveal-all sv) vN
      (CTI2.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≡absent prem q₀) q =
    CTI2.reveal⊑-identity (Conv.⊢↑-∀ refl c⊢)
      position≡absent
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-all c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ‵ ι} (sv-reveal-all sv) vN
      (CTI2.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≡absent prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  right-inj-inversion² {γ = γ} {gH = ＇ Y} (sv-reveal-all sv) vN
      (CTI2.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≡absent prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  right-inj-inversion² {γ = γ} {gH = ★⇒★}
      (sv-reveal-all sv) vN
      (CTI2.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    CTI2.reveal⊑-only² (Conv.⊢↑-∀ refl c⊢)
      position≠absent dynamic no-target represented
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ∀★} (sv-reveal-all sv) vN
      (CTI2.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    CTI2.reveal⊑-only² (Conv.⊢↑-∀ refl c⊢)
      position≠absent dynamic no-target represented
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-all c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ‵ ι} (sv-reveal-all sv) vN
      (CTI2.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  right-inj-inversion² {γ = γ} {gH = ＇ Y} (sv-reveal-all sv) vN
      (CTI2.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  -- Universal conceal: the dual transport has the same obligations, while
  -- the variable-rebase decay uses conceal's opposite rebase orientation.
  right-inj-inversion² {γ = γ} {gH = ★⇒★}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≡absent prem q₀) q =
    CTI2.conceal⊑-identity (Conv.⊢↓-∀ refl c⊢)
      position≡absent
      (right-inj-inversion² sv vN prem
        (TT.transport↓-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ∀★}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≡absent prem q₀) q =
    CTI2.conceal⊑-identity (Conv.⊢↓-∀ refl c⊢)
      position≡absent
      (right-inj-inversion² sv vN prem
        (TT.transport↓-∀-all c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ‵ ι}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≡absent prem q₀) q =
    ⊥-elim
      (TT.transport↓-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  right-inj-inversion² {γ = γ} {gH = ＇ Y} (sv-conceal-all sv) vN
      (CTI2.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≡absent prem q₀) q =
    ⊥-elim
      (TT.transport↓-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  right-inj-inversion² {γ = γ} {gH = ★⇒★}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    CTI2.conceal⊑-only² (Conv.⊢↓-∀ refl c⊢) position≠absent
      dynamic no-target represented
      (right-inj-inversion² sv vN prem
        (TT.transport↓-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ∀★}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    CTI2.conceal⊑-only² (Conv.⊢↓-∀ refl c⊢) position≠absent
      dynamic no-target represented
      (right-inj-inversion² sv vN prem
        (TT.transport↓-∀-all c⊢
          (toRenameᵗ-injective (ηᴸᶜ γ))
          (toRenameᵗ-injective (ηᴸᶜ γ))
          p₀ q))
      q
  right-inj-inversion² {γ = γ} {gH = ‵ ι}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    ⊥-elim
      (TT.transport↓-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  right-inj-inversion² {γ = γ} {gH = ＇ Y} (sv-conceal-all sv) vN
      (CTI2.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
        position≠absent dynamic no-target represented prem q₀) q =
    ⊥-elim
      (TT.transport↓-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸᶜ γ)) (toRenameᵗ-injective (ηᴸᶜ γ))
        p₀ q)
  -- Bare unmatched source seal.
  right-inj-inversion² {gH = ‵ ι} (sv-seal sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal X∈) position≠absent
        dynamic no-target represented prem q₀) q
      with q
  right-inj-inversion² {gH = ‵ ι} (sv-seal sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal X∈) position≠absent
        dynamic no-target represented prem q₀) q
      | ()
  right-inj-inversion² {gH = ★⇒★} (sv-seal sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal X∈) position≠absent
        dynamic no-target represented prem q₀) q
      with q
  right-inj-inversion² {gH = ★⇒★} (sv-seal sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal X∈) position≠absent
        dynamic no-target represented prem q₀) q
      | ()
  right-inj-inversion² {gH = ∀★} (sv-seal sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal X∈) position≠absent
        dynamic no-target represented prem q₀) q
      with q
  right-inj-inversion² {gH = ∀★} (sv-seal sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal X∈) position≠absent
        dynamic no-target represented prem q₀) q
      | ()
  right-inj-inversion² {γ = γ} {gH = ＇ Y}
      (sv-seal {X = Xᴸ} {R = R} sv) vN
      (CTI2.conceal⊑-only² (Conv.⊢↓-seal Xᴸ∈) position≠absent
        dynamic disaligned represented prem q₀) q =
    ⊥-elim
      (disaligned Y
        (sym (variable-obligation-aligns {γ = γ} {X = Xᴸ} {Y = Y} q)))
  right-inj-inversion² (sv-seal sv) vN
      (CTI2.conceal⊑-identity (Conv.⊢↓-seal X∈) () prem q₀) q

  -- Type applications are not spine values.
  right-inj-inversion² () vN (CTI2.•⊑² _ _ _ _) q

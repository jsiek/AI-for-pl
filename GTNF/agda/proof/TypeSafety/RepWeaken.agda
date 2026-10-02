module proof.TypeSafety.RepWeaken where

-- File Charter:
--   * REPRESENTATION-ONLY MOVES OF A TYPING DERIVATION — the two
--     transports whose movers have an IDENTITY ordinary component:
--     `ShiftTyping` (§2, THE SIBLING SHIFT every congruence of
--     `preserve` consumes) and `CrossΛTyping` (§3, what substitution
--     consumes when an image crosses `Λ`).  §1 is the renaming
--     induction they are both instances of.
--   * THE WORKHORSE IS THE CUT `⊢renᴿ`: the insertion is abstracted
--     into an arbitrary `RepWk ρ Ξ Ξ′` and the name map is renamed
--     POINTWISE, so going under `Λ` is just `extᵗ ρ`.  The term
--     context passes through UNCHANGED, and crossing a boundary runs
--     the SAME ρ — there is no bind block to offset.
--   * THE PAYLOAD MUST BE WELL FORMED, or the shift is FALSE.
-- Commentary: Commentary.md § proof/RepWeaken.agda

open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Properties using (_≟_; _<?_; +-cancelˡ-≡)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Properties using (length-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import Ctx
open import proof.Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst
open import proof.TermSubst
open import proof.TypeSafety.PreservationSupport
  using (CrossΛTyping; ShiftTyping; repwk-alloc; WfRen-wk; wf-ren;
         wf-same; same-weaken; wf-underΛ; ν-boundary-ren)

------------------------------------------------------------------------
-- §1  The renaming induction
------------------------------------------------------------------------

⊢ctx-cast : ∀ {Ξ : RepCtx} {η η′ : TyCtx} {Γ : Ctx} {M : Term} {A : Ty}
  → η ≡ η′ → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A → (Ξ ∣ η′) ∣ Γ ⊢ M ⦂ A
⊢ctx-cast refl ⊢M = ⊢M

mutual
  toExt-renᴮᴿ : ∀ {ρ} → Injᵗ ρ → (Θ : Boundary) → (X : ℕ)
    → toExt (renᴮᴿ ρ Θ) X ≡ toExt Θ X
  toExt-renᴮᴿ inj [] X = refl
  toExt-renᴮᴿ {ρ} inj (bind Y α ∷ Θ) X with X ≟ Y
  toExt-renᴮᴿ {ρ} inj (bind Y α ∷ Θ) X | yes eq =
    seekUnbind-renᴮᴿ inj α Θ
  toExt-renᴮᴿ {ρ} inj (bind Y α ∷ Θ) X | no ne with X <? Y
  toExt-renᴮᴿ {ρ} inj (bind Y α ∷ Θ) X | no ne | yes lt =
    toExt-renᴮᴿ inj Θ X
  toExt-renᴮᴿ {ρ} inj (bind Y α ∷ Θ) X | no ne | no nlt =
    toExt-renᴮᴿ inj Θ (pred X)
  toExt-renᴮᴿ {ρ} inj (unbind Y α ∷ Θ) X with X <? Y
  toExt-renᴮᴿ {ρ} inj (unbind Y α ∷ Θ) X | yes lt =
    toExt-renᴮᴿ inj Θ X
  toExt-renᴮᴿ {ρ} inj (unbind Y α ∷ Θ) X | no nlt =
    toExt-renᴮᴿ inj Θ (suc X)

  seekUnbind-renᴮᴿ : ∀ {ρ} → Injᵗ ρ → (α : ℕ) → (Θ : Boundary)
    → seekUnbind (ρ α) (renᴮᴿ ρ Θ) ≡ seekUnbind α Θ
  seekUnbind-renᴮᴿ inj α [] = refl
  seekUnbind-renᴮᴿ inj α (bind Y β ∷ Θ) =
    seekUnbind-renᴮᴿ inj α Θ
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y β ∷ Θ) with α ≟ β
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y β ∷ Θ) | yes refl
      with ρ α ≟ ρ α
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y .α ∷ Θ) | yes refl | yes eq =
    toExt-renᴮᴿ inj Θ Y
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y .α ∷ Θ) | yes refl | no ne =
    ⊥-elim (ne refl)
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y β ∷ Θ) | no ne
      with ρ α ≟ ρ β
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y β ∷ Θ) | no ne | yes eq =
    ⊥-elim (ne (inj eq))
  seekUnbind-renᴮᴿ {ρ} inj α (unbind Y β ∷ Θ) | no ne | no neq =
    seekUnbind-renᴮᴿ inj α Θ

mutual
  simple-renᴹᴿ : ∀ {M ρ} → Injᵗ ρ → Simple M → Simple (renᴹᴿ ρ M)
  simple-renᴹᴿ inj S-$ = S-$
  simple-renᴹᴿ inj S-true = S-true
  simple-renᴹᴿ inj S-false = S-false
  simple-renᴹᴿ inj S-ƛ = S-ƛ
  simple-renᴹᴿ {ρ = ρ} inj (S-Λ v) =
    S-Λ (value-renᴹᴿ (inj-extᵗ inj) v)
  simple-renᴹᴿ inj (S-cast v inert) =
    S-cast (value-renᴹᴿ inj v) inert

  value-renᴹᴿ : ∀ {M ρ} → Injᵗ ρ → Value M → Value (renᴹᴿ ρ M)
  value-renᴹᴿ inj (V-simple u) = V-simple (simple-renᴹᴿ inj u)
  value-renᴹᴿ inj (V-⟪⟫ u it) = V-⟪⟫ (simple-renᴹᴿ inj u) it
  value-renᴹᴿ inj (V-fresh {Θ = Θ} {X = X} v fresh) =
    V-fresh (value-renᴹᴿ inj v)
      (trans (toExt-renᴮᴿ inj Θ X) fresh)

coercion-ctx-cast : ∀ {Ξ : RepCtx} {η η′ : TyCtx} {μ p A B}
  → η ≡ η′
  → (Ξ ∣ η) ∣ μ ⊢ᵖ p ∶ A ⟹ B
  → (Ξ ∣ η′) ∣ μ ⊢ᵖ p ∶ A ⟹ B
coercion-ctx-cast refl ⊢p = ⊢p

coercion-renᴿ : ∀ {Ξ Ξ′ η ρ μ p A B}
  → RepWk ρ Ξ Ξ′
  → (Ξ ∣ η) ∣ μ ⊢ᵖ p ∶ A ⟹ B
  → (Ξ′ ∣ map ρ η) ∣ μ ⊢ᵖ p ∶ A ⟹ B
coercion-renᴿ w (⊢id wA) = ⊢id (wf-ren-rep wA)
coercion-renᴿ w (⊢tag g) = ⊢tag g
coercion-renᴿ {ρ = ρ} w (⊢tag-var tv mode ok) =
  ⊢tag-var (tv-ren ρ tv) mode ok
coercion-renᴿ w (⊢check g) = ⊢check g
coercion-renᴿ {ρ = ρ} w (⊢check-var tv mode ok) =
  ⊢check-var (tv-ren ρ tv) mode ok
coercion-renᴿ w (⊢fun ⊢p ⊢q) =
  ⊢fun (coercion-renᴿ w ⊢p) (coercion-renᴿ w ⊢q)
coercion-renᴿ {η = η} {ρ = ρ} w (⊢all ⊢p) =
  ⊢all (coercion-ctx-cast (names-underΛ-ren ρ η)
          (coercion-renᴿ (repwk-abst w) ⊢p))
coercion-renᴿ {η = η} {ρ = ρ} w (⊢inst ⊢p wB nv occ ns) =
  ⊢inst (coercion-ctx-cast (names-underΛ-ren ρ η)
           (coercion-renᴿ (repwk-abst w) ⊢p))
        (wf-ren-rep wB) nv occ ns
coercion-renᴿ {η = η} {ρ = ρ} w (⊢gen ⊢p wA nv occ ns safe) =
  ⊢gen (coercion-ctx-cast (names-underΛ-ren ρ η)
          (coercion-renᴿ (repwk-abst w) ⊢p))
       (wf-ren-rep wA) nv occ ns safe
coercion-renᴿ {ρ = ρ} w (⊢seq-tag ⊢p tg ns) =
  ⊢seq-tag (coercion-renᴿ w ⊢p) (tag-ground-renᴿ ρ tg) ns
  where
  tag-ground-renᴿ : ∀ {Ξ Ξ′ η μ G}
    → (ρ : Renameᵗ)
    → TagGround (Ξ ∣ η) μ G
    → TagGround (Ξ′ ∣ map ρ η) μ G
  tag-ground-renᴿ ρ (tg-nv g) = tg-nv g
  tag-ground-renᴿ ρ (tg-var tv mode ok) = tg-var (tv-ren ρ tv) mode ok
coercion-renᴿ {ρ = ρ} w (⊢seq-check cg ⊢p ns) =
  ⊢seq-check (check-ground-renᴿ ρ cg) (coercion-renᴿ w ⊢p) ns
  where
  check-ground-renᴿ : ∀ {Ξ Ξ′ η μ G}
    → (ρ : Renameᵗ)
    → CheckGround (Ξ ∣ η) μ G
    → CheckGround (Ξ′ ∣ map ρ η) μ G
  check-ground-renᴿ ρ (cg-nv g) = cg-nv g
  check-ground-renᴿ ρ (cg-var tv mode ok) = cg-var (tv-ren ρ tv) mode ok
coercion-renᴿ w ⊢bot-elim = ⊢bot-elim
coercion-renᴿ w ⊢bot-intro = ⊢bot-intro

⊢renᴿ : ∀ {Ξ Ξ′ : RepCtx} {η : TyCtx} {ρ : Renameᵗ}
          {Γ : Ctx} {M : Term} {A : Ty}
  → RepWk ρ Ξ Ξ′
  → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
  → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A
⊢renᴿ w (⊢` d) = ⊢` d
⊢renᴿ w ⊢$ = ⊢$
⊢renᴿ w ⊢true = ⊢true
⊢renᴿ w ⊢false = ⊢false
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢ƛ wA ⊢N) =
  ⊢ƛ (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA) (⊢renᴿ w ⊢N)
⊢renᴿ w (⊢· ⊢L ⊢M) = ⊢· (⊢renᴿ w ⊢L) (⊢renᴿ w ⊢M)
⊢renᴿ {η = η} {ρ = ρ} w (⊢Λ vN ⊢N) =
  ⊢Λ (value-renᴹᴿ (inj-extᵗ (wk-inj w)) vN)
     (⊢ctx-cast (names-underΛ-ren ρ η) (⊢renᴿ (repwk-abst w) ⊢N))
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢ν wA rA ⊢L mw ⊢c same wB)
  with ν-boundary-ren w rA mw ⊢c same
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢ν wA rA ⊢L mw ⊢c same wB)
  | Δ′ , mw′ , ⊢c′ , same′ =
  ⊢ν (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA) (same-ren ρ rA)
     (⊢renᴿ w ⊢L) mw′ ⊢c′ same′
     (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wB)
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {η = η} {ρ = ρ} w
      (boundary (bw wΔ (interior cs) (conversion csᶜ))
           ⊢M ⊢c (Rᵢ , pᵢ , qᵢ) (Rₑ , pₑ , qₑ) wE) =
  boundary (bw (wfctx-ren w wΔ)
          (interior-ren w (interior cs))
          (conversion-ren w (conversion csᶜ)))
      (⊢renᴿ w ⊢M)
      (conv-ren w ⊢c)
      (renameᵗ ρ Rᵢ , same-ren ρ pᵢ , same-ren ρ qᵢ)
      (renameᵗ ρ Rₑ , same-ren ρ pₑ , same-ren ρ qₑ)
      (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wE)
⊢renᴿ {η = η} {ρ = ρ} w (⊢cast ⊢M ⊢p len) =
  ⊢cast (⊢renᴿ w ⊢M) (coercion-renᴿ w ⊢p)
        (trans len (sym (length-map ρ η)))
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢blame wA) =
  ⊢blame (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA)

------------------------------------------------------------------------
-- §2  The sibling shift
------------------------------------------------------------------------

-- THE INSTANCE THE STORE RUNS AT: `allocate R (Ξ ∣ η)` is literally
-- `(bindR R ∷ Ξ) ∣ map suc η`, so the one new lemma of the store
-- experiment is `⊢renᴿ` at `repwk-alloc`, with no cast at all.
shift-⊢ : ShiftTyping
shift-⊢ wR ⊢M = ⊢renᴿ (repwk-alloc wR) ⊢M

------------------------------------------------------------------------
-- §3  Crossing one `Λ`
------------------------------------------------------------------------

cross-Λ-⊢ : CrossΛTyping
cross-Λ-⊢ {Δ = Ξ ∣ η} {W = W} {A = A} wfΔ wA ⊢W =
  boundary mwΛ inner (mkId-⊢ w↑) sameᵢ sameₑ w↑
  where
  Δᵢ : Ctxᵗ
  Δᵢ = (abstR ∷ Ξ) ∣ shiftReps η

  w↑ : underΛ (Ξ ∣ η) ⊢ᵗ ⇑ᵗ A
  w↑ = wf-ren (WfRen-wk {Δ = Ξ ∣ η}) wA

  mwΛ : BoundaryWf (underΛ (Ξ ∣ η))
          ((unbind 0 0 ∷ [])) Δᵢ (underΛ (Ξ ∣ η))
  mwΛ =
    bw (wf-underΛ wfΔ)
       (interior (changes∷ changes[]
                   (step-unbind (_ , here) del-here fresh-zero-shift)))
       (conversion (conv-unbind (_ , here) conv[]))

  inner : Δᵢ ∣ [] ⊢ renᴹᴿ suc W ⦂ A
  inner = ⊢renᴿ repwk-abst₀ ⊢W

  sameᵢ : Δᵢ ⊢ A ≈ ⇑ᵗ A ⊣ underΛ (Ξ ∣ η)
  sameᵢ with wf-same wA
  sameᵢ | R , p = ⇑ᵗ R , same-ren suc p , same-weaken p

  sameₑ : underΛ (Ξ ∣ η) ⊢ ⇑ᵗ A ≈ ⇑ᵗ A ⊣ underΛ (Ξ ∣ η)
  sameₑ with wf-same w↑
  sameₑ | R , p = R , p , p

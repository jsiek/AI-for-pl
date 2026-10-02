module proof.TypeSafety.ExitScope where

-- File Charter:
--   * WHERE A MOVED TAG LANDS: the facts `IdDyn`/`IdDyn-var`
--     preservation needs about `toExt` and `exitEnv` (Reduction §0).
--   * §1 lookups through one inserted or deleted name.  §2 `toExt` is
--     SOUND: an interior name that `toExt` sends to exterior position X′
--     denotes, at X′, the same rep. var.  §3 on unique names it is
--     therefore injective, so `exitEnv` finds the interior mode of the
--     moved name; §4 `exitEnv` has one mode per exterior name.

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; _<?_; +-suc; +-identityʳ; ≤∧≢⇒<; ≮⇒≥)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Ctx
open import proof.Ctx
open import Boundary
open import Coercion using (Mode; ModeEnv)
open import Reduction using (modeAtExt; exitEnvFrom; exitEnv)

private
  variable
    Ξ : RepCtx
    η η′ ηᵢ : TyCtx
    X X′ Y : ℕ
    α β : RVar

------------------------------------------------------------------------
-- §1  Lookups through one insertion or deletion
------------------------------------------------------------------------

ins-at : α ⊢+ η at Y ⇒ η′ → η′ ∋ˡ Y := α
ins-at ins-here = here
ins-at (ins-there i) = there (ins-at i)

ins-below : α ⊢+ η at Y ⇒ η′ → η′ ∋ˡ X := β → X < Y → η ∋ˡ X := β
ins-below ins-here d ()
ins-below (ins-there i) here lt = here
ins-below (ins-there i) (there d) (s≤s lt) = there (ins-below i d lt)

ins-above : α ⊢+ η at Y ⇒ η′ → η′ ∋ˡ X := β → Y < X
  → η ∋ˡ pred X := β
ins-above ins-here here ()
ins-above ins-here (there d) lt = d
ins-above (ins-there i) here ()
ins-above (ins-there i) (there d) (s≤s lt@(s≤s _)) =
  there (ins-above i d lt)

ins-fresh-back : α ⊢+ η at Y ⇒ η′ → η′ ∌ʳ β → η ∌ʳ β
ins-fresh-back ins-here (fresh∷ ne f) = f
ins-fresh-back (ins-there i) (fresh∷ ne f) =
  fresh∷ ne (ins-fresh-back i f)

del-at : α ⊢- η at Y ⇒ η′ → η ∋ˡ Y := α
del-at del-here = here
del-at (del-there d) = there (del-at d)

del-below : α ⊢- η at Y ⇒ η′ → η′ ∋ˡ X := β → X < Y → η ∋ˡ X := β
del-below del-here d ()
del-below (del-there dl) here lt = here
del-below (del-there dl) (there d) (s≤s lt) = there (del-below dl d lt)

del-above : α ⊢- η at Y ⇒ η′ → η′ ∋ˡ X := β → Y ≤ X
  → η ∋ˡ suc X := β
del-above del-here d le = there d
del-above (del-there dl) here ()
del-above (del-there dl) (there d) (s≤s le) = there (del-above dl d le)

del-fresh-back : α ⊢- η at Y ⇒ η′ → η′ ∌ʳ β → β ≢ α → η ∌ʳ β
del-fresh-back del-here f ne = fresh∷ ne f
del-fresh-back (del-there d) (fresh∷ ne′ f) ne =
  fresh∷ ne′ (del-fresh-back d f ne)

------------------------------------------------------------------------
-- §2  `toExt` is sound
------------------------------------------------------------------------

mutual
  toExt-sound : ∀ {Θ}
    → Ξ ∣ η ⊢χ Θ ⇒ ηᵢ
    → ηᵢ ∋ˡ X := α
    → toExt Θ X ≡ just X′
    → η ∋ˡ X′ := α
  toExt-sound changes[] d refl = d
  toExt-sound {X = X} (changes∷ {δ = bind Y β} cs (step-bind v fr i)) d e
    with X ≟ Y
  toExt-sound {X = X} (changes∷ {δ = bind Y β} cs (step-bind v fr i)) d e
    | yes refl with ∋ˡ-det d (ins-at i)
  toExt-sound {X = X} (changes∷ {δ = bind Y β} cs (step-bind v fr i)) d e
    | yes refl | refl = seek-sound cs fr e
  toExt-sound {X = X} (changes∷ {δ = bind Y β} cs (step-bind v fr i)) d e
    | no ne with X <? Y
  toExt-sound {X = X} (changes∷ {δ = bind Y β} cs (step-bind v fr i)) d e
    | no ne | yes lt = toExt-sound cs (ins-below i d lt) e
  toExt-sound {X = X} (changes∷ {δ = bind Y β} cs (step-bind v fr i)) d e
    | no ne | no nlt =
    toExt-sound cs (ins-above i d (≤∧≢⇒< (≮⇒≥ nlt) (λ eq → ne (sym eq))))
                e
  toExt-sound {X = X}
      (changes∷ {δ = unbind Y β} cs (step-unbind v dl fr)) d e
    with X <? Y
  toExt-sound {X = X}
      (changes∷ {δ = unbind Y β} cs (step-unbind v dl fr)) d e
    | yes lt = toExt-sound cs (del-below dl d lt) e
  toExt-sound {X = X}
      (changes∷ {δ = unbind Y β} cs (step-unbind v dl fr)) d e
    | no nlt = toExt-sound cs (del-above dl d (≮⇒≥ nlt)) e

  seek-sound : ∀ {Θ}
    → Ξ ∣ η ⊢χ Θ ⇒ ηᵢ
    → ηᵢ ∌ʳ β
    → seekUnbind β Θ ≡ just X′
    → η ∋ˡ X′ := β
  seek-sound changes[] f ()
  seek-sound (changes∷ {δ = bind Y γ} cs (step-bind v fr i)) f e =
    seek-sound cs (ins-fresh-back i f) e
  seek-sound {β = β}
      (changes∷ {δ = unbind Y γ} cs (step-unbind v dl fr)) f e
    with β ≟ γ
  seek-sound {β = β}
      (changes∷ {δ = unbind Y γ} cs (step-unbind v dl fr)) f e
    | yes refl = toExt-sound cs (del-at dl) e
  seek-sound {β = β}
      (changes∷ {δ = unbind Y γ} cs (step-unbind v dl fr)) f e
    | no ne = seek-sound cs (del-fresh-back dl f ne) e

------------------------------------------------------------------------
-- §3  `exitEnv` finds the moved name's interior mode
------------------------------------------------------------------------

modeAt-find : ∀ (Θ : Boundary) {μ : ModeEnv} {X m} (i j : ℕ)
  → μ ∋ˡ X := m
  → toExt Θ (X + i) ≡ just j
  → (∀ {Y m′} → μ ∋ˡ Y := m′ → toExt Θ (Y + i) ≡ just j → Y ≡ X)
  → modeAtExt Θ μ i j ≡ m
modeAt-find Θ i j here e u with toExt Θ i
modeAt-find Θ i j here refl u | just j′ with j ≟ j′
modeAt-find Θ i j here refl u | just j′ | yes _ = refl
modeAt-find Θ i j here refl u | just j′ | no ne = ⊥-elim (ne refl)
modeAt-find Θ {μ = m₀ ∷ μ} {X = suc X} i j (there d) e u
    with toExt Θ i in eq
modeAt-find Θ {μ = m₀ ∷ μ} {X = suc X} i j (there d) e u
    | nothing =
  modeAt-find Θ (suc i) j d (trans (cong (toExt Θ) (+-suc X i)) e) u′
  where
  u′ : ∀ {Y m′} → μ ∋ˡ Y := m′ → toExt Θ (Y + suc i) ≡ just j → Y ≡ X
  u′ {Y} d′ e′ =
    cong pred (u (there d′) (trans (cong (toExt Θ) (sym (+-suc Y i))) e′))
modeAt-find Θ {μ = m₀ ∷ μ} {X = suc X} i j (there d) e u
    | just j′ with j ≟ j′
modeAt-find Θ {μ = m₀ ∷ μ} {X = suc X} i j (there d) e u
    | just j′ | yes refl with u here eq
modeAt-find Θ {μ = m₀ ∷ μ} {X = suc X} i j (there d) e u
    | just j′ | yes refl | ()
modeAt-find Θ {μ = m₀ ∷ μ} {X = suc X} i j (there d) e u
    | just j′ | no ne =
  modeAt-find Θ (suc i) j d (trans (cong (toExt Θ) (+-suc X i)) e) u′
  where
  u′ : ∀ {Y m′} → μ ∋ˡ Y := m′ → toExt Θ (Y + suc i) ≡ just j → Y ≡ X
  u′ {Y} d′ e′ =
    cong pred (u (there d′) (trans (cong (toExt Θ) (sym (+-suc Y i))) e′))

------------------------------------------------------------------------
-- §4  `exitEnv` has one mode per exterior name
------------------------------------------------------------------------

exitEnvFrom-length : ∀ (Θ : Boundary) (μ : ModeEnv) (j r : ℕ)
  → length (exitEnvFrom Θ μ j r) ≡ r
exitEnvFrom-length Θ μ j zero = refl
exitEnvFrom-length Θ μ j (suc r) = cong suc (exitEnvFrom-length Θ μ (suc j) r)

exitEnv-length : ∀ (Θ : Boundary) (μ : ModeEnv) (n : ℕ)
  → length (exitEnv Θ μ n) ≡ n
exitEnv-length Θ μ n = exitEnvFrom-length Θ μ 0 n

exitEnvFrom-lookup : ∀ (Θ : Boundary) (μ : ModeEnv) (j k r : ℕ)
  → k < r
  → exitEnvFrom Θ μ j r ∋ˡ k := modeAtExt Θ μ 0 (k + j)
exitEnvFrom-lookup Θ μ j zero (suc r) lt = here
exitEnvFrom-lookup Θ μ j (suc k) (suc r) (s≤s lt) =
  subst (λ z → exitEnvFrom Θ μ j (suc r) ∋ˡ suc k := modeAtExt Θ μ 0 z)
        (+-suc k j) (there (exitEnvFrom-lookup Θ μ (suc j) k r lt))

exitEnv-lookup : ∀ (Θ : Boundary) (μ : ModeEnv) {k n : ℕ}
  → k < n
  → exitEnv Θ μ n ∋ˡ k := modeAtExt Θ μ 0 (k + 0)
exitEnv-lookup Θ μ {k} {n} lt = exitEnvFrom-lookup Θ μ 0 k n lt

------------------------------------------------------------------------
-- §5  The moved tag's mode, assembled
------------------------------------------------------------------------

lookup-lt : ∀ {A : Set} {xs : List A} {k a} → xs ∋ˡ k := a → k < length xs
lookup-lt here = s≤s z≤n
lookup-lt (there d) = s≤s (lookup-lt d)

lookup-transfer : ∀ {A B : Set} {xs : List A} {ys : List B} {k a}
  → length xs ≡ length ys → xs ∋ˡ k := a → ∃[ b ] (ys ∋ˡ k := b)
lookup-transfer {ys = y ∷ ys} eq here = y , here
lookup-transfer {ys = []} () here
lookup-transfer {ys = []} () (there d)
lookup-transfer {ys = y ∷ ys} eq (there d)
  with lookup-transfer (cong pred eq) d
lookup-transfer {ys = y ∷ ys} eq (there d) | b , d′ = b , there d′

-- the interior environment μ is parallel to the interior names; the
-- moved name X, which `toExt` sends to X′, keeps its mode at X′
exit-tag-mode : ∀ {Θ : Boundary} {μ : ModeEnv} {X m}
  → Ξ ∣ η ⊢χ Θ ⇒ ηᵢ
  → Unique ηᵢ
  → length μ ≡ length ηᵢ
  → μ ∋ˡ X := m
  → ηᵢ ∋ˡ X := α
  → toExt Θ X ≡ just X′
  → exitEnv Θ μ (length η) ∋ˡ X′ := m
exit-tag-mode {α = α} {X′ = X′} {Θ = Θ} {μ = μ} {X = X} {m = m}
    cs uq len dμ dᵢ e =
  subst (λ k → exitEnv Θ μ _ ∋ˡ X′ := k) found
        (subst (λ z → exitEnv Θ μ _ ∋ˡ X′ := modeAtExt Θ μ 0 z)
               (+-identityʳ X′) (exitEnv-lookup Θ μ (lookup-lt dΔ)))
  where
  dΔ = toExt-sound cs dᵢ e

  u : ∀ {Y m′} → μ ∋ˡ Y := m′ → toExt Θ (Y + 0) ≡ just X′ → Y ≡ X
  u {Y} dY eY with lookup-transfer len dY
  u {Y} dY eY | γ , dYᵢ
    with ∋ˡ-det dΔ (toExt-sound cs dYᵢ
                      (trans (cong (toExt Θ) (sym (+-identityʳ Y))) eY))
  u {Y} dY eY | γ , dYᵢ | refl = unique-lookup uq dYᵢ dᵢ

  found : modeAtExt Θ μ 0 X′ ≡ m
  found = modeAt-find Θ 0 X′ dμ
            (trans (cong (toExt Θ) (+-identityʳ X)) e) u

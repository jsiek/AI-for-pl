module strong.proof.StoreWeaken where

-- Strong System F v8 — carrying a judgment across a STORE extension.
--
-- The store is append-only (`strong.Ctx`): `Alloc` extends it on the
-- RIGHT with `Σ ∷ʳ R`, and a level is a position from the START, so the
-- snoc disturbs no existing level.  Every judgment that reads the store
-- reads it only through `_∋ˡ_:=_`, so each one transports along the
-- snoc by a plain structural recursion: `∋ˡ-snoc` at the leaves, the
-- constructors everywhere else.
--
-- The one piece of arithmetic is `storeOk-snoc`, which `Alloc` needs to
-- keep the new store well-formed.  `StoreOk Σ` grades each entry by the
-- STRICTLY EARLIER prefix `take ℓ Σ`, so a lookup in `Σ ∷ʳ R` splits:
-- an old level ℓ has `take ℓ (Σ ∷ʳ R) ≡ take ℓ Σ` (it never reaches the
-- new tail), and the new level `length Σ` has `take ℓ (Σ ∷ʳ R) ≡ Σ` —
-- exactly the prefix the freshly allocated R was checked against.  Both
-- `take` facts come out of ONE induction, `∋ˡ-snoc-inv`, which returns
-- the prefix equation alongside the case split.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; take)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; subst)

open import strong.Ctx
open import strong.Conversion using
  (Conv; ConvElt; _∣_⊢_∶_⇝_⊣_; _∣_⊢̂_∶_⇝_⊣_;
   conv-id; conv-cons; conv-seal; conv-unseal; conv-hide; conv-show;
   conv-fun; conv-all)
open import strong.Terms using
  (_∣_∣_⊢_⦂_; ⊢`; ⊢$; ⊢#; ⊢⊕; ⊢ƛ; ⊢·; ⊢Λ; ⊢•[]; ⊢ν; ⊢⟨⟩)

------------------------------------------------------------------------
-- Levels
------------------------------------------------------------------------
-- A level points from the front, so appending on the right leaves it
-- where it was.

∋ˡ-snoc : ∀ {Σ R ℓ S} → Σ ∋ˡ ℓ := S → (Σ ∷ʳ R) ∋ˡ ℓ := S
∋ˡ-snoc l-here = l-here
∋ˡ-snoc (l-there p) = l-there (∋ˡ-snoc p)

------------------------------------------------------------------------
-- Addresses, represented addresses, and well-formed representations
------------------------------------------------------------------------
-- Only the `lvl` rules touch the store; every other rule is carried by
-- its own constructor.

∋a-snoc : ∀ {Σ R Δ α} → Σ ∣ Δ ∋a α → (Σ ∷ʳ R) ∣ Δ ∋a α
∋a-snoc (a-lvl p) = a-lvl (∋ˡ-snoc p)
∋a-snoc a-here-addr = a-here-addr
∋a-snoc a-here-nu = a-here-nu
∋a-snoc (a-skip-addr p) = a-skip-addr (∋a-snoc p)
∋a-snoc (a-skip-nu p) = a-skip-nu (∋a-snoc p)

∋r-snoc : ∀ {Σ R Δ α S} → Σ ∣ Δ ∋r α := S → (Σ ∷ʳ R) ∣ Δ ∋r α := S
∋r-snoc (r-lvl p) = r-lvl (∋ˡ-snoc p)
∋r-snoc r-here = r-here
∋r-snoc (r-skip-addr p) = r-skip-addr (∋r-snoc p)
∋r-snoc (r-skip-nu p) = r-skip-nu (∋r-snoc p)

wfᴿ-snoc : ∀ {Σ R Δ n S} → Σ ∣ Δ ⊢ᴿ[ n ] S → (Σ ∷ʳ R) ∣ Δ ⊢ᴿ[ n ] S
wfᴿ-snoc (wfᴿ-var p) = wfᴿ-var (∋a-snoc p)
wfᴿ-snoc (wfᴿ-bv lt) = wfᴿ-bv lt
wfᴿ-snoc wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-snoc wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-snoc (wfᴿ-⇒ p q) = wfᴿ-⇒ (wfᴿ-snoc p) (wfᴿ-snoc q)
wfᴿ-snoc (wfᴿ-∀ p) = wfᴿ-∀ (wfᴿ-snoc p)

------------------------------------------------------------------------
-- Reading back, and quoting
------------------------------------------------------------------------
-- Neither judgment consults the store at all — names live in the
-- context — so both transports are pure re-indexing.

read-snoc : ∀ {Σ R Δ S A} → Σ ∣ Δ ⊢ S ⇓ A → (Σ ∷ʳ R) ∣ Δ ⊢ S ⇓ A
read-snoc (read-var n) = read-var n
read-snoc (read-bv n) = read-bv n
read-snoc read-ℕ = read-ℕ
read-snoc read-𝔹 = read-𝔹
read-snoc (read-⇒ p q) = read-⇒ (read-snoc p) (read-snoc q)
read-snoc (read-∀ p) = read-∀ (read-snoc p)

quote-snoc : ∀ {Σ R Δ A S} → Σ ∣ Δ ⊢⌊ A ⌋ S → (Σ ∷ʳ R) ∣ Δ ⊢⌊ A ⌋ S
quote-snoc (quote-var n) = quote-var n
quote-snoc (quote-bv n) = quote-bv n
quote-snoc quote-ℕ = quote-ℕ
quote-snoc quote-𝔹 = quote-𝔹
quote-snoc (quote-⇒ p q) = quote-⇒ (quote-snoc p) (quote-snoc q)
quote-snoc (quote-∀ p) = quote-∀ (quote-snoc p)

------------------------------------------------------------------------
-- Conversion typing
------------------------------------------------------------------------
-- The store appears only under `seal`/`unseal`, which look up a
-- represented address and read it back; `hide`/`show` carry a source
-- well-formedness and a pop, neither of which mentions the store.

mutual
  convElt-snoc : ∀ {Σ R Δᵢ Δ ĉ A B} → Σ ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δ
    → (Σ ∷ʳ R) ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δ
  convElt-snoc (conv-seal r rd pop) =
    conv-seal (∋r-snoc r) (read-snoc rd) pop
  convElt-snoc (conv-unseal r rd pop na) =
    conv-unseal (∋r-snoc r) (read-snoc rd) pop na
  convElt-snoc (conv-hide sc wf pop na) = conv-hide (∋a-snoc sc) wf pop na
  convElt-snoc (conv-show sc wf pop na) = conv-show (∋a-snoc sc) wf pop na
  convElt-snoc (conv-fun s t) = conv-fun (conv-snoc s) (conv-snoc t)
  convElt-snoc (conv-all s) = conv-all (conv-snoc s)

  conv-snoc : ∀ {Σ R Δᵢ Δ c A B} → Σ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
    → (Σ ∷ʳ R) ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
  conv-snoc (conv-id wf) = conv-id wf
  conv-snoc (conv-cons e c) = conv-cons (convElt-snoc e) (conv-snoc c)

------------------------------------------------------------------------
-- Term typing
------------------------------------------------------------------------

⊢-snoc : ∀ {Σ R Δ Γ M A} → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → (Σ ∷ʳ R) ∣ Δ ∣ Γ ⊢ M ⦂ A
⊢-snoc (⊢` x) = ⊢` x
⊢-snoc ⊢$ = ⊢$
⊢-snoc ⊢# = ⊢#
⊢-snoc (⊢⊕ p q) = ⊢⊕ (⊢-snoc p) (⊢-snoc q)
⊢-snoc (⊢ƛ wf p) = ⊢ƛ wf (⊢-snoc p)
⊢-snoc (⊢· p q) = ⊢· (⊢-snoc p) (⊢-snoc q)
⊢-snoc (⊢Λ v p) = ⊢Λ v (⊢-snoc p)
⊢-snoc (⊢•[] p wf) = ⊢•[] (⊢-snoc p) wf
⊢-snoc (⊢ν wf p) = ⊢ν (wfᴿ-snoc wf) (⊢-snoc p)
⊢-snoc (⊢⟨⟩ nf p c) = ⊢⟨⟩ nf (⊢-snoc p) (conv-snoc c)

------------------------------------------------------------------------
-- The new store is still well-formed
------------------------------------------------------------------------
-- `StoreOk Σ = ∀ {ℓ S} → Σ ∋ˡ ℓ := S → take ℓ Σ ∣ ([] ∥ []) ⊢ᴿ S`, so
-- the transport above is NOT enough: the prefix the entry is graded
-- against moves with the store.  One induction settles both halves.
--
--   * an OLD level never reaches the new tail, so its prefix in
--     `Σ ∷ʳ R` is the prefix it had in `Σ`;
--   * the NEW level is `length Σ`, and its prefix is all of `Σ` — the
--     very store the allocated R was checked against.
--
-- Rather than stating the two `take` equations separately, the
-- inversion returns the equation that belongs to its case: `inj₁` is
-- accompanied by the OLD lookup (whose own prefix equation is
-- `take-∋ˡ-snoc` below), `inj₂` by `take ℓ (Σ ∷ʳ R) ≡ Σ` directly.

take-∋ˡ-snoc : ∀ {Σ R ℓ S} → Σ ∋ˡ ℓ := S → take ℓ (Σ ∷ʳ R) ≡ take ℓ Σ
take-∋ˡ-snoc l-here = refl
take-∋ˡ-snoc {S = S} (l-there {S = T} p) =
  cong (T ∷_) (take-∋ˡ-snoc p)

∋ˡ-snoc-inv : ∀ Σ {R ℓ S} → (Σ ∷ʳ R) ∋ˡ ℓ := S
  → (Σ ∋ˡ ℓ := S) ⊎ (take ℓ (Σ ∷ʳ R) ≡ Σ × S ≡ R)
∋ˡ-snoc-inv [] l-here = inj₂ (refl , refl)
∋ˡ-snoc-inv [] (l-there ())
∋ˡ-snoc-inv (T ∷ Σ) l-here = inj₁ l-here
∋ˡ-snoc-inv (T ∷ Σ) (l-there p) with ∋ˡ-snoc-inv Σ p
∋ˡ-snoc-inv (T ∷ Σ) (l-there p) | inj₁ q = inj₁ (l-there q)
∋ˡ-snoc-inv (T ∷ Σ) (l-there p) | inj₂ (e , refl) =
  inj₂ (cong (T ∷_) e , refl)

storeOk-snoc : ∀ {Σ R} → StoreOk Σ → Σ ∣ ([] ∥ []) ⊢ᴿ R
  → StoreOk (Σ ∷ʳ R)
storeOk-snoc {Σ} {R} ok wf {ℓ} {S} lk with ∋ˡ-snoc-inv Σ lk
storeOk-snoc {Σ} {R} ok wf {ℓ} {S} lk | inj₁ p =
  subst (λ Σ′ → Σ′ ∣ ([] ∥ []) ⊢ᴿ S) (sym (take-∋ˡ-snoc p)) (ok p)
storeOk-snoc {Σ} {R} ok wf {ℓ} {S} lk | inj₂ (e , refl) =
  subst (λ Σ′ → Σ′ ∣ ([] ∥ []) ⊢ᴿ S) (sym e) wf

module strong-rep-nu.proof.Compose where

-- File Charter:
--   * COMPOSITION IS WELL TYPED: `⊢⨟` — if `c₁ : A ⇝ B` and
--     `c₂ : B ⇝ C` at one conversion context with unique names, then
--     `Δ ⊢ c₁ ⨟ c₂ : A ⇝ C` (strong-rep-nu.Conversion §4b).  Typing is
--     also what makes the result TIGHT: the chain premises `¬ IsId`
--     and `NoCancel` are rebuilt, never assumed.
--   * §1 an identity has equal endpoints (`isIdᶜ-types`); §2 the
--     lookup functions are complete, so `repOf` IS the lookup square
--     (`repOf-sound`); §3 the smart constructors (`⊢⨾sealˢ`,
--     `⊢cancelᵀ`, `⊢unseal⨾ˢ`); §4 `⊢⨟`, one lemma per sort.
--   * `Unique (names Δ)` is all it needs: `∋:=-det` at the cancelled
--     seal/unseal pair and at `repOf`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Lookup
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary using (Boundary)
open import strong-rep-nu.proof.Preserve using (same-wf)

private
  variable
    Δ : Ctxᵗ
    Θ : Boundary
    p : Pol
    A B C R : Ty
    X Y : ℕ
    α β : RVar
    g g₂ : Mid
    t t₂ : Tail
    c c₁ c₂ : Conv

------------------------------------------------------------------------
-- §1  An identity has equal endpoints
------------------------------------------------------------------------

mutual
  isIdᵐ-types : IsIdᵐ g → Δ ∣ Θ ⊢ᵐ[ p ] g ∶ A ⇝ B → A ≡ B
  isIdᵐ-types i (conv-id b) = refl
  isIdᵐ-types i (conv-idv d) = refl
  isIdᵐ-types (i , j) (conv-fun p q) =
    cong₂ _⇒_ (sym (isIdᶜ-types i p)) (isIdᶜ-types j q)
  isIdᵐ-types i (conv-all p) = cong `∀ (isIdᶜ-types i p)

  isIdᵀ-types : IsIdᵀ t → Δ ∣ Θ ⊢ᵀ[ p ] t ∶ A ⇝ B → A ≡ B
  isIdᵀ-types i (conv-mid p) = isIdᵐ-types i p
  isIdᵀ-types () (conv-seal d ok)
  isIdᵀ-types () (conv-seal-seq p d ok n)

  isIdᶜ-types : IsIdᶜ c → Δ ∣ Θ ⊢[ p ] c ∶ A ⇝ B → A ≡ B
  isIdᶜ-types i (conv-tail p) = isIdᵀ-types i p
  isIdᶜ-types () (conv-unseal d ok)
  isIdᶜ-types () (conv-unseal-seq d ok p n m)

-- A middle whose source or target is a variable is `id` at it.
mid-var-tgt : Δ ∣ Θ ⊢ᵐ[ p ] g ∶ A ⇝ ` β → A ≡ ` β
mid-var-tgt (conv-id ())
mid-var-tgt (conv-idv d) = refl

mid-var-src : Δ ∣ Θ ⊢ᵐ[ p ] g ∶ ` α ⇝ B → B ≡ ` α
mid-var-src (conv-id ())
mid-var-src (conv-idv d) = refl

------------------------------------------------------------------------
-- §2  The lookup functions are complete
------------------------------------------------------------------------

lookupˡ?-just : ∀ {S : Set} (xs : List S) (i : ℕ) {x : S}
  → xs ∋ˡ i := x → ∃[ d ] (lookupˡ? xs i ≡ just (x , d))
lookupˡ?-just (x ∷ xs) zero here = here , refl
lookupˡ?-just (y ∷ xs) (suc i) (there d)
  with lookupˡ? xs i | lookupˡ?-just xs i d
lookupˡ?-just (y ∷ xs) (suc i) (there d) | just (z , d′) | d″ , refl =
  there d′ , refl
lookupˡ?-just (y ∷ xs) (suc i) (there d) | nothing | d″ , ()

lookupʳ?-just : ∀ (Ξ : RepCtx) (α : RVar) {b : RepBinding}
  → Ξ ∋ʳ α := b → ∃[ d ] (lookupʳ? Ξ α ≡ just (b , d))
lookupʳ?-just (b ∷ Ξ) zero r-here = r-here , refl
lookupʳ?-just (bindR R ∷ Ξ) (suc α) (r-there d)
  with lookupʳ? Ξ α | lookupʳ?-just Ξ α d
lookupʳ?-just (bindR R ∷ Ξ) (suc α) (r-there d)
  | just (b , d′) | d″ , refl = r-there d′ , refl
lookupʳ?-just (bindR R ∷ Ξ) (suc α) (r-there d) | nothing | d″ , ()
lookupʳ?-just (abstR ∷ Ξ) (suc α) (r-there-abst d)
  with lookupʳ? Ξ α | lookupʳ?-just Ξ α d
lookupʳ?-just (abstR ∷ Ξ) (suc α) (r-there-abst d)
  | just (b , d′) | d″ , refl = r-there-abst d′ , refl
lookupʳ?-just (abstR ∷ Ξ) (suc α) (r-there-abst d) | nothing | d″ , ()

find?-just : ∀ (η : TyCtx) (α : RVar) {X : ℕ}
  → η ∋ˡ X := α → ∃[ p ] (find? η α ≡ just p)
find?-just (β ∷ η) α d with α ≟ β
find?-just (β ∷ η) α d | yes refl = _ , refl
find?-just (β ∷ η) α here | no ne = ⊥-elim (ne refl)
find?-just (β ∷ η) α (there d) | no ne
  with find? η α | find?-just η α d
find?-just (β ∷ η) α (there d) | no ne | just p | q , refl = _ , refl
find?-just (β ∷ η) α (there d) | no ne | nothing | q , ()

unread?-just : ∀ (η : TyCtx) {A R : Ty}
  → η ⊢ A ~ R → ∃[ p ] (unread? η R ≡ just p)
unread?-just η (same-var {α = α} d) with find? η α | find?-just η α d
unread?-just η (same-var {α = α} d) | just (X , e) | q , refl = _ , refl
unread?-just η (same-var {α = α} d) | nothing | q , ()
unread?-just η same-ℕ = _ , refl
unread?-just η same-𝔹 = _ , refl
unread?-just η (same-⇒ {R = R} {S = S} p q)
  with unread? η R | unread?-just η p
unread?-just η (same-⇒ {R = R} {S = S} p q) | nothing | r , ()
unread?-just η (same-⇒ {R = R} {S = S} p q) | just (A , p′) | r , refl
  with unread? η S | unread?-just η q
unread?-just η (same-⇒ {R = R} {S = S} p q) | just (A , p′) | r , refl
  | just (B , q′) | r′ , refl = _ , refl
unread?-just η (same-⇒ {R = R} {S = S} p q) | just (A , p′) | r , refl
  | nothing | r′ , ()
unread?-just η (same-∀ {R = R} p)
  with unread? (zero ∷ shiftReps η) R | unread?-just (zero ∷ shiftReps η) p
unread?-just η (same-∀ {R = R} p) | just (A , p′) | r , refl = _ , refl
unread?-just η (same-∀ {R = R} p) | nothing | r , ()

∋:=?-just : ∀ (Γ : Ctxᵗ) (X : ℕ) {A : Ty}
  → Γ ∋ X := A → ∃[ p ] (∋:=? Γ X ≡ just p)
∋:=?-just Γ X (α , R , nm , rp , sm)
  with lookupˡ? (names Γ) X | lookupˡ?-just (names Γ) X nm
∋:=?-just Γ X (α , R , nm , rp , sm) | nothing | d , ()
∋:=?-just Γ X (α , R , nm , rp , sm) | just (β , nm′) | d , refl
  with lookupʳ? (reps Γ) α | lookupʳ?-just (reps Γ) α rp
∋:=?-just Γ X (α , R , nm , rp , sm) | just (β , nm′) | d , refl
  | nothing | e , ()
∋:=?-just Γ X (α , R , nm , rp , sm) | just (β , nm′) | d , refl
  | just (b , rp′) | e , refl
  with unread? (names Γ) R | unread?-just (names Γ) sm
∋:=?-just Γ X (α , R , nm , rp , sm) | just (β , nm′) | d , refl
  | just (b , rp′) | e , refl | just (A′ , sm′) | f , refl = _ , refl
∋:=?-just Γ X (α , R , nm , rp , sm) | just (β , nm′) | d , refl
  | just (b , rp′) | e , refl | nothing | f , ()

-- `repOf` is the lookup square read as a function: at a leaf it is
-- the leaf's type, which reads its representation.
repOf-sound : Unique (names Δ) → Δ ∋ X ⊸ α := R
  → names Δ ⊢ repOf Δ X ~ R
repOf-sound {Δ = Δ} {X = X} uq (nm , rp , A , sm)
  with ∋:=? Δ X | ∋:=?-just Δ X (_ , _ , nm , rp , sm)
repOf-sound {Δ = Δ} {X = X} uq (nm , rp , A , sm)
  | just (A′ , d′) | q , refl
  rewrite ∋:=-det uq d′ (_ , _ , nm , rp , sm) = sm
repOf-sound {Δ = Δ} {X = X} uq (nm , rp , A , sm) | nothing | q , ()

------------------------------------------------------------------------
-- §3  The smart constructors
------------------------------------------------------------------------

⊢⨾sealˢ : Δ ∣ Θ ⊢ᵀ[ p ] t ∶ A ⇝ R → Δ ∋ Y ⊸ β := R → SealOK p Θ β
  → Δ ∣ Θ ⊢ᵀ[ p ] t ⨾sealˢ Y ∶ A ⇝ ` β
⊢⨾sealˢ {t = t} ⊢t d ok with isIdᵀ? t
⊢⨾sealˢ {t = t} ⊢t d ok | yes i =
  subst (λ T → _ ∣ _ ⊢ᵀ[ _ ] seal _ ∶ T ⇝ ` _) (sym (isIdᵀ-types i ⊢t))
        (conv-seal d ok)
⊢⨾sealˢ {t = t} ⊢t d ok | no n = conv-seal-seq ⊢t d ok n

-- When `cancelᵀ X t` is not a tail, `unseal X` did not cancel, and
-- that is exactly `NoCancelᵀ X t`.
cancel-view : ∀ X t → (∃[ t′ ] (cancelᵀ X t ≡ tail t′)) ⊎ NoCancelᵀ X t
cancel-view X (mid g) = inj₂ tt
cancel-view X (seal Y) with X ≟ Y
cancel-view X (seal Y) | yes eq = inj₁ (_ , refl)
cancel-view X (seal Y) | no ne = inj₂ ne
cancel-view X (t ⨾seal Y) with cancelᵀ X t | cancel-view X t
cancel-view X (t ⨾seal Y) | tail t′ | v = inj₁ (_ , refl)
cancel-view X (t ⨾seal Y) | unseal Z | inj₁ (t′ , ())
cancel-view X (t ⨾seal Y) | unseal Z | inj₂ nc = inj₂ nc
cancel-view X (t ⨾seal Y) | unseal Z ⨾ c | inj₁ (t′ , ())
cancel-view X (t ⨾seal Y) | unseal Z ⨾ c | inj₂ nc = inj₂ nc

conv-tail⁻ : Δ ∣ Θ ⊢[ p ] tail t ∶ A ⇝ B → Δ ∣ Θ ⊢ᵀ[ p ] t ∶ A ⇝ B
conv-tail⁻ (conv-tail q) = q

⊢cancelᵀ : Δ ∋ X ⊸ α := R → UnsealOK p Θ α → Δ ∣ Θ ⊢ᵀ[ p ] t ∶ R ⇝ C
  → ¬ IsIdᵀ t → Δ ∣ Θ ⊢[ p ] cancelᵀ X t ∶ ` α ⇝ C
⊢cancelᵀ d ok (conv-mid q) n =
  conv-unseal-seq d ok (conv-tail (conv-mid q)) n tt
⊢cancelᵀ {X = X} d ok (conv-seal {X = Y} dY okY) n with X ≟ Y
⊢cancelᵀ {X = X} (nm , rp , sm) ok (conv-seal {X = Y} (nmY , rpY , smY) okY)
  n | yes refl with ∋ˡ-det nm nmY
... | refl = conv-tail (conv-mid (conv-idv nm))
⊢cancelᵀ {X = X} d ok (conv-seal {X = Y} dY okY) n | no ne =
  conv-unseal-seq d ok (conv-tail (conv-seal dY okY)) (λ ()) ne
⊢cancelᵀ {X = X} d ok (conv-seal-seq {t = t} q dY okY m) n
  with cancelᵀ X t | ⊢cancelᵀ d ok q m | cancel-view X t
⊢cancelᵀ {X = X} d ok (conv-seal-seq {t = t} q dY okY m) n
  | tail t′ | ⊢r | v = conv-tail (⊢⨾sealˢ (conv-tail⁻ ⊢r) dY okY)
⊢cancelᵀ {X = X} d ok (conv-seal-seq {t = t} q dY okY m) n
  | unseal Z | ⊢r | inj₁ (t′ , ())
⊢cancelᵀ {X = X} d ok (conv-seal-seq {t = t} q dY okY m) n
  | unseal Z | ⊢r | inj₂ nc =
  conv-unseal-seq d ok (conv-tail (conv-seal-seq q dY okY m)) (λ ()) nc
⊢cancelᵀ {X = X} d ok (conv-seal-seq {t = t} q dY okY m) n
  | unseal Z ⨾ c | ⊢r | inj₁ (t′ , ())
⊢cancelᵀ {X = X} d ok (conv-seal-seq {t = t} q dY okY m) n
  | unseal Z ⨾ c | ⊢r | inj₂ nc =
  conv-unseal-seq d ok (conv-tail (conv-seal-seq q dY okY m)) (λ ()) nc

⊢unseal⨾ˢ : Δ ∋ X ⊸ α := R → UnsealOK p Θ α → Δ ∣ Θ ⊢[ p ] c ∶ R ⇝ C
  → Δ ∣ Θ ⊢[ p ] unseal X ⨾ˢ c ∶ ` α ⇝ C
⊢unseal⨾ˢ d ok (conv-tail {t = t} q) with isIdᵀ? t
⊢unseal⨾ˢ d ok (conv-tail {t = t} q) | yes i =
  subst (λ T → _ ∣ _ ⊢[ _ ] unseal _ ∶ ` _ ⇝ T) (isIdᵀ-types i q)
        (conv-unseal d ok)
⊢unseal⨾ˢ d ok (conv-tail {t = t} q) | no n = ⊢cancelᵀ d ok q n
⊢unseal⨾ˢ d ok (conv-unseal dY okY) =
  conv-unseal-seq d ok (conv-unseal dY okY) (λ ()) tt
⊢unseal⨾ˢ d ok (conv-unseal-seq dY okY q n m) =
  conv-unseal-seq d ok (conv-unseal-seq dY okY q n m) (λ ()) tt

------------------------------------------------------------------------
-- §4  Composition is well typed
------------------------------------------------------------------------

-- the representation a seal and an unseal of the same variable agree on
leaf-rep : Δ ∋ X ⊸ α := A → Δ ∋ Y ⊸ α := B → A ≡ B
leaf-rep (_ , rd , _) (_ , rd′ , _) with ∋ʳ-det rd rd′
... | refl = refl

-- Jeremy's statement, now at one scope and one polarity.  Each clause
-- of `Δ ⊢ c₁ ⨟ c₂` is justified by the types; the pairs typing rules
-- out never arise.  Permissions need no argument: the composite's
-- seals and unseals are among its parts'.
mutual
  ⊢⨟ : Unique (names Δ) → Δ ∣ Θ ⊢[ p ] c₁ ∶ A ⇝ B
    → Δ ∣ Θ ⊢[ p ] c₂ ∶ B ⇝ C
    → Δ ∣ Θ ⊢[ p ] (Δ ⊢ c₁ ⨟ c₂) ∶ A ⇝ C
  ⊢⨟ uq (conv-tail q) ⊢c₂ = ⊢⨟ᵀ uq q ⊢c₂
  ⊢⨟ uq (conv-unseal d ok) ⊢c₂ = ⊢unseal⨾ˢ d ok ⊢c₂
  ⊢⨟ uq (conv-unseal-seq d ok q n m) ⊢c₂ =
    ⊢unseal⨾ˢ d ok (⊢⨟ uq q ⊢c₂)

  ⊢⨟ᵀ : Unique (names Δ) → Δ ∣ Θ ⊢ᵀ[ p ] t ∶ A ⇝ B
    → Δ ∣ Θ ⊢[ p ] c₂ ∶ B ⇝ C
    → Δ ∣ Θ ⊢[ p ] (Δ ⊢ t ⨟ᵀ c₂) ∶ A ⇝ C
  ⊢⨟ᵀ uq ⊢t (conv-tail q) = conv-tail (⊢⨟ᵀᵀ uq ⊢t q)
  -- the cancelled pair: CancelR
  ⊢⨟ᵀ uq (conv-seal dX okX) (conv-unseal dY okY)
    rewrite leaf-rep dY dX = mkId-⊢ (repOf-sound uq dX)
  ⊢⨟ᵀ uq (conv-seal dX okX) (conv-unseal-seq dY okY q n m)
    rewrite leaf-rep dY dX = q
  ⊢⨟ᵀ uq (conv-seal-seq p dX okX n) (conv-unseal dY okY)
    rewrite leaf-rep dY dX = conv-tail p
  ⊢⨟ᵀ uq (conv-seal-seq p dX okX n) (conv-unseal-seq dY okY q n′ m)
    rewrite leaf-rep dY dX = ⊢⨟ᵀ uq p q
  -- a middle whose target is a variable is the identity there
  ⊢⨟ᵀ uq (conv-mid p) (conv-unseal dY okY) with mid-var-tgt p
  ⊢⨟ᵀ uq (conv-mid p) (conv-unseal dY okY) | refl = conv-unseal dY okY
  ⊢⨟ᵀ uq (conv-mid p) (conv-unseal-seq dY okY q n m) with mid-var-tgt p
  ⊢⨟ᵀ uq (conv-mid p) (conv-unseal-seq dY okY q n m) | refl =
    conv-unseal-seq dY okY q n m

  ⊢⨟ᵀᵀ : Unique (names Δ) → Δ ∣ Θ ⊢ᵀ[ p ] t ∶ A ⇝ B
    → Δ ∣ Θ ⊢ᵀ[ p ] t₂ ∶ B ⇝ C
    → Δ ∣ Θ ⊢ᵀ[ p ] (Δ ⊢ t ⨟ᵀᵀ t₂) ∶ A ⇝ C
  ⊢⨟ᵀᵀ uq ⊢t (conv-seal dY okY) = ⊢⨾sealˢ ⊢t dY okY
  ⊢⨟ᵀᵀ uq ⊢t (conv-seal-seq q dY okY n) =
    ⊢⨾sealˢ (⊢⨟ᵀᵀ uq ⊢t q) dY okY
  ⊢⨟ᵀᵀ uq (conv-mid p) (conv-mid q) = conv-mid (⊢⨟ᵐ uq p q)
  -- a middle whose source is a variable is the identity there
  ⊢⨟ᵀᵀ uq (conv-seal dX okX) (conv-mid q) with mid-var-src q
  ⊢⨟ᵀᵀ uq (conv-seal dX okX) (conv-mid q) | refl = conv-seal dX okX
  ⊢⨟ᵀᵀ uq (conv-seal-seq p dX okX n) (conv-mid q) with mid-var-src q
  ⊢⨟ᵀᵀ uq (conv-seal-seq p dX okX n) (conv-mid q) | refl =
    conv-seal-seq p dX okX n

  ⊢⨟ᵐ : Unique (names Δ) → Δ ∣ Θ ⊢ᵐ[ p ] g ∶ A ⇝ B
    → Δ ∣ Θ ⊢ᵐ[ p ] g₂ ∶ B ⇝ C
    → Δ ∣ Θ ⊢ᵐ[ p ] (Δ ⊢ g ⨟ᵐ g₂) ∶ A ⇝ C
  ⊢⨟ᵐ uq (conv-id b) q = q
  ⊢⨟ᵐ uq (conv-idv d) q = q
  ⊢⨟ᵐ uq (conv-fun p₁ p₂) (conv-id ())
  -- the domain flips
  ⊢⨟ᵐ uq (conv-fun p₁ p₂) (conv-fun q₁ q₂) =
    conv-fun (⊢⨟ uq q₁ p₁) (⊢⨟ uq p₂ q₂)
  ⊢⨟ᵐ uq (conv-all p) (conv-id ())
  ⊢⨟ᵐ {Δ = Δ} uq (conv-all p) (conv-all q) =
    conv-all (⊢⨟ (unique-underΛ {Γ = Δ} uq) p q)

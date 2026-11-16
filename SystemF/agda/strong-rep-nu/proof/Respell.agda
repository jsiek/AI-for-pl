module strong-rep-nu.proof.Respell where

-- File Charter:
--   * THE PER-NAME RESPELLING RESPECTS THE NAME MAPS.  `respell Θₛ Π
--     Θₜ` (strong-rep-nu.Conversion §2b) is computed from the scopes
--     alone; here it is proved to send each name of the source
--     conversion context to the target's name for the SAME
--     representation variable (`respell-respects`), whenever the target
--     keeps the source's representation variables.  Instances:
--     `respects-Wrap`, `respects-Merge₁`, `respects-Merge₂`.
--   * WHAT A TOKEN DENOTES (`_⊨_:=_`): a position names its variable,
--     and `gone α` says α has NO name there.  §1 positions under one
--     insertion or deletion; §2 liveness read off the scope
--     (`Mentions`), which needs the INTERIOR reading too — a
--     well-formed scope binds a name the context has only after
--     unbinding it; §3 each of decode, the path and encode keeps the
--     denotation; §4 the theorem and its instances.
-- Commentary: Commentary.md § proof/Respell.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion

private
  variable
    Ξ : RepCtx
    Δ Δ′ Δᵢ Δᶜ : TyCtx
    χ : List Change
    δ : Change
    t : Tok
    X Y p : ℕ
    α β γ : RVar

------------------------------------------------------------------------
-- §0  What a token denotes
------------------------------------------------------------------------

infix 4 _⊨_:=_
data _⊨_:=_ (Δ : TyCtx) : Tok → RVar → Set where
  den-pos  : Δ ∋ˡ p := γ → Δ ⊨ pos p := γ
  den-gone : ¬ (Δ ∋ᵅ γ) → Δ ⊨ gone γ := γ

-- a token whose last step removed α's name: either α's token, or a
-- position (freshness of α is supplied separately)
data Peeled (Δ : TyCtx) (α : RVar) : Tok → RVar → Set where
  peel-hit  : Peeled Δ α (gone α) α
  peel-miss : Δ ∋ˡ p := γ → Peeled Δ α (pos p) γ

peeled-den : ¬ (Δ ∋ᵅ α) → Peeled Δ α t γ → Δ ⊨ t := γ
peeled-den nα peel-hit = den-gone nα
peeled-den nα (peel-miss d) = den-pos d

------------------------------------------------------------------------
-- §1  Positions under one insertion or deletion
------------------------------------------------------------------------

ins-at : α ⊢+ Δ at Y ⇒ Δ′ → Δ′ ∋ˡ Y := α
ins-at ins-here = here
ins-at (ins-there i) = there (ins-at i)

punch-ins : α ⊢+ Δ at Y ⇒ Δ′ → Δ ∋ˡ p := γ → Δ′ ∋ˡ punchIn Y p := γ
punch-ins ins-here d = there d
punch-ins (ins-there i) here = here
punch-ins (ins-there i) (there d) = there (punch-ins i d)

peeled-up : Peeled Δ α t γ → Peeled (β ∷ Δ) α (upTok t) γ
peeled-up peel-hit = peel-hit
peeled-up (peel-miss d) = peel-miss (there d)

peel-ins : α ⊢+ Δ at Y ⇒ Δ′ → Δ′ ∋ˡ X := γ → Peeled Δ α (peel Y α X) γ
peel-ins ins-here here = peel-hit
peel-ins ins-here (there d) = peel-miss d
peel-ins (ins-there i) here = peel-miss here
peel-ins (ins-there i) (there d) = peeled-up (peel-ins i d)

peel-del : α ⊢- Δ at Y ⇒ Δ′ → Δ ∋ˡ p := γ → Peeled Δ′ α (peel Y α p) γ
peel-del del-here here = peel-hit
peel-del del-here (there d) = peel-miss d
peel-del (del-there dl) here = peel-miss here
peel-del (del-there dl) (there d) = peeled-up (peel-del dl d)

------------------------------------------------------------------------
-- §2  Liveness read off the scope
------------------------------------------------------------------------

-- a name the scope mentions is live in the conversion reading
mentions-live : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Mentions β χ → Δᶜ ∋ᵅ β
mentions-live (changes∷ cs (step-unbind v dl fr)) (conv-unbind v′ csᶜ)
              m-unbind =
  int⇒conv-live cs csᶜ (del-live dl)
mentions-live (changes∷ cs (step-unbind v dl fr)) (conv-unbind v′ csᶜ)
              (m-there m) =
  mentions-live cs csᶜ m
mentions-live (changes∷ cs (step-bind v fr i)) (conv-bind v′ csᶜ fr′ i′)
              m-bind =
  ins-live i′
mentions-live (changes∷ cs (step-bind v fr i)) (conv-bind v′ csᶜ fr′ i′)
              (m-there m) =
  ins-mono i′ (mentions-live cs csᶜ m)
mentions-live (changes∷ cs (step-bind v fr i)) (conv-bind-live v′ csᶜ d)
              m-bind =
  _ , d
mentions-live (changes∷ cs (step-bind v fr i)) (conv-bind-live v′ csᶜ d)
              (m-there m) =
  mentions-live cs csᶜ m

-- a name the scope never mentions, live in the conversion reading, is
-- live in the interior reading too (it came from the exterior and was
-- never unbound)
unmentioned-keep : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → ¬ Mentions β χ → Δᶜ ∋ᵅ β → Δᵢ ∋ᵅ β
unmentioned-keep changes[] conv[] nm lv = lv
unmentioned-keep (changes∷ cs (step-unbind v dl fr)) (conv-unbind v′ csᶜ)
                 nm lv =
  del-mono dl (λ where refl → nm m-unbind)
    (unmentioned-keep cs csᶜ (λ m → nm (m-there m)) lv)
unmentioned-keep (changes∷ cs (step-bind v fr i)) (conv-bind v′ csᶜ fr′ i′)
                 nm lv with ins-inv i′ lv
unmentioned-keep (changes∷ cs (step-bind v fr i)) (conv-bind v′ csᶜ fr′ i′)
                 nm lv | inj₁ refl = ⊥-elim (nm m-bind)
unmentioned-keep (changes∷ cs (step-bind v fr i)) (conv-bind v′ csᶜ fr′ i′)
                 nm lv | inj₂ lv′ =
  ins-mono i (unmentioned-keep cs csᶜ (λ m → nm (m-there m)) lv′)
unmentioned-keep (changes∷ cs (step-bind v fr i)) (conv-bind-live v′ csᶜ d)
                 nm lv =
  ins-mono i (unmentioned-keep cs csᶜ (λ m → nm (m-there m)) lv)

------------------------------------------------------------------------
-- §3  Decode, the path, and encode keep the denotation
------------------------------------------------------------------------

step-den : Ξ ∣ Δ ⊢δ δ ⇒ Δ′ → Δ ⊨ t := γ → Δ′ ⊨ stepTok δ t := γ
step-den (step-unbind v dl fr) (den-pos d) =
  peeled-den (λ (_ , d′) → fresh-not-lookup fr d′) (peel-del dl d)
step-den (step-unbind v dl fr) (den-gone n) =
  den-gone (λ lv → n (del-inv dl lv))
step-den (step-bind v fr i) (den-pos d) = den-pos (punch-ins i d)
step-den {δ = bind Y β} {γ = γ} (step-bind v fr i) (den-gone n)
  with γ ≟ β
step-den {δ = bind Y β} {γ = γ} (step-bind v fr i) (den-gone n)
  | yes refl = den-pos (ins-at i)
step-den {δ = bind Y β} {γ = γ} (step-bind v fr i) (den-gone n)
  | no ne = den-gone (λ lv → [ ne , n ]′ (ins-inv i lv))

-- the path: forward through an interior reading
encodeI-den : Ξ ∣ Δ ⊢χ χ ⇒ Δ′ → Δ ⊨ t := γ → Δ′ ⊨ encodeI χ t := γ
encodeI-den changes[] den = den
encodeI-den (changes∷ cs st) den = step-den st (encodeI-den cs den)

-- forward through a conversion reading
encodeU-den : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Δ ⊨ t := γ → Δᶜ ⊨ encodeU χ t := γ
encodeU-den changes[] conv[] den = den
encodeU-den (changes∷ cs st) (conv-unbind v csᶜ) den =
  encodeU-den cs csᶜ den
encodeU-den {χ = bind Y β ∷ χ} (changes∷ cs st) (conv-bind v csᶜ fr i) den
  with mentions? β χ
encodeU-den {χ = bind Y β ∷ χ} (changes∷ cs st) (conv-bind v csᶜ fr i) den
  | yes m = ⊥-elim (fresh-not-lookup fr (proj₂ (mentions-live cs csᶜ m)))
encodeU-den {χ = bind Y β ∷ χ} (changes∷ cs st) (conv-bind v csᶜ fr i) den
  | no nm = step-den (step-bind v fr i) (encodeU-den cs csᶜ den)
encodeU-den {χ = bind Y β ∷ χ} (changes∷ cs (step-bind v fr i))
            (conv-bind-live v′ csᶜ d) den
  with mentions? β χ
encodeU-den {χ = bind Y β ∷ χ} (changes∷ cs (step-bind v fr i))
            (conv-bind-live v′ csᶜ d) den
  | yes m = encodeU-den cs csᶜ den
encodeU-den {χ = bind Y β ∷ χ} (changes∷ cs (step-bind v fr i))
            (conv-bind-live v′ csᶜ d) den
  | no nm =
  ⊥-elim (fresh-not-lookup fr
           (proj₂ (unmentioned-keep cs csᶜ nm (_ , d))))

-- a peeled token, continued by a sound decoding of its position
then-den : ∀ {k} → ¬ (Δ ∋ᵅ α) → Peeled Δ′ α t γ
  → (∀ {q} → Δ′ ∋ˡ q := γ → Δ ⊨ k q := γ)
  → Δ ⊨ thenTok t k := γ
then-den nα peel-hit kd = den-gone nα
then-den nα (peel-miss d) kd = kd d

-- backward through a conversion reading
decodeU-den : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Δᶜ ∋ˡ X := γ → Δ ⊨ decodeU χ X := γ
decodeU-den changes[] conv[] d = den-pos d
decodeU-den (changes∷ cs st) (conv-unbind v csᶜ) d = decodeU-den cs csᶜ d
decodeU-den {χ = bind Y β ∷ χ} (changes∷ cs st) (conv-bind v csᶜ fr i) d
  with mentions? β χ
decodeU-den {χ = bind Y β ∷ χ} (changes∷ cs st) (conv-bind v csᶜ fr i) d
  | yes m = ⊥-elim (fresh-not-lookup fr (proj₂ (mentions-live cs csᶜ m)))
decodeU-den {χ = bind Y β ∷ χ} (changes∷ cs st) (conv-bind v csᶜ fr i) d
  | no nm =
  then-den (λ lv → fresh-not-lookup fr (proj₂ (conv-mono csᶜ lv)))
           (peel-ins i d) (λ d′ → decodeU-den cs csᶜ d′)
decodeU-den {χ = bind Y β ∷ χ} (changes∷ cs (step-bind v fr i))
            (conv-bind-live v′ csᶜ e) d
  with mentions? β χ
decodeU-den {χ = bind Y β ∷ χ} (changes∷ cs (step-bind v fr i))
            (conv-bind-live v′ csᶜ e) d
  | yes m = decodeU-den cs csᶜ d
decodeU-den {χ = bind Y β ∷ χ} (changes∷ cs (step-bind v fr i))
            (conv-bind-live v′ csᶜ e) d
  | no nm =
  ⊥-elim (fresh-not-lookup fr
           (proj₂ (unmentioned-keep cs csᶜ nm (_ , e))))

------------------------------------------------------------------------
-- §4  The theorem
------------------------------------------------------------------------

finish-den : Δ ∋ᵅ γ → Δ ⊨ t := γ → Δ ∋ˡ finish X t := γ
finish-den lv (den-pos d) = d
finish-den lv (den-gone n) = ⊥-elim (n lv)

-- Both scopes are read in full (interior AND conversion) at their
-- exteriors, the path `Π` leads from the source's exterior to the
-- target's, and the target keeps the source's representation variables.
respell-respects : ∀ {Γₛ Γₛᵢ Γₛᶜ Γₜ Γₜᵢ Γₜᶜ : Ctxᵗ} {Θₛ Π Θₜ : Boundary}
  → Γₛ ⊢ⁱ Θₛ ⇒ Γₛᵢ → Γₛ ⊢ᶜ Θₛ ⇒ Γₛᶜ
  → Γₛ ⊢ⁱ Π ⇒ Γₜ
  → Γₜ ⊢ⁱ Θₜ ⇒ Γₜᵢ → Γₜ ⊢ᶜ Θₜ ⇒ Γₜᶜ
  → names Γₛᶜ ⊆ᵃ names Γₜᶜ
  → Respects (respell Θₛ Π Θₜ) (names Γₛᶜ) (names Γₜᶜ)
respell-respects (interior isₛ) (conversion csₛ) (interior iπ)
                 (interior isₜ) (conversion csₜ) keep d =
  finish-den (keep (_ , d))
    (encodeU-den isₜ csₜ (encodeI-den iπ (decodeU-den isₛ csₛ d)))

-- WRAP: from Θ's conversion reading, through Θ's interior, into the
-- dual's conversion reading; (Q) is the keeping
respects-Wrap : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ᶜ Θ ⇒ Γᶜ → Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ
  → Respects (respell Θ Θ (dual Θ)) (names Γᶜ) (names Γᵈ)
respects-Wrap ri rc rd =
  respell-respects ri rc ri (dual-interior ri) rd (Q ri rc rd)

-- MERGE, the inner part: from Θ₁'s conversion reading over Θ₂'s
-- interior, back through the dual of Θ₂ to the exterior, into the
-- merged reading
respects-Merge₁ : ∀ {Γ Γᵢ Γ₁ᵢ Γ₁ᶜ Γ⋉ᶜ : Ctxᵗ} {Θ₁ Θ₂ : Boundary}
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ → Γᵢ ⊢ᶜ Θ₁ ⇒ Γ₁ᶜ
  → Γ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Γ⋉ᶜ
  → names Γ₁ᶜ ⊆ᵃ names Γ⋉ᶜ
  → Respects (respell Θ₁ (dual Θ₂) (Θ₁ ++ Θ₂)) (names Γ₁ᶜ) (names Γ⋉ᶜ)
respects-Merge₁ ri₂ ri₁ rc₁ r⋉ keep =
  respell-respects ri₁ rc₁ (dual-interior ri₂)
    (merged-interior ri₂ ri₁) r⋉ keep

-- MERGE, the outer part: from Θ₂'s conversion reading straight into the
-- merged one (the path is empty)
respects-Merge₂ : ∀ {Γ Γᵢ Γ₁ᵢ Γ₂ᶜ Γ⋉ᶜ : Ctxᵗ} {Θ₁ Θ₂ : Boundary}
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ → Γ ⊢ᶜ Θ₂ ⇒ Γ₂ᶜ
  → Γ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Γ⋉ᶜ
  → names Γ₂ᶜ ⊆ᵃ names Γ⋉ᶜ
  → Respects (respell Θ₂ [] (Θ₁ ++ Θ₂)) (names Γ₂ᶜ) (names Γ⋉ᶜ)
respects-Merge₂ ri₂ ri₁ rc₂ r⋉ keep =
  respell-respects ri₂ rc₂ (interior changes[])
    (merged-interior ri₂ ri₁) r⋉ keep

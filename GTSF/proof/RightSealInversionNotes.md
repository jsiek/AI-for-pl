# `right-seal-inversion₁` proof notes

These notes record the local proof search for the postulate in
`proof.DynamicGradualGuarantee`:

```agda
right-seal-inversion₁ :
  ∀ {Δ σ γ M V r A α} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
```

No new postulates were added during this exploration.

## Attempt 1. Direct structural inversion

The first direct definition tried only the two right-cast constructors:

```agda
right-seal-inversion₁ (⊒cast+ qᶜ q⨟s≈r M⊒M′) = _ , M⊒M′
right-seal-inversion₁ (⊒cast- qᶜ q⨟s≈r M⊒M′) = _ , M⊒M′
```

Agda rejected the `⊒cast+` split because it could not solve
`M′ ⟨ - s ⟩ ≟ V ⟨ seal A α ⟩`.  The blocker is the defined dual
operation `-_`, not the term shape itself.

## Attempt 2. Equality-indexed outer cast

The next attempt used an auxiliary with an arbitrary outer coercion `c` and a
separate equality `c ≡ seal A α`:

```agda
right-seal-inversion₁-aux :
  ∀ {Δ σ γ M V c r A α} →
  c ≡ seal A α →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ c ⟩ ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
```

This avoids asking coverage to reduce `- s`.  Agda then exposed the real
frontier: `extend`, where the right term is stuck as `N′ [ α ]ᵀ`.

## Attempt 3. Equality-indexed right term

The auxiliary was generalized again to carry an arbitrary right term `T`:

```agda
right-seal-inversion₁-aux :
  ∀ {Δ σ γ M T V c r A α} →
  T ≡ V ⟨ c ⟩ →
  c ≡ seal A α →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
```

With this shape, the `extend` case can use the existing transport
`extendReplaceRel-term (replace-here qᶜ)` from `proof.Catchup` after the
recursive call:

```agda
right-seal-inversion₁-aux eq c≡seal (extend qᶜ pαᶜ M⊒Vseal)
    with right-seal-inversion₁-aux eq c≡seal M⊒Vseal
... | q , M⊒V =
  q , extendReplaceRel-term (replace-here qᶜ) M⊒V
```

This got past `extend`.  Agda then stopped at `split`.

## Frontier. `split`

For `split`, the premise strips under `(α ꞉ q) ∷ σ`, but the conclusion must
live under `(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ` and changes the source opening from
`N [ α ]ᵀ` to `N [ αᵢ ]ᵀ`.

The obvious recursive call gives:

```agda
Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ N [ α ]ᵀ ⊒ V ∶ q′
```

The desired conclusion is:

```agda
Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ ∣ γ
  ⊢ N [ αᵢ ]ᵀ ⊒ V ∶ q″
```

This is not the same transport as `extendReplaceRel-term`: it must both change
the source opening and retype or reindex the exposed coercion.  This matches
the existing split warning in `proof.Catchup`, where `catchup-split-catchup`
is still postulated because the split-specific opening transport has not been
mechanized.

## Counterexample search

After merging the latest `main`, the stricter narrowing/widening grammar made
one proof branch clearer: a right `⊒cast+` cannot hide a right seal, because it
would require a `Narrowing (unseal α A)`.  Splitting on the possible ground
casts closes the analogous tag-looking cases.

The actual counterexample is simpler than the earlier `split` search.  It is
mechanized in `proof.RightSealInversionCounterexample`:

```agda
counterexample-premise :
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩
      ⊒ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩
    ∶ id (＇ 0)
```

The premise is built by adding a right seal to the bare constant relation and
then adding the same seal on the left:

```agda
right-sealed-constant =
  ⊒cast- idNatᶜ right-seal-compose (κ⊒κ k0)

counterexample-premise =
  cast-⊒ idAlphaᶜ left-seal-compose right-sealed-constant
```

If `right-seal-inversion₁` were true, applying it to
`counterexample-premise` would produce:

```agda
∃[ q ]
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩ ⊒ $ (κℕ 0) ∶ q
```

The module proves this stripped relation impossible:

```agda
stripped-impossible :
  ∀ {q} →
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ($ (κℕ 0)) ⟨ seal (‵ `ℕ) 0 ⟩ ⊒ $ (κℕ 0) ∶ q →
  ⊥
```

The two nontrivial stripped cases are:

- `cast+⊒`: the displayed left seal would have to be `- t`, so `t` would be
  `unseal`.  The post-merge grammar has no `Narrowing (unseal α A)`.
- `cast-⊒`: the premise relates bare constants, forcing its index to be
  `id (‵ `ℕ)`.  The composition side condition then forces the remaining
  narrowing after the visible seal to have type `＇ 0 ⊒ ‵ `ℕ`, which is ruled
  out by `narrowing-var-to-older⊥`.

The final checked statement is:

```agda
right-seal-inversion₁-counterexample :
  (∀ {Δ σ γ M V r A α} →
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
    ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q) →
  ⊥
```

So `right-seal-inversion₁` is false as currently stated.  Any replacement
lemma must exclude left-cast wrappers like this example, or return a weaker
conclusion that permits a compensating left seal.

## Exact DGG `seal-unseal` case search

The DGG redex case is narrower than `right-seal-inversion₁`.  The local goal is
the branch

```agda
dynamicGradualGuarantee okM
    (⊒cast+ {s = seal B α} qᶜ q⨟seal≈r M⊒Vseal)
    (pure-step (seal-unseal vV))
```

where `M⊒Vseal` relates `M` to `V ⟨ seal A α ⟩` and the outer
`⊒cast+` supplies the side condition

```agda
Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F .
```

The paper proof uses zero source steps and contracts the relation itself:

```agda
σ ⊢ M ⊒ V ⟨ α♯ ⟩ ⟨ α♭ ⟩ : q
=/⊢→
σ ⊢ M ⊒ V : q .
```

### Attempt 1. Reuse `right-seal-inversion₂`

The current mechanized lemma `right-seal-inversion₂` is intentionally weak.  It
only re-exposes the premise relation at endpoint-normalized composition:

```agda
∃[ u ]
  (Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ u ∶ src q ⊒ ＇ α) ×
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ u
```

This is enough to document that the right redex was introduced by the exact
outer cast, but it does not strip the remaining right seal.  Returning
`M⊒Vseal` in DGG therefore gives a relation to the pre-step term, not the
right-hand reduct `V`.

### Attempt 2. Prove a `q`-specific zero-step contraction

The strongest DGG-shaped helper is:

```agda
right-seal-strip-zero :
  ∀ {Δ σ M V q r A B C D E F α} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ q
```

The direct `⊒cast-` branch exposes a premise
`M ⊒ V ∶ q₀`.  To return exactly `q`, the proof must cancel two right-seal
compositions:

```agda
q  ⨾ⁿ seal B α ≈ r
q₀ ⨾ⁿ seal A α ≈ r
```

and then reindex the term-narrowing derivation from `q₀` to `q`.  No such
right-seal cancellation lemma currently exists.  Even after cancellation, the
needed reindexing resembles the unfinished `termNarrowing-resp-≈` hole in
`proof.LeftSealNarrowingInversion`.

Left-cast cases need more than cancellation.  For example, a branch shaped by
`cast+⊒` requires a factorization lemma turning

```agda
q ⨾ⁿ seal B α ≈ p
r ≈ t ⨾ⁿ p
```

into some `u` such that

```agda
u ⨾ⁿ seal B α ≈ r
u ≈ t ⨾ⁿ q .
```

The current composition API packages `_⨟ⁿ_` and endpoint equivalence, but it
does not provide this associativity/factorization principle.

### Attempt 3. Weaken the final index existentially

DGG only existentially quantifies the final index, so the branch could use the
weaker helper:

```agda
right-seal-strip-some :
  ∀ {Δ σ M V q r A B C D E F α} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ p ] Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ p
```

This removes the `q₀ ≡ q` cancellation obligation in the direct `⊒cast-`
branch, but it still gets stuck before the proof reaches that branch.  Agda's
coverage checker exposes `extend`:

```text
N′ [ α ]ᵀ ≟ V ⟨ seal A α₁ ⟩
p [ α ]ᶜ ≟ r
```

An equality-indexed auxiliary can expose `extend`, and the output can move from
the source-only store to the ordinary store with `extendReplaceRel-term`.  The
corresponding `split` branch still needs the same source-opening transport that
is called out by `catchup-split-catchup`: the proof must change the source term
from `N [ α ]ᵀ` to `N [ αᵢ ]ᵀ` while preserving or reconstructing the stripped
right term and index.

### Attempt 4. Catch up the source first

Another route catches `M` up to a source value using

```agda
catchup-lemma okM (vV ⟨ seal A α ⟩) M⊒Vseal .
```

This produces a value `W` with

```agda
W ⊒ applyTerms χs (V ⟨ seal A α ⟩)
  ∶ applyCoercions χs r .
```

However, this route still needs a value-level version of the same right-seal
stripping/contraction fact to obtain a relation to `applyTerms χs V`.  The
existing left widening/narrowing lemmas move casts on the source side; they do
not remove this remaining right seal.

### Attempt 5. Cancel two right-seal compositions

The direct `⊒cast-` strip branch first suggested the algebraic cancellation

```agda
right-seal-compose-cancelᶜ :
  Δ ∣ srcStoreⁿ σ ⊢ q  ∶ᶜ C  ⊒ D →
  Δ ∣ srcStoreⁿ σ ⊢ q₀ ∶ᶜ C₀ ⊒ D₀ →
  Δ ∣ σ ⊢ q  ⨾ⁿ seal B  α ≈ r ∶ E  ⊒ F →
  Δ ∣ σ ⊢ q₀ ⨾ⁿ seal A₀ α ≈ r ∶ E₀ ⊒ F₀ →
  q₀ ≡ q .
```

A first proof tried to use the `StoreDetWf` carried by `compose-leftⁿ` and the
seal memberships from the internal composition.  This is not sufficient:
`endpointsⁿ` has its own target store for the computed composite, and that
store is the one constrained by the store narrowing `σ`.  The internal
composition store and the endpoint target store are related only through the
fact that both type the computed composite.

The useful algebraic fact added during this attempt is the dual of
`srcStoreⁿ-⊒ˢ`:

```agda
tgtStoreⁿ-⊒ˢ :
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Σ′ ≡ tgtStoreⁿ σ .
```

The next cancellation attempt should first prove a shape lemma for the computed
composite `proj₁ (_⨟ⁿ_ q⊒ seal⊒)`: any endpoint typing of that computed
coercion must expose the final seal membership in the endpoint target store.
Only after extracting those endpoint-store memberships can `tgtStoreⁿ-⊒ˢ` and
store uniqueness force the two seal payloads to agree.  Trying to use the
internal `cast-seal` memberships repeats the wrong-store mistake.

For the DGG redex itself this cancellation is less central than it first
appeared, because the theorem conclusion existentially chooses the post-step
index `p′`.  In the direct `⊒cast-` branch the proof can return the inner
relation at its original index.  The cancellation lemma would still be useful
for a stronger exact-index strip theorem, but the DGG-oriented strip theorem
mainly needs the store-shaping cases (`extend` and `split`) and a way to handle
or exclude remaining left-cast wrappers after catchup.

For `extend`, `extendReplaceRel-term` and `extendReplaceRel-compose-left`
transport from the source-only store `(α ꞉= A ⊒) ∷ σ` to the ordinary store
`(α ꞉ q) ∷ σ`.  The recursive strip premise would need the opposite direction:
from the outer composition in `(α ꞉ q) ∷ σ` to a composition premise in
`(α ꞉= A ⊒) ∷ σ`.  Reusing the existing transport directly therefore repeats
the wrong-direction mistake.

### Attempt 6. Existential strip goals after exposing Agda holes

The equality-indexed scratch theorem was checked far enough to expose the exact
remaining goals for

```agda
right-seal-strip-some :
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ p ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p
```

The easy cases are:

- direct `⊒cast-`: return the premise relation to `V`;
- right `⊒cast+` with `unseal`: impossible by
  `right-seal-inversion₂-cast-unseal⊥`;
- right `⊒cast+` with tag/untag: syntactically impossible after exposing
  small dual-shape contradictions for `-(G !)` and `-(G ？)` versus `seal`.

The remaining Agda goals are exactly the structural and source-left wrappers:

```agda
∃[ p ] Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ V ∶ p
∃[ p ] Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ ∣ γ
  ⊢ N [ αᵢ ]ᵀ ⊒ V ∶ p
∃[ p ] Δ ∣ σ ∣ γ ⊢ ν ★ N (⇑ᶜ r) ⊒ V ∶ p
∃[ p ] Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ V ∶ p
∃[ p ] Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ V ∶ p
```

This rules out a purely local fix to the DGG hole.  The source-left goals need
the factorization that cambridge25 calls out in the erratum:

```agda
q ⨾ⁿ seal B α ≈ r
r ≈ t ⨾ⁿ p
```

must decompose so the induction can strip the premise and rebuild `cast+⊒`.
Similarly, the `cast-⊒` branch needs a decomposition of

```agda
q ⨾ⁿ seal B α ≈ p
r ≈ t ⨾ⁿ p .
```

No existing lemma proves either factorization.  The raw coercion lemma
`⨟-sealʳ` suggests the intended trailing-seal algebra, but the typed
`_⨟ⁿ_` composition only exposes the computed composite inside
`compose-leftⁿ`/`compose-rightⁿ`.

The most direct factorization for the `cast+⊒` source-left case is false.  The
module `proof.RightSealFactorCounterexample` proves

```agda
case1-factorization-is-false :
  Case1Factorization →
  ⊥
```

using the exact premises

```agda
id (‵ `ℕ) ⨾ⁿ seal (‵ `ℕ) 0 ≈ seal (‵ `ℕ) 0
seal (‵ `ℕ) 0 ≈ seal (‵ `ℕ) 0 ⨾ⁿ id (＇ 0)
```

and showing that no `q′` can satisfy

```agda
q′ ⨾ⁿ seal (‵ `ℕ) 0 ≈ id (＇ 0) .
```

So the DGG proof cannot proceed by simply decomposing every source-left cast
into a smaller right-seal composite.  The next proof attempt should instead be
a genuinely dynamic helper that lets source-left casts take their own source
steps, probably using the existing value-level `left-widening-lemma` and
`left-narrowing-lemma`, rather than trying to prove a zero-step strip theorem.

### Attempt 7. Value-restricted right-seal continuation

The next scratch theorem restricted the strip to source values:

```agda
rightSealValueStrip :
  Value W →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ W ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ p ] Δ ∣ σ ∣ [] ⊢ W ⊒ V ∶ p
```

This restriction is meaningful: the checked
`proof.RightSealFactorCounterexample` uses a source-left `cast+⊒` whose source
cast is `- seal`, i.e. `unseal`, so the source term is not a value.  The
value-restricted theorem therefore avoids that exact counterexample.

The equality-indexed scratch version closed these cases:

- all target-shape contradictions (`⊒blame`, variables, lambdas, applications,
  `Λ`, `⊒Λ`, `⊒⟨ν⟩`, `⊒α`, `⊒ν`, constants, and primitive operations);
- right `⊒cast+`: cast-term injectivity gives the premise target `V`, so the
  premise relation is the witness;
- right `⊒cast-`: the same cast-term injectivity argument gives the premise
  relation.

The remaining value-restricted goals are:

```agda
extend
split
ν⊒
cast+⊒
cast-⊒
```

This is a better target than the original zero-step strip, but it still does
not directly fill the DGG hole after a `catchup-lemma` call.  Catchup relates
the source value to `applyTerms χs (V ⟨ seal A α ⟩)`, so the continuation must
be stated over the renamed target value and transported through the emitted
store prefix.  The likely DGG-shaped helper has final right side
`applyTerms χs V`:

```agda
right-seal-unseal-catchup :
  RuntimeOK M →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ N ⊒ applyTerms χs V ∶ p′
```

The literal `dynamicGradualGuarantee` conclusion currently wants bare `V`, so
after this helper there is still a global target-transport issue unless the
helper can prove that the emitted source changes leave `V` unchanged in the
needed cases.

A dynamic scratch probe confirmed this mismatch mechanically: after
`catchup-lemma okM (vV ⟨ seal A α ⟩) M⊒Vseal`, the available relation is to
the sealed target, not to `V`; attempting to finish the branch with a reflexive
placeholder fails at exactly the required term-narrowing derivation
`W ⊒ V`.

As a small checked algebraic step toward the renamed continuation,
`proof.ReductionProperties` now proves

```agda
applyCoercions-seal :
  ∀ χs A α →
  applyCoercions χs (seal A α) ≡
    seal (applyTys χs A) (applyTyVars χs α)

applyCoercions-unseal :
  ∀ χs α A →
  applyCoercions χs (unseal α A) ≡
    unseal (applyTyVars χs α) (applyTys χs A)

applyTerms-cast-seal :
  ∀ χs M A α →
  applyTerms χs (M ⟨ seal A α ⟩) ≡
    applyTerms χs M ⟨ seal (applyTys χs A) (applyTyVars χs α) ⟩

applyTerms-cast-unseal :
  ∀ χs M α A →
  applyTerms χs (M ⟨ unseal α A ⟩) ≡
    applyTerms χs M ⟨ unseal (applyTyVars χs α) (applyTys χs A) ⟩
```

These lemmas remove the coercion-shape ambiguity after rewriting the
store-changed sealed or unsealed target term.

### Attempt 8. Refine the value-source strip by source cast shape

A follow-up scratch proof tightened Attempt 7 by pattern matching on the source
`Value` evidence.  This closed the `ν⊒` branch: its source is syntactically
`ν ★ N (⇑ᶜ p)`, and `ν` is not a `Value` constructor.  The ordinary right-cast
branches remained as before:

- right `⊒cast+` is either syntactically impossible or, for the hidden
  `unseal`, contradictory by `right-seal-inversion₂-cast-unseal⊥`;
- right `⊒cast-` strips directly to its premise relation.

After splitting source-left casts against `Inert`, the only remaining
source-left shapes are the ones whose visible source cast can be a value:

```agda
cast+⊒ with t = c ↦ d
cast+⊒ with t = `∀ c
cast+⊒ with t = G ？
cast+⊒ with t = unseal β A
cast+⊒ with t = inst B c

cast-⊒ with t = c ↦ d
cast-⊒ with t = `∀ c
cast-⊒ with t = G !
cast-⊒ with t = seal A β
cast-⊒ with t = gen B c
```

So the value-source strip is not blocked by arbitrary source-left casts; it is
blocked by exactly the inert cast forms.  These are also exactly the forms that
would require either typed endpoint contradictions or a dynamic move via
`left-widening-lemma`/`left-narrowing-lemma`.

The typed composition code points at the likely algebraic boundary.  In
`_⨟ⁿ_`, composing any narrowing on the right with a seal goes through
`wrap-sealⁿ`, yielding either a literal `seal A α` or a strict narrowing
followed by `︔ seal A α`.  A useful next algebraic lemma would expose this
trailing-seal shape for the computed composite in `compose-leftⁿ`; the existing
raw coercion lemma `⨟-sealʳ` is the untyped analogue.

A read-only algebra pass narrowed the source-left obligations further.  The
existing library already has the endpoint facts that most of these branches
need:

```agda
narrowing-cross-var-source-target
widening-cross-var-target-source
narrowing-target-star-source-star
widening-source-star-target-star
narrowing-var-to-star⊥
widening-star-to-var⊥
narrowing-cross-ground-target-seal-var⊥
widening-cross-ground-source-seal-var⊥
```

The expected reusable corollary is not just a raw syntax fact.  It must combine
the endpoint stores from `endpointsⁿ`, `srcStoreⁿ-⊒ˢ`/`tgtStoreⁿ-⊒ˢ`, and mode
conflicts such as `tag-or-id-seal-conflict`.  The over-broad first statement

```agda
right-seal-compose-castlike-result⊥ :
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ p ∶ src q ⊒ ＇ α →
  ⊥
```

is false.  The checked module `proof.RightSealBroadCounterexample` gives the
witness

```agda
p = (＇ 0) ？
q = id ★
B = ★
α = 0
```

and proves

```agda
right-seal-compose-to-untag :
  1 ∣ (0 ꞉ id ★) ∷ []
    ⊢ id ★ ⨾ⁿ seal ★ 0 ≈ (＇ 0) ？ ∶ src (id ★) ⊒ ＇ 0
```

The reason is that `∶ᶜ` uses `tag-or-idᵈ`, while the computed right-seal
composite is typed under `seal-or-idᵈ`; `endpointsⁿ` relates the endpoints
without requiring the same mode witness on both sides.

The same checked module proves the narrower source-endpoint contradiction:

```agda
right-seal-compose-source-var⊥ :
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ ＇ α ⊒ ＇ α →
  ⊥
```

This is the useful algebraic boundary for the old closed
`right-seal-inversion₁` counterexample: that counterexample's stripped index is
`id (＇ α)`, and an exact DGG outer premise would force precisely the impossible
source endpoint `＇ α ⊒ ＇ α`.

### Attempt 9. Use the source-endpoint contradiction on source-left casts

The checked lemma `right-seal-compose-source-var⊥` is too narrow to close all
of the inert source-left branches by itself.  It applies when the exact outer
right-seal premise has endpoints

```agda
＇ α ⊒ ＇ α
```

That is exactly why the old closed `right-seal-inversion₁` counterexample cannot
be wrapped in the DGG `⊒cast+ {s = seal B α}` branch.  It does not by itself
cover source-left casts whose post-cast index has source endpoint `★`, a base
type, a function type, or a different store variable.

So the next helper should be DGG-shaped rather than a blanket contradiction:
first expose the right-seal exactness, then handle the source-left branches with
the value-level left widening/narrowing lemmas that already appear in
`catchup-lemma`.  A useful target statement is:

```agda
right-seal-unseal-catchup :
  RuntimeOK M →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ E ⊒ F →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ⟨ seal A α ⟩ ∶ r →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ V ∶ p′
```

The direct `⊒cast-` branch of this helper should strip the target seal with
zero source steps.  The `⊒cast+` branch whose hidden target cast is `unseal`
is contradictory by `right-seal-inversion₂-cast-unseal⊥`.  The remaining
source-left `cast+⊒` and `cast-⊒` branches are the places where a source value
may need to reduce through the inert cast before the post-step relation to `V`
can be built.

One source-left branch is now especially concrete.  In

```agda
cast-⊒ {t = seal A β} pᶜ r≈seal⨟p M⊒Vseal₀
```

the exact outer premise has result `p`:

```agda
q⨾seal≈p : Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ p ∶ src q ⊒ ＇ α
```

The branch closes by `right-seal-compose-source-var⊥` once the endpoints are
rewritten to `＇ α ⊒ ＇ α`.  The algebraic fact needed for this rewrite is a
cast-like variable-to-variable endpoint inversion:

```agda
castlike-var-var-endpoints :
  Δ ∣ Σ ⊢ p ∶ᶜ ＇ β ⊒ ＇ α →
  β ≡ α
```

This is now proved in `proof.NarrowWidenProperties` using
`narrowing-var≢-to-var-tag⊥`.  The branch packaging is also checked:

```agda
right-seal-compose-left-seal-factor⊥ :
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ p ∶ src q ⊒ ＇ α →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ seal A β ⨾ⁿ p ∶ E ⊒ F →
  ⊥
```

The proof transports the cast-like typing of `p` to endpoints
`＇ β ⊒ ＇ α`, applies `castlike-var-var-endpoints`, and then transports the
outer right-seal composition to the impossible endpoint `＇ α ⊒ ＇ α`.

Three other source-left inert shapes are impossible before using the outer
right-seal premise, because `compose-rightⁿ` requires its left factor to be a
narrowing:

```agda
compose-right-unseal-factor⊥ :
  Δ ∣ σ ⊢ r ≈ unseal β A ⨾ⁿ p ∶ E ⊒ F →
  ⊥

compose-right-inst-factor⊥ :
  Δ ∣ σ ⊢ r ≈ inst B c ⨾ⁿ p ∶ E ⊒ F →
  ⊥

compose-right-tag-factor⊥ :
  Δ ∣ σ ⊢ r ≈ G ! ⨾ⁿ p ∶ E ⊒ F →
  ⊥
```

These remove the `cast+⊒` branches with `t = unseal β A` and `t = inst B c`,
and the `cast-⊒` branch with `t = G !`.  The remaining source-left branches
are therefore the dynamically meaningful function, universal, ground untag,
and generic `gen` cases, plus any endpoint-specific refinements of those.

### Counterexample search

The known `right-seal-inversion₁` counterexample does not satisfy the exact DGG
outer-cast premise.  In that example the sealed relation has index
`id (＇ 0)`, but the DGG branch would require some `q` with

```agda
q ⨾ⁿ seal (‵ `ℕ) 0 ≈ id (＇ 0) .
```

`proof.RightSealInversionCounterexample` already proves this impossible in
`old-counterexample-revised-premise⊥`.

The `right-seal-inversion₂` variable counterexample is also not an exact DGG
counterexample: its right-side core is a variable rather than a `Value`, the
term context is nonempty, and the top-level derivation is `ν⊒`, not the exact
outer `⊒cast+` redex used by DGG.

The closed exact candidates that do type check are harmless.  The basic
constant case

```agda
$ 0 ⊒ (($ 0) ⟨ seal (‵ `ℕ) 0 ⟩) ⟨ unseal 0 (‵ `ℕ) ⟩
```

has the expected post-step relation `$ 0 ⊒ $ 0`.  The closed `ν⊒` candidate
with an admissible identity annotation also has a post-step relation:

```agda
ν ★ ($ 0) (⇑ᶜ (id (‵ `ℕ))) ⊒ $ 0 .
```

The tempting `ν⊒` counterexample would annotate the source `ν` with a shifted
seal coercion.  Agda rejects this shape for the DGG premises: `ν⊒` requires its
index premise to be cast-like, and `∶ᶜ` is `tag-or-idᵈ`, so literal seals are
excluded by `tag-or-id-seal-conflict`.

Before the source-left tag candidate below, no exact counterexample to the DGG
redex had been found.  The checked factorization counterexample only refutes a
tempting zero-step proof strategy: it does not refute the dynamic branch,
because DGG may still reduce the source side through the problematic left cast
before relating it to the unsealed target.

### Attempt 10. Broad exact source-left tag candidate

The broad algebraic witness

```agda
id ★ ⨾ⁿ seal ★ 0 ≈ (＇ 0) ？
```

is term-realizable.  `proof.ExactSealUnsealCounterexample` first checks the
benign direct premise

```agda
c★ ⊒ c★ ⟨ seal ★ 0 ⟩ ⟨ unseal 0 ★ ⟩ ∶ id ★
```

where `c★ = ($ 0) ⟨ (‵ `ℕ) ! ⟩`.  This is not a counterexample, because
after the right `seal-unseal` step the source and target are both `c★`, and
the existing two-sided cast example gives `c★ ⊒ c★ ∶ id ★`.

A more dangerous exact premise adds a real source-side tag:

```agda
c★ ⟨ seal ★ 0 ⟩ ⟨ (＇ 0) ! ⟩
  ⊒ c★ ⟨ seal ★ 0 ⟩ ⟨ unseal 0 ★ ⟩ ∶ id ★
```

This also type-checks in `proof.ExactSealUnsealCounterexample`.  It uses
`c★ ⟨ seal ★ 0 ⟩ ⊒ c★ ⟨ seal ★ 0 ⟩ ∶ id (＇ 0)`, then a source-left
`cast+⊒` with `t = (＇ 0) ？`, and finally the broad right-seal composition
above.  The source is a value, so any counterexample proof reduces to the
post-step impossibility

```agda
∀ Δ p →
  Δ ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ c★ ⟨ seal ★ 0 ⟩ ⟨ (＇ 0) ! ⟩ ⊒ c★ ∶ p →
  ⊥ .
```

The inversion discharges the outer right-cast and source `cast-⊒` tag cases
using term-cast injectivity plus
`compose-left-tag-factor⊥`/`compose-right-tag-factor⊥`.  The source-left
`cast+⊒` branch peels the tag and then proves
`c★ ⟨ seal ★ 0 ⟩ ⊒ c★` impossible by a second inversion: the only productive
route would force either a tag factor in the wrong composition position or a
seal/untag endpoint contradiction.

The final checked theorem is

```agda
exact-seal-unseal-dgg-result⊥ :
  ExactSealUnsealDGGResult → ⊥
```

where `ExactSealUnsealDGGResult` is the DGG conclusion instantiated with the
checked premise

```agda
c★ ⟨ seal ★ 0 ⟩ ⟨ (＇ 0) ! ⟩
  ⊒ c★ ⟨ seal ★ 0 ⟩ ⟨ unseal 0 ★ ⟩ ∶ id ★
```

and the target step `seal-unseal`.  The conclusion is refuted after
`value-multistep-refl` forces the source reduction to be zero steps.  The
post-step contradiction is generalized over the existentially chosen `Δ′`;
otherwise the DGG result could hide behind an arbitrary context choice even
though the source and target stores are both empty after the step.

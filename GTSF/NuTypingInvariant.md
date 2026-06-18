# Nu Typing Invariant for `β-gen`

This note records the term-typing strengthening needed to remove the
`coercion-open-gen-existing` postulate in `proof/NuPreservation.agda`.
The goal is to reject programs where the type variable used for a runtime seal
is later reused as the tag-like variable produced by opening a `gen` coercion.

## The Preservation Blocker

The problematic preservation case has the shape

    (V ⟨ gen C c ⟩) • α  -->  V ⟨ c[α] ⟩

The premise for `cast-gen` types the body coercion as

    suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σtag ∣ ⟰ᵗ Σseal
      ⊢ c ∶ ⇑ᵗ C =⇒ B

The bound zero introduced by `gen` is tag-like. After opening at an existing
type variable `α`, preservation must type `c[α]` in a cast split where `α` is on
the tag side. The current application rule only remembers `α < Δ`, so it cannot
show that `α` is absent from the seal side of the split.

The counterexample in `NuPreservationCounterexample.agda` exploits exactly
this gap: after a `ν-step`, the term applies a `gen` coercion at the newly
allocated seal variable `α`, while the same coercion body already uses free
`α` as a seal. Opening the bound tag variable to `α` then requires `α` on both
sides of one split.

## Why a Local `ν` Check Is Too Early

A rule that only recognizes

    ν α := A. L α ⟨ B[seal_α] ⟩

does not survive long enough. The `ν-step` removes the syntactic `ν`, leaving
the body in a store that now contains `α`. The later `β-gen` step only sees a
plain type application `L • α`. Therefore the evidence must be attached to the
typing of that application, or to the typing of the polymorphic value being
applied.

## Why a Raw `NoTyVar α L` Premise Is Not Enough

The source-language invariant says that in

    ν α := A. L α ⟨ B[seal_α] ⟩

both `L` and `B` do not mention `α`. As a closed-program criterion this is the
right intuition, but using only a raw syntactic premise on `⊢•` is too weak for
the metatheory.

The first pitfall is freshness. The reduction relation should carry `Δ`, and
`ν-step` should allocate only variables at or above `Δ`:

    Δ ≤ α
    -------------------------------------
    Δ ∣ Σ ∣ ν A N  -->  (α , A) ∷ Σ ∣ N[α]

Then the common progress choice is `α = Δ`. This keeps opening from collapsing
the new runtime seal onto an existing type variable in the open preservation
theorem. Without this Δ-indexed freshness discipline, a raw no-occurrence fact
for the bound zero would not transport cleanly through `singleRenameᵗ α`.

Even with Δ-indexed freshness, term substitution makes polymorphic variables
matter. A term such as
`f • α` is syntactically α-free in its function position, but after β
substitution the value supplied for `f` may contain a bad `gen` coercion that
uses `α` as a seal. Thus the invariant cannot live only on the surface syntax
of the application; the context must record what is promised about values
standing behind polymorphic variables.

## Strengthened Judgment

A workable term system should track a seal-use effect:

    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A ▷ E

Here `E` is the set of type variables that the term may use in seal positions
inside suspended casts. The term context must carry the same information:

    Γ ::= [] | x : A ▷ E , Γ

The important rules are:

    x : A ▷ E ∈ Γ
    -------------------------
    Δ ∣ Σ ∣ Γ ⊢ x ⦂ A ▷ E

    Δ ∣ Σ ∣ Γ ⊢ L ⦂ ∀B ▷ E
    α < Δ
    α ∉ E
    α ∉ FV(B)
    -----------------------------
    Δ ∣ Σ ∣ Γ ⊢ L • α ⦂ B[α] ▷ E

The `α ∉ E` premise is the invariant needed by `β-gen`: the function being
opened at `α` may not have any suspended coercion that uses `α` as a seal. The
`α ∉ FV(B)` premise reflects the source-program restriction that the result
body `B` does not already mention the runtime seal variable.

The cast rule computes the effect of a cast from its coercion:

    Δ ∣ complement d ∣ Π ⊢ c ∶ A =⇒ B
    dom(Π) ⊆ SealUses(c)
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A ▷ E
    -----------------------------------------
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B ▷ E ∪ SealUses(c)

`SealUses(c)` can be defined either syntactically or by a more precise
derivation-indexed relation over coercion typing. The derivation-indexed
version is closer to the existing split discipline: `cast-seal` and
`cast-unseal` contribute the sealed variable, while `cast-gen` treats its bound
zero as tag-like and does not contribute it as a free seal use.

The `dom(Π) ⊆ SealUses(c)` premise rules out gratuitously placing a variable on
the seal side of a split. This is important because the raw two-store coercion
judgment is monotone in both stores: without exactness, a derivation could put
`α` in `Π` even when `c` never uses `α` as a seal, and the later `β-gen` proof
would still be unable to choose the tag-side split.

## Effect-System Preservation Pattern

The standard preservation proof for an effect system treats effects as upper
bounds. A subeffecting rule lets a term checked with effect `E` also be checked
with any larger effect `F`:

    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A ▷ E
    E ⊆ F
    ----------------------
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A ▷ F

For β-reduction, the substitution lemma must respect the effect promised by the
context:

    Δ ∣ Σ ∣ x : A ▷ Earg , Γ ⊢ N ⦂ B ▷ EN
    Δ ∣ Σ ∣ Γ ⊢ V ⦂ A ▷ EV
    EV ⊆ Earg
    ---------------------------------------
    Δ ∣ Σ ∣ Γ ⊢ N[V/x] ⦂ B ▷ EN

The key point is that `Earg` is not chosen at the application site in isolation.
It is latent in the function type, so the application rule can compare the
actual argument effect with the assumption used when typing the function body.

## Preservation Attempt: Latent Function Effects

The first preservation attempt shows that the simple judgment-level effect is
not enough for β-substitution. The prototype lambda rule checks the body with
the bound argument assigned effect `∅`:

    Δ ∣ Σ ∣ x : A ▷ ∅ , Γ ⊢ M ⦂ B ▷ E
    ----------------------------------
    Δ ∣ Σ ∣ Γ ⊢ λx. M ⦂ A → B ▷ E

This makes the following term typable whenever `α < Δ`:

    (λf. f α) V

Inside the lambda body, `f` has effect `∅`, so the type-application premise
`α ∉ Effect(f)` holds. But after β-reduction the target is

    V α

Typing this target requires `α ∉ Effect(V)`. The source typing only knows that
`V` has type `∀B`; it does not know that `V` satisfies the latent cleanliness
assumption used when checking the body. If `V` is a polymorphic value carrying a
suspended `gen` coercion whose body uses `α` as a seal, the source term is
accepted by the prototype while the reduct is rejected.

Therefore the preservation theorem requires latent argument effects on function
types, or an equivalent refinement of function values. The arrow type should
record the effect promised for the parameter:

    A -[Earg]-> B

Then the lambda rule checks the body under `x : A ▷ Earg`, and the application
rule must require the actual argument effect to be included in `Earg`. This is
the ordinary reason effect systems annotate function types, and it applies here
even though the effect tracks suspended seal uses rather than evaluation
effects.

The current prototype implements this as an effect-decorated type layer:

    A ⇒[ Earg ] B

with erasure back to the ordinary GTSF type `erase(A) ⇒ erase(B)`. This keeps the
core `Types.agda` grammar unchanged while making the latent effect available to
the preservation proof.

The same preservation attempt also suggests that effects should be treated as
upper bounds rather than exact lists. β-substitution can duplicate an argument,
so an exact list effect is not stable. The metatheory should use an inclusion
or subeffecting relation:

    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A ▷ E
    M --> N
    --------------------------------
    ∃ E'. Δ ∣ Σ ∣ Γ ⊢ N ⦂ A ▷ E' and E' ⊆ E

With idempotent set-like effects, duplicating an argument does not introduce a
new forbidden type variable.

## Replacement for the Postulate

With the effect and split-exactness premises from `⊢•` and `⊢⟨⟩`, the
`β-gen` case should use two lemmas. The coercion-side bridge already has this
shape in Agda as `coercion-open-gen-tagged`:

    α < Δ
    α ∈ dom(Σtag)
    suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σtag ∣ ⟰ᵗ Π
      ⊢ c ∶ ⇑ᵗ C =⇒ B
    ------------------------------------------------------------
    Δ ∣ Σtag ∣ Π ⊢ c[α] ∶ C =⇒ B[α]

The strengthened application inversion must provide `α ∈ dom(Σtag)` for the
`gen` split. That should follow from `α ∉ E`, split exactness, and the fact
that the enclosing store contains `α`.

Equivalently, the high-level replacement for the postulate is:

    α ∉ SealUses(gen C c)
    α ∈ dom Σ
    d : Π ⊆ Σ
    suc Δ ∣ (0 , ★) ∷ ⟰ᵗ (complement d) ∣ ⟰ᵗ Π
      ⊢ c ∶ ⇑ᵗ C =⇒ B
    ------------------------------------------------------------
    ∃[ Π′ ] (d′ : Π′ ⊆ Σ) ×
      Δ ∣ complement d′ ∣ Π′ ⊢ c[α] ∶ C =⇒ B[α]

Intuitively, if the original split placed `α` on the seal side only
gratuitously, split exactness rules that derivation out. The proof can choose a
split `d′` that moves `α` to the tag side. The opened bound zero is then
checked using `tagAlpha` for `α`, while all original free seal uses remain on
the seal side.

This is the precise bridge that should replace
`coercion-open-gen-existing`.

## Preservation Obligations

The effect system must prove the usual structural lemmas:

* Weakening preserves effects.
* Type renaming transports effects; the `ν-step` case either needs a freshness
  premise strong enough for the chosen runtime name or an effect-renaming lemma
  that accounts for name collisions.
* Term substitution requires an effect-respecting substitution environment:
  each substituted value must satisfy the effect promised by its context entry.
* One-step reduction does not introduce new seal uses outside the effect
  already assigned to the redex.

The last two obligations are what make the strengthening a real term-typing
change instead of a local side condition on `⊢•`.

## Expected Outcome

The counterexample is rejected because the function in the offending
application contains a suspended `gen` body with a free `unseal α`, so its
effect contains `α`. The application premise `α ∉ E` fails after the `ν-step`,
which is exactly where the surviving evidence is needed.

The intended source shape

    ν α := A. L α ⟨ B[seal_α] ⟩

is accepted when `L` and `B` are typed with effects excluding `α`; the outer
cast that seals into `B[seal_α]` may use `α`, but it occurs after the protected
type application and is not part of the function being opened by `β-gen`.

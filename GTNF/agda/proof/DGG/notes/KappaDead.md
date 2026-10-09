# Do the counterexamples stay dead at nonempty κ?

Status: notes, 2026-10-09 (worker; question approved by Jeremy).
Agda: `KappaDead.agda` (no postulates, no holes; checked with
`agda --safe -v0 proof/DGG/notes/KappaDead.agda`).  LEFT is the MORE
precise side.

Relation checked: HEAD 8fe66241 (D31).  The working tree's
`TermImprecision`/`ImprecisionWorld` are being changed by another
worker (D32: `Revoke`, `jr-rebind`), so `KappaDead.agda` §0 carries a
verbatim copy of HEAD's relation and HEAD's `JoinRep`; `World`, the
marks, `Interior`, `WfWorld` and `ConvImp` are imported (they are
unchanged).  Every derivation below uses only `rv-none`-style
boundaries, so it is also a derivation of D32 as drafted.

## 1. Verdicts

| pair | κ = [] (PermissionExamples) | any κ (here) |
|---|---|---|
| C1 `L₆ ⊑ R₇` | dead | **RELATED** at κ = [α]: `C1.c1-at-κ` (left-first route; right-first by the same steps, not mechanized; matched route dead by R2) |
| C2 `LE₃ ⊑ RE₅` | dead | **RELATED** at κ = [α]: `C2.c2-at-κ` |
| C3 `LE₁ ⊑ RE₁` | dead | **dead**, every world, any κ, any slots: `C3.c3-dead` |
| C4 `L₀ ⊑ R₂` | dead | **RELATED** at κ = [αᴿ]: `C4.c4-at-κ` |
| C4g `L₀ ⊑ R2g` | dead | **RELATED** at κ = [αᴿ]: `C4.c4g-at-κ` |
| C5 (+ redex, hidden) | dead | dead (already, `C5Dead`) |

All worlds are well formed (`C1.c1-world-wf`, `C4.wf-V4`,
`Worlds.V⁰-wf`).  In each of these worlds the right store has exactly
one rep. var, so a well-formed κ is `[]` or permits that rep. var
(`Worlds.κ-only0`).  So question 2 (the variant with the relevant
right rep. var permitted from the start) is the same case as question
1.

**The κ-relevant world arises under a related top-level pair.**
`WrapC1.wrapped-c1`, `WrapC2.wrapped-c2` and `WrapC4.wrapped-c4` are
related at a top-level world (κ = [], well formed).  The wrapped right
blames and the wrapped left answers 5.  `RefuteC1.unrelated` shows
that no left reduct is related to any right reduct.  So **SimBack as
stated in `proof/DGG/SimBackDef` (any `WfWorld`, `κʷ W ≡ []`) is
refuted by wrapped C1** (§4).

## 2. The derivable cases, from their sources

### C1

Source programs (UNRELATED: `∀X.X→X ⋢ ∀X.X→★`):

```
L   ((ΛX. λx:X. x) : ★→★) 5 : ℕ
R   ((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ
```

Initial cast terms (UNRELATED):

```
L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
```

The pair is left state 6 against right state 7 (`C1.L₆-state`,
`C1.R₇-state`).  Each store is α:=★, and S = `[−X^α] 5⟨ℕ!⟩ ⟨−X⟩`.

```
L₆  (([+X^α] S ⟨+X⟩)⟨id(★)⟩)⟨ℕ?ℓ0⟩
R₇  ([+X^α] S⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
```

The world is `W★.V⁰ [0]`: no type variables, ϱᵍ = {(α, αᴿ)}, and
κ = [αᴿ].  The derivation, outermost first:

```
cast⊑cast ℕ?, cast⊑ id(★)
⟪⟫⊑   left +X^α:   X left-only (X⊑★ for any κ); pay X ⊑ ★ holds; K = []
⊑⟪⟫   right +X^α:  X rejoins through ϱ; mark = permit αᴿ κ = X⊑★;
                   pay X ⊑ ★ holds; K = []
⊑cast X!:          S ⊑ S at X ⊑ X, result X ⊑ ★
⟪⟫⊑⟪⟫ the seals:   5⟨ℕ!⟩ ⊑ 5⟨ℕ!⟩
```

The proof at κ = [] fails at the rejoin.  There the rejoined X is X⊑X
(`no-tag★`).  At κ = [αᴿ] it is X⊑★, and no boundary had to pay for it
because the permission came from outside.  The matched route
`⟪⟫⊑⟪⟫ (+X ⊑ id(★))` stays dead at any κ.  R2's `LeftUnpermitted`
contradicts the mark X⊑★ of a joined X, as in `C3.matched-conv`.

### C2

Source programs (UNRELATED: `∀Y.Y→Y ⋢ ∀Y.Y→★`):

```
L   (((ΛY. λx:Y. x) [ℕ]) 5 : ★) : ℕ
R   ((((λx:★. x) : ∀Y. Y→★) [ℕ]) 5) : ℕ
```

Initial cast terms (`LE`, `RE`, UNRELATED):

```
LE  ((ν X:=ℕ. ((ΛY. λx:Y. x) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩⟨ℕ?ℓ0⟩
RE  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩ X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
```

The pair is left state 3 against right state 5.  Each store is α:=ℕ,
S₄ = `[−X^α] 5 ⟨−X⟩`, and J = `[+X^α] S₄⟨X!⟩ ⟨id(★)⟩`.

```
LE₃  (([+X^α] S₄ ⟨+X⟩)⟨ℕ!⟩)⟨ℕ?ℓ0⟩
RE₅  ([+X^α] ([−X^α] J ⟨id(★)⟩)⟨id★⟩^[X:★∼X] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
```

At κ = [αᴿ] the derivation runs left first.  Every right `+X^α`
rejoins X at the permitted αᴿ, and every right `−X^α` makes X
left-only again.  The innermost pair is P4 B4's own `S ⊑ J`
(`C2.S⊑J`).  C2 and P4 differ only in where αᴿ's permission comes
from.  In P4 the matched TyBeta boundary that joins X pays for it.
In C2 at κ = [αᴿ] nothing pays for it.

### C4, C4g

Source programs (UNRELATED: `∀X.X→X ⋢ ∀X.X→★`):

```
L      ((ΛX. λx:X. x) : ★→★) 5 : ℕ
R      ((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ                       (C4)
R(g)   (((λx:★. x) : ∀X.X→★ by gen X.(X! → id★)) : ★→★) 5 : ℕ (C4g)
```

The initial cast terms are C1's `L₀`, `R₀` and C4g's `R0g` (UNRELATED).
The pair is `L₀` against the right's state 2 (`C4.R₂-state`,
`C4.R2g-state`):

```
R₂   (([+X^αᴿ] (λx:X. x⟨X!⟩) ⟨−X → id(★)⟩)⟨id★→id★⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
R2g  (([+X^αᴿ] ([−X^αᴿ] λx:★.x ⟨id★→⟩)⟨X! → id★⟩^[X:★∼X]
        ⟨−X → id(★)⟩)⟨id★→id★⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
```

The world is `C4.V4`: the left store is empty, the right store is
αᴿ:=★, nothing is paired, and κ = [αᴿ].  The derivation:

```
⊑⟪⟫  the right's Inst +X^αᴿ: push [opn X], K = [];
     pay ∀X.X→X ⊑^[X] X→★ needs X⊑★: holds (permit αᴿ κ)
Λ⊑   b-join of the opening
⊑cast X!  (C4), or the gen body X! → id★ over the right's −X (C4g)
```

At κ = [] the payment is exactly what fails (`pay-∀`).  Here the
permitted αᴿ has no left partner at all.

## 3. The dead case

`C3.c3-dead` covers every `W : World ΔL ΔL`, well formed or not, with
any κ and any slots.  The two one-sided orders fail on types alone,
because they meet X ⊑ ℕ or ℕ ⊑ X.  The left type comes from `lam-ty`
and the right type from `cast-ty-r`.  The matched order compares
`−X → +X` with `−X → id(★)`:

```
conv-seal⊑seal j        joins X (fresh, so Paired α αᴿ, conv-join-fresh)
conv-unseal⊑id★ h u     h : mark(X) = X⊑★,  u : LeftUnpermitted X
```

For a joined X, mark(X) = permit αᴿ κ.  `u` says permit αᴿ κ = X⊑X.
So R2, which is read in the exterior conversion world, kills it for
every κ.

## 4. Can that world arise?  The wrapper

```
wrap M = [+Y^α] ([−Y^α] M ⟨id(ℕ)⟩) ⟨id(ℕ)⟩
```

```
⟪⟫⊑⟪⟫ +Y ∥ +Y   fresh pair joined through ϱ (jr-join): K = [α];
                pay ℕ ⊑ ℕ at κ = []
⟪⟫⊑⟪⟫ −Y ∥ −Y   matched hide; no R1′ premise on ⟪⟫⊑⟪⟫; κ passes
                (Interior.same-κ): interior world = the C1/C2 world
                at κ = [α]
```

`wrap L₆ ⊑ wrap R₇` is related at `V⁰ []`, which has κ = [] and is
well formed.  The same holds for C2 and for C4 (in the store α:=★ on
both sides).  The runs:

```
wrap R₇  →  [+Y^α]([−Y^α] blame ⟨…⟩)⟨…⟩  →* blame        (WR-blames)
wrap L₆  →* 5, never blame                              (WL-answers, WL-never-blames)
```

The wrapped right's states after its step are `blame` under boundaries
(`BlameR`).  A derivation against such a term puts blame on the left
spine (`spine`), and no wrapped-left state has blame on its spine.  So
no left reduct is related to a right reduct (`RefuteC1.unrelated`),
and neither disjunct of SimBack holds.

Consequences:

- **SimBack as stated is false** for the D31 relation, already at
  κ = [].  SimBack quantifies over every related pair in a well-formed
  world with `κʷ W ≡ []`, and wrapped C1 is such a pair.  The
  generalized statement at any κ is false a fortiori, through C1, C2,
  C4 and C4g themselves.
- **Not settled: reachability from related sources.**  The outer `+Y^α`
  binds the same rep. var α that C1's own TyBeta allocates.  A run
  produces a second binding of an existing rep. var only by rebinding:
  P4's right `[+X^α]([−X^α] … [+X^α] …)` (the gen wrapper's J), or
  Merge's `[−X^α, +X^α]` (P4 B5).  I did not find a pair of related
  sources whose run puts C1's left boundary under such a matched
  rebinding.  The DGG theorem may still hold.  But its proof cannot go
  through SimBack over all related pairs unless the relation or the
  statement changes (§5).

## 5. The invariant the generalized statements need

`PermitNamed W O` (`KappaDead.agda` §8) says that every permitted
right rep. var β satisfies one of:

```
Named W O β =  ∃ α. (names Δ ∋ᵅ α) × Paired W α β     -- a left partner bound to a
                                                      -- left type variable in scope
             ⊎ ∃ k. (O ∋ᵒ k) × (Δ′ ∋ᵗ k := β)         -- or β's type variable is
                                                      -- opened by a slot
PermitNamed W O = All (Named W O) (κʷ W)
```

- It holds at every top-level world (κ = []).  It also holds wherever
  P4 uses its permission: inside the permitting boundary and inside the
  right's `−X` under it, the left's X stays bound to α (`p4-shape`).
- In all four counterexample worlds there is no left type variable
  and no slot, so it forces κ = [] (`no-names`; `c1-world-bad`,
  `c2-world-bad`, `c4-world-bad`).  The κ = [] proofs of
  PermissionExamples then apply.
- **The HEAD rules do not preserve it.**  The wrapper's matched hide
  removes the left's Y and keeps κ (`wrapper-breaks`).  To preserve it,
  a boundary must REVOKE for its interior every permitted β that it
  leaves without a named left partner.  D32's `Revoke` (`rv-drop`, with
  the payment read without the dropped rep. vars) has the right shape,
  but D32 makes it optional (`rv-none` is always allowed), and then the
  wrapper is still derivable.  It must be OBLIGATORY for those rep.
  vars.

Preservation, rule by rule (argued, not mechanized):

| rule | effect on PermitNamed |
|---|---|
| congruence, `blame⊑`, `ν⊑ν`, `ν⊑`, `⊑cast`, `cast⊑cast`, `cast⊑` with `co-plain`/`co-∀` | same world; the slots are kept or passed |
| `Λ⊑Λ` (`⊕²`) | κ and ϱ shift with the rep. vars; the witnesses shift |
| `Λ⊑` `b-fresh`/`b-rep` | the left gains a type variable; the witnesses shift (`shiftᴸ`) |
| `Λ⊑` `b-join` | the slot witness of β becomes a named witness: a new left type variable 0 paired lexically with β (`Join1`) |
| boundaries, the new `K` | `jr-join`: the joined X is in scope and `Joint` gives Paired; `jr-open`: β's type variable is a new slot of Oᵢ (`Fill`) |
| boundaries, the inherited κ | continuing left type variables keep their rep. vars (`Interior`); a left unbind can remove the last witness, so it must revoke.  R1′'s `ok-unbind` already says no permitted partner; `ok-hidden` (P4h) and the matched `⟪⟫⊑⟪⟫` (seals, hides) need the obligatory revocation; `⊑⟪⟫` carries slots through `Carried` |
| allocation (Sim's world evolution) | renumbering only |
| `cast⊑` with `co-gen` | **open**: the consumed slot's β loses its slot witness with no world change.  Either the consumption revokes β (the gen value does not see the binder), or the left value is shown never to rejoin β |
| Merge | **open** (the other worker's change; a merged `[−X^α, +X^α]` must keep the rejoin's witness) |

Revoking costs no existing derivation that I traced.  P4 B4's matched
seal `S ⊑ S` pays `X ⊑ X`, and P4h's left hide pays `ℕ→ℕ ⊑ ℕ→ℕ`.
Neither interior uses the permission.  Still to be checked under the
revision: TwoGen (the `co-gen` consumption), P4c (Merge), CgB1 and
C18b B7.

**Recommendation.**  Generalize Sim/SimBack/CatchupRight/CatchupLeft
to `WfWorld W × PermitNamed W O` (O the index's slots) instead of any
κ, and make revocation obligatory at boundaries for the rep. vars they
leave without a named left partner.  `PermitNamed` is derived from the
world and the index, so it needs no new world field.  The current
SimBack (`κʷ W ≡ []`) also needs the revocation, or wrapped C1
refutes it.

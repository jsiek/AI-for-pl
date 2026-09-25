# Erasure to plain System F: design, statements, example checks

2026-09-25.  Agda: `notes/ErasureProbe.agda` (module
`strong-rep-nu.notes.ErasureProbe`) and `SourceReduction.agda`.
Both are gated by `notes/All.agda`.

The goal is a theorem in the style of Blame for All Prop. 1 (Ahmed,
Findler, Siek, Wadler 2011, section 5.3) and Syntactic Type Abstraction
Lemma 5.8 / Thm 5.10 (Grossman, Morrisett, Zdancewic 2000).  An
erasure `⌊_⌋` takes run-time terms to source `STerm`s.  It preserves
types, and each run-time step either leaves the erasure unchanged or
is one source step.

Status:

  * the typing and simulation theorems are STATED as `Set`s and not
    proved;
  * `EraseCompileAt` and `EraseCompile` are PROVED;
  * all 20 compiled runs, plus `Bg` and the section 9 runs, pass the
    checks by `refl`;
  * no counterexample was found to any stated theorem;
  * one checked counterexample (`Mbad`) shows that the typing premise
    of the simulation cannot be dropped.

## 1. The erasure

### 1a. What a representation variable denotes

The key choice: an ordinary type variable is resolved to what it
DENOTES.  The resolution follows the name map to a representation
variable, then follows the store until it reaches a concrete type or
an abstract cell.  Abstract cells become source type variables.

    env(·)          α  =  α                       (junk, never read under WfCtx)
    env(Ξ, β)       β  =  0                       an abstract cell (made by Λ)
    env(Ξ, β)       α  =  ⇑ env(Ξ) α              α ≠ β
    env(Ξ, β := R)  β  =  R[env(Ξ)]               payload read BELOW its cell
    env(Ξ, β := R)  α  =  env(Ξ) α                α ≠ β

In Agda this is `env : RepCtx → Substᵗ`:

    env (abstR ∷ Ξ)   = ` 0 •ᵗ (⇑ᵗ ∘ env Ξ)
    env (bindR R ∷ Ξ) = substᵗ (env Ξ) R •ᵗ env Ξ

Two consequences:

  * An abstract cell's source index is the number of abstract cells
    NEWER than it.
  * An ALIAS cell `β := γ` denotes whatever `γ` denotes, because
    `R[env(Ξ)]` with `R = γ` is `env(Ξ) γ`.

A payload's own local `∀`s are handled by `substᵗ`'s `extsᵗ`.  That is
exactly the mixed reading `_⊢ᴿ[_]_`: local index `i < n`, free index
`n + α`.  The checks for this are `alias-concrete`, `alias-abstract` and
`abstract-numbering`.

The source SCOPE is `srcScope Ξ`, the number of abstract cells in the
store: the number of source type variables the erased term is typed
with (it is the index of the source judgement `n ∣ Γ ⊢ˢ M : A`, and it
appears only in `ErasureTyping`; `erase` itself does not use it).

### 1b. Types

    nameσ(Ξ ∣ Γ) X  =  env(Ξ) α     if X ↦ α ∈ Γ
                    =  X            otherwise (junk)
    ⌊A⌋_Δ           =  A[nameσ(Δ)]

In Agda: `nameσ`, `eraseTy`, and `eraseCtx` for term contexts.

### 1c. Terms

    ⌊x⌋_Δ               = x
    ⌊n⌋_Δ, ⌊true⌋_Δ, …  = n, true, …
    ⌊λx:A. N⌋_Δ         = λx:⌊A⌋_Δ. ⌊N⌋_Δ
    ⌊L · M⌋_Δ           = ⌊L⌋_Δ · ⌊M⌋_Δ
    ⌊ΛX. N⌋_Δ           = ΛX. ⌊N⌋_under(X,α,Δ)
    ⌊νX:=A · L ⟨c⟩⌋_Δ   = ⌊L⌋_Δ [⌊A⌋_Δ]
    ⌊M ⟪Θ, c⟫⌋_Δ        = ⌊M⌋_inside(Δ,Θ)

`inside(Ξ ∣ Γ, Θ) = Ξ ∣ Γᵢ` is the interior reading, COMPUTED
(`inside`, `interiorⁿ`).  `inside-sound` proves that
`Δ ⊢ⁱ Θ ⇒ Δᵢ` implies `inside Δ Θ ≡ Δᵢ`.

The context matters.  `P-state₁-erase` and `P-state₁-naive` show why.
After section 1a's `TyBeta` the state is `(λx:X. x) ⟪ ↥X , … ⟫ · 7`
at store `(α := ℕ)` with no ambient names:

  * the right erasure gives `(λx:ℕ. x) · 7`;
  * erasing the body at the EXTERIOR context (`eraseNaive`) leaves `X`
    dangling.

Conversions `c` vanish.  This is sound because every conversion
relates two types with the SAME erasure:

  * `seal X : A ⇝ X` requires `Δ ∋ X := A`, so `X` denotes `A`'s
    representation;
  * `unseal X` is the same in reverse;
  * `id`, `↦` and `∀` are structural.

## 2. Source reduction (`SourceReduction.agda`)

This is standard call-by-value System F on `STerm`, with the value
restriction of `⊢ˢΛ`:

    (β-ƛ)    (λx:A. N) · W  ⟶ˢ  N[x := W]           W a source value
    (β-Λ)    (ΛX. N) [A]    ⟶ˢ  N[X := A]           N a source value
    (ξˢ-·₁)  L ⟶ˢ L′  ⟹  L · M ⟶ˢ L′ · M
    (ξˢ-·₂)  M ⟶ˢ M′  ⟹  V · M ⟶ˢ V · M′            V a source value
    (ξˢ-[])  L ⟶ˢ L′  ⟹  L [A] ⟶ˢ L′ [A]

There is no congruence under `Λ`.  `N[x := W]` is `_[_]ᵛ`, standard
substitution: under `λ` the image is shifted in the term universe, and
under `Λ` in the type universe.  `N[X := A]` is `_[_]ᵀ`.

`stepˢ` is leftmost-outermost and RETURNS the derivation.  `stepToˢ`
forgets the derivation, and `runˢ` lists the states of a run.

## 3. The statements (`ErasureProbe.agda` §5, §6)

    ErasureTyping                                              (stated)
      WfCtx Δ      Δ ∣ Γₜ ⊢ M : A
      ------------------------------------------------
      srcScope(Ξ) ∣ ⌊Γₜ⌋_Δ ⊢ˢ ⌊M⌋_Δ : ⌊A⌋_Δ

    ErasureSimulation                                          (stated)
      WfCtx Δ      Δ ∣ · ⊢ M : A      Δ ⊢ M -→ M′ ∣ δ
      ------------------------------------------------
      ⌊M⌋_Δ = ⌊M′⌋_(apply δ Δ)   or   ⌊M⌋_Δ ⟶ˢ ⌊M′⌋_(apply δ Δ)

    ErasureStutter                                             (stated)
      same premises, r the step,   Stutter r
      ------------------------------------------------
      ⌊M⌋_Δ = ⌊M′⌋_(apply δ Δ)

    ErasureStep                                                (stated)
      same premises, r the step,   ¬ Stutter r
      ------------------------------------------------
      ⌊M⌋_Δ ⟶ˢ ⌊M′⌋_(apply δ Δ)

`Stutter r` (`Stutter r = T (isStutter r)`) holds when `r` is `Wrap`,
`Merge` or `Id`, or a congruence around one.  The two statements replace
the earlier `ErasureSimulationExact`, whose `Matches` relation Jeremy
ruled out for readability (2026-09-25).  The per-step test harness reads
its prediction off the same `isStutter`.

`ruleKind` names which disjunct each rule takes, looking through the
congruences:

  * `Wrap`, `Merge` and `Id` take `same`, so the two erasures are
    equal;
  * `TyBeta`, `TyWrap` and `Beta` take `src`: exactly one source step.

    ErasureRun                                                 (stated)
      WfCtx Δ      Δ ∣ · ⊢ M : A      r : Δ ⊢ M -→* N
      ------------------------------------------------
      ⌊M⌋_Δ ⟶ˢ* ⌊N⌋_(runCtx r)

    ErasureReflection                                     (stated, ASK)
      WfCtx Δ      Δ ∣ · ⊢ M : A      ⌊M⌋_Δ ⟶ˢ N
      ------------------------------------------------
      r : Δ ⊢ M -→* M′  with  ⌊M′⌋_(runCtx r) = N

    CompiledRunErases                                          (stated)
      d : 0 ∣ · ⊢ˢ M : A      r : · ⊢ ⟦d⟧ -→* N
      ------------------------------------------------
      M ⟶ˢ* ⌊N⌋_(runCtx r)

    EraseCompileAt                                              (PROVED)
      d : n ∣ Γₜ ⊢ˢ M : A
      ------------------------------------------------
      ⌊⟦d⟧⌋_Δ = M[nameσ(Δ)]            for EVERY Δ

    EraseCompile                                                (PROVED)
      d : n ∣ Γₜ ⊢ˢ M : A
      ------------------------------------------------
      ⌊⟦d⟧⌋_(idCtx n) = M

`idCtx n` is `under` applied n times to `·`.  The proofs are
`erase-compile-at` and `erase-compile`.  They go by induction on `d`,
using `nameσ-underΛ` (the name map under `Λ` denotes `extsᵗ` of the
outer one), `substˢᵗ-cong`, `substˢᵗ-id` and `nameσ-idCtx`.  The junk
value `X` for an unnamed variable makes both statements
unconditional.

How the statements relate:

  * `ErasureRun` follows from `ErasureSimulation` and `preservation`;
  * `CompiledRunErases` follows from `EraseCompile` (at `n = 0`),
    `compile-closed` and `ErasureRun`.

### Deviations from the candidate statements

  * **Typing is over a count.**  The source judgement has a count, so
    the typing statement uses `srcScope(Ξ)`, the abstract cells.  At a
    run's ambient this count is 0: a run's store holds only concrete
    cells.
  * **Simulation assumes `Γₜ = ·`.**  The run-time `Beta` does not
    shift a value image under `λ` (`shiftᴵ (ival W A) = ival W A`), but
    the source substitution does.  The two agree because the image is
    closed.
  * **Simulation keeps `WfCtx Δ`, as preservation does.**  The
    stuttering equation for `Wrap` needs the dual to restore the name
    map, and the `TyBeta` equation needs well-scoped payloads, so the
    junk values are never read.
  * **`ErasureStutter`, `ErasureStep`, `ErasureRun`, `ErasureReflection` and
    `CompiledRunErases` are additions.**

## 4. Why the simulation should hold (the lemmas a proof needs)

Each rule has an equation, and each is what a proof would have to
establish:

  * **`TyBeta`.**  The contractum's body is erased at
    `inside(allocate(α:=R, Δ), [bind X α])`.  That context has the same
    name map as `under(X,α,Δ)`, and differs only in cell `α`: `α := R`
    against abstract.  Since `R` is `A` read through `Γ`, the lemma is

        ⌊N⌋_inside(allocate(α:=R,Δ), [bind X α])  =  ⌊N⌋_under(X,α,Δ) [X := ⌊A⌋_Δ]

  * **`TyWrap`.**  The same lemma applies, through `liftᴮ-interior`.
  * **`Beta`.**  Erasure commutes with frame-exact substitution.  The
    crossing wrapper `W ⟪ ↓Z , mkId A ⟫` of a representation-weakened
    `W` erases to `⇑⌊W⌋`, which is the source substitution's
    type-shifted image.  (`Bg`, section 10, exercises this.)
  * **`Wrap`.**  `inside(inside(Δ,Θ), dual Θ) = Δ`, from
    `dual-interior` and `inside-sound`.
  * **`Merge`.**  `inside(Δ, Θ₂ ++ Θ₁) = inside(inside(Δ,Θ₂),Θ₁)`.
    This holds by the definition of `interiorⁿ`.
  * **`Id`.**  Typing makes `U` a literal, and a literal's erasure does
    not depend on the context.
  * **The congruences.**  The sibling shift is invisible:
    `⌊↑ᴹ[new R] M⌋_(allocate(α:=R,Δ)) = ⌊M⌋_Δ`, because
    `env(Ξ, α:=R)` on an old variable is `env(Ξ)`.
  * **The evaluation order agrees.**  Run-time values erase to source
    values, so the redex `step` picks erases to the redex `stepˢ`
    picks.

## 5. Example checks (`ErasureProbe.agda` §7)

A row is `row rule predicted observed`:

  * `predicted` is `ruleKind` of the step that `Eval.step` took;
  * `observed` is `link` on the two erasures: `same` if they are equal,
    `src` if the second is `stepToˢ` of the first, and `bad`
    otherwise.

The per-step rows, checked by `refl`:

| run | rows | source steps | result |
|---|---|---|---|
| §1a `P₀` (`P-rows`) | TyBeta→ˢ Wrap= Beta→ˢ Merge= Id= | 2 | pass |
| §5a `E₀ᴮ` (`Eᴮ-rows`) | 16 steps: TyBeta, 2× TyWrap, 3× Beta →ˢ; the rest = | 6 | pass |
| §7a `A₀` (`A-rows`) | TyBeta→ˢ Wrap= Beta→ˢ Merge= Wrap= Id= Beta→ˢ Id= | 3 | pass |
| §8 `S₀`, alias `β := γ` (`S-rows`) | 15 steps | 6 | pass |
| §2c `R₀`, chained cell (`R-rows`) | 16 steps | 6 | pass |
| §10 `Bg`, Beta under Λ (`Bg-rows`) | Beta→ˢ TyBeta→ˢ Wrap= Id= Beta→ˢ Id= Id= | 3 | pass |
| §9a `Tcancel` at Δ₆ (`Tcancel-rows`) | Merge= Id= | 0 | pass |
| §9c `Tid₂` at Δ₆ (`Tid₂-rows`) | Merge= Merge= Merge= Id= | 0 | pass |

`RunChecks` checks three things for each of the 20 compiled programs
of `SourceExamples`, and for `Bg` (`P-checks` … `S-checks`,
`Bg-checks`):

  1. every row agrees and none is `bad`;
  2. the erased run with its stutters dropped IS `runˢ` of the source
     program;
  3. every erased state has the program's type under `inferˢ 0 []`.

All pass.  Check 2 contains `EraseCompile` at the first state, and it
checks `ErasureRun` and `ErasureReflection` on every run.  Check 3 is
`ErasureTyping` at each state.

Section 8's `S₀`, erased and collapsed (rendered by `showErased`
through `scripts/render_term.sh`).  Its fifteen run-time steps become
six source steps:

    ((ΛX. (λx:X. ((ΛY. (λy:(∀Z. (Z⇒Y)). (y [ℕ] · 7))) [X] · (ΛY. (λy:Y. x))))) [ℕ] · 7)
    ~~> ((λx:ℕ. ((ΛX. (λy:(∀Y. (Y⇒X)). (y [ℕ] · 7))) [ℕ] · (ΛX. (λy:X. x)))) · 7)
    ~~> ((ΛX. (λx:(∀Y. (Y⇒X)). (x [ℕ] · 7))) [ℕ] · (ΛX. (λx:X. 7)))
    ~~> ((λx:(∀X. (X⇒ℕ)). (x [ℕ] · 7)) · (ΛX. (λx:X. 7)))
    ~~> ((ΛX. (λx:X. 7)) [ℕ] · 7)
    ~~> ((λx:ℕ. 7) · 7)
    ~~> 7

The five-`Merge` tail of the notes' "A Merge run excerpt" is all
stutter.  It happens at the store `[α := ℕ , β := γ , γ := ℕ]`, where
`Y` (naming the alias `β`) erases to `ℕ`.

### A statement that is false without its premise

`ErasureSimulation` without the typing premise is FALSE.  The
counterexample is `Mbad`, checked by `Mbad-rows : rows 5 E.Δ₆ Mbad ≡
row "Id" same bad ∷ []`.  At `Δ₆ = (α := ℕ) ∣ (X ↦ α)`:

    (λx:X. x) ⟪ ↓X , id ℕ ⟫   --[Id]-->   λx:X. x

  * `Id` checks only `Simple U` and `Base A`, so it fires on this
    ill-typed term.
  * The body is erased at the interior, where `X` is unnamed, so its
    annotation dangles.
  * The contractum reads `X` as `ℕ`.
  * The two erasures are neither equal nor related by a source step.

On typed terms `U` is a literal and the problem disappears.  No
counterexample to any statement AS STATED was found.

## 6. Decision points

1. **ASK — erasure is a function of `(Δ, M)`, not of a typing
   derivation.**  The context carries everything a type variable
   needs.  Types, conversions and `ν`'s `c` are dropped, and `ν`'s `A`
   is kept.  The alternative is erasure on derivations (as `compile`
   is), which would make the junk cases impossible but the statements
   heavier.
2. **ASK — abstract cells are numbered by their abstract-only depth.**
   A cell's source index counts only the abstract cells newer than
   it, and concrete cells are transparent.  The source count is
   therefore `srcScope`, not `length (names Δ)`.  The two differ
   inside a boundary that unbinds a `Λ`'s name, and `srcScope` is the
   one that is invariant across a boundary, since `inside` keeps the
   store.
3. **ASK — junk for unnamed variables.**  An unnamed ordinary `X`
   erases to `X`, and an unallocated `α` to `α`.  This is what makes
   `EraseCompileAt` unconditional.  It is never read at `WfCtx` on a
   typed term, and `Mbad` shows what happens when it is.
4. **ASK — the source reduction.**  It is standard call-by-value with
   `β-Λ` requiring `SValue N` (the value restriction), and it lives in
   a NEW module; `Source.agda` is untouched.  Should it move to the
   top level (a `SourceReduction.agda` beside `Source.agda`) once the
   statements are accepted?
5. **ASK — simulation's shape.**  It is BfA's "equal or one step",
   with `Γₜ = ·` and `WfCtx`.  The refinement
   `ErasureStutter` / `ErasureStep` pin WHICH rules stutter (`Wrap`,
   `Merge`, `Id`).  Should the refinement replace the disjunction as the
   headline statement?
6. **ASK — the converse `ErasureReflection`.**  It is not in BfA.  It
   needs the stutter rules to terminate: a measure on boundary towers
   and on `Wrap`-able applications.  The corpus exhibits it in every
   run (check 2), but it is conjectural.  Should it be stated at all,
   or should it be replaced by the two halves "stutters terminate"
   and "a stutter-free redex erases to a source redex"?
7. **ASK — `EraseCompileAt` as the general form.**  It says: at any
   `Δ`, `⌊⟦d⟧⌋_Δ = M[nameσ Δ]`.  `EraseCompile` is its `idCtx`
   instance.  `CompiledRunErases` then needs only the closed case.

## 7. Next, if the statements are accepted

  * The `TyBeta` substitution lemma, stated in section 4, and its
    `Λ`-extended form.
  * Erasure commuting with `renᴹᴿ suc` (the sibling shift) and with
    `renᴹ² (ren² idᵗ suc)` (the crossing).
  * Erasure commuting with `substᵐ` / `_[_∶_]ᵐ`.
  * `inside` over `dual` and `liftᴮ`: the computed forms of
    `dual-interior` and `liftᴮ-interior`.
  * Conversions are erasure-identities:
    `Δ ⊢ c ∶ A ⇝ B → ⌊A⌋_Δ ≡ ⌊B⌋_Δ`.  This is the heart of
    `ErasureTyping`'s `boundary` and `⊢ν` cases.


## 7. Rulings (Jeremy, 2026-09-25)

1. Erasure stays a function of (Δ, M).
2. The source scope is `srcScope` (renamed from `countAbs`); it is only the
   index of the source typing judgement in `ErasureTyping`.
3. The junk choice is accepted.
4. `SourceReduction.agda` moved to the top level (`All.agda` imports it).
5. The exact simulation is two statements, `ErasureStutter` and
   `ErasureStep`, with no `Matches` relation.
6. `ErasureReflection` is accepted as stated.
7. `EraseCompileAt` is accepted, with `EraseCompile` as its instance.

Merge to `main` waits until the proofs are finished.

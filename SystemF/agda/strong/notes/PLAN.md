# Strong System F Representation-Variable Experiment

## Goal

This branch investigates a two-universe design for Strong System F. In the
main-branch design, ordinary System F type variables serve two roles:

1. variables bound by `∀` and used as parameters inside ordinary types; and
2. names that connect `seal`/`unseal` changes in a context morphism to the
   representation types bound by that morphism.

The experiment separates the second role into a distinct universe of
representation variables, with its own de Bruijn indices. Ordinary types and
ordinary type substitution remain as close as possible to the main-branch
design.

In the new design:

- `Ctxᵗ` contains a representation context and a list mapping live ordinary
  type-variable indices to representation-variable indices.
- A representation binding is either abstract (`abstR`) or concrete
  (`bindR R`).
- `Λ` binds both an ordinary type variable and an abstract representation
  variable.
- A context morphism's `binds` introduce representation variables.
- `lock X α` removes ordinary name `X`, recording that it named
  representation variable `α`.
- `unlock X α` restores that ordinary name.
- Locked ordinary variables are absent from the ordinary de Bruijn universe;
  surviving ordinary indices therefore compress across a lock.
- Representation payloads may contain ordinary `∀` binders and occurrences of
  the locally bound type variables inside those payloads.

The design is intentionally experimental. The objective is to determine
whether separating the two variable roles makes boundary scoping and the
preservation argument cleaner without otherwise redesigning Strong System F.

## Current status

The branch is `codex/strong-system-f-representation-vars` and was created from
the latest `main` available when the experiment began.

The following parts have been ported and typecheck:

- contexts, representation bindings, lookups, and well-formedness in
  `Ctx.agda`;
- context morphisms and relational interior/conversion contexts in
  `CtxMorph.agda`;
- conversions in `Conversion.agda`;
- terms and typing in `Terms.agda`;
- paired ordinary/representation renaming and term substitution in
  `TermSubst.agda`;
- reduction and determinism in `Reduction.agda`.

`Types.agda` and `TypeSubst.agda` remain unchanged, as intended.
`TypeCheck.agda` is new on this branch and has no main-branch counterpart, and
`Eval.agda` is rewritten from scratch rather than ported.

The reduction tests are in `notes/RepresentationReductionExamples.agda`. All
twelve closed programs reduce to first-order values:

- `( ΛX. λx:X. x ) [ℕ] · 7` reduces in six steps to `7 : ℕ`;
- the polymorphic Boolean example reduces in nine steps to `true : 𝔹`;
- the polymorphic constant example reduces in eleven steps to `3 : ℕ`;
- `( ΛX. λf:(∀Z. Z⇒Z). ΛY. f [Y] ) [ℕ] · (ΛZ. λz:Z. z)`, continued with
  `[ 𝔹 ] · true`, reduces in twenty-five steps to `true : 𝔹`;
- the same identity at `𝔹` reduces in six steps to `false : 𝔹`;
- a value applied to an argument that still reduces takes seven steps to
  `5 : ℕ`;
- the later-bound identity with a SECOND later binder, `ΛY. ΛW. f [W]`,
  continued with `[𝔹] [𝔹] · true`, reduces in thirty-seven steps to
  `true : 𝔹`;
- the identity instantiated at its own type, `[∀Z. Z⇒Z]`, continued with
  `[𝔹] · true`, reduces in seventeen steps to `true : 𝔹`;
- a payload `∀Z. Z⇒X` formed under `ΛX` reduces in twenty-three steps to
  `7 : ℕ`;
- a FUNCTION crossing a boundary and then applied reduces in eleven steps to
  `7 : ℕ`, and crossing twice, in twenty-one. These are the only runs in
  which `Peel` fires on a composite (`_⋉_`, `rewind`) frame: elsewhere the
  value that crosses is first-order, so the composites only ever carry an
  identity conversion rather than a `_↦_`;
- a function flowing through example 4's TOWER reduces in thirty-eight steps
  to `7 : ℕ`. This is the hardest case the suite puts to `Peel`: the
  identities the unwinding tower mints are at a function type, so they are
  `_↦_`s and `Peel` fires on the composites `CancelR` and `IdPush` build.

All fifteen reduction rules fire somewhere in those seven runs. The last three
exist for the four that the first four reached once or not at all:
`Drop-false` and `ξ-·-r` fired nowhere, and `TyPeelR-⟪⟫` and `IdPush` only in
the fourth — `TyPeelR-⟪⟫` exactly once. Across the suite `TyPeelR-⟪⟫` now
fires three times and `IdPush` twenty-one. What is still thin is depth: the
deepest seal tower any run builds is four, and unwinding is quadratic in that
depth, so a defect needing five boundaries would not show up.

Examples 8 and 9 instantiate at a polymorphic type, so their morphisms bind a
representation payload with a `∀` in it. They did not run when they were
written, and finding that is what produced the sixth repair below.

The fourth run is the only one that puts the boundary rules under real load,
because its argument is instantiated beneath a *later* `Λ`, so the value that
reaches `true` has crossed three boundaries and carries three seals. The shape
of its tail is a property of the rule set worth recording: with a tower of n
seals against n unseals, `CancelR` at the innermost live pair leaves two
identity layers, each of which `IdPush` walks outward one layer at a time
before the next `CancelR` can fire, so unwinding is quadratic in n. For n = 3
that is four `Peel`/`Beta` steps, two `CancelR`s inside, five `IdPush`es, a
last `CancelR`, and six `Drop-true`s.

Testing has found and repaired these errors:

1. Exterior type alignment must use `SameTyExt (numBinds Θ)` because a
   representation type crosses the morphism's representation-bind prefix.
2. `Peel` shifts the argument only in the representation-variable universe.
3. Substitution across `Λ` shifts a value only in the representation-variable
   universe before adding the binder's lock. Since that lock deletes the new
   ordinary name, the surviving ordinary indices retain their positions.
4. `TyPeelR-⟪⟫` requires the same rep-only movement for the moved value and
   its frame. For example, shifting `[lock 0 1]` in both universes incorrectly
   produced `[lock 1 2, lock 0 0]`; after the fresh lock acts, ordinary index
   `1` is out of range. The corrected frame is
   `[lock 0 2, lock 0 0]`.
5. The conversion context needs a third clause. It skips a `lock`, so the
   matching `unlock` that `rewind Θ` and `Θ₁ ⋉ Θ₂` append meets a name that
   is still live and fails `conv-unlock`'s freshness premise. Both of
   `CancelR`'s frames therefore had no conversion context whenever the
   cancelled boundary locked, which made its contractum untypeable. The
   repair is `conv-unlock-live`: an `unlock` of an already-live name is a
   no-op, which is what reading the conversion context as the union of the
   names live along the morphism already meant. See
   `notes/DECISIONS.md` (2026-09-17) and the machine-checked
   `no-old-rewind-conv` in `notes/ReUnlockWall.agda`.
6. A spelling — an ordinary de Bruijn index — that is valid in a morphism's
   conversion context is not valid in its interior, and `TyPeelR-⟪⟫` and
   `IdPush` each carried one across without re-basing. The two name maps can
   even reorder relative to each other, so the crossing is a partial lookup
   through the representation a name denotes, never arithmetic on positions.
   Both rules now NAME the interior spelling and carry a `SameTy` relating
   it to the conversion context's; determinism is `sameTy-src-unique`.
   Found by examples 8 and 9, the first programs that instantiate at a
   polymorphic type. See `notes/DECISIONS.md` (2026-09-18) and
   `notes/ForallPayloadWall.agda`. `CancelR` had the same crossing and was
   repaired the same way, preventively: no example distinguishes its two
   spellings, so that one is justified by uniformity and by the reorder
   witness rather than by a failing program. `Peel` was the fourth and
   last crossing, repaired on 2026-09-18 with `SameConv` — the same idea
   one universe up, since `Peel` carries a CONVERSION rather than a type.
   That one is justified neither by a failing program nor by uniformity
   alone: the invariant that would have excused it, `conv(dual Θ,
   int(Θ,Δ)) ≡ conv(Θ,Δ)`, is DISPROVED. `TyBeta`, `Beta` and
   `TyPeelR-Λ` were audited and are safe STRUCTURALLY — their frames either
   never lock, or the conversion context skips the only lock, so the two
   maps coincide. `Peel` is neither repaired nor clean, and the invariant
   that would have excused it — write it (P), `conv(dual Θ, int(Θ, Δ)) =
   conv(Θ, Δ)` — is FALSE: lock-free and unlock-free change lists have it,
   mixed ones need not, and `_⋉_` mixes. No REACHABLE frame violating (P)
   has been exhibited; what the disproof rules out is the proof strategy,
   not the rule. See the immediate plans. Machine-checked in
   `notes/CrossingAudit.agda`.

   The invariant that REPLACES (P) is proved. Write (Q) for: the two
   conversion contexts `Peel` straddles name the same representation
   variables — both being Δ with the unlocked names added. (P) said they
   are the same LIST; (Q) says only the same SET, and a premise on `Peel`
   absorbs the difference. (Q) holds for every well-formed morphism, with
   no restriction on the change list and no `Unique`, so it holds exactly
   where (P) fails. With it, the premise always has a witness, so
   installing it would cost no reduction. The third context those claims
   are stated over — the dual's conversion context, which typing the redex
   does NOT supply — always exists: `dual-conversion-exists`, for every
   morphism, needing only that the exterior name map is `Unique`. The one
   position obligation is a lock's, and `pigeon` discharges it: everything
   live just before the lock is either still live at the end or is the
   locked name itself, so the recorded position is still in range. The
   premise, the rule it would produce, (Q), satisfiability and existence
   are all in `notes/PeelPremise.agda`, with `peel-premises` putting them
   together; nothing is installed, and `strong.Reduction` is unchanged.
   Nothing is assumed: `Unique (names Γ)` is `WfCtx.name-fn`, and `env`
   carries a `MorphWf` whose `mw-exterior` is a `WfCtx` of the crossed
   boundary's exterior, so `peel-premises-env` takes the redex's own
   typing and returns the rule premises plus the `Unique` fact determinism
   derives via `dual-unique`. None of the five boundary rules now carries
   a `Unique` premise.

   `MorphWf`'s two OUTPUT well-formedness fields are now DERIVED and have
   been dropped from the record (`CtxMorph.agda` §3a, `interior-wf` and
   `conversion-wf`; `notes/DECISIONS.md`, 2026-09-18). All three `WfCtx`
   fields transport: `Unique` because a lock deletes and an unlock inserts
   a name its own premise says is fresh; `ValidNames` because an unlock
   carries its own `ValidRVar`; and `WfRepCtx` because neither reading
   touches the representation context, leaving only a weakening of each
   bind payload past the block's tail (`wfᴿ-rename`, the one new proof).
   The former fields survive as functions of the same names, so use sites
   are unchanged, and `morphWf?` no longer re-runs `wfCtx?` on both
   derived contexts at every boundary.

   (P) is a theorem on `main` — `convCtx-dual` in `proof/PeelDual.agda`,
   for an arbitrary well-formed change list — because there a name map is
   a fixed carrier with a lock BIT per slot, so nothing is renumbered, two
   updates commute and the dual's reversal is invisible. Here a name map is
   a sequence and deleting an entry renumbers the rest, which is precisely
   what this branch's design buys by putting variables in or out of scope
   instead of marking them. Repairing `dual` rather than `Peel` does not
   work: on a mixed frame the list that inverts the interior and the list
   that satisfies (P) differ, so no single change list serves both readings
   (`notes/CrossingAudit.agda` §6).

`TypeCheck.agda` is an executable, derivation-producing type checker for the
whole development: decidable equality on types, the two contexts a morphism
induces, context and type well-formedness, the lookup square, conversion
typing, and `infer`/`check⊢` for terms. Every checker returns a `Maybe` of
the ORDINARY derivation, so nothing is postulated and nothing is trusted; the
caller states the answer and the checker is forced at it, so a failure or a
different answer is a type error. A state's typing derivation in the example
module is now `tc`, which reads its arguments off the goal.

The checker became necessary at the fourth example. `CancelR` and `IdPush`
replace their frames by `_⋉_`/`rewind` composites, whose change lists are
concatenations, so unwinding an n-deep tower reaches frames carrying tens of
changes; a hand-written `Ξ ∣ Δ ⊢χ χ ⇒ Δ′` is one line per change and contains
nothing the change list does not already determine.

Three things about it are worth knowing before using it.

The checker has to INFER, not just check: `⊢·` and `⊢·[]` need the head's type
and a head can be a boundary. Inferring a boundary's exterior type means
inverting `shiftRep`, since `env` reads that type across the morphism's
representation-bind prefix; that is `strAt`, strengthening at a binder depth,
and it is the only place in the checker that produces an equation rather than a
derivation.

A rule premise can only be discharged by the goal-directed forms (`tc`, `tk`,
`tu`, `tf`, `tr`) when the goal fixes every input. The lookup premise of
`CancelR` and `IdPush` does not: both contracta mention the looked-up type only
under `mkId`, which the unifier cannot invert, so `A` is fixed by that premise
and by nothing else and the inferring `sq!` has to be used there. Expect the
same wherever a rule mints a conversion from a looked-up type — which includes
the preservation cases for those two rules.

When a checker fails, the hidden argument's type is `⊥` and Agda reports an
unsolved meta at the call site. That is a rejection, not an acceptance —
`--no-allow-unsolved-metas` and `make check` turn it into an error — but it
does not say why; `proj₂ (ty! Δ Γ M)` reports the type the checker did infer.

`Eval.agda` is rewritten around a step function that needs no metatheory.
`step Δ M` searches for a redex and returns the contractum *together with its
`Δ ⊢ M -→ M′` derivation*, so it is not a second rule table and there is no
`step-sound` theorem to prove — that was the objection to v1's evaluator, and
returning the derivation answers it. It takes no typing derivation, so it runs
while preservation and progress are still unported; the side conditions the
four boundary rules carry come from `TypeCheck.agda`. What it does *not* give
is the other half — that a well-typed term is a value or steps — so a
`nothing` means only that this search found no redex, and progress is still
owed.

`eval k M ⊢M` iterates `step` with fuel and calls the type checker on each
contractum, at the type the run started with. The checker is what closes the
loop: preservation is not available to retype the contractum, so the
contractum is *checked* instead. Each state's typing derivation is stored in
the returned `Trace`, and a step whose contractum the checker rejected is
recorded as `broke`; `Checked tr` is the unit record exactly when nothing
broke, so `trace-⦂` hands back the endpoint's typing and Agda discharges the
side condition by eta at a concrete run.

That is subject reduction *for that run*, checked rather than proved, and it
is the check that would have caught the `rewind` defect on its own: the
contractum of the run's eleventh step is the first state `check⊢` would have
rejected.

Because of that, the example module no longer writes out intermediate states
at all. Each of the twelve runs is one `Reaches k n ⊢M V`: with fuel `k` the
evaluator reaches `V` in exactly `n` steps, `V` is a value, and no state along
the way lost the type. `reaches-run` turns the same thing into the headline
`Δ ⊢ M -→* V` and `reaches-⦂` into the endpoint's typing, neither of which
re-runs anything; `evalTerms` hands the states back whenever a reader wants to
see one. The module went from 1266 lines to 224 at four examples, and an
example costs four lines, so the suite grew to twelve (375 lines) without
the cost becoming a problem.

Growing it cheaply took one more step, because **Agda shares nothing between
the occurrences of a term**: a statement mentioning `eval k M ⊢M` three times
runs the program three times. Measured on the 25-step example, one occurrence
costs about 0.12s, and the module was paying for four per example. `Reaches`
therefore states everything in a single equation on a `report` that walks the
trace once. Two details are load-bearing and were each found by measuring:
`report` returns a **datatype**, because a tuple has eta and comparing one
against a literal splits back into three independent projections; and it
recurses through a helper that pattern-matches, because projecting instead
would put three copies of the recursive call back. The marginal cost of an
example dropped from about 0.42s to 0.17s and the module from 2.3s to 1.8s.

The trade is real and worth stating: hand-written states were a second,
independent transcription that `step` could be checked against, and they are
gone. What replaces them is the per-state type check, which catches strictly
more than the endpoint alone and strictly less than an exact transcript. The
checks are not vacuous — a wrong endpoint, a wrong step count, too little
fuel, a value that "steps", and a `broke` trace are all rejected.

The reduction development, the checker and the test module pass Agda with
`--safe` and with unsolved metas disabled, and `make postulate-check` is
clean. The stage-1 preservation induction now passes as well, through the
parameterized interface described in immediate-plan item 1 below. `All.agda`
now reaches `proof/Canonical.agda`; its first failure is the retired
`shiftBy-base` lemma at line 126.

## Resuming on another machine

The work is pushed to `codex/strong-system-f-representation-vars`
(github.com/jsiek/AI-for-pl/pull/205). Fetch that branch; it is the one the
PR tracks.

What compiles, from `SystemF/agda/strong/`:

```
agda --safe --no-allow-unsolved-metas -v0 All.agda
```

stops at the FIRST unported dependency, `proof/Canonical.agda`, on the
retired `shiftBy-base` lemma at line 126. The core, `Reduction`, `TypeCheck`,
`Eval`, the notes modules, the stage-1 `proof/Preserve.agda`, and its honest
parameterized public wrapper all pass before that frontier.

The twelve-example suite alone is about 7.4s cold:

```
agda --safe -v0 notes/RepresentationReductionExamples.agda
```

Where the open threads are: item 1's stage-1 preservation port is done;
item 2 and the other two crossing cases remain parameters for stage 2; two
representation-only typing transports identified by stage 1 await review;
item 3's rewind transport and item 4's rule-set cleanup are done; item 6 is
progress and `Examples.agda`.

## Immediate plans

1. **STAGE 1 DONE (2026-09-18).** `proof/Preserve.agda` now uses relational
   interior and conversion readings throughout. It proves TyBeta, Beta,
   both TyPeelR clauses, Drop$/Drop-true/Drop-false, and every congruence
   case. `Nameable`, `masked`, and the computed-context interface were
   deleted from this proof rather than reproduced as shims. Peel, CancelR,
   and IdPush remain module parameters for stage 2.

   The statement now carries `WfCtx Δ`. For a concrete reason, take a
   context whose name map is `0 ∷ 0 ∷ []` and the redex

       (Λ ($ 0)) ·[ `ℕ , `ℕ ] .

   The redex types without inspecting either duplicate ordinary name, but
   TyBeta's contractum must construct a `MorphWf`, whose exterior field
   requires the name map to be unique. Typing alone therefore cannot recover
   the well-formed context required by the new relational interface.

   **REVIEW REQUIRED — NEW MAJOR LEMMA STATEMENTS.** The old development's
   `⊢crossΛ` and `⊢addLock0-cross` have no two-universe counterparts yet.
   Stage 1 exposes exactly the two required transports as parameters:

       CrossΛTyping : Set
       CrossΛTyping = ∀ {Δ W A}
         → WfCtx Δ
         → Δ ⊢ᵗ A
         → Δ ∣ [] ⊢ W ⦂ A
         → underΛ Δ ∣ [] ⊢ crossΛᴹ W A ⦂ ⇑ᵗ A

       AddLock0Typing : Set
       AddLock0Typing = ∀ {Δ W Θ s A P}
         → WfCtx ((bindR P ∷ reps Δ) ∣
                      (zero ∷ shiftNames (names Δ)))
         → Δ ∣ [] ⊢ W ⟪ Θ , `∀ s ⟫ ⦂ `∀ A
         → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
             ∣ [] ⊢
               (renᴹ² (ren² (λ X → X) (extN (numBinds Θ) suc)) W
                 ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ)
                 , `∀ (renᶨ (extᵗ suc) s) ⟫)
               ⦂ `∀ (renameᵗ (extᵗ suc) A)

   On the Beta redex `( ƛ A ∙ N) · W`, `CrossΛTyping` types each
   substituted image when it crosses a `Λ`. On the nested TyPeelR redex,
   `AddLock0Typing` types the moved inner boundary after the fresh lock and
   paired ordinary/representation renaming. No proofs of these two new
   statements are attempted in stage 1.
2. Preservation for `Peel`. The RULE repair is INSTALLED (2026-09-18):
   `Peel` names the dual's spelling `s′` and carries
   `SameConv Δᵈ s′ Δᶜ s`, with the morphism's two readings, the dual's
   conversion context beside it. `SameConv` lives
   in `Conversion.agda` §2b, `det` closes on `sameConv-src-unique`,
   `respell?` decides it in `TypeCheck.agda`, `crossPremises?` builds the
   premises in `Eval.agda`, and all twelve runs pass unchanged — same step
   counts, same endpoints — at about the same cost as before.

   The argument that it costs no reduction is in `notes/PeelPremise.agda`
   and is complete: (Q) — the two contexts name the same representation
   variables — is proved for every morphism (§5); a well-typed conversion
   always has a reading to transport (§6); the dual's conversion context
   always exists, the position obligation being discharged by a pigeonhole
   argument (§7); and `peel-premises-env` assembles all of it from the
   `MorphWf` that `env` already stores (§8). `det` now takes that typing
   derivation and obtains the dual context's uniqueness with the core
   `dual-unique`, so the rule does not carry it.

   What is left for this item is the PRESERVATION case. It is the `peel`
   parameter of `proof.Preserve.Impl`; CancelR and IdPush are likewise kept
   as `cancel` and `idpush` parameters for their stage-2 downstream ports.

3. **DONE (2026-09-18).** The two rewind invariants are now relational
   transport lemmas in `CtxMorph.agda` §3a:

       rewind-interior : ∀ {Θ : CtxMorph}
         → Γ ⊢ⁱ Θ ⇒ Γᵢ
         → Γ ⊢ⁱ rewind Θ ⇒ extendReps (binds Θ) Γ

       rewind-conversion : ∀ {Θ : CtxMorph}
         → Γ ⊢ⁱ Θ ⇒ Γᵢ
         → Γ ⊢ᶜ Θ ⇒ Γᶜ
         → Γ ⊢ᶜ rewind Θ ⇒ Γᶜ

   Both take the original interior reading; the second also takes the
   original conversion reading. No `WfCtx`, bind-well-formedness or
   `MorphWf` hypothesis is needed. The interior reading is genuinely
   necessary for the second lemma because the raw conversion relation
   permits a `conv-lock` whose name is absent; it proves that every inverse
   unlock corresponds to a name the original change run could actually
   lock. `conv-unlock-live` then makes that inverse unlock a no-op.

   These are exactly the facts the outer `rewind Θ₂` frame in both
   `CancelR` and `IdPush` consumes. Their inner `Θ₁ ⋉ Θ₂` frame already
   comes with the required conversion reading as an explicit rule premise,
   so no extra composite form is needed.
4. **DONE (2026-09-18).** Give `det` a TYPING-DERIVATION premise, and drop
   the `Unique` premises from the rules that carried them.

       det : ∀ {Δ Γ M M₁ M₂ A} → Δ ∣ Γ ⊢ M ⦂ A
         → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

   All eight `Unique` arguments came out: one each from `Peel` and
   `TyPeelR-Λ`, and two each from `TyPeelR-⟪⟫`, `CancelR` and `IdPush`.
   The `SameTy`/`SameConv` premises and every interior/conversion-context
   reading stayed: those are what pin each contractum's spelling.

   `det` now inverts the redex typing to the boundary's `env`. For
   `TyPeelR-⟪⟫` it reads the induced contexts' `name-fn` fields through
   `mw-interior-wf` and `mw-conversion-wf`, then uses `unique-underΛ`.
   `CancelR` and `IdPush` read the outer conversion context the same way
   and obtain the merged context's uniqueness by transporting the
   exterior `name-fn` through its conversion reading. `Peel` uses
   `dual-unique`, moved from `notes/PeelPremise.agda` into
   `CtxMorph.agda` §3a beside the new lifted `interior-unique` and
   `conversion-unique` lemmas. The ξ cases invert their source typing and
   pass the corresponding subterm derivation to the recursive call.

   Determinism is consequently about well-typed terms. `Eval.agda` no
   longer imports or runs `unique?`; its premise gatherers build only the
   context readings, lookup/re-spelling evidence and conversion typings
   the reduction rules retain. The twelve `Reaches` statements remain
   unchanged.
5. Re-audit every rule that crosses a `Λ` or a morphism bind prefix. At each
   crossing, state separately how ordinary indices and representation indices
   move, AND in which of the two contexts each spelling is read — that last
   question is what the 2026-09-18 defect turns on.
6. Port progress and the remaining modules imported by `All.agda`, deleting
   obsolete masking/nameability compatibility machinery rather than adding
   shims. Progress is the half `Eval.agda`'s `step` deliberately does not
   claim, and the twelve `Reaches` checks are the evidence for what it will
   have to prove: `step` finds a redex at every non-value state of all
   twelve runs.
   `Examples.agda` is the big one, and it is the same transcription problem
   the reduction traces had: port it onto `TypeCheck.agda` rather than
   rewriting its boundary typings by hand.
7. Run `agda --no-allow-unsolved-metas -v0 All.agda` from
   `SystemF/agda/strong/`, then update the design notes with the final
   invariants and proof lessons.

This draft branch should remain experimental until the preservation proof
succeeds. The fourth trace is done, and it shows that determinism plus the
first three examples were not enough evidence: the rule set was wrong at
exactly the configuration none of them reached.

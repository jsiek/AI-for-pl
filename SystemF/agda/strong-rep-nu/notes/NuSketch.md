# strong-rep-nu — design sketch (2026-09-24)

Status: DECIDED 2026-09-24 (see "Decisions" at the end); being
implemented.  The proposal text below is kept as the record.

## The idea

GTPLC has a term `ν A · L •⟨ c ⟩` (GTPLC/Terms.agda, `⊢ν`): evaluate
`L` to a `∀`-value, allocate a fresh seal `α := A`, instantiate `L` at
`α`, and coerce the result with `c`, which the compiler wrote.
strong-rep-nu borrows the shape, with a strong-rep-store **Conversion**
in place of the coercion:

    ν A · L ⟨ c ⟩

System F elaborates into it, and type application is the only source
of `ν`:

    ⟦ L [A] ⟧  =  ν A · ⟦L⟧ ⟨ reveal 0 C ⟩        where  L : ∀X.C

So the conversion `reveal 0 C` that `TyBeta` mints AT RUN TIME today
(`TyBeta`'s contractum `N ⟪ inst [] , reveal 0 B ⟫`) is written by
the compiler instead, and the `·[ B , A ]` annotation `B` disappears
from the run-time term: `ν` needs only `A` (to allocate) and `c`.

## Rule 1: `Nu-Λ` — `TyBeta` with the reveal moved to compile time

    (TyBeta, today)  Δ ⊢ (ΛX.V) [B,A]      -→ V ⟪ [bind X α] , reveal X B ⟫ ∣ new R
    (Nu-Λ)           Δ ⊢ ν A · (ΛX.V) ⟨c⟩  -→ V ⟪ [bind X α] , c ⟫          ∣ new R
                     where Δ ⊢ᶜ A ~ R

The contractum is the same term; only the origin of the conversion
changes.  Example §1a, `(ΛX. λx:X. x) [ℕ] · 7`, compiles to

    ν ℕ · (ΛX. λx:X. x) ⟨ seal X ↦ unseal X ⟩ · 7

and runs exactly as today after the first step (rendered from the fork
with `scripts/render_term.sh 'showRun 0 5 P₀-⊢'`; only step 1's label
and redex change):

    Ξ = []         ν ℕ · (ΛX. λx:X. x) ⟨ seal X ↦ unseal X ⟩ · 7
      --[Nu-Λ]-->
    Ξ = [α := ℕ]   ((λx:X. x) ⟪ ↥X , (seal X ↦ unseal X) ⟫) · 7
      --[Peel]-->
    Ξ = [α := ℕ]   ((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↥X , unseal X ⟫
      --[Beta]-->  --[CancelR]-->  --[Drop$]-->
    Ξ = [α := ℕ]   7

Typing sketch (the `boundary` pattern, at the context `Nu-Λ` leaves):

    ⊢ν : Δ ⊢ᵗ A → Δ ∣ Γ ⊢ L ⦂ ∀C
       → Δ ⊢ᶜ A ~ R
       → Δᶜ ⊢ c ∶ C ⇝ Cₑ          -- Δᶜ = conversion context of [bind 0 0]
       → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ    -- B's names read at `allocate R Δ`
       → Δ ∣ Γ ⊢ ν A · L ⟨ c ⟩ ⦂ B

(`c`'s target is compared to `B` by representation, as `boundary` does, so
the compiler is free to spell `c` = `reveal 0 C`.)

## Rule 2: `ν` over a boundary — the open question

The second canonical `∀`-value is `V ⟪ Θ , ∀ s ⟫`.  Today's
`TyPeelR-Λ` FUSES the crossed conversion with the reveal at run time:
its contractum is `N ⟪ inst Θ , instReveal 0 s ⟫`.  With a
compile-time `c`, there is nothing to fuse with.  Example §1b:

    ((ΛX. λf:(∀Y. Y⇒𝔹). f[X]) [𝔹] · (ΛY. λx:Y. true)) · false

compiles (both `ν`s written by the compiler) to

    ((ν 𝔹 · (ΛX. λf:(∀Y. Y⇒𝔹). ν X · f ⟨ seal Y ↦ id 𝔹 ⟩)
          ⟨ (∀Y. id Y ↦ id 𝔹) ↦ (seal X ↦ id 𝔹) ⟩)
       · (ΛY. λx:Y. true)) · false

and after `Nu-Λ`, `Peel`, `Beta` (same as today) reaches

    Ξ = [α := 𝔹]
    (ν X · ((ΛY. λx:Y. true) ⟪ ↓X , ∀Y. (id Y ↦ id 𝔹) ⟫) ⟨ seal Y ↦ id 𝔹 ⟩)
        ⟪ ↥X , (seal X ↦ id 𝔹) ⟫ · false

Today's run at the same point (`TyPeelR-Λ`, rendered):

    --[TyPeelR-Λ]-->  Ξ = [α := β , β := 𝔹]
    ((λx:X. true) ⟪ ↥X , ↓Y , (seal X ↦ id 𝔹) ⟫) ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫ · false

Candidate **N1 — stack, don't fuse.**  Both conversions move verbatim;
the step writes no conversion at all:

    (Nu-⟪Λ⟫)  Δ ⊢ ν A · ((ΛY.V) ⟪ Θ , ∀Y.s ⟫) ⟨c⟩
                  -→ (V ⟪ inst Θ , s ⟫) ⟪ [bind Y α] , c ⟫ ∣ new R

    --[Nu-⟪Λ⟫]-->  Ξ = [α := β , β := 𝔹]
    (((λx:Y. true) ⟪ ↥Y , ↓X , (id Y ↦ id 𝔹) ⟫) ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫)
        ⟪ ↥X , (seal X ↦ id 𝔹) ⟫ · false

  One more (transparent) layer than today; `Peel` passes through it
  (`false ⟪ … , id Y ⟫` — an inert id-at-a-variable) and the run
  stays finite.  (Inner-boundary spelling is hand-derived — the
  `↓X` needs checking against `inst`.)

Candidate **N2 — fuse at run time** with a conversion composition
`s ⨟ c`.  Keeps today's layer count but needs a `_⨟_` on conversions
(is `seal X ⨟ unseal X` a conversion? today it is a `CancelR` redex),
i.e. it puts back the run-time work Rule 1 removed.

The NESTED case `(W ⟪ Θ′ , ∀s′ ⟫) ⟪ Θ , ∀s ⟫` (today's `TyPeelR-⟪⟫`,
which pushes a type application `[Bᵢ′ , 0]` inward and so re-allocates
an ALIAS cell `β := α` on the next step) is the real design point:

* **(a)** keep re-allocating: the pushed-in instantiation becomes a
  `ν (` 0) · … ⟨ s ⟩` — but then `ν`'s conversion is no longer a
  compile-time `reveal`, it is the crossed `s`, and the inner `ν`
  needs its own reveal of the inner body at run time;
* **(b)** allocate ONCE, GTPLC-style: `ν` allocates and produces
  `(V •) ⟪ [bind 0 α] , c ⟫`, and a separate, NON-allocating
  instantiation-at-the-fresh-cell form `V •` peels the stack.  Then
  exactly one rule (`ν`) allocates, which is the "allocate
  differently" half of the brief.  Cost: `(Λ N) •` re-reads `N`'s
  abstract rep 0 as the existing cell α — a non-injective
  representation renaming, which `RepWk`/`⊢renᴿ` do not cover today.

## Questions for Jeremy

1. Elaboration: does the compiler write `c = reveal 0 C` exactly, or
   should `⊢ν` accept any `c` whose types line up (as sketched)?
2. Rule 2: N1 (stack) or N2 (fuse)?
3. Nested case: (a) alias re-allocation per layer, or (b) one
   allocation per `ν` with a non-allocating `•`?
4. Does the source `·[_,_]` term go away entirely (ν is the only
   instantiation form), or stay as the elaboration's input language?

## Decisions (Jeremy, 2026-09-24)

1. The compiler writes `c = reveal 0 C`, but `⊢ν` accepts ANY `c` whose
   types line up, as GTPLC's `⊢ν` does.  (This is what lets `Nu-⟪⟫`
   push a `ν` whose conversion is a run-time reveal of the inner body.)
2. N1 — stack, don't fuse.
3. (a) — the nested case re-allocates an alias cell per layer.
4. `·[_,_]` leaves the run-time language.  A SEPARATE source language,
   plain System F with the standard `L [ A ]` (`Source.agda`), is
   compiled into it (`Compile.agda`).

## As implemented

    ν_·_⟨_⟩ : Ty → Term → Conv → Term

    ⊢ν : Δ ⊢ᵗ A → Δ ⊢ᶜ A ~ R → Δ ∣ Γ ⊢ L ⦂ ∀C
       → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
       → Δᶜ ⊢ c ∶ C ⇝ Cₑ → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ → Δ ⊢ᵗ B
       → Δ ∣ Γ ⊢ ν A · L ⟨ c ⟩ ⦂ B

    (Nu-Λ)    ν A · (Λ N) ⟨c⟩
                -→ N ⟪ inst [] , c ⟫                                ∣ new R
    (Nu-⟪Λ⟫)  ν A · ((Λ N) ⟪ Θ , ∀ s ⟫) ⟨c⟩
                -→ (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫              ∣ new R
    (Nu-⟪⟫)   ν A · ((W ⟪ Θ′ , ∀ s′ ⟫) ⟪ Θ , ∀ s ⟫) ⟨c⟩
                -→ ((ν 0 · (↑W ⟪ ↑Θ′ ++ [unbind 0 0] , ∀ s″ ⟫)
                        ⟨ reveal 0 (⇑Bᵢ′) ⟩)
                      ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫              ∣ new R
    (ξ-ν)     L -→ L′ ∣ δ  gives  ν A · L ⟨c⟩ -→ ν A · L′ ⟨c⟩ ∣ δ

`liftᴮ Θ` is `Θ` shifted one step in both universes, and
`inst Θ = liftᴮ Θ ++ [bind 0 0]`: the middle layer of a stacked
contractum, read at the outer layer's interior, has exactly the interior
that `inst Θ` had before.  `Nu-⟪⟫` is where the one remaining run-time
reveal is minted: the old `TyPeelR-⟪⟫` pushed in `·[⇑Bᵢ′, 0]`, which
the next `TyBeta` turned into `reveal 0 (⇑Bᵢ′)`.

Source/compile (`Source.agda`, `Compile.agda`): `n ∣ Γ ⊢ˢ M ⦂ A` over
a COUNT `n` of type variables, with the same value restriction on `Λ`
as the run-time `⊢Λ`; `compile` is defined on derivations
(`⟦⊢ˢ[] d _⟧ = ν A · ⟦d⟧ ⟨ reveal 0 C ⟩`).

# SystemF/agda/intrinsic-subst

A new version of `SystemF/agda/intrinsic` (intrinsically typed System F with
naturals and booleans). Its renaming and substitution come from the kit
library in the top-level `Subst/` directory (`Subst/Kit.agda` for types,
`Subst/Poly.agda` for terms).

**No function extensionality and no postulates.** The old development
postulates `extensionality` (used for `exts-id-id` and `extsᵗ-idᵗ-id`) and
`substᵀ-shiftSubst-renameᵀ-core-∙`. Here every equation between
substitutions is pointwise, and all substitution lemmas are proved.

## Files

- `Types.agda`: `TyCtx`, `TyVar`, `Type`, and the one traversal of types
  `travᵗ`. `renameᵗ`, `substᵗ`, `extsᵗ`, `⇑ᵗ`, and `_[_]ᵗ` come from the library.
- `Ctx.agda`: `Ctx Δ`, `Γ ∋ A`, and `⇑ᶜ`, plus the library's maps of term
  variables along a map of types (`TyRen`, `extρ`, `⇑ρ`, `instᵛ`).
- `Terms.agda`: the terms `Δ ∣ Γ ⊢ A` and their two traversals:
  - `travᵀ` renames or substitutes type variables, giving `renᵀ`, `subᵀ`, `⇑ᵀ`,
    and `N [ B ]ᵀ`;
  - `trav` renames or substitutes term variables, giving `ren`, `sub`, `⇑`, and
    `N [ M ]`.
- `Reduction.agda`: values, reduction, progress, and multi-step reduction.
- `Examples.agda`: reduction traces ending in constants. One goes through the
  cast in the `_∙_` clause of `travᵀ`.
- `Parametricity.agda`: the binary logical relation (`Rel`, `RelSub`, `𝒱`,
  `ℰ`, `RelEnv`, `𝒢`, `LogicalRel`) and the hypothesis `CompatInst`.
- `FreeTheorems.agda`: `neg`, `flip`, and `R`, used in the free theorems.
- `MetaTheory.agda`: the public statements `fundamental`, `terminate`,
  `free-theorem-id`, and `free-theorem-rep`, each under the hypothesis
  `CompatInst`.
- `proof/Parametricity.agda`: the renaming lemma for the logical relation
  (`𝒱-ren⇒`, `𝒱-ren⇐`), the compatibility lemmas for every typing rule
  except type application, the fundamental theorem, and termination.
- `proof/FreeTheorems.agda`: the two free theorems.
- `proof/TypeSubst.agda`: the two inductions on types (`fuseᵗ`, `sub-idᵗ`).
  The library derives the rest (module `TL`).
- `proof/TermSubst.agda`: the five inductions on terms (`fuseᵀ`, `idᵀ`,
  `commute`, `fuse`, `sub-id`). The library derives the rest: `sub-sub`,
  `ren-sub`, `sub-ren`, `sub-⇑ᵀ`, `exts-[]`, `sub-[]`, `travᵀ-[]`, `⇑ᵀ-[]ᵀ`, …
- `All.agda`: aggregate driver.

## Differences from `intrinsic`

- The typing judgment is written `Δ ∣ Γ ⊢ A`. The old files write `Δ ; Γ ⊢ A`
  with U+037E GREEK QUESTION MARK, because Agda does not allow the ASCII `;`
  in names.
- A type-level map acts on a term together with a map of its term variables
  (`TyRen 𝒯 θ Γ Γ'`) rather than to the fixed context `substCtx σ Γ`. This
  keeps the context casts out of the `Λ` case. The canonical versions are
  `renᵀ` and `subᵀ`, which target `mapᶜ 𝒯 θ Γ`.
- Laws that change the type of a term (`fuseᵀ`, `idᵀ`, `⇑ᵀ-[]ᵀ`) are stated
  with heterogeneous equality `_≅_`. Laws of term-variable substitution are
  homogeneous.
- Parametricity. `intrinsic` uses `--cumulativity --omega-in-omega`, an unsafe
  and inconsistent flag, and still postulates `compat-∙`, `Λ-body-coherence`,
  and both free theorems. Here everything is checked with `--safe`.
  `Λ-body-coherence` is now proved: the type-abstraction case is `compat-Λ`.
  The two free theorems are proved too. The one remaining assumption is the
  type-application case, `CompatInst`, which is a module parameter of
  `MetaTheory`, not a postulate.

  Why it can't be proved: take `M = Λα. λ(x:α). x` instantiated at
  `B = ∀β. β→β`. The case for `M ∙ B` must instantiate α's relation with
  `𝒱 B`, and `𝒱 B` itself quantifies over all relations, so it lives one
  universe above the relations that `∀` quantifies over. More generally, the
  fundamental theorem implies termination of System F, and that is beyond
  predicative (`--safe`) Agda.
- Environments: a `RelEnv` carries its own map of term variables along the
  type substitution (`r₁ : TyRen subKᵗ ρ₁ Γ Γ₁`), not the fixed context
  `substCtx ρ₁ Γ`. This lets the `Λ` case pick the instantiated context freely
  (`ΛEnv`), so it needs no context casts. Closed terms use the empty
  substitution and environment (`ρ∅`, `e∅`), and closing a closed term changes
  nothing (`close∅-≅`).

## Checking

    make check     # from this directory: agda --safe on All.agda, plus
                   # the postulate/hole grep

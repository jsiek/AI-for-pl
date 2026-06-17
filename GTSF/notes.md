--------------------------------------------------------------------------------
Strict Coercions

The cambridge22 notes use store-domain side conditions to keep the
``tag`` and ``seal`` views of a type variable from being mixed in the
same coercion/imprecision derivation.  The intended invariant is
roughly:

* If a variable ``α`` is represented by a store seal, then coercions
  should use ``seal_α`` and ``-seal_α``.
* If a variable ``α`` is represented as an ordinary ground tag, then
  coercions should use ``tag_α`` and ``-tag_α``.
* The same variable should not be usable as both an ordinary ground tag
  and a store seal in one derivation.

The notes express this by side conditions such as:

* ``id_α`` is not allowed when ``α`` is in the store.
* ``tag_α`` and ``-tag_α`` are not allowed when ``α`` is in the store.
* ``seal_α`` and ``-seal_α`` require ``α`` to be in the store.
* In ``ν α. c[α]``, all occurrences of the bound ``α`` should be
  tag-like, written ``c[tag_α]``.
* In ``-ν α. c[α]``, all occurrences of the bound ``α`` should be
  seal-like, written ``c[seal_α]``.

Those side conditions are natural for a static description of coercions,
but they are awkward for preservation because preservation repeatedly
opens a binder into a store that has just gained the opened variable.
The problem is not that a bad coercion can be typed in isolation.  The
problem is that a coercion that is well-typed before a reduction can be
rejected after the reduction, even though the reduction is exactly the
one that creates the store entry needed by the operational semantics.

This note uses named type variables informally.  The Agda development
uses de Bruijn indices: a named binder ``β`` below corresponds to index
``zero`` in the mechanization, ``Δ, β`` corresponds to ``suc Δ``, and
``Σ↑`` corresponds to the lifted store ``⟰ᵗ Σ``.

The nominal notation below writes binders explicitly in each syntactic
form that binds a type variable:

    ∀X. c[X]
    gen β. A c[β]
    inst β. B c[β]

These correspond to the Agda constructors ``∀``, ``gen A c``, and
``inst B c``; the displayed variable marks the scope that Agda handles
with ``extᵗ`` in renaming and substitution.

Concrete preservation problem: ``gen``
-------------------------------------

Consider the body coercion

    c[β] = (＇ β) ？

under a ``gen`` coercion:

    gen β. ★ c[β]

In the body of ``gen``, the newly bound variable ``β`` is intended to be
tag-like.  The body coercion has shape

    Δ, β ∣ Σ↑ ⊢ (＇ β) ？ ∶ ★ =⇒ β

because ``β`` is bound by the coercion and is not a store seal in
``Σ↑``.  Thus

    Δ ∣ Σ ⊢ gen β. ★ c[β] ∶ ★ =⇒ ∀β.β

The Nu reduction rule for ``gen`` is

    V ⟨ gen β. C c[β] ⟩ • α  —→  V ⟨ c[α] ⟩

so the example reduces to

    V ⟨ gen β. ★ c[β] ⟩ • α
      —→
    V ⟨ c[α] ⟩
      =
    V ⟨ (＇ α) ？ ⟩

If ``α`` is already in the store, the cambridge22 side condition for
``tag_α``/``-tag_α`` rejects the reduct coercion ``(＇ α) ？``.  But the
source term can be well typed: the ``gen`` body only mentioned the
bound variable ``β`` in its tag-like role.  Preservation would need
to show that opening a tag-like bound variable at an arbitrary in-scope
type variable preserves coercion typing.  A store-domain side condition
cannot prove that, because it asks the wrong question after opening:
it asks whether the chosen ``α`` is in the store, while the reduction is
tracking whether the occurrence came from the tag-like ``gen`` binder.

The same issue appears in the older store-allocating reduction rule:

    Σ ∣ V ⟨ gen β. C c[β] ⟩ ⦂∀ B • A
      —→
    (α , A) ∷ Σ ∣ V ⟨ c[α] ⟩ ⟨ reveal B[α] α A ⟩

Here ``α`` is fresh for the old store ``Σ``, but the reduct is typed in
the new store ``(α , A) ∷ Σ``.  Thus a reduct coercion such as
``(＇ α) ？`` is again rejected by the side condition precisely because
preservation has moved to the store that now contains ``α``.

Concrete preservation problem: ``inst``
--------------------------------------

Now consider the opposite binder.  In an ``inst`` coercion, the freshly
bound variable is seal-like, because type instantiation creates an
abstract runtime representation.  For example:

    d[β] = seal ★ β ︔ unseal β ★

    inst β. ★ d[β]

The body coercion is typed under a store extended with the new
``β`` seal:

    instᵈ normalᵈ ∣ Δ, β ∣ (β , ★) ∷ Σ↑
      ⊢ seal ★ β ︔ unseal β ★ ∶ ★ =⇒ ★

The Nu reduction rule is

    V ⟨ inst β. B c[β] ⟩
      —→
    ν β := ★. (((V↑) • β) ⟨ c[β] ⟩)

Inside the body of ``ν β := ★``, the term typing rule supplies the
matching store entry ``(β , ★)``.  So the reduct is operationally
sensible: the body coercion can use ``seal ★ β`` and ``unseal β ★``
because the ``ν`` binder has created the seal.

The preservation proof still has to move between two views of the same
body coercion:

* As the body of ``inst``, it is checked under the special seal-like
  binder discipline.
* As a term cast inside the body of ``ν``, the term typing rule expects
  the ordinary coercion typing judgment.

With global side conditions, this conversion is not a structural lemma.
One has to re-check all the store-domain side conditions after moving
the coercion under ``ν``.  In larger bodies, that re-checking is where
the proof gets stuck, because the side conditions do not remember which
occurrences came from the ``inst`` binder and which were ordinary store
variables.

Why the mode context solves preservation
----------------------------------------

The mode-based design replaces the global store-domain side condition
with a local mode context:

    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

where ``μ`` maps type variables to one of three modes:

* ``normal``: ordinary coercion typing.  Endpoint occurrences and
  tags/untags are allowed; seals/unseals are allowed when the ordinary
  store membership premise holds.
* ``tag-to-seal``: the variable is currently the tag-like variable bound
  by ``gen``.  Tags/untags of the variable are allowed; seals/unseals
  and arbitrary endpoint occurrences are rejected.
* ``seal-to-tag``: the variable is currently the seal-like variable
  bound by ``inst``.  Seals/unseals of the variable are allowed;
  tags/untags and arbitrary endpoint occurrences are rejected.

The public judgment remains the old one:

    Δ ∣ Σ ⊢ c ∶ A =⇒ B

but it is an abbreviation for normal mode:

    normalᵈ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

The binder rules change the mode context instead of relying on a
store-domain side condition:

    extᵈ μ ∣ Δ, X ∣ Σ↑ ⊢ c[X] ∶ A[X] =⇒ B[X]
    ------------------------------------------------
    μ ∣ Δ ∣ Σ ⊢ ∀X. c[X] ∶ ∀X.A[X] =⇒ ∀X.B[X]

    genᵈ μ ∣ Δ, β ∣ Σ↑ ⊢ c[β] ∶ A↑ =⇒ B[β]
    ------------------------------------------------
    μ ∣ Δ ∣ Σ ⊢ gen β. A c[β] ∶ A =⇒ ∀β.B[β]

    instᵈ μ ∣ Δ, β ∣ (β , ★) ∷ Σ↑
      ⊢ c[β] ∶ A[β] =⇒ B↑
    ------------------------------------------------
    μ ∣ Δ ∣ Σ ⊢ inst β. B c[β] ∶ ∀β.A[β] =⇒ B

Here ``A↑`` and ``B↑`` mean the outer type has been weakened under the
new binder.

The side checks are now mode checks:

* ``tyAllowed μ A`` says that endpoint type ``A`` does not mention a
  currently special variable in an ordinary way.
* ``tagTyAllowed μ G`` permits a variable ground type only in ``normal``
  or ``tag-to-seal`` mode.
* ``sealTyAllowed μ α`` permits ``seal``/``unseal`` only in ``normal``
  or ``seal-to-tag`` mode.

This is enough for preservation because opening and weakening now have
mode-aware lemmas.

For the ``gen`` example, preservation uses a lemma of this form:

    μ ∣ Δ, β ∣ Σ↑ ⊢ c[β] ∶ A[β] =⇒ B[β]
    ------------------------------------------------
    Δ ∣ Σ ⊢ c[α] ∶ A[α] =⇒ B[α]

The proof uses ``ModeRename-to-normal``.  Intuitively, the special
bound variable is consumed by opening; after substitution by an
ordinary in-scope variable ``α``, the resulting coercion is checked in
normal mode.  We do not ask whether ``α`` is in the store.  We ask
whether the occurrence was legal in the binder mode before opening.
Thus the reduct

    V ⟨ (＇ α) ？ ⟩

can be typed even when ``α`` is in ``Σ``, because the occurrence came
from a tag-like ``gen`` binder.

For the ``inst`` example, preservation uses mode relaxation:

    ModeIncl μ normalᵈ

Every restricted mode can be relaxed to normal mode after the
restricted body has already been checked.  Thus, inside the body of
``ν β := ★``, the coercion ``c`` from ``inst`` can be used by the ordinary
term cast rule:

    ⊢⟨⟩ (coercion-mode-relax modeIncl-normal c⊢) app-src⊢

This does not weaken the design unsafely.  The restriction was enforced
when ``c`` was checked under ``instᵈ``.  Relaxation only says that a
coercion that has passed the stricter local discipline is also usable
at an ordinary cast site once the surrounding term rule has provided
the necessary store entry.

How the mode context enables endpoint flipping
----------------------------------------------

The endpoint-flipping theorem says that if a coercion is well typed
from ``A`` to ``B``, then its dual is well typed from ``B`` to ``A``:

    StoreWfAt Δ Σ →
    Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    Δ ∣ Σ ⊢ - c ∶ B =⇒ A

The theorem is false for raw coercions.  For example, the raw coercion

    gen β. ★ (seal (‵ `ℕ) β)

is not well typed, and indeed duality is not an involution on that raw
term.  The typing discipline is what makes duality meaningful.

The hard cases are exactly the bound ``gen``/``inst`` cases.  Duality
swaps the representation of the bound variable:

* Under ``gen``, occurrences of the bound variable are tag-like.  When
  dualized, ``tag_β`` becomes a seal of the same bound variable, so the
  target proof must type the dual body under ``inst`` with a fresh
  ``(β , ★)`` store entry.
* Under ``inst``, occurrences of the bound variable are seal-like.  When
  dualized, ``seal_β`` becomes a tag of the same bound variable, so the
  target proof must type the dual body under ``gen``.

For the concrete typed coercion

    inst β. ★ (seal ★ β ︔ unseal β ★)
      : ∀β.★ =⇒ ★

the dual is

    gen β. ★ (((＇ β) ？) ︔ ((＇ β) !))
      : ★ =⇒ ∀β.★

The source body is legal because ``β`` is in ``seal-to-tag`` mode and
the store contains ``(β , ★)``.  The dual body is legal because ``β``
is in ``tag-to-seal`` mode and tags/untags of ``β`` are
allowed there.  A store-domain-only side condition cannot see this
mode switch; it only sees whether ``β`` is in the store at a
particular point.

The proof uses an internal relation ``DualStore μ Σ ν Π`` between the
source mode/store and target mode/store.  Its important clauses are:

* If ``μ α = tag-to-seal``, then the target store ``Π`` contains
  ``(α , ★)``.  This is exactly what is needed when a tag becomes a
  seal in the dual.
* If ``μ α = seal-to-tag``, then the source store ``Σ`` contains
  ``(α , ★)``.  This is exactly what is needed when a seal becomes a
  tag in the dual.
* If ``μ α = normal``, ordinary store membership is carried from the
  source store to the target store.

The binder cases extend this relation in the way duality requires:

    genᵈ μ over Σ↑
      flips to
    instᵈ ν over (β , ★) ∷ Π↑

    instᵈ μ over (β , ★) ∷ Σ↑
      flips to
    genᵈ ν over Π↑

Thus the proof does not need to guess after the fact whether a variable
should be a tag or a seal.  The mode context records that information
at the binder, and ``DualStore`` records the store entry that will be
needed after the flip.  This is the reason endpoint flipping can be
proved structurally over the coercion typing derivation.

Suggested changes to the cambridge22 coercion typing presentation
----------------------------------------------------------------

The cambridge22 notes should keep the existing coercion typing shape:

    c : A =⇒_Σ B

The only suggested presentation change is to refine this judgment with
a mode context when stating the side conditions:

    μ ⊢ c : A =⇒_Σ B

The store ``Σ`` stays as the subscript on the arrow, and no separate
type-variable context needs to be introduced.  The unqualified judgment
can be read as the normal-mode instance, where every free type variable
that is not specially bound by a coercion rule is ordinary:

    c : A =⇒_Σ B
      means
    normal ⊢ c : A =⇒_Σ B

The mode context only records how variables bound by coercion structure
may be used inside the body coercion:

    μ, X : normal   -- the variable bound by ∀X. c[X]
    μ, α : tag      -- α may occur as tag_α or -tag_α
    μ, α : seal     -- α may occur as seal_α or -seal_α

Equivalently, the existing informal annotations
``c[tag_α]`` and ``c[seal_α]`` become tracked side conditions rather
than comments on the binding forms ``ν α. c[tag_α]`` and
``-ν α. c[seal_α]``.  In ``c[tag_α]``, the bound ``α`` may occur as
``tag_α`` or ``-tag_α``, but not as an ordinary type endpoint and not
as a seal.  In ``c[seal_α]``, the bound ``α`` may occur as
``seal_α`` or ``-seal_α``, but not as an ordinary type endpoint and not
as a tag.

The side conditions that currently mention ``dom(Σ)`` should be
replaced by mode admissibility checks:

    TyOK_μ(A)
    TagOK_μ(G)
    SealOK_μ(α)

``TyOK_μ(A)`` says that no variable currently in tag mode or seal mode
appears as an ordinary type endpoint in ``A``.  Thus ``TyOK_μ(α)``
holds when ``α`` is normal, and fails when ``α`` is the special
variable of an enclosing ``ν α. c[tag_α]`` or ``-ν α. c[seal_α]``
annotation.

``TagOK_μ(G)`` says that ``G`` is legal in ``tag_G`` and ``-tag_G``.
For variable ground types, ``TagOK_μ(α)`` holds when ``α`` is normal or
in tag mode, and fails when ``α`` is in seal mode.

``SealOK_μ(α)`` says that ``α`` is legal in ``seal_α`` and
``-seal_α``.  It holds when ``α`` is normal or in seal mode, and fails
when ``α`` is in tag mode.

With those predicates, the rules whose side conditions change are:

    ---------------- TyOK_μ(A)
    μ ⊢ id_A : A =⇒_Σ A

    ---------------- TagOK_μ(G)
    μ ⊢ tag_G : G =⇒_Σ ★

    ------------------- TagOK_μ(G)
    μ ⊢ -tag_G^ℓ : ★ =⇒_Σ G

    ----------------- (α:=A) ∈ Σ, TyOK_μ(A), SealOK_μ(α)
    μ ⊢ seal_α : A =⇒_Σ α

    ------------------ (α:=A) ∈ Σ, TyOK_μ(A), SealOK_μ(α)
    μ ⊢ -seal_α : α =⇒_Σ A

The important difference from the current cambridge22 side conditions
is this replacement:

    ftv(A) ∩ dom(Σ) = ∅
      becomes
    TyOK_μ(A)

and

    if G = α then α ∉ dom(Σ)
      becomes
    TagOK_μ(G)

The store-membership premises for ``seal_α`` and ``-seal_α`` remain
unchanged.  In particular, the mode discipline does not try to replace
``(α:=A) ∈ Σ``; it only replaces the freshness checks that were using
``dom(Σ)`` to approximate where tags and ordinary endpoints were
allowed.

The structural rules should keep their cambridge22 conclusions and only
thread the mode context through their premises.  For example:

    μ ⊢ c : A =⇒_Σ B    μ ⊢ d : B =⇒_Π C
    ---------------------------- (if α:=A ∈ Σ and α:=B ∈ Π then A = B)
    μ ⊢ (c ; d) : A =⇒_{Σ,Π} C

    μ ⊢ c : A′ =⇒_Σ A    μ ⊢ d : B =⇒_Σ B′
    ------------------------------
    μ ⊢ (c→d) : (A→B) =⇒_Σ (A′→B′)

    μ, X : normal ⊢ c[X] : A[X] =⇒_Σ B[X]
    ------------------------------------
    μ ⊢ (∀X. c[X]) : (∀X.A[X]) =⇒_Σ (∀X.B[X])

The two ``ν`` rules are where the mode annotations matter most:

    μ, α : tag ⊢ c[tag_α] : A =⇒_Σ B[α]
    ---------------------------- α ∉ fv(A), α ∈ fv(B[α])
    μ ⊢ (ν α. c[tag_α]) : A =⇒_Σ (∀X.B[X])

    μ, α : seal ⊢ c[seal_α] : A[α] =⇒_{Σ,α:=⋆} B
    ----------------------------- α ∈ fv(A[α]), α ∉ fv(B)
    μ ⊢ (-ν α. c[seal_α]) : (∀X.A[X]) =⇒_Σ B

This keeps the cambridge22 presentation intact while making explicit
the invariant already suggested by the notation: ``ν α. c[tag_α]`` opens
the body with tag-like occurrences, while ``-ν α. c[seal_α]`` opens the
body with seal-like occurrences.  The preservation benefit is that
opening no longer depends on whether the opened variable happens to be
absent from ``dom(Σ)``; legality follows from the mode assigned by the
binder.

Open cleanup notes
------------------

Inline and remove sealTyAllowed. It's too short.

Rename dualWith to dual.

In the coercion typing relation, change the new side conditions
to be explicit parameters instead of implicit.

--------------------------------------------------------------------------------
Maximal Lower Bounds

A = ∀Y. ★ → Y → ★ → ★
B = ∀X. X → ★ → ★ → X
C = ∀X.∀Z.∀Y.X → Y → Z → X
MLB = ∀X.∀Y.X → Y → ★ → X

A = ∀X.∀Z.∀S.∀T.∀V. X → ★ → Z → ★ → S → T → ★ → V → ★ → X
B = ∀Y.∀Z.∀W.∀T.∀U. ★ → Y → Z → W → ★ → T → U → ★ → ★ → ★
C = ∀X.∀Y.∀Z.∀W.∀S.∀T.∀U.∀V.∀R. X → Y → Z → W → S → T → U → V → R → X
MLB = ?

--------------------------------------------------------------------------------

What does the compilation from the source language to the poly. blame
calculus look like?  We need to make sure it satisfies the static
gradual guarantee.

F = λf:∀X.X→X. ΛY. λy:Y. f[Y] y
  = λf:∀X.X→X. ΛY. λy:Y. να:=Y. (f[α] @+(seal_α → seal_a)) y

F⋆ =  λf:⋆→⋆. ΛY. λy:Y. f[Y] y
   =? λf:⋆→⋆. ΛY. λy:Y. να:=Y. f @-(tag_α → tag_α) @+(seal_α → seal_α)  y

   The sealing and tagging on the domain is necessary to get from Y to ⋆,
   but what about the codomain? 
   Also, would we have to use a kind of bidirectional typing to have
   the type of y influence the compilation of the type application.

id : ∀X.X→X = ΛX. λx:X. x
id⋆ : ⋆ → ⋆ = λx:⋆. x

F id [ℕ] 42 -->* 42
F id⋆ [ℕ] 42 -->* 42

# ariadne: one runner and one checker for every target

The tool behind Ariadne's VST proofs (EVALUATION.md §5).  A *target* is
a C program or library unit with frozen specs; a *run* has an agent
prove it; the *check* decides, by the tools alone, what is proved.

```
python3 Ariadne/ariadne/cli.py list                        # the 20 targets
python3 Ariadne/ariadne/cli.py ready FILE.c                # VST readiness, free
python3 Ariadne/ariadne/cli.py check picol Ariadne/bench/picol/proofs
python3 Ariadne/ariadne/cli.py run picol --usd 50 [--from RUN] [--note F]
python3 Ariadne/ariadne/check_all.py                       # every kept proof
```

## Targets (`targets.py`)

One `targets.toml` per family; for example picol's
(`../bench/picol/targets.toml`) says, in part:

```toml
[[target]]
name = "picol"
lib = "Picol"                    # coqc -Q . Picol
c = "picol_full.c"               # what clightgen verifies
proof = "verif_picol.v"          # the agent's last proof file
goals = { prog_correct = "semax_prog Picol.picol_full.prog tt Picol.spec_picol.Vprog Gprog" }
extra = ["Goal ... find_id Picol.picol_full._fopen Gprog = Some (snd Picol.spec_picol.fopen_spec) ..."]

[target.files."picol_full.c"]    # frozen files: generated, write-denied
preprocess = ["bench/picol/picol_vst.c"]
[target.files."spec_picol.v"]
copy = "bench/picol/spec_picol.v"
libc = true                      # expand (* @libc fopen fclose ... *)
```

Targets now: `picol`; `libc-strlen`, `-strcmp`, `-strchr`, `-memcpy`,
`-isupper` (`../libc/targets.toml`); sglib's `dllist`
(`../bench/sglib_vst/targets.toml`) and its 13 clients
(`../bench/sglib_vst/clients/targets.toml`).

## The shared libc specs (`../libc/specs/`)

One file per libc function: its funspec, and for a trusted function
its `body_X` axiom; `FILE_handle.v` is the trusted stream predicate.  A
program's spec file names what it uses on one line,

```coq
(* @libc FILE_handle realloc fopen fclose fputs *)
```

and the target expands it.  `../libc/TRUSTED_SPECS.md` records the
owner's approval of each trusted spec, so a later program asks only
about functions not yet there.

## The check (`check.py`)

In `PROOF_DIR/check_NAME/`, from pristine frozen files and the proof
files only: compile; keyword lint; each goal against its statement and
`Print Assumptions` (PROVED or OPEN); **coqchk** on the proof modules,
every axiom by full name either VST's (`../vst/smoke/coqchk_axioms.txt`)
or an `Axiom`/`Parameter` of a frozen file; the leak lint (`lint/`).
It writes `check_NAME.json` and the bundle manifest `manifest_NAME.json`:
the hash of every input, the tool versions, the image, and the command
that re-checks.  Example: an `Admitted` lemma named `mem_mgr` in a
proof file leaves the goal that uses it OPEN, and coqchk reports
`SglibVST.verif_dllist.mem_mgr` (`test_check.py`, case `shadow`).

## A run (`session.py`)

Fenced `claude -p` (only the tool script, which runs one command in the
VST image without network; the run directory only; frozen files
write-denied); after every command the tool prints
`[spent so far: about $X of $Y]`, priced from the stream (each
response's output tokens come in its `message_delta`; the 2026-11-25
meter missed them and read 19% low).  If the agent stops with the
proof open and money left, the run starts it again (at most 3 times).
The stream, without per-token deltas, is kept as `stream_N.jsonl`.

## VST readiness (`vst_ready.py`)

From clightgen's output, before any paid run: reachable `goto`,
`switch` without `default`, variadic calls and definitions, struct
parameters by value, externs without definition, `setjmp`, functions
whose address is taken.  On upstream picol it reports the 7 `goto`s,
the 2 `switch`es, the `printf` family and `stdin`/`stdout`/`stderr`
that fixes 3–5 and 7 dealt with (`test_vst_ready.py`); on upstream
huffman, the 2 `fprintf`, `qsort`'s comparator and `stdin`/`stdout`/
`stderr`/`optarg`.  It does not see type punning (a `uint32_t` read as
bytes) or anonymous unions; `bench/huffman/README.md` found those by
reading.

## Tests

```
python3 test_vst_ready.py     # clightgen in the image; a minute
python3 test_check.py         # 7 cases, Coq in the image
python3 lint/test_post_lint.py
```

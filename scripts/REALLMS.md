# REALLMS Agda proof-grinding harness

Offload the token-heavy, mechanical part of Agda proof work to IU's free
**REALLMS** LLM service, while Claude (or you) orchestrates: pick the goal,
supply insight when needed, and let the model do the reading / editing /
type-checking on **free** REALLMS tokens. Agda is the oracle — a candidate
"passes" only if the whole file type-checks with no errors and no holes.

## The service

REALLMS is an OpenAI-compatible API (LiteLLM router + vLLM backend), hosted
on-prem at IU, free for IU researchers.

- Base URL: `https://reallms.rescloud.iu.edu/direct/v1`
- KB: <https://servicenow.iu.edu/kb?id=kb_article_view&sysparm_article=KB0027272>
- Get a key via RT Projects (create a project + REALLMS allocation, then make a
  key on the allocation page).

### API key

Both scripts read the key from, in order:

1. `$REALLMS_API_KEY`
2. an `export REALLMS_API_KEY=...` line in `~/.zshrc`

The key is never printed. Do **not** commit it.

### Live text models (as of 2026-08)

`glm-5.2`, `gpt-oss-120b`, `Qwen3-Coder-Next`, `gemma-4-31B-it`
(plus embeddings/rerank/audio/image models not used here).

## Which model?

Benchmarked on reconstructing a real inductive proof (`renameᵗ-compose` in
`GTPLC/proof/TypeInTypeSubst.agda`) that requires one genuine insight (a
propositional-not-definitional commutation, closed with `renameᵗ-cong` + a local
`where` lemma):

| Model | Result |
|---|---|
| **glm-5.2** | solved with **no hint**, first `check_solution` |
| **gpt-oss-120b** | solved with **no hint**, first `check_solution` |
| Qwen3-Coder-Next | needed two corrective hints (weakest, despite "coder") |

**Default to `glm-5.2` or `gpt-oss-120b`.** The "coder" model was the weakest on
insight steps. (Caveat: that hole had a close in-file analog; genuinely novel
holes will be harder.)

## The two tools

### `reallms_agent.py` — agentic worker (preferred)

Gives the model its own tools so it finds its **own** context and iterates:

- `grep(pattern, path?, max_results?)` — ripgrep over `*.agda` in the repo
- `read_file(path, start?, end?)` — read any repo file (read-only)
- `check_solution(code)` — splice `code` into the target region, run `agda`,
  return `{ok, errors}`. This IS the feedback loop; the model calls it until
  `ok`.

Only a **compact** JSON report goes to stdout (final code, solved?, step/tool
counts, short error) so the orchestrator's context stays tiny; the full
blow-by-blow goes to `--log`.

```bash
python3.13 scripts/reallms_agent.py \
  --model glm-5.2 \
  --file GTPLC/proof/TypeInTypeSubst.agda \
  --start 133 --end 133 \
  --repo-root . \
  --goal "Fill the hole: prove <signature>. Induct on A." \
  --hint "optional one-line steer from the orchestrator" \
  --max-steps 24 \
  --log /tmp/agent.log
```

- `--start/--end` are the 1-based line range to replace (a hole line, or a whole
  clause/lemma). Blank the target to a single `... = {!!}` first if you want the
  model to reconstruct from scratch (otherwise it can read the existing proof).
- `--hint` is the cheap "hybrid" lever: a sentence of insight from the
  orchestrator, when the model stalls on the non-mechanical step.
- The Agda project root is auto-detected from the file's `module A.B.C` line;
  override with `--agda-root` if needed.

### `reallms_grind.py` — scripted single-region loop

No tool use: sends the whole file, asks for replacement code for a line range,
splices, type-checks, and feeds the Agda error back for `--max-iters` rounds.
Simpler, but the model only sees the one file — it cannot discover definitions
in other files. Use `reallms_agent.py` unless you specifically want the model
boxed to a single file.

```bash
python3.13 scripts/reallms_grind.py \
  --file <path> --start N --end M --model glm-5.2 \
  --max-iters 6 --instructions "curated context / strategy" --show-candidate
```

## Gotchas learned the hard way

- **`reasoning_content`.** These vLLM models often leave `content` empty and put
  the whole reply (final answer included) in a `reasoning_content` field. Both
  scripts read both.
- **Streaming is required.** Plain buffered reads hit `IncompleteRead` on long
  reasoning responses; the agent streams SSE and assembles `tool_calls` from the
  deltas. `gemma-4-31B-it` emits malformed tool-call JSON — avoid it for tool use.
- **Agda project root.** Run `agda` with cwd = the module root (the dir the
  dotted module name is relative to), not the repo root, or you get
  "top level module does not match the file name". Auto-detected from the
  `module` line.
- **Verdict = no errors AND no unsolved metas.** A file with a hole still
  "type-checks" with a warning, so both scripts explicitly reject
  `Unsolved interaction metas` / `Unsolved metas`.

## Orchestration pattern

1. Read the proof state; classify each goal as *grind-friendly* (mechanical /
   has an analog) vs *insight-heavy*.
2. Grind-friendly → hand to `reallms_agent.py` with just a goal.
3. Insight-heavy → design the key step yourself, then delegate the mechanical
   remainder (or pass the insight as `--hint`).
4. Apply what type-checks; re-scope or add a sharper hint when it stalls; escalate
   model (`glm-5.2` → `gpt-oss-120b`) or step count as needed.

## Safety

The agent's file access is read-only except for the single target region, which
it only writes transiently during `check_solution` (the original is always
restored). It runs only `agda` and `rg`, and all paths are confined to
`--repo-root`.

#!/usr/bin/env python3.13
"""
REALLMS Agda grinding harness.

Given an Agda file and a line range to replace, ask a REALLMS model to produce
replacement code, splice it in, type-check with the real `agda` binary, then
restore the original file. Agda is the oracle: a clause succeeds iff type-check
reports no errors and no "Unsolved interaction metas".

The API key is read from (in priority order):
  1. $REALLMS_API_KEY
  2. the `export REALLMS_API_KEY=...` line in ~/.zshrc
The key is never printed.

Usage:
  reallms_grind.py --file PATH --start N --end M --model NAME [--agda-root DIR]
                   [--instructions TEXT] [--max-iters K] [--show-candidate]
"""
import argparse
import json
import os
import re
import subprocess
import sys
import urllib.request
import urllib.error

BASE_URL = "https://reallms.rescloud.iu.edu/direct/v1"


def read_key() -> str:
    # env override, then an export in ~/.zshrc, then a ~/.reallms_key file
    # (last, so a working zshrc export is never shadowed by a stale file).
    k = os.environ.get("REALLMS_API_KEY")
    if k and k.strip():
        return k.strip()
    try:
        with open(os.path.expanduser("~/.zshrc")) as f:
            for line in f:
                m = re.match(r'\s*export\s+REALLMS_API_KEY=(.*)', line)
                if m:
                    v = m.group(1).strip().strip('"').strip("'")
                    if v:
                        return v
    except FileNotFoundError:
        pass
    try:
        with open(os.path.expanduser("~/.reallms_key")) as f:
            v = f.read().strip()
            if v:
                return v
    except FileNotFoundError:
        pass
    sys.exit("No REALLMS_API_KEY found (checked $REALLMS_API_KEY, ~/.zshrc, "
             "~/.reallms_key)")


def chat(model: str, messages: list, key: str, temperature: float = 0.2):
    """Stream a chat completion (SSE) and return (content, reasoning).

    Streaming avoids the IncompleteRead failures that plain urllib hits on these
    long reasoning responses, and lets long generations complete reliably.
    """
    payload = json.dumps({
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": 16384,
        "stream": True,
    }).encode()
    req = urllib.request.Request(
        f"{BASE_URL}/chat/completions",
        data=payload,
        headers={
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    content_parts, reasoning_parts = [], []
    try:
        with urllib.request.urlopen(req, timeout=1200) as resp:
            for raw in resp:
                line = raw.decode("utf-8", errors="replace").strip()
                if not line.startswith("data:"):
                    continue
                data = line[len("data:"):].strip()
                if data == "[DONE]":
                    break
                try:
                    chunk = json.loads(data)
                except json.JSONDecodeError:
                    continue
                choices = chunk.get("choices") or []
                if not choices:
                    continue
                delta = choices[0].get("delta") or {}
                if delta.get("content"):
                    content_parts.append(delta["content"])
                if delta.get("reasoning_content"):
                    reasoning_parts.append(delta["reasoning_content"])
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="replace")
        raise RuntimeError(f"HTTP {e.code}: {body[:500]}")
    return "".join(content_parts), "".join(reasoning_parts)


def extract_code(content: str, reasoning: str) -> str:
    """Pull the LAST fenced code block, preferring `content` over `reasoning`.

    The last block is the model's final answer (earlier blocks are drafts it
    reconsidered). If neither has a fence, use whichever text is non-empty.
    """
    for text in (content, reasoning):
        blocks = re.findall(r"```(?:agda)?\s*\n(.*?)```", text, re.DOTALL)
        if blocks:
            return blocks[-1].rstrip("\n")
    return (content or reasoning).strip()


def detect_agda_root(file_path: str) -> str:
    """Infer the Agda include root from the file's `module A.B.C` declaration:
    strip (len parts - 1) directory components off the file's directory."""
    mod = None
    with open(file_path) as f:
        for line in f:
            m = re.match(r'\s*module\s+([\w.Ā-￿]+)\s+where', line)
            if m:
                mod = m.group(1)
                break
    d = os.path.dirname(os.path.abspath(file_path))
    if mod:
        for _ in range(mod.count(".")):
            d = os.path.dirname(d)
    return d


def typecheck(agda_root: str, file_path: str) -> tuple[bool, str]:
    """Return (ok, output). ok iff no errors and no unsolved interaction metas."""
    proc = subprocess.run(
        ["agda", file_path],
        cwd=agda_root,
        capture_output=True,
        text=True,
    )
    out = proc.stdout + proc.stderr
    ok = (proc.returncode == 0) and ("Unsolved interaction metas" not in out) \
        and ("Unsolved metas" not in out)
    return ok, out


def relevant_output(out: str, file_path: str) -> str:
    """Trim the type-checker log to the interesting tail (errors/warnings)."""
    lines = out.splitlines()
    # Drop the "Checking X (...)" progress spam.
    keep = [ln for ln in lines if not ln.lstrip().startswith("Checking ")]
    tail = "\n".join(keep).strip()
    return tail if tail else out[-2000:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", required=True, help="Agda file (absolute path)")
    ap.add_argument("--start", type=int, required=True, help="1-based first line to replace")
    ap.add_argument("--end", type=int, required=True, help="1-based last line to replace")
    ap.add_argument("--model", required=True)
    ap.add_argument("--agda-root", default=None,
                    help="cwd for agda (defaults to file's dir chain root guess)")
    ap.add_argument("--instructions", default="")
    ap.add_argument("--max-iters", type=int, default=1,
                    help="feedback iterations: re-prompt with the type error")
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--show-candidate", action="store_true")
    args = ap.parse_args()

    key = read_key()
    file_path = os.path.abspath(args.file)
    agda_root = args.agda_root or detect_agda_root(file_path)

    with open(file_path) as f:
        original = f.read()
    src_lines = original.splitlines(keepends=True)
    region = "".join(src_lines[args.start - 1:args.end])

    system = (
        "You are an expert Agda proof engineer. You will be given a complete Agda "
        "source file and asked to replace one specific region (a clause or a hole) "
        "so that the whole file type-checks with no errors and no remaining holes. "
        "Study the sibling clauses in the file and mirror their style exactly. "
        "You MUST return ONLY the replacement Agda code for the indicated region, "
        "inside a single ```agda code block, with no commentary. Do not include the "
        "rest of the file. Preserve indentation appropriate to the region."
    )
    user = (
        f"Here is the full file `{os.path.basename(file_path)}`:\n\n"
        f"```agda\n{original}\n```\n\n"
        f"Replace lines {args.start}-{args.end}, which currently are:\n\n"
        f"```agda\n{region}\n```\n\n"
        f"{args.instructions}\n\n"
        "Return ONLY the replacement code for those lines, in one ```agda block."
    )
    messages = [
        {"role": "system", "content": system},
        {"role": "user", "content": user},
    ]

    result = {"model": args.model, "ok": False, "iters": 0, "candidate": None,
              "error": None, "agda_tail": None}
    try:
        for it in range(1, args.max_iters + 1):
            result["iters"] = it
            content, reasoning = chat(args.model, messages, key, args.temperature)
            reply = content or reasoning
            candidate = extract_code(content, reasoning)
            result["candidate"] = candidate
            # Splice: replace the region lines with candidate.
            new_lines = (src_lines[:args.start - 1]
                         + [candidate + "\n"]
                         + src_lines[args.end:])
            try:
                with open(file_path, "w") as f:
                    f.write("".join(new_lines))
                ok, out = typecheck(agda_root, file_path)
            finally:
                with open(file_path, "w") as f:
                    f.write(original)
            tail = relevant_output(out, file_path)
            result["agda_tail"] = tail
            if ok:
                result["ok"] = True
                break
            # Feedback for next iteration.
            messages.append({"role": "assistant", "content": reply})
            messages.append({
                "role": "user",
                "content": (
                    "That did not type-check. Agda reported:\n\n"
                    f"```\n{tail[:3000]}\n```\n\n"
                    "Fix it. Return ONLY the corrected replacement code for the "
                    "same region, in one ```agda block."
                ),
            })
    except Exception as e:
        result["error"] = str(e)

    if not args.show_candidate:
        result_print = dict(result)
        result_print["candidate"] = (result["candidate"] or "")[:0] or None
        print(json.dumps({k: result[k] for k in
                          ["model", "ok", "iters", "error"]}, indent=2))
        if result["agda_tail"]:
            print("--- agda tail ---")
            print(result["agda_tail"][:1500])
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

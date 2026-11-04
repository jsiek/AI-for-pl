"""Shared REALLMS client: key lookup, model listing, streaming chat with
tool calls, and the tool-calling loop (with nudging) used by the Agda
worker (reallms_agent.py) and the Ariadne Coq prover
(Ariadne/prover/reallms_coq.py).

REALLMS is IU's OpenAI-compatible LLM service (scripts/REALLMS.md).  The
base URL can be overridden with $REALLMS_BASE_URL.  The key is read from
$REALLMS_API_KEY, then an `export REALLMS_API_KEY=...` line in ~/.zshrc,
then ~/.reallms_key; it is never printed or logged.
"""
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request

BASE_URL = os.environ.get("REALLMS_BASE_URL",
                          "https://reallms.rescloud.iu.edu/direct/v1")


def read_key() -> str:
    v = os.environ.get("REALLMS_API_KEY", "").strip()
    if v:
        return v
    try:
        with open(os.path.expanduser("~/.zshrc")) as f:
            for line in f:
                m = re.match(r"\s*export\s+REALLMS_API_KEY=['\"]?([^'\"\s]+)",
                             line)
                if m:
                    return m.group(1)
    except FileNotFoundError:
        pass
    try:
        with open(os.path.expanduser("~/.reallms_key")) as f:
            v = f.read().strip()
    except FileNotFoundError:
        v = ""
    if not v:
        sys.exit("No REALLMS key: set $REALLMS_API_KEY or create "
                 "~/.reallms_key holding just the key.")
    return v


def _request(path, key, payload=None):
    return urllib.request.Request(
        f"{BASE_URL}{path}",
        data=json.dumps(payload).encode() if payload is not None else None,
        headers={"Authorization": f"Bearer {key}",
                 "Content-Type": "application/json"},
        method="POST" if payload is not None else "GET")


def list_models(key):
    with urllib.request.urlopen(_request("/models", key), timeout=60) as r:
        return sorted(m["id"] for m in json.load(r).get("data", []))


def chat(model, messages, key, tools=None, temperature=0.2,
         max_tokens=16384, retries=6):
    """chat_once, retried with exponential backoff (honouring
    Retry-After) on HTTP 429 and 5xx: the service is rate-limited."""
    for attempt in range(retries + 1):
        try:
            return chat_once(model, messages, key, tools, temperature,
                             max_tokens)
        except urllib.error.HTTPError as e:
            if attempt == retries or not (e.code == 429 or e.code >= 500):
                raise
            wait = e.headers.get("Retry-After") if e.headers else None
            try:
                wait = float(wait)
            except (TypeError, ValueError):
                wait = 5 * 2 ** attempt
            time.sleep(min(wait, 300))


def chat_once(model, messages, key, tools=None, temperature=0.2,
              max_tokens=16384):
    """One streamed chat completion.  Returns content, reasoning (vLLM
    models often put the whole reply in reasoning_content), tool_calls
    assembled from the deltas, finish reason, and usage if reported."""
    payload = {"model": model, "messages": messages,
               "temperature": temperature, "max_tokens": max_tokens,
               "stream": True, "stream_options": {"include_usage": True}}
    if tools:
        payload["tools"] = tools
        payload["tool_choice"] = "auto"
    content, reasoning = [], []
    tool_calls = {}  # index -> {id, name, args}
    finish = usage = None
    with urllib.request.urlopen(_request("/chat/completions", key, payload),
                                timeout=1200) as resp:
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
            if chunk.get("usage"):
                usage = chunk["usage"]
            ch = (chunk.get("choices") or [{}])[0]
            delta = ch.get("delta") or {}
            if ch.get("finish_reason"):
                finish = ch["finish_reason"]
            if delta.get("content"):
                content.append(delta["content"])
            if delta.get("reasoning_content"):
                reasoning.append(delta["reasoning_content"])
            for tc in (delta.get("tool_calls") or []):
                idx = tc.get("index", 0)
                slot = tool_calls.setdefault(
                    idx, {"id": None, "name": "", "args": ""})
                if tc.get("id"):
                    slot["id"] = tc["id"]
                fn = tc.get("function") or {}
                if fn.get("name"):
                    slot["name"] = fn["name"]
                if fn.get("arguments"):
                    slot["args"] += fn["arguments"]
    calls = [tool_calls[i] for i in sorted(tool_calls)]
    return {"content": "".join(content), "reasoning": "".join(reasoning),
            "tool_calls": calls, "finish": finish, "usage": usage}


def logline(fh, s):
    if fh:
        fh.write(s + "\n")
        fh.flush()


CUT_OFF = ("Your last reply was cut off at the output limit before you "
           "made a tool call, so nothing was checked.  Do not reason it all "
           "out first: submit your current best attempt now with a tool "
           "call, and let the checker's errors guide the next step.")


def tool_loop(model, key, system, user, tools, dispatch, solved,
              check_tool, nudge, max_steps=24, temperature=0.2, fh=None,
              max_tokens=16384):
    """Run the model with tools until `solved()` after a call to
    `check_tool`, the model gives up, or max_steps.  `dispatch(name, args)`
    runs a tool and returns a str or JSON-able value.  `nudge` is the
    message sent (up to 3 times) when the model answers without a tool
    call while unsolved; a reply cut off at max_tokens gets CUT_OFF
    instead, and does not count as a nudge.  Returns {status, steps,
    usage, seconds, cut_off}."""
    messages = [{"role": "system", "content": system},
                {"role": "user", "content": user}]
    status, nudges, step, cut_off = "incomplete", 0, 0, 0
    usage = {"prompt_tokens": 0, "completion_tokens": 0}
    t0 = time.time()
    for step in range(1, max_steps + 1):
        try:
            r = chat(model, messages, key, tools, temperature, max_tokens)
        except Exception as e:  # network or HTTP error; never echo headers
            status = f"api_error: {type(e).__name__}: {e}"
            break
        for k in usage:
            usage[k] += (r["usage"] or {}).get(k) or 0
        logline(fh, f"\n===== step {step} =====")
        if r["reasoning"]:
            logline(fh, "[reasoning]\n" + r["reasoning"])
        if r["content"]:
            logline(fh, "[content]\n" + r["content"])
        calls = r["tool_calls"]
        assistant = {"role": "assistant", "content": r["content"] or ""}
        if calls:
            assistant["tool_calls"] = [
                {"id": c["id"] or f"call_{step}_{i}", "type": "function",
                 "function": {"name": c["name"], "arguments": c["args"]}}
                for i, c in enumerate(calls)]
        messages.append(assistant)
        if not calls:
            # Reasoning models often narrate a proof without checking it.
            if solved():
                status = "solved"
                break
            if r["finish"] == "length":
                cut_off += 1
                logline(fh, f"[cut off at max_tokens ({cut_off}) -> told so]")
                messages.append({"role": "user", "content": CUT_OFF})
                continue
            nudges += 1
            if nudges > 3:
                logline(fh, "[no tool calls after nudges -> giving up]")
                status = "gave_up"
                break
            logline(fh, f"[no tool calls -> nudge {nudges}/3]")
            messages.append({"role": "user", "content": nudge})
            continue
        for i, c in enumerate(calls):
            cid = assistant["tool_calls"][i]["id"]
            try:
                cargs = json.loads(c["args"]) if c["args"].strip() else {}
            except json.JSONDecodeError as e:
                messages.append({"role": "tool", "tool_call_id": cid,
                                 "name": c["name"],
                                 "content": f"(bad tool arguments JSON: {e})"})
                logline(fh, f"[tool {c['name']}] BAD ARGS: {c['args'][:200]}")
                continue
            result = dispatch(c["name"], cargs)
            rendered = result if isinstance(result, str) else json.dumps(result)
            logline(fh, f"[tool {c['name']}({json.dumps(cargs)[:200]})] -> "
                        f"{rendered[:400]}")
            messages.append({"role": "tool", "tool_call_id": cid,
                             "name": c["name"], "content": rendered})
            if solved():
                # Stop at the first call that leaves the goal solved
                # (check_tool, or another tool that checks with it): a
                # later failing call in the same turn must not overwrite
                # the verified solution.
                status = "solved"
                break
        if status == "solved":
            break
    return {"status": status, "steps": step, "usage": usage,
            "seconds": round(time.time() - t0, 1), "cut_off": cut_off}


if __name__ == "__main__":
    # Smoke test: list the models this key can use (the key is not shown).
    for m in list_models(read_key()):
        print(m)

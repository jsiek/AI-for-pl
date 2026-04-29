#!/usr/bin/env python3
"""Run TODO items through Codex and triage them into Completed or Blocked."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

CHECKBOX_RE = re.compile(r"^(\s*[-*]?\s*)\[( |x|X|B)\](\s*.*)$")
HEADING_RE = re.compile(r"^##\s+(.*)$")


@dataclass
class Section:
    start: int
    end: int
    title: str


@dataclass
class TodoItem:
    start: int
    end: int
    lines: list[str]
    signature: str


@dataclass
class RunResult:
    status: str
    summary: str
    blocker: str


def read_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines(keepends=True)


def write_lines(path: Path, lines: list[str]) -> None:
    path.write_text("".join(lines), encoding="utf-8")


def list_sections(lines: list[str]) -> list[Section]:
    starts: list[tuple[int, str]] = []
    for i, line in enumerate(lines):
        m = HEADING_RE.match(line.strip())
        if m:
            starts.append((i, m.group(1)))
    sections: list[Section] = []
    for idx, (start, title) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        sections.append(Section(start=start, end=end, title=title))
    return sections


def find_todo_section(lines: list[str]) -> Section:
    for section in list_sections(lines):
        lower = section.title.lower()
        if "todo" in lower and "completed" not in lower and "blocked" not in lower and "postponed" not in lower:
            return section
    raise ValueError("Could not find a TODO section (expected a heading like `## TODO items`).")


def find_section_by_keyword(lines: list[str], keyword: str) -> Optional[Section]:
    keyword_lower = keyword.lower()
    for section in list_sections(lines):
        if keyword_lower in section.title.lower():
            return section
    return None


def ensure_section(lines: list[str], title: str) -> Section:
    existing = find_section_by_keyword(lines, title)
    if existing:
        return existing
    if lines and lines[-1].strip() != "":
        lines.append("\n")
    lines.append(f"## {title}\n")
    lines.append("\n")
    return Section(start=len(lines) - 2, end=len(lines), title=title)


def normalize_signature(line: str) -> str:
    m = CHECKBOX_RE.match(line)
    if not m:
        return line.strip()
    return m.group(3).strip()


def find_item(lines: list[str], todo_section: Section, signature: Optional[str] = None) -> Optional[TodoItem]:
    i = todo_section.start + 1
    while i < todo_section.end:
        line = lines[i]
        if HEADING_RE.match(line.strip()):
            break
        m = CHECKBOX_RE.match(line)
        if m and m.group(2) == " ":
            sig = normalize_signature(line)
            if signature is None or sig == signature:
                j = i + 1
                while j < todo_section.end:
                    next_line = lines[j]
                    if HEADING_RE.match(next_line.strip()):
                        break
                    if CHECKBOX_RE.match(next_line):
                        break
                    j += 1
                return TodoItem(start=i, end=j, lines=lines[i:j], signature=sig)
        i += 1
    return None


def first_todo_item(lines: list[str], todo_section: Section) -> Optional[TodoItem]:
    return find_item(lines, todo_section, signature=None)


def extract_task_text(item: TodoItem) -> str:
    if not item.lines:
        return ""
    first = CHECKBOX_RE.sub(r"\3", item.lines[0]).rstrip("\n")
    rest = [line.rstrip("\n") for line in item.lines[1:]]
    return "\n".join([first] + rest).strip()


def mark_item_completed(item: TodoItem) -> list[str]:
    lines = item.lines[:]
    if lines:
        lines[0] = re.sub(r"\[( )\]", "[x]", lines[0], count=1)
    return lines


def mark_item_blocked(item: TodoItem, blocker: str) -> list[str]:
    lines = item.lines[:]
    if lines:
        if "[ ]" in lines[0]:
            lines[0] = lines[0].replace("[ ]", "[B]", 1)
        else:
            lines[0] = f"- [B] {lines[0].strip()}\n"
    blocker_clean = " ".join(blocker.split())
    lines.append(f"  Blocker: {blocker_clean}\n")
    return lines


def append_to_section(lines: list[str], section: Section, block: list[str]) -> None:
    insert_at = section.end
    chunk: list[str] = []
    if insert_at > section.start + 1 and lines[insert_at - 1].strip() != "":
        chunk.append("\n")
    chunk.extend(block)
    if chunk and chunk[-1].strip() != "":
        chunk.append("\n")
    lines[insert_at:insert_at] = chunk


def build_prompt(todo_file: Path, task_text: str) -> str:
    return (
        "You are executing one queued task from a TODO runner.\n"
        f"TODO file: {todo_file}\n\n"
        "Task:\n"
        f"{task_text}\n\n"
        "Please attempt to complete this task in the repository.\n"
        "Do not edit the TODO file itself.\n"
        "Return only a JSON object that matches the provided schema.\n"
        "Set status to `success` only if the task is actually completed.\n"
        "Set status to `blocked` if you cannot complete it now, and provide a concrete blocker."
    )


def run_codex(
    todo_file: Path,
    task_text: str,
    run_dir: Path,
    model: Optional[str],
    sandbox: str,
    approval: str,
) -> RunResult:
    run_dir.mkdir(parents=True, exist_ok=True)
    schema_path = run_dir / "status_schema.json"
    out_path = run_dir / "last_message.json"

    schema = {
        "type": "object",
        "required": ["status", "summary", "blocker"],
        "properties": {
            "status": {"type": "string", "enum": ["success", "blocked"]},
            "summary": {"type": "string"},
            "blocker": {"type": "string"},
        },
        "additionalProperties": False,
    }
    schema_path.write_text(json.dumps(schema, indent=2), encoding="utf-8")

    cmd = ["codex", "-s", sandbox, "-a", approval, "exec", "--output-schema", str(schema_path), "-o", str(out_path)]
    if model:
        cmd.extend(["-m", model])
    cmd.append(build_prompt(todo_file, task_text))

    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        blocker = proc.stderr.strip() or proc.stdout.strip() or f"codex exec failed with exit code {proc.returncode}"
        return RunResult(status="blocked", summary="Task attempt failed to run.", blocker=blocker[:1200])

    try:
        payload = json.loads(out_path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        return RunResult(
            status="blocked",
            summary="Could not parse Codex result.",
            blocker=f"Could not parse JSON output from codex exec: {exc}",
        )

    status = payload.get("status", "blocked")
    summary = str(payload.get("summary", "")).strip() or "No summary provided."
    blocker = str(payload.get("blocker", "")).strip()
    if status == "success":
        return RunResult(status="success", summary=summary, blocker="")
    if not blocker:
        blocker = "Codex reported blocked status without a blocker explanation."
    return RunResult(status="blocked", summary=summary, blocker=blocker)


def process_one_item(
    todo_path: Path,
    run_dir: Path,
    model: Optional[str],
    sandbox: str,
    approval: str,
    dry_run: bool,
) -> bool:
    lines = read_lines(todo_path)
    todo_section = find_todo_section(lines)
    item = first_todo_item(lines, todo_section)
    if not item:
        return False

    task_text = extract_task_text(item)
    if dry_run:
        result = RunResult(status="success", summary="Dry run: skipped codex execution.", blocker="")
    else:
        result = run_codex(todo_path, task_text, run_dir, model, sandbox, approval)

    latest = read_lines(todo_path)
    latest_todo = find_todo_section(latest)
    current_item = find_item(latest, latest_todo, signature=item.signature) or first_todo_item(latest, latest_todo)
    if not current_item:
        return True

    del latest[current_item.start:current_item.end]

    if result.status == "success":
        done_section = ensure_section(latest, "Completed TODO items")
        append_to_section(latest, done_section, mark_item_completed(current_item))
        print(f"SUCCESS: {current_item.signature}")
    else:
        blocked_section = ensure_section(latest, "Blocked TODO items")
        append_to_section(latest, blocked_section, mark_item_blocked(current_item, result.blocker))
        print(f"BLOCKED: {current_item.signature}")
        print(f"  blocker: {result.blocker}")

    write_lines(todo_path, latest)
    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Process the first TODO item with Codex, then move it to Completed or Blocked. Repeats until TODO is empty."
    )
    parser.add_argument("todo_file", type=Path, help="Path to the markdown TODO file.")
    parser.add_argument("--watch", action="store_true", help="Keep polling the TODO file after it is empty.")
    parser.add_argument("--interval-seconds", type=float, default=10.0, help="Polling interval for --watch mode.")
    parser.add_argument("--model", default=None, help="Optional model to pass to codex exec.")
    parser.add_argument("--sandbox", default="workspace-write", help="Sandbox mode for codex (`workspace-write`, etc.).")
    parser.add_argument(
        "--approval",
        default="never",
        help="Approval mode for codex (`never`, `on-request`, `untrusted`). Default is `never` for unattended runs.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Do not call codex; move items as if each task succeeded.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    todo_path = args.todo_file.resolve()
    if not todo_path.exists():
        print(f"TODO file not found: {todo_path}", file=sys.stderr)
        return 1

    run_dir = Path(".codex-todo-runner")

    while True:
        try:
            processed = process_one_item(
                todo_path=todo_path,
                run_dir=run_dir,
                model=args.model,
                sandbox=args.sandbox,
                approval=args.approval,
                dry_run=args.dry_run,
            )
        except ValueError as exc:
            print(str(exc), file=sys.stderr)
            return 1

        if not processed:
            if args.watch:
                time.sleep(args.interval_seconds)
                continue
            print("No remaining unchecked TODO items.")
            return 0


if __name__ == "__main__":
    raise SystemExit(main())

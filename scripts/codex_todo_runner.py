#!/usr/bin/env python3
"""Run TODO items through Codex and triage them into Completed or Blocked."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import time
import tempfile
from datetime import datetime
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

CHECKBOX_RE = re.compile(r"^(\s*[-*]?\s*)\[( |x|X|B)\](\s*.*)$")
HEADING_RE = re.compile(r"^##\s+(.*)$")
DIRECTIVE_RE = re.compile(r"^\s*(Workers|Plan|Helpers)\s*:\s*(.+?)\s*$", re.IGNORECASE)
PLAN_HOLE_RE = re.compile(r"^\s*-\s*([A-Z]\d+)\s*:\s*(\d+)\s*$")
AGDA_PATH_RE = re.compile(r"([A-Za-z0-9_./-]+\.agda)")
BLOCKED_LINE_COMMENT_RE = re.compile(r"^\s*--\s*BLOCKED\[W\d+\]\[[A-Z]\d+\]:")
BLOCKED_BLOCK_COMMENT_START_RE = re.compile(r"^\s*\{\-\s*BLOCKED\[W\d+\]\[[A-Z]\d+\]:")


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


@dataclass
class TaskOutcome:
    item: TodoItem
    result: RunResult
    worker_dir: Path
    base_rev: Optional[str] = None
    copied: int = 0
    removed: int = 0
    touched_paths: set[Path] = field(default_factory=set)
    hole_id: Optional[str] = None
    worker_id: Optional[int] = None


@dataclass
class TodoDirectives:
    workers: Optional[int] = None
    plan: Optional[Path] = None
    helpers: list[Path] = field(default_factory=list)


@dataclass
class HoleTarget:
    hole_id: str
    line: int


@dataclass
class HoleLocator:
    line: int
    lhs_key: Optional[str]


def run_checked(
    cmd: list[str],
    *,
    cwd: Optional[Path] = None,
    timeout_seconds: Optional[float] = None,
) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
    )
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or f"exit code {proc.returncode}"
        raise RuntimeError(f"Command failed: {' '.join(cmd)}\n{detail}")
    return proc


def run_checked_bytes(cmd: list[str], *, cwd: Optional[Path] = None) -> subprocess.CompletedProcess[bytes]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=False,
    )
    if proc.returncode != 0:
        detail = proc.stderr.decode("utf-8", errors="replace").strip() or proc.stdout.decode(
            "utf-8", errors="replace"
        ).strip() or f"exit code {proc.returncode}"
        raise RuntimeError(f"Command failed: {' '.join(cmd)}\n{detail}")
    return proc


def parse_nul_paths(payload: bytes) -> list[Path]:
    return [Path(raw.decode("utf-8", errors="surrogateescape")) for raw in payload.split(b"\0") if raw]


def git_toplevel(start_dir: Path) -> Path:
    out = run_checked(["git", "-C", str(start_dir), "rev-parse", "--show-toplevel"])
    return Path(out.stdout.strip()).resolve()


def ensure_path_within(base: Path, path: Path) -> None:
    try:
        path.relative_to(base)
    except ValueError as exc:
        raise ValueError(f"Path must be inside repository root: {path}") from exc


def prepare_worktree(repo_root: Path, worktree_dir: Path) -> None:
    if not worktree_dir.exists():
        run_checked(["git", "-C", str(repo_root), "worktree", "add", "--detach", str(worktree_dir), "HEAD"])
    else:
        try:
            wt_root = git_toplevel(worktree_dir)
        except RuntimeError as exc:
            raise ValueError(f"Existing worktree path is not a git worktree: {worktree_dir}") from exc
        if wt_root != worktree_dir.resolve():
            raise ValueError(f"Worktree path resolves to unexpected git root: {wt_root}")


def reset_worktree_to_head(repo_root: Path, worktree_dir: Path) -> None:
    run_checked(["git", "-C", str(worktree_dir), "reset", "--hard", "HEAD"])
    run_checked(["git", "-C", str(worktree_dir), "clean", "-fd"])
    main_head = run_checked(["git", "-C", str(repo_root), "rev-parse", "HEAD"]).stdout.strip()
    run_checked(["git", "-C", str(worktree_dir), "checkout", "--detach", main_head])


def copy_path_preserving_kind(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists() or dst.is_symlink():
        if dst.is_dir() and not dst.is_symlink():
            shutil.rmtree(dst)
        else:
            dst.unlink()
    if src.is_symlink():
        os.symlink(os.readlink(src), dst)
    elif src.is_file():
        shutil.copy2(src, dst)
    else:
        raise RuntimeError(f"Cannot copy non-file path: {src}")


def apply_worktree_changes_to_main(
    repo_root: Path,
    worktree_dir: Path,
    *,
    excluded_relative: set[Path],
    base_rev: Optional[str] = None,
) -> tuple[int, int, set[Path]]:
    changed = parse_nul_paths(
        run_checked_bytes(["git", "-C", str(worktree_dir), "diff", "--name-only", "-z", "HEAD"]).stdout
    )
    deleted = set(
        parse_nul_paths(
            run_checked_bytes(
                ["git", "-C", str(worktree_dir), "diff", "--name-only", "--diff-filter=D", "-z", "HEAD"]
            ).stdout
        )
    )
    untracked = parse_nul_paths(
        run_checked_bytes(["git", "-C", str(worktree_dir), "ls-files", "--others", "--exclude-standard", "-z"]).stdout
    )

    copied = 0
    removed = 0
    touched: set[Path] = set()

    def read_bytes_if_exists(path: Path) -> Optional[bytes]:
        if path.exists() and path.is_file():
            return path.read_bytes()
        return None

    def git_show_bytes(rev: str, rel: Path) -> Optional[bytes]:
        proc = subprocess.run(
            ["git", "-C", str(repo_root), "show", f"{rev}:{rel.as_posix()}"],
            capture_output=True,
            text=False,
        )
        if proc.returncode != 0:
            return None
        return proc.stdout

    def merge_three_way_text(rel: Path, ours: bytes, base: bytes, theirs: bytes) -> bytes:
        merge_tmp_root = repo_root / ".codex-todo-runner" / "merge-tmp"
        merge_tmp_root.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="todo-merge-", dir=merge_tmp_root) as td:
            tdir = Path(td)
            ours_path = tdir / "ours"
            base_path = tdir / "base"
            theirs_path = tdir / "theirs"
            ours_path.write_bytes(ours)
            base_path.write_bytes(base)
            theirs_path.write_bytes(theirs)
            proc = subprocess.run(
                [
                    "git",
                    "merge-file",
                    "-p",
                    str(ours_path),
                    str(base_path),
                    str(theirs_path),
                ],
                capture_output=True,
                text=False,
            )
            if proc.returncode == 0:
                return proc.stdout
            if proc.returncode == 1:
                raise RuntimeError(
                    f"Conflicting edits for `{rel}` while applying worker changes. "
                    "Both another worker and this worker modified overlapping text."
                )
            detail = proc.stderr.decode("utf-8", errors="replace").strip() or "merge-file failed"
            raise RuntimeError(f"Could not merge changes for `{rel}`: {detail}")

    for rel in changed:
        if rel in excluded_relative:
            continue
        src = worktree_dir / rel
        dst = repo_root / rel
        src_bytes = read_bytes_if_exists(src)
        dst_bytes = read_bytes_if_exists(dst)
        base_bytes = git_show_bytes(base_rev, rel) if base_rev else None

        if rel in deleted:
            if dst_bytes is not None and base_bytes is not None and dst_bytes != base_bytes:
                raise RuntimeError(
                    f"Conflicting delete for `{rel}`: main file changed since worker started."
                )
            if dst.exists() or dst.is_symlink():
                if dst.is_dir() and not dst.is_symlink():
                    shutil.rmtree(dst)
                else:
                    dst.unlink()
                removed += 1
                touched.add(rel)
            continue

        if src_bytes is None:
            raise RuntimeError(f"Expected modified file is missing in worker tree: `{rel}`")

        if dst_bytes is None:
            copy_path_preserving_kind(src, dst)
            copied += 1
            touched.add(rel)
            continue

        if dst_bytes == src_bytes:
            continue
        if base_bytes is None:
            raise RuntimeError(
                f"Cannot safely apply changes for `{rel}` because base revision content is unavailable."
            )
        if dst_bytes == base_bytes:
            copy_path_preserving_kind(src, dst)
            copied += 1
            touched.add(rel)
            continue
        if src_bytes == base_bytes:
            continue

        merged = merge_three_way_text(rel, dst_bytes, base_bytes, src_bytes)
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(merged)
        copied += 1
        touched.add(rel)

    for rel in untracked:
        if rel in excluded_relative:
            continue
        src = worktree_dir / rel
        if src.is_dir():
            continue
        dst = repo_root / rel
        src_bytes = read_bytes_if_exists(src)
        if src_bytes is None:
            continue
        dst_bytes = read_bytes_if_exists(dst)
        if dst_bytes is not None:
            if dst_bytes == src_bytes:
                continue
            raise RuntimeError(
                f"Conflicting new-file content for `{rel}` from multiple workers."
            )
        copy_path_preserving_kind(src, dst)
        copied += 1
        touched.add(rel)

    return copied, removed, touched


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


def list_todo_items(lines: list[str], todo_section: Section, limit: Optional[int] = None) -> list[TodoItem]:
    items: list[TodoItem] = []
    i = todo_section.start + 1
    while i < todo_section.end:
        line = lines[i]
        if HEADING_RE.match(line.strip()):
            break
        m = CHECKBOX_RE.match(line)
        if m and m.group(2) == " ":
            j = i + 1
            while j < todo_section.end:
                next_line = lines[j]
                if HEADING_RE.match(next_line.strip()):
                    break
                if CHECKBOX_RE.match(next_line):
                    break
                j += 1
            items.append(TodoItem(start=i, end=j, lines=lines[i:j], signature=normalize_signature(line)))
            if limit is not None and len(items) >= limit:
                break
            i = j
            continue
        i += 1
    return items


def first_todo_item(lines: list[str], todo_section: Section) -> Optional[TodoItem]:
    items = list_todo_items(lines, todo_section, limit=1)
    return items[0] if items else None


def extract_task_text(item: TodoItem) -> str:
    body_lines, _directives = parse_item_body_and_directives(item)
    return "\n".join(body_lines).strip()


def parse_item_body_and_directives(item: TodoItem) -> tuple[list[str], TodoDirectives]:
    if not item.lines:
        return ([], TodoDirectives())

    first = CHECKBOX_RE.sub(r"\3", item.lines[0]).rstrip("\n")
    rest = [line.rstrip("\n") for line in item.lines[1:]]
    raw_lines = [first] + rest

    directives = TodoDirectives()
    body_lines: list[str] = []

    for raw in raw_lines:
        m = DIRECTIVE_RE.match(raw)
        if not m:
            body_lines.append(raw)
            continue
        key = m.group(1).lower()
        value = m.group(2).strip()
        if key == "workers":
            try:
                directives.workers = int(value)
            except ValueError:
                body_lines.append(raw)
        elif key == "plan":
            directives.plan = Path(value)
        elif key == "helpers":
            directives.helpers = [Path(part.strip()) for part in value.split(",") if part.strip()]
        else:
            body_lines.append(raw)

    return (body_lines, directives)


def resolve_repo_relative_path(repo_root: Path, path: Path) -> Path:
    resolved = (repo_root / path).resolve() if not path.is_absolute() else path.resolve()
    ensure_path_within(repo_root, resolved)
    return resolved


def validate_item_directives(
    directives: TodoDirectives,
    repo_root: Path,
    parallel: int,
) -> Optional[str]:
    if directives.workers is not None:
        if directives.workers <= 0:
            return f"Invalid `Workers` directive: {directives.workers}. Must be a positive integer."
        if directives.workers != parallel:
            return (
                f"`Workers: {directives.workers}` does not match runner concurrency "
                f"`--parallel {parallel}`."
            )

    if directives.plan is not None:
        try:
            plan_path = resolve_repo_relative_path(repo_root, directives.plan)
        except ValueError as exc:
            return f"Invalid `Plan` path: {exc}"
        if not plan_path.exists() or not plan_path.is_file():
            return f"`Plan` file does not exist: {directives.plan}"

    for helper in directives.helpers:
        try:
            helper_path = resolve_repo_relative_path(repo_root, helper)
        except ValueError as exc:
            return f"Invalid `Helpers` path: {exc}"
        if not helper_path.exists() or not helper_path.is_file():
            return f"`Helpers` file does not exist: {helper}"

    return None


def parse_plan_holes(plan_path: Path) -> list[HoleTarget]:
    holes: list[HoleTarget] = []
    for line in plan_path.read_text(encoding="utf-8").splitlines():
        m = PLAN_HOLE_RE.match(line)
        if not m:
            continue
        holes.append(HoleTarget(hole_id=m.group(1), line=int(m.group(2))))
    return holes


def infer_primary_agda_target(base_task_text: str, repo_root: Path, directives: TodoDirectives) -> Optional[Path]:
    helper_paths: set[Path] = set()
    for helper in directives.helpers:
        try:
            helper_paths.add(resolve_repo_relative_path(repo_root, helper))
        except ValueError:
            continue

    for match in AGDA_PATH_RE.finditer(base_task_text):
        raw = match.group(1)
        path = Path(raw)
        try:
            resolved = resolve_repo_relative_path(repo_root, path)
        except ValueError:
            continue
        if resolved in helper_paths:
            continue
        if resolved.exists() and resolved.is_file():
            return resolved
    return None


def locate_hole_line(lines: list[str], preferred_line: int) -> Optional[int]:
    if preferred_line > 0 and preferred_line <= len(lines):
        idx = preferred_line - 1
        if "{!!}" in lines[idx]:
            return idx
    base = max(0, min(len(lines) - 1, preferred_line - 1))
    for dist in range(1, 41):
        left = base - dist
        right = base + dist
        if left >= 0 and "{!!}" in lines[left]:
            return left
        if right < len(lines) and "{!!}" in lines[right]:
            return right
    return None


def hole_lhs_key_from_line(line: str) -> Optional[str]:
    if "{!!}" not in line or "=" not in line:
        return None
    lhs = line.split("=", 1)[0]
    normalized = " ".join(lhs.split())
    return normalized or None


def locate_hole_line_by_lhs(lines: list[str], lhs_key: str) -> Optional[int]:
    for idx, line in enumerate(lines):
        if "{!!}" not in line:
            continue
        key = hole_lhs_key_from_line(line)
        if key == lhs_key:
            return idx
    return None


def build_hole_locators(plan_holes: list[HoleTarget], target_file: Optional[Path]) -> dict[str, HoleLocator]:
    locators: dict[str, HoleLocator] = {hole.hole_id: HoleLocator(line=hole.line, lhs_key=None) for hole in plan_holes}
    if target_file is None:
        return locators
    try:
        lines = target_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return locators
    for hole in plan_holes:
        idx = locate_hole_line(lines, hole.line)
        if idx is None:
            continue
        lhs_key = hole_lhs_key_from_line(lines[idx])
        locators[hole.hole_id] = HoleLocator(line=hole.line, lhs_key=lhs_key)
    return locators


def hole_is_cleared(target_file: Path, locator: HoleLocator) -> bool:
    try:
        lines = target_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return False

    if locator.lhs_key:
        for line in lines:
            if "=" not in line:
                continue
            lhs = " ".join(line.split("=", 1)[0].split())
            if lhs == locator.lhs_key:
                return "{!!}" not in line
        return False

    if locator.line > 0 and locator.line <= len(lines):
        return "{!!}" not in lines[locator.line - 1]

    return False


def blocked_comment_block(indent: str, worker_id: int, hole_id: str, blocker: str) -> list[str]:
    # Avoid accidentally closing the Agda block comment from blocker text.
    safe = blocker.replace("-}", "- }")
    body = safe.splitlines() or ["(no blocker details provided)"]
    out = [f"{indent}{{- BLOCKED[W{worker_id:02d}][{hole_id}]:\n"]
    for line in body:
        out.append(f"{indent}   {line}\n")
    out.append(f"{indent}-}}\n")
    return out


def add_blocked_comment_after_hole(
    target_file: Path,
    hole: HoleTarget,
    worker_id: int,
    blocker: str,
    locator: Optional[HoleLocator] = None,
) -> tuple[bool, str]:
    try:
        lines = target_file.read_text(encoding="utf-8").splitlines(keepends=True)
    except OSError as exc:
        return (False, f"Could not read hole target file: {exc}")
    if not lines:
        return (False, "Hole target file is empty.")

    hole_idx = None
    if locator and locator.lhs_key:
        hole_idx = locate_hole_line_by_lhs(lines, locator.lhs_key)
    if hole_idx is None:
        hole_idx = locate_hole_line(lines, hole.line)
    if hole_idx is None:
        return (False, f"Could not locate hole for {hole.hole_id} near line {hole.line}.")

    hole_line = lines[hole_idx]
    indent_match = re.match(r"^(\s*)", hole_line)
    indent = indent_match.group(1) if indent_match else ""
    comment_block = blocked_comment_block(indent, worker_id, hole.hole_id, blocker)
    insert_at = hole_idx + 1
    replace_start: Optional[int] = None
    replace_end: Optional[int] = None

    if insert_at < len(lines) and BLOCKED_LINE_COMMENT_RE.match(lines[insert_at]):
        replace_start = insert_at
        replace_end = insert_at + 1
    elif insert_at < len(lines) and BLOCKED_BLOCK_COMMENT_START_RE.match(lines[insert_at]):
        replace_start = insert_at
        end_idx = insert_at + 1
        while end_idx < len(lines):
            if "-}" in lines[end_idx]:
                end_idx += 1
                break
            end_idx += 1
        replace_end = end_idx

    if replace_start is not None and replace_end is not None:
        lines[replace_start:replace_end] = comment_block
    else:
        lines[insert_at:insert_at] = comment_block

    target_file.write_text("".join(lines), encoding="utf-8")
    return (True, "")


def build_hole_task_text(
    base_task_text: str,
    hole: HoleTarget,
    worker_id: int,
    worker_count: int,
) -> str:
    return (
        f"{base_task_text}\n\n"
        "Subtask assignment:\n"
        f"- Worker-ID: W{worker_id:02d} of {worker_count}\n"
        f"- Hole-ID: {hole.hole_id}\n"
        f"- Hole-Line: {hole.line}\n"
        "- Focus only on this hole and any directly required helper lemmas.\n"
        f"- If blocked, add a multi-line Agda comment directly below the hole in this exact shape:\n"
        f"  `{{- BLOCKED[W{worker_id:02d}][{hole.hole_id}]:` then the full blocker reason on following lines, then `-}}`."
    )


def format_directive_context(directives: TodoDirectives) -> str:
    extra: list[str] = []
    if directives.workers is not None:
        extra.append(f"Workers: {directives.workers}")
    if directives.plan is not None:
        extra.append(f"Plan: {directives.plan}")
    if directives.helpers:
        extra.append("Helpers: " + ", ".join(str(p) for p in directives.helpers))
    if not extra:
        return ""
    return "\n\nTask metadata:\n" + "\n".join(extra)


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
    normalized = block[:]
    while normalized and normalized[0].strip() == "":
        normalized.pop(0)
    while normalized and normalized[-1].strip() == "":
        normalized.pop()

    insert_at = section.start + 1
    if insert_at >= len(lines) or lines[insert_at].strip() != "":
        lines.insert(insert_at, "\n")

    item_start = insert_at + 1
    chunk: list[str] = normalized + ["\n"]
    lines[item_start:item_start] = chunk

    boundary = item_start + len(chunk)
    while boundary < len(lines) and lines[boundary].strip() == "":
        del lines[boundary]


def now_timestamp() -> str:
    return datetime.now().astimezone().strftime("%I:%M %p %Z %Y-%m-%d")


def upsert_item_metadata(lines: list[str], label: str, value: str) -> list[str]:
    out = lines[:]
    while out and out[-1].strip() == "":
        out.pop()
    needle = f"{label}:"
    for i, line in enumerate(out):
        if line.strip().startswith(needle):
            out[i] = f"  {label}: {value}\n"
            return out
    out.append(f"  {label}: {value}\n")
    return out


def ensure_started_timestamp(lines: list[str], started_at: str) -> list[str]:
    return upsert_item_metadata(lines, "Started", started_at)


def ensure_stopped_timestamp(lines: list[str], stopped_at: str) -> list[str]:
    return upsert_item_metadata(lines, "Stopped", stopped_at)


def short_text(text: str, limit: int = 160) -> str:
    normalized = " ".join(text.split())
    if len(normalized) <= limit:
        return normalized
    return normalized[: limit - 3].rstrip() + "..."


def worker_completion_description(outcome: TaskOutcome) -> str:
    if outcome.result.status == "success":
        if outcome.result.summary.strip():
            return short_text(outcome.result.summary)
        return "Completed assigned changes."
    if outcome.result.summary.strip():
        return short_text(outcome.result.summary)
    if outcome.result.blocker.strip():
        return "Attempt blocked: " + short_text(outcome.result.blocker)
    return "Attempt blocked."


def log_worker_completion(outcome: TaskOutcome, signature: str) -> None:
    hid = f" [{outcome.hole_id}]" if outcome.hole_id else ""
    wid = f" (W{outcome.worker_id:02d})" if outcome.worker_id is not None else ""
    status = "SUCCESS" if outcome.result.status == "success" else "BLOCKED"
    desc = worker_completion_description(outcome)
    print(f"{status}: {signature}{hid}{wid} - {desc}")


def commit_message_for_item(signature: str) -> str:
    one_line = " ".join(signature.split())
    if len(one_line) > 72:
        one_line = one_line[:72].rstrip()
    return f"todo: {one_line}"


def commit_message_for_hole(signature: str, hole_id: str) -> str:
    one_line = " ".join(signature.split())
    if len(one_line) > 56:
        one_line = one_line[:56].rstrip()
    return f"todo: {one_line} [{hole_id}]"


def stage_and_commit_paths(repo_root: Path, paths: set[Path], message: str) -> None:
    pathspecs = sorted(str(path) for path in paths)
    if not pathspecs:
        print("  commit: no changed paths; skipping commit")
        return

    run_checked(["git", "-C", str(repo_root), "add", "-A", "--", *pathspecs])
    staged = run_checked(["git", "-C", str(repo_root), "diff", "--cached", "--name-only", "--", *pathspecs]).stdout.strip()
    if not staged:
        print("  commit: no staged changes for this scope; skipping commit")
        return

    run_checked(["git", "-C", str(repo_root), "commit", "-m", message, "--", *pathspecs])
    print(f"  committed: {message}")


def stage_and_commit_item(repo_root: Path, todo_path: Path, outcome: TaskOutcome) -> None:
    todo_rel = todo_path.relative_to(repo_root)
    paths = set(outcome.touched_paths)
    paths.add(todo_rel)
    message = commit_message_for_item(outcome.item.signature)
    stage_and_commit_paths(repo_root, paths, message)


def build_prompt(todo_file: Path, task_text: str, directives: TodoDirectives) -> str:
    return (
        "You are executing one queued task from a TODO runner.\n"
        f"TODO file: {todo_file}\n\n"
        "Task:\n"
        f"{task_text}"
        f"{format_directive_context(directives)}\n\n"
        "Please attempt to complete this task in the repository.\n"
        "Do not edit the TODO file itself.\n"
        "Return only a JSON object that matches the provided schema.\n"
        "Set status to `success` only if the task is actually completed.\n"
        "Set status to `blocked` if you cannot complete it now, and provide a concrete blocker."
    )


def run_codex(
    todo_file: Path,
    task_text: str,
    directives: TodoDirectives,
    run_dir: Path,
    codex_cwd: Path,
    model: Optional[str],
    sandbox: str,
    approval: str,
    timeout_seconds: Optional[float],
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

    cmd = [
        "codex",
        "-C",
        str(codex_cwd),
        "-s",
        sandbox,
        "-a",
        approval,
        "exec",
        "--output-schema",
        str(schema_path),
        "-o",
        str(out_path),
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append(build_prompt(todo_file, task_text, directives))

    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        return RunResult(
            status="blocked",
            summary="Task attempt timed out.",
            blocker=f"codex exec exceeded timeout of {timeout_seconds} seconds.",
        )
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


def worker_worktree_dirs(base_dir: Path, parallel: int) -> list[Path]:
    if parallel <= 1:
        return [base_dir]
    return [base_dir.parent / f"{base_dir.name}-{i}" for i in range(1, parallel + 1)]


def run_task_attempt(
    *,
    item: TodoItem,
    todo_path: Path,
    repo_root: Path,
    run_dir: Path,
    worker_dir: Path,
    use_worktree: bool,
    model: Optional[str],
    sandbox: str,
    approval: str,
    timeout_seconds: Optional[float],
    dry_run: bool,
    parallel: int,
    task_text_override: Optional[str] = None,
    directives_override: Optional[TodoDirectives] = None,
    hole_target: Optional[HoleTarget] = None,
    worker_id: Optional[int] = None,
) -> TaskOutcome:
    task_text = extract_task_text(item) if task_text_override is None else task_text_override
    _body, parsed_directives = parse_item_body_and_directives(item)
    directives = directives_override if directives_override is not None else parsed_directives
    directive_error = validate_item_directives(directives, repo_root, parallel)
    if directive_error:
        return TaskOutcome(
            item=item,
            result=RunResult(
                status="blocked",
                summary="Invalid TODO directives.",
                blocker=directive_error,
            ),
            worker_dir=worker_dir,
            hole_id=hole_target.hole_id if hole_target else None,
            worker_id=worker_id,
        )

    if dry_run:
        result = RunResult(status="success", summary="Dry run: skipped codex execution.", blocker="")
        return TaskOutcome(
            item=item,
            result=result,
            worker_dir=worker_dir,
            hole_id=hole_target.hole_id if hole_target else None,
            worker_id=worker_id,
        )

    base_rev: Optional[str] = None
    if use_worktree:
        reset_worktree_to_head(repo_root, worker_dir)
        try:
            base_rev = run_checked(["git", "-C", str(worker_dir), "rev-parse", "HEAD"]).stdout.strip()
        except RuntimeError:
            base_rev = None
    codex_cwd = worker_dir if use_worktree else repo_root
    result = run_codex(todo_path, task_text, directives, run_dir, codex_cwd, model, sandbox, approval, timeout_seconds)
    return TaskOutcome(
        item=item,
        result=result,
        worker_dir=worker_dir,
        base_rev=base_rev,
        hole_id=hole_target.hole_id if hole_target else None,
        worker_id=worker_id,
    )


def reserve_next_item(todo_path: Path) -> Optional[TodoItem]:
    lines = read_lines(todo_path)
    todo_section = find_todo_section(lines)
    item = first_todo_item(lines, todo_section)
    if not item:
        return None
    started_at = now_timestamp()
    stamped_lines = ensure_started_timestamp(item.lines, started_at)
    item = TodoItem(start=item.start, end=item.end, lines=stamped_lines, signature=item.signature)
    del lines[item.start:item.end]
    in_progress = ensure_section(lines, "In progress TODO items")
    append_to_section(lines, in_progress, item.lines)
    write_lines(todo_path, lines)
    return item


def finalize_outcome(todo_path: Path, outcome: TaskOutcome, use_worktree: bool, *, emit_status_logs: bool = True) -> None:
    latest = read_lines(todo_path)
    current_item: Optional[TodoItem] = None
    in_progress = find_section_by_keyword(latest, "In progress TODO items")
    if in_progress:
        current_item = find_item(latest, in_progress, signature=outcome.item.signature)
    if not current_item:
        latest_todo = find_todo_section(latest)
        current_item = find_item(latest, latest_todo, signature=outcome.item.signature) or first_todo_item(
            latest, latest_todo
        )
    if not current_item:
        return

    stopped_at = now_timestamp()
    stamped_item = TodoItem(
        start=current_item.start,
        end=current_item.end,
        lines=ensure_stopped_timestamp(current_item.lines, stopped_at),
        signature=current_item.signature,
    )

    del latest[current_item.start:current_item.end]
    if outcome.result.status == "success":
        done_section = ensure_section(latest, "Completed TODO items")
        append_to_section(latest, done_section, mark_item_completed(stamped_item))
        if emit_status_logs:
            print(f"SUCCESS: {stamped_item.signature}")
            if use_worktree:
                print(f"  applied: copied {outcome.copied} path(s), removed {outcome.removed} path(s)")
    else:
        blocked_section = ensure_section(latest, "Blocked TODO items")
        append_to_section(latest, blocked_section, mark_item_blocked(stamped_item, outcome.result.blocker))
        if emit_status_logs:
            print(f"BLOCKED: {stamped_item.signature}")
            print(f"  blocker: {outcome.result.blocker}")
    write_lines(todo_path, latest)


def process_item_per_hole(
    item: TodoItem,
    todo_path: Path,
    repo_root: Path,
    run_dir: Path,
    worker_dirs: list[Path],
    use_worktree: bool,
    parallel: int,
    model: Optional[str],
    sandbox: str,
    approval: str,
    timeout_seconds: Optional[float],
    dry_run: bool,
) -> TaskOutcome:
    body_lines, directives = parse_item_body_and_directives(item)
    base_task_text = "\n".join(body_lines).strip()
    directive_error = validate_item_directives(directives, repo_root, parallel)
    if directive_error:
        return TaskOutcome(
            item=item,
            result=RunResult(status="blocked", summary="Invalid TODO directives.", blocker=directive_error),
            worker_dir=worker_dirs[0],
        )
    if directives.plan is None:
        return TaskOutcome(
            item=item,
            result=RunResult(
                status="blocked",
                summary="Per-hole mode requires a plan.",
                blocker="Missing `Plan:` directive for per-hole parallelism.",
            ),
            worker_dir=worker_dirs[0],
        )

    plan_path = resolve_repo_relative_path(repo_root, directives.plan)
    holes = parse_plan_holes(plan_path)
    if not holes:
        return TaskOutcome(
            item=item,
            result=RunResult(
                status="blocked",
                summary="No holes discovered in plan.",
                blocker=f"Could not parse hole IDs from plan file: {directives.plan}",
            ),
            worker_dir=worker_dirs[0],
        )

    worker_budget = directives.workers if directives.workers is not None else parallel
    worker_count = max(1, min(worker_budget, len(worker_dirs), len(holes)))
    todo_rel = todo_path.relative_to(repo_root)
    total_holes = len(holes)
    holes_by_id = {hole.hole_id: hole for hole in holes}
    primary_target = infer_primary_agda_target(base_task_text, repo_root, directives)
    hole_locators = build_hole_locators(holes, primary_target)

    hole_queue = holes[:]
    blocked: list[TaskOutcome] = []
    completed_count = 0
    blocked_count = 0
    submitted_count = 0
    last_heartbeat = time.time()

    def submit_hole(
        executor: concurrent.futures.ThreadPoolExecutor,
        futures: dict[concurrent.futures.Future[TaskOutcome], int],
        worker_idx: int,
        hole: HoleTarget,
    ) -> None:
        nonlocal submitted_count
        worker_id = worker_idx + 1
        print(f"RUNNING: {item.signature} [{hole.hole_id}] (W{worker_id:02d})")
        task_text = build_hole_task_text(base_task_text, hole, worker_id, worker_count)
        fut = executor.submit(
            run_task_attempt,
            item=item,
            todo_path=todo_path,
            repo_root=repo_root,
            run_dir=run_dir / f"worker-{worker_id}" / hole.hole_id,
            worker_dir=worker_dirs[worker_idx],
            use_worktree=use_worktree,
            model=model,
            sandbox=sandbox,
            approval=approval,
            timeout_seconds=timeout_seconds,
            dry_run=dry_run,
            parallel=parallel,
            task_text_override=task_text,
            directives_override=directives,
            hole_target=hole,
            worker_id=worker_id,
        )
        futures[fut] = worker_idx
        submitted_count += 1

    with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as executor:
        futures: dict[concurrent.futures.Future[TaskOutcome], int] = {}
        for worker_idx in range(worker_count):
            if not hole_queue:
                break
            submit_hole(executor, futures, worker_idx, hole_queue.pop(0))

        while futures:
            done, _pending = concurrent.futures.wait(
                futures.keys(),
                timeout=5.0,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            if not done:
                now = time.time()
                if now - last_heartbeat >= 15.0:
                    print(
                        f"PROGRESS: {item.signature} - completed {completed_count}/{total_holes}, "
                        f"blocked {blocked_count}, active {len(futures)}, remaining {len(hole_queue)}"
                    )
                    last_heartbeat = now
                continue
            for finished in done:
                worker_idx = futures.pop(finished)
                outcome = finished.result()
                completed_count += 1

                if use_worktree and outcome.result.status == "success":
                    try:
                        copied, removed, touched = apply_worktree_changes_to_main(
                            repo_root,
                            outcome.worker_dir,
                            excluded_relative={todo_rel},
                            base_rev=outcome.base_rev,
                        )
                        outcome.copied = copied
                        outcome.removed = removed
                        outcome.touched_paths = touched
                    except RuntimeError as exc:
                        outcome.result = RunResult(
                            status="blocked",
                            summary="Could not apply worktree changes to main tree.",
                            blocker=str(exc),
                        )

                if outcome.result.status == "success":
                    if use_worktree and not outcome.touched_paths:
                        hid = outcome.hole_id or "?"
                        outcome.result = RunResult(
                            status="blocked",
                            summary="No file changes were applied to the main checkout.",
                            blocker=f"Hole {hid} reported success but produced no applied file changes.",
                        )
                    elif primary_target is None:
                        hid = outcome.hole_id or "?"
                        outcome.result = RunResult(
                            status="blocked",
                            summary="Could not verify hole completion.",
                            blocker=f"Hole {hid} reported success, but the runner could not infer the main `.agda` target file.",
                        )
                    elif outcome.hole_id is not None:
                        hole = holes_by_id.get(outcome.hole_id)
                        locator = hole_locators.get(outcome.hole_id, HoleLocator(line=hole.line if hole else 0, lhs_key=None))
                        if hole is not None and not hole_is_cleared(primary_target, locator):
                            outcome.result = RunResult(
                                status="blocked",
                                summary="Assigned hole still unresolved.",
                                blocker=(
                                    f"Hole {hole.hole_id} at {primary_target}:{hole.line} "
                                    "still contains `{!!}` after the reported success."
                                ),
                            )
                    if use_worktree and outcome.result.status == "success" and outcome.touched_paths:
                        hid = outcome.hole_id or "hole"
                        msg = commit_message_for_hole(item.signature, hid)
                        stage_and_commit_paths(repo_root, outcome.touched_paths, msg)

                if (
                    outcome.result.status == "blocked"
                    and not dry_run
                    and primary_target is not None
                    and outcome.hole_id is not None
                    and outcome.worker_id is not None
                ):
                    hole = holes_by_id.get(outcome.hole_id)
                    if hole is not None:
                        wrote, detail = add_blocked_comment_after_hole(
                            primary_target,
                            hole,
                            outcome.worker_id,
                            outcome.result.blocker,
                            locator=hole_locators.get(outcome.hole_id),
                        )
                        if not wrote:
                            print(f"  note: could not record blocked comment for {outcome.hole_id}: {detail}")

                log_worker_completion(outcome, item.signature)
                if outcome.result.status == "blocked":
                    blocked.append(outcome)
                    blocked_count += 1

                if hole_queue:
                    submit_hole(executor, futures, worker_idx, hole_queue.pop(0))

    if blocked:
        blocked_ids = ", ".join((out.hole_id or "?") for out in blocked[:16])
        if len(blocked) > 16:
            blocked_ids += ", ..."
        blocker = f"Blocked holes: {blocked_ids}"
        return TaskOutcome(
            item=item,
            result=RunResult(
                status="blocked",
                summary=f"{len(blocked)} hole subtask(s) blocked.",
                blocker=blocker,
            ),
            worker_dir=worker_dirs[0],
        )

    return TaskOutcome(
        item=item,
        result=RunResult(
            status="success",
            summary=f"Completed {len(holes)} hole subtask(s).",
            blocker="",
        ),
        worker_dir=worker_dirs[0],
    )


def process_queue(
    todo_path: Path,
    repo_root: Path,
    run_dir: Path,
    worker_dirs: list[Path],
    use_worktree: bool,
    parallel: int,
    model: Optional[str],
    sandbox: str,
    approval: str,
    timeout_seconds: Optional[float],
    dry_run: bool,
) -> bool:
    first = reserve_next_item(todo_path)
    if not first:
        return False

    _body, first_directives = parse_item_body_and_directives(first)
    if first_directives.plan is not None:
        aggregate = process_item_per_hole(
            item=first,
            todo_path=todo_path,
            repo_root=repo_root,
            run_dir=run_dir,
            worker_dirs=worker_dirs,
            use_worktree=use_worktree,
            parallel=parallel,
            model=model,
            sandbox=sandbox,
            approval=approval,
            timeout_seconds=timeout_seconds,
            dry_run=dry_run,
        )
        finalize_outcome(todo_path, aggregate, use_worktree)
        if use_worktree and aggregate.result.status == "success":
            stage_and_commit_item(repo_root, todo_path, aggregate)
        return True

    workers = min(parallel, len(worker_dirs))
    todo_rel = todo_path.relative_to(repo_root)
    completed_items = 0
    blocked_items = 0
    last_heartbeat = time.time()

    def submit_for_worker(
        executor: concurrent.futures.ThreadPoolExecutor,
        futures: dict[concurrent.futures.Future[TaskOutcome], int],
        worker_idx: int,
        item: TodoItem,
    ) -> None:
        worker = worker_dirs[worker_idx]
        print(f"RUNNING: {item.signature}")
        fut = executor.submit(
            run_task_attempt,
            item=item,
            todo_path=todo_path,
            repo_root=repo_root,
            run_dir=run_dir / f"worker-{worker_idx + 1}",
            worker_dir=worker,
            use_worktree=use_worktree,
            model=model,
            sandbox=sandbox,
            approval=approval,
            timeout_seconds=timeout_seconds,
            dry_run=dry_run,
            parallel=parallel,
        )
        futures[fut] = worker_idx

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures: dict[concurrent.futures.Future[TaskOutcome], int] = {}
        submit_for_worker(executor, futures, 0, first)

        for worker_idx in range(1, workers):
            item = reserve_next_item(todo_path)
            if not item:
                break
            submit_for_worker(executor, futures, worker_idx, item)

        while futures:
            done, _pending = concurrent.futures.wait(
                futures.keys(),
                timeout=5.0,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            if not done:
                now = time.time()
                if now - last_heartbeat >= 15.0:
                    print(
                        f"PROGRESS: queue - completed {completed_items}, blocked {blocked_items}, "
                        f"active {len(futures)}"
                    )
                    last_heartbeat = now
                continue
            for finished in done:
                worker_idx = futures.pop(finished)
                outcome = finished.result()
                if outcome.result.status == "success":
                    completed_items += 1
                else:
                    blocked_items += 1

                if use_worktree and outcome.result.status == "success":
                    try:
                        copied, removed, touched = apply_worktree_changes_to_main(
                            repo_root,
                            outcome.worker_dir,
                            excluded_relative={todo_rel},
                            base_rev=outcome.base_rev,
                        )
                        outcome.copied = copied
                        outcome.removed = removed
                        outcome.touched_paths = touched
                    except RuntimeError as exc:
                        outcome.result = RunResult(
                            status="blocked",
                            summary="Could not apply worktree changes to main tree.",
                            blocker=str(exc),
                        )

                log_worker_completion(outcome, outcome.item.signature)
                finalize_outcome(todo_path, outcome, use_worktree, emit_status_logs=False)
                if use_worktree and outcome.result.status == "success":
                    stage_and_commit_item(repo_root, todo_path, outcome)

                next_item = reserve_next_item(todo_path)
                if next_item:
                    submit_for_worker(executor, futures, worker_idx, next_item)

    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Process TODO items with Codex, then move each to Completed or Blocked. Repeats until TODO is empty."
    )
    parser.add_argument("todo_file", type=Path, help="Path to the markdown TODO file.")
    parser.add_argument("--watch", action="store_true", help="Keep polling the TODO file until it is empty.")
    parser.add_argument("--interval-seconds", type=float, default=10.0, help="Polling interval for --watch mode.")
    parser.add_argument("--model", default=None, help="Optional model to pass to codex exec.")
    parser.add_argument("--sandbox", default="workspace-write", help="Sandbox mode for codex (`workspace-write`, etc.).")
    parser.add_argument(
        "--approval",
        default="never",
        help="Approval mode for codex (`never`, `on-request`, `untrusted`). Default is `never` for unattended runs.",
    )
    parser.add_argument(
        "--codex-timeout-seconds",
        type=float,
        default=1800.0,
        help="Timeout for each `codex exec` attempt. Use 0 or a negative value to disable timeout.",
    )
    parser.add_argument(
        "--worktree-dir",
        type=Path,
        default=Path(".codex-todo-worktree"),
        help="Path to the isolated worktree used for Codex execution.",
    )
    parser.add_argument(
        "--parallel",
        type=int,
        default=1,
        help="Number of concurrent workers processing TODO items.",
    )
    parser.add_argument(
        "--no-worktree",
        action="store_true",
        help="Disable isolated worktree mode and run Codex directly in the main tree.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Do not call codex; move items as if each task succeeded.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    todo_path = args.todo_file.resolve()
    if not todo_path.exists():
        print(f"TODO file not found: {todo_path}", file=sys.stderr)
        return 1
    try:
        repo_root = git_toplevel(todo_path.parent)
    except RuntimeError as exc:
        print(f"Could not determine git repository root: {exc}", file=sys.stderr)
        return 1
    ensure_path_within(repo_root, todo_path)

    run_dir = Path(".codex-todo-runner")
    timeout_seconds = args.codex_timeout_seconds if args.codex_timeout_seconds > 0 else None
    parallel = max(1, args.parallel)
    use_worktree = not args.no_worktree
    if parallel > 1 and not use_worktree:
        print("Parallel mode requires worktree mode. Remove `--no-worktree` or set `--parallel 1`.", file=sys.stderr)
        return 1

    worker_dirs: list[Path] = [repo_root]
    if use_worktree:
        base_worktree = (repo_root / args.worktree_dir).resolve()
        ensure_path_within(repo_root, base_worktree)
        worker_dirs = worker_worktree_dirs(base_worktree, parallel)
        for worker_dir in worker_dirs:
            ensure_path_within(repo_root, worker_dir)
            try:
                prepare_worktree(repo_root, worker_dir)
            except (RuntimeError, ValueError) as exc:
                print(f"Failed to prepare worktree `{worker_dir}`: {exc}", file=sys.stderr)
                return 1

    while True:
        try:
            processed = process_queue(
                todo_path=todo_path,
                repo_root=repo_root,
                run_dir=run_dir,
                worker_dirs=worker_dirs,
                use_worktree=use_worktree,
                parallel=parallel,
                model=args.model,
                sandbox=args.sandbox,
                approval=args.approval,
                timeout_seconds=timeout_seconds,
                dry_run=args.dry_run,
            )
        except (ValueError, RuntimeError) as exc:
            print(str(exc), file=sys.stderr)
            return 1

        if not processed:
            print("Completed all TODO items.")
            return 0


if __name__ == "__main__":
    raise SystemExit(main())

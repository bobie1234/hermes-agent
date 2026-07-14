#!/usr/bin/env python3
"""
Xiaoma Project Tools — read/write project documents, list ledger files,
and retrieve approved market/genre knowledge cards.

Registered under toolset "xiaoma_project".  Path security follows the same
resolve + relative_to pattern used by tools/path_security.py.
"""

import json
import fnmatch
import logging
import os
import re
import sys
import threading
from html import unescape
from pathlib import Path
from urllib.parse import quote_plus, urlparse, parse_qs, unquote
from urllib.request import Request, urlopen
from typing import Optional
from datetime import datetime, timezone

from packages.artifact_canonicalization import (
    CanonicalizationContext,
    canonicalize_artifact_content,
)
from packages.artifact_contract import ArtifactManifest
from packages.episode_outline_contract import (
    is_episode_outline_path,
    validate_episode_outline_content,
)
from packages.episode_revision_contract import (
    existing_episode_paths_from_snapshot_cache,
    normalize_episode_revision_target,
    validate_pending_episode_revision_paths,
)


def _ensure_runtime_root_on_syspath() -> None:
    """Ensure packaged runtime can import repo-root modules like packages.*."""
    candidates: list[Path] = []
    env_root = os.environ.get("XIAOMA_APP_ROOT", "").strip()
    if env_root:
        candidates.append(Path(env_root))

    mei = getattr(sys, "_MEIPASS", "")
    if mei:
        mei_path = Path(mei)
        candidates.append(mei_path)
        candidates.append(mei_path / "runtime" / "core")

    candidates.append(Path(__file__).resolve().parents[3])

    seen: set[Path] = set()
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except OSError:
            continue
        if resolved in seen:
            continue
        seen.add(resolved)
        if not (resolved / "packages").exists():
            continue
        candidate_str = str(resolved)
        if candidate_str not in sys.path:
            sys.path.insert(0, candidate_str)


_ensure_runtime_root_on_syspath()

from packages.knowledge.topic_profiles import canonicalize_topic, get_topic_profile
from tools.registry import registry, tool_error, tool_result

logger = logging.getLogger(__name__)
_EPISODE_CONTRACT_BLOCK_RE = re.compile(
    r"^\s*```episode_contract\s*\n(.*?)\n```\s*",
    re.DOTALL | re.IGNORECASE,
)
# Also accept contract block not at the very start of content (models
# sometimes prefix with "现在开始写第1集" before the fence).
_EPISODE_CONTRACT_BLOCK_SEARCH_RE = re.compile(
    r"(?:^|\n)\s*```episode_contract\s*\n(.*?)\n```\s*",
    re.DOTALL | re.IGNORECASE,
)

# ---------------------------------------------------------------------------
# Methodology index — unified knowledge retrieval (replaces fixed stitching)
# ---------------------------------------------------------------------------

try:
    from packages.knowledge.methodology_index import (
        build_methodology_index,
        query_index,
        conflict_check,
    )
    _METHODOLOGY_INDEX_AVAILABLE = True
except ImportError:
    _METHODOLOGY_INDEX_AVAILABLE = False
    logger.warning("methodology_index not available; falling back to fixed-file retrieval")

try:
    from packages.xiaoma_config import (
        PROJECTS_ROOT as _PROJECTS_ROOT,
        PROCESSED_ROOT as _KNOWLEDGE_ROOT,
        STABLE_ROOT as _STABLE_ROOT,
        REDFRUIT_ROOT as _REDFRUIT_ROOT,
        TOPIC_PACKS_ROOT as _TOPIC_PACKS_ROOT,
    )
except ImportError:
    import os
    from pathlib import Path
    _app_root = os.environ.get("XIAOMA_APP_ROOT", "")
    if _app_root:
        _base = Path(_app_root)
    else:
        _base = Path.cwd()
        logger.warning(
            "packages.xiaoma_config not importable and XIAOMA_APP_ROOT not set. "
            "Falling back to CWD: %s. Set XIAOMA_APP_ROOT for deterministic paths.",
            _base,
        )
    _PROJECTS_ROOT = _base / "data" / "projects"
    _KNOWLEDGE_ROOT = _base / "packages" / "knowledge" / "processed"
    _STABLE_ROOT = _base / "packages" / "knowledge" / "stable"
    _REDFRUIT_ROOT = _KNOWLEDGE_ROOT / "redfruit-2026-05"
    _TOPIC_PACKS_ROOT = _KNOWLEDGE_ROOT / "topic-packs"

# ---------------------------------------------------------------------------
# Security helpers (inline; avoids importing the full security module for
# what amounts to two function calls, but keeps the same semantics).
# ---------------------------------------------------------------------------

_MAX_CARD_CHARS = 5000
_MAX_CARD_SUMMARY_CHARS = 900
from xiaoma.episode_quality_contract import (
    MIN_EPISODE_CHARS,
    MAX_EPISODE_CHARS,
)
_WRITE_POLICIES_BY_THREAD: dict[int, dict] = {}
_METHODOLOGY_TRACES_BY_THREAD: dict[int, dict] = {}
_CANCELLED_PROJECTS: set[str] = set()
_CANCEL_LOCK = threading.Lock()

# A-EXECUTE-REALTIME-PROGRESS-SSE-01：进度 hook（agent 工具调用时触发）
# orchestrator 注册一个回调，工具调用时推进度给前端（通过 SSE）
_PROGRESS_SINK = None
# A-Streaming-01 打假修复：线程级当前 page（per-thread dict 隔离并发），供 _emit_artifact_event 注入 page 字段
_ACTIVE_PAGES_BY_THREAD: dict[int, str] = {}
# Artifact identity is scoped to a run, not to the worker thread. A single
# run can execute several episode batches on different threads, and resetting
# a thread counter made every batch reuse artifact_id=...-1.
_ARTIFACT_SEQUENCE_BY_THREAD: dict[int, int] = {}
_ARTIFACT_SEQUENCE_BY_RUN: dict[str, int] = {}
_ARTIFACT_SEQUENCE_LOCK = threading.Lock()


def _next_artifact_sequence(run_id: str = "") -> int:
    """Allocate a unique sequence within one run, safely across threads."""
    normalized_run_id = str(run_id or "").strip()
    if normalized_run_id:
        with _ARTIFACT_SEQUENCE_LOCK:
            seq = _ARTIFACT_SEQUENCE_BY_RUN.get(normalized_run_id, 0) + 1
            _ARTIFACT_SEQUENCE_BY_RUN[normalized_run_id] = seq
            return seq
    tid = threading.get_ident()
    with _ARTIFACT_SEQUENCE_LOCK:
        seq = _ARTIFACT_SEQUENCE_BY_THREAD.get(tid, 0) + 1
        _ARTIFACT_SEQUENCE_BY_THREAD[tid] = seq
        return seq


def _reset_artifact_sequence() -> None:
    """Reset the legacy no-run fallback counter for the current thread."""
    with _ARTIFACT_SEQUENCE_LOCK:
        _ARTIFACT_SEQUENCE_BY_THREAD.pop(threading.get_ident(), None)


def clear_artifact_sequence_for_run(run_id: str) -> None:
    """Release the run-scoped identity counter after the run is complete."""
    normalized_run_id = str(run_id or "").strip()
    if not normalized_run_id:
        return
    with _ARTIFACT_SEQUENCE_LOCK:
        _ARTIFACT_SEQUENCE_BY_RUN.pop(normalized_run_id, None)


def _build_artifact_manifest(
    *,
    run_id: str,
    sequence: int,
    project_id: str,
    page: str,
    path: str,
    kind: str,
    content: str,
    artifact_id: str = "",
) -> ArtifactManifest:
    """Allocate one immutable manifest for collect and direct write events."""
    return ArtifactManifest.create(
        run_id=run_id,
        artifact_id=artifact_id,
        sequence=sequence,
        project_id=project_id,
        page=page,
        path=path,
        kind=kind,
        content=content,
    )


def _hermes_canonicalization_context(project_id: str) -> CanonicalizationContext:
    """Build a CanonicalizationContext backed by Hermes ``_resolve_project_path``.

    Hermes can read local project files during collect, so the normalizer
    can fill in ``base_content_hash`` / ``old_content`` from the actual
    episode files on disk. Desktop backend runs do not share the sidecar's
    workspace directory, so the snapshot cache is the authoritative fallback
    for the target episode in collect mode.
    """

    snapshot_cache = _active_workspace_snapshot_cache()
    snapshot_files = snapshot_cache.get("files") if isinstance(snapshot_cache.get("files"), dict) else {}

    def _read_file(path: str) -> str:
        normalized = str(path or "").replace("\\", "/").strip().strip("/")
        if normalized in snapshot_files:
            return str(snapshot_files[normalized] or "")
        resolved = _resolve_project_path(project_id, path)
        if resolved is None or not resolved.exists():
            raise FileNotFoundError(f"episode file not found: {path}")
        return resolved.read_text(encoding="utf-8")

    def _resolve_file(path: str) -> Optional[str]:
        normalized = str(path or "").replace("\\", "/").strip().strip("/")
        if normalized in snapshot_files:
            return normalized
        resolved = _resolve_project_path(project_id, path)
        return str(resolved) if resolved is not None else None

    return CanonicalizationContext(
        read_file_content=_read_file,
        resolve_file_path=_resolve_file,
    )


def set_progress_sink(callback):
    """注册进度回调（orchestrator 在跑 agent 前调）。callback(dict) → 被 orchestrator 的 SSE 推给前端。"""
    global _PROGRESS_SINK
    _PROGRESS_SINK = callback

def clear_progress_sink():
    global _PROGRESS_SINK
    _PROGRESS_SINK = None

def set_active_page(page: str):
    _ACTIVE_PAGES_BY_THREAD[threading.get_ident()] = page

def clear_active_page():
    _ACTIVE_PAGES_BY_THREAD.pop(threading.get_ident(), None)

def active_page() -> str:
    return _ACTIVE_PAGES_BY_THREAD.get(threading.get_ident(), "")

def _emit_progress(action: str, path: str):
    """工具调用时触发进度信号。翻译表内置——绝不暴露 skill/tool/路径。"""
    if _PROGRESS_SINK is None:
        return
    msg = _translate_tool_to_progress(action, path)
    if msg:
        try:
            _PROGRESS_SINK({"progress": msg, "action": action, "path": path})
        except Exception:
            pass  # 进度推送失败不影响主流程


def _emit_artifact_commit(
    project_id: str,
    path: str,
    content: str,
    *,
    manifest: ArtifactManifest | None = None,
):
    """发出 artifact_commit 事件。直接写盘模式下调用。manifest 由写盘逻辑一次性构造。"""
    _emit_artifact_event("artifact_commit", project_id, path, content, manifest=manifest)


def _emit_artifact_ready(
    project_id: str,
    path: str,
    content: str,
    *,
    manifest: ArtifactManifest | None = None,
):
    """发出 artifact_ready 事件。collect 模式下调用。manifest 由 collect 逻辑一次性构造。"""
    _emit_artifact_event("artifact_ready", project_id, path, content, manifest=manifest)


def _emit_artifact_event(
    event_type: str,
    project_id: str,
    path: str,
    content: str,
    *,
    manifest: ArtifactManifest | None = None,
):
    """统一发出 artifact 事件。

    identity 字段由调用方通过 ``manifest`` 一次性传入，本函数不再自行分配
    sequence / artifact_id / content_hash。``manifest`` 缺失时仅用于 display
    事件（start/delta/replace），lifecycle 事件（ready/commit/failed）必须
    携带完整 manifest，否则不发送。
    """
    if _PROGRESS_SINK is None:
        return
    page = active_page()

    # Display events can run without manifest; lifecycle events MUST have one
    is_lifecycle = event_type in {"artifact_ready", "artifact_commit", "artifact_failed"}
    if is_lifecycle and manifest is None:
        # Lifecycle event without manifest — protocol violation, do not send
        return

    # Build event from manifest when available
    if manifest is not None:
        event = manifest.to_event(
            event_type,
            content=content if event_type in {"artifact_ready", "artifact_commit"} else None,
        )
    else:
        event: dict = {"type": event_type}
        # Display event — minimal identity from trace for association
        trace = _active_methodology_trace() or {}
        run_id = str(trace.get("run_id") or "")
        seq = _next_artifact_sequence(run_id)
        event.update({
            "schema_version": 1,
            "run_id": run_id,
            "artifact_id": f"art-{run_id}-{seq}" if run_id else f"art-local-{seq}",
            "sequence": seq,
        })

        # Always inject page and content for display events
        event["page"] = page
        event["content"] = content

    try:
        _PROGRESS_SINK(event)
    except Exception:
        pass


def _infer_artifact_kind(path: str) -> str:
    normalized = str(path or "").replace("\\", "/").strip("/")
    # New format: characters/01.md
    if normalized.startswith("characters/") and normalized.endswith(".md") and not normalized.startswith("characters/00-"):
        return "character_card"
    if re.fullmatch(r"outline_variants/[45]/outline\.md", normalized):
        return "outline_stage"
    if re.fullmatch(r"outline_variants/[45]/episode_outline\.json", normalized):
        return "episode_outline"
    if normalized.startswith("episodes/ep") and normalized.endswith(".md"):
        return "episode_body"
    return "generic"

def _translate_tool_to_progress(action: str, path: str) -> str:
    """工具调用 → 用户语言翻译表。核心：绝不暴露内部词。"""
    p = str(path or "").replace("\\", "/").strip()
    if action == "read":
        if "project_brief" in p: return "正在回顾灵感设定"
        if "synopsis" in p: return "正在回顾故事梗概"
        if "outline" in p: return "正在回顾故事大纲"
        if p.startswith("characters/"): return "正在回顾人物设定"
        if p.startswith("episodes/"): return "正在回顾已有剧集"
        if p.startswith("ledger/"): return "正在整理连续性记录"
        if p.rstrip("/") == "episodes": return "正在整理已写剧集"
        if p.rstrip("/") == "characters": return "正在整理人物列表"
        return "正在读取项目内容"
    elif action == "write":
        if p.startswith("episodes/ep"):
            # ep022 → 本轮第N集（从 ep 号算本轮序号，需要 external context）
            # 简化：直接用集号 - base + 1，但 base 未知，这里只返回"正在写入剧集"
            return "正在写入剧集"
        if "project_brief" in p: return "正在生成灵感总结"
        if "synopsis" in p: return "正在生成故事梗概"
        if "outline" in p: return "正在生成故事大纲"
        if p.startswith("characters/"): return "正在生成人物设定"
        return "正在写入内容"
    elif action == "list":
        return "正在整理项目内容"
    elif action == "skill":
        return "正在构思剧情"
    return ""


def mark_project_cancelled(project_id: str) -> None:
    """Best-effort cancellation gate for long-running project writes."""
    if not project_id:
        return
    with _CANCEL_LOCK:
        _CANCELLED_PROJECTS.add(str(project_id))


def clear_project_cancelled(project_id: str) -> None:
    if not project_id:
        return
    with _CANCEL_LOCK:
        _CANCELLED_PROJECTS.discard(str(project_id))


def _is_project_cancelled(project_id: str) -> bool:
    with _CANCEL_LOCK:
        return str(project_id) in _CANCELLED_PROJECTS


def start_methodology_trace(
    run_id: str,
    project_id: str,
    page: str,
    expected_skills: list[str] | None = None,
) -> None:
    """Start a per-thread methodology trace for one Hermes run."""
    set_active_page(page)
    _METHODOLOGY_TRACES_BY_THREAD[threading.get_ident()] = {
        "run_id": run_id,
        "project_id": project_id,
        "page": page,
        "expected_skills": expected_skills or [],
        "skills_loaded": [],
        "cards_retrieved": [],
        "rules_conflicts": [],
        "project_docs_read": [],
        "project_docs_written": [],
        "project_docs_listed": [],
        "ledger_docs_read": [],
        "warnings": [],
        "tool_failure_counts": {},
        "episode_write_attempts": [],
    }


def consume_methodology_trace() -> dict:
    """Return and clear the current thread's methodology trace."""
    return _METHODOLOGY_TRACES_BY_THREAD.pop(threading.get_ident(), {})


def _active_methodology_trace() -> Optional[dict]:
    return _METHODOLOGY_TRACES_BY_THREAD.get(threading.get_ident())


def _append_unique_trace_list(key: str, value) -> None:
    trace = _active_methodology_trace()
    if trace is None:
        return
    bucket = trace.setdefault(key, [])
    if value not in bucket:
        bucket.append(value)


# 非剧集生成任务的重复工具错误保险。剧集正文每集只允许一次提交，
# 第一次失败也必须结束当前内层回合，由外层继续调度下一集。
STOP_LOSS_FAILURE_LIMIT = 5


def _tool_failure(tool_name: str, project_id: str, message: str) -> str:
    """Record repeated tool failures and stop a run after STOP_LOSS_FAILURE_LIMIT.

    A-STOPLOSS-THRESHOLD-BLACKBOX-01（根因级修法，波别 2026-06-15）：
    旧逻辑连续失败超阈值后 `mark_project_cancelled` 取消整个 project，
    导致同 run 已成功的其他集（如 ep016-018）被连累——"一集失败陪葬全轮"。
    现改为：超阈值只停止该工具的继续重试（return error + warning），
    **不再 mark_project_cancelled**，同 run 其他未失败文件不受连累。
    额度保护仍由"单次工具失败计数 + 超限停止重试"保证（每次失败消耗一次
    模型调用，超限后该工具停止，不会无限消耗）。project 级 cancel 只留给
    真正的致命故障（os/系统层），不因单文件字数失败触发。
    """
    trace = _active_methodology_trace()
    if trace is None:
        return tool_error(message)

    counts = trace.setdefault("tool_failure_counts", {})
    count = int(counts.get(tool_name, 0) or 0) + 1
    counts[tool_name] = count
    policy = active_project_write_policy() or {}
    if (
        tool_name == "write_project_doc"
        and str(policy.get("page") or "") == "episodes"
        and str(policy.get("action_intent") or "") in {"preset_execute", "custom_execute"}
    ):
        _append_unique_trace_list("warnings", f"episode_write_rejected_once: {message}")
        # 剧集单集回合：第一次写工具失败就结束当前内层回合，禁止 5 次重试。
        # 外层 orchestrator 继续调度后续集；已成功集不受影响。
        trace["tool_hard_stop"] = {
            "tool": tool_name,
            "reason": "episode_write_rejected_once",
        }
        trace["failure_stage"] = "episode_write_rejected"
        trace["completion_reached"] = False
        return tool_error(message, stop_current_turn=True)
    if count >= STOP_LOSS_FAILURE_LIMIT:
        _append_unique_trace_list(
            "warnings",
            f"tool_failure_stop_loss: {tool_name} failed {count}/{STOP_LOSS_FAILURE_LIMIT} times (single-file stop, run preserved)",
        )
        trace["tool_hard_stop"] = {
            "tool": tool_name,
            "reason": "stop_loss",
        }
        trace["failure_stage"] = "write_stop_loss"
        trace["completion_reached"] = False
        return tool_error(
            f"该文件已连续写入失败 {STOP_LOSS_FAILURE_LIMIT} 次，停止重试此文件。"
            "其他文件不受影响，请修正本次错误后重试该文件。"
        )
    return tool_error(message)


def record_skill_loaded(name: str, path: str | None = None) -> None:
    item = {"name": name}
    if path:
        item["path"] = path
    _append_unique_trace_list("skills_loaded", item)


def _record_cards_retrieved(args: dict, cards: list[dict], conflicts: list[dict]) -> None:
    trace = _active_methodology_trace()
    if trace is None:
        return
    for card in cards:
        item = {
            "id": card.get("id"),
            "path": card.get("path"),
            "priority": card.get("priority"),
            "score": card.get("score"),
            "reason": card.get("reason"),
            "query": {
                "stage": args.get("stage"),
                "format": args.get("format"),
                "topic": args.get("topic"),
                "audience": args.get("audience"),
                "task": args.get("task"),
                "problem": args.get("problem"),
            },
        }
        _append_unique_trace_list("cards_retrieved", item)
    for conflict in conflicts or []:
        _append_unique_trace_list("rules_conflicts", conflict)


def set_project_write_policy(policy: dict | None) -> None:
    """Set write policy for the current agent execution thread."""
    thread_id = threading.get_ident()
    if policy is None:
        _WRITE_POLICIES_BY_THREAD.pop(thread_id, None)
    else:
        _WRITE_POLICIES_BY_THREAD[thread_id] = policy


def clear_project_write_policy() -> None:
    _WRITE_POLICIES_BY_THREAD.pop(threading.get_ident(), None)


def active_project_write_policy() -> Optional[dict]:
    return _WRITE_POLICIES_BY_THREAD.get(threading.get_ident())


def _active_workspace_snapshot_cache() -> dict:
    policy = active_project_write_policy() or {}
    cache = policy.get("workspace_snapshot_cache")
    return cache if isinstance(cache, dict) else {}


def _normalize_project_doc_trace_path(path: str, *, is_dir: bool = False) -> str:
    raw = str(path or "").strip().replace("\\", "/")
    if raw in {"", ".", "/", "./"}:
        return "."
    normalized = raw.strip("/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    if not normalized:
        return "."
    return f"{normalized.rstrip('/')}/" if is_dir else normalized.rstrip("/")


def _project_doc_read_satisfies(required_path: str, read_docs: list[str] | tuple[str, ...]) -> bool:
    required = _normalize_project_doc_trace_path(
        required_path,
        is_dir=str(required_path or "").replace("\\", "/").strip().endswith("/"),
    )
    read_set = {
        _normalize_project_doc_trace_path(path)
        for path in (read_docs or [])
        if str(path or "").strip()
    }
    if required in read_set:
        return True
    if required.endswith("/"):
        return any(path.startswith(required) and path != required for path in read_set)
    return False


def _path_allowed_by_policy(project_id: str, path: str) -> Optional[str]:
    policy = active_project_write_policy()
    if not policy or policy.get("project_id") != project_id:
        return None
    if policy.get("mode") == "deny":
        return policy.get("message") or "当前流程不允许直接写项目文件"
    required_reads = [str(item).strip() for item in (policy.get("required_reads_before_write") or []) if str(item).strip()]
    if required_reads:
        trace = _active_methodology_trace() or {}
        # 预载进 system_message 的文档 agent 已经看到（_build_execute_preloaded_reads
        # 把 ledger/ 等前置正文拼进 system_message），等价于"已读"，必须合并进来。
        # 否则会出现"内容已塞给 agent、却因 agent 没主动调 read 被拦死写集"的问题。
        preloaded = [
            _normalize_project_doc_trace_path(str(item))
            for item in (policy.get("preloaded_reads") or [])
            if str(item).strip()
        ]
        read_docs = [
            _normalize_project_doc_trace_path(str(item))
            for item in (trace.get("project_docs_read") or [])
        ] + preloaded
        missing_reads = []
        for item in required_reads:
            # 目录型 required（如 ledger/）：项目里该目录不存在（老项目没生成过账本/
            # 约束书，它们是生成大纲时才自动产出）→ 不强制读，避免误拦写集。
            if item.endswith("/"):
                try:
                    if not (_PROJECTS_ROOT / project_id / item.rstrip("/")).exists():
                        continue
                except OSError:
                    continue
            if not _project_doc_read_satisfies(item, read_docs):
                missing_reads.append(item)
        if missing_reads:
            return f"写入前必须先读取：{', '.join(missing_reads)}"
    specific_writes = [
        _normalize_project_doc_trace_path(str(item))
        for item in (policy.get("allowed_specific_writes") or [])
        if str(item).strip()
    ]
    normalized_path = _normalize_project_doc_trace_path(path)
    if specific_writes and not any(
        normalized_path == item or fnmatch.fnmatch(normalized_path, item)
        for item in specific_writes
    ):
        # 超出本轮 specific-write 范围 —— 这是"集号/批次超范围"，
        # 不是"越页面"。必须给 agent 一条带具体允许文件的专属文案，
        # 让它自纠到范围内的集，而不是套用 policy.message（那条是为
        # "越 allowed_paths 页面"写的，会把 agent 带沟里）。
        return (
            f"本轮只允许写这些文件：{', '.join(specific_writes)}；"
            f"你写的 {normalized_path} 超出本轮范围。"
            f"请改写允许范围内的文件，不要写范围外的集号或路径。"
        )
    allowed = policy.get("allowed_paths") or []
    for item in allowed:
        item = str(item).strip()
        if not item:
            continue
        if item.endswith("/"):
            if path.startswith(item):
                return None
        elif path == item:
            return None
    return (
        policy.get("message")
        or f"当前页面只允许写入：{', '.join(allowed)}；拒绝越级写入 {path}"
    )

_STAGE_FILES = {
    "inspiration": [
        "cards-index.md",
        "trend-brief.md",
        "genre-opportunity-matrix.md",
        "platform-trends/CARD-TREND-001-ai-manhua-mainstage.md",
        "platform-trends/CARD-TREND-002-female-ai-gap.md",
        "platform-trends/CARD-TREND-012-format-choice.md",
        "platform-trends/CARD-TREND-013-good-to-do-matrix.md",
    ],
    "synopsis": [
        "platform-trends/CARD-TREND-009-first-three-episodes.md",
        "platform-trends/CARD-TREND-010-ip-seriality.md",
        "manhua-opening-hooks/CARD-MANHUA-OPENING-001-shock-contrast.md",
        "manhua-opening-hooks/CARD-MANHUA-OPENING-002-extreme-crisis.md",
        "manhua-opening-hooks/CARD-MANHUA-OPENING-005-hybrid-hook.md",
        "ad-materials/CARD-AD-003-identity-contrast.md",
        "ad-materials/CARD-AD-010-power-reversal.md",
    ],
    "outline": [
        "manhua-rhythm/CARD-MANHUA-RHYTHM-001-ai-real.md",
        "manhua-rhythm/CARD-MANHUA-RHYTHM-004-female.md",
        "manhua-rhythm/CARD-MANHUA-RHYTHM-005-selfcheck.md",
        "platform-trends/CARD-TREND-009-first-three-episodes.md",
        "ad-materials/CARD-AD-002-visual-spectacle.md",
    ],
    "episodes": [
        "manhua-rhythm/CARD-MANHUA-RHYTHM-001-ai-real.md",
        "manhua-rhythm/CARD-MANHUA-RHYTHM-005-selfcheck.md",
        "ad-materials/CARD-AD-001-rule-reveal.md",
        "ad-materials/CARD-AD-002-visual-spectacle.md",
        "ad-materials/CARD-AD-004-premonition-planning.md",
        "ad-materials/CARD-AD-009-safehouse-comfort.md",
    ],
}

_STABLE_STAGE_FILES = {
    "inspiration": [
        "redfruit-four-stage-structure-2026-05.md",
        "redfruit-first-episode-hook-rules-2026-05.md",
        "redfruit-realistic-plot-power-rules-2026-05.md",
        "first-three-episode-scorecard-2026-05.md",
        "hook-and-reversal-rules-2026-05.md",
        "character-empathy-rules-2026-05.md",
    ],
    "synopsis": [
        "short-drama-compliance-hard-rules-2026-05.md",
        "redfruit-four-stage-structure-2026-05.md",
        "redfruit-first-episode-hook-rules-2026-05.md",
        "redfruit-cheat-layering-rules-2026-05.md",
        "redfruit-antagonist-tier-rules-2026-05.md",
        "redfruit-realistic-plot-power-rules-2026-05.md",
        "first-three-episode-scorecard-2026-05.md",
        "plot-density-rules-2026-05.md",
        "hook-and-reversal-rules-2026-05.md",
        "character-empathy-rules-2026-05.md",
    ],
    "outline": [
        "short-drama-compliance-hard-rules-2026-05.md",
        "redfruit-four-stage-structure-2026-05.md",
        "redfruit-cheat-layering-rules-2026-05.md",
        "redfruit-antagonist-tier-rules-2026-05.md",
        "redfruit-ad-material-rules-2026-05.md",
        "first-three-episode-scorecard-2026-05.md",
        "plot-density-rules-2026-05.md",
        "hook-and-reversal-rules-2026-05.md",
        "character-empathy-rules-2026-05.md",
    ],
    "episodes": [
        "script-format-rules-2026-05.md",
        "short-drama-compliance-hard-rules-2026-05.md",
        "redfruit-four-stage-structure-2026-05.md",
        "redfruit-first-episode-hook-rules-2026-05.md",
        "redfruit-cheat-layering-rules-2026-05.md",
        "redfruit-antagonist-tier-rules-2026-05.md",
        "redfruit-ad-material-rules-2026-05.md",
        "first-three-episode-scorecard-2026-05.md",
        "plot-density-rules-2026-05.md",
        "hook-and-reversal-rules-2026-05.md",
        "character-empathy-rules-2026-05.md",
    ],
}

_PROCESSED_STAGE_FILES = {
    "inspiration": [
        "female-first-ten-episodes-beat-sheet-2026-05.md",
        "male-superpower-revenge-first-three-episodes-2026-05.md",
    ],
    "synopsis": [
        "female-first-ten-episodes-beat-sheet-2026-05.md",
        "male-superpower-revenge-first-three-episodes-2026-05.md",
    ],
    "outline": [
        "female-first-ten-episodes-beat-sheet-2026-05.md",
        "male-superpower-revenge-first-three-episodes-2026-05.md",
    ],
    "episodes": [
        "female-first-ten-episodes-beat-sheet-2026-05.md",
        "male-superpower-revenge-first-three-episodes-2026-05.md",
    ],
}

_PATTERN_STAGE_FILES = {
    "inspiration": [
        "patterns/audience-emotion-map.md",
        "patterns/archetype-library.md",
    ],
    "synopsis": [
        "patterns/audience-emotion-map.md",
        "patterns/archetype-library.md",
        "patterns/worldbuilding-atlas.md",
    ],
    "outline": [
        "patterns/pacing-atlas.md",
        "patterns/worldbuilding-atlas.md",
        "patterns/ad-material-atlas.md",
    ],
    "episodes": [
        "patterns/pacing-atlas.md",
        "patterns/ad-material-atlas.md",
    ],
}

_TOPIC_CASE_FILES = {
    "xianxia": [
        "blockbuster-cases/CASE-BLOCKBUSTER-009-shanhai-cangxu.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-006-fanren-baishishu.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-008-xianwo-feigen.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-010-wotinei-youtiaolong.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-001-wanyao-tuluzhuan-s5.md",
    ],
    "rule-horror-infinite": [
        "blockbuster-cases/CASE-BLOCKBUSTER-011-rixin-yiwan.md",
    ],
    "female-housefight-rebirth": [
        "blockbuster-cases/CASE-BLOCKBUSTER-003-buzheng-fengyue.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-013-chuancheng-paohui.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-018-chongsheng70.md",
    ],
    "family-comedy": [
        "blockbuster-cases/CASE-BLOCKBUSTER-007-datang-sizi.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-016-tiaopi-lebao.md",
    ],
    "professional-romance": [
        "blockbuster-cases/CASE-BLOCKBUSTER-002-shangan-zhanwo.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-012-lihun-renqin.md",
        "blockbuster-cases/CASE-BLOCKBUSTER-017-zhaoxue-jiche.md",
    ],
}

_TOPIC_STAGE_FILES = {
    "inspiration": ["README.md", "brainholes.md", "case-index.md", "pitfalls.md"],
    "synopsis": ["README.md", "first-3-episodes.md", "character-hooks.md", "brainholes.md"],
    "outline": ["README.md", "first-3-episodes.md", "tropes.md", "plot-modules.md", "punch-modules.md", "scene-and-visual.md"],
    "episodes": ["first-3-episodes.md", "plot-modules.md", "punch-modules.md", "scene-and-visual.md", "pitfalls.md"],
}


def _resolve_project_path(project_id: str, path: str) -> Optional[Path]:
    """Resolve a project-relative path and validate it stays within bounds.

    Uses WorkspacePathResolver to enforce:
      - No path traversal (relative_to check)
      - Only allowed file extensions and paths
      - No absolute paths or outside-workspace writes

    Returns the absolute Path if safe, or None on violation.
    """
    try:
        from packages.workspace_resolver import resolve_project_path as _resolver
        return _resolver(project_id, path, projects_root=_PROJECTS_ROOT)
    except ImportError:
        pass

    # Fallback: basic traversal protection (when resolver module unavailable)
    project_root = (_PROJECTS_ROOT / project_id).resolve()
    target = (project_root / path).resolve()
    try:
        target.relative_to(project_root)
    except ValueError:
        return None
    return target


def _check_project_id(project_id: str) -> Optional[str]:
    """Reject project IDs with path-traversal components.

    Returns an error message string or None if the ID is safe.
    """
    if not project_id or not project_id.strip():
        return "project_id is required"
    # Block obvious traversal and separator injection
    forbidden = {"..", "/", "\\", "\x00"}
    if any(c in project_id for c in forbidden):
        return f"Invalid project_id: {project_id!r}"
    return None


def _clean_markdown_for_workspace(text: str) -> str:
    """Keep generated project docs readable in the UI editor."""
    lines = []
    table_rule = re.compile(r"^\s*\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?\s*$")
    for raw_line in text.replace("\r\n", "\n").split("\n"):
        line = raw_line
        if re.match(r"^\s*-{3,}\s*$", line) or table_rule.match(line):
            continue
        line = re.sub(r"^\s{0,3}#{1,6}\s*", "", line)
        line = re.sub(r"\*\*([^*]+)\*\*", r"\1", line)
        line = re.sub(r"__([^_]+)__", r"\1", line)
        line = re.sub(r"`([^`]+)`", r"\1", line)
        line = re.sub(r"^\s*[-*+]\s+", "", line)
        line = re.sub(r"^\s*\d+\.\s+", "", line)
        lines.append(line)
    return re.sub(r"\n{3,}", "\n\n", "\n".join(lines)).lstrip()


def _normalize_topic(topic: str) -> str:
    return canonicalize_topic(topic)


def _read_knowledge_file(base: Path, relative_path: str) -> Optional[dict]:
    target = (base / relative_path).resolve()
    try:
        target.relative_to(base.resolve())
    except ValueError:
        return None
    if not target.exists() or not target.is_file():
        return None
    try:
        return {
            "path": str(target.relative_to(_KNOWLEDGE_ROOT)),
            "content": target.read_text(encoding="utf-8").strip(),
        }
    except (OSError, UnicodeDecodeError):
        return None


def _read_stable_file(relative_path: str) -> Optional[dict]:
    target = (_STABLE_ROOT / relative_path).resolve()
    try:
        target.relative_to(_STABLE_ROOT.resolve())
    except ValueError:
        return None
    if not target.exists() or not target.is_file():
        return None
    try:
        return {
            "path": str(target.relative_to(_STABLE_ROOT.parent)),
            "content": target.read_text(encoding="utf-8").strip(),
        }
    except (OSError, UnicodeDecodeError):
        return None


def _append_card(cards: list, card: Optional[dict], budget: int) -> int:
    if not card or not card.get("content"):
        return budget
    summary = _compact_card_content(card["content"], budget)
    cards.append({
        "path": card["path"],
        "summary": summary,
        "truncated": len(card["content"]) > len(summary),
    })
    return budget - len(summary)


def _compact_card_content(content: str, budget: int) -> str:
    """Return a bounded, readable card excerpt for model context."""
    max_chars = max(0, min(budget, _MAX_CARD_SUMMARY_CHARS))
    if len(content) <= max_chars:
        return content
    if max_chars <= 80:
        return "[截断：超出本次检索预算]"
    return content[: max_chars - 80].rstrip() + "\n\n[截断：超出本次检索预算；如需全文请按 path 精确读取]"


_CHINESE_DIGITS = {
    "零": 0,
    "一": 1,
    "二": 2,
    "两": 2,
    "三": 3,
    "四": 4,
    "五": 5,
    "六": 6,
    "七": 7,
    "八": 8,
    "九": 9,
}


def _parse_chinese_int(raw: str) -> Optional[int]:
    text = (raw or "").strip().lstrip("零")
    if not text:
        return 0
    if text == "十":
        return 10
    if "百" in text:
        left, right = (text.split("百", 1) + [""])[:2]
        hundreds = _CHINESE_DIGITS.get(left, 1 if not left else -1)
        if hundreds <= 0:
            return None
        rest = _parse_chinese_int(right) if right else 0
        return None if rest is None else hundreds * 100 + rest
    if "十" in text:
        left, right = (text.split("十", 1) + [""])[:2]
        tens = _CHINESE_DIGITS.get(left, 1 if not left else -1)
        ones = _CHINESE_DIGITS.get(right, 0 if not right else -1)
        if tens <= 0 or ones < 0:
            return None
        return tens * 10 + ones
    if len(text) == 1:
        return _CHINESE_DIGITS.get(text)
    return None


def _episode_number_from_path(path: str) -> Optional[int]:
    normalized = (path or "").replace("\\", "/")
    name = Path(normalized).name
    for pattern in (
        r"^(?:ep|e)(\d{1,4})\.md$",
        r"^第\s*(\d{1,4})\s*集\.md$",
        r"^(\d{1,4})\.md$",
    ):
        match = re.search(pattern, name, re.IGNORECASE)
        if match:
            value = int(match.group(1))
            return value if value > 0 else None
    chinese = re.search(r"^第\s*([零一二两三四五六七八九十百]{1,8})\s*集\.md$", name)
    if chinese:
        value = _parse_chinese_int(chinese.group(1))
        return value if value and value > 0 else None
    return None


def _normalize_episode_doc_path(path: str) -> str:
    normalized = (path or "").replace("\\", "/")
    if not normalized.startswith("episodes/"):
        return path
    number = _episode_number_from_path(normalized)
    if number is None:
        return path
    return f"episodes/ep{number:03d}.md"


_PROJECT_DOC_PATH_ALIASES = {
    "灵感总结.md": "project_brief.md",
    "项目灵感.md": "project_brief.md",
    "项目简介.md": "project_brief.md",
    "梗概.md": "synopsis.md",
    "故事梗概.md": "synopsis.md",
    "剧情梗概.md": "synopsis.md",
}


def _canonical_project_doc_path(path: str) -> str:
    """Map user-facing stage document names to canonical internal paths."""
    normalized = (path or "").replace("\\", "/")
    path_obj = Path(normalized)
    alias = _PROJECT_DOC_PATH_ALIASES.get(path_obj.name)
    if not alias:
        return path
    parent = "" if str(path_obj.parent) in {"", "."} else str(path_obj.parent).replace("\\", "/")
    return alias if not parent else f"{parent}/{alias}"


def _project_doc_sort_key(path: Path) -> tuple[int, int, str]:
    parent = path.parent.name
    number = _episode_number_from_path(path.name) if parent == "episodes" else None
    if number is not None:
        return (0, number, path.name.lower())
    return (1, 0, path.name.lower())


# ---------------------------------------------------------------------------
# Tool handlers
# ---------------------------------------------------------------------------


def read_project_doc(args: dict, **kw) -> str:
    """Read a project document file at ``data/projects/{project_id}/{path}``.

    Schema:
        project_id (str): Project identifier
        path (str):      File path relative to the project directory
    """
    project_id = args.get("project_id", "")
    path = args.get("path", "")
    path = _normalize_episode_doc_path(_canonical_project_doc_path(path))

    if _is_project_cancelled(project_id):
        return _tool_failure("read_project_doc", project_id, "本轮任务已停止，拒绝继续读取项目内容。")

    err = _check_project_id(project_id)
    if err:
        return _tool_failure("read_project_doc", project_id, err)

    target = _resolve_project_path(project_id, path)
    if target is None:
        return _tool_failure("read_project_doc", project_id, f"Path traversal blocked: {path!r}")

    snapshot_cache = _active_workspace_snapshot_cache()
    snapshot_files = snapshot_cache.get("files") if isinstance(snapshot_cache.get("files"), dict) else {}
    if path in snapshot_files:
        content = str(snapshot_files.get(path) or "")
        _append_unique_trace_list("project_docs_read", path)
        _emit_progress("read", path)
        return tool_result(
            success=True,
            content=content,
            path=path,
            bytes=len(content),
            source="workspace_snapshot",
        )

    if not target.exists():
        return _tool_failure("read_project_doc", project_id, f"File not found: data/projects/{project_id}/{path}")

    if not target.is_file():
        return _tool_failure("read_project_doc", project_id, f"Not a file: data/projects/{project_id}/{path}")

    try:
        content = target.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return _tool_failure(
            "read_project_doc",
            project_id,
            f"Cannot read binary file: data/projects/{project_id}/{path}"
        )
    except Exception as exc:
        return _tool_failure("read_project_doc", project_id, f"Read error: {exc}")

    _append_unique_trace_list(
        "project_docs_read",
        target.relative_to(_PROJECTS_ROOT / project_id).as_posix(),
    )

    return tool_result(
        success=True,
        content=content,
        path=target.relative_to(_PROJECTS_ROOT / project_id).as_posix(),
        bytes=len(content),
    )


def _resolve_project_dir(project_id: str, path: str) -> Optional[Path]:
    """Resolve a project-relative *directory* path (root aliases allowed).

    Uses WorkspacePathResolver.resolve_project_dir when available; falls back
    to basic traversal protection otherwise. Returns the absolute directory
    Path if safe, or None on violation / unknown directory.
    """
    try:
        from packages.workspace_resolver import resolve_project_dir as _dir_resolver
        return _dir_resolver(project_id, path, projects_root=_PROJECTS_ROOT)
    except ImportError:
        pass

    # Fallback: treat root aliases as project root and allow only known
    # listable directories. Keep this path strict because it runs when the
    # canonical resolver cannot be imported in packaged builds.
    stripped = (path or "").strip()
    normalized = "" if stripped in {"", ".", "/", "./", "\\"} else stripped.replace("\\", "/").strip("/")
    if ".." in normalized.split("/"):
        return None
    if normalized not in {"", "characters", "episodes", "ledger", "runs", "traces", "manhua_prompts"}:
        return None
    project_root = (_PROJECTS_ROOT / project_id).resolve()
    target = (project_root / normalized).resolve() if normalized else project_root
    try:
        target.relative_to(project_root)
    except ValueError:
        return None
    return target


def list_project_docs(args: dict, **kw) -> str:
    """List project files under a directory, with optional short previews.

    Schema:
        project_id (str): Project identifier
        path (str):      Directory path relative to the project directory.
                         Empty / "." / "/" all mean the project root.
        include_content (bool): Include content preview for each text file
        max_chars (int): Maximum preview characters per file
    """
    project_id = args.get("project_id", "")
    path = args.get("path", "")
    include_content = bool(args.get("include_content", False))
    max_chars = int(args.get("max_chars") or 1200)
    max_chars = max(200, min(max_chars, 5000))

    err = _check_project_id(project_id)
    if err:
        return tool_error(err)

    snapshot_cache = _active_workspace_snapshot_cache()
    snapshot_dirs = snapshot_cache.get("dirs") if isinstance(snapshot_cache.get("dirs"), dict) else {}
    normalized_input = "" if (path or "").strip() in {"", ".", "/", "./", "\\"} else (path or "").strip().replace("\\", "/").strip("/")
    if normalized_input in snapshot_dirs:
        result_files = []
        for child in sorted(snapshot_dirs.get(normalized_input) or [], key=lambda item: _project_doc_sort_key(Path(str(item.get("path") or "")))):
            item = {
                "name": str(child.get("name") or Path(str(child.get("path") or "")).name),
                "path": str(child.get("path") or ""),
                "bytes": int(child.get("bytes") or len(str(child.get("content") or ""))),
            }
            if include_content:
                content = str(child.get("content") or "")
                item["content_preview"] = content[:max_chars]
                item["truncated"] = len(content) > max_chars
                _append_unique_trace_list("project_docs_read", item["path"])
            result_files.append(item)

        trace_path = _normalize_project_doc_trace_path(normalized_input, is_dir=bool(normalized_input))
        _append_unique_trace_list("project_docs_listed", trace_path or ".")
        return tool_result(
            success=True,
            path=path,
            files=result_files,
            dirs=[],
            count=len(result_files),
            source="workspace_snapshot",
        )

    target = _resolve_project_dir(project_id, path)
    if target is None:
        return tool_error(
            f"Invalid directory: {path!r}. Use '' / '.' for the project root, "
            "or a known subdirectory (characters/, episodes/, ledger/, "
            "manhua_prompts/, runs/, traces/)."
        )

    if not target.exists():
        return tool_result(success=True, path=path, files=[], dirs=[], count=0)

    if not target.is_dir():
        return tool_error(f"Not a directory: data/projects/{project_id}/{path}")

    project_root = (_PROJECTS_ROOT / project_id).resolve()
    files = sorted(
        [child for child in target.iterdir() if child.is_file()],
        key=_project_doc_sort_key,
    )
    dirs = [
        child.relative_to(project_root).as_posix() + "/"
        for child in sorted(target.iterdir())
        if child.is_dir()
    ]

    result_files = []
    for child in files:
        child_path = child.relative_to(project_root).as_posix()
        item = {
            "name": child.name,
            "path": child_path,
            "bytes": child.stat().st_size,
        }
        if include_content:
            try:
                content = child.read_text(encoding="utf-8")
                item["content_preview"] = content[:max_chars]
                item["truncated"] = len(content) > max_chars
                _append_unique_trace_list("project_docs_read", child_path)
            except (UnicodeDecodeError, OSError):
                item["content_preview"] = "[binary or unreadable file]"
                item["truncated"] = False
        result_files.append(item)

    trace_path = "" if (path or "").strip() in {"", ".", "/", "./", "\\"} else (path or "").strip().replace("\\", "/").strip("/")
    trace_path = _normalize_project_doc_trace_path(trace_path, is_dir=bool(trace_path))
    _append_unique_trace_list("project_docs_listed", trace_path or ".")

    return tool_result(
        success=True,
        path=path,
        files=result_files,
        dirs=dirs,
        count=len(result_files),
    )


def write_project_doc(args: dict, **kw) -> str:
    """Write content to a project document file (overwrites, creates dirs).

    Schema:
        project_id (str): Project identifier
        path (str):      File path relative to the project directory
        content (str):   File content to write
    """
    project_id = args.get("project_id", "")
    path = args.get("path", "")
    content = args.get("content", "")

    if _is_project_cancelled(project_id):
        return _tool_failure("write_project_doc", project_id, "本轮任务已停止，拒绝继续写入项目内容。")

    trace = _active_methodology_trace()
    hard_stop = trace.get("tool_hard_stop") if isinstance(trace, dict) else None
    if (
        isinstance(hard_stop, dict)
        and hard_stop.get("tool") == "write_project_doc"
        and hard_stop.get("reason") in {"stop_loss", "episode_write_rejected_once"}
    ):
        return tool_error(
            "该文件已停止重试，拒绝继续写入项目内容。请修正本次错误后重试该文件。",
            stop_current_turn=True,
        )

    # Redirect user-facing Chinese stage filenames to canonical internal
    # paths before WritePolicy checks, otherwise a correct stage write can be
    # rejected only because the model chose the display name.
    original_path = path
    path = _normalize_episode_doc_path(_canonical_project_doc_path(path))
    policy = active_project_write_policy() or {}
    if (
        str(policy.get("page") or "") == "character-biography"
        and str(policy.get("action_intent") or "") == "preset_execute"
        and _normalize_project_doc_trace_path(path) == "characters/00-人物关系图.md"
    ):
        _append_unique_trace_list("warnings", "character_relationship_map_write_blocked")
        return _tool_failure(
            "write_project_doc",
            project_id,
            "人物小传页只生成正式人物卡，不生成关系图。请继续逐个写入人物卡。",
        )
    # 剧集首次非空提交就是交付底稿。字数只记录质量提示，不拒写、不重写。
    _episode_effective_chars: int | None = None
    _episode_attempt_payload: dict | None = None
    if isinstance(content, str) and path.startswith("episodes/ep"):
        content, _discarded_contract = _strip_episode_contract_block(content)
        if not content.strip():
            return _tool_failure("write_project_doc", project_id, "剧集正文为空，无法写入。")
        normalized_path_for_gate = _normalize_project_doc_trace_path(path)
        _body_for_count = re.sub(r"```.*?```", "", content, flags=re.DOTALL)
        _body_for_count = re.sub(r"^\s*#+\s*", "", _body_for_count, flags=re.MULTILINE)
        _body_for_count = re.sub(
            r"[`\s*_>#|《》「」『』【】\[\]（）()：:，,。.!！?？、；;·\-—▲△]",
            "", _body_for_count,
        )
        _body_chars = len(_body_for_count)
        _episode_effective_chars = _body_chars
        _episode_write_mode = str(policy.get("write_mode") or "direct").strip()
        trace = _active_methodology_trace()

        if _episode_write_mode == "collect" and trace is not None:
            capture_policy_error = _path_allowed_by_policy(project_id, path)
            if capture_policy_error:
                return _tool_failure("write_project_doc", project_id, capture_policy_error)
            seen_paths = trace.setdefault("_episode_write_paths_seen", [])
            if normalized_path_for_gate in seen_paths:
                return tool_result(
                    success=True,
                    path=normalized_path_for_gate,
                    normalized_path=normalized_path_for_gate,
                    duplicate_ignored=True,
                    accepted=normalized_path_for_gate in (trace.get("project_docs_written") or []),
                    effective_chars=_body_chars,
                    stop_current_turn=True,
                    message="本路径本轮已交付，禁止再次生成。",
                )
            seen_paths.append(normalized_path_for_gate)

        _episode_attempt_payload = {
            "path": normalized_path_for_gate,
            "phase": "initial",
            "attempt": 1,
            "effective_chars": _body_chars,
            "accepted": True,
        }
        if _body_chars < MIN_EPISODE_CHARS:
            _append_unique_trace_list(
                "warnings",
                f"episode_length_advisory_under: {normalized_path_for_gate} "
                f"({_body_chars} < {MIN_EPISODE_CHARS})",
            )
        elif _body_chars > MAX_EPISODE_CHARS:
            _append_unique_trace_list(
                "warnings",
                f"episode_length_advisory_over: {normalized_path_for_gate} "
                f"({_body_chars} > {MAX_EPISODE_CHARS})",
            )
        # 波别要求：剧集正文严禁破折号「——」（DeepSeek 强写、SKILL/prompt 都管不住），
        # 写盘兜底：把「——」替换成全角逗号（对白/动作的连接停顿用逗号，语义无损）。
        content = content.replace("——", "，")
        # 波别要求：△ 动作符号必须顶格行首，不能跟在对白后面同一行。
        # 写盘兜底：把非行首的 △ 前插入换行，确保每个 △ 都是行首。
        content = re.sub(r"(?<!\n)(?<=.)([ \t]*)(?=△)", "\n", content)
    # ──────────────────────────────────────────────────────────────────

    policy_error = _path_allowed_by_policy(project_id, path)
    if policy_error:
        return _tool_failure("write_project_doc", project_id, policy_error)

    err = _check_project_id(project_id)
    if err:
        return _tool_failure("write_project_doc", project_id, err)

    target = _resolve_project_path(project_id, path)
    if target is None:
        return _tool_failure("write_project_doc", project_id, f"Path traversal blocked: {path!r}")

    normalized_path = target.relative_to(_PROJECTS_ROOT / project_id).as_posix()
    write_mode = str(policy.get("write_mode") or "direct").strip() or "direct"
    trace = _active_methodology_trace()
    run_id = str(trace.get("run_id") or "") if trace else ""

    if write_mode == "collect":
        if not run_id:
            return _tool_failure(
                "write_project_doc",
                project_id,
                "collect 模式缺少 run_id，无法发出正式 artifact 事件。",
            )

        if is_episode_outline_path(normalized_path):
            try:
                validate_episode_outline_content(content)
            except ValueError as exc:
                return _tool_failure("write_project_doc", project_id, str(exc))

        if (
            normalized_path == "ledger/pending_episode_revisions.json"
            and str(policy.get("action_intent") or "").strip() == "fix_problems"
        ):
            existing_paths = list(
                existing_episode_paths_from_snapshot_cache(
                    policy.get("workspace_snapshot_cache")
                )
            )
            project_root = _PROJECTS_ROOT / project_id / "episodes"
            if project_root.exists():
                for child in project_root.iterdir():
                    if not child.is_file():
                        continue
                    episode_path = normalize_episode_revision_target(
                        f"episodes/{child.name}"
                    )
                    if episode_path and episode_path not in existing_paths:
                        existing_paths.append(episode_path)
            existing_paths = sorted(set(existing_paths))
            path_error = validate_pending_episode_revision_paths(
                content,
                existing_episode_paths=existing_paths,
            )
            if path_error:
                return _tool_failure("write_project_doc", project_id, path_error)

        # Canonicalize content before creating manifest so that
        # content_hash/bytes reflect the canonical (written) content.
        # on-the-fly normalization would produce a different content
        # hash at commit time.  The sidecar's artifact executor no
        # longer rehashes — it trusts the manifest computed here.
        try:
            _canonical_content = canonicalize_artifact_content(
                project_id=project_id,
                path=normalized_path,
                content=content,
                workspace_context=_hermes_canonicalization_context(project_id),
                now_iso=datetime.now(timezone.utc)
                .isoformat(timespec="seconds")
                .replace("+00:00", "Z"),
            )
        except ValueError as exc:
            return _tool_failure(
                "write_project_doc",
                project_id,
                str(exc) or "待确认修改规范化失败，请改用已落盘剧集后重试。",
            )
        if (
            normalized_path == "ledger/pending_episode_revisions.json"
            and str(policy.get("action_intent") or "").strip() == "fix_problems"
            and not (json.loads(_canonical_content).get("revisions") or [])
        ):
            return _tool_failure(
                "write_project_doc",
                project_id,
                "本次修订至少要生成一条待确认修改记录，不能写入空修改清单。",
            )

        _seq = _next_artifact_sequence(run_id)
        try:
            _manifest = _build_artifact_manifest(
                run_id=run_id,
                sequence=_seq,
                project_id=project_id,
                page=active_page(),
                path=normalized_path,
                kind=_infer_artifact_kind(path),
                content=_canonical_content,
            )
        except ValueError as exc:
            return _tool_failure("write_project_doc", project_id, f"invalid artifact manifest: {exc}")
        if trace is not None:
            pending = trace.setdefault("pending_workspace_writes", [])
            existing = next(
                (item for item in pending if str(item.get("path") or "") == normalized_path),
                None,
            )
            payload = _manifest.to_pending_write(_canonical_content)
            if _episode_attempt_payload is not None:
                payload.update(
                    {
                        "episode_write_phase": _episode_attempt_payload["phase"],
                        "episode_write_attempt": _episode_attempt_payload["attempt"],
                        "effective_chars": _episode_attempt_payload["effective_chars"],
                    }
                )
            if existing is None:
                pending.append(payload)
            else:
                existing.update(payload)
            if _episode_attempt_payload is not None:
                trace.setdefault("episode_write_attempts", []).append(_episode_attempt_payload)
        _emit_artifact_ready(project_id, normalized_path, _canonical_content, manifest=_manifest)
    else:
        # B-EPISODE-BACKUP-01：写入剧集文件前先备份旧版本。
        # 检查目标文件是否存在，如果存在则复制为 .v{N} 版本文件。
        # 版本号从 1 开始递增，保留所有历史版本供前端对比。
        if path.startswith("episodes/ep"):
            try:
                if target.exists() and target.stat().st_size > 0:
                    old_content = target.read_text(encoding="utf-8")
                    # 扫描已有版本文件确定下一个版本号
                    version_num = 1
                    for sibling in target.parent.iterdir():
                        sibling_name = sibling.name
                        if sibling_name.startswith(target.stem) and sibling_name.endswith(".md"):
                            v_match = re.search(r"\.v(\d+)\.md$", sibling_name)
                            if v_match:
                                version_num = max(version_num, int(v_match.group(1)) + 1)
                    # 如果主文件本身也是某个版本（如 ep001.md.v2.md 格式），
                    # 以上扫描已覆盖。此处备份前一份内容。
                    backup_name = f"{target.stem}.v{version_num}.md"
                    backup_path = target.parent / backup_name
                    backup_path.write_text(old_content, encoding="utf-8")
                    _append_unique_trace_list("warnings",
                        f"episode_backup: {normalized_path} -> {backup_name}")
            except Exception as _backup_exc:
                # 备份失败不影响主流程，仅记录 warning
                _append_unique_trace_list("warnings",
                    f"episode_backup_failed: {normalized_path}: {_backup_exc}")

        try:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
            written_back = target.read_text(encoding="utf-8")
        except OSError as exc:
            return _tool_failure("write_project_doc", project_id, f"Write error: {exc}")
        except Exception as exc:
            return _tool_failure("write_project_doc", project_id, f"Write error: {exc}")
        if written_back != content:
            return _tool_failure(
                "write_project_doc",
                project_id,
                f"Write verification failed: {normalized_path}",
            )

        # A-EPISODE-NUMBER-TRUTH-SOURCE-01 §方案B：写入 episode 文件后自动更新 episode_index.json
        if path.startswith("episodes/ep"):
            try:
                import re as _re_ep
                from xiaoma.episode_index import EpisodeIndexManager as _EIM
                ep_match = _re_ep.search(r"ep0*(\d+)\.md$", path)
                if ep_match and project_id and _PROJECTS_ROOT is not None:
                    _EIM((_PROJECTS_ROOT / project_id).resolve()).add_episode(int(ep_match.group(1)))
            except Exception as _idx_exc:
                # 索引更新失败不影响主流程，仅记录 warning
                _append_unique_trace_list("warnings", f"episode_index_update_failed: {path}: {_idx_exc}")

        # Direct write mode — construct manifest ONCE for the commit event
        if run_id:
            _dseq = _next_artifact_sequence(run_id)
            try:
                _direct_manifest = _build_artifact_manifest(
                    run_id=run_id,
                    sequence=_dseq,
                    project_id=project_id,
                    page=active_page(),
                    path=normalized_path,
                    kind=_infer_artifact_kind(path),
                    content=content,
                )
            except ValueError as exc:
                return _tool_failure("write_project_doc", project_id, f"invalid artifact manifest: {exc}")
            _emit_artifact_commit(project_id, normalized_path, content, manifest=_direct_manifest)

    _append_unique_trace_list(
        "project_docs_written",
        normalized_path,
    )
    _emit_progress("write", normalized_path)

    _stop_episode_collect_turn = (
        write_mode == "collect" and normalized_path.startswith("episodes/ep")
    )
    return tool_result(
        success=True,
        path=normalized_path,
        normalized_path=normalized_path,
        original_path=original_path if original_path != path else None,
        bytes=len(content),
        overwritten=True,
        stop_current_turn=_stop_episode_collect_turn,
        message=(
            "剧集候选已收集，当前内层回合立即结束。"
            if _stop_episode_collect_turn
            else None
        ),
    )


def _strip_episode_contract_block(content: str) -> tuple[str, dict | None]:
    match = _EPISODE_CONTRACT_BLOCK_RE.match(content or "")
    if not match:
        # Try search relax — models sometimes prefix text before the fence
        match = _EPISODE_CONTRACT_BLOCK_SEARCH_RE.search(content or "")
    if not match:
        return content, None
    raw = (match.group(1) or "").strip()
    if not raw:
        return content, None
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError:
        return content, None
    if not isinstance(parsed, dict):
        return content, None
    stripped = content[match.end():].lstrip()
    return stripped, parsed


def list_ledger(args: dict, **kw) -> str:
    """List all files in a project's ``ledger/`` directory with their content.

    Schema:
        project_id (str): Project identifier
    """
    project_id = args.get("project_id", "")

    err = _check_project_id(project_id)
    if err:
        return tool_error(err)

    ledger_dir = (_PROJECTS_ROOT / project_id / "ledger").resolve()
    try:
        ledger_dir.relative_to((_PROJECTS_ROOT / project_id).resolve())
    except ValueError:
        # If for some reason the resolved path escapes, block
        return tool_error("Path traversal blocked")

    if not ledger_dir.exists() or not ledger_dir.is_dir():
        return tool_result(success=True, files=[], count=0)

    files = []
    for child in sorted(ledger_dir.iterdir()):
        if child.is_file():
            try:
                child_content = child.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError):
                child_content = f"[binary or unreadable file: {child.name}]"
            files.append(
                {
                    "name": child.name,
                    "path": str(child.relative_to(_PROJECTS_ROOT / project_id)),
                    "content": child_content,
                }
            )

    _append_unique_trace_list("ledger_docs_read", "ledger/")

    return tool_result(success=True, files=files, count=len(files))


def _resolve_knowledge_path(source: str) -> Optional[Path]:
    """Resolve a knowledge file path (from index.yaml source field) to an absolute path."""
    path = Path(source)
    if path.is_absolute():
        return path if path.exists() else None
    candidates = [
        _KNOWLEDGE_ROOT / path,
        _STABLE_ROOT / path,
        _STABLE_ROOT.parent / path,
        _KNOWLEDGE_ROOT.parent / path,
    ]
    for c in candidates:
        if c.exists() and c.is_file():
            return c.resolve()
    return None


def _read_index_card_content(file_path: Path, source: str) -> str:
    try:
        content = file_path.read_text(encoding="utf-8")
        if "\ufffd" in content:
            logger.warning("Indexed knowledge card contains replacement characters: %s", source)
            _append_unique_trace_list("warnings", f"knowledge_card_replacement_chars: {source}")
            content = content.replace("\ufffd", "")
        return content.strip()
    except UnicodeDecodeError as exc:
        logger.warning("Indexed knowledge card is not UTF-8 readable: %s: %s", source, exc)
        _append_unique_trace_list("warnings", f"knowledge_card_unreadable: {source}")
    except OSError as exc:
        logger.warning("Indexed knowledge card could not be read: %s: %s", source, exc)
        _append_unique_trace_list("warnings", f"knowledge_card_read_failed: {source}")
    return ""


def retrieve_market_cards(args: dict, **kw) -> str:
    """Retrieve approved knowledge cards with index-based retrieval and priority scoring.

    Schema:
        stage (str): inspiration | synopsis | outline | episodes | character
        format (str): manhua | short_drama
        topic (str): optional topic alias, e.g. xianxia, rule-horror, 宅斗
        audience (str): optional audience filter, e.g. male, female, mixed
        task (str): optional task filter, e.g. brainstorm, synopsis, outline, write_batch, first_episode, revise, audit
        problem (str): optional specific problem to search for, e.g. format, hook, pacing, character, dialogue
        max_chars (int): optional maximum returned content characters
    """
    stage = (args.get("stage") or "inspiration").strip()
    fmt = (args.get("format") or "manhua").strip()
    topic = _normalize_topic(args.get("topic") or "")
    audience = (args.get("audience") or "").strip()
    task = (args.get("task") or "").strip()
    problem = (args.get("problem") or "").strip()
    budget = int(args.get("max_chars") or _MAX_CARD_CHARS)
    budget = max(3000, min(budget, _MAX_CARD_CHARS))
    topic_profile = get_topic_profile(topic) if topic else None
    allow_fixed_fallback = os.environ.get("XIAOMA_ALLOW_FIXED_RETRIEVAL_FALLBACK", "").strip() == "1"

    cards = []
    conflicts = []
    score_reasons = []

    # --- Stage 1: Index-based retrieval (A-M02) ---
    use_methodology_index = _METHODOLOGY_INDEX_AVAILABLE
    if use_methodology_index:
        try:
            index_results = query_index(
                stage=stage,
                topic=topic,
                audience=audience,
                task=task,
                problem=problem,
                max_results=8,
            )
            for ir in index_results:
                file_path = _resolve_knowledge_path(ir["path"])
                if file_path:
                    full_content = _read_index_card_content(file_path, ir["path"])
                    if full_content:
                        summary = _compact_card_content(full_content, budget)
                        cards.append({
                            "path": ir["path"],
                            "id": ir["id"],
                            "layer": ir["layer"],
                            "priority": ir["priority"],
                            "priority_order": ir.get("priority_order"),
                            "score": ir["score"],
                            "reason": ir["reason"],
                            "summary": summary,
                            "truncated": len(full_content) > len(summary),
                        })
                        budget -= len(summary)
                        score_reasons.append(f"{ir['id']}: {ir['reason']}")
                if budget <= 0:
                    break

            conflicts = conflict_check(cards)
        except Exception as exc:
            logger.warning("Index retrieval failed: %s", exc)
            use_methodology_index = False

    if _METHODOLOGY_INDEX_AVAILABLE and not cards and not allow_fixed_fallback:
        return tool_error(
            "知识索引未返回可用卡片。当前运行时已切到索引驱动主路径，"
            "请补齐 topic-pack 子文件索引、题材 profile 或 retrieval profile，"
            "不要再依赖固定文件 fallback。"
        )

    # --- Stage 2: Fixed-file fallback (explicitly opt-in for diagnostics only) ---
    if not use_methodology_index:
        if not allow_fixed_fallback:
            return tool_error(
                "知识索引不可用，且未开启诊断 fallback。请先修复 methodology_index 或显式设置 "
                "XIAOMA_ALLOW_FIXED_RETRIEVAL_FALLBACK=1 做临时排查。"
            )
        for relative_path in _STABLE_STAGE_FILES.get(stage, _STABLE_STAGE_FILES["inspiration"]):
            budget = _append_card(cards, _read_stable_file(relative_path), budget)
            if budget <= 0:
                break

        for relative_path in _PROCESSED_STAGE_FILES.get(stage, _PROCESSED_STAGE_FILES["inspiration"]):
            budget = _append_card(cards, _read_knowledge_file(_KNOWLEDGE_ROOT, relative_path), budget)
            if budget <= 0:
                break

        for relative_path in _PATTERN_STAGE_FILES.get(stage, _PATTERN_STAGE_FILES["inspiration"]):
            budget = _append_card(cards, _read_knowledge_file(_REDFRUIT_ROOT, relative_path), budget)
            if budget <= 0:
                break

        for relative_path in _STAGE_FILES.get(stage, _STAGE_FILES["inspiration"]):
            budget = _append_card(cards, _read_knowledge_file(_REDFRUIT_ROOT, relative_path), budget)
            if budget <= 0:
                break

        if topic_profile and budget > 0:
            topic_dir = (_TOPIC_PACKS_ROOT / topic_profile.topic_pack).resolve()
            try:
                topic_dir.relative_to(_TOPIC_PACKS_ROOT.resolve())
            except ValueError:
                topic_dir = None
            if topic_dir and topic_dir.exists():
                if budget > 0:
                    for relative_path in _TOPIC_CASE_FILES.get(topic_profile.canonical_id, []):
                        budget = _append_card(cards, _read_knowledge_file(_REDFRUIT_ROOT, relative_path), budget)
                        if budget <= 0:
                            break
                if budget > 0:
                    for filename in _TOPIC_STAGE_FILES.get(stage, _TOPIC_STAGE_FILES["inspiration"]):
                        budget = _append_card(cards, _read_knowledge_file(topic_dir, filename), budget)
                        if budget <= 0:
                            break

    _record_cards_retrieved(args, cards, conflicts)

    return tool_result(
        success=True,
        stage=stage,
        format=fmt,
        topic=topic or None,
        default_episode_range="80-99" if fmt in {"manhua", "ai-manhua", "AI仿真人漫剧", "漫剧"} else "按项目需求",
        instruction=(
            "这些卡片是趋势参考和可重组方法，不是抄袭模板。"
            "漫剧默认按 80-99 集设计；若卡片里出现 60-80 集，以 80-99 集为当前口径。"
            "卡片只返回摘要；需要全文时按 path 精确读取，不要反复扩大检索。"
        ),
        cards=cards,
        count=len(cards),
        score_summary=score_reasons if score_reasons else None,
        conflicts=conflicts if conflicts else None,
    )


def _strip_html(value: str) -> str:
    text = re.sub(r"<[^>]+>", " ", value or "")
    text = unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def _duckduckgo_search(query: str, limit: int) -> list[dict]:
    url = f"https://duckduckgo.com/html/?q={quote_plus(query)}"
    req = Request(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        },
    )
    with urlopen(req, timeout=8) as response:
        html = response.read().decode("utf-8", errors="ignore")

    results: list[dict] = []
    pattern = re.compile(
        r'<a[^>]+class="result__a"[^>]+href="(?P<href>[^"]+)"[^>]*>(?P<title>.*?)</a>.*?'
        r'<a[^>]+class="result__snippet"[^>]*>(?P<snippet>.*?)</a>',
        re.DOTALL,
    )
    for match in pattern.finditer(html):
        href = unescape(match.group("href"))
        parsed = urlparse(href)
        if parsed.path.endswith("/l/"):
            href = unquote(parse_qs(parsed.query).get("uddg", [href])[0])
        title = _strip_html(match.group("title"))
        snippet = _strip_html(match.group("snippet"))
        if not title:
            continue
        results.append({"title": title, "url": href, "snippet": snippet})
        if len(results) >= limit:
            break
    return results


def search_reference_drama(args: dict, **kw) -> str:
    """Search reference drama information from approved knowledge first, then web."""
    query = str(args.get("query") or "").strip()
    if not query:
        return tool_error("query is required")
    limit = max(1, min(int(args.get("limit") or 5), 8))

    knowledge_matches: list[dict] = []
    index_path = (_REDFRUIT_ROOT / "blockbuster-cases" / "index.md").resolve()
    if index_path.exists():
        try:
            for line in index_path.read_text(encoding="utf-8").splitlines():
                if "|" not in line or query not in line:
                    continue
                cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
                if len(cells) < 5 or cells[0] in {"编号", "------"}:
                    continue
                knowledge_matches.append({
                    "id": cells[0],
                    "title": cells[1],
                    "heat": cells[2],
                    "episodes": cells[3],
                    "tags": cells[4],
                    "source": "knowledge",
                })
                if len(knowledge_matches) >= limit:
                    break
        except OSError:
            knowledge_matches = []

    web_results: list[dict] = []
    try:
        from tools.web_tools import web_search_tool
        raw = web_search_tool(f"{query} 短剧 漫剧 热度 集数 剧情", limit=limit)
        parsed = json.loads(raw) if isinstance(raw, str) else raw
        if isinstance(parsed, dict) and parsed.get("success") is True:
            web_data = parsed.get("data", {}).get("web", [])
            for entry in web_data:
                web_results.append({
                    "title": str(entry.get("title", "")),
                    "url": str(entry.get("url", "")),
                    "snippet": str(entry.get("description", "")),
                    "source": "web",
                })
        if not web_results:
            raise RuntimeError("web_search_tool returned no results")
    except Exception as exc:
        _append_unique_trace_list("warnings", f"reference_drama_web_search_failed: {exc}")
        try:
            web_results = _duckduckgo_search(f"{query} 短剧 漫剧 热度 集数 剧情", limit)
        except Exception:
            pass

    return tool_result(
        success=True,
        query=query,
        instruction=(
            "先使用 knowledge_results；web_results 只做公开信息补充。"
            "这些信息只能参考热度、题材、受众和卖点，不得复刻原剧剧情、人物、台词或核心桥段。"
        ),
        knowledge_results=knowledge_matches,
        web_results=web_results,
        count=len(knowledge_matches) + len(web_results),
    )


# ---------------------------------------------------------------------------
# Registration
# ---------------------------------------------------------------------------

registry.register(
    name="read_project_doc",
    toolset="xiaoma_project",
    schema={
        "name": "read_project_doc",
        "description": "Read a project document file at data/projects/{project_id}/{path}",
        "parameters": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "Project identifier (e.g. 'proj_abc123')",
                },
                "path": {
                    "type": "string",
                    "description": "File path relative to the project directory (e.g. 'synopsis.md')",
                },
            },
            "required": ["project_id", "path"],
        },
    },
    handler=read_project_doc,
    description="Read a project document file",
)

registry.register(
    name="list_project_docs",
    toolset="xiaoma_project",
    schema={
        "name": "list_project_docs",
        "description": "List files under a project directory, optionally with short content previews",
        "parameters": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "Project identifier (e.g. 'proj_abc123')",
                },
                "path": {
                    "type": "string",
                    "description": "Directory or file path relative to the project directory (e.g. 'episodes/')",
                },
                "include_content": {
                    "type": "boolean",
                    "description": "Whether to include short content previews for each file",
                },
                "max_chars": {
                    "type": "integer",
                    "description": "Maximum preview characters per file, capped by the tool",
                },
            },
            "required": ["project_id", "path"],
        },
    },
    handler=list_project_docs,
    description="List project files",
)

registry.register(
    name="write_project_doc",
    toolset="xiaoma_project",
    schema={
        "name": "write_project_doc",
        "description": "Write content to a project document file (creates directories if needed, overwrites existing file)",
        "parameters": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "Project identifier (e.g. 'proj_abc123')",
                },
                "path": {
                    "type": "string",
                    "description": "File path relative to the project directory (e.g. 'synopsis.md')",
                },
                "content": {
                    "type": "string",
                    "description": "File content to write",
                },
                "episode_contract": {
                    "type": "object",
                    "description": "Optional structured prewrite contract for episodes/ep*.md writes. Must include scene_plan, opening_conflict, protagonist_goal, ending_hook, target_chars_min, target_chars_max, os_budget.",
                },
            },
            "required": ["project_id", "path", "content"],
        },
    },
    handler=write_project_doc,
    description="Write content to a project document file",
)

registry.register(
    name="list_ledger",
    toolset="xiaoma_project",
    schema={
        "name": "list_ledger",
        "description": "List all files in a project's ledger/ directory with their content",
        "parameters": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "Project identifier (e.g. 'proj_abc123')",
                },
            },
            "required": ["project_id"],
        },
    },
    handler=list_ledger,
    description="List project ledger files",
)

registry.register(
    name="retrieve_market_cards",
    toolset="xiaoma_project",
    schema={
        "name": "retrieve_market_cards",
        "description": "Retrieve approved knowledge cards with index-based retrieval and priority scoring. Use before market judgment, synopsis, outline, or episode writing. Supports stage/topic/audience/task/problem filtering.",
        "parameters": {
            "type": "object",
            "properties": {
                "stage": {
                    "type": "string",
                    "description": "Creation stage: inspiration, synopsis, outline, episodes, character",
                },
                "format": {
                    "type": "string",
                    "description": "Project format, usually manhua or short_drama",
                },
                "topic": {
                    "type": "string",
                    "description": "Topic alias such as xianxia, rule-horror, apocalypse, female-rebirth, 修仙, 规则怪谈, 末日, 宅斗",
                },
                "audience": {
                    "type": "string",
                    "description": "Target audience filter: male, female, mixed",
                },
                "task": {
                    "type": "string",
                    "description": "Task filter: brainstorm, synopsis, character, outline, first_episode, write_batch, revise, audit",
                },
                "problem": {
                    "type": "string",
                    "description": "Specific problem to search for, e.g. format, hook, pacing, character, dialogue, rhythm, naming, compliance",
                },
                "max_chars": {
                    "type": "integer",
                    "description": "Maximum returned content characters, capped by the tool",
                },
            },
            "required": ["stage"],
        },
    },
    handler=retrieve_market_cards,
    description="Retrieve approved knowledge cards with index-based retrieval",
)

registry.register(
    name="search_reference_drama",
    toolset="xiaoma_project",
    schema={
        "name": "search_reference_drama",
        "description": "Search a reference drama by name. Looks in approved knowledge first, then public web search for title, heat, episode count, tags, and summaries.",
        "parameters": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Drama title or keywords"},
                "limit": {"type": "integer", "description": "Maximum results, 1-8"},
            },
            "required": ["query"],
        },
    },
    handler=search_reference_drama,
    description="Search reference drama information from knowledge and web",
)

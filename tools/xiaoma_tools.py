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
from typing import Any, Optional
from datetime import datetime, timezone

from packages.artifact_canonicalization import (
    CanonicalizationContext,
    canonicalize_artifact_content,
)
from packages.artifact_contract import ArtifactManifest
from packages.script_document import (
    SCRIPT_PATH,
    ScriptDocumentError,
    merge_episode_range,
    parse_script_document,
    parse_script_target,
    render_episode_range,
)
from packages.episode_outline_contract import (
    is_episode_outline_path,
    validate_episode_outline_content,
)
from packages.episode_revision_contract import (
    validate_pending_episode_revision_paths,
)
from packages.xiaoma_identity_policy import (
    _WRITE_POLICIES_BY_RUN as _IDENTITY_POLICIES_BY_RUN,
    _WRITE_POLICIES_BY_THREAD as _IDENTITY_POLICIES_BY_THREAD,
    active_project_write_policy as _active_identity_policy,
    clear_project_write_policy as _clear_identity_policy,
    set_project_write_policy as _set_identity_policy,
)
from xiaoma.orchestrator_episode_batches import keep_existing_pending_payload, pending_write_key


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
        WORKSPACE_ROOT as _WORKSPACE_ROOT,
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
    _WORKSPACE_ROOT = Path(os.environ.get("XIAOMA_WORKSPACE_ROOT", str(_base / "data" / "workspaces")))
    _KNOWLEDGE_ROOT = _base / "packages" / "knowledge" / "processed"
    _STABLE_ROOT = _base / "packages" / "knowledge" / "stable"
    _REDFRUIT_ROOT = _KNOWLEDGE_ROOT / "redfruit-2026-05"
    _TOPIC_PACKS_ROOT = _KNOWLEDGE_ROOT / "topic-packs"

# Desktop truth: Tauri sets XIAOMA_PROJECTS_ROOT / XIAOMA_WORKSPACE_ROOT to the
# AppData workspace root. Backend Hermes often only inherits XIAOMA_APP_ROOT and
# would otherwise read empty data/projects/<id>. Prefer env overrides, then
# WORKSPACE_ROOT when the project only exists there.
_env_projects = os.environ.get("XIAOMA_PROJECTS_ROOT", "").strip()
_env_workspace = os.environ.get("XIAOMA_WORKSPACE_ROOT", "").strip()
_env_local_workspace = os.environ.get("LOCAL_WORKSPACE_PATH", "").strip()
if _env_projects:
    _PROJECTS_ROOT = Path(_env_projects)
elif _env_workspace:
    _PROJECTS_ROOT = Path(_env_workspace)
elif _env_local_workspace:
    _PROJECTS_ROOT = Path(_env_local_workspace)
else:
    try:
        _ws = Path(_WORKSPACE_ROOT)
    except Exception:
        _ws = None
    if _ws is not None:
        # Keep default PROJECTS_ROOT; read path resolver can still fall back.
        pass


def _projects_root_for(project_id: str):
    """Return the projects root that actually contains this project_id.

    P2 身份返工：候选顺序改为“当前环境变量优先，模块 import 时捕获值殿后”。
    旧顺序把 import 时的 _PROJECTS_ROOT 放第一——同一进程内 env 切换后
    （测试夹具轮换工作区）仍命中旧根，导致冻结与落盘看到不同项目树。
    生产进程 env 全程稳定，新旧顺序结论一致；写路径与冻结共用本函数，
    两者 parity 恒成立。
    """
    pid = str(project_id or "").strip()
    candidates = []
    for env_name in ("XIAOMA_PROJECTS_ROOT", "XIAOMA_WORKSPACE_ROOT", "LOCAL_WORKSPACE_PATH"):
        raw = os.environ.get(env_name, "").strip()
        if raw:
            candidates.append(Path(raw))
    try:
        candidates.append(Path(_PROJECTS_ROOT))
    except Exception:
        pass
    try:
        candidates.append(Path(_WORKSPACE_ROOT))
    except Exception:
        pass
    seen = set()
    for root in candidates:
        try:
            resolved = root.resolve()
        except OSError:
            continue
        if resolved in seen:
            continue
        seen.add(resolved)
        if not pid:
            return resolved
        if (resolved / pid).exists():
            return resolved
    return Path(_PROJECTS_ROOT)

# ---------------------------------------------------------------------------
# Security helpers (inline; avoids importing the full security module for
# what amounts to two function calls, but keeps the same semantics).
# ---------------------------------------------------------------------------

_MAX_CARD_CHARS = 5000
_MAX_CARD_SUMMARY_CHARS = 900
# Compatibility aliases for existing tests/tools.  The actual owner is the
# neutral packages registry so ordinary chat never imports this Hermes module.
_WRITE_POLICIES_BY_THREAD = _IDENTITY_POLICIES_BY_THREAD
_WRITE_POLICIES_BY_RUN = _IDENTITY_POLICIES_BY_RUN
_METHODOLOGY_TRACES_BY_THREAD: dict[int, dict] = {}
# run_id → trace: lets ThreadPoolExecutor worker threads (which have a
# different ident and never see the main thread's registration) reach the same
# trace dict, and lets a follow-up start for the same run reuse the collected
# writes instead of replacing them with a fresh empty trace.
_METHODOLOGY_TRACES_BY_RUN: dict[str, dict] = {}

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
    episode_range: tuple[int, int] | None = None,
    stage_range: tuple[int, int] | None = None,
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
        episode_range=episode_range,
        stage_range=stage_range,
    )


def _hermes_canonicalization_context(project_id: str) -> CanonicalizationContext:
    """Build a CanonicalizationContext backed by Hermes ``_resolve_project_path``.

    Hermes can read local project files during collect, so the normalizer
    can fill in ``base_content_hash`` / ``old_content`` from the actual
    the single screenplay on disk. Desktop backend runs do not share the
    sidecar's workspace directory, so the snapshot cache is authoritative.
    """

    snapshot_cache = _active_workspace_snapshot_cache()
    snapshot_files = snapshot_cache.get("files") if isinstance(snapshot_cache.get("files"), dict) else {}

    def _read_file(path: str) -> str:
        normalized = str(path or "").replace("\\", "/").strip().strip("/")
        if normalized in snapshot_files:
            return str(snapshot_files[normalized] or "")
        resolved = _resolve_project_path(project_id, path)
        if resolved is None or not resolved.exists():
            raise FileNotFoundError(f"project document not found: {path}")
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
    page = _ACTIVE_PAGES_BY_THREAD.get(threading.get_ident(), "")
    if page:
        return page
    # Hermes runs concurrent tool calls in worker threads; they don't see the
    # page the main thread registered. Fall back to the most recently set page
    # so formal artifact manifest construction in a worker doesn't fail with
    # "page is required".
    for tid, candidate in reversed(tuple(_ACTIVE_PAGES_BY_THREAD.items())):
        return candidate
    return ""

def _emit_progress(action: str, path: str, *, phase: str = "completed", message: str | None = None, step_id: str = ""):
    """Emit one structured, user-visible action event for the running task.

    Phases: ``started`` (before the tool body), ``completed`` (success),
    ``failed`` (tool rejected or errored). Callers that only know the final
    outcome may keep the default ``completed``.

    Message copy stays phase-neutral (usually already starts with 正在…);
    the frontend history collapses completed steps and keeps a separate
    "current activity" line for started/failed.

    ``step_id`` groups related events (thinking/started/completed) for the
    same logical step. Auto-derived from path+action when not provided.
    """
    if _PROGRESS_SINK is None:
        return
    safe_phase = str(phase or "completed").strip() or "completed"
    if safe_phase not in {"started", "completed", "failed"}:
        safe_phase = "completed"
    msg = str(message or "").strip() or _translate_tool_to_progress(action, path)
    if not msg:
        return
    # Auto-derive step_id: same path+action shares one step
    resolved_step_id = str(step_id or "").strip()
    if not resolved_step_id:
        resolved_step_id = f"{path or action}-{action}"
    # Do not double-prefix 正在/未能: translate already returns user-facing copy.
    trace = _active_methodology_trace() or {}
    events = trace.setdefault("action_events", [])
    event = {
        "type": "action",
        "schema_version": 1,
        "step_id": resolved_step_id,
        "sequence": len(events) + 1,
        "run_id": str(trace.get("run_id") or ""),
        "action": str(action or ""),
        "path": str(path or ""),
        "page": active_page(),
        "message": msg,
        "progress": msg,
        "phase": safe_phase,
    }
    events.append(
        {key: value for key, value in event.items() if key not in {"type", "schema_version", "progress"}}
    )
    try:
        _PROGRESS_SINK(event)
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
    if normalized == SCRIPT_PATH:
        return "episode_body"
    return "generic"


def _script_target_from_policy(policy: dict[str, Any]) -> Any:
    raw = policy.get("script_target")
    if not isinstance(raw, dict):
        return None
    try:
        return parse_script_target(raw)
    except ScriptDocumentError:
        return None


def _validate_script_candidate(content: str, policy: dict[str, Any]) -> tuple[str, Any] | tuple[None, str]:
    """Return (normalized, target), or (None, reason_code) with a stable reason.

    W-script-submit-contract-gap：拒绝原因必须可区分，不能合并返回 None。
    reason_code 只有四种：no_script_target / parse_failed / empty_episodes /
    range_mismatch，调用方据此给出不同修复指引。
    """

    target = _script_target_from_policy(policy)
    if target is None:
        return None, "no_script_target"
    try:
        document = parse_script_document(content)
    except ScriptDocumentError:
        return None, "parse_failed"
    if not document.episodes:
        return None, "empty_episodes"
    try:
        selected = document.range(target.episode_range)
    except ScriptDocumentError:
        return None, "range_mismatch"
    normalized = render_episode_range(
        (episode.episode_id, episode.body) for episode in selected
    )
    return normalized, target

def _current_progress_task_context() -> tuple[str, str]:
    """Return (page, action_intent) for the active run, if known.

    Write policy is the authoritative task context (set before agent runs).
    Fall back to thread-local active page when policy is absent.
    """
    policy = active_project_write_policy(run_id=_policy_run_id_from_trace()) or {}
    page = str(policy.get("page") or active_page() or "").strip()
    action_intent = str(policy.get("action_intent") or "").strip()
    return page, action_intent


def _describe_doc_path(path: str) -> str:
    """路径 → 用户可理解的具体文档名（不暴露内部目录结构）。

    B-UX-EXEC-TIMELINE-03：执行时间线文案要带具体内容（如“人物卡 01”“第 3 集”），
    而不是一律笼统的“人物设定”“剧集”。返回空串表示无法从路径推断。
    """
    p = str(path or "").replace("\\", "/").strip().strip("/")
    if not p:
        return ""
    if p == SCRIPT_PATH:
        target = _script_target_from_policy(active_project_write_policy(run_id=_policy_run_id_from_trace()) or {})
        if target is not None:
            return target.episode_range.label()
        return "整部剧稿"
    m = re.search(r"characters/0*(\d+)\.md", p)
    if m:
        return f"人物卡 {int(m.group(1)):02d}"
    m = re.search(r"outline_variants/([45])/outline\.md", p)
    if m:
        return f"故事大纲（{m.group(1)}级）"
    if "episode_outline" in p:
        return "集纲"
    if "project_brief" in p:
        return "灵感设定"
    if "synopsis" in p:
        return "故事梗概"
    if "outline" in p:
        return "故事大纲"
    if p.rstrip("/") == "characters":
        return "人物列表"
    if p.rstrip("/") == "episodes":
        return "剧集目录"
    if p.startswith("ledger/"):
        return "连续性记录"
    return ""


def _translate_tool_to_progress(action: str, path: str) -> str:
    """工具调用 → 用户语言翻译表。核心：绝不暴露内部词。

    B-UX-EXEC-TIMELINE-03：在动词之外尽量带上具体文档名（如“回顾人物卡 01”
    “写入第 3 集”），让执行时间线读起来是真实操作而非笼统泛称。

    Path alone is not enough: outline generation reads characters/ as a
    dependency. Without task context that looks like a character-page job.
    Prefer the active page/action_intent so dependency reads stay framed as
    preparation for the real task.
    """
    p = str(path or "").replace("\\", "/").strip()
    _page, action_intent = _current_progress_task_context()
    outline_stage = action_intent in {"outline_stage_plan_4", "outline_stage_plan_5"}
    episode_outline = action_intent in {"episode_outline_plan_4", "episode_outline_plan_5"}
    is_characters_path = p.startswith("characters/") or p.rstrip("/") == "characters"
    doc = _describe_doc_path(p)

    if action == "read":
        # Outline-generation dependency reads: never surface as a character main task.
        if outline_stage:
            if is_characters_path:
                return f"正在读取{doc}作参考" if doc else "正在读取人物参考"
            if "project_brief" in p or "synopsis" in p or p.startswith("ledger/"):
                return f"正在回顾{doc}" if doc else "正在准备粗纲"
            if "outline" in p:
                return "正在整理大纲结构"
            return "正在准备粗纲"
        if episode_outline:
            if is_characters_path:
                return f"正在读取{doc}作参考" if doc else "正在读取人物参考"
            if "outline" in p or "project_brief" in p or "synopsis" in p:
                return f"正在回顾{doc}，准备集纲" if doc else "正在准备集纲"
            return "正在准备集纲"
        # 通用读取：目录/账本类用“整理”，内容类用“回顾”，均带具体文档名。
        if p.rstrip("/") in {"characters", "episodes"} or p.startswith("ledger/"):
            return f"正在整理{doc}" if doc else "正在整理项目内容"
        if doc:
            return f"正在回顾{doc}"
        return "正在读取项目内容"
    elif action == "write":
        if outline_stage and ("outline" in p or p.endswith(".md")):
            return f"正在写入{doc}" if doc else "正在生成故事大纲"
        if episode_outline and ("episode_outline" in p or "outline" in p):
            return f"正在写入{doc}" if doc else "正在生成集纲"
        if doc:
            return f"正在写入{doc}"
        return "正在写入内容"
    elif action == "list":
        if outline_stage:
            return "正在准备粗纲"
        if episode_outline:
            return "正在准备集纲"
        return f"正在整理{doc}" if doc else "正在整理项目内容"
    elif action == "skill":
        if outline_stage:
            return "正在构思粗纲"
        if episode_outline:
            return "正在构思集纲"
        return "正在构思剧情"
    return ""


def mark_project_cancelled(project_id: str, run_id: str = "") -> None:
    """Best-effort cancellation gate for long-running project writes.

    R03: delegates to packages.cancellation run-scoped registry.
    """
    if not project_id:
        return
    from packages.cancellation import request_cancel

    request_cancel(project_id=str(project_id), run_id=str(run_id or ""), reason="cancelled")


def clear_project_cancelled(project_id: str, run_id: str = "") -> None:
    """Clear finished-run cancel state only.

    Must not be used as a turn-start second source of truth.
    """
    if not project_id and not run_id:
        return
    from packages.cancellation import clear_context

    clear_context(project_id=str(project_id or ""), run_id=str(run_id or ""))


def _is_project_cancelled(project_id: str, run_id: str = "") -> bool:
    from packages.cancellation import is_cancelled

    return is_cancelled(project_id=str(project_id or ""), run_id=str(run_id or ""))


def start_methodology_trace(
    run_id: str,
    project_id: str,
    page: str,
    expected_skills: list[str] | None = None,
) -> None:
    """Start a per-thread methodology trace for one Hermes run.

    The trace is ALSO registered under a global run_id → trace map so worker
    threads (Hermes runs tools in ThreadPoolExecutor workers, which have a
    different ident and never see the main thread's registration) can reach the
    same dict object. A follow-up start for the same run_id REUSES the existing
    trace (keeps already-collected writes) instead of replacing it with a fresh
    empty one — that is what made collect-mode writes appear "lost" and drove
    the wrote-no-docs follow-up loop.
    """
    set_active_page(page)
    existing = _METHODOLOGY_TRACES_BY_RUN.get(run_id)
    if existing is not None:
        existing["page"] = page
        existing["expected_skills"] = list(expected_skills or [])
        _METHODOLOGY_TRACES_BY_THREAD[threading.get_ident()] = existing
        return
    trace = {
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
        "pending_workspace_writes": [],
        "warnings": [],
        "tool_failure_counts": {},
        "episode_write_attempts": [],
    }
    _METHODOLOGY_TRACES_BY_RUN[run_id] = trace
    _METHODOLOGY_TRACES_BY_THREAD[threading.get_ident()] = trace


def set_methodology_trace_field(key: str, value) -> None:
    """Attach structured runtime metadata to the active tool trace."""
    trace = _active_methodology_trace()
    if trace is not None and str(key or "").strip():
        trace[str(key).strip()] = value


def consume_methodology_trace() -> dict:
    """Return and clear the current thread's methodology trace."""
    trace = _METHODOLOGY_TRACES_BY_THREAD.pop(threading.get_ident(), None)
    if trace is not None:
        rid = str(trace.get("run_id") or "").strip()
        if rid:
            _METHODOLOGY_TRACES_BY_RUN.pop(rid, None)
    return trace or {}


def _active_methodology_trace() -> Optional[dict]:
    trace = _METHODOLOGY_TRACES_BY_THREAD.get(threading.get_ident())
    if trace is not None:
        return trace
    # Hermes runs concurrent tool calls in ThreadPoolExecutor workers; those
    # worker threads have a different ident and never see the trace the main
    # thread registered. Fall back to the most recently started trace so
    # collect-mode writes from a worker are still recorded instead of silently
    # dropped (which made the orchestrator think "wrote no docs" and forced
    # follow-up retries → dead loop + wasted spend). Self-heal: bind this
    # worker thread to the found trace so later writes in the same worker keep
    # hitting the same dict object.
    for tid, candidate in reversed(tuple(_METHODOLOGY_TRACES_BY_THREAD.items())):
        _METHODOLOGY_TRACES_BY_THREAD[threading.get_ident()] = candidate
        return candidate
    return None


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
    policy = active_project_write_policy(run_id=_policy_run_id_from_trace()) or {}
    if (
        tool_name == "write_project_doc"
        and str(policy.get("page") or "") == "episodes"
        and str(policy.get("action_intent") or "") in {"preset_execute", "custom_execute", "workflow2_execute"}
    ):
        _append_unique_trace_list("warnings", f"episode_write_rejected_once: {message}")
        # Multi-episode SSS/preset: refuse this call but keep the agent turn so
        # remaining targets can still be written. Single-episode turns still stop.
        if _is_multi_episode_batch_policy(policy):
            return tool_error(
                message + " 请改写或压缩后继续写本批剩余目标集，不要结束回合。",
                stop_current_turn=False,
            )
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
            "title": card.get("title"),
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


def set_project_write_policy(policy: dict | None, *, run_id: str = "") -> None:
    """Set write policy for the current agent execution thread.

    P2 权威身份返工：策略同时按 run_id 登记（_WRITE_POLICIES_BY_RUN），
    worker 线程凭本轮 run_id 显式取得同一份冻结上下文，不再靠"最近一个"
    猜。run_id 与 policy["run_id"] 不一致时拒绝登记，调用方必须传本轮真实 run。
    """
    _set_identity_policy(policy, run_id=run_id)


def clear_project_write_policy(*, run_id: str = "") -> None:
    """清理本轮写策略：当前线程＋该 run 在各线程的残留绑定一并清除。

    P2 权威身份返工：worker 线程一旦绑定过期策略会一直沿用（旧自愈逻辑），
    因此按 run_id 横扫所有线程绑定，不只清当前线程。请求结束、异常和取消
    路径都必须带 run_id 调用（orchestrator finally 保证）。
    """
    _clear_identity_policy(run_id=run_id)


def _policy_run_id_from_trace() -> str:
    """本轮 run 亲和：从方法论 trace 取 run_id，供策略按 run 精确取得。

    trace 仍沿用既有 _active_methodology_trace 通道（含 worker 可达性）；
    策略侧只做精确键匹配，不再叠加第二套"最近"兜底——两层各用一套
    "最近"且可能指向不同 run，正是跨项目串线的结构成因。
    """
    trace = _active_methodology_trace()
    if isinstance(trace, dict):
        return str(trace.get("run_id") or "").strip()
    return ""


def active_project_write_policy(*, run_id: str = "") -> Optional[dict]:
    """取本轮写策略：只认精确绑定，不认"最近一个"。

    P2 权威身份返工：删除"最近注册策略"兜底（该兜底不校验归属，
    还会自愈永久粘住 worker 线程）。解析顺序：
    1. 显式 run_id（非空）→ _WRITE_POLICIES_BY_RUN 精确命中即返回；
    2. 当前线程精确绑定（同线程直调与直设策略兼容）。
    两者皆无即 None（调用方 fail-closed），绝不返回别的 run 的策略，
    也绝不把"最近 set 的任意策略"当成当前策略。
    """
    return _active_identity_policy(run_id=run_id)


def _active_workspace_snapshot_cache() -> dict:
    policy = active_project_write_policy(run_id=_policy_run_id_from_trace()) or {}
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


def _is_multi_episode_batch_policy(policy: Optional[dict] = None) -> bool:
    """True when multi-episode batch must continue after one write fail/success."""
    pol = policy if isinstance(policy, dict) else (active_project_write_policy(run_id=_policy_run_id_from_trace()) or {})
    action = str(pol.get("action_intent") or "").strip()
    if action == "workflow2_execute":
        return True
    raw_target = pol.get("script_target")
    if isinstance(raw_target, dict):
        try:
            return parse_script_target(raw_target).episode_range.count > 1
        except ScriptDocumentError:
            return False
    specific = [
        str(item).replace("\\", "/").strip()
        for item in (pol.get("allowed_specific_writes") or [])
        if str(item).strip()
    ]
    return specific.count(SCRIPT_PATH) > 1


def _path_allowed_by_policy(project_id: str, path: str) -> Optional[str]:
    policy = active_project_write_policy(run_id=_policy_run_id_from_trace())
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
        root = _projects_root_for(project_id)
        return _resolver(project_id, path, projects_root=root)
    except ImportError:
        pass

    # Fallback: basic traversal protection (when resolver module unavailable)
    project_root = (_projects_root_for(project_id) / project_id).resolve()
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


def _project_doc_sort_key(path: Path) -> tuple[int, str]:
    normalized = path.as_posix().replace("\\", "/").lower()
    return (0 if normalized == SCRIPT_PATH else 1, normalized)


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
    path = _canonical_project_doc_path(path).replace("\\", "/").strip().lstrip("./")

    if path.startswith("episodes/") and path != SCRIPT_PATH:
        return _tool_failure(
            "read_project_doc",
            project_id,
            "剧集正文只有一个正式资产，请读取 episodes/script.md。",
        )

    if _is_project_cancelled(project_id):
        return _tool_failure("read_project_doc", project_id, "本轮任务已停止，拒绝继续读取项目内容。")

    err = _check_project_id(project_id)
    if err:
        return _tool_failure("read_project_doc", project_id, err)

    # Agents often pass a directory (e.g. characters/ or outline_variants/5/)
    # to "read" when they mean list. Route those to list_project_docs instead
    # of treating them as path-traversal failures.
    stripped_for_dir = str(path or "").strip().replace("\\", "/").strip("/")
    looks_like_dir = (
        not stripped_for_dir
        or stripped_for_dir.endswith("/")
        or ("." not in Path(stripped_for_dir).name)
    )
    if looks_like_dir and _resolve_project_dir(project_id, path) is not None:
        return list_project_docs(
            {
                "project_id": project_id,
                "path": stripped_for_dir,
                "include_content": False,
            }
        )

    _emit_progress("read", path, phase="started")
    target = _resolve_project_path(project_id, path)
    if target is None:
        _emit_progress("read", path, phase="failed")
        return _tool_failure(
            "read_project_doc",
            project_id,
            (
                f"Invalid file path: {path!r}. Use a concrete project file "
                f"(e.g. outline_variants/5/outline.md or characters/01.md), "
                f"or list_project_docs for a directory."
            ),
        )

    snapshot_cache = _active_workspace_snapshot_cache()
    snapshot_files = snapshot_cache.get("files") if isinstance(snapshot_cache.get("files"), dict) else {}
    if path in snapshot_files:
        content = str(snapshot_files.get(path) or "")
        _append_unique_trace_list("project_docs_read", path)
        _emit_progress("read", path, phase="completed")
        return tool_result(
            success=True,
            content=content,
            path=path,
            bytes=len(content),
            source="workspace_snapshot",
        )

    if not target.exists():
        _emit_progress("read", path, phase="failed")
        return _tool_failure("read_project_doc", project_id, f"File not found: {path}")

    if not target.is_file():
        # Directory reached file resolver — hand off to list for better recovery.
        _emit_progress("read", path, phase="failed")
        listed = list_project_docs(
            {
                "project_id": project_id,
                "path": stripped_for_dir,
                "include_content": False,
            }
        )
        return listed

    try:
        content = target.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        _emit_progress("read", path, phase="failed")
        return _tool_failure(
            "read_project_doc",
            project_id,
            f"Cannot read binary file: {path}"
        )
    except Exception as exc:
        _emit_progress("read", path, phase="failed")
        return _tool_failure("read_project_doc", project_id, f"Read error: {exc}")

    _append_unique_trace_list(
        "project_docs_read",
        target.relative_to(_PROJECTS_ROOT / project_id).as_posix(),
    )
    _emit_progress("read", path, phase="completed")

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
        return _dir_resolver(project_id, path, projects_root=_projects_root_for(project_id))
    except ImportError:
        pass

    # Fallback: treat root aliases as project root and allow only known
    # listable directories. Keep this path strict because it runs when the
    # canonical resolver cannot be imported in packaged builds.
    stripped = (path or "").strip()
    normalized = "" if stripped in {"", ".", "/", "./", "\\"} else stripped.replace("\\", "/").strip("/")
    if ".." in normalized.split("/"):
        return None
    known_dirs = {
        "",
        "characters",
        "episodes",
        "ledger",
        "runs",
        "traces",
        "manhua_prompts",
        "discussion_handoff",
        "submission",
        "novel",
        "outline_variants",
        "outline_variants/4",
        "outline_variants/5",
    }
    if normalized not in known_dirs:
        return None
    project_root = (_projects_root_for(project_id) / project_id).resolve()
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

    # If the model listed a concrete file path by mistake, read it instead of
    # failing Invalid directory (common free-chat recovery loop).
    stripped_list = str(path or "").strip().replace(chr(92), "/").strip("/")
    if stripped_list and "." in Path(stripped_list).name:
        file_target = _resolve_project_path(project_id, stripped_list)
        if file_target is not None:
            return read_project_doc({"project_id": project_id, "path": stripped_list})

    _emit_progress("list", path or ".", phase="started")
    snapshot_cache = _active_workspace_snapshot_cache()
    snapshot_dirs = snapshot_cache.get("dirs") if isinstance(snapshot_cache.get("dirs"), dict) else {}
    normalized_input = "" if (path or "").strip() in {"", ".", "/", "./", "\\"} else (path or "").strip().replace("\\", "/").strip("/")
    if normalized_input in snapshot_dirs:
        result_files = []
        snapshot_children = [
            child for child in (snapshot_dirs.get(normalized_input) or [])
            if not (
                normalized_input.rstrip("/") == "episodes"
                and str(child.get("path") or "").replace("\\", "/") != SCRIPT_PATH
            )
        ]
        for child in sorted(snapshot_children, key=lambda item: _project_doc_sort_key(Path(str(item.get("path") or "")))):
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
        _emit_progress("list", path or ".", phase="completed")
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
        _emit_progress("list", path or ".", phase="failed")
        return tool_error(
            f"Invalid directory: {path!r}. Use '' / '.' for the project root, "
            "or a known subdirectory (characters/, episodes/, ledger/, "
            "outline_variants/, outline_variants/4/, outline_variants/5/, "
            "manhua_prompts/, runs/, traces/)."
        )

    if not target.exists():
        _emit_progress("list", path or ".", phase="completed")
        return tool_result(success=True, path=path, files=[], dirs=[], count=0)

    if not target.is_dir():
        _emit_progress("list", path or ".", phase="failed")
        return tool_error(f"Not a directory: {path}")

    project_root = (_PROJECTS_ROOT / project_id).resolve()
    files = sorted(
        [
            child for child in target.iterdir()
            if child.is_file()
            and not (target.name == "episodes" and child.name != "script.md")
        ],
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
    _emit_progress("list", path or ".", phase="completed")

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
        path (str):      File path relative to the project directory
        content (str):   File content to write

    project_id 不再是模型参数：服务端按本轮冻结身份执行；若仍传入，
    与冻结不一致即拒绝，一致则忽略（见下方身份门）。
    """
    path = args.get("path", "")
    content = args.get("content", "")

    # P2 权威身份返工：身份只读冻结上下文，不读模型参数、不读进程最近值。
    # - 策略缺失（无本线程绑定、无本轮 run 登记）→ 整轮停止，不退回模型值，
    #   不计 stop-loss 预算（tool_error，非 _tool_failure）；
    # - 冻结身份 = policy["frozen_project_id"]（入口冻结盖章）；兼容直设策略
    #   时退到 policy["project_id"]（调用方自保证，仅测试与非模型直调）；
    # - 模型若仍传 project_id：与冻结不一致即拒绝（零副作用；篡改信号计入
    #   stop-loss，与旧轮行为一致）；一致或缺席都不改变身份（缺席是提示词
    #   整改后的正常形态）。
    # 拒绝分支早于 manifest/pending/磁盘三者，后续逻辑不可达。
    frozen_policy = active_project_write_policy(run_id=_policy_run_id_from_trace())
    if frozen_policy is None:
        return tool_error(
            "本轮缺少已冻结的项目身份，已停止写入（未写入任何内容）。"
            "请从当前项目重新发起该步骤。",
            stop_current_turn=True,
        )
    frozen_project_id = str(
        frozen_policy.get("frozen_project_id") or frozen_policy.get("project_id") or ""
    ).strip()
    if not frozen_project_id:
        return tool_error(
            "本轮冻结的项目身份为空，已停止写入（未写入任何内容）。"
            "请从当前项目重新发起该步骤。",
            stop_current_turn=True,
        )
    model_project_id = str(args.get("project_id", "") or "").strip()
    if model_project_id and model_project_id != frozen_project_id:
        return _tool_failure(
            "write_project_doc",
            frozen_project_id,
            "项目身份不一致：本轮归属项目 "
            f"{frozen_project_id}，但写入参数为 {model_project_id}，"
            "已拒绝（未写入任何内容）。请从当前项目重新发起该步骤。",
        )
    project_id = frozen_project_id

    # Episode duplicate-guard state, initialized at function scope so the
    # canonicalize-time check (after the SCRIPT_PATH block) can safely read it
    # even when this write is NOT episodes/script.md (e.g. pending revisions).
    _episode_seen_keys: list | None = None
    _episode_key: str | None = None

    if not isinstance(path, str) or not path.strip():
        return _tool_failure(
            "write_project_doc",
            project_id,
            "项目文档写入 path 不能为空；请使用当前合同指定的正式目标路径。",
        )

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
    path = _canonical_project_doc_path(path).replace("\\", "/").strip().lstrip("./")
    policy = active_project_write_policy(run_id=_policy_run_id_from_trace()) or {}
    if path.startswith("episodes/") and path != SCRIPT_PATH:
        return _tool_failure(
            "write_project_doc",
            project_id,
            "剧集正文只有一个正式目标，必须写入 episodes/script.md 并携带逻辑集范围。",
        )
    # Every screenplay candidate must pass the shared write-time gate before
    # it can enter the formal artifact pipeline.
    _episode_effective_chars: int | None = None
    _episode_attempt_payload: dict | None = None
    _episode_target = None
    if isinstance(content, str) and path == SCRIPT_PATH:
        content, _discarded_contract = _strip_episode_contract_block(content)
        if not content.strip():
            return _tool_failure("write_project_doc", project_id, "剧集正文为空，无法写入。")
        _validated_script = _validate_script_candidate(content, policy)
        if _validated_script[0] is None:
            _validate_reason = _validated_script[1]
            expected_target = _script_target_from_policy(policy)
            range_detail = (
                expected_target.episode_range.label()
                if expected_target is not None
                else "no_script_target"
            )
            _reason_guidance = {
                "no_script_target": "当前写入缺少有效 script_target，目标区间未知，请检查写剧任务的目标集范围配置。",
                "parse_failed": "剧集标题行格式错误：目标区间内每集必须使用独立一行的第N集标题，不要合并多集或改写标题格式。",
                "empty_episodes": "正文为空或没有可识别的剧集段落，无法提交。",
                "range_mismatch": "提交区间与系统指定的连续范围不一致，请只提交系统指定的连续范围（目标为" + range_detail + "）。",
            }
            return _tool_failure(
                "write_project_doc",
                project_id,
                _reason_guidance.get(str(_validate_reason), "剧集候选校验未通过（" + range_detail + "）。"),
            )
        content, _episode_target = _validated_script
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
            seen_keys = trace.setdefault("_episode_write_keys_seen", [])
            episode_key = pending_write_key(
                {
                    "path": normalized_path_for_gate,
                    "episode_range": _episode_target.episode_range.as_list()
                    if _episode_target is not None
                    else None,
                }
            )
            # Defer marking the path as "already delivered" until the candidate
            # actually PASSES the quality gate and its pending write is recorded.
            # Recording seen at this point (before quality) makes a rejected
            # rewrite of the same episode look like a duplicate → the model's
            # correction attempt is ignored → wrote-no-docs follow-up loop.
            _episode_seen_keys = seen_keys
            _episode_key = episode_key

        from packages.quality.candidate_gate import evaluate_script_candidate_per_episode

        _trace_skills = list((trace or {}).get("skills_loaded") or [])
        # run_agent_task always compiles and injects the QualityPack for execute
        # turns (compile_quality_pack writing_guidance + _preload_required_skills).
        # The per-thread trace marker can fail to reach a Hermes worker under
        # follow-up reuse, so an active execute-turn write policy is authoritative:
        # the pack WAS injected and quality_pack_not_loaded must not false-block
        # an otherwise valid candidate (modification-workflow script repairs).
        _quality_pack_loaded = bool(
            (trace or {}).get("quality_pack_loaded")
            or _trace_skills
            or str(policy.get("action_intent") or "").strip()
        )
        _quality = evaluate_script_candidate_per_episode(
            content,
            path=normalized_path_for_gate,
            quality_pack_loaded=_quality_pack_loaded,
            skills_loaded=_trace_skills,
        )
        # The evaluator is a review instrument only. It supplies concrete
        # findings for the trace and later Agent review; it never blocks a
        # structurally valid screenplay from entering the artifact pipeline.
        _episode_attempt_payload = {
            "path": normalized_path_for_gate,
            "phase": "initial",
            "attempt": 1,
            "effective_chars": _body_chars,
            "accepted": True,
            "quality": _quality.to_dict(),
        }
        for issue in _quality.issues:
            _append_unique_trace_list(
                "warnings",
                f"episode_quality_advisory:{issue.code}:{issue.path or normalized_path_for_gate}:{issue.message}",
            )
        # 波别要求：剧集正文严禁破折号「——」（DeepSeek 强写、SKILL/prompt 都管不住），
        # 写盘兜底：把「——」替换成全角逗号（对白/动作的连接停顿用逗号，语义无损）。
        content = content.replace("——", "，")
        # 波别要求：△ 动作符号必须顶格行首，不能跟在对白后面同一行，且动作块
        # 前必须空一行。写盘兜底：同时识别 ▲（模型常写）与 △。
        # ① 同一行内跟在其它文字后的动作标记 → 拆成独立行并前插空行；
        # ② 已是行首但前一行为非空（无空行分隔）→ 补一个空行；
        # ③ 去掉动作标记前的行首空格。
        content = re.sub(r"^[ \t]+(?=[▲△])", "", content, flags=re.MULTILINE)
        content = re.sub(r"(?<=.)[ \t]*(?=[▲△])", "\n\n", content)
        content = re.sub(r"\n{3,}", "\n\n", content)
        # 已是行首但前一行为非空（无空行分隔）→ 补一个空行
        content = re.sub(r"(?<=[^\n])\n(?=[▲△])", "\n\n", content)
    # ──────────────────────────────────────────────────────────────────

    _emit_progress("write", path, phase="started")
    policy_error = _path_allowed_by_policy(project_id, path)
    if policy_error:
        _emit_progress("write", path, phase="failed")
        return _tool_failure("write_project_doc", project_id, policy_error)

    err = _check_project_id(project_id)
    if err:
        return _tool_failure("write_project_doc", project_id, err)

    target = _resolve_project_path(project_id, path)
    if target is None:
        _emit_progress("write", path, phase="failed")
        return _tool_failure("write_project_doc", project_id, f"Path traversal blocked: {path!r}")

    normalized_path = target.relative_to(_PROJECTS_ROOT / project_id).as_posix()
    write_mode = str(policy.get("write_mode") or "direct").strip() or "direct"
    trace = _active_methodology_trace()
    run_id = str(trace.get("run_id") or "") if trace else ""

    # Progressive outline writes are a run-level contract.  The model may not
    # collapse all stages into one write or rewrite an earlier stage between
    # writes; the frontend's progressive view depends on this invariant.
    outline_action = str(policy.get("action_intent") or "").strip()
    outline_mode = outline_action.rsplit("_", 1)[-1] if outline_action.startswith("outline_stage_plan_") else ""
    if (
        normalized_path == f"outline_variants/{outline_mode}/outline.md"
        and outline_mode in {"4", "5"}
        and write_mode == "collect"
        and isinstance(trace, dict)
    ):
        from packages.outline_variants import outline_stage_bodies, validate_progressive_outline_write

        previous_outline = str(
            trace.get("_progressive_outline_content")
            or policy.get("progressive_outline_seed")
            or ""
        )
        valid_outline, outline_error = validate_progressive_outline_write(
            previous_content=previous_outline,
            next_content=str(content or ""),
            mode=outline_mode,
        )
        if not valid_outline:
            _emit_progress("write", normalized_path, phase="failed")
            return _tool_failure("write_project_doc", project_id, outline_error)
        trace["_progressive_outline_content"] = str(content or "")
        trace.setdefault("outline_write_stages", []).append(
            len(outline_stage_bodies(content, outline_mode))
        )

    if write_mode == "collect":
        if not run_id:
            return _tool_failure(
                "write_project_doc",
                project_id,
                "collect 模式缺少 run_id，无法发出正式 artifact 事件。",
            )

        if is_episode_outline_path(normalized_path):
            try:
                validate_episode_outline_content(
                    content,
                    allow_partial=policy.get("bridge_source") == "quick-story-sidecar-drive",
                )
            except ValueError as exc:
                return _tool_failure("write_project_doc", project_id, str(exc))

        if (
            normalized_path == "ledger/pending_episode_revisions.json"
            and str(policy.get("action_intent") or "").strip() == "episode_rewrite"
        ):
            script_file = _PROJECTS_ROOT / project_id / Path(SCRIPT_PATH)
            try:
                script_content = script_file.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as exc:
                return _tool_failure(
                    "write_project_doc",
                    project_id,
                    f"读取整部剧稿失败，不能生成单集修改记录：{exc}",
                )
            path_error = validate_pending_episode_revision_paths(
                content,
                script_content=script_content,
                expected_target=policy.get("script_target"),
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
            and str(policy.get("action_intent") or "").strip() == "episode_rewrite"
            and not (json.loads(_canonical_content).get("revisions") or [])
        ):
            return _tool_failure(
                "write_project_doc",
                project_id,
                "本次修订至少要生成一条待确认修改记录，不能写入空修改清单。",
            )

        # Duplicate guard is evaluated only after the candidate passed quality.
        # A same-episode rewrite is only "already delivered" once a previous
        # candidate actually landed in pending_workspace_writes.
        if _episode_key is not None and _episode_seen_keys is not None:
            if _episode_key in _episode_seen_keys:
                _dup_stop = not _is_multi_episode_batch_policy(policy)
                return tool_result(
                    success=True,
                    path=normalized_path_for_gate,
                    normalized_path=normalized_path_for_gate,
                    duplicate_ignored=True,
                    accepted=normalized_path_for_gate in (trace.get("project_docs_written") or []) if trace is not None else False,
                    effective_chars=_body_chars,
                    stop_current_turn=_dup_stop,
                    message=(
                        "本路径本轮已交付；请继续写本批其他目标集。"
                        if not _dup_stop
                        else "本路径本轮已交付，禁止再次生成。"
                    ),
                )
            _episode_seen_keys.append(_episode_key)

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
                episode_range=(
                    (_episode_target.episode_range.start, _episode_target.episode_range.end)
                    if _episode_target is not None else None
                ),
                stage_range=(
                    (_episode_target.stage_range.start, _episode_target.stage_range.end)
                    if _episode_target is not None and _episode_target.stage_range is not None else None
                ),
            )
        except ValueError as exc:
            return _tool_failure("write_project_doc", project_id, f"invalid artifact manifest: {exc}")
        if trace is not None:
            pending = trace.setdefault("pending_workspace_writes", [])
            payload = _manifest.to_pending_write(_canonical_content)

            if _episode_attempt_payload is not None:
                payload.update(
                    {
                        "episode_write_phase": _episode_attempt_payload["phase"],
                        "episode_write_attempt": _episode_attempt_payload["attempt"],
                        "effective_chars": _episode_attempt_payload["effective_chars"],
                    }
                )
            payload_key = pending_write_key(payload)
            existing = next(
                (item for item in pending if pending_write_key(item) == payload_key),
                None,
            )
            if existing is None:
                pending.append(payload)
            elif keep_existing_pending_payload(existing, payload):
                # W-sss-all-episodes-verifier-reject (a)：同 key 已有更完整候选时，
                # 极简存根不得覆盖；工具结果语义不变，只记机器诊断账供重试对账。
                trace.setdefault("episode_write_notes", []).append({
                    "kept": "existing",
                    "key": payload_key,
                    "existing_chars": len(str(existing.get("content") or "")),
                    "incoming_chars": len(str(payload.get("content") or "")),
                })
            else:
                existing.update(payload)
            if _episode_attempt_payload is not None:
                trace.setdefault("episode_write_attempts", []).append(_episode_attempt_payload)
        _emit_artifact_ready(project_id, normalized_path, _canonical_content, manifest=_manifest)
    else:
        try:
            target.parent.mkdir(parents=True, exist_ok=True)
            if _episode_target is not None:
                existing_content = target.read_text(encoding="utf-8") if target.exists() else ""
                content = merge_episode_range(existing_content, _episode_target.episode_range, content)
            from packages.atomic_file import replace_atomic
            from packages.workspace_text import decode_workspace_bytes, normalize_workspace_text

            content = normalize_workspace_text(content)
            replace_atomic(target, content.encode("utf-8"))
            written_back = decode_workspace_bytes(target.read_bytes())
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
                    episode_range=(
                        (_episode_target.episode_range.start, _episode_target.episode_range.end)
                        if _episode_target is not None else None
                    ),
                    stage_range=(
                        (_episode_target.stage_range.start, _episode_target.stage_range.end)
                        if _episode_target is not None and _episode_target.stage_range is not None else None
                    ),
                )
            except ValueError as exc:
                return _tool_failure("write_project_doc", project_id, f"invalid artifact manifest: {exc}")
            _emit_artifact_commit(project_id, normalized_path, content, manifest=_direct_manifest)

    _append_unique_trace_list(
        "project_docs_written",
        normalized_path,
    )
    _emit_progress("write", normalized_path, phase="completed")

    # SSS / multi-episode collect: do NOT stop the agent turn after the first
    # episode write. Stopping after each ep makes a 2-episode batch finish with
    # only one file and then report "本批未写满". stop_current_turn remains for
    # single-episode non-batch flows if needed later.
    _multi_episode_batch = _is_multi_episode_batch_policy()
    _stop_episode_collect_turn = (
        write_mode == "collect"
        and normalized_path == SCRIPT_PATH
        and not _multi_episode_batch
    )
    return tool_result(
        success=True,
        path=normalized_path,
        normalized_path=normalized_path,
        original_path=original_path if original_path != path else None,
        bytes=len(content),
        overwritten=True,
        accepted=True,
        effective_chars=_episode_effective_chars,
        quality=(
            _episode_attempt_payload.get("quality")
            if _episode_attempt_payload is not None
            else None
        ),
        stop_current_turn=_stop_episode_collect_turn,
        message=(
            "剧集候选已收集，当前内层回合立即结束。"
            if _stop_episode_collect_turn
            else (
                "剧集候选已收集，请继续写本批剩余目标集，不要结束。"
                if write_mode == "collect" and normalized_path == SCRIPT_PATH
                else None
            )
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
        market (str): REQUIRED canonical market: domestic | overseas | thailand
            (R6 市场隔离：海外请求排除国内索引；缺失 fail-closed 不回退全库)
    """
    market = (args.get("market") or "").strip().lower()
    if market not in ("domestic", "overseas", "thailand"):
        return tool_error(
            "retrieve_market_cards 需要合法 market 参数（domestic|overseas|thailand）；"
            "海外项目禁止检索国内知识索引，market 缺失时不回退全库。"
        )
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
                market=market,
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
                            "title": ir.get("title", ""),
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
    """Search reference drama information from approved knowledge first, then web.

    R6 市场隔离（用户批准保护子模块修改）：market 必填（canonical 三市场）；
    国内红果索引只对 domestic 查询开放；海外项目联网搜索词按市场限定，
    不再使用固定中文红果语境；无匹配返回 coverage_gap，不回退国内索引。
    """
    query = str(args.get("query") or "").strip()
    if not query:
        return tool_error("query is required")
    market = str(args.get("market") or "").strip().lower()
    if market not in ("domestic", "overseas", "thailand"):
        return tool_error(
            "search_reference_drama 需要合法 market 参数（domestic|overseas|thailand）；"
            "海外项目不得检索国内红果索引，market 缺失时不回退全库。"
        )
    limit = max(1, min(int(args.get("limit") or 5), 8))

    knowledge_matches: list[dict] = []
    index_path = (_REDFRUIT_ROOT / "blockbuster-cases" / "index.md").resolve()
    if market == "domestic" and index_path.exists():
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
        market_query_suffix = {
            "domestic": "短剧 漫剧 热度 集数 剧情",
            "overseas": "English vertical drama US short drama",
            "thailand": "泰剧 ละครสั้น Thai short drama",
        }.get(market, "短剧 漫剧 热度 集数 剧情")
        raw = web_search_tool(f"{query} {market_query_suffix}", limit=limit)
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
            web_results = _duckduckgo_search(f"{query} {market_query_suffix}", limit)
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
        "description": (
            "Write content to a project document file (creates directories if needed, "
            "overwrites existing file). "
            "The project is bound server-side to the current run: do NOT pass project_id "
            "(it is ignored); only pass the business-relative path and content."
        ),
        "parameters": {
            "type": "object",
            "properties": {
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
                    "description": "Optional structured prewrite contract for the requested logical episode range in episodes/script.md. Must include scene_plan, opening_conflict, protagonist_goal, ending_hook, target_chars_min, target_chars_max, os_budget. W-script-submit-contract-gap, three submission rules: (1) RANGE EXCLUSIVITY: content must contain ONLY the requested episode range; continuity anchors outside the range are dropped server-side, never merge them in. (2) TITLE FORMAT: every episode starts with its own standalone title line like 第1集; never merge episodes into one title or rewrite the title format. (3) REJECTION ECHO: a rejection names the exact cause (no_script_target/parse_failed/empty_episodes/range_mismatch); fix exactly that cause and resubmit, never blindly retry.",
                },
            },
            "required": ["path", "content"],
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

# R4-schema（Review 返工四）：canonical market 工具参数唯一合同。
# 所有注册入口读取同一份定义——handler 已在 R6 强制 fail-closed，
# schema 同步要求模型必须传入 market，禁止国内知识流入海外请求。
_MARKET_TOOL_PARAM = {
    "type": "string",
    "enum": ["domestic", "overseas", "thailand"],
    "description": (
        "REQUIRED canonical market. domestic=国内, overseas=欧美(北美), thailand=泰国. "
        "海外请求排除国内知识索引；缺失或非法值 fail-closed 不回退全库。"
    ),
}


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
                "market": dict(_MARKET_TOOL_PARAM),
            },
            "required": ["stage", "market"],
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
                "market": dict(_MARKET_TOOL_PARAM),
            },
            "required": ["query", "market"],
        },
    },
    handler=search_reference_drama,
    description="Search reference drama information from knowledge and web",
)

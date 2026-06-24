"""DeepSeek provider profile.

DeepSeek's native API is OpenAI-compatible (chat.completions) for standard
chat models (deepseek-chat, deepseek-v4-flash) and uses ``thinking`` as a
top-level request parameter or ``extra_body`` entry for reasoning control.

This profile maps Hermes ``reasoning_config`` to DeepSeek's ``thinking``
parameter so that DeepSeek V4 Flash / DeepSeek V3 properly handle
function-calling with reasoning.
"""

from typing import Any

from providers import register_provider
from providers.base import ProviderProfile


class DeepSeekProfile(ProviderProfile):
    """DeepSeek provider profile with reasoning/thinking support."""

    def build_api_kwargs_extras(
        self,
        *,
        reasoning_config: dict | None = None,
        **context: Any,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        """Map reasoning_config to DeepSeek's thinking parameter.

        DeepSeek chat models (deepseek-chat, deepseek-v4-flash) accept
        ``thinking`` as a top-level request parameter:
          - {"type": "enabled"}  → enabled with default effort
          - {"type": "disabled"} → disabled
          - {"type": "enabled", "effort": "high"} → with effort hint

        Returns (extra_body_additions, top_level_kwargs).
        """
        if reasoning_config is None or not isinstance(reasoning_config, dict):
            return {}, {}

        if reasoning_config.get("enabled") is False:
            return {}, {"thinking": {"type": "disabled"}}

        effort = str(reasoning_config.get("effort", "medium") or "medium").strip().lower()
        thinking = {"type": "enabled"}
        if effort in ("low", "medium", "high", "xhigh"):
            thinking["effort"] = "high" if effort in ("high", "xhigh") else effort
        return {}, {"thinking": thinking}

    def build_extra_body(
        self, *, session_id: str | None = None, **context: Any
    ) -> dict[str, Any]:
        """No extra_body additions for DeepSeek (thinking is top-level)."""
        return {}


deepseek = DeepSeekProfile(
    name="deepseek",
    aliases=("deepseek-chat",),
    env_vars=("DEEPSEEK_API_KEY",),
    display_name="DeepSeek",
    description="DeepSeek — native DeepSeek API",
    signup_url="https://platform.deepseek.com/",
    fallback_models=(
        "deepseek-chat",
        "deepseek-reasoner",
    ),
    base_url="https://api.deepseek.com/v1",
)

register_provider(deepseek)

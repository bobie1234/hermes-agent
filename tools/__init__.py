#!/usr/bin/env python3
"""Tools package namespace.

Keep package import side effects minimal. Importing ``tools`` should not
eagerly import the full tool stack, because several subsystems load tools while
``hermes_cli.config`` is still initializing.

Callers should import concrete submodules directly, for example:

    import tools.web_tools
    from tools import browser_tool

Python will resolve those submodules via the package path without needing them
to be re-exported here.

IMPORTANT: xiaoma_tools must be imported to register the xiaoma_project toolset.
This is done lazily via _ensure_xiaoma_tools() called from get_tool_definitions()
in model_tools.py.
"""


def check_file_requirements():
    """File tools only require terminal backend availability."""
    from .terminal_tool import check_terminal_requirements

    return check_terminal_requirements()


def _ensure_xiaoma_tools():
    """Import xiaoma_tools to register the xiaoma_project toolset with the registry.

    This is called lazily by model_tools.get_tool_definitions() to avoid
    importing the heavy xiaoma_tools module when tools are not needed.
    """
    try:
        import tools.xiaoma_tools  # noqa: F401
    except ImportError:
        pass


__all__ = ["check_file_requirements", "_ensure_xiaoma_tools"]

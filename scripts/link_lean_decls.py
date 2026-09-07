#!/usr/bin/env python3
"""Point the blueprint's Lean links at this repository's own sources.

leanblueprint turns every ``\\lean{Decl}`` tag into a link of the form
``{dochome}/find/#doc/Decl``, and with no ``\\dochome`` set it falls back to
Mathlib's documentation site (see ``leanblueprint/Packages/blueprint.py``).
None of this project's declarations live there, so every one of those links is
dead.  The URL shape is hard-coded in the plugin, so it cannot be pointed at a
repository through ``\\dochome``; this script rewrites the rendered HTML
instead, which is also where the workflow already tidies the dependency graph.

Each declaration is resolved to the file and line it is declared on, and the
link becomes a permalink into the repository at a fixed commit, so the line
numbers stay valid as the sources move.  A declaration that cannot be resolved
loses its ``href`` altogether: an ``<a>`` without one renders as plain text,
which is better than a link that 404s.

Usage::

    python scripts/link_lean_decls.py --repo owner/name --rev <sha> \\
        [--web blueprint/web] [--expect 208]

Exits non-zero if no link was found at all, if any declaration could not be
resolved, or if ``--expect`` is given and the number of links found differs.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Directories that must not contribute declarations: dependencies, and the
# Palomar submission surfaces, which restate the same names with `sorry` and
# would otherwise shadow the real definitions.
SKIP_DIRS = {".lake", "Palomar", "PalomarChallenges", "PalomarSolutions"}

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"(_root_\.)?([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
END_RE = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_.']*)")

# The anchor leanblueprint emits, e.g.
#   href="https://leanprover-community.github.io/mathlib4_docs/find/#doc/Foo.bar"
LINK_RE = re.compile(r'\s*href="[^"]*/find/#doc/([^"]+)"')


def declaration_table(root: Path) -> dict[str, tuple[str, int]]:
    """Map every declaration in the Lean sources to its file and line."""
    table: dict[str, tuple[str, int]] = {}
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root).as_posix()
        if rel.split("/")[0] in SKIP_DIRS:
            continue
        stack: list[str] = []
        with path.open(encoding="utf-8", errors="replace") as handle:
            for lineno, line in enumerate(handle, 1):
                match = NAMESPACE_RE.match(line)
                if match:
                    stack.append(match.group(1))
                    continue
                match = END_RE.match(line)
                if match and stack and stack[-1] == match.group(1):
                    stack.pop()
                    continue
                match = DECL_RE.match(line)
                if match:
                    name = match.group(2)
                    # `_root_.Foo` escapes the enclosing namespaces.
                    full = name if match.group(1) else ".".join(stack + [name])
                    table.setdefault(full, (rel, lineno))
    return table


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="owner/name on GitHub")
    parser.add_argument("--rev", required=True, help="commit the links point at")
    parser.add_argument("--web", default="blueprint/web", help="rendered site")
    parser.add_argument("--root", default=".", help="repository root")
    parser.add_argument(
        "--expect", type=int, default=None,
        help="fail unless exactly this many links are found",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    table = declaration_table(root)
    print(f"declarations found in the Lean sources: {len(table)}")

    base = f"https://github.com/{args.repo}/blob/{args.rev}"
    rewritten = 0
    dropped: set[str] = set()

    for page in sorted(Path(args.web).glob("*.html")):
        text = page.read_text(encoding="utf-8")

        def replace(match: re.Match[str]) -> str:
            nonlocal rewritten
            decl = match.group(1)
            target = table.get(decl)
            if target is None:
                dropped.add(decl)
                return ""
            rewritten += 1
            path, lineno = target
            return f' href="{base}/{path}#L{lineno}"'

        new_text, hits = LINK_RE.subn(replace, text)
        if hits:
            page.write_text(new_text, encoding="utf-8")
            print(f"  {page.name}: {hits}")

    total = rewritten + len(dropped)
    print(f"links rewritten: {rewritten}")
    if dropped:
        print(f"declarations not found, href dropped: {len(dropped)}")
        for decl in sorted(dropped):
            print(f"  {decl}")

    if total == 0:
        print("error: no Lean links found -- has the upstream template changed?")
        return 1
    if dropped:
        print("error: every cited declaration should resolve in this repository")
        return 1
    if args.expect is not None and rewritten != args.expect:
        print(f"error: expected {args.expect} links, rewrote {rewritten}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

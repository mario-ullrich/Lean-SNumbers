#!/usr/bin/env python3
"""Check that every declaration the blueprint cites exists in the compiled project.

Every ``\\lean{Decl}`` tag in ``blueprint/src/content.tex`` names a Lean
declaration.  This script collects these names, writes a Lean file that imports
the root module of each library of the project, and asks Lean whether the
resulting environment contains each name.  A blueprint citing a declaration that
the project no longer has is wrong, so a missing name fails the run.

The check runs inside Lean itself, through ``lake env lean``, and therefore sees
exactly the environment the build produced.  It is the check that
``leanblueprint checkdecls`` performs, done without the ``checkdecls``
executable: that executable links Lake, and loading a project that imports Lake
a second time, as Mathlib does through ``importGraph``, is rejected by recent
Lean versions.

Run it from the project root after ``lake build``::

    python blueprint/scripts/check_lean_decls.py

Exits non-zero if no ``\\lean`` tag is found, or if any cited name is missing.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

CONTENT = Path("blueprint/src/content.tex")
# The root module of every `lean_lib` in `lakefile.toml`, as `checkdecls` imports them.
ROOTS = ["SNumbers", "BasicResults", "AddOns", "PalomarChallenges", "PalomarSolutions"]
CHECK_FILE = Path(".lake/check_lean_decls.lean")

LEAN_TAG = re.compile(r"\\lean\{([^}]*)\}")


def cited_names(tex: str) -> list[str]:
    """The declaration names in all `\\lean{...}` tags, each once, sorted.

    Lines starting with `%` are LaTeX comments and are skipped."""
    text = "\n".join(line for line in tex.splitlines() if not line.lstrip().startswith("%"))
    tagged = {name.strip() for group in LEAN_TAG.findall(text) for name in group.split(",")}
    return sorted(tagged - {""})


def lean_source(names: list[str]) -> str:
    """A Lean file that fails, naming them, if any of `names` is not declared."""
    imports = "".join(f"import {root}\n" for root in ROOTS)
    listed = ",\n    ".join(f'"{name}"' for name in names)
    return f"""{imports}
open Lean Elab Command in
run_cmd do
  let names : List String := [
    {listed}]
  let env ← getEnv
  let missing := names.filter fun n => !env.contains n.toName
  unless missing.isEmpty do
    throwError m!"declarations cited by the blueprint but missing: {{missing}}"
  logInfo m!"all {{names.length}} declarations cited by the blueprint exist"
"""


def main() -> int:
    names = cited_names(CONTENT.read_text(encoding="utf-8"))
    if not names:
        print(f"no \\lean tag found in {CONTENT}", file=sys.stderr)
        return 1
    CHECK_FILE.parent.mkdir(exist_ok=True)
    CHECK_FILE.write_text(lean_source(names), encoding="utf-8")
    result = subprocess.run(["lake", "env", "lean", str(CHECK_FILE)])
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())

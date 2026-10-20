#!/usr/bin/env python3
"""Give every result whose proof has dependencies the "Uses" button in its heading, and
order every Uses dialog by the numbers of the results it lists.

leanblueprint puts the button, which opens the list of results a statement rests on, into
the heading only when the *statement* carries a ``\\uses``; the list then also contains
the ``\\uses`` of the proof. A result whose ``\\uses`` sit in the proof alone, the usual
case, gets no button, and its dependencies can only be read off the dependency graph.

This script reads every ``\\uses`` from the blueprint source, in the statement and in the
proof that follows it or names it with ``\\proves``, and inserts into each heading that
has no button yet, but dependencies to show, the same button and dialog that the plugin
renders, so that the page script serves it like the others.

Every dialog lists its results in the order of the document, which is the order of their
numbers. A dialog that leanblueprint renders concatenates the statement's list and the
proof's list, so the script reorders its entries; the dialogs it adds are built in that
order from the start. The sources keep every ``\\uses`` in document order as well, and the
two lists of a result disjoint: leanblueprint appends the proof's list to the statement's
list unchecked, so a label in both would appear twice. The script fails on a list out of
order or on a repeat, naming the result; ``--sort-source`` rewrites the lists of the
source into document order and stops.

The pages are edited in place. The script also fails if a cited label has no result on
the pages, or if it finds no result headings at all, which is how an upstream template
change would show up; a second run changes nothing.

Usage::

    python blueprint/scripts/add_uses_buttons.py [--source SRC] [--web DIR] [--sort-source]
"""

from __future__ import annotations

import argparse
import glob
import io
import os
import re
import sys

KINDS = "theorem|proposition|lemma|corollary|remark|definition|example"
BS = re.escape(chr(92))  # a backslash, kept out of the source text of this file
WIDTH = 88               # the line length of the blueprint sources

ICON = ('<svg  class="icon icon-{name} "><use xlink:href="symbol-defs.svg#icon-{name}">'
        '</use></svg>\n')

BUTTON = (
    "\n    <button class=\"modal\">" + ICON.format(name="mindmap") + "</button>\n"
    "        <div class=\"modal-container\">\n"
    "      <div class=\"modal-content\">\n"
    "        <header>\n"
    "          <h1>Uses</h1>\n"
    "          <button class=\"closebtn\">" + ICON.format(name="cross") + "</button>\n"
    "        </header>\n"
    "        \n"
    "        <ul class=\"uses\">\n"
    "{items}"
    "        </ul>\n"
    "    \n"
    "      </div>\n"
    "    </div>\n"
)
ITEM = "          <li><a href=\"{url}\">{caption} {ref}</a></li>\n"

USES = re.compile(BS + r"uses\{([^}]*)\}")
RESULT = re.compile(BS + r"begin\{(" + KINDS + r")\}(.*?)" + BS + r"end\{\1\}", re.S)
PROOF = re.compile(BS + r"begin\{proof\}(.*?)" + BS + r"end\{proof\}", re.S)
LABEL = re.compile(BS + r"label\{([^}]*)\}")


def split(arg: str) -> list[str]:
    return [x.strip() for x in arg.split(",") if x.strip()]


def tags(block: str, name: str) -> list[str]:
    """The labels listed in every ``\\name{...}`` of ``block``, in order."""
    out: list[str] = []
    for m in re.finditer(BS + name + r"\{([^}]*)\}", block):
        out += split(m.group(1))
    return out


def wrap(items: list[str], nl: str, indent: int) -> str:
    """A ``\\uses`` command over lines of at most WIDTH columns, continuation lines
    indented by ``indent`` spaces, as the source writes them."""
    lines, cur = [], chr(92) + "uses{"
    for i, u in enumerate(items):
        piece = u + ("," if i < len(items) - 1 else "}")
        if cur.endswith("{"):
            cur += piece
        elif len(cur) + 1 + len(piece) <= WIDTH:
            cur += " " + piece
        else:
            lines.append(cur)
            cur = " " * indent + piece
    lines.append(cur)
    return nl.join(lines)


def continuation_indent(text: str) -> int:
    """The indentation most of the multi-line ``\\uses`` lists of ``text`` give their
    continuation lines; six spaces, the width of ``\\uses{``, when there is none."""
    counts: dict[int, int] = {}
    for m in USES.finditer(text):
        for line in m.group(1).split("\n")[1:]:
            ind = len(line) - len(line.lstrip(" "))
            counts[ind] = counts.get(ind, 0) + 1
    return max(counts, key=counts.get) if counts else 6


class Source:
    """The results of the blueprint source: their document order and their two lists."""

    def __init__(self, path: str):
        self.path = path
        with io.open(path, "r", encoding="utf-8", newline="") as f:
            self.text = f.read()
        self.nl = "\r\n" if "\r\n" in self.text else "\n"
        self.indent = continuation_indent(self.text)
        self.position: dict[str, int] = {}
        results = []
        for m in RESULT.finditer(self.text):
            label = LABEL.search(m.group(2))
            if label:
                self.position[label.group(1)] = len(self.position)
                results.append({"label": label.group(1), "end": m.end(),
                                "stmt": tags(m.group(2), "uses"), "proof": []})
        for m in PROOF.finditer(self.text):
            proves = tags(m.group(1), "proves")
            if proves:
                owners = [r for r in results if r["label"] in proves]
            else:
                owners = [r for r in results if r["end"] <= m.start()][-1:]
            for r in owners:
                r["proof"] += [u for u in tags(m.group(1), "uses") if u not in r["proof"]]
        self.deps = {r["label"]: (r["stmt"], r["proof"]) for r in results}

    def order(self, labels: list[str]) -> list[str]:
        return sorted(labels, key=lambda u: self.position.get(u, len(self.position)))

    def problems(self) -> list[str]:
        """Lists out of document order, labels that are no result, and repeats."""
        out = []
        for m in USES.finditer(self.text):
            items = split(m.group(1))
            unknown = [u for u in items if u not in self.position]
            if unknown:
                out.append(f"no result has the label {', '.join(unknown)}")
            elif items != self.order(items):
                out.append(f"out of document order: {', '.join(items)}")
        for label, (stmt, proof) in self.deps.items():
            rep = [u for u in proof if u in stmt]
            if rep:
                out.append(f"the proof of {label} repeats {', '.join(rep)} from the uses of its statement")
        return out

    def sort_lists(self) -> int:
        """Rewrite every list of the source into document order; the number of lists changed."""
        edits = []
        for m in USES.finditer(self.text):
            items = split(m.group(1))
            ordered = self.order(items)
            if items != ordered and all(u in self.position for u in items):
                edits.append((m.start(), m.end(), wrap(ordered, self.nl, self.indent)))
        text = self.text
        for s, e, r in sorted(edits, reverse=True):
            text = text[:s] + r + text[e:]
        if edits:
            with io.open(self.path, "w", encoding="utf-8", newline="") as f:
                f.write(text)
        return len(edits)


HEADING = re.compile(
    r'<div class="(\w+)_thmwrapper[^"]*" id="([^"]+)">\s*<div class="\w+_thmheading">'
    r'\s*<span class="\w+_thmcaption">\s*([^<]*?)\s*</span>'
    r'(?:\s*<span class="\w+_thmlabel">([^<]*)</span>)?', re.S)
DIALOG = re.compile(r'(<h1>Uses</h1>.*?<ul class="uses">\n?)(.*?)(\s*</ul>)', re.S)
LI = re.compile(r'\s*<li><a href="[^"#]*#([^"]*)">.*?</a></li>\n?', re.S)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--source", default="blueprint/src/content.tex")
    parser.add_argument("--web", default="blueprint/web")
    parser.add_argument("--sort-source", action="store_true",
                        help="rewrite the uses lists of the source into document order and stop")
    args = parser.parse_args()

    src = Source(args.source)
    if args.sort_source:
        n = src.sort_lists()
        print(f"{args.source}: {n} uses lists put into document order")
        return 0
    problems = src.problems()
    if problems:
        for p in problems:
            print("error:", p)
        print("hint: --sort-source orders the lists of the source; repeats are removed by hand")
        return 1

    pages = [p for p in sorted(glob.glob(os.path.join(args.web, "*.html")))
             if not p.endswith("dep_graph_document.html")]
    texts = {p: io.open(p, encoding="utf-8").read() for p in pages}

    # where every result lives and how it is numbered
    where: dict[str, tuple[str, str, str]] = {}
    for p, h in texts.items():
        for m in HEADING.finditer(h):
            where[m.group(2)] = (os.path.basename(p), m.group(3), (m.group(4) or "").strip())
    if not where:
        print(f"error: no result headings found under {args.web} -- has the upstream template changed?")
        return 1

    added, ordered, kept, changed_pages = 0, 0, 0, 0
    for p, h in texts.items():
        out, pos = [], 0
        for m in HEADING.finditer(h):
            label = m.group(2)
            stmt, proof = src.deps.get(label, ([], []))
            uses = src.order(stmt + proof)
            content = h.find("_thmcontent", m.end())
            head_end = h.rfind("<div class=", 0, content)  # start of the content div
            heading = h[m.end():head_end]
            if not uses:
                continue
            dialog = DIALOG.search(heading)
            if dialog:
                # the plugin's dialog: put its entries into document order
                entries = list(LI.finditer(dialog.group(2)))
                order = sorted(range(len(entries)),
                               key=lambda i: src.position.get(entries[i].group(1), len(src.position)))
                if order != list(range(len(entries))):
                    body = "".join(entries[i].group(0) for i in order)
                    s = m.end() + dialog.start(2)
                    e = m.end() + dialog.end(2)
                    out.append(h[pos:s]); out.append(body); pos = e
                    ordered += 1
                else:
                    kept += 1
                continue
            rows = []
            for u in uses:
                if u not in where:
                    print(f"error: {label} uses {u}, which is no result on the pages")
                    return 1
                page, caption, ref = where[u]
                rows.append(ITEM.format(url=f"{page}#{u}", caption=caption, ref=ref))
            button = BUTTON.format(items="".join(rows))
            # the plugin's order: permalink, proof link, Uses, Lean declarations
            lean = heading.find('<button class="modal lean">')
            if lean >= 0:
                at = m.end() + lean
            else:
                at = m.end() + heading.rfind("</a>") + len("</a>")
            out.append(h[pos:at]); out.append(button); pos = at
            added += 1
        if out:
            out.append(h[pos:])
            io.open(p, "w", encoding="utf-8").write("".join(out))
            changed_pages += 1

    print(f"Uses dialogs: {added} added, {ordered} put into document order, {kept} already in order; "
          f"{changed_pages} pages changed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

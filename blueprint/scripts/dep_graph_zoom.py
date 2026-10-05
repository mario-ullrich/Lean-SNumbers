#!/usr/bin/env python3
"""Let the dependency graph, not the page, take the zoom gestures.

The dependency-graph page of leanblueprint draws the graph with d3-graphviz. Two of its
defaults get in the way of reading a large graph:

* d3's zoom ignores ctrl+wheel, which is also how a touchpad pinch reaches the page. The
  browser then zooms the whole page instead of the graph, and with it the statement that
  opens on a click, which lies outside the window or comes out huge. This script lets the
  graph take ctrl+wheel and keeps the page from zooming over the graph; a pinch moves
  little, so its steps are enlarged (``PINCH``).
* d3-graphviz stops at ten times the fitted size, too little to read a wide graph; the
  range becomes 200 times (``ZOOM``).

The page is edited in place. The script fails if the page no longer has the hooks it edits,
which is how an upstream template change would show up, and a second run changes nothing.

Usage::

    python blueprint/scripts/dep_graph_zoom.py [PAGE ...]
"""

from __future__ import annotations

import sys
from pathlib import Path

PAGES = ["blueprint/web/dep_graph_document.html"]

# The zoom range of d3-graphviz, as multiples of the fitted size (default [0.1, 10]).
FIT = ".fit(true)"
ZOOM = ".zoomScaleExtent([0.1, 200])"

# Run when the graph is drawn, at the start of the page's `interactive()`.
HOOK = "function interactive() {"
PINCH = """
    var zoom = document.getElementById("graph").__graphviz__.zoomBehavior();
    if (zoom) {
        zoom.filter(function () { return !d3.event.button; })
            .wheelDelta(function () {
                var e = d3.event;
                return -e.deltaY * (e.deltaMode === 1 ? 0.05 : e.deltaMode ? 1 : 0.002)
                    * (e.ctrlKey ? 10 : 1);
            });
    }
    document.getElementById("graph").addEventListener("wheel", function (e) {
        if (e.ctrlKey) { e.preventDefault(); }
    }, {passive: false});
"""


def main() -> int:
    for name in sys.argv[1:] or PAGES:
        page = Path(name)
        html = page.read_text(encoding="utf-8")
        if PINCH in html:
            print(f"{name}: already done")
            continue
        fit, hook = html.find(FIT), html.find(HOOK)
        if fit < 0 or hook < 0:
            print(f"error: {name} has no {FIT!r} or {HOOK!r} -- has the upstream template changed?")
            return 1
        hook += len(HOOK)
        html = html[:hook] + PINCH + html[hook:]
        html = html[:fit] + FIT + ZOOM + html[fit + len(FIT):]
        page.write_text(html, encoding="utf-8")
        print(f"{name}: zoom range widened, pinch and ctrl+wheel zoom the graph")
    return 0


if __name__ == "__main__":
    sys.exit(main())

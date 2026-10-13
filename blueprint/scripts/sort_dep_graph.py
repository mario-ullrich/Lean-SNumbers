"""Put the statements of the dependency graph into a fixed order.

plastexdepgraph writes the nodes and edges of the dependency graph in the iteration order
of Python sets, and that order changes from one run to the next, because Python hashes
strings with a random seed per process.  Graphviz lays a graph out partly according to the
order of its statements, so the same blueprint gave mirrored pictures in consecutive
builds.  This script sorts the node statements by name and the edge statements by their
endpoints, so that the graph source, and with it the picture, depends only on the
blueprint.

The graph source is the DOT text that the page passes to `renderDot`.  The default
statements for the graph, the nodes and the edges stay in front and subgraphs at the end,
each in their original order.

Usage: python blueprint/scripts/sort_dep_graph.py [PAGE]
with PAGE defaulting to blueprint/web/dep_graph_document.html.
"""

import io
import sys

START = ".renderDot(`"
END = "`)"
DEFAULTS = ("graph", "node", "edge")


def split_statements(body):
    """Split the body of a DOT graph at the semicolons that lie outside quotes, brackets
    and braces."""
    statements, current, depth, quoted, escaped = [], [], 0, False, False
    for ch in body:
        if quoted:
            current.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                quoted = False
            continue
        if ch == '"':
            quoted = True
        elif ch in "[{":
            depth += 1
        elif ch in "]}":
            depth -= 1
        elif ch == ";" and depth == 0:
            statements.append("".join(current).strip())
            current = []
            continue
        current.append(ch)
    statements.append("".join(current).strip())
    return [s for s in statements if s]


def head(statement):
    """The part of a statement before its attribute list: a node name or an edge."""
    return statement.split("[", 1)[0].strip()


def sort_graph(dot):
    """Return the DOT source with its node and edge statements sorted."""
    i = dot.index("{") + 1
    j = dot.rindex("}")
    statements = split_statements(dot[i:j])
    keyword = [s.split(None, 1)[0] for s in statements]
    defaults = [s for s, k in zip(statements, keyword) if k in DEFAULTS]
    subgraphs = [s for s, k in zip(statements, keyword) if k == "subgraph"]
    others = [s for s, k in zip(statements, keyword) if k not in DEFAULTS + ("subgraph",)]
    nodes = sorted((s for s in others if " -> " not in head(s)), key=head)
    edges = sorted((s for s in others if " -> " in head(s)), key=head)
    ordered = defaults + nodes + edges + subgraphs
    assert len(ordered) == len(statements)
    return dot[:i] + "\t" + ";\t".join(ordered) + ";\n" + dot[j:]


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "blueprint/web/dep_graph_document.html"
    page = io.open(path, encoding="utf-8", newline="").read()
    i = page.index(START) + len(START)
    j = page.index(END, i)
    page = page[:i] + sort_graph(page[i:j]) + page[j:]
    io.open(path, "w", encoding="utf-8", newline="").write(page)
    print(f"sorted the dependency graph in {path}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Set frontmatter fields of a page file: setfields.py PAGE.md key=value ... (a value is written
quoted, `true` and `false` bare); an existing line is replaced, a new one added at the end
of the frontmatter. An edit of the file, as a person would make it; the vault judges it at the open."""
import sys
path, pairs = sys.argv[1], [a.split("=", 1) for a in sys.argv[2:]]
lines = open(path, encoding="utf-8").read().split("\n")
end = lines.index("---", 1)
for k, v in pairs:
    val = v if v in ("true", "false") else '"' + v + '"'
    for i in range(1, end):
        if lines[i].split(":", 1)[0] == k:
            lines[i] = f"{k}: {val}"
            break
    else:
        lines.insert(end, f"{k}: {val}")
        end += 1
open(path, "w", encoding="utf-8").write("\n".join(lines))

#!/usr/bin/env python3
"""DEV.md against git: what no law of the vault can read.

    tools/check_dev.py VAULT OBEND_REPO FIRST LAST

For every first-parent merge `merge lane-…` on the repository between FIRST and LAST, the lane's page
and whether DEV lists it; for every lane DEV lists, whether the page's `dev:` commit is an ancestor of
LAST (the vault's law reads only the page's `ancestor:` field, which this script is the source of).
Prints one line per merge the vault does not hold as merged, and exits 1 if a listed lane's commit is
not an ancestor."""
import os, re, subprocess, sys
V, REPO, FIRST, LAST = sys.argv[1:5]
dev = open(os.path.join(V, 'DEV.md')).read()
listed = re.findall(r'\[\[lanes/(lane-[a-z0-9]+)\]\]', dev)
log = subprocess.run(['git', '-C', REPO, 'log', '--first-parent', '--format=%h %s', FIRST + '^..' + LAST],
                     capture_output=True, text=True, check=True).stdout.split('\n')
bad = 0
merged = []
for line in log:
    m = re.match(r'(\w+) merge (lane-[a-z0-9]+)', line)
    if m:
        merged.append((m.group(2), m.group(1)))
for br, h in reversed(merged):
    if br not in listed:
        page = os.path.join(V, 'lanes', br + '.md')
        state = re.search(r'^state: (\S+)', open(page).read(), re.M) if os.path.exists(page) else None
        print(f'{br}: merged on dev at {h}, not on DEV (its page says state {state.group(1) if state else "?"})')
later = 0
for br in listed:
    src = open(os.path.join(V, 'lanes', br + '.md')).read()
    d = re.search(r'^dev: "?(\w+)"?', src, re.M).group(1)
    if subprocess.run(['git', '-C', REPO, 'merge-base', '--is-ancestor', d, LAST]).returncode != 0:
        # a lane that landed after the range is on dev, later: not a fault of DEV's
        if subprocess.run(['git', '-C', REPO, 'merge-base', '--is-ancestor', LAST, d]).returncode == 0:
            later += 1
            continue
        print(f'{br}: DEV lists {d}, which is not an ancestor of {LAST}')
        bad += 1
print(f'{len(listed)} lanes on DEV ({later} landed after {LAST}), {len(merged)} merges on dev between {FIRST} and {LAST}')
sys.exit(1 if bad else 0)

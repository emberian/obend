#!/usr/bin/env bash
# On hbox: SWARM_MEM_MAX=12G swarm-build timeout --kill-after=10s 600s lean/tools/test/pancake-kmac256.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
[[ $(uname -sm) == 'Linux x86_64' ]] || { echo "Requires Linux x86-64" >&2; exit 1; }

tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
src=Obend/Lower/Pancake
lake build Obend.Lower.Pancake.PancakeKmac256 Obend.Tactic.Tooth
cake --pancake --main_return=true < "$src/kmac256.pnk" > "$tmp/kmac256.S"
cc -O2 -Wall -Wextra -Werror -static -Wl,-z,noexecstack "$src/kmac256.c" "$tmp/kmac256.S" -o "$tmp/kmac256"
lake env lean --run tests/metasystem/PancakeKmac256Test.lean "$tmp/kmac256" "$tmp/vectors"

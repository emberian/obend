#!/usr/bin/env bash
# Run from lean/ on the Linux build host inside swarm-build.
set -euo pipefail
: "${CAKE:?set CAKE to the cake-x64-64/cake executable}"
dir=.lake/build/durable-turn
mkdir -p "$dir"
lake build Obend.OS.DragonStyleAppliance Obend.Lower.Pancake.DurableTurn Obend.Consensus.SimplexLiveness
lake env lean --run tests/dragonstyle/Emit.lean "$dir/turn.pnk"
cmp "$dir/turn.pnk" Obend/Lower/Pancake/durable_turn.pnk
lake env lean --run tests/dragonstyle/Tickets.lean "$dir/tickets.bin"
"$CAKE" --pancake --main_return=true < "$dir/turn.pnk" > "$dir/turn.S"
"$CAKE" --pancake --target=arm8 --main_return=true < "$dir/turn.pnk" > "$dir/turn.arm8.S"
clang --target=aarch64-linux-gnu -c "$dir/turn.arm8.S" -o "$dir/turn.arm8.o"
readelf -h "$dir/turn.arm8.o" | grep -E 'Machine:.*AArch64'
readelf -Ws "$dir/turn.arm8.o" | grep -E 'GLOBAL.*turnIntake$'
readelf -Ws "$dir/turn.arm8.o" | grep -E 'GLOBAL.*parseFrame$'
cc -std=c11 -O2 -Wall -Wextra -Werror -Wl,-z,noexecstack \
  -Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc \
  tests/dragonstyle/powercut.c "$dir/turn.S" -o "$dir/powercut"
"$dir/powercut" "$dir/tickets.bin"

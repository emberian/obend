# Brief of lane-hvm2

Sent by the root (session 01a1ad7d, message 811, 2026-11-06T00:18:28.906Z) to agent a6cc27c5, verbatim:

    Your rung-2 work is merged (dev fb6555c, now well past it; dev is at b8a9446 with widths, the LEC and the csimp twins landed; `obend-emit-sv` and `obend` build and all verify scripts pass). Next quest, extending `Obend.Hardware.Hvm` to the fragment the reduction machine needs, which you named and refused by name:
    
    1. `fix`: recursion as λ-lifted REFs (an HVM2 `@def` per fixpoint body, the recursive call a REF to it), with `lowerBookToHvm_sound` extended; the theorem's hypothesis about `evalE` keeping values below 2^24 stays, and a fuel or a termination witness from `evalBookAt` is the induction measure. The test book gets a factorial and a loop that reads `self` through a pinned slot.
    2. Records and `get`, and sums with `case`: records as HVM CON trees (or tuples), `get` as projection by pattern, variants as a tag plus payload with `case` as a `switch` on the tag; the decoding function `d.sort.observe` extended to these sorts.
    3. λ as a value where the book returns a closure: HVM's native lambdas; state what is and is not handled.
    
    Keep the refusal-by-name for everything still outside (the object forms, activities, bitwise and fixed-point) and keep the gate shape: byte-identical committed `.hvm`, `hvm run` and `hvm run-c` against `evalBookAt` on vectors, planted wrong rules caught. Then one more thing that matters to HARDWARE.md: say in the module header, precisely, how `lowerBookToHvm`'s nets relate to `Obend.Hardware.ReductionMachine`'s `INetNode`/`ActivePair` representation (same combinators, or a translation), because rung 5 and 6 will put those nets on a fabric and the two models must be one or related by a proved map. If a translation theorem `inetOfHvm_sound` is within reach, state it; if not, say what is missing.
    
    Work from dev: `git fetch /Users/ember/dev/obend dev && git checkout -B lane-hvm2 FETCH_HEAD` in your worktree (`.lake` is warm there). Same rules as before: box safety, PID file or nothing, never stash, never an unfiltered suite. Commit named files unsigned if 1Password refuses, do not merge; report the extended theorem statement verbatim, the fragment handled and refused, the gate tails, and what you left out.

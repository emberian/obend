# Brief of lane-fabric2

Sent by the root (session 01a1ad7d, message 794, 2026-11-06T00:05:50.399Z) to agent a72ff1b9, verbatim:

    You are the distilled successor of the widths lane (your predecessor hit its context ceiling after the FABulous groundwork; its report and transcript are in your pack). lane-fabric 53ad71e is merged (dev b431f17). The three decisions:
    
    1. Theorem shape: yours. State `fabric_realizes_module` as a simulation: given a register-to-flip-flop correspondence R between the decoded configured fabric and the `RtlModule`, if one clock step preserves R and gives equal outputs for every state and input, then every trace agrees (plain induction). For each concrete bitstream, the one-step condition is a closed `BitVec` statement discharged by `bv_decide` (kernel-checked); the vector comparison stays a test, never reported as the theorem.
    
    2. Design: `iceStickMac8` (8x8+16) replaces `goldenRetimedMacRtl`. DSP tiles stay out of scope.
    
    3. Fabric and pins: generate a fabric that fits the design with real pins, from a FABulous fabric CSV committed under `hardware/fabulous/`; no serializing wrapper, since the port map must mean the module's ports. For the iCEstick MAC that is 48 pins. If FABulous supports IO tiles on more than the west edge (check its tile library for N_IO/S_IO/E_IO or a wider IO tile), use them to keep the fabric square-ish; otherwise 24 W_IO rows is acceptable. Do the MAC first. The width probe (85 bits) is the second design only if a fabric FABulous can generate in minutes holds it; otherwise say so and leave it.
    
    Model only LUT4AB tiles (the 8 LUT4 cells with FF-with-enable-and-reset, the MUX8LUT, the switch matrix from its `.list`, the config-memory table) and the IO tiles as port mapping; name BRAM, DSP, RegFile as out of scope in the module header. Everything else in the original brief stands: `Obend.Hardware.Fabulous`, the bitstream decoder over `bit_gen`'s output plus `bitStreamSpec.csv`, `obend fabric check`, `hardware/fabulous/verify_fabric.sh` with the flipped-bit refusal naming tile and bit, and FABulous's own simulation of the configured fabric agreeing with the Lean evaluation. Same rules as before (box safety, PID file or nothing, never stash, never an unfiltered suite). Work from dev: `git fetch /Users/ember/dev/obend dev && git checkout -B lane-fabric2 FETCH_HEAD` in the build worktree. Commit named files unsigned if 1Password refuses, do not merge; report the theorem statement verbatim, the script tails, the refusal text, and what you left out.

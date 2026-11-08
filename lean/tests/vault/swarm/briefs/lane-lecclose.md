# Brief of lane-lecclose

Sent by the root (session 01a1ad7d, message 809, 2026-11-06T00:18:13.758Z) to agent aee107e1, verbatim:

    lane-lecscript is merged (dev b8a9446). Rung 4 is closed as far as the file goes; the closing quest is your own left-out list, so the LEC's statement is about the module's semantics rather than a per-register restatement of it:
    
    1. The corollary: `lecScript_unsat_of_agree` stated against `stepModuleRegs` and `evalModuleOutputs` (or whatever the module-level names are on dev after the widths lane) rather than `leanNext`, under the hypotheses it needs (distinct `regIdx`, the reset wiring), and against the clock-domain edge semantics the widths lane added (`stepModuleDomain`): say precisely which clocking the LEC checks (Yosys's single global clock with per-domain resets) and prove the corollary for the single-domain case, with the multi-domain case stated as what the LEC does not check, in the module header and `hardware/README.md`.
    2. `checkWidths m = true → moduleFaithful m = true`, so emission-time refusal and the theorem's hypothesis are the same check; then `obend-emit-sv --lec` needs no second check.
    3. The documentation closeout: `QUALIFICATION-AND-SILICON-LEAN.md` §3.2 and `hardware/README.md` say exactly what rung 4 proves and trusts (Yosys frontend and `write_smt2`, z3, the two `print` functions writing SMT-LIB syntax, pinned by tests), with no sentence left from the BEL-miter era; delete any remaining `*_props.smt2` reference that nothing runs, or say why each stays.
    
    Work from dev (`git fetch /Users/ember/dev/obend dev && git checkout -B lane-lecclose FETCH_HEAD`). Same rules. Report the corollary verbatim and what you left out. After this one, your lane is done unless something in the scripts turns red; thank you, this was the honest LEC the expert asked for.

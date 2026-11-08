# The four gates run after their merges (SWARM.md section 4), written into the lane pages and DEV.
T="${OBEND_ROOT:-.}/lean/tests/vault/swarm/tools/setfields.py"
python3 "$T" lanes/lane-lecscript.md 'gate=bash hardware/sim/verify_sim.sh: [PASS] hardware/sim (root msg 807, read at 849)' gate_dev=b8a9446 gated=after
python3 "$T" lanes/lane-fabric.md state=merged commit=53ad71e dev=b431f17 ancestor=true 'gate=bash hardware/fabulous/verify_fabric.sh: [PASS] hardware/fabulous (root msg 900, read at 928)' gate_dev=6183619 gated=after
python3 "$T" lanes/lane-fabric3.md state=merged commit=0380418 dev=889a09d ancestor=true 'gate=lake build Obend.Hardware.Fabulous.Tile Obend.Hardware.Fabulous.Cli Obend.Hardware.Fabulous.Mac8 obend obend-emit-sv; bash hardware/fabulous/verify_fabric.sh: Build completed successfully (669 jobs), [PASS] tile LEC, [PASS] hardware/fabulous (root msg 972, read at 984)' gate_dev=889a09d gated=after
python3 "$T" lanes/lane-docs.md state=merged commit=200d6a7 dev=158952e ancestor=true 'gate=swarm-build lake build Obend.Census Teeth Tests on bb2: Build completed successfully (578 jobs), the docs census reports none stale (~/obend/logs/swarmvault-t2.log)' gate_dev=021a0b0 gated=after
printf -- '- [[lanes/lane-fabric]] at b431f17\n- [[lanes/lane-lecscript]] at b8a9446\n- [[lanes/lane-fabric3]] at 889a09d\n- [[lanes/lane-docs]] at 158952e\n' >> DEV.md

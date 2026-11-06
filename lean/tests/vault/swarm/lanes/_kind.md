---
law fields: not (new.branch == "") and not (new.agent == "") and not (new.brief == "") and not (new.worktree == "")
law states: new.state in ["briefed", "running", "reported", "merged"]
law commit: new.state in ["reported", "merged"] implies not (new.commit == "")
law gate: new.state in ["reported", "merged"] implies not (new.gate == "")
law landed: new.state == "merged" implies not (new.dev == "")
law pidfile: new.job == "running" implies not (new.pidfile == "")
law buildbox: linked.nobuild == 0
law reachable: linked.unreachable == 0
---
A lane: one quest of the swarm, in one worktree, answering one brief. It names its branch, its agent
(the cv id), its brief and its worktree; its state is briefed, running, reported or merged. A report
names the lane commit and the gate that passed (`gate:`, the script and what its output showed); a
merged lane names the dev commit it landed at. A detached job marked running names its PID file. A
lane may not name, as a box it builds on, a box that carries no builds or that does not answer.

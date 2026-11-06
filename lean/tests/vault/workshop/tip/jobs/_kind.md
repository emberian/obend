---
law states: new.state in ["offered", "accepted", "working", "blocked", "proposed", "landed", "declined", "refused"]
law assignee: new.state in ["accepted", "working", "blocked", "proposed", "landed"] implies not (new.assignee == "")
law budget: new.spent <= new.runs
law spent: monotone(spent)
law blocked: new.state == "blocked" implies not (new.why == "")
law proposal: new.state in ["proposed", "landed"] implies not (new.commit == "")
law onbase: new.state in ["proposed", "landed"] implies new.on == new.base
law closed: new.open == 0 implies new.state in ["proposed", "landed"]
law receipt: new.state == "landed" implies not (new.receipt == "")
---
A job: a change to `research.py` someone wants, offered as a form. It names the scope, the test
that proves it, and the base commit a proposal must be on (`base:`, set by the reviewer). Its
budget (`runs:`) is moved to it from the pool when a resident takes it; each test run spends one
(`spent:`), never more than it holds and never back. A proposal names its commit and the commit it
is on (`on:`), which must be the job's base. A blocked job names why (`why:`, an atom of the
reasons). The job closes (`open: 0`) only by its landing form, and only as a proposal.

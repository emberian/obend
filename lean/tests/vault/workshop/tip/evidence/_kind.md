---
law result: new.result in ["pass", "fail"]
law fields: not (new.artifact == "") and not (new.test == "") and not (new.by == "")
law fixed: writeOnce(result) and writeOnce(artifact) and writeOnce(test) and writeOnce(run)
---
One run of a test: which test, which run of its job's budget, the artifact it ran on (the commit,
and a digest of any uncommitted change), who ran it, and the result. Written once by `tools/ws run`;
never rewritten.

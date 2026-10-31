# Fetch six papers no open mirror would give up

Into `~/paperbin`, each as `<name>.pdf` with a `<name>.txt` sibling from `pdftotext`; the names are
fixed: `moran-sands1999-improvement-in-a-lazy-context` (POPL 1999, "Improvement in a lazy context: an
operational theory for call-by-need"), `brandt-henglein1998-coinductive-axiomatization-recursive-type-equality`
(TLCA 1997 / Fundamenta Informaticae 1998), `leijen2005-extensible-records-scoped-labels` (TFP 2005),
`ducournau1994-monotonic-multiple-inheritance-linearization` (OOPSLA 1994, "Proposal for a monotonic
multiple inheritance linearization"), `cardelli1986-polymorphic-lambda-calculus-type-type` (DEC SRC
report 10), `birgisson2014-macaroons` (NDSS 2014, the paper, not the slides). The environment
variable `ANNAS_SECRET_KEY` is set for Anna's Archive's API (figure out the request shape from their
documentation; do not print the key); Kagi is available too (key in `~/dev/allgame/.env`, request shape
in `~/dev/allgame/claude_resident/tools/web_tools.py`), frugally. Verify each file is a real PDF of the
right paper (`file`, then read the first page of the text) before keeping it; a garbled extraction
(the earlier Moran–Sands attempt extracted as font garbage) is a failure, so try OCR
(`ocrmypdf` if installed) or another source. Then fix the two stale references in
`/Users/ember/dev/obend/review/PRIOR-ART-20261030.md` that say these are not in paperbin, and commit
that one file on `dev` with `git -c commit.gpgsign=false commit -F -` and trailer
`Co-Authored-By: Claude Sonnet <noreply@anthropic.com>`, rebase before pushing. Reply with which of
the six you got, from where, and which you could not.

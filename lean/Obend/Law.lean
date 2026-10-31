module
/-
# Obend.Law — laws by occasion over Core4

The law library, ported from nanodregg's (`Lang/Std.lean`, `Lang/Claim.lean`) onto Core4 terms:
`Syntax` (the types, the `At` cursor, the combinators, the skeleton), `Std` (the generators),
`Run` (the reference step as a function, for teeth), `Claim` (the `keeps` checker), `Inherit`
(laws with parents, combined by conjunction along a C4 precedence list), `Machine` (a kernel's
verdict: the law's probe executed on the demand machine). The meaning theorems are
in `Obend.Law.Proofs.*`, built by `lake build Obend`; nothing imports them here, and
`lake build Obend.Law.Proofs.Inherit` builds every one of them.
-/
public import Obend.Law.Syntax
public import Obend.Law.Std
public import Obend.Law.Run
public import Obend.Law.Claim
public import Obend.Law.Inherit
public import Obend.Law.Machine

# Root return using the blank margin as a delimiter

This is a physical refinement of the exact source and storage construction in
[phase_swap](../phase_swap/COMPOSITION.md). Its unchanged source has SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
No permanent claim ID is introduced or changed. The affected interface is the
return from `6.continue.0` to `5.root.1`. All source operations, both existential
acceptance callers, both comparison outcomes, the three-transfer swap,
allocation, projection and class-sum ownership remain unchanged.

## Admitted entry and actual information

At an ordinary clean operation boundary the left control word is `110p`, with
`p` a terminal path in the finite emitted grammar, followed by a zero gap and
the inherited nonempty unary register fields. The physical bank, finite
reserve, head and every scratch coordinate have the exact predecessor ABI.
The active bank has twelve classes and its logical values are unbounded.

Preparation may extend the path by `1 0 0 1...1` for shared INC/DECNZ/BEEP,
or `1 0 1...1` for native HALF. Register kernels do not redispatch through this
interface until they have restored the inherited return representation.
Break and continue remove a suffix of the path; the new traversal starts
only after `6.continue.0` has skipped the erased zero suffix and found a one.
It therefore reads an unchanged prefix of an admitted path, or an admitted
prepared word. A break that changes the selected zero to one cannot introduce
a longer run of zeroes. The earlier root sentinel remains `11`.

All 279 unfolded terminal paths of this exact fixed grammar have at most
five consecutive zeroes; their largest total zero count is eleven. Appending
either preparation suffix preserves the five-zero bound. This finite syntactic
fact is certified from the whole grammar, including unexecuted paths and both
conditional outcomes. It is not inferred from a finite blank prefix. Every
prefix of such a word also avoids six consecutive zeroes.

The old return stored a bound on the total number of path zeroes in fourteen
control states. The replacement stores only the length of the current zero
run, from zero through five, in six physical states. The required delimiter
information already exists in the left blank margin and the verified path
language. No new tape field, initial symbol, address, external decoder or
counter is supplied.

## Six-state traversal and termination

On entry to `repeat.dispatch.0`, the head has just moved one cell left from
the one found by `6.continue.0`. Every row preserves the scanned bit and moves
left. On a one it enters state zero. On a zero in state `r<5` it enters
`r+1`. On a zero in state five it moves left into the inherited rightward
`4.dispatch.scan`.

The invariant is that `r` zeroes have been seen since the last scanned one.
The finite interval from entry through the root cannot contain six zeroes,
so the detector cannot turn right inside an admitted control word. The two
root ones reset the detector. The blank interval to their left supplies six
zeroes, after which the inherited scan moves right through a finite blank
interval to the first root one. It enters `5.root.1` on the second root one,
exactly as the old countdown did. Tape, head and target state agree at this
boundary; elapsed transition counts need not agree.

Every step moves toward one of these finite endpoints. Thus the region
completes in a positive finite number of physical transitions on every finite
admitted configuration. It has no event, no scratch, no data mutation and no
other exit. The register values and reserve can grow without invalidating the
proof because the scan never selects or traverses their contents.

The inherited startup uses a different temporary ABI. Its applicability is
a separate exact finite blank-initialization obligation on these new literal
bytes; the ordinary path argument above is not substituted for that obligation.
Fresh independent engines must agree on the entire clean source-entry tape,
head and state, with no previous event. Once that entry is established, the
ordinary induction applies to every subsequent finite source stage.

## Complete composition and review boundary

`build.py` replays all fixed predecessor source, allocation, grammar,
projection and coalescence inputs, including all intermediate swap ownership
obligations. It validates every old countdown row and its sole external
ingress before replacing that family. It leaves every other named transition
unchanged. Both rows of every new state are defined. Fresh ordinary all-row
quotients produce the complete parent, and `select.py` uses a separately
frozen completion plan with fresh preimages and event maps.

The semantic exclusions used by completion are the same named preparation,
selector and native HALF entry facts. Their new numerical identities must be
derived from every raw preimage. None of the six new dispatcher states has an
excluded row. The changed traversal proves the inherited entry invariants
again; it does not authorize discarding an inconvenient reachable branch.

The complete selected construction counts the writer, program control,
selection, arithmetic, clocks, certificate capacity and enumeration, reset,
both callers, cleanup, all return scans, events and totalization. Source
boundaries and the ordered source events agree with the reviewed 284 source.
Every primitive and administrative region has positive finite progress, so
the physical execution is infinite in both cases. The source theorem gives
finitely many designated events exactly when NP=coNP. Infinite events, the
established 1-acceptance convention, mean NP differs from coNP. A finite
silent interval decides neither alternative.

The source proof and unchanged component arguments retain their original
scope. The new dispatcher, maps and literal tables require fresh nonauthor
physical review at an immutable producer revision. Finite tests, conventional
proof, internal model review, remote CI and Lean checking remain separate;
this document makes no Lean/kernel or external-human certification claim.

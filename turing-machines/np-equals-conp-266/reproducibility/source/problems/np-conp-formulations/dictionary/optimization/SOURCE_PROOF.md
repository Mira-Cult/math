# Controlled source compression: header, parser, decoding and rejection

## Scope and provenance

This is new source work on the complete bounded-machine NP = coNP construction.
The input is the unchanged PR43 `source_parser_successor_ge.py`, SHA-256
`83f1e5d4758839878eb7806262c9595e92b2941b420cb097387cf672d43c9ac6`,
preserved as `sources/baseline.py`. The transformations were implemented by
model-agent `internal-model-reviewer` after recovery. This is an author argument
with tests using a separately authored reference; it is not an independent
review of this agent's own new source transformations.

No candidate indexing, input enumeration, reference language, candidate
clock, tape alphabet, state event convention, or initialization is changed.
The source/compiler interface remains mathematical naturals, finite acyclic
calls with fixed tuple return arities, and no read before assignment. The
existing source theorem and compiler correspondence remain dependencies.
No permanent claim IDs are allocated.

The selected source is
`sources/unary_local--equality_inline--fused.py`, SHA-256
`ae23de7359cefdd34c139e59418c54e26eddf9e207b9122cfb3473d0f52a380a`.
Its selected strict-half-pair table has **931 states / 1,862 complete rows**,
SHA-256 `f6247b5a8fe8b67047fedb99bb26ebf0134c616ada0e497e1d9ac837a31480bb`.
It remains a B=1 state-exit machine with blank 0, initial head 0, start 0,
binary writes and L/R moves. The unchanged source is separately measured
on each compiler before source savings are attributed.

## Dense program-header identity

For any natural e, count its trailing one bits. Let this count be k, and
let s be the value after removing those k bits. Then s is even, possibly
zero, and

    e = 2^k s + (2^k - 1),
    e + 1 = 2^k (s + 1).

Since s+1 is odd, the original loop beginning with `h=e+1, m=1` divides
exactly k times. Its final m is k+1, its final h is s+1, its program payload
is `floor((s+1)/2)=s/2`, and its radix is `4*(k+3)`.

The selected replacement starts with `h=e, m=0`, counts trailing ones and
removes them, then sets `program=h//2` and `radix=4*(m+3)`. Thus program and
radix are exactly the old values for every natural e. The temporary variable
m has a different intermediate meaning; the source uses it afterward only
to compute that radix. This includes e=0 and every all-ones value 2^k-1.
All such descriptions remain valid dense program codes. No program is
renumbered or dropped.

The loop terminates: each iteration has a positive odd h and replaces it
by floor(h/2), a strictly smaller natural. Its only possible zero final
value is allowed. All divisors remain positive.

## Shared-prefix competitors and malformed inputs

Two measured competitors use a common `prefix` procedure for the header
and both unary fields of `instance`.

- `prefix_raw` returns `(k,s)` before removing the terminating zero.
- `prefix_tail` returns `(k,s//2)`, including the zero removal.

Both versions use the identity above for `accept`. That use deliberately
does not reject a zero tail: the dense program grammar admits every natural
e. The separate `instance` caller retains the malformed-input checks.

After counting a unary prefix, s is even. Therefore `s != 0` if and only if
`s//2 != 0`. In the sentinel-coded input, a zero remaining value means the
scan has consumed all represented bits, including the high sentinel, before
finding a terminating zero followed by that sentinel. Such a prefix is
malformed. A nonzero even s is at least 2, so removing its low zero leaves
at least one represented bit and preserves the sentinel.

Consequently the raw helper may check s before dividing, while the tail
helper may check its returned divided tail. They reject exactly the same
codes at the same two prefix boundaries as the original parser. The rest
of `instance` is unchanged: it extracts exactly the declared word width,
requires a remaining sentinel, verifies that all remaining clock symbols
are one, and returns the same encoded initial tape and clock. A malformed
code still returns `(0,0,0)`. The unchanged `accept(0,0,0)` returns zero,
so malformed strings retain their original complemented-reference meaning.

The helper call graph is acyclic: main calls accept or instance, and those
procedures call prefix. Reusing the helper does not authorize conflating
its live return registers with an active caller's arguments. The physical
compiler must still pay for and preserve those frames, which is why these
mathematically sound helpers are losing experiments here.

## Simultaneous transition-digit decoding

After the existing `digit %= radix`, write d for the bounded digit. The
old source obtains:

    write = d % 2,
    direction = (d // 2) % 2,
    state = d // 4.

The replacement is two simultaneous assignments:

    write, digit = digit % 2, digit // 2
    direction, state = digit % 2, digit // 2

The first assignment produces `(d mod 2, floor(d/2))`; the second produces
`(floor(d/2) mod 2, floor(d/4))`. These are exactly the original fields.
The source's right-hand sides are evaluated before either destination is
written. This requirement is especially relevant to the first assignment,
whose quotient destination aliases the dividend. The strict half-pair
compiler loads the operand before clearing or writing either target.

Moving the `state` assignment ahead of the tape update is sound: after
selecting the transition, that tape update uses only `write`, `direction`,
`left` and `right`, and does not read `state`. The next state guard is at
the next simulation iteration. No branch bit, transition, or clock tick
is added or omitted. Halt states continue to be held while the remaining
choice bits and clock ticks are consumed.

The source-only paired form is measured on the unchanged PR44 dictionary,
the base hybrid, and the separately identified strict half-pair extension.
A saving from the new pair kernel is not attributed to the source alone.

## Direct rejection comparison

Both calls to `accept` terminate and return either zero or one. Write R for
the reference acceptance bit and A for the candidate acceptance bit. The
original controller rejects exactly when

    A != 1 - R.

For Boolean A,R this is equivalent to `A == R`. One variant retains a
`truth=accept(...)` temporary and changes the comparison. The selected
variant compares the two calls inline, with the reference call evaluated
first as in the original source.

The calls have only local state and emit no source beeps. The selected
compiler must nevertheless preserve the first returned value while the
second call reuses the same accept frame; tests explicitly exercise this
case with independent expected answers. The logical equality does not
assume that a callee's return register survives another call.

The predicate is identical at each candidate/input pair. By induction, the
controller advances through the same input indices and rejects the same
candidate at the same first counterexample. It emits exactly the same
sequence of source beeps with the same candidate indices. If a correct
candidate is reached, both controllers continue the same infinite silent
sequence of finite comparisons. This argument preserves finite versus
infinite beeping, rather than only a finite event prefix.

## Descending branch enumeration: retained regression

A separate source begins with `branch=2**clock`, loops while branch is
positive, decrements it before simulating, and removes the old `if choices`
overflow return and final branch increment. This changes the order of
branch words but retains exactly the same finite set.

For a natural clock C, the old implementation tests every branch integer
from 0 to 2^C-1. Each simulation consumes exactly C choice bits even after
entering a halt state. The first out-of-range branch has remaining choices
and is rejected by the overflow check before its result can be accepted.
The descending version instead tests 2^C-1 through 0 and then returns zero.
Both accept precisely when one of the same 2^C bitstrings reaches state 0
within the clock. For C=0, both return zero from initial state 2. Each step
and the entire finite branch loop terminate. No beep occurs inside accept,
so changed branch order and runtime preserve controller event behavior.

This variant costs 959 states on the no-forward PR44 dictionary, versus
951 for the selected source; 939 on the strict half-pair compiler, versus
931; and 937 with its additional power-of-two option. It is retained as a
complete losing experiment. The same power-of-two option on the selected
source still costs 931, with a different exact table hash, so the option
is not silently substituted for the selected compiler/table binding.

## Complete measured cost ledger

All figures count complete binary B-exit tables, including initialization,
program/control, scratch/register machinery, dispatch and silent totalization.

| Source/configuration | PR44 forward | PR44 no-forward | Base hybrid | Strict half-pair hybrid |
| --- | ---: | ---: | ---: | ---: |
| Unchanged PR43 source | 978 | 978 | 952 | 952 |
| Trailing-one header only | 971 | 971 | 947 | 947 |
| Inline equality only | 968 | 966 | 942 | 942 |
| Paired digit decode only | 970 | 970 | 951 | 946 |
| All three selected source changes | 953 | 951 | 936 | 931 |
| Raw shared-prefix helper only | 1,057 | 1,057 | 1,032 | 1,032 |
| Tail shared-prefix helper only | 1,034 | 1,033 | 1,010 | 1,010 |
| Selected changes with raw helper instead of local header | 1,038 | 1,036 | 1,020 | 1,015 |
| Selected changes with tail helper instead of local header | 1,015 | 1,012 | 998 | 993 |
| Selected changes plus descending branch enumeration | 961 | 959 | 944 | 939 |

The selected table's profile is **706 arithmetic/control + 135
engine/dispatch + 82 register operations + 5 initialization + 2 beep
machinery + 1 totalization = 931 states**, with 41 physical registers.
The raw-helper-only version has 47 registers and adds 56 arithmetic/control,
12 engine and 12 register-operation states to the 952-state hybrid baseline.
The tail-helper-only version has 46 registers and adds 38 arithmetic/control,
10 engine and 10 register-operation states. This identifies the paid
argument/return/frame overhead in these concrete helpers; it is not a lower
bound on all possible sharing architectures.

The controlled sequence is: reviewed B2 compiler 1,036; unchanged source on
exact PR44 dictionary 978; unchanged source on base hybrid 952; selected
source on that same base hybrid 936; selected source on the strict half-pair
extension 931. These respectively separate the generic compiler change,
new compiler kernels, new source transformations and extra pair kernel.
There is no event-convention saving in these figures.

## Evidence and limits

`make_variants.py` preserves the full 24-source factorial comparison of
four header implementations, three rejection comparisons and two digit
forms. `branch_variant.py` adds the separate descending source. The
`matrix.json` records exact sources, compiler options, table hashes, complete
profiles and build commands; each table is in its own machine subfolder.
The complete losing alternatives remain available.

`semantic_checks.py` tests all 25 sources against unchanged separately
written string/decoded-row/sparse-tape references. The final run checks
208,200 parser comparisons, including malformed inputs; 139,000 acceptance
comparisons; 49,536 helper/header comparisons; all four Boolean rejection
cases; and representative first-three-event source prefixes. Finite fixtures
include trailing-one boundaries, high unused program words, rejecting and
looping programs, nondeterministic choice, delayed acceptance, clock zero,
input delimiters, short data fields and invalid clock tails. The unbounded
claims rely on the arguments above, not extrapolation from those tests.

`compiled_checks.py` tests the selected source and helper competitors
through all four separately identified compiler configurations: 424
arithmetic-grammar fixture calls, including repeated helper frames and
inline equality between two calls to the same accept procedure. It compares
to the independent reference and verifies scratch cleanliness. Together
with three selected controller events it executes 2,739,103 INC/DECNZ
primitives. The controller grammar event positions are 2, 57,544 and
121,622. These are grammar positions, **not physical binary-tape times**.
The focused descending-source gate adds 96 compiled accept calls, 1,154,042
primitive steps, clock-zero and ascending/descending-order cases, and the
same first three source-controller event snapshots.

The first half-pair prototype accepted the unsupported float literal 2.0
because its guard checked only equality with integer 2. The producer fixed
that input-contract error by requiring exact `int` type. The earlier source
is preserved in `experiments/half_pairs_pre_literal_guard.py` and is not an
accepted generic compiler. All 24 integer-source cases were rebuilt with
the repaired compiler into `machines/half_pairs_strict/`; all 120 compared
source/grammar/raw-table/quotient/final-table artifacts match the earlier
integer outputs. Their new metadata binds the repaired source hash
`7a2ac08cea2ffcab398ba1aebabd1a82f404fc0e2d804bcea5bf0548fa3af052`.
This does not relabel the earlier input contract as correct.

No physical billion-transition replay or proof-assistant certification is
claimed by this source task. Full physical initialization, exact table
acceptance, and independent mathematical/implementation review belong to
the coordinator's separately frozen delivery. The 931-state result is a
measured complete implementation candidate with author proof and bounded
checks; it supplies no justified estimate of reaching 250 states.

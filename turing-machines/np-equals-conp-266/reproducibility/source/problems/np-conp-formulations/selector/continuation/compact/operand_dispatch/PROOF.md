# Operation mode retained in control

This construction has **271 marked states and 272 B-exit states**. It changes
the complete operand-selection interface while retaining the exact source,
control grammar, physical bank and three-transfer orientation swap of
[phase_swap](../phase_swap/COMPOSITION.md). The six-zero return delimiter is
reapplied to this runtime from [repeated_control](../repeated_control/PROOF.md).
It is a new producer. Predecessor review acceptance is not transferred to
these changed literal tables.

## Exact source and retained theorem boundary

The canonical source is [phase_swap/source.py](../phase_swap/source.py), with
SHA-256 `4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
It is byte-identical to the reviewed 291 source and the published 284 source.
No source expression, enumeration, acceptance call, record lookup, arithmetic
lowering or comparison branch is changed. The fixed `swap290` source/control
and coalescence plans are replayed, including the region lowerer that exchanges
the simulated left and right halves by three transfers through a proved-zero
work cell. All intermediate ownership obligations remain in the regenerated
whole-program class-sum invariant.

The reference and candidate predicates remain respectively
`A(D(i),0,N(i))` and `A(j,i,(N(i)+1)^j)`, each existential over the protected
negative certificate tape. The source theorem retains normalized low-first
marker/payload parsing, independent write and relative-turn bits, address
`s+z-1` for overlapping records, virtual zero tails, immutable description
masters, absent and truncated records, absorbing acceptance, and real high
candidate input bits after an empty parsed prefix. Neither numerical clock
construction nor the full certificate capacity is removed. Both `(1,1)` and
`(0,0)` returned-bit pairs refute a candidate complement; unequal results
continue silently. These are unchanged source-level facts with the exact
scope of the predecessor proofs, not consequences of finite execution.

The changed obligation here is physical refinement of every retained primitive
occurrence, including both actual acceptance callers, event preparation,
all returns and startup. The conventional endpoint follows only after that
obligation, complete storage/control certificates and fresh completion/event
maps have been supplied.

## Admitted clean and prepared configurations

At a clean primitive occurrence the finite left control word has the inherited
`110` root and its emitted path. Let `h` be the selected terminal cell. That
cell reads zero. A finite zero gap separates it from the bank anchor `P`.
The bank has the inherited form

`1 0 1^(x_0+1) 0 1^(x_1+1) 0 ...`,

with twelve active physical classes in the emitted register order, followed
by the finite zero-valued reserve. Every block is nonempty; values are
unbounded natural numbers. Coordinates outside the finite represented region
are blank. All source and arithmetic ghost values obey the generated class-sum
ownership invariant, including zero peers at each operated class.

The operation entry's read-zero row writes one at `h`, moves right, and enters
`1b.reg.prep_1`. The asserted read at `h+1` is zero. Preparation preserves that
separator and fills the finite gap from `h+2` through the original bank anchor
with ones. The unchanged return machinery redispatches the same path. The
prepared terminal then reads one; its row clears `h`, moves right and enters
the fully paid operand chain for its operation and position. No operation
mode bit remains on tape. The physical state carries the operation kind.

This is the original one-zero preparation ABI for INC, DECNZ and BEEP. Native
HALF already uses that ABI, through its own preparation entry. The local
change removes the shared selector's second separator, temporary selected
block marker, leftward mode recovery, rightward recovery, and bootstrap aliases.
The original entry states and all source callers remain explicit and paid.
The builder validates the entire inherited runtime before retaining this
representation; it does not merely patch rows observed in a blank prefix.

## Address chains, operation result and finite progress

For operation kind `o` and bank index `i`, `2b.reg.i.o` preserves each scanned
one and moves right in the same state. On zero it preserves the zero, moves
right and enters `2b.reg.(i-1).o`. Thus the remaining field distance and mode
are both in finite control. Starting at the one-zero header, the inherited
negative-index suffix passes the preparation run and enters the selected
kernel at exactly its old ABI. Each loop crosses a finite nonempty unary
block, and each zero decreases the remaining distance. Selection completes
in positive finite time on every admitted finite bank, independently of the
values in other fields. No address is supplied on an uncounted initial tape.

The existing INC and DECNZ kernels are retained row for row. INC maps `x` to
`x+1` and takes success return `6.break.0`. DECNZ on positive `x` maps it to
`x-1`, takes `6.break.0`, and preserves the exact inherited reserve extension;
on zero it retains zero and takes failure return `6.break.1`. The complete
kernel restores the selected terminal and prepared gap convention before
returning with head `h-1`. All other physical values agree, including dirty
unrelated fields. These unchanged unary-kernel contracts are the ones used by
the [retained framework](../../../vendor/pr44/shared/vendor/TMBuilder.py); selection presents
their original entry configuration.

More explicitly, INC scans to the selected block's terminating zero, writes
one there, and shifts the finite suffix right by one cell. Every later
block keeps its length. DECNZ first erases the selected block's first one.
If its next cell is zero, the block encoded zero; the kernel restores that
one and returns failure. Otherwise it locates the finite bank's trailing
double zero, then sweeps left, shifting the suffix one cell left until it
reaches the erased selected-cell boundary. The selected block has lost one
unit, every later value is preserved, and the exact representation gains
one trailing zero-valued block. Neither directional sweep can cycle: the
head moves monotonically to a finite delimiter. The return scan finds the
header's two adjacent zeroes at `h,h+1`; every intervening bank block and
preparation run is nonempty. It returns at `h-1` without changing data.

For HALF the selected entry still scans the first one of `1^(x+1)`.
The unchanged kernel returns `floor(x/2)`, success exactly when the old `x`
was odd, and its exact finite zero-reserve extension. All four native operand
entries, preparation, selection, boundary handling and both returns are paid.
They use the original one-zero header and need no shared-mode adapters.
The [HALF proof](../compiler/native/PROOF.md) removes two finite input units
per cycle; the inherited boundary
and temporary-quotient invariants prove its positive finite termination.

BEEP follows the same ordinary preparation. On its prepared entry it clears
the terminal and moves left into B. Both inherited success-return behaviors
are retained: B/read0 writes one, moves right and enters `2e.reg.cleanup_1`;
B/read1 clears the bit, moves left and enters `6.break.0`. The actual sole
BEEP path is `1100`, so its B entry reads zero and takes the cleanup branch.
These are the corresponding two rows of the inherited success return, with
one distinguished B exit. The ingress conversion marks only the transition
entering B, exactly one step before the companion B-exit convention. Neither
preparation nor return emits an extra event. The fresh maps give the sole
selected marked row `104 1 0 L 1 1`.

## Root delimiter and bootstrap

The new selector reduces the ordinary prepared suffix from `100` to `10`.
The six-state delimiter generator freshly examines all 279 unfolded paths
of this exact grammar. It checks the stronger suffix `100`, so it also
covers `10`, all untouched native HALF paths, and the shortened prefixes
returned by break/continue. The maximum total path-zero count is eleven,
the maximum path length is 55, and the maximum consecutive prepared zero
run is five. The restored old runtime's countdown has thirteen states;
all are removed and replaced by the paid six-state run detector.

Each detector row preserves its bit and moves left. A one resets the zero-run
count; the sixth consecutive zero turns into the existing rightward scan.
No admitted finite control prefix contains six zeroes. The root's `11` resets
the detector, and the blank margin to its left supplies the six-zero delimiter.
The rightward scan therefore reaches exactly the same `5.root.1` boundary,
with the same complete tape and head. Both directed traversals are finite.
This is the same argument as the [delimiter proof](../repeated_control/PROOF.md),
with its path-language premise freshly recalculated for this interface.

Startup has its separate temporary ABI. The operation-specific index-zero
chains were already retained for that ABI in the shared design. Here the
original boot transitions call those original entries directly and use the
original one-zero preparation. No renamed shared-selector aliases remain.
The complete writer, source-program construction, finite reserve construction,
and all initialization loops are counted in the table.

The finite initialization lemma is established separately by literal execution
on the new bytes. Two independently written exact engines reach raw state 269
at step 89,821,408 with head -3818, no event, and exactly the one-cell set
`{-3821,-3820} union {3,5,...,3821}`. This is the clean source entry with 1909
initialized zero fields. This author receipt is a finite feasibility check;
the independent immutable physical review must bind its own execution. The
ordinary source-boundary induction starts at this exact configuration.

## Fresh excluded rows and every raw preimage

The retained runtime has five named partial-domain reads, freshly collected
before totalization. Their exclusions follow from the all-natural contracts:

| Named row | Excluded read | Reason at every admitted ingress |
| --- | ---: | --- |
| `1b.reg.prep_1` | 1 | The first header cell is the clean zero separator. |
| `2h.native_half.prep` | 1 | Native preparation sees that same clean separator. |
| `2h.native_half.begin` | 0 | The selected unary block has at least one one. |
| `2h.native_half.boundary` | 1 | The kernel has reached its zero field separator. |
| `2h.native_half.undo` | 0 | The temporary quotient one being restored exists. |

The ordinary domain proof plus the separate exact initialization lemma exclude
all five reads from the actual infinite blank run. The silent totalization
sink consequently has no admitted predecessor. Its two rows may also be
completed. The six new dispatcher states have both reads admitted and total;
no dispatcher branch is excluded to manufacture a merge.

Fresh canonicalization and quotienting yield the following complete fibers.
Numbers refer only to this new ordinary parent; the files bind them by hash.

| Parent B row | Every raw preimage | Named justification |
| --- | --- | --- |
| `(9,1)` | `(9,1)`, `(65,1)` | ordinary and native preparation |
| `(51,0)` | `(52,0)` | native HALF begin |
| `(52,1)` | `(53,1)` | native HALF boundary |
| `(70,0)` | `(72,0)` | native HALF undo |
| `(274,0)`, `(274,1)` | `(276,0)`, `(276,1)` | unreachable silent sink |

There are six quotient holes and seven raw-preimage row occurrences. Every
fiber is checked, rather than reusing a numerical hole from the shared-selector
parent. domain.json (historical reference: `machines/control_mode_selected/domain.json`; outside this selected-only export) binds the
source, full parent table, named inventory and quotient. The fixed completion
plan changes only these proved-excluded rows. All other rows are byte-for-byte
unchanged before quotienting; the distinguished B class remains separate.
The resulting ordinary quotient and ingress-event quotient are checked over
both reads of every state. All final tables have two binary rows per state,
valid targets and only L/R moves.

## Whole-program composition and cost

The complete source graph, allocation, control contraction, projection,
coalescence and class-sum invariants are regenerated. Their structural values
are unchanged: twelve physical classes, 184 retained register operations, 81
explicit zero-peer sites, and the same simultaneous-operand and intermediate
three-transfer obligations. `whole-action.json` is explicitly empty because
this construction enables no new fused action primitive. The source still
uses both actual record-selection callers and retains their complete adapters.

The selector change removes 31 raw named shared-selector states: 14 indexed
shared scans, 13 marker/mode/recovery states, one extra preparation state and
three bootstrap adapters. It restores 22 raw states for the two chains at
positions 1 through 11; position 0's two chains already served bootstrap. Net
raw savings are nine. Ordinary quotienting reduces the old 283 B parent to 275.
Fresh admitted completion saves three states here instead of six in the shared
parent; final marked counts are therefore 276 to 271, a net saving of five.
No isolated-routine count is substituted for these whole-table measurements.

Every retained arithmetic and administrative segment makes positive finite
physical progress and preserves its source boundary relation. All finite
source comparisons terminate, the outer enumeration remains fair, and the
physical machine runs forever in both cases. Its source event order is exact,
although physical transition counts differ. The unchanged source theorem then
gives finitely many designated events if and only if NP=coNP; infinite events,
including established 1-acceptance, mean NP differs from coNP. Continued silence
cannot arise from an administrative cycle under these admitted invariants.

## Evidence scope

Author fixtures cover all 24 INC/DECNZ entries, all four native HALF entries,
values 0 through 128 at varied finite gaps with dirty unrelated fields, both
returns, exact reserve growth, and ordinary/native preparation. There are 1,126
primitive/preparation cases. A separate 513 injected cases enter every one of
the 279 unfolded grammar occurrences through the actual root control rows,
including all branch outcomes, both caller regions, break, continue and BEEP.
Each step is checked through the parent/completion/companion/event maps, and
whole exit tapes are compared with independently computed arithmetic values.
These prepared fixtures are distinct from literal blank-start execution.

The author two-engine blank receipt establishes the new finite source entry
and three event positions with whole-configuration agreement. It does not
establish rejection coverage, infinite behavior or eventual silence by testing.
Fresh nonauthor source/physical reviews, deliberate mutations, extended silent
progress and immutable producer bindings are recorded separately. Conventional
proof, finite tests, internal model review, remote CI, external certification
and Lean/kernel checking retain distinct scopes. No external or Lean
certification is asserted by this document.

# Direct marker and payload phases

This is an additional source-equivalent parser transformation on top of
[the ordinal/direct-branch construction](../PROOF.md). `source.py` retains
exactly the acceptance function proved there. Its complete fixed parent has
366 marked states, 367 B-exit states and 370 raw states. The marked SHA-256 is
`d92cb03aa83fdc90431deffbf2f17cc14af4707cd846c2c080b453a3e59fdc83`.
No excluded-row completion is assumed in this count.

## Exact source relation

At parser entry, `scan=i`, `n=0` and `e=1`. The frozen normalized parser
extracts the low marker, divides scan by two, exits on marker zero, otherwise
extracts the low payload, divides scan again, sets `e=2*e+payload`, increments
n, and repeats. Its final `scan` is the suffix after consuming the first zero
marker. The unchanged master i is subsequently supplied to the candidate.

The new source has a `while scan%2` marker loop. Its first successful-body
statement divides scan by two, consuming the marker. It then doubles e,
increments e iff the payload parity is one, divides scan by two, and increments
n. A final division immediately after the loop consumes the zero marker that
made the loop fail. Thus at every next marker boundary the pair `(n,e)` and
scan equal those of the frozen parser. On exit all four `(n,e,scan,i)` values
agree. This is a straightforward induction on the number of marker-one pairs.

Every even i has an empty prefix. The final scan may contain arbitrary ignored
higher bits, but the untouched i still reaches candidate acceptance. If the
highest marker is one and there is no represented payload bit, scan becomes
zero after consuming that marker, so its virtual payload is zero; the new
source doubles e without incrementing it. The next marker is the virtual zero
and ends the loop. All finite integers, including zero and all-one bit strings,
are therefore interpreted identically.

For each successful marker iteration, scan is divided by four. Hence there
are at most `ceil(bit_length(i)/2)` such iterations. The terminal scan division
also terminates. There is no fixed prefix bound or finite-width assumption.
The description reversal convention, sentinel one, clock `(n+1)^j`, empty-prefix
clock one including j=0, candidate description/exponent coupling, and both equal
comparison branches remain unchanged. The existing normalized source endpoint
proof applies after this exact parser-value adapter and the acceptance-value
adapter in the parent proof. No different NP reference language is introduced.

## Guarded native marker-loop lowering

`build_parser.py` recognizes a loop with test `x%2`, first body statement
`x//=2`, no else, and an immediate following `x//=2`. Both divisors must be the
literal integer two and all three uses must name the same variable. The rest
of the loop body may not contain a call, return, break or continue. In
particular no branch may bypass the source's leading or terminal division.

The lowered grammar applies native HALF on x at the marker boundary. On odd
success, this has consumed exactly the source's marker and leading division;
the remainder of the body is executed, then control returns to the marker
boundary. On even failure, this consumes exactly the source's failed marker
and following terminal division, and exits. The compiler omits that following
source division because the failed HALF already performed it. No division is
lost or applied twice. The body is recursively lowered, so its independent
payload parity branch uses the parent's proved direct-branch rule.

The successful case and failed case match the source at their respective
boundaries for every natural x. The division timing changes no other value.
The source-CFG allocator already sees x overwritten before the successful
body, and sees its terminal division before the next source statement. This
lowering therefore adds no new lifetime or early result installation. Fresh
allocation, projection, native-aware control analysis and every-operation
zero-peer coalescence certificates are regenerated, rather than reusing the
374 or 387 groups.

## Physical refinement and progress

Every emitted leaf is an inherited paid native HALF, INC/DECNZ, event or
lexical control operation. The bank ABI and binary runtime rows are unchanged;
the finite register order and program grammar are newly generated. Each HALF
realization has positive finite physical duration and preserves every other
live register, with the proved reserve growth. The finite parser iteration
argument above rules out a false quiet administrative cycle.

Both acceptance calls, the complete normalized outer controller, certificate
attempts, clocks, resets, initialization, scratch, selectors, return paths,
events and both binary rows of every final state are included. The exact
raw/B quotient and ingress/event maps are emitted and checked. No numerical
event state or completion hole is inherited from another table. Ingress marks
precede B exits by one transition under the fresh map.

The infinite physical run therefore emits finitely many designated events
iff the normalized source does, iff NP=coNP. Infinite events correspond to the
established 1-acceptance condition NP!=coNP. This proof does not turn any finite
trace into a decision of eventual silence.

## Evidence and Lean interface

`check_parser.py` extracts the actual normalization statements from both
source ASTs, compares them with a separate low-first string parser on every
integer below 65536 and additional large/degenerate fixtures, and compares
compiled native grammar/class sums on prepared parser inputs. Such fixtures
are finite evidence, not blank-start evidence or a substitute for the general
boundary argument. Nonauthor source review, binary review, literal blank runs,
Git binding and CI are separate publication records.

For Lean, the new source adapter is the equality of `(n,e,scan,i)` at parser
exit. Its invariant is equality after each complete marker/payload pair, and
its termination measure is the remaining finite bit length. The new physical
segment contract is the two-outcome marker-loop rule above composed with the
inherited native HALF segment and all freshly bound compiler certificates.
The shared existential endpoint theorem does not identify this literal table.

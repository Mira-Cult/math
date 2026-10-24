# A 17-state beeping machine for the full Collatz conjecture

This note gives a two-symbol Turing machine that starts on a blank tape and
beeps infinitely often if and only if every positive integer reaches 1 under
the ordinary Collatz map. The machine has exactly 17 states, including its
designated beep state, and no halting transition.

The construction tests starting values 1, 2, 3, … in order. It advances to the
next input only after the current trajectory reaches 1. An input that never
reaches 1 therefore leaves it running silently forever, whether the trajectory
enters a nontrivial cycle or is nonperiodic. That is the distinction from a
machine that searches only for nontrivial cycles.

The result below is a correctness reduction, not a proof of the Collatz
conjecture. It has an ordinary mathematical proof and finite regression checks;
it is not Lean- or Rocq-certified. No minimality, priority, or record claim is
made. The public files here suffice to read the proof and reproduce the checks.

## Statement and machine model

Let the ordinary positive Collatz map be

$$
U(v)=
\begin{cases}
v/2 & \text{if }v\text{ is even},\\
3v+1 & \text{if }v\text{ is odd}.
\end{cases}
$$

The tape is indexed by the integers and initially contains only 0s. The head
starts at cell 0 in state A. Every transition writes 0 or 1, moves one cell
left or right, and enters one of the 17 states A through Q.

A **beep** means an exit from state O, on either read symbol. It is an event
attached to an ordinary transition, not an additional instruction or an
uncounted state. There is no halt state or halt transition.

**Theorem.** For the literal machine below, the blank-tape run beeps infinitely
often if and only if every positive integer reaches 1 under iteration of U.
If this assertion about U is false and b is its least positive counterexample,
the machine emits exactly

$$
\sum_{n=1}^{b-1}n=\frac{b(b-1)}{2}
$$

beeps, and then runs silently forever.

This is an equivalence about an infinite run. A long silent interval is not a
finite certificate of a counterexample.

## The complete transition table

An entry `1RL` means: write 1, move right, enter state L. The rows below contain
all 34 transitions; none is implicit.

| State | Read 0 | Read 1 | Function |
| --- | --- | --- | --- |
| A | `1RL` | `0RB` | Dispatch on whether the value is 1 |
| B | `1LC` | `1RB` | Find and fill the value hole |
| C | `0LK` | `0LD` | Move the hole left or detect the even meeting |
| D | `1RE` | `1LD` | Return to the halving marker |
| E | `0RF` | `0RB` | Move the marker right or detect the odd meeting |
| F | `0LG` | `0LG` | Place the odd-step hole |
| G | `1LH` | `1LG` | Return to the odd-step marker |
| H | `0RA` | `0RI` | Move that marker left or finish the odd step |
| I | `1RJ` | `1RI` | Find and fill the odd-step hole |
| J | `1RF` | `1RF` | Advance the odd-step hole |
| K | `0RA` | `1LK` | Return to the active-field beginning |
| L | `0LM` | `0LM` | Place the reset or copy hole |
| M | `0LN` | `1LM` | Return over the active field to the separator |
| N | `1RO` | `1LN` | Increment the counter or restore a copy marker |
| **O** | **`0RA`** | **`0RP`** | **Beep; finish the reset or copy another cell** |
| P | `0RQ` | `1RP` | Cross the counter and separator |
| Q | `1RL` | `1RQ` | Find and advance the active-field hole |

The [literal machine file](collatz_beeping17.tm) uses underscore-separated
rows in alphabetical state order, with the read-0 transition before the read-1
transition in each row:

```text
1RL0RB_1LC1RB_0LK0LD_1RE1LD_0RF0RB_0LG0LG_1LH1LG_0RA0RI_1RJ1RI_1RF1RF_0RA1LK_0LM0LM_0LN1LM_1RO1LN_0RA0RP_0RQ1RP_1RL1RQ
```

The string specifies the transitions; the designated beep state O and the
blank-tape starting convention above are also part of the specification.

## The representation and the three macro rules

The right-hand field represents a number by the position of a missing 1,
called its **hole**. A separate left-hand unary counter remembers which
starting input is being tested. Keeping these separate allows the trajectory
value to grow past its starting input without losing that input.

For integers $n\geq1$ and $1\leq v\leq K$, define $C(n,v,K)$ by:

- The machine is in A with its head at cell 0.
- Cells $-n,\ldots,-2$ contain 1. This counter has $n-1$ cells and is empty
  when $n=1$.
- Cell $-1$ is a 0 separator.
- Cells $0,\ldots,K-1$ contain 1 except for a 0 hole at $v-1$.
- Every other cell contains 0.

Here n is the starting input, v its current trajectory value, and K the
retained workspace capacity. K is not a ceiling on the trajectory: the
machine extends the field when necessary. If $v=K$, the hole is the first
blank after the right-hand block of 1s. In particular, the completely blank
initial configuration is exactly $C(1,1,1)$.

For example, $C(4,3,6)$ has counter 1s at cells $-4,-3,-2$, the separator
at $-1$, and right-hand field `110111` in cells 0 through 5. Its head is at
the first cell of that field, in A.

Use the shortcut Collatz map

$$
T(v)=
\begin{cases}
v/2 & \text{if }v\text{ is even},\\
(3v+1)/2 & \text{if }v\text{ is odd}.
\end{cases}
$$

We will prove the following complete-configuration rules. An arrow is the
first return to A after a positive finite number of literal transitions.

| Input configuration | Configuration on return to A | Beeps |
| --- | --- | ---: |
| $C(n,2k,K)$, $k\geq1$ | $C(n,k,K)$ | 0 |
| $C(n,2k+1,K)$, $k\geq1$ | $C(n,3k+2,\max(K,3k+2))$ | 0 |
| $C(n,1,K)$ | $C(n+1,n+1,\max(K,n+1))$ | n |

In particular these rules assert equality of the whole tape, not just a
decoded output number. The head returns to cell 0, and the separator and
counter are preserved by the arithmetic rules.

## Proof of the even rule

Suppose $v=2k$. A reads 1, erases cell 0 to make a second hole, the **marker**,
and enters B at cell 1. The marker moves right while the value hole moves
left. Their meeting determines parity without a separate parity computation.

At the start of shuttle $i$, for $0\leq i\leq k-1$, the marker is at i, the
value hole is at $2k-1-i$, and B is just to the marker's right. All the cells
between marker and hole are 1.

If $i<k-1$, B scans right to the value hole, fills it, and moves left into C.
C sees 1 and erases that cell, moving the value hole left by one. D scans
left to the marker, fills it, and moves right into E. E sees 1 and erases
that cell, moving the marker right by one. It enters B just to the new
marker's right. This establishes the invariant for shuttle $i+1$.

At $i=k-1$, the marker at $k-1$ and the hole at k are adjacent. B fills the
hole and C reads the marker's 0. C leaves it in place and enters K one cell
to its left. K scans left to the separator at $-1$ and returns to A at 0.
The only remaining hole is at $k-1$, representing k. All changes were within
the old field. There was no visit to O and no earlier return to A. Every
scan crossed a finite interval, so this proves the even macro, including
termination and the entire resulting tape.

## Proof of the odd rule

Suppose $v=2k+1>1$. The initial marker-and-hole shuttle is the same, with
marker i and hole $2k-i$ at the start of shuttle i. On the kth shuttle,
B and C move the hole to k, D fills the marker at $k-1$, and E reads the
hole's 0 at k. This is the odd meeting.

E enters F at $k+1$. F puts a hole there and enters G at k; G fills the old
hole and H puts the marker at $k-1$. The machine is now in I, just right
of the marker. The marker is at $k-1$ and the value hole at $k+1$.

Each I/J/F/G/H round moves the value hole two cells right and the marker
one cell left:

1. I scans right to the value hole and fills it.
2. J fills the next cell and F puts the new hole one cell beyond that.
3. G scans left to the marker and fills it.
4. H erases the next cell to the left to form the new marker, unless that
   cell is the separator at $-1$. In that final case H leaves the separator
   0 and returns to A at cell 0.

There are exactly k such rounds. The final value hole is at
$k+1+2k=3k+1$, representing $3k+2=T(v)$. At each nonfinal round the cell
H reads is 1; at the final round it reads the separator. Thus there is no
earlier return to A.

J and F have the same action on either read symbol. Crossing the old right
edge therefore does not abandon the trajectory. Newly crossed cells become
1 except for the final hole. Cells farther right are unchanged, so the
new capacity is exactly $\max(K,3k+2)$. The marker never crosses the
separator into the counter. All scans are between the stated finite marker
positions, and none visits O. This proves the odd macro.

## Proof of the reset and copy rule

Suppose $v=1$. A fills the hole at 0 and enters L at 1. L places a new hole
at 1. M scans left over the active field to the separator at $-1$, then
enters N at $-2$. N scans left over the old counter to its first outer
blank, at $-n-1$. It writes 1 there and enters O at $-n$.

This has increased the left counter's length from $n-1$ to n without
destroying an old counter cell. The active hole is at 1, and O is at the
leftmost old counter cell, or at the separator when $n=1$.

For each of the $n-1$ old counter cells j, from $-n$ through $-2$:

1. O reads 1, beeps, erases that cell to make a temporary copy marker,
   and enters P to its right.
2. P scans right across the remaining counter to the separator, leaves it
   0, and enters Q at cell 0.
3. Q scans to and fills the active hole. L puts a new hole one cell farther
   right, advancing the represented value by one.
4. M returns to the separator and enters N. N scans left to the temporary
   copy marker, restores its 1, and enters O at $j+1$.

After these $n-1$ finite trips, O reaches the separator at $-1$. It reads
0, beeps once more, and returns to A at 0. The new counter has n cells,
and the active hole is at $1+(n-1)=n$, representing $n+1$. Cells beyond
the advancing hole were never cleared, so the new capacity is
$\max(K,n+1)$.

There are exactly n exits from O and no earlier return to A. For $n=1$
there are no copy trips; the first O visit is already at the separator.
Consequently the same routine initializes the blank tape, with no extra
boot states. In six transitions it takes $C(1,1,1)$ to $C(2,2,2)$ and
beeps once.

### The reusable increment and copy idea

States L through Q form a six-state routine, with O already included as the
beep state. The existing dispatch transition A on 0 prepares its entry:
it fills the right hole at cell 0 and enters L at cell 1. With the left
counter still of length $n-1$, L through Q then extend that counter to
length n and place the right hole at n. The routine copies the updated
counter's size into the position encoding, using a temporary erased
counter cell to remember progress.

The extra 1s to the right need not be erased. They are retained capacity,
not part of the logical value. This separation avoids both an overflow
cutoff and a workspace-clearing phase. Together with the 11-state
unbounded arithmetic core A through K, the routine gives $11+6=17$ states.

## Exact lengths of the macros

Counting literal transitions in the proofs also gives:

| Macro | Number of transitions |
| --- | ---: |
| Even value $v=2k$ | $2k(k+1)$ |
| Odd value $v=2k+1>1$ | $5k^2+9k+4$ |
| Reset from $C(n,1,K)$ | $2n(n+2)$ |

These counts are independent of the retained capacity K. To see the counts
directly, let d be the distance between the marker and the hole at the
start of a halving shuttle. A shuttle through B, C, D and E takes
$d+1+(d-1)+1=2d+1$ transitions.

- In the even case the nonfinal distances are $2k-1,2k-3,\ldots,3$.
  Add the initial A transition and $k+2$ transitions for the final meeting
  and return home. The total is $2k(k+1)$; for $k=1$ the nonfinal sum is
  empty.
- In the odd case the k initial shuttle distances are $2k,2k-2,\ldots,2$.
  Add the initial A transition, three transitions to establish the odd
  marker, and k expansion rounds of lengths $9+6r$ for
  $r=0,\ldots,k-1$. In round r the marker-to-hole distance is $2+3r$,
  and I/J/F/G/H costs twice that distance plus five transitions.
  The total is $5k^2+9k+4$.
- In the reset case, reaching the first O takes $n+4$ transitions. Each
  of the $n-1$ copy trips takes $2n+5$: in trip r the temporary marker
  is at $j=-n+r$ and the active hole at $h=1+r$, so the O/P/Q/L/M/N
  loop costs $2h-2j+3=2n+5$. The final O exit takes one.
  Thus $(n+4)+(n-1)(2n+5)+1=2n(n+2)$.

The finite positive lengths also make explicit that an infinite trajectory
cannot get stuck inside a single unfinished macro.

## Proof of the global theorem

The blank tape is $C(1,1,1)$. By the three macro rules, a round for input n
iterates T from n until it reaches 1, making no beeps during the arithmetic
steps. At 1 the reset routine emits n beeps and starts the next round at
$C(n+1,n+1,K')$. Every individual macro has positive finite duration.

If every positive T-trajectory reaches 1, all rounds finish. There are
infinitely many completed rounds, each emitting at least one beep, so the
blank-tape run beeps infinitely often.

Conversely, if some positive T-trajectory fails to reach 1, let b be the
least such input. Every earlier round finishes, producing exactly
$1+2+\cdots+(b-1)=b(b-1)/2$ beeps in total. The bth round never enters
the reset routine. It consists of endlessly many finite arithmetic macros,
so the machine keeps running but never visits O again. This argument
covers both nontrivial cycles and nonperiodic trajectories, without
requiring a finite test for either kind of failure.

Finally, T and U have the same reaches-1 predicate on positive integers.
An even T-step is an ordinary U-step. An odd T-step compresses an odd
U-step to $3v+1$ and its forced even successor. The skipped value $3v+1$
is at least 4 and cannot be 1, so this compression neither loses nor
introduces a first visit to 1. Therefore the conclusions just proved for
T are exactly the theorem stated for ordinary Collatz iteration U.

## Reproduce the finite checks

With Python 3.9 or newer and a C++17 compiler, run from this directory:

```sh
python3 machine.py
python3 -O machine.py
python3 machine.py --emit
g++ -O3 -std=c++17 validate.cpp -o /tmp/collatz-beeping17-validate
/tmp/collatz-beeping17-validate
python3 independent_check.py
```

The [Python checker](machine.py) constructs the named transition table,
compares its compact serialization to a pinned literal, checks the state
and beep conventions, and tests 2,079 canonical macro configurations. Its
checks remain enabled under Python's `-O` option.

The [C++ checker](validate.cpp) separately parses the literal table and
checks 20,736 macro cases, including 256 deterministically seeded random
cases. It also runs 200 million literal transitions from blank tape and
compares every completed macro with a separate arithmetic model. These
checks compare whole finite tape arrays or supports, the head, return state,
and beep count. Exceeding the configured tape bounds or macro timeout is
a failure, not a successful or silently truncated test.

The development snapshot recorded the following results, which were
reproduced when preparing this public release:

```text
PASS: 2079 macro cases; 17 states; beep state O
Macro cases: 20736; transitions: 175723118; all passed
Blank trace steps: 200000000; checked macros: 712; completed inputs: 46; beeps: 1081; current input: 47; last checkpoint value: 3644; last checkpoint time: 198095814
```

The Python PASS line is the output in both normal and optimized mode.
The 1,081 beeps equal $1+\cdots+46=46\cdot47/2$. At 200 million
transitions the run is partway through input 47; 3,644 is its last completed
macro's value, not a claim about the in-progress tape at the stopping instant.

The additional [independent literal-table checker](independent_check.py),
written for this release, imports neither of the development checkers. It
checks 1,807 cases comprising 47,399,744 transitions, including whole tapes,
first returns to A at head 0, exact beep counts, the macro-length formulas,
and exact visited-cell intervals. These intervals are $[-1,v-1]$ for even
values, $[-1,T(v)-1]$ for odd values greater than 1, and $[-n-1,n]$ for resets.
The test set includes large retained tails and deterministic random cases,
with counter inputs up to 1,024, trajectory values up to 1,001, and capacity
up to 10,000. It reports `PASS` and the SHA-256 of the tested literal file.

All of these are bounded checks, not a proof of the infinite-run theorem
or an exhaustive check of arbitrary retained capacity. The all-input
justification is the invariant argument above.

## Provenance and attribution

The construction and validation programs come from
[`Mira-Cult/turing-machines` commit `116c88e`](https://github.com/Mira-Cult/turing-machines/commit/116c88e23fb6580113b1f86f22816bdce316ba1f),
directory `experiments/collatz-beeping17/`. That development repository is
private, so the link is a provenance reference, not a prerequisite for
reading or verifying this public release. [SOURCE.json](SOURCE.json) records
the full commit identifier, source paths, and file hashes. The table and
C++ checker are byte-identical to that snapshot. The Python checker differs
only in its documentation link to this README. This article reorganizes and
expands the snapshot's ordinary proof, including the macro-length calculation.

The arithmetic geometry is adapted from Charlie Reams's 14-state
weak-Collatz machine in
[`calr3/tinycryptids`](https://github.com/calr3/tinycryptids/tree/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz),
at commit `ad9c597ad728f301400325b8e2115a4bb62a25d3`. Its
[README](https://github.com/calr3/tinycryptids/blob/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz/README.md)
and [generator](https://github.com/calr3/tinycryptids/blob/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz/build.py)
explain how that 14-state design was obtained from the earlier 16-state
cycle detector released [alongside the 12-state evaluator](../README.md).

The bounded weak-Collatz machine abandons a trial when the trajectory exceeds
its starting value, and halts on the appropriate equality. The present
construction removes that cutoff and equality test, preserves the starting
input separately, and advances it only after reaching 1. The state accounting
relative to the 14-state design is $14-3+6=17$: remove its final hole scan,
equality peek, and overflow-fill state; retain the 11-state arithmetic core
with the necessary transition changes; add the six-state increment/copy
routine. This accounting is explanatory, not a minimality proof.

Neither the upstream formal proof nor this repository's Lean proofs for the
other two machines certify the modified 17-state table. No external source
files are vendored for the arithmetic core. See the repository's
[attribution and unchanged license status](../ATTRIBUTION.md).

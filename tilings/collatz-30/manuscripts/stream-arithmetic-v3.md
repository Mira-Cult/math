# Infinite carry rows with standard arithmetic forced by acceptance

## Scope and changed contract

This is an ordinary arithmetic proof for the **unchanged 26 digit types** of
`arithmetic_v2.ReverseTransducer(odd_inputs=True, merge_odd_reset=True)`, now read
on right-infinite rows. It is authored by task agent `/root/arithmetic`.
Independent review and source bindings are recorded separately; this is not a
kernel-checked theorem. The literal helper and finite-prefix checks are in
[`arithmetic_v3.py`](../code/arithmetic_v3.py).

The source frame must supply an actual intrinsic root, its initialized pair
(n,v)=(1,1), a right-infinite digit row at each positive logical time, and one
of the declared left carry starts. No externally supplied infinite boundary
is allowed: the frame theorem must force the initial zero tail from its finite
tile alphabet. The frame and polygon costs are separate from this lemma.

**The contract differs from v2.** There is no right endpoint or finite final
carry requirement. A legal rooted row may be an infinite binary stream that
does not represent a positive standard integer. Every accepted rooted row,
however, will be proved to have finite support and to represent a positive
standard integer. A nonstandard excursion is permanently nonaccepting. This
is not a claim that local rules force a canonical finite termination marker
in every legal tiling.

## Compatible residues instead of an implicit infinite integer

For a right-infinite LSB-first binary stream x=(x_0,x_1,...) define

    X_K = sum_{0<=i<K} x_i 2^i,   K>=1.

These are compatible residues: X_(K+1) is congruent to X_K modulo 2^K.
A stream represents a **standard nonnegative integer** m exactly when
X_K is congruent to m modulo 2^K for every K. Equivalently, it is the ordinary
finite binary expansion of m followed by infinitely many zeros. Equality of
two streams means equality of every finite prefix, and compatible residues
uniquely determine all bits. The constructions below can be phrased entirely
with these ordinary modular equalities. The usual name for this stream space
is the 2-adic integers; no interpretation of a nonstandard stream as a positive
integer is used.

Each vertical color is a bit pair (saved target bit, active bit). The two
fields are read in parallel, least significant bit first from the intrinsic
left boundary. Logical time increases in the direction forced by the source
spine. A fixed mode and input prefix determine at most one output prefix and
carry path.

## Exact infinite-row relations

The eight quotient states in the literal v2 alphabet are all singleton raw
control states. Thus no assertion about preserving infinite paths under an
arbitrary finite-word automaton quotient is needed. The state families are
DOUBLE D_0,D_1; PREIMAGE M_0,M_1,M_2; RESET R_0,R_1; and the shared initial
CHOICE U. The starts are D_0 and U. The families have no cross-family transitions
after the first letter. The former finite finals D_0,M_0,R_0 retain their
literal zero-pair self-loops, but are not required at an arbitrary finite cutoff.

Let N,V be the input streams and N',V' the output streams.

### DOUBLE

The saved bits copy. With initial carry c_0=0, the digit equation is

    2 v_i + c_i = v'_i + 2 c_(i+1),   c_i in {0,1}.

For every K, summation gives

    2 V_K - V'_K = 2^K c_K.

Hence N'=N and V'=2V in compatible-residue notation. The output is even.

### PREIMAGE

For an odd saved target, U on an even active first bit forces output first
bit one and carry two. This is exactly the first digit of the equation with
initial carry c_0=1:

    3 v'_i + c_i = v_i + 2 c_(i+1),   c_i in {0,1,2}.

The saved bits copy. For every K,

    3 V'_K + 1 - V_K = 2^K c_K.

Thus N'=N, 3V'+1=V as compatible residues, and V' is odd. No assertion that
ordinary integer division by three succeeds follows from an arbitrary legal
row. For example an input value two permits the nonstandard output stream 1/3.

Conversely an even input stream has exactly one output stream satisfying this
equation: multiplication by three is invertible modulo each 2^K, and those
solutions are compatible. The bit carry rule realizes it. Its allowed carry
range is invariant, as is checked directly from the two possible input bits
at each of the three carry states.

### RESET

For an odd saved target, U on active first bit one takes the RESET branch.
The first input and output bit pairs are both (1,1), and the successor carry
starts at one in the next column. Every later digit requires v_i=n_i,
sets v'_i=0, and performs ordinary binary addition on the saved field.
Consequently a completed infinite RESET row requires

    V=N,   N'=N+2,   V'=1.

The equality guard checks **all** input bits. An initial apparent reset in a
finite patch may fail at a later bit and have no completed reset row. Its
first-digit event is counted only in a completed legal tiling.

If N is a standard positive odd integer n, the equality guard makes V exactly
n. The binary successor carry discharges beyond n's highest bit, so N' is the
standard integer n+2 and V' is the standard integer one. No nonzero carry can
remain hidden forever above a standard saved target.

## Saved targets remain standard in every rooted run

Assume the frame initializes N=V=1. Induction on each finite logical time shows
that N is always a standard positive odd integer: DOUBLE and PREIMAGE copy it,
and a legal RESET changes n to n+2. In particular, every actual RESET has a
standard positive active input n and restarts at the standard value one.
This conclusion does not assume that the intermediate active streams are
standard.

## Backward standardness lemma

Suppose a legal nonreset edge has output stream equal to a standard positive
integer w.

For DOUBLE, w is even because the output low bit is zero. For any K, apply the
row equation at length K+1 and divide its ordinary integer congruence by two.
This yields V_K congruent to w/2 modulo 2^K. Thus the input stream is exactly
the standard positive integer w/2. The ordinary Collatz edge is C(w)=w/2.

For PREIMAGE, the input residues are congruent to 3w+1 modulo every 2^K, so
the input is exactly the standard positive integer 3w+1. The output low bit
was forced odd, giving the ordinary edge C(w)=3w+1.

Therefore, every finite nonreset segment ending at a standard positive active
value consists entirely of standard positive values, and reversing the segment
gives genuine ordinary Collatz edges. A nonstandard active stream can never
reach any later RESET, since that RESET's input is a standard positive integer.
This also excludes negative-integer streams from such a finite segment. The
frame must separately supply its actual finite-time initialization; an
unrooted infinite backward history is not being treated as that initialization.

## Infinite reset recurrence and full Collatz

The precise arithmetic assertion is:

> From the initialized stream pair (1,1), there exists an infinite legal row
> sequence with RESET at unbounded finite logical times if and only if every
> positive integer reaches one under the ordinary positive Collatz map.

Assume such a sequence exists. For any logical time t, choose the first RESET
at or after t; it exists because reset times are unbounded. Between t and that
reset there are finitely many nonreset edges. The reset input is a standard
positive integer, so the backward standardness lemma makes the active value at
t standard and positive. Thus **every row of the accepted rooted computation
has finite support in both fields**, despite the absence of locally forced
right endpoints.

For sufficiently large K, the data in an accepted row are ordinary zero tails.
Its genuine integer equation and the telescoping carry equation then force
c_K=0. RESET's ordinary successor carry likewise discharges. Thus every
accepted row has a finite valid v2 carry core, ending at D_0,M_0 or R_0, followed
by the corresponding zero-pair self-loop forever. No phantom nonzero carry
remains hidden beyond the finite support.

Between initialization or a previous RESET and the next RESET, the saved target
n is fixed and the active value begins at one. At the next RESET it equals n.
Reversing the finite segment proves C^t(n)=1 for some finite t. RESET advances
the target by exactly two, so unbounded resets certify all positive odd targets.
Every positive integer is a power of two times a positive odd integer, so these
certificates imply full positive Collatz.

Conversely, assume full Collatz. For each n=1,3,5,..., take its finite ordinary
trajectory to its first occurrence of one, reverse that finite path, and then
RESET at n. All operations are standard and satisfy the literal finite-word
relation proved in v2. Choose enough columns to contain the finite input and
output values. The terminal carry is one of D_0,M_0,R_0; append its zero-pair
self-loop forever. This produces actual legal infinite rows without adding a
tile type. Every block is finite, and infinitely many blocks give unbounded
reset times. The frame's separate construction fills the entire source plane;
the geometric compiler then supplies the completed polygon tiling.

There is no cutoff when a trajectory exceeds its input, no time bound, no
workspace bound, and no cycle-only criterion. A hypothetical failing target
can have neither a cyclic nor a nonperiodic forward counterexample silently
converted into a reset: either would contradict the extracted finite path to
one. Recurrence remains existential; legal runs may remain silent even when
every target converges.

## Concrete nonstandard and quiet exceptions

The sequence with fixed target one and active values 1,2,4,8,... is an
unconditional standard quiet run.

There is also an actual legal nonstandard run: DOUBLE from one to two, PREIMAGE
from two to the compatible residues of 1/3, then DOUBLE forever. The subsequent
active streams represent 2^j/3. None is a standard integer, because three does
not divide a power of two, so none can equal the standard target one. This is
a completed silent exception once placed by the source frame; it does not
satisfy reset recurrence. The finite alphabet contains no encoded irrational
constant or external infinite input: the nonstandard bits are forced by the
ordinary local carry recurrence after the finite choice of PREIMAGE at two.

The helper `rational_bits` reproduces these prefixes with integer arithmetic.
Finite prefixes and their mutation checks provide reproducible finite evidence;
the all-time rejection follows from the backward standardness proof. The
observer does not evaluate rational numbers, inspect digit strings, or check
these congruences. Its event recognition and global same-root time condition
remain separate, charged geometric definitions.

## Limits

This theorem permits nonstandard **nonaccepting** rooted tilings explicitly.
It does not claim that every legal row has a unique finite endpoint, or that
infinite occurrence of an arbitrary event-colored tile is sufficient. The
frame/observer compiler must identify the same root, correct event column and
unbounded logical row times. Rootless components are classified by that frame
proof and cannot supply the required root predicate. No complexity class is
assigned to unrestricted recurrent-tiling existence from this equivalence.

# Twenty-four digit types with active parity on the spine

## Scope and measured alphabet

This is a separate arithmetic compression of the reviewed v2 relation. It is
implemented by `HalfValueTransducer` in
[`arithmetic_v3.py`](../code/arithmetic_v3.py), preserving all v2 sources.
The literal generated alphabet has **24 digit types**: eight DOUBLE, twelve
PREIMAGE and four RESET. It uses seven horizontal carries and four vertical
bit-pair colors. It additionally requires **four spine types and two spine
parity colors**. Those interface costs are part of the design, not a free
interpretation of an unlabeled boundary.

The generator's arithmetic manifest SHA-256 is
`c5c561c6d3c07ec9684e59736f3b04050408b3160c59750be3be233a66788ce9`.
This manuscript is an ordinary mathematical proof authored by task agent
`/root/arithmetic`; independent review provenance is recorded separately.
It is not a kernel-checked result or a polygon side-count claim.

The central change removes the fixed low bit of the saved odd target and moves
the active low bit into the vertical spine interface. Write

    n = 2h+1,       v = 2a+p,       p in {0,1}.

The digit field stores (h,a), not (n,v). The saved half h is nonnegative and
the active half a is nonnegative whenever the active value is a positive
standard integer. The spine carries p between successive rows. Initialization
is (h,a,p)=(0,0,1), representing (n,v)=(1,1).

## Literal carry and parity interfaces

Carry IDs are fixed by the generator:

| ID | Meaning |
| ---: | --- |
| 0 | D_0 |
| 1 | D_1 |
| 2 | M_0 |
| 3 | M_1 |
| 4 | M_2 |
| 5 | R_0 |
| 6 | R_1 |

The four paid left-boundary interfaces are:

| Mode | Input parity p | Output parity p' | Initial carry | Event |
| --- | ---: | ---: | ---: | --- |
| DOUBLE0 | 0 | 0 | D_0 = 0 | no |
| DOUBLE1 | 1 | 0 | D_1 = 1 | no |
| PREIMAGE | 0 | 1 | M_2 = 4 | no |
| RESET | 1 | 1 | R_1 = 6 | yes |

All carry families are disjoint, and none changes family within a row. Finite
final carries are D_0,M_0,R_0, with IDs 0,2,5. The implementation generates the
following complete rules; the input bit pair is (h_i,a_i) and the output pair
is (h'_i,a'_i).

**DOUBLE.** Copy h_i and require

    2 a_i + c_i = a'_i + 2 c_(i+1),   c_i in {0,1}.

Equivalently a'_i=c_i and c_(i+1)=a_i. There are two carries, two active bits
and two saved bits, hence eight literal tuples.

**PREIMAGE.** Copy h_i and require

    3 a'_i + c_i = a_i + 2 c_(i+1),   c_i in {0,1,2}.

For each carry and input active bit, parity determines a'_i uniquely, and the
resulting next carry remains in {0,1,2}. Including the two saved bits gives
twelve literal tuples.

**RESET.** Require a_i=h_i, a'_i=0, and

    h_i + c_i = h'_i + 2 c_(i+1),   c_i in {0,1}.

For each carry and saved bit there is one tuple, giving four types. The
comparison, successor, and writing of the new active field are all included.

These families produce 24 distinct tuples. No DFA quotient or inferred tile
count is used. Enumerating every binary input/output letter and the seven
displayed states is a deterministic finite generator.

## Whole finite-word theorem

Fix a finite width W>=1, a declared spine mode, and binary pair words of that
width. Their LSB-first values h,a,h',a' are ordinary nonnegative integers.
An all-zero high prefix is allowed, and the physically supplied width is part
of the word. Every finite word therefore has one unambiguous pair of values.

A path beginning at the mode's initial carry and ending at its family's zero
carry exists if and only if the appropriate displayed relation holds and both
input and output pairs fit the given width:

| Mode | Complete finite-word relation |
| --- | --- |
| DOUBLEp | h'=h and a'=2a+p |
| PREIMAGE | h'=h and a=3a'+2 |
| RESET | a=h, h'=h+1 and a'=0 |

For DOUBLE, summing the digit equations gives

    2a+p = a' + 2^W c_W.

For PREIMAGE it gives

    3a'+2 = a + 2^W c_W.

For RESET it gives h+1=h'+2^W c_W, in addition to the bitwise equalities a=h
and a'=0. The finite final condition c_W=0 proves soundness. For completeness,
the usual binary addition or multiplication carry is forced at each bit. Its
range is exactly the one displayed above, and the asserted whole-word equality
forces the terminal carry to zero. Each mode and input word has at most one
output word and one carry path. Truncation cannot discard a nonzero overflow.

The paid parity interfaces convert these relations into genuine ordinary
inverse Collatz steps. DOUBLE has p'=0, giving

    v' = 2a' = 4a+2p = 2v.

PREIMAGE has p=0 and p'=1, so

    v = 2a = 6a'+4 = 3(2a'+1)+1 = 3v'+1,

and v' is odd. RESET has p=p'=1 and a=h, so its input has v=n; its output is
n'=2(h+1)+1=n+2 and v'=1.

For a positive standard input, these operations preserve positivity. In
particular PREIMAGE has a=3a'+2>=2, so its output v'=2a'+1 is positive; DOUBLE
of a positive input is positive; RESET writes one. The raw local alphabet also
admits the zero half-word in DOUBLE0, representing active value zero if used
without grounding. Positive arithmetic is asserted under the initialized or
accepted-source hypotheses, not for an arbitrary isolated ungrounded tile row.

## Infinite rows and accepted standardness

The intended compact source uses right-infinite digit rows. Its contract is the
one stated in [the stream theorem](stream-arithmetic-v3.md#scope-and-changed-contract):
arbitrary legal rooted active streams may be nonstandard, while acceptance
forces every rooted computation row to be standard and positive.

For an infinite half-word, let H_K and A_K be its residues modulo 2^K. Append
the literal low bits supplied by the encoding: the actual target stream has
low bit one followed by H, and the active stream has low bit p followed by A.
The row equations at every finite prefix give the same compatible-residue
relations as above, without imposing c_K=0 at an arbitrary cutoff. After
restoring p and p', they are exactly

    DOUBLE:   N'=N, V'=2V;
    PREIMAGE: N'=N, 3V'+1=V, V' odd;
    RESET:    V=N, N'=N+2, V'=1.

The spine is essential here: consecutive vertical parity colors force the
output p' of one row to be the input p of the next. A parity change cannot be
chosen afresh by an observer or test harness.

Starting at h=0, the saved half remains a standard nonnegative integer in every
rooted run. DOUBLE/PREIMAGE copy it; a completed RESET checks a=h at every bit
and increments h exactly once. The actual targets therefore enumerate positive
odd integers, regardless of intermediate active streams.

The backward-standardness lemma in the stream theorem now applies to the
actual active streams V. If a nonreset edge ends at a standard positive value,
its predecessor is the standard positive value v'/2 for DOUBLE or 3v'+1 for
PREIMAGE. A completed RESET has standard positive input n. Consequently a
nonstandard excursion can never have a later reset. Unbounded reset times
force every earlier rooted active stream to have finite support and positive
ordinary value. This proves that accepted rows cannot contain phantom carries,
negative integer streams or an unresolved infinite digit tail.

There is also a finite-core statement stronger than eventual-zero data alone.
In an accepted row, take K beyond the support of both input and output half
fields. The genuine integer relation and the telescoping equation force c_K=0.
All subsequent bit pairs are zero and the path follows its family's zero
self-loop forever. Thus every accepted infinite row is a valid finite carry
core, ending at one of IDs 0,2,5, followed by the standard zero tail. The source
does not provide a unique locally marked cutoff; all sufficiently large cuts
give the same positive integer arithmetic.

## Coverage, completeness and observer interface

Given full Collatz, reverse each positive odd target's finite forward path to
one and then RESET. The four spine signatures above realize every required
step. A finite core can always be padded with zeros, because a standard step
increases the bit length of either half by at most one. Starting from zero
halves, the operation at time t can use width t+1 and then append the zero tail.
The source frame supplies all of those columns geometrically; no externally
supplied tape or bounded workspace is used.

Conversely, an initialized accepted stream run certifies each consecutive odd
target by a finite genuine reverse path from one. The same argument as in the
stream theorem proves full positive Collatz, including exclusion of both
nontrivial forward cycles and nonperiodic failures. This is an existential
accepted-run assertion. Silent doubling and nonstandard silent excursions
remain legal nonaccepting examples.

The event is now recognized on the **RESET spine**, whose outgoing carry is
ID 6. Among the four spine types only RESET exposes that carry. Digit tiles can
also carry ID 6, so its unrestricted spatial recurrence is insufficient. The
frame/observer compiler must use the spine column of the same actual ROOT,
with unbounded positive logical row indices. Complete row legality then
supplies the full equality guard and successor beyond the local event contact.

The separate [source frame](stream-frame-v3.md) implements this interface in
`spine_frame_v3.py`. The 24 arithmetic types, four spine types, BG and ROOT give
30 actual source types, with eight horizontal and six vertical colors. This
source count does not assert any polygon upper bound: geometric specification,
all-plane converse, ROOT recognition, event recognition and measured side costs
must be proved and charged by the geometric compiler. ROOT no longer has the
older unique east initializer color, so its replacement geometric predicate
must be explicitly supplied rather than inherited from v2.

## Reproduction and limitations

```sh
python problems/collatz-polygons/code/arithmetic_v3.py
python problems/collatz-polygons/code/arithmetic_v3.py --manifest
python problems/collatz-polygons/code/test_arithmetic_v3.py
```

The tests compare the complete finite-word relation, not only a list of decoded
outputs; check exact tuple counts and interfaces; exercise rational stream
prefixes and counterfeit carries; and check standard certificates through the
paid parity modes. Finite computations do not decide infinite recurrence or
prove Collatz. The complete stream interpretation and acceptance implications
are the ordinary proofs above and in the linked stream theorem. No minimum
count, ordinary-tileability encoding or unrestricted recurrent-problem
complexity classification is claimed.

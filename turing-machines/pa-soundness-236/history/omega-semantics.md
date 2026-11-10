# A common omega observer for arithmetic-theory producers

This document fixes the observer before specializing its producer to PA. The
observer never mentions a theory, a proof system, an axiom, or the standard truth
of a selected sentence. Its finite-prefix decoder is executable; its acceptance
condition is a mathematical predicate on an infinite execution, not an algorithm
executed by the machine.

## 1. Physical events and complete frames

A physical execution is indexed by transition times t in N, starting with the
transition out of the initial configuration at t=0. Every transition has one
label from the fixed alphabet {silent, 0, 1}. Several transition rows may share
a label. A label is an event of taking a transition, not a promise that an
output-state name is visited only once. Initialization transitions are silent.
Erase silent events, preserving the order of all emitted bits.

Write u(k)=1^k 0. An address is a triple

    a=(n,p,(x1,...,xn)),  n>=1, p in N, xi in N.

Its record with value b in {0,1} is the finite binary frame

    u(n) u(p) u(x1) ... u(xn) u(b).

There are n+3 natural-number fields. The first field determines how many fields
remain; no extra start symbol, separator event, or output tape alphabet is
granted. Rank zero is not a legal address. A zero record has a physical final
zero field; absence of a frame is never interpreted as a successfully produced
zero record. The frame length is n+p+sum(xi)+b+n+3 bits and is positive and finite.

The decoder reads maximal runs of 1 terminated by 0. A first field of zero or a
final field exceeding one is a permanent syntax error. Complete frames determine
addresses and values. Identical repeated records are allowed. Two completed
records with the same address and different values are a permanent conflict.
An incomplete field or incomplete frame contributes no record. After a permanent
error, the decoder remains failed; later bits cannot repair the prefix.

### WellFormedTotal

For an arbitrary physical trace tau, WellFormedTotal(tau) means all of the following:

1. Every event is in the stated fixed alphabet and the parser never reports an error.
2. Every nonsilent event is eventually part of a completed legal frame.
3. No two completed records for one address conflict.
4. Every legal address has at least one completed record.

Condition 2 explicitly excludes a forever unfinished unary field. It is also
implied by condition 4 together with sequential error-free parsing, but retaining
it makes the progress contract visible. A finite event stream, an empty trace,
silent divergence after finitely many frames, and infinite writing inside one
unfinished frame all fail this guard. There are infinitely many legal addresses.

Define E_tau(a) on every trace, including malformed traces, as the value of the
first completed legal record for a before the decoder's first permanent error,
and use zero when there is no such record. Under WellFormedTotal this default
case never occurs and E_tau is the unique total recorded Boolean function.
The default exists only to make the following predicate defined everywhere;
it does not license acceptance of missing records.

## 2. The fixed acceptance predicate

For rank n>=1 let Q_i be existential when i is odd and universal when i is even.
Its dual is universal when i is odd and existential when i is even. Define

    Bad_n(tau) := exists p forall x1 exists x2 forall x3 ... dual(Q_n) xn
                   [ E_tau(n,p,(x1,...,xn)) = 1 ].

The definition of the alternating prefix is by finite recursion on n, with the
rank-zero suffix evaluating its matrix. In particular,

    Bad_1 = exists p forall x1 E_tau(1,p,x1)=1;
    Bad_2 = exists p forall x1 exists x2 E_tau(2,p,x1,x2)=1.

Finally,

    Accept_omega(tau) := WellFormedTotal(tau) and forall n>=1, not Bad_n(tau).

This is one theory-independent interpretation. The countable conjunction ranges
over unbounded quantifier ranks. It is not a fixed finite arithmetical formula
obtained by merely giving n a number variable, and it is not an eventual-silence
condition. A correct accepted producer emits infinitely many completed records.
No finite simulation decides the displayed predicate.

## 3. Presentations to which the construction applies

Fix the arithmetic signature 0, S, +, multiplication and equality. Boolean
connectives and first-order quantifiers are logical syntax. All domains in this
section are nonempty. The intended structure is the standard natural numbers.

An admitted effective presentation has a total decidable proof checker. Given a
natural code p it returns either an invalid result or the closed arithmetic
sentence which is its conclusion. Its certified sentences are exactly the
consequences of the stated calculus and theory. If the proof convention admits
open theorems, universal closure in a specified variable order is part of the
checker/conclusion interface and must be justified by its generalization rule.

The presentation must be closed under the ordinary classical first-order logical
consequences needed for normalization. This is automatic for a complete
first-order calculus with the specified nonlogical axioms. Mere equiconsistency
with another calculus is not a substitute for this consequence-preservation
condition. A recursively enumerable axiom set can also be used when each axiom
occurrence carries a finite enumeration witness checked in bounded time; the
proof checker, not a possibly nonterminating membership query, remains total.

Call a sentence normalized of rank n when it has a strictly alternating,
existential-leading prefix of exactly n>=1 single-variable quantifiers and a
quantifier-free matrix. Bound variables are distinct, and the matrix has no
unbound variables. Its variables are read in prefix order. Let

    Valid_T(n,p)

mean that p is accepted by this proof checker and its conclusion already has this
normalized shape and rank. Proofs with a different conclusion shape, the wrong
rank, a free variable, malformed syntax, or a failed inference are invalid at
this address. They receive explicit zero records. A nonnormalized theorem is not
ignored semantically: normalization coverage below supplies a proof of an
equivalent normalized theorem.

For valid p write R_p for its quantifier-free matrix, interpreted in N. Its
evaluation at any finite tuple terminates: variables are looked up in a finite
environment, arithmetic terms are evaluated by finite structural recursion, and
Boolean connectives combine Boolean results. This computes no quantified truth.

The producer's record function is

    E_T(n,p,x) = 1 iff Valid_T(n,p) and R_p(x) is false in N,

and is zero otherwise. The proof checker and structural parser run before matrix
evaluation; an invalid proof has no purported matrix whose evaluation could
diverge or access an undefined variable.

The physically economical implementation enumerates proofs whose conclusions
are already normalized. A separate checked normalizer is a reference and a
coverage witness; prenex conversion need not execute inside the physical
producer. This is an implementation choice with a proof obligation, not a
weakened theorem set.

## 4. Complete normalized coverage

Here is a constructive normal-form argument with an explicit rank convention.
Begin with a closed arithmetic sentence A.

1. Expand derived Boolean connectives into negation, conjunction and disjunction.
2. Move negations inward, replacing a negated quantifier by its dual. Rename
   bound variables so all binders are distinct and disjoint from every free
   variable in the surrounding subformulas.
3. Move the finite quantifier prefixes outward across conjunction and
   disjunction. Each move uses the usual equivalence

       (Qx B) * C <-> Qx(B * C), when x is not free in C,

   and its symmetric version, with *=and/or and Q=exists/forall. The variable
   condition and nonempty domain are essential. After these moves the matrix
   is quantifier free. No rank-preservation claim is made for the original syntax.
4. Scan this finite prefix, expecting an existential quantifier first. If the
   next real quantifier has the other polarity, insert a fresh dummy variable
   with the expected quantifier, then place the real quantifier. After each
   placement toggle the expected polarity. Consecutive equal real quantifiers
   thus get an intervening vacuous opposite quantifier. A universal-leading
   prefix gets a dummy leading existential. An empty prefix becomes one dummy
   existential. Finally rename the prefix into the chosen canonical convention.

Vacuous quantification preserves truth and is provably equivalent over a
nonempty domain. If the prenex prefix before padding has m>0 variables, the
resulting rank is between m and 2m. For m=0 it is exactly one. The matrix ignores
dummy-variable positions. Universal-leading and rank-zero sentences therefore
have complete coverage without special cases in the observer.

Every local equivalence has a finite classical first-order derivation with the
stated freshness conditions. Consequently there is a finite proof of
A <-> N(A), and any proof of A extends to a proof of N(A). This statement is
syntactic and does not assume that the theory's axioms are true. An implementation
claim that constructs these proof extensions must preserve its derivation
certificate; otherwise the status is the conventional proof of coverage, not a
kernel-checked compiler for proof objects.

For example, an unquantified 0=0 becomes exists d (0=0). The sentence forall x
x=x becomes exists d forall x x=x. The prefix exists x exists y forall z becomes
exists x forall d exists y forall z. All dummy variables are fresh. The same
transformations apply to false sentences, not only to known true examples.

## 5. The general reduction theorem

**Theorem.** Let T be an admitted effective arithmetic presentation, and let
M_T be any complete ordinary machine whose decoded trace is WellFormedTotal and
whose recorded function is exactly E_T. Then

    Accept_omega(trace(M_T)) iff every arithmetic sentence proved by T is true in N.

**Proof.** Fix n and p. If Valid_T(n,p) fails, E_T is constantly zero as a
function of its n tuple arguments. Any finite alternating prefix of quantifiers
over the nonempty domain N applied to this false constant is false. Thus this p
cannot witness Bad_n.

If Valid_T(n,p) holds, write its conclusion as Q1 x1 ... Qn xn R_p. Classical
quantifier duality, by induction on n, gives

    not [Q1 x1 ... Qn xn R_p]
       iff dual(Q1) x1 ... dual(Qn) xn [not R_p]
       iff dual(Q1) x1 ... dual(Qn) xn [E_T(n,p,x)=1].

Therefore Bad_n holds exactly when a normalized rank-n theorem is false. This
step does not assume T sound. If T is sound, none of these bad channels exists.
Conversely, if T proves any false sentence A, normalized coverage gives a proof
p of N(A) at some finite rank n, and its provable equivalence to A makes N(A)
false in N. That p witnesses Bad_n, so the omega observer rejects. The guard
already holds for the intended producer. This proves both directions. QED.

The forward implication is a structural consequence of coverage and the record
equations. It is not obtained by assuming PA sound and observing that a constant
all-zero trace accepts. The same producer algorithm responds to an effectively
changed theory's actual checked proofs; false fixtures produce bad channels.

For each fixed n the intended computable producer yields a finite-rank statement
of the form exists p forall x1 exists x2 ... with a decidable matrix. Its negation
is the corresponding fixed-rank soundness statement for normalized proofs.
The omega theorem collects every n; separate low-rank stabilization cannot be
replaced by one global last-event condition.

## 6. A fair schedule using one unbounded counter

Let pair(a,b)=(a+b)(a+b+1)/2+b be Cantor's bijection and unpair its total inverse.
At stage s=0,1,2,..., decode

    (a,r) = unpair(s); n=a+1;
    (p,r) = unpair(r);
    repeat n times: (xi,r)=unpair(r).

Discard the final residual r. Compute the one Boolean E_T record, emit its finite
frame, and advance s. This requires no fixed maximum rank and no queue of
unfinished matrix evaluations. Every individual proof check, matrix evaluation,
unpairing, loop of n iterations and unary frame emission terminates.

For a prescribed address a=(n,p,(x1,...,xn)) and any tail t define

    C_t(a)=pair(n-1,pair(p,pair(x1,...,pair(xn,t)...))).

Unpairing shows the scheduled address at stage C_t(a) is exactly a. The function
t -> C_t(a) is strictly increasing, since pair(c,t) is strictly increasing in t.
Thus every fixed address is served infinitely often, including addresses at
earlier ranks. There is no starvation. The mechanism neither exchanges nested
limits nor samples each rank just once. Because the Boolean function is
deterministic, repetitions agree. These facts establish WellFormedTotal.

The reference inverse uses integer square root. A physical compiler may instead
use terminating repeated subtraction or a triangular-number loop; the inverse
equations and termination proof are its implementation obligation. Both versions
must be compared on exact integer values, never floating-point approximations.

## 7. Simulation and permitted changes

The compiler must provide a relation between source configurations and physical
configurations at block boundaries b_0<b_1<... . Startup through b_0 is finite
and silent. For each source step, its physical block is positive and finite,
terminates in the related next configuration, and emits exactly the prescribed
source event word in order. Strict increase implies b_k>=b_0+k, so these blocks
cover physical time cofinally. Merely proving that every *completed* block is
correct would leave silent divergence unaddressed.

Under these conditions erasing silent transitions yields the identical bit
stream, so framing, the totality guard, every E value, and acceptance are
preserved. An event can be moved from a state exit to a finite transition adapter
when the adapter emits it exactly once and preserves event order. Its states,
initialization, tape handling and transitions count toward the physical machine.

The following preserve acceptance when their hypotheses hold:

- finite silent startup changes and arbitrary finite silent delays between events;
- order-preserving positive finite block simulations with cofinal boundaries;
- physical state renaming accompanied by the same transition-event labels;
- reordering whole completed records, or adding/removing identical duplicates,
  provided every address remains covered and all events still complete frames;
- adding finitely many complete records to an already WellFormedTotal trace,
  at frame boundaries and agreeing with its existing total recorded function.

Arbitrary finite bit prefixes, incomplete headers, bit reordering, conflicting
duplicates and omission of a zero-valued address do not have this invariance.
Infinite delays are not finite stutters. A finite delay can be arbitrarily long
and still preserve acceptance, but a source obligation delayed forever fails
the guard.

The hypothesis on finite record additions cannot be omitted. Start with an
all-zero producer enumerating every address except one fixed address a0. It has
legal frames and no conflicts but fails total coverage, so it is rejected. Add
the single zero record for a0 at the beginning. The new trace has full coverage,
all Bad_n are false, and it accepts. Thus finite *event* modifications do not
have ordinary eventual-silence invariance. `test_missing_zero_record_does_not_count_as_coverage`
retains the corresponding finite-window regression; this paragraph establishes
the unbounded counterexample analytically.

## 8. PA and the metatheory

Instantiate T with unrestricted first-order PA: arithmetic signature as above,
the specified equality and arithmetic axioms, induction for every arithmetic
formula with parameters, and a complete classical first-order calculus. A
bounded induction fragment or merely equiconsistent replacement does not meet
this instantiation without the requisite consequence theorem.

The conventional uniform proof here is made in an external metatheory capable
of discussing finite syntax, the standard N-structure and its satisfaction
relation. ZFC is a sufficient explicit choice. It constructs satisfaction for
all finite first-order arithmetic formulas by recursion on syntax and proves
the statements above uniformly in rank. No assertion about the least possible
metatheory is needed for the construction.

For each fixed rank, a finite partial arithmetic truth definition suffices for
the semantic duality and reduction lemma. After the concrete coding and
termination invariants have been formalized, these form individual arithmetical
theorems/schemas; they do not by themselves instantiate one internal
arithmetical predicate for truth at every rank. The uniform all-rank theorem
uses the external satisfaction relation or an explicitly stronger semantic
extension. Tarski's undefinability issue is not evaded by calling a number a
formula code. A Lean development can define satisfaction in its stronger type
theory; that is not a claim that PA defines its own full truth predicate.

Separately, ZFC proves that the standard natural-number structure satisfies PA.
Arithmetic axioms hold by the construction of N. Each induction instance holds
because induction on standard natural numbers applies to the subset defined by
that formula with its fixed parameters. First-order inference soundness then
gives Sound(PA). Together with the machine reduction this gives acceptance as
a separate ZFC corollary. The construction is consequently not automatically
independent of ZFC, and its equivalence proof does not require PA to prove its
own soundness.

## 9. Analytic fixtures and bounded tests

Sound fixture: pure first-order equality logic, or its closure with finitely
many arithmetic axioms known true in N. Inference soundness proves acceptance.
Inconsistent fixture: both 0=S0 and its negation; classical logic proves a false
normalized theorem, so rejection follows.

A useful consistent but explicitly unsound fixture is first-order equality
logic with the single axiom forall x x=0, without PA's other nonlogical axioms.
It has a one-element model, so it is consistent, but its axiom is false in N.
Its normalized rank-two consequence exists d forall x x=0 witnesses rejection.
This separates standard soundness from consistency without an incompleteness
assumption about a stronger theory.

True and false fixtures at additional normalized ranks include:

| Rank | True sentence | False sentence |
| --- | --- | --- |
| 1 | exists x x=x | exists x not(x=x) |
| 2 | exists d forall x x=x | exists x forall y x=y |
| 3 | exists x forall y exists z z=y | exists x forall y exists z y=0 |
| 4 | exists x forall y exists z forall w z+y=y+z | exists x forall y exists z forall w z=w |

The truth values are about N and follow directly from equality and elementary
arithmetic. In the false rank-four example, for every z there is w different
from z. Dummy and redundant quantifiers are intentionally retained.

Finite tests can verify decoding, conflicts, zero records, partial frames,
delays, finite schedule windows, inverse coding equations, and the dual-prefix
identity on a finite test domain. They cannot infer a fixture's unbounded truth
by substituting a finite domain. In particular, exists y y>x is true over N and
can fail at the largest point of a finite test domain.

`trace_semantics.py` supplies these finite-prefix utilities. Its test file checks
11 cases, including an independent bottom-up truth-table evaluation at ranks up
to three. The tests support implementation claims only; the infinite theorem is
the argument above. A selected literal-table release still requires exact-byte
review of its proof checker, compiler, labels, table and independent simulators.


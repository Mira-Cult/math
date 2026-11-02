# Phased prime allocation and reflected bins for the signed cube

Public proof manuscript. See [provenance](../PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## 1. The precise finite replacement

Use [FSC](explicit_signed_controller.md)'s notation: exact input pool, n,X,T,m,mu,g,F,P,R,K0,...,K3,
delta, the complete invoice Q, and Q*=2^21 n²K2. Put


```math
Q_0=4288n^2P+8(192n+4)P+(8n^2+38n-14)R.                 \qquad\text{(R1)}
```


This counts all prefix endpoints, including their seeds, and every old and
new residue endpoint. It contains no macro endpoint. The seed gap and its
reduced lower class are selected exactly as in the first composition;
the full seed-pair demand is still 256F²(2144n²+768n+16).

**The finite phased controller FSR.** Retain all FSC geometry, centering,
capacity, compatibility, invoice and floor conditions. Retain PS1. Replace
PS2 by its same fresh-growth requirement after at most Q0 deletions, and
retain the residue part of PS3 only after at most Q0 deletions. Replace the
macro part of PS3 by the reflected-stock conditions below. Then FSC's same
conclusion holds for every compatible odd target vector within K0X of mu.

Here is the construction proving this finite implication. Plan all supports
using the existing finite packing proof, with g fixed by the initial seed
selection. Reserve all seed pairs first. Complete **every** main prefix,
then select **every** old and new residue gadget, before allocating any
macro entry. The maximum preceding deletion in these phases is Q0. Growth
therefore uses the fresh common class with its four-pair matching argument;
residue gadgets use actual equal gaps 2 modulo g in endpoint classes -1,+1.
When g=2 the residue phase is empty. The growth lengths are at most P and
all residue lengths at most R, exactly as in the original invoice.

Allocate all macro stages last by the following finite matching argument.
The selected four pairs may come from different reduced classes, but every
pair's endpoints are in the same class modulo g. Their shared actual gap is
therefore a multiple of g. FSC's complete-grid extension, midpoint expectation,
physical cuboid and scalar capacity proofs require precisely that gap and
midpoint property; they do not require a fixed lower endpoint class across
macro stages. Each macro stage has four actual disjoint pairs when needed.

The resulting filled reservoir system has exactly the geometry and prime
values required in FSC Sections 2 onward. Its fair choices are whole
complementary reservoir orientations, with the same ranges and native floors.
The rest of its finite centering, all-line residue repair, axis/body/face
correction and exact-pool preservation proof applies without alteration.
This proves FSR once the allocation lemma below is established. It is a new
finite composition, not an application of old USC3 with changed parameters.

## 2. Reflected bins and exact adaptive deletion accounting

Let w=1/48 and suppose 0<delta<=w/2. Set


```math
B=\lfloor w/\delta\rfloor\ge2,\qquad h=2\delta X,
 \qquad a=m-X/6-wX.
```


For i=0,...,B-1, let the lower interval be
$`I_i=(a+ih,a+(i+1)h]`$. Its upper partner has the reflected center:


```math
J_i=(2m-a-(i+1)h,\;2m-a-ih].                           \qquad\text{(R2)}
```


Both families consist of disjoint half-open intervals. The full lower and
upper bands are disjoint, and all their endpoints lie inside [X/4,3X/4]
under the exact-pool mean box 12X/25<m<501X/1000. These endpoint conventions
make each prime belong to at most one bin on either side. They also allow
direct application of the half-open prime-count theorem. Reflection of an
endpoint convention is not needed: the two centers, lengths and disjointness
are the facts used here.

Suppose every bin and every reduced class modulo g has at least


```math
W=\frac{\delta X}{\varphi(g)(L+1)}             \qquad\text{(R3)}
```


primes before any allocation. After arbitrary preceding deletions, write
A_(i,r),B_(i,r) for the two remaining stocks and


```math
S=\sum_{i,r}\min\{|A_{i,r}|,|B_{i,r}|\}.
```


Deleting one prime decreases S by at most one, because it lies in at most
one of these bin/class sets. This is true for adaptive choices and concentrated
deletions; it uses no independence. Thus after at most Q* deletions,


```math
S\ge B\varphi(g)W-Q_*
   =\frac{B\delta X}{L+1}-Q_*.
```


Since B delta>=w/2, the condition


```math
Q_*\le\frac{wX}{4(L+1)}                         \qquad\text{(R4)}
```


implies S>=wX/[4(L+1)]. The complete Q invoice is checked below Q* before
this is used, so every preceding prefix, residue and macro deletion is paid.

Within each matched bin and class all lower/upper pairs have g-multiple
positive differences. Their total number is at least


```math
\sum_{i,r}|A_{i,r}||B_{i,r}|
 \ge\sum_{i,r}\min(|A_{i,r}|,|B_{i,r}|)^2
 \ge\frac{S^2}{B\varphi(g)}.                           \qquad\text{(R5)}
```


There are at most floor(X/g)+1 possible differences, at most 2X/g when
X>=g. Since g/phi(g)>=1, one actual difference occurs at least
S²/(2BX) times. A sufficient condition for four occurrences is


```math
\delta wX\ge128(L+1)^2.                          \qquad\text{(R6)}
```


Indeed B<=w/delta and S>=wX/[4(L+1)] give S²>=8BX. For a fixed
positive difference, the upper partner of any lower prime is unique and
the lower partner of any upper prime is unique. The two whole bands are
disjoint. Consequently these occurrences are already a matching, even if
they came from different bins or reduced classes. Four distinct pairs can
be selected and immediately removed. No prime is counted twice in (R5).

Every selected pair has midpoint within delta X of m. Its difference lies
between X/3-2wX=7X/24 and X/3+2wX=3X/8, hence inside [X/4,X/2]. The
matching argument remains valid after each later request by the same exact
stock invariant. It supplies every ordinary, rectangle and cuboid macro,
paying four pairs per cuboid and leaving unused candidate primes available.

The number B may be very large. It is finite and explicitly defined; no
efficient implementation at the cutoff is claimed. The only multiplicity
cost of many bins is the B in (R5), and (R6) explicitly pays it.

## 3. Effective supply at all local centers

Set delta=eta/L^d with a fixed positive rational eta<=1 and positive integer
d. In the final profile d=2. Each bin has center Y in the fixed bands, with


```math
\frac{117}{400}X\lt Y_-\lt X,\qquad
 \frac{751}{1200}X\lt Y_+\lt X.                              \qquad\text{(R7)}
```


The original residue centers m±X/6 have still larger respective lower
bounds, 47X/150 and 97X/150. With u=logY, we have L<u+2. For
u>=4d, (1+2/u)^d<=2, so the actual bin/residue length 2delta X is at
least eta Y/u^d. The strong analytic interface with denominator
ceil(1/eta), exponent d therefore covers every bin and residue request.
Its bound is at least (R3), because log(2Y)<L+1. Also
g<=24L+16<=64u. Each interval is contained in [Y/2,2Y], and both bands
lie in the original pool. The actual lower bin center is paid in the
order-to-scale conversion; it is not replaced by X or by m.

During the early phase, it suffices to check


```math
Q_0\le X/(8gL),\qquad
 Q_0\le\delta X/[2g(L+1)],\qquad
 \delta^2X\ge32g(L+1)^2.                               \qquad\text{(R8)}
```


The global class then retains at least X/(8gL)>X/(gF), while each early
residue endpoint class retains at least delta X/[2g(L+1)]. The latter
product is at least 4(floor(X/g)+1), exactly paying its four-pair request.
These are the first composition's finite matching arguments with the
correct smaller preceding invoice Q0, not Q*. The macro phase uses (R4)
and (R6) instead, across all classes and reflected bins.

## 4. Whole-tail certificate and architecture boundary

The companion arithmetic (see [verification scope](../PROVENANCE.md#explicit-prime-cube))
uses X/n³>L/2, n>=L^201, F<=100L+1, g<=24L+16, R<=12L+7 and
Ki/n<=ki L^-ai+L^-201. Its thirteen ratios include the seed floor,
the full early invoice, both early stocks, four-pair multiplicities,
the bin floor, total macro depletion, interval containment and local domains.
Every ratio is a nonnegative Laurent polynomial with nonpositive powers.
Its value at the selected endpoint therefore proves the entire real tail,
with all rounding and bin-count jumps handled pointwise.

The improvement is structural. Charging every macro deletion against one
narrow class forces a2>=d+1 for log exponents. Aggregating all classes in
one narrow pair of bands relaxes this to a2>=d. Reflected bins in fixed-width
bands remove d from the total depletion condition. Fixed small positive
fractions K2/n and K3/n are then allowed, provided the **finite** packing
conditions are checked. No old o(n) exclusion is retained in place of that
check. The unchanged tensor bound still requires a1>=a2+2; the final
profile realizes a0=a1=2 and a2=a3=0 with exact rational multipliers.

This allocation proof does not change the exact input pool, any required
line, correction order, target compatibility, or incidence exceptions. It
does not claim that fewer bins alone improves the final maximum. The actual
composite cutoff and its independent review are separate from this finite
lemma.

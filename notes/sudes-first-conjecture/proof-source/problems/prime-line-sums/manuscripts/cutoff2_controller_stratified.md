# A stratified full-pool controller beginning at odd order 38,969

Author: `/root/controller_redesign`. This additive numerical controller
preserves GP, CF and every earlier frozen proof. It needs independent
nonauthor review at the exact scientific revision. The complete upper-tail
composition is a separate root deliverable; no formal kernel theorem is
asserted.

## SC1. Exact order cover and input

Use exactly the first n^2 odd primes, once each, with n odd. Let
X=p_(n^2+1), T be their total, m=T/n^2, y=T/n and v=log_2 n.
This controller covers

    n^4>=2^61,                         n^2<2^31.       (SC1)

The exact comparisons

    38967^4<2^61<38968^4,
    46340^2<2^31<46341^2

make the first relevant odd order 38969. The numerical proof has three
contiguous closed real-order bands:

| Band | v lower | v upper | Target denominator R | Growth-pool coefficient rho | Allocation depth cap |
|---:|---:|---:|---:|---:|---:|
| 1 | 61/4 | 245/16 | 2800 | 9/10 | 18 |
| 2 | 245/16 | 123/8 | 2800 | 9/10 | 18 |
| 3 | 123/8 | 31/2 | 1800 | 112/125 | 19 |

Each band has a fixed, explicitly listed profile for every even g<=30.
The exact input manifest gives all integer seed counts, stage caps,
stratum counts, bridge geometries, flow parameters and rational
allowances. At n^2>=2^31 the frozen GP controller applies. Its CF and
subsequent handoffs belong to the root's complete infinite-tail theorem.

The common graph has degree6 and cut expansion26/25. The growth pool
remains (X/8,X], while only the initial seed matching uses the larger
known input pool. The mean bounds .487X<m<.492X and the index gain
X/n^2>log X-9/8 are BG's actual-scale statements.

## SC2. The source envelopes and graph threshold

Use a=693147/10^6, b=693148/10^6 and

    i=305121/100000,       s=118251/50000.

Directly reapplying Rosser--Schoenfeld to j=n^2+1, with n^-2<=2^-30,
gives the whole-band envelopes

    log X >=2av+i,          E=ceil(log_2 X)<sv,
    log X < b(sv-1).                                  (SC2)

The upper proof pays the complete ceiling unit; the lower proof checks
i<log(2av) at v=61/4. The exact verifier checks the original index domain,
the endpoint, and the positive derivative of the smooth majorant. It
never differentiates E across a jump. Both lower and upper logarithmic
scales lie in BG's actual domain 24<log X<29.

For each band [v0,v1], put n0=floor(2^v0), n1=floor(2^v1)+1 and

    U=2av0+i, V=b(sv1-1), Q=U-9/8, X0=n0^2 Q.        (SC3)

All these quantities are certified as exact rational envelopes. The
sixteenth-root comparisons for n0,n1 pay every integer endpoint. The
first two bands have 6(n1+8)<=2^18; the last has 6(n1+8)<=2^19. Thus
all deterministic-allocation depth jumps are covered. Every K=floor(n/C)
is enclosed by K>=n(1-C/n0)/C.

The original degree-six graph proof uses epsilon=1/400. Its small-cut
entropy inequalities are unchanged and rechecked. For the large-cut
union bound, retain log2 in the actual condition

    epsilon n > [6(v+2)+3]log2.                     (SC4)

The rational bound with n=n0, v=61/4 and log2<b proves SC4, and
epsilon n0>6 proves persistence. The former replacement log2<1 is
unnecessary here. No graph theorem is imported below its literal
premise; its numerical hypotheses have been re-established.

## SC3. Target primes and the actual small modulus family

On the first two bands TL supplies the exact-total TP construction with
D=y/2800 and local raw growth count rho X/log X with rho=9/10.
Its source statement applies throughout 61/4<=v<=123/8, which the
controller checks before using that coefficient. The actual input
scale satisfies 24.19<log X<24.52 on these bands. On the third band,
the unchanged DT row from v=61/4 supplies R=1800, and S18 supplies
the general raw coefficient112/125 on 24<=log X<=29.

TL's target saving uses a finite verified wheel potential to select an
actual even gap h<=42 with phi(h)<=12. It does not incorrectly assign
phi<=12 to every even modulus<=36: h=32 and34 are explicitly excluded
by the selection argument. For the possible h=42, the relevant odd
prime classes are exactly those of the corresponding class modulo21.
All target intervals and primitive-character error terms are paid by
TL's source-bound specialization. The numerical checker does not
independently prove BMOR's analytic theorem or repeat its zero verification.

The target modulus h is independent of the entry gap g. The exact-total
list contains exactly n odd prime targets summing to T; repetitions of
target values are allowed. The same list may be used for rows and
columns. Both diagonals have their own prime targets in the same radius.
The exact parity, finite-list and arithmetic-grid hypotheses are supplied
by TL or DT, and every actual entry/bridge/central interval still uses
the full S18 BMOR1.9 count inside (2,X], with X<2^41<10^13.

## SC4. Full-pool seed selection and class separation

Fix all fifteen gap profiles before selecting a label. Let G=30,
H=G+2, b_g=ceil(log_2(g/2)), Q_s=6(n+8), s_g be the number of
retained seed stages, t_g the number of midpoint strata, and J_g the
number of preselected bridge stages. The full-pool FS lemma applies
to all prescribed input primes greater than G. Its exact vertex count
is n^2-pi(G)+1, and its span is less than X.

The class-separation lemma CS changes only the destruction of that
fixed-class seed matching. For g>=8 every binary pair can choose its
two unit classes to avoid the seed class. For g>=4 every bridge may
use the opposite unit class -a. Bridge differences remain multiples
of g, and the later BN phase imposes the actual target residues after
completion. The genuine exceptions are g=2,4,6. Set

    L_g=2Q_s J_g                    if g=2,
    L_g=2(n+1)b_g                  if g=4 or6,
    L_g=0                          if g>=8,
    D_g=Q_s(s_g+t_g-1)+L_g.                          (SC5)

The single weighted seed condition is

    n^2-pi(G)-X/H
        >2 sum_{even g<=G} phi(g)(1-g/H)D_g.         (SC6)

It chooses one gap and one reduced seed class with enough disjoint
pairs for that gap's own profile. After all residue and bridge entries
are selected with their original budgets, at most L_g pairs are lost.
No favorable class or independent overlap assumption is used.

All other invoices retain the full residue and bridge counts. In
particular the pooled growth stock subtracts every residue entry and
every bridge entry, even though they avoid the selected seed matching.
Every local residue-side charge, bridge overlap, rectangle and baseline
term is unchanged. CS is not an excuse to subtract L_g from the pooled
or geometric reservation count.

## SC5. Stratification and the kept-entry invoice

From the surviving Q_s(s_g+t_g-1) pairs, FS partitions midpoints into
t_g bins of width X/t_g, sorts inside each bin, and takes exactly s_g
full groups of Q_s pairs. The floor identity guarantees enough groups.
Only 2Q_s s_g entries are reserved. All unkept candidates remain
available to later phases and to the exact final permutation.

All retained seed pairs still have the same gap g. Their stage ranges
satisfy sum R_i^2<=X^2/t_g and max R_i^2<=X^2/t_g^2. Hence the initial
all-line allocation error, in units of X, is bounded by

    sqrt((18/t_g+4/t_g^2)log(8n+8)/2).                (SC7)

The common growth stages remain in (X/8,X]. From each z_g Q_s-candidate
batch, keep only Q_s pairs in midpoint width7X/(8z_g), and add DP's
separate bound

    10(7/(8z_g))ceil(log_2 Q_s).                    (SC8)

The actual kept stage means and prime total are used throughout PB's
cancellation identity. No unkept candidate is counted as a deletion.
The full seed pool still has midpoint distance at most .513X from m,
so the existing prefix mean-bias allowance is unchanged. All retained
seed entries are conservatively charged against the later growth pool.

## SC6. Prefix, bridge, placement and completion gates

After the selected gap is fixed, the MC/AW/BT mechanisms are exactly
those verified in GP, with that gap's numerical data. Let P_g=s_g plus
the sum of the declared integer growth caps. Candidate groups t_g-1
are not additional stages. With the band envelopes SC3, define

    epsilon_g=1/[2(7/8+1/L_split,g)]-eta_g,
    mf=f alpha_g/V,       f=9999/10000,
    q=6(n0+8)/X0,
    m0=rho/V-4(n0+1)b_g/X0-2q(J_g+s_g).             (SC9)

Every actual retained stock is at least X(m0-2qj). The checker pays
the complete candidate batch

    epsilon_g mf^2 g >=2z_g q phi(g),               (SC10)

and all integer floors. Every affine-wheel phase subtracts its own
origin; every BT phase pays its actual interval-length threshold.
The direct logarithmic growth comparison uses the declared integer
caps and the decreasing retained stock. If the actual complete grid
reaches X/L_split,g early, later phases are not invoked, though all
caps remain charged. This is the already explicit conditional
stopping rule, not a use of a source outside its range.

The complete bridge geometry is recomputed separately for each gap.
All same-side window overlaps and residue intersections are paid.
Bridge classes can differ from the seed class because only their
positive g-multiple differences and equal-gap diagonal copies are
used. Every difference and midpoint endpoint remains within its
certified interval.

The full entry fraction is

    Z=4(n0+1)b_g/n0^2
       +12(1+8/n0)(P_g+J_g)/n0
       +84(1+8/n0)/C_g.                             (SC11)

The reflected-bin aggregate and stock-square inequalities use the
full BMOR density, every source endpoint and this entire Z. RP's
rectangle packing and the retained ordinary matching condition are
both checked. The latter also supplies RF's actual-r0 regular-factor
domain; r0 always refers to the actual number of executed stages.

RF fills both diagonals, pays the signed conditional mean shift,
reserves its central exceptional stock, and factors the remaining
support. Its central interval is separated from all wide and residue
bands. The count pays every prefix and bridge entry, all prior
diagonal choices and all exceptional entries. The completion
allowance is (4+2(9b_g+6)epsilon_c,g)X.

Add SC7--SC8, the retained prefix mean, signed binary residues,
shared wide midpoints, bridge midpoints and RF completion. Each exact
manifest profile gives a rational baseline allowance beta_g. The
certificate proves

    baseline error < beta_g KX,
    beta_g + .492 C_g/[(1-C_g/n0)R]
                          < (999/1000)(26/25).       (SC12)

It also pays the integer-flow slack and every position restriction.
The original finite controller then makes every row and column equal
to its selected prime target and fixes both independent diagonal
prime targets. All input entries are used exactly once; prime line
sums may repeat.

## SC7. Whole-band seed persistence and certificate scope

For the full-pool seed gate, use the direct RS upper-index ratio

    W(v)=(1+2^-30)[z+log z-1/2],
    z=2bv+2^-30,                 X/n^2<W(v).        (SC13)

The weighted demands in SC6 sum to An+B with exact positive rational
A,B for each band. The numerical comparison is

    [2(An+B)+pi(G)]/[n^2(1-W(v)/H)]<1.              (SC14)

The checker verifies H>W(v1) and

    (1+2^-30)2b(1+1/(2bv0+2^-30))
                      /[H-W(v1)] < a.              (SC15)

This is FS's strict derivative guard, so SC14 decreases throughout
the band. Both endpoints are also checked using exact integer lower
order bounds. All other n-dependent quantities use the fixed band
envelopes and pointwise rounding bounds in SC3. No floating mesh,
endpoint-only heuristic, or derivative across E,e,K jumps is used.

The standard-library verifier and complete exact input manifest are
`code/cutoff2_controller_stratified.py` and
`inputs/cutoff2_controller_stratified_inputs.json`. The required public
source closure fails on missing, empty, malformed, extra, mismatched
or physically substituted files. Negative controls attack the actual
seed budget, candidate multiplicity, phase growth, target flow,
central stock, geometry, integer depths and contiguous handoffs.

The finite arithmetic does not independently prove the imported
analytic theorems or kernel check the conventional graph, matching,
probability and construction arguments. Exact-revision independent
review and the complete upper-tail composition remain prerequisites
for presenting the new cutoff as established.

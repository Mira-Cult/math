# Gap-dependent controller profiles from the square-root order 2^31

Author: `/root/controller_redesign`. This is an additive, conditional finite
controller supplement. Its numerical certificate and mathematical composition
require independent nonauthor review at the exact scientific revision. It
preserves every frozen source, including CF. It does not itself assert the
complete infinite-tail theorem.

## GP1. Domain and the new optimization

Let n be odd, let X=p_(n^2+1), and use exactly the first n^2 odd primes.
Write T for their total, m=T/n^2, y=T/n, v=log_2 n, and u=log X.
The domain of this component is

    n^2 >= 2^31,                  n^4 < 2^63.             (GP1)

The first integer order is 46341. The two real-order bands are

    31/2 <= v <= 249/16,          249/16 <= v <= 63/4.    (GP2)

The endpoint 63/4 is included in the finite checks to give a closed
numerical cover. CF supplies the adjoining domain n^4>=2^63, and the root
composition is responsible for its subsequent handoffs and the infinite tail.
This supplement uses the same underlying finite controller as CF, but does
not invoke CF's literal lower-order premise below its domain.

The main change is to fix a different valid numerical profile for each
possible even seed gap g in {2,4,...,34}. Each profile includes its own
seed-stage count, prefix mass and growth rate, affine-wheel and BT schedule,
bridge geometry, reflected-bin width, candidate multiplier, flow parameter,
and completion allowance. All profiles are specified before choosing the
seed. The single weighted seed inequality pays every one of these different
demands. No favorable gap, favorable residue class, or independent shared
supply is assumed.

The source parameters common to every profile are

    degree d=6, cut expansion kappa=26/25,
    growth pool (X/8,X], width c=7/8,
    raw total-prime coefficient rho=112/125,
    .487 X < m < .492 X,       X/n^2 > u-9/8,
    target radius D=y/2200,    retained rounding f=9999/10000,
    reflected half-extent w=3/28.                         (GP3)

The complete per-gap parameters and integer stage caps are the exact input
manifest. Values discovered with floating-point optimization have no role in
the final inequalities.

## GP2. Analytic sources and exact order envelopes

DT, the separately proved target-density tradeoff, provides the exact-total
TP target construction with R=2200 from v=31/2 through v=18. Its actual even
auxiliary modulus is at most42, with maximum totient18. It uses 193/200 of
the parity seed density and the strict selected gap h<(22/21)L; the controller
entry gap g is unrelated to this target modulus h. All target repetitions are
allowed; input entries are still distinct.

For the input pool, the direct Rosser--Schoenfeld index inequalities give

    u >= 2 a v + i,       u < b(s v-1),
    a=693147/10^6, b=693148/10^6,
    i=306747/100000,       s=118027/50000.                 (GP4)

Here i<log(2av) throughout the domain. For the upper bound, apply the
original p_j<j(log j+log log j-1/2) to j=n^2+1, with n^-2<=2^-31,
and pay the full ceiling unit in E=ceil(log_2 X). The exact endpoint check
and positive derivative of the continuous majorant prove E<sv. The
before-ceiling estimate also proves u<b(sv-1). This does not differentiate
E across its jumps. The verifier checks these original source domains and
the majorant rather than importing an older order wrapper.

Both bands lie in 24<u<29. BG's actual mean and index theorems therefore
apply. S18's computed raw count on (X/8,X] gives rho X/u primes. The direct
upper index gives X<2^41<10^13. Every entry/bridge/central interval lies in
(2,X], so the actual arguments and small moduli satisfy BMOR Theorem1.9.
The full interval count in S18.5 is used, including both square-root errors.
These are imported analytic theorems with explicit source domains; a
successful finite script does not independently prove them or repeat their
published zero computations.

For a band [v0,v1], let n0=floor(2^v0), n1=floor(2^v1)+1 and set

    U=2av0+i, V=b(sv1-1), Q=U-9/8, X0=n0^2 Q.          (GP5)

These are pointwise envelopes for every actual integer n in the band.
The exact sixteenth-root inequalities establish the integer endpoints.
For both bands, d(n1+8)<=2^19, so DP's allocation depth is at most19
through every jump. Every K=floor(n/C_g) is bounded pointwise by
(1-C_g/n0)n/C_g. The certificate never transfers a smooth derivative
across a ceiling or floor boundary.

## GP3. One weighted seed selection pays all profiles

For each g, let s_g be the number of seed stages, J_g the number of
preselected bridge stages, and b_g=ceil(log_2(g/2)). Put Q_s=d(n+8).
The seed need in a single reduced lower-endpoint class is

    D_g=Q_s s_g + 2(n+1)b_g + 2Q_s J_g.                (GP6)

The final terms pay all binary-residue deletions in that class and every
bridge entry. For g>=4, BN chooses bit-dependent unit classes by CRT.
Each pair's two endpoint classes are distinct, because its bit increment
2^(j+1) lies strictly between0 and g. Therefore any fixed class contains
at most one endpoint of each pair, and the total class charge is B_r/2,
where B_r=4(n+1)b_g. This does not require the classes for different bits
to agree. For g=2, b_g=0. The seed matching consists of disjoint input pairs, so a deleted
entry destroys at most one candidate pair.

Apply SQ's weighted consecutive-prime-path argument to the full common
pool (X/8,X], with G=34 and weight w_g=1-g/36. Its sufficient condition is

    (rho/u-c/36)X-1 > 2 sum_{even g<=34} phi(g) w_g D_g. (GP7)

If every gap and reduced class had fewer than its own D_g disjoint pairs,
the weighted matching upper bound would contradict (GP7). Thus one gap
and one class meet their actual, already specified profile. Only after
that selection are that profile's residue and bridge entries reserved.
They may destroy every pair permitted by their full deletion invoice;
(GP6) still leaves Q_s s_g usable seed pairs. The sorted-seed allocation
in BN therefore applies without changing any input entry or assumed
class invariant.

Let A and B be the exact positive coefficients such that the weighted
sum on the right before its factor2 is An+B. The checker sums all17
profiles, using their own J_g and s_g. For an endpoint v it tests

    [2(An0+B)+1] /
      [n0^2 (2av+i-9/8) (rho/[b(sv-1)]-c/36)] <1.   (GP8)

The continuous logarithmic derivative is strictly negative throughout
each band. A sufficient guard, checked exactly, is

    bs/V(v0)+(c/36)bs/[rho-(c/36)V(v1)] < a.          (GP9)

Indeed 2(An+B)+1 grows no faster than n, the n^2 denominator supplies
2 log2, the positive index factor only improves decay, and the two
remaining logarithmic losses are bounded by the left side of GP9.
Using n0<=2^v at the endpoint only increases the ratio. Both endpoints
are checked as an additional control. The seed argument therefore
covers every order, not just a mesh or a single integer.

## GP4. Growth, bridges and all shared depletion

After the gap is selected, all prefix-growth primes may use any reduced
class modulo g. Only differences divisible by g are needed for the
complete grids and line residues. MC, AW and BT prove the finite
binning mechanism with r=phi(g). A candidate batch contains z_g Q_s
pairs of a common positive difference; BN sorts its midpoints and keeps
exactly Q_s pairs in a subinterval of width cX/z_g. The unused candidate
primes remain in the input pool. Every kept pair is fully charged.

For each gap set

    epsilon_g=1/[2(c+1/L_g)]-eta_g,
    mf=f alpha_g/V,
    q=d(n0+8)/X0,
    m0=rho/V-4(n0+1)b_g/X0-2q(J_g+s_g).             (GP10)

The actual stock after seed selection and j growth stages is at least
X(m0-2qj). This pays all residue and bridge deletions before growth.
The certificate verifies terminal stock at least mf X and

    epsilon_g mf^2 g >= 2 z_g q phi(g).             (GP11)

This is the complete common-batch matching invoice. No supply is reused
as if it were independent of other stages.

Each phase has its own multiplier zeta and affine intercept A_phase.
Ordinary growth has zeta=1,A_phase=1/2. An affine wheel has
zeta=1/rho_w,A_phase=1/2+C_w, with the exact periodic discrepancy
and every added prime paid by AW. BT has zeta=lambda phi(g)/(2g)
and its original interval-length hypothesis. Every wheel is coprime
to g and its screened primes are smaller than X/8.

With scale phi(g)/(eta_g mf), the phase origin is A_phase times scale.
Its entry radius is an exact integer ceiling of the greater of the
previous/new line intersection and its actual source threshold.
Subtract this new origin in full. For an integer stage cap J, after j
previous stages, the verified logarithmic growth is

    zeta eta_g g [J(m0-2qj)-qJ(J-1)] /
       [phi(g)(1+tmax)],
    tmax=zeta eta_g g rho/[phi(g)U] <=1.             (GP12)

The required logarithm is the ratio of the next shifted radius to the
current shifted radius, or V-log(L_g times shifted radius) at the end.
The checker compares these quantities with rational outward logarithms.
If the actual grid reaches X/L_g before a later scheduled threshold,
growth stops there. All later caps remain paid but no unjustified
phase invocation is made. This is CF's explicit conditional early-stop
rule, now checked separately for every gap profile.

Every gap has its own exact reflected bridge windows. Their complete
geometric progression and terminal stages cover X, with total prefix
coverage below5X/2. The checker enumerates all same-side overlaps and
both residue-band intersections before charging local depletion.
Every double-block multiplicity, floor and endpoint is paid with the
full BMOR count for that actual g. Different gap profiles are mutually
exclusive constructions; windows from unchosen profiles do not remove
entries.

## GP5. Placement, centering, and exact completion

Once a gap is fixed, PB/BN/DP/WB/RP/BR apply with that profile's actual
parameters. The graph is the same degree-six, expansion26/25 graph for
all profiles. Its original entropy inequalities and finite order gate
are rechecked at n0=floor(2^(31/2)); no older graph domain is imported
below its premise.

Write P_g=s_g+sum J_phase and K=floor(n/C_g). The reserved fraction is
bounded pointwise by

    Z_g=4(n0+1)b_g/n0^2
        +2d(1+8/n0)(P_g+J_g)/n0
        +14d(1+8/n0)/C_g.                           (GP13)

All entries and all rectangles remain disjoint. RP packs diagonal
rectangles using n>=2J_rect+1. The stronger ordinary-matching invoice
is checked in its retained form

    8d(P_g+J_g)/n0+56d/C_g+(24b_g+16)/n0 <1.       (GP14)

It also gives RF's actual-r0 regular-factor domain. Here r0 uses the
actual number of executed stages, not the cap P_g. The RF proof fills
both diagonals, tracks the signed conditional mean, reserves its
central exceptional stock, and factors the remaining support. The
completion error is at most (4+2(9b_g+6)epsilon_c,g)X.

The central interval is checked to be disjoint from every wide and
residue band. Its prime count pays the entire prefix and bridge stock,
at most2n prior diagonal choices, and all exceptional entries. The
normalized BMOR error is -(1036/125)/sqrt(X), so the lower X0 bound is
used in the correct direction. The signed mean displacement includes
both diagonal choices and the actual remaining-pool denominator.

Each profile's baseline error combines the sorted-seed allocation,
narrow common-batch allocation, prefix mean, binary residues and their
signed repairs, shared wide midpoints, bridge midpoints, and RF
completion. The input manifest gives a rational allowance beta_g.
The exact checker proves

    baseline error < beta_g KX,
    beta_g + .492 C_g/[(1-C_g/n0)2200]
                  < (999/1000)(26/25).             (GP15)

The right side is the same routing capacity as before. The original
finite controller then fixes the target residues, repairs the remaining
g-multiple discrepancies, and treats the two diagonal reservoirs
independently. Every reserved and unreserved prime appears exactly once.
The target list contains exactly n primes summing to T, and both diagonal
targets lie in the same radius. Prime line sums may repeat.

## GP6. Certificate scope and recovery

Run the standard-library verifier

    python3 problems/prime-line-sums/code/cutoff2_controller_gap_profiles.py

Its exact input manifest includes every required public proof, program
and source-input dependency. It rejects missing, empty, malformed,
extra, substituted and mismatched sources and physical ancestor symlinks.
Negative controls attack the seed invoice, complete gap cover, both band
handoffs, candidate batch, phase growth, bridge overlap geometry, central
stock and separation, allocation depth, baseline and target flow.

All rounded parameters are enclosed pointwise. Within each band the
source upper u and lower X are fixed; n-dependent deletion and centering
terms are bounded by their exact lower-order envelopes. The separate
weighted seed expression has the persistence proof GP9. These facts
cover the entire band including changes of E, e, K and every ceiling.
A check at a single huge value or a floating mesh is not being used as
an infinite-order argument.

This is an ordinary mathematical proof with exact finite arithmetic
support. The imported analytic theorems, universal graph and construction
arguments remain conventional proof obligations. Complete publication
must pin this exact revision, obtain independent nonauthor review, and
compose the upper handoffs. No statement here asserts the unresolved
orders below46341 or calls the theorem kernel checked.

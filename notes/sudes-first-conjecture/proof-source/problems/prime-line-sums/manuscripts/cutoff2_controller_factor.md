# Conditional controller from order 55,109 using regular-factor completion

Author: `/root/controller_redesign`. This additive finite-band theorem
requires independent nonauthor review at its exact scientific revision.
It changes no frozen source or public note. Its arithmetic certificate
does not prove the imported analytic theorems, the universal construction,
or the complete larger-order handoff by itself.

## CF0. Statement and parameters

For every odd integer n satisfying

                     n^4 >= 2^63,  n < 2^16,               (CF1)

the construction below, composed with the pinned parity target theorem,
arranges exactly the first n^2 odd primes once each into a square with
prime row, column and both main-diagonal sums. Prime target values may
repeat; input entries may not. The program proves

                  55108^4 < 2^63 < 55109^4,

so the first relevant order is55,109. Above the band, the separately
frozen WC controller begins at n=2^16; its BCM and MC18 handoffs and the
accepted complete311744 tail remain obligations of the root composition.
No claim of a complete55,109 theorem is made by this component alone.

Write X=p_(n^2+1), T for the exact input sum, m=T/n^2, y=T/n,
v=log_2 n, u=log X, E=ceil(log_2 X), and e=ceil(log_2 y).
The symbol e denotes the integer ceiling, not Euler's number. All
analytic logarithms are natural. The proof uses one closed envelope
63/4<=v<=16, even though its upper order endpoint is assigned to WC.

The exact common parameters are

| Parameter | Value |
|---|---:|
| graph degree d and cut constant kappa | 6,26/25 |
| allowed even seed gaps | 2 through36 |
| prefix pool | (X/8,X] |
| raw and weighted-seed density rho | 112/125 |
| retained prefix mass alpha | 4061/5000 |
| growth eta | 241709/500000 |
| initial bridge split L | 12 |
| K | floor(n/671) |
| candidate multiplier z | 8 |
| common-prefix midpoint width after selection | (7/8)X/8 |
| bin halfwidth delta and count N | 1/308,33 |
| total wide extent w=N delta | 3/28 |
| reflected stock denominator | 1515 |
| minimum bridge interval width | X/280 |
| target tolerance D | y/1050 |
| retained floor fraction f | 9999/10000 |
| central completion halfwidth epsilon_c | 1/25 |

The manifest gives a fixed seed count and an explicit finite phase
list for every possible gap. Every phase cap is an integer. Its source
wheel factors, analytic BT parameter where used, and the exact
phase-boundary rules below are part of the certificate.

## CF1. Re-specialize the bounded sources below the old order wrapper

The analytic imports are unchanged: RS62 Theorem3(3.11)--(3.12),
printed p69; BMOR Theorem1.9 and definition(1.18), printed434--435;
the primitive-correct low-zero interface in S18.23--S18.24; and the
separately reviewed MV73 BT theorem used only in the corresponding
prefix phases. The fixed-q4 mean and prime-index factor of BG1--BG4
hold for every24<=u<=29, independently of the old completion wrapper's
order restriction. In particular

       .487X<m<.492X,             X/n^2>u-9/8.             (CF2)

S18.15 similarly supplies total raw stock greater than.896X/u on
(X/8,X] throughout24<=u<=29. We prove that scale range directly here;
we do not invoke any literal n>=2^16 premise below its domain.

Put a=693147/10^6, b=693148/10^6, s=11781/5000 and
eta_0=2^-31. The RS lower index gives

    u>2av+log(2av)>U(v):=2av+308347/100000.                (CF3)

The last constant is certified below log(2a*63/4). For the upper
index use z(v)=2bv+eta_0 and W(v)=z(v)+log z(v)-1/2.
As n^-2<=eta_0 and n^2+1>=20, RS(3.11) gives

    log_2 X < 2v+[eta_0+log W(v)]/a.

The exact endpoint and derivative checks prove

    2v+1+[eta_0+log W(v)]/a < s v       (v>=63/4).

Indeed W>z and W'/W<1/v+1/(2bv^2), while
s-2-[1/v+1/(2bv^2)]/a is positive at63/4 and increases afterwards.
Consequently, retaining the whole ceiling unit before specializing,

                   E<s v,       u<V(v):=b(sv-1).         (CF4)

Thus U(63/4)>24 and V(16)<29. The upper index at n=2^18,
already checked in S18, also bounds every actual entry here by
X<2^41<10^13. The full BMOR interval formulas S18.5 apply at every
bin, bridge and central completion endpoint. All their actual arguments
are checked to lie in(1,X]. Modulus2 uses the sum of both reduced
classes modulo4; no prime-power substitution is used in this bounded
count. Every selected gap is at most36 and hence inside q<=100. No
condition g<=E is assumed.

For the target scales, use the same conservative e<=59, L_t<=42,
even auxiliary q<=42 and phi(q)<=18 as S18.7. They depend only on
the upper order n<=2^18, not its old lower endpoint. At v=63/4,
CF2 and the lower prime index give

    log(3y/4)>1741/50=34.82,
    log(15y/16)>701/20=35.05.                            (CF5)

These bounds increase throughout the band. Reapply equation(S18.24)
at z=1741/50 with exactly Q42,Phi18,r16,tau=21/10^7 and
low-zero cap28911/500. Reapply its fixed-q2 seed formula at
z_s=701/20 with H=3*10^10,r20,tau=202/10^12 and cap941/10.
The exact checker verifies all original smoothing, height, zero-count,
proper-prime-power and primitive/imprimitive normalization hypotheses,
and the numerical bounds

       8(1050+1)*error_target<1,
       400*1050*error_seed<1.                            (CF6)

Thus the full target progression intervals receive at least
H/[2phi(q)log(2y)] primes, and the parity seed interval receives at
least.99(D/2)/log(2y), for D=y/1050. The factors in CF6 pay both
endpoints uniformly; the seed uses its narrower actual interval.

The finite list-size requirement is at most
3*42*(4*59+6)+7=30499<55108<n. The checker also verifies
D>=8*42^2, D<=y/4 and the dense seed's lower L_t domain.
These are direct finite hypotheses of the parity/dense-target theorem.
They supply exact-total row and column prime lists and both diagonal
targets within D of y. Those targets are chosen before residue repair.
Repeated target primes are allowed.

## CF2. The actual seed, entry and position invoices

Let phi=phi(g), b_g=ceil(log_2(g/2)) and Q_s=d(n+8).
Let s_g be the manifest's seed count and P_g the sum of that count
and all its phase caps. The weighted seed condition is SQ's original
path argument on the same raw pool, with span at most7X/8:

    [rho/u-(7/8)/38]X-1
     >2 sum_(even g<=36) phi(g)(1-g/38)
                         [Q_s s_g+B_r/2+2Q_s J_b],
           B_r=4(n+1)b_g.                               (CF7)

The half-residue budget is used only for this fixed-class seed matching.
The pooled growth stock pays the complete B_r. Every actual bridge
entry is paid; no analytic supply is independent of the others.

Bridge radii follow the same exact geometric recurrence as BCM/WC,
now with epsilon_b=L/280. The checker recomputes every lower and upper
interval, every mutual overlap, and every residue-window intersection.
It proves the ordinary final prefix coverage at least X and retains the
amplified diagonal coverage. Differences on distinct diagonal copies
need not be identical; each pays the same guaranteed lower bound.

Write s_e and s_i for twice the full BMOR main-term fractions retained
in the ordinary bins and bridge intervals. The exact formulas of BCM7--8
are used with the actual phi(g), X lower bound and natural logarithm
upper bound. All deletion and floor ratios divide by the corresponding
supply factor, and double-pair ratios divide by its square. The
aggregate reflected-bin condition retains the prime-index factor
X/n^2>u-9/8; it is not replaced by X>=n^2. Every required floor
argument exceeds10000, so f=9999/10000 is valid in every supply.

The complete reservation count remains

                  B=B_r+2Q_s(P_g+J_b+7K).                (CF8)

The seven-wide-stage identity7(1/2-2w)=2 is unchanged. RP packs the
diagonal rectangles with its exact2J+1 condition. The stronger
ordinary matching condition

     8d(P_g+J_b)/n+56d/671+(24b_g+16)/n<1               (CF9)

is still paid. All placements preserve disjoint entry positions and
independence of both diagonal controls.

## CF3. Affine-wheel and BT phases with explicit origin changes

Use U_0=U(63/4), V_1=V(16), n_0=55108,
Q_0=U_0-9/8, X_0=n_0^2 Q_0 and q_0=d(n_0+8)/X_0.
Put

    m_f=f alpha/V_1,
    m_0=rho/V_1-4(n_0+1)b_g/X_0-2q_0(J_b+s_g).         (CF10)

These are pointwise lower stock densities relative to the actual X.
The actual Q_s/X is at most q_0. The common-candidate gate is

                  epsilon m_f^2 g >= 2z q_0 phi,
                 epsilon=1/[2(7/8+1/L)]-eta.            (CF11)

It pays all8Q_s candidates. BN retains Q_s pairs in one midpoint
subinterval of width(7/8)X/8. Unretained candidates stay unused;
every actual kept stage consumes exactly2Q_s entries.

An ordinary phase has multiplier zeta=1 and normalized origin A=1/2.
An AW wheel phase has zeta=1/rho_W and A=1/2+C_W. Each wheel is
defined by an exact small-prime subset and an ordered extension list;
AW1 supplies a rational discrepancy bound for all extensions. All
actual primes exceed43, and every wheel is coprime to g. A BT phase
uses A=1/2, zeta=lambda phi/(2g), and the exact source threshold
x>=1/2+exp(lambda)/zeta, where x=eta m_f R/phi.

For adjacent phases with strictly increasing multipliers, their linear
growth bounds meet at

    x_cross=(zeta_new A_new-zeta_old A_old)
                                      /(zeta_new-zeta_old).

The new phase's start is the ceiling of phi/(eta m_f) times the
maximum of this crossing and its own source threshold. The first start
is the actual seed radius s_g g. All boundary ceilings and all
exponentials are evaluated by outward rational enclosures. These are
fixed actual-radius bounds, not shifted-radius bounds.

For a phase starting at R_0, its own origin is
R_*=A phi/(eta m_f). The checker explicitly verifies R_0>R_*
and the required BT threshold when applicable. It subtracts this new
origin even when the preceding phase had a different one. At J_prev
earlier growth stages, use the lower stock density
m_cur=m_0-2q_0 J_prev. Its positive terminal remainder is checked
after the phase cap J. The pointwise upper multiplier is

                  t_max=zeta eta g rho/(phi U_0)<=1.

The certified logarithmic growth is

     zeta eta g[J m_cur-q_0 J(J-1)]/[phi(1+t_max)].       (CF12)

For an intermediate target R_1 it is at least the outward upper bound
of log[(R_1-R_*)/(R_0-R_*)]. For the final phase it exceeds
V_1-log[L(R_0-R_*)], a conservative bound obtained by dropping the
positive origin from the target's numerator. These are direct finite
product inequalities, with no implicit root or floating optimization in
the inputs.

Each phase runs only while the actual complete prefix radius is below
X/L. If it reaches that value before a listed phase boundary, stop the
growth prefix immediately. A later listed phase whose starting bound
would already exceed X/L is therefore never needed at that order.
Conditional on a phase being needed, all its count hypotheses hold.
Paying every listed stage cap is conservative for the entry and seed
budgets. Both the complete grid and every repeated diagonal stage are
preserved by AW/MC/BT.

## CF4. Replace quantile completion by RF

After reservations and the diagonal-first completion, RF3 uses the
actual r_0=2d(P_0+J_b+7K), not P_g. The residual degrees lie in
[n-r_0-(6b_g+4),n-r_0]. Equation CF9 implies
r_0+6b_g+4<n/4, precisely RF5. Thus the dense regular factor needs
no stronger position hypothesis. Its exceptional degree is
t=9b_g+6.

Let Z be the full upper reservation fraction, and write b_p,b_b,b_w,b_r
for its four normalized entry budgets. With beta=.513,
beta_b=epsilon_b/4+.013 and epsilon_c=1/25, the checker proves

    sigma=[beta b_p+beta_b b_b+delta(b_w+b_r)]/(1-Z)
              +3/[2(n_0^2(1-Z)-2n_0)],
    sigma+epsilon_c<1/4-w,

    {V_1[b_p+b_b+(t+2)/n_0]/Q_0}
              < 2epsilon_c-(1036/125)/sqrt(X_0).         (CF13)

Every square root is rounded in the safe direction. The final right
side is positive, and the central interval is inside(2,X]. The first
inequality separates that interval from all wide and residue entries;
the second pays all prefix, bridge, preassigned and exceptional values.
It is exactly RF8--RF11 divided by X, not an assumption of disjoint
analytic stocks. The completed square consequently has uniform
completion error at most

                      [4+2(9b_g+6)/25]X.                 (CF14)

The other centering invoices are unchanged: BN sorted seed assignment,
DP simultaneous narrow-prefix assignment, PB's signed global mean
cancellation, BR's signed binary repair, WB's shared wide-block
allocation, and the full bridge midpoint cost. The integer allocation
depth is19 throughout the band since6(n+8)<2^19. There is no quantile
depth or old n>=2^16 completion premise in CF14.

The exact table bounds the total baseline error by its selected allowance
times KX and adds the entire target tolerance .492*671/(f_K*1050).
The sum is below.999 kappa, with the unchanged integer-flow slack
KX>=1000g. Hence the fixed rows, columns and both diagonals can reach
their prescribed prime targets.

For orientation, the exact certificate gives the following upward
decimal summaries. The comparisons themselves use fractions, not these
displayed numbers.

| Quantity | Uniform upper bound |
|---|---:|
| weighted seed demand / supply | .977994 |
| common candidate batch demand / supply | .937423 |
| pooled prefix depletion / available margin | .919718 |
| aggregate reflected-bin demand / supply | .977322 |
| central completion demand / supply | .965716 |
| baseline error / KX | .703830 |
| selected baseline allowance | .71 |
| complete target tolerance / KX | .318287 |
| selected allowance plus target tolerance | 1.028287 |
| available normalized routing capacity | 1.03896 |

The maximum prefix cap is327 stages. RF's completion allowance is at
most202X/25=8.08X, with the exact gap-dependent smaller allowances
retained in the table. Every phase-growth inequality is positive; the
largest required/provided growth ratio is less than.999783.

## CF5. Whole-band coverage and verification boundary

All chosen phase counts and seed counts are fixed for the whole band.
The smooth scale bounds CF3--CF4 apply before any ceiling operation.
Each integer floor uses an explicit envelope, including K>=n/671-1,
the integer stock floors and every phase-boundary ceiling. Entry,
matching, growth and centering expressions use pointwise monotone
upper envelopes in n_0,U_0,V_1, so no derivative is transferred across
an E,e,K or depth jump.

The weighted seed ratio is checked separately. Its numerator is an
explicit positive affine function A_0 n+B_0. Dividing by
n^2 Q(v)[rho/V(v)-(7/8)/38] gives the actual sufficient ratio.
The checker proves the denominator positive and its logarithmic
decrease criterion on the full real band, then checks the integer
endpoint enclosures. This controls every possible selected gap and
residue class jointly, including all deletion budgets.

The verifier uses exact fractions and outward logarithm, exponential
and square-root bounds. Its manifest enforces the entire required
public source closure and rejects missing, empty, malformed, extra,
mismatched or substituted files. Negative controls reach the stock,
phase, central-completion, target and coverage conditions. The root
composition must bind this exact revision, its independent analytic,
finite and arithmetic reviews, and the larger-order handoffs before
announcing a complete all-odd-tail numerical theorem.

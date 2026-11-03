# A controller beginning at odd order 27,555

Author: `/root/controller_redesign`. This additive conditional controller
preserves NC and every frozen predecessor. Its exact scientific revision
requires independent nonauthor review. Root's complete infinite-tail
composition and publication are separate; an arithmetic PASS is not an
end-to-end formal theorem.

## EW1. Scope, scales, and exact order cover

Use exactly the first n^2 odd primes, each once, for odd n. Write
X=p_(n^2+1), T for their total, m=T/n^2, y=T/n, E=ceil(log_2 X),
e=ceil(log_2 y), and v=log_2 n. Natural logarithms are used in every
analytic estimate. The controller covers

                     n^4>=2^59,       n^8<2^121.           (EW1)

Since27554^4<2^59<27555^4 and35733^8<2^121<35734^8, its first odd
order is27555 and its final odd order is35733. At35735 the frozen NC
controller begins. NC and the subsequent handoffs to the accepted
upper tail belong to root's separately reviewed complete composition.

The three contiguous real-order bands are

    [59/4,119/8],      [119/8,15],       [15,121/8].         (EW2)

The input manifest fixes every parameter and recipe for all fifteen
possible even seed gaps2<=g<=30 in each band. There is no favorable
preselected gap or omitted rounding case.

TB proves the actual-scale interface

    .486X<m<.492X,        X/n^2>log X-9/8,
                      23<log X<29,                        (EW3)

and exact-total prime targets with D=y/R for R=1920,2100,2300 in the
respective bands. Its actual (e,L) cases and original source domains
are rechecked in the certificate. The target modulus and the input
seed gap g are independent. Repeated target primes are allowed.
Rows and columns may use the same exact-total list; both diagonals
independently choose a permitted prime target. No input prime is repeated.

For each band take n_0=floor(2^v0), n_1=floor(2^v1)+1. Let U,V be
TB's outward rational lower and upper bounds on log X. Put

    Q_x=U-9/8, X_0=n_0^2 Q_x, q=d(n_0+8)/X_0, d=6.        (EW4)

The direct RS upper estimate at j=n^2+1 supplies an upper W for X/n^2
throughout the band. A rational upper Xbar>=exp(V) bounds X itself.
The exact value of E need not be inserted into these estimates; its
jumps cannot invalidate pointwise inequalities. TB separately checks
all actual E and e cases.

PD's depth is at most18, since6n_1<=2^18 in each band. For a profile's
integer C, K=floor(n/C) has the pointwise lower bound
n(1-C/n_0)/C. Every use of a floor is paid this way; no smooth argument
crosses a rounding discontinuity.

## EW2. Fixed gap demands, cyclic residues, and retained seeds

Use the full-pool FS weighted matching on all prescribed primes>30.
For each gap, let s_g be its retained seed-stage count, t_g its narrowest
extra-group allowance, and J_g its bridge-stage count. Set Q_s=6(n+8).
The class-separation lemma CS and cyclic layout CY give the only seed
matching destruction charges

    loss_g=2Q_s J_g for g=2,
    loss_g=2(n+2)b_g for g=4 or6,
    loss_g=0 for g>=8,             b_g=ceil(log_2(g/2)).       (EW5)

The single joint selection gate is

    n^2-pi(30)-X/32
      >2 sum_g phi(g)(1-g/32)[Q_s(s_g+t_g-1)+loss_g].         (EW6)

The manifest pays every gap's own demand before a label is selected.
Each profile contributes a fixed positive linear expression in n to
the right-hand side. The verifier uses the band's one constant upper bound W for X/n^2;
the resulting positive 1/n and 1/n^2 terms decrease throughout the
whole band, so its lower-endpoint check covers every order. The numerator's constant term includes the new CY closing pairs.

After selecting a candidate matching label, reserve the residue controls
and bridges, then retain the s_g narrowest groups from exactly
Q_s(s_g+t_g-1) surviving seed pairs, as in NS. Only2Q_s s_g entries are
kept. Every unused candidate remains in the input pool.

CY closes the two ordinary residue paths into balanced permutation
cycles with fixed closing pairs. Its full count is B_r=4(n+2)b_g.
Every ordinary line has exactly4b_g ordinary residue entries, and both
diagonal initial states are balanced as specified in CY. The subsequent
BR signed repair is still paid in full. Neither the pooled global count
nor any interval invoice uses the seed-only CS saving.

## EW3. Move the wide reservation before growth

The order of selecting values is essential:

1. Select the candidate seed matching and label.
2. Reserve all cyclic residue controls and all bridge blocks.
3. Select and retain the narrowest seed groups.
4. Reserve ALL7K wide stages through WB's sequential double blocks.
5. Grow the common prefixes from the remaining input primes>43.

This changes selection order, not the order in which differences are
appended to a completed correction reservoir. Once growth reaches X/L,
append the stored bridges to obtain coverage X; append the stored wide
pairs afterward exactly as before. Every wide difference is a positive
g-multiple below X, so completeness and7(1/2-2w)=2 capacity remain valid.
Here w=3/28 and the same seven wide stages per K are used.

During step4 the only deleted entries are the residue family, bridge
family, retained seed entries, and earlier wide entries. Consequently
RBC's same pair-count argument is applied with the selection budget

             B_ref=B_r+B_b+2Q_s s_g+B_w,
             B_b=2Q_s J_g,       B_w=14Q_s K.              (EW7)

It is unnecessary to subtract FUTURE growth entries at this selection
stage. This is a re-specialization of the actual post-deletion counting
proof: N phi(g)W_bin-B_ref must remain positive and its square must
exceed NX. Every overlapping bin/class supply still refers to the same
prime set and the same full earlier-deletion budget. No independence or
shared-prime reuse is assumed.

Conversely step5 pays every wide entry in full. With all input primes>43
there are exactly n^2-13 candidates before deletions. Put c=1. A uniform
normalized post-seed/post-wide lower stock is

    a_0=(1-13/n_0^2)/W,
    m_0=a_0-[B_r+B_b+2Q_s s_g+B_w]/X,                   (EW8)

where the subtracted ratio uses the explicit safe band upper envelopes.
The verifier never retains the old width7/8 or raw-density coefficient
from a different pool. Only internal supply subsets have changed; the
complete prescribed input pool remains unchanged.

All final geometric, completion and mean invoices still use

                  B=B_r+B_b+B_p+B_w,
                  B_p=2Q_s P_g.                         (EW9)

Only the selection-specific RBC budget in EW7 omits future growth.
The global prefix budget includes B_w, and the central prime stock
still pays every possible seed, growth and bridge entry.

## EW4. Direct finite growth instead of a padded logarithmic cap

Let m_f=(9999/10000)alpha_g/V and m_j=m_0-2qj. Set

    epsilon_g=1/[2(1+1/L_g)]-eta_g.

The certificate checks m_j>=m_f>0 through the entire declared cap and

                 epsilon_g m_f^2 g>=2z_g q phi(g).         (EW10)

Each listed DR step checks its original ordinary, wheel or
Brun--Titchmarsh short-neighbor bound and a positive cutoff D_j<=R_j.
It then updates the integer lower grid radius by

                   R_(j+1)=R_j+g ceil(D_j/g).             (EW11)

All phase gains, positive affine terms, integer lattice gains and
overshoots are retained. Wheels are screened against the actual primes>43;
every BT interval-length hypothesis is checked with a rational upper
exp(lambda). The finite recipe reaches Xbar/L_g. At an earlier actual
crossing of X/L_g the construction stops, while the declared budget is
still charged. The initial seed count and every recipe mode are exact
manifest data, not a floating quadratic root.

Every common step supplies the full z_g Q_s candidate matching, keeps
only Q_s pairs within midpoint width X/z_g, and leaves all other
candidates unused. PD supplies the all-line growth-allocation bound

              (X/z_g)[8 ceil(log_2(6n))+2+3/n].           (EW12)

NS's independent narrowest-seed error is added with its actual t_g.
The original stage means are preserved. Thus no O(P_g) midpoint bias
is hidden by changing the selected populations. The disjoint seed,
growth, bridge and wide populations may each be allocated to meet its
own simultaneous all-line bound; these choices can be made separately
and their resulting errors added. No assumption that overlapping prime
supplies are independent is used.

## EW5. All-line centering and completion

BB chooses every bridge pair as part of a sequential equal-gap double
block and uses one shared stage population for ordinary and diagonal
slots. All previous window overlaps, residue intersections, source
endpoints and local deletion budgets are unchanged. Its completed-line
error is

    [u_b+2 beta_b+2d beta_b J_g H/(n^2-B)]X,
    u_b=(epsilon_bridge/2)sqrt((3dJ_g+4)log(8n+8)),
    beta_b=|m/X-1/2|+epsilon_bridge/4,
                         H=(3b_g+8)n.                   (EW13)

The same CY coefficient H is used for the shared growth and wide mean
terms. Their separate total-residue correction delta*n*B_r/(n^2-B)
remains. CY's exact initial residue charge and BR's full signed modular
repair charge are both added. The flow correction uses the actual
reservoir centers and the same nearest-grid rounding allowance.

CY keeps the actual main degree r_0=2d(P_0+J_g+7K) unchanged in
the shared mean cancellation. Only for completion it defines
rho=r_0+4b_g. Its center trim and RF factor leave maximum
exceptional degree4 and at most3n+1
exceptional cells. Therefore the completion error is

                       [4+(7+1/n)eps_c]X.               (EW14)

The central count must exceed B_p+B_b+5n+1. Its interval is centered at
the actual unused mean, with both signed mean-conditioning costs and
separation from every residue/wide interval explicitly checked. The
complete B and actual executed P_0, rather than an assumed equal cap,
remain the combinatorial quantities. Numerical caps only majorize them.

The ordinary placement condition is

    8d(P_g+J_g)/n+56d/C_g+(16b_g+16)/n<1.                (EW15)

It implies CY's actual-degree factor domain; RP separately retains
all disjoint rectangles, both diagonals, and the center. Every target
and integral-flow tolerance is charged jointly to the displayed exact
baseline allowance. The manifest records which inequality is largest
for each possible gap; no favorable branch is discarded.

## EW6. Re-specialize the graph at the actual order

Use degree6 and cut expansion26/25. Recheck PB's small-cut and entropy
conditions, with the same t_0=1/256. The actual worst entropy endpoint
is below -0.0028969613, so epsilon_graph=1/350 is legitimate. This is
stronger than the previously inherited1/400 sufficient bound. The exact
base comparison

    (1/350)n_0 > [6(v_0+2)+3]log2

holds at v_0=59/4, n_0=27554. Its derivative margin is positive for all
larger n. Thus the whole tail graph source is rederived from its finite
numerical hypotheses, not invoked below a predecessor's literal order
premise. The graph existence proof remains ordinary mathematics.

## EW7. Certificate and review boundary

The exact checker binds the complete public dependency set, validates
all three adjacent real-order bands, and checks each of the fifteen gap
profiles in every band. It covers all E,e,K changes by actual ceiling
partitions or pointwise integer envelopes. It checks every DR stage,
source threshold, complete candidate quota, selector-specific and final
entry budget, bridge overlap, target case and completion invoice.

Required files, nonempty maps, canonical hashes and parameter types are
strict. Missing, empty, extra, substituted and malformed maps and files,
symlinked ancestors, and numerical gate mutations are negative controls.
The public checker requires no inaccessible private artifacts.

The certificate is not a proof of BMOR, RS or Brun--Titchmarsh, and it
is not kernel verification. The finite mechanisms, conventional proofs,
independent exact-revision reviews, root's complete all-odd composition,
and eventual public-note update have distinct responsibilities.

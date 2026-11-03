# Prime-sum arrays in every fixed cyclotomic field

## Contents

- [Frozen problem and canonical pool](PROBLEM.md)
- [Every fixed conductor: theorem CYC](manuscripts/general_composition.md)
- [Exact energy normalization and general local arithmetic](manuscripts/general_normalization_local.md)
- [General principal-prime inputs and representative geometry](manuscripts/general_analytic.md)
- [Physical control in every fixed arithmetic rank](manuscripts/general_controller.md)
- [Order-three cube obstruction at every conductor 3^a, and the K9 repair](manuscripts/ternary_cube_obstruction.md)
- [Eventual theorem and composition](manuscripts/composition.md)
- [Full units, canonical geometry and local obstructions](manuscripts/normalization_local.md)
- [Precise prime inputs and actual centered pairs](manuscripts/analytic.md)
- [Rank-four controller and improved integer tensor rounding](manuscripts/controller.md)
- [Sources and immutable foundations](REFERENCES.md)
- [Open obligations and relationships](OPEN_PROBLEMS.md)
- [Exact implementation and checking](code/README.md)
- [Finite physical and local controls](manuscripts/finite_controls.md)
- [Recovery, reviews, evidence and coordinator handoff](RECOVERY.md)

## Current status

The new conventional author proof [CYC](manuscripts/general_composition.md)
covers every fixed nontrivial cyclotomic field, without a degree cap or a
class-number-one assumption. Every sufficiently large order works unless
the reduced conductor is a power of two; in those fields every sufficiently
large odd order works and every even order at least two is impossible.
Both squares and all full signed cube lines are included. The thresholds
are ineffective and depend on the fixed field.

The new fields use a precisely defined minimum trace-energy associate, with
exact sector and coefficient ties. A finite trace ellipsoid compares all
associates, including every possible missing unit-index coset. The general
energy domain has the required regularity and centered interior chords.
Only principal prime ideals contribute elements, with density factor 1/h_K;
every principal higher-residue-degree class remains in the exact prefix.
The original quartic balanced-log pools remain unchanged. The rational
field retaining 2 is separately obstructed, with the explicit odd-prime repair.

New scientific source: `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b`.
Three nonauthor internal component reviews found no blocking defect in their
disclosed scopes; see the [review manifest](RECOVERY.md#actual-independent-reviews).
Eight new arrays in conductors 7,9,15,16 pass the independent exact energy
checker, including full cubes in all four fields and even squares in 7,9,15.
It rejects 116 corrupted certificates and passes 50 common arithmetic
controls. Unit subgroups in eight fields through degree 22 and a
nonprincipal-prime K23 control are separately certified.

Supplemental source: `3fe1dfbcec2e2c500ac974081f0f5eda8b9e344d`.
[TC3](manuscripts/ternary_cube_obstruction.md) proves that order-three full
cubes are impossible at every conductor 3^a. Its proof combines a full-unit
sector argument with an exact 31-node non-two-colorability certificate,
replayed by a separately authored checker. In the unchanged K9 model,
the next order has a certified full cube using exactly the first 64 entries
and all 76 required lines. The failed order-three search is not used as
evidence for the obstruction, and the order-four example is not asserted
for every power of three.

## Retained quartic checkpoint

CPA4 has a complete conventional author proof for the frozen pools: every
sufficiently large order for conductors 5 and 12 and every sufficiently large
odd order for conductor 8 admit squares and full signed-line cubes. Every even
conductor-8 order at least two is impossible. The theorem retains all input
classes except the explicitly omitted ramified ones, including higher residue
degrees and incomplete norm ties. Its thresholds are ineffective.

The proof uses opposite-second-phase endpoints centered at the actual mean,
four-direction physical zonotopes with reserved exact prefixes, and a new
linear rather than quadratic integer tensor-rounding loss. The manuscript
states every dependency on established analytic and imported geometric sources.
Three independent internal reviews at scientific source
`6f8524253c32db096e38715fd69e880e0fa85fdd` found no blocking defect in
their disclosed scopes. Authorship exclusions and exact digest bindings are in
the [analytic/local](reviews/analytic-local-review.md),
[normalization/controller](reviews/normalization-controller-review.md), and
[composition](reviews/composition-review.md) records. They are not formal
GitHub approvals, external refereeing, or kernel verification.

Nine nontrivial exact arrays are independently certified, including full
order-three cubes in all three fields, an even fifth-root square of order four,
and a twelfth-root square of order six. Finite certificates do not establish
the eventual theorem.

Owner: /root. Workspace: [PR85](https://github.com/Mira-Cult/math-wip/pull/85).
State: completed fixed-conductor research and internal review checkpoint.
The coordinator retains integration, including the successful fleet-run gate.
No permanent claim identifiers are allocated.

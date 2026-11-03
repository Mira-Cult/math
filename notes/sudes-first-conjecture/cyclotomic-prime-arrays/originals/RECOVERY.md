# Recovery, verification, and coordinator handoff

PR/workspace owner: `/root`. Integration: coordinator.
Workspace: [PR85](https://github.com/Mira-Cult/math-wip/pull/85).
Branch: `research/cyclotomic-prime-arrays-20261102`.
State: completed conventional research checkpoint with independent internal
reviews; awaiting the coordinator's integration decision and successful fleet CI.
Only `problems/cyclotomic-prime-arrays/` changes. No permanent claim IDs were
allocated, and no other active lane, public manuscript, workflow, or repository
permission was modified.

## Strongest justified result

The [canonical composition, CYC](manuscripts/general_composition.md), proves
the prescribed square and full signed-cube theorem for **every fixed
nontrivial cyclotomic field**, with no degree cap and no class-number-one
assumption. Reduce m to c=m/2 when m is 2 modulo 4, and otherwise c=m.
Every sufficiently large n works when c is not a power of two; every
sufficiently large odd n works when c is a power of two, and every even
n>=2 is impossible in that case. Squares include all 2n+2 lines; cubes
include all 3n^2+6n+4 full signed-coordinate lines. The entries are exactly
the first n^D canonical elements, without later rescaling or selection.

The original balanced-log pools at c=5,8,12 are retained under the unchanged
[CPA4](manuscripts/composition.md) proof. New fields use minimum full
Minkowski trace energy over all unit associates, then the exact first sector
and coefficient-lexicographic tie. Only principal unramified prime ideals
contribute; every principal higher-residue-degree class and partial norm tie
is retained. The rational field's pool retaining 2 is separately impossible
for every n>=2. Its explicit minimal repair omits 2 at the outset and recovers
the initial odd-prime model.

The new [TC3 supplement](manuscripts/ternary_cube_obstruction.md) proves an
order-three full-cube obstruction at every conductor 3^a. A full-unit sector
argument excludes every exceptional ramified-prime associate, and a 31-node
exact certificate proves non-two-colorability of the required line family.
In the unchanged K9 energy model, the next order is certified positively:
the first 64 entries admit a cube with all 76 required sums prime. This
finite next-order repair is asserted for K9 only.

No additional unresolved mathematical premise is retained in CYC beyond
the explicitly cited established analytic theorems and pinned geometric
imports. Its threshold is ineffective and field-dependent. No uniform
growing-conductor claim, numerical cutoff, efficient full construction,
equivalence with another normalization, or classification of all finite
exceptions is asserted. Conventional proof, internal nonauthor review,
exact finite certificates, repository integrity, external refereeing,
kernel verification, and integration are distinct statuses.

## Immutable source manifest

| Role | Exact commit |
|---|---|
| Base main | `59e00a03e48e71c79a5c1be2cdba66d593cf42a0` |
| Opening definitions and owned workspace | `6e07af5fa2b519ab7310cb41c3f5468db9ea6ef9` |
| Quartic proof, nine arrays, independent checker, tensor control | `6f8524253c32db096e38715fd69e880e0fa85fdd` |
| Quartic reviews plus physical/local fixture source | `e926c54566643ce57126ac9c676d836652f4fddc` |
| Completed quartic delivery | `ec0ce071f2fbaa965396ded9a0438ec1248a772c` |
| Fixed-conductor canonical definitions | `a7f841cf1dba596477ffc360e20fef273a14d729` |
| General scientific proof, first seven energy arrays, four programs, unit data | `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b` |
| Three general reviews, ternary obstruction, independent replay, K9 cube4 | `3fe1dfbcec2e2c500ac974081f0f5eda8b9e344d` |
| Quadratic scientific foundation | `e6e581efb9b676a7d5bc88b91c01571b087ed5da` |
| Quadratic delivery | `cbb061c575d201252487327771bac75659e6d9d7` |
| Public foundation, Mira-Cult/math | `d86405ccea875963fd66e5cb8ed5b64b016c88d8` |
| Ordinary signed geometry | `a2445962ec6e06b2a893980fb7a183057eb9bcee` |
| Scalar square support | `c2118dfad1aeb660d66308dc6a94d6c959f5010c` |

The current delivery adds the supplemental review and navigation after these
immutable sources. Its full SHA is maintained in the PR description, avoiding
a self-referential commit claim. Both sets of scientific manuscripts remain
byte-identical to their reviewed sources. The general source's exact hashes:

| Manuscript | SHA-256 |
|---|---|
| `general_normalization_local.md` | `7d21da0fe1d2fcd50ba708c4b555c3e5a12f01c349661e5626fb1a928538e160` |
| `general_analytic.md` | `31da5bf826935c6c08fd3f98c2cc1246a4422ef226ef378354e0c09c232b74d9` |
| `general_controller.md` | `233027e3650aee504735a197ddb02d24246d0823ee4551eb80baef68a53ab1bd` |
| `general_composition.md` | `53cbd81439c3584b4bb18f390747a6f837f99f646af9aa725e9264ef2eaa2acd` |
| `ternary_cube_obstruction.md` | `3e9f58ec0d8c8bf109d63494550b1360aa1119d024f33b11121e3e61abc02ecf` |

Retained quartic scientific hashes:

| Manuscript | SHA-256 |
|---|---|
| `normalization_local.md` | `e7c4a406da14483b34f451b4fd67e5d589d79a95816a2451781505377437927b` |
| `analytic.md` | `5dbe0b8a5f485870274da96b3f80f9d5469174ece1bdb9b5fc384903813724b8` |
| `controller.md` | `30904f8f03c150e029662d33f9dfca7fef6babc223d3d972f45883b79e04a8c3` |
| `composition.md` | `9b224ea217b03a1b6e7ead46b47edcf4b62a1fcad0ffc1baa4a94a70c01ee636` |

The public foundation's source-map.json explicitly binds its editorial
presentation to the listed quadratic scientific source. The latter's complete
analytic, local, controller, and architecture manuscripts were the mathematical
imports; their proofs were read rather than inferred from a public summary.

## Actual independent reviews

Continuation reviews:

| Reviewer | Scope and exclusion | Exact reviewed source | Record |
|---|---|---|---|
| `/root/controller` | General normalization/local, analytic and composition, producer and unit certificates; excludes own controller and energy checker | `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b` | [general analytic/local review](reviews/general-analytic-local-review.md) |
| `/root/analytic` | Exact normalization/local, general controller, composition and finite code; excludes own analytic manuscript and disclosed shared geometry | `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b` | [general normalization/controller review](reviews/general-normalization-controller-review.md) |
| `/root/normalization` | General analytic/controller, final composition, energy producer and independent checker; excludes own normalization/unit utility and disclosed shared geometry | `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b` | [general composition review](reviews/general-composition-review.md) |
| `/root/controller` | TC1--TC3, all three combinatorial programs, proof tree and new K9 certificate; excludes own earlier energy checker from independent acceptance | `3fe1dfbcec2e2c500ac974081f0f5eda8b9e344d` | [ternary supplement review](reviews/ternary-obstruction-review.md) |

Retained quartic reviews:

| Reviewer | Scope | Exact reviewed source | Record |
|---|---|---|---|
| `/root/controller` | Analytic inputs, normalization/local arithmetic and interface composition; excludes own physical manuscript and tensor code | `6f8524253c32db096e38715fd69e880e0fa85fdd` | [analytic/local review](reviews/analytic-local-review.md) |
| `/root/analytic` | Full units, local exception proof, rank-four controller, finite producer/checker and tensor replay; excludes own analytic/centroid interfaces | `6f8524253c32db096e38715fd69e880e0fa85fdd` | [normalization/controller review](reviews/normalization-controller-review.md) |
| `/root/normalization` | Analytic/controller and end-to-end composition; excludes own normalization and checker, and discloses shared geometric observation | `6f8524253c32db096e38715fd69e880e0fa85fdd` | [composition review](reviews/composition-review.md) |
| `/root/analytic` | Separate actual four-direction cuboids, cumulative local ledger, finite obstruction proof, independent array reconstruction | `e926c54566643ce57126ac9c676d836652f4fddc` | [physical/local controls review](reviews/physical-local-controls-review.md) |

No blocking defect was found in those disclosed scopes. Each record binds the
actual bytes with hashes and identifies authorship exclusions. Three distinct
internal reviewer agents performed these reviews; repeated rows are additional
scopes by those same agents, not additional independent people. These are not
formal GitHub approvals, external mathematical acceptance, or CI passes.

## Exact reproducibility commands

Recorded runtime: CPython 3.12.14. All new programs use the standard library.
Use a full-history checkout of the branch, with the reviewed commits available
locally. From the repository root:

```sh
python -B problems/cyclotomic-prime-arrays/code/check_energy_certificate.py --negative-controls problems/cyclotomic-prime-arrays/inputs/energy_*.json
python -B problems/cyclotomic-prime-arrays/code/general_unit_certificates.py --output /tmp/general_unit_subgroups.json
python -B problems/cyclotomic-prime-arrays/code/check_ternary_cube_obstruction.py --negative-controls --independent-search problems/cyclotomic-prime-arrays/inputs/ternary_cube3_unsat.json
python -B problems/cyclotomic-prime-arrays/code/replay_ternary_cube_tree.py --negative-controls problems/cyclotomic-prime-arrays/inputs/ternary_cube3_unsat.json
python -B problems/cyclotomic-prime-arrays/code/check_certificate.py --negative-controls problems/cyclotomic-prime-arrays/inputs/m*_square*.json problems/cyclotomic-prime-arrays/inputs/m*_cube*.json
python -B problems/cyclotomic-prime-arrays/code/tensor_rounding_check.py
python -B problems/cyclotomic-prime-arrays/code/vector_fixture.py verify problems/cyclotomic-prime-arrays/inputs/physical_*.json --negative-controls
python -B problems/cyclotomic-prime-arrays/code/local_audit.py verify problems/cyclotomic-prime-arrays/inputs/local_ledger.json --negative-controls
python -B check.py --base 59e00a03e48e71c79a5c1be2cdba66d593cf42a0
```

Use the format-specific globs above. The local ledger and physical trades are
not all-prime array certificates and are intentionally rejected by that checker.
Generator commands, seeds, all inputs and finite search budgets are in
[code/README.md](code/README.md) and the exact JSON metadata. Repeating a
finite search is optional for validation: the deterministic certificate check
does not depend on reproducing the stochastic search history.

Compare the generated unit JSON byte-for-byte with
`inputs/general_unit_subgroups.json`. The finite energy-array driver supports
only the four certified class-number-one fields c=7,9,15,16. The complete
all-field enumeration algorithm is proved in GN1, using a certified independent
unit subgroup and an exact complete coefficient scan; this small producer is
not presented as its efficient implementation. No PARI or GRH-dependent
class/unit computation is used by the retained programs.

Continuation evidence:

| Evidence | Observed result | Limit |
|---|---|---|
| Independent energy-array checker | Eight arrays, 261 required prime lines, 116 corrupted certificates rejected, 50 common arithmetic controls | Finite instances in degrees 6 and 8 |
| Independent unit subgroup certificates | Eight fields c=7,9,11,15,16,20,24,23; 30 exact norm-one units, nonzero certified log determinants | Independence is certified; index one is not asserted |
| K23 nonprincipal-prime control | Exact Gauss-sum/norm descent; the two primes above 2 are nonprincipal; 2 is irreducible and not prime | Proves 3 divides the class number, not its exact value |
| TC3 finite tree | 31 nodes, 15 branches, 16 conflicts, 220 forced assignments, depth 5; all 49 lines reconstructed | Certificate uses 47 required lines, already an unsatisfiable subset |
| Independent combinatorial checker | Eight rejected mutations and a separate 15-node exhaustive search; reviewer adds a genuine-line/nonmonochromatic control | Finite combinatorial proof supporting the uniform arithmetic reduction |
| K9 next-order repair | Exact first 64 entries through norm 307; all 76 cube lines prime | Order four only in K9; included among the eight arrays above |

The author replay of the tree also rejects its two negative controls, but
shares authorship with the generator and is not an additional independent
review. The tree's byte SHA-256 is
`dd55e8f59cf73c47afce579e413d7572d744485c06feeeaecf636efa3ab316b9`.
The new K9 cube's JSON byte SHA-256 is
`63026669c57fd3e68b59b4e1ec2dba41ae3beb59cc6975f68e1c158a93752919`;
its checker digest for normalized pool/arrangement/line data is separately
`b5e00f771055537ac309e4969f5ce407446deb811fd2a0d98acce683ea29b5da`.
These hashes use different input bytes and are intentionally distinct.

Retained quartic evidence:

| Evidence | Observed result | Limit |
|---|---|---|
| Independent full-array checker | 9 nontrivial arrays; 90 corruptions rejected; 11 common arithmetic controls | Finite instances only |
| Reviewer arithmetic cross-check | 7,203 coefficient vectors across the three fields; independent norm, boundary and prime tests agree | Finite arithmetic range |
| Tensor correction | 192 exact residual corrections, orders 3-18, seed 20261102; 4 rejected controls | Integer residual stage, not prime distribution |
| Actual four-direction cuboids | 3 exact pools of 729 entries, 16 actual pairs and 16 orientations per field; all 301 lines; 30 rejected corruptions | Physical fixtures, not all-prime arrays |
| Cumulative local ledgers | 21 prefixes, 49 residue histograms, exact aggregate totals; 5 rejected corruptions | Finite residue data |
| Order-two obstructions | 6 complete impossibility witnesses, for each field/dimension | Side two only, apart from separate general m=8 proof |
| Repository integrity | All 45 tool tests passed locally | Metadata/tool integrity, not a mathematical proof |

The tensor fixture digest is
`b27bee7d4385edaa0ea41a221bbc3b9c6bbaaa03583705d8f2a771cba09ab16f`.
The three physical files contain complete-array and all-line-sum SHA-256
bindings for every orientation. Their independent reviewer reconstructed the
48 arrays without using the shared build_array helper and checked those hashes.

The finite examples expose the intended arithmetic subtleties. K5 square4
uses 16 of 17 prime ideals through norm 61; K8 square3 uses 9 of 12 through
norm 41; K12 square3 uses 9 of 10 through norm 37. The K5 cube includes inert
prime elements, including a prime line sum of norm 81. The K12 cube has a
prime line sum `3+4*zeta_12-2*zeta_12^3 = 3+2*sqrt(3)`, of norm 9: this is
a ramified-prime associate, allowed as a target sum. It illustrates why
divisibility and large coordinates alone cannot imply compositeness. The
eventual theorem can choose unramified targets, but does not require that
every finite valid array have only unramified line sums.

## Integrity recovery and remote CI

The first local integrity attempt reported missing historical review objects
from inherited research and an empty allocation-array format in the new scope.
The latter was corrected to `ranges = []` before the scientific freeze.
Existing content-addressed objects were recovered read-only from local caches;
remote scientific commits were reconstructed with their hashes verified. The
unchanged baseline and repeated integrity checks then passed all 45 tests.
No historical review attribution, checker gate, workflow, or permission was
altered to make the check pass. In a fresh checkout, fetch an exact historical
review SHA explicitly if the checker reports it unavailable.

The observed GitHub run at the supplemental source,
[41609618661](https://github.com/Mira-Cult/math-wip/actions/runs/41609618661),
completed with conclusion **skipped**, not passed. The latest delivery's
remote observation is kept in the PR description. A successful fleet run
remains a repository integration gate; local success does not replace it.
The workflow and permission gates were not changed or bypassed.

## Next bounded action and disposition

Coordinator review for integration of this completed checkpoint, preserving
the exact scientific, fixture and review pins and satisfying the successful
fleet-run requirement. Public-note incorporation is a separate coordinator
action. No merge, branch deletion, formal approval, numerical-cutoff campaign,
or automatic continuation is performed here. Scientifically useful next
work includes effective fixed-field prime-box/target input, efficient complete
enumeration in larger class number, further finite-order obstructions, or a
geometric analysis of the separate minimum coefficient-height pool. The
original fixed-conductor existence objective is completed by CYC; these
further questions are not concealed premises of that theorem.

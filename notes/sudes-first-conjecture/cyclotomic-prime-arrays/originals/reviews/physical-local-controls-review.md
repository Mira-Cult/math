# Independent review of physical and local finite controls

Reviewer: /root/analytic. Author of the reviewed new fixture, ledger, and
finite-controls source: /root. Reviewed revision:
**e926c54566643ce57126ac9c676d836652f4fddc**.
This exact commit is available locally; the seven files below were compared
byte for byte with its contents before review was recorded.

**Outcome: no blocking correctness defect found.** The three physical
fixtures and local ledger pass exact replay at the frozen source.
This review accepts their finite claims and the side-two obstruction
argument. It does not treat a physical fixture as an all-prime-line array,
an asymptotic multiscale implementation, or evidence of prime-distribution
estimates. It is an internal nonauthor source review, not a formal GitHub
approval or kernel proof.

## Authorship and scope

The reviewer did not author vector_fixture.py, local_audit.py, their
inputs, or finite_controls.md. The reused ExactField and all_lines
dependency in check_certificate.py was authored by /root/normalization
and independently reviewed at the earlier scientific revision; its
content is unchanged here. The generator and verifier for the physical
fixture share build_array. That shared construction is disclosed, and
the reviewer independently reconstructed every vertex below without
calling build_array.

The four asymptotic scientific manuscripts remain pinned to
6f8524253c32db096e38715fd69e880e0fa85fdd. This record does not re-review
the reviewer's own analytic.md or supersede the other component reviews.

## Physical fixture source audit

For each of m=5,8,12, the verifier proves that the pool is exactly the
first 729 canonical representatives. Its complete norm-prefix list has
one certified element per distinct prime-ideal key, no ramified classes,
and cardinality equal to the independently computed total number of
unramified prime ideals through the cutoff. Sorting by exact norm and
the coefficient tuple then fixes the initial 729, including a partial
last tie. No norm-prime shortcut is used.

The retained four gap columns are exactly 2e_0,...,2e_3. Their integer
determinant is 16, so their span is exactly 2O. The verifier independently
checks the determinant, even coefficient residues, and equality of
every actual endpoint difference. Each cuboid has four pairs, and all
sixteen pairs have 32 distinct endpoints in the prescribed pool.

The four supports are disjoint. In each stage its vertex with all
bits zero is the intended body cell (j,j,j). The intersections of its
three coordinate pairs consist only of j. All coordinates are in
{0,1,2,3}, below the center 4, so no mixed-sign body diagonal meets a
support: such a diagonal would require both t and 8-t in that set.
The alternating eight-vertex signature preserves every axis line.

All sixteen choices of four stage orientations are checked as
permutations of the same entire pool, with the same unused entries as
filler. Their native body changes are the sums of the selected 2e_j.
The other three bodies and every axis line remain fixed. For every
one of the 301 signed lines, the verifier recomputes the actual sum
and its difference from baseline, and separately compares this with
the cuboid alternating-sign incidence formula. Face-line changes are
therefore included, rather than hidden behind an axis-only check.

The physical negative controls reject dependent gap columns, wrong
lattice index, wrong residue, repeated endpoints, an incomplete
four-pair cuboid, an omitted required line, an omitted orientation,
an incorrect native sum, an incomplete prime pool, and hidden unit
rescaling. These are checks of the stated finite fixture contracts.
They are not a proof that the asymptotic gap basis is 2I or that
these four cuboids constitute the entire multiscale controller.

## Local ledger and side-two obstruction

The seven prefix lengths 4,8,9,16,25,27,36 are checked for all three
fields, giving 21 exact prefixes. Every listed quotient is checked
to be an irreducible factor of the defining polynomial over its
indicated prime field. The 49 residue histograms are recomputed
from the actual canonical coefficients. The exact total and its
reduction are checked against the weighted histogram in each quotient.

At side two, every unordered pair of distinct cells is a full
signed-coordinate line: agreeing coordinates are fixed, and
disagreeing coordinates take either direction. The verifier checks
the resulting sets against all pairs, giving six square lines or
28 cube lines. A single pair of prescribed entries with nonprime
sum therefore rules out every arrangement of that finite pool.

The retained obstruction pair is indices (0,1) in all six cases.
Its sum norm is 155 in K5, 4 in K8, and 225 in K12. Each is verified
as a nonprime element, not simply rejected for failing rational-prime
norm. In particular the K8 norm-four element is 2+sqrt(2); its
principal ideal is a proper ramified prime-ideal power, and the
finite quotient test rejects it. Thus all three side-two squares
and all three side-two full cubes are impossible. These six finite
exceptions do not contradict any eventual statement.

The five ledger corruptions are rejected: changed residue count,
changed total, omitted prime class, omitted obstruction, and false
obstruction norm.

## Observed commands and results

Environment: CPython 3.12.14, standard library only. From the repository root:

    python -B problems/cyclotomic-prime-arrays/code/vector_fixture.py verify --negative-controls problems/cyclotomic-prime-arrays/inputs/physical_m5_cube9.json problems/cyclotomic-prime-arrays/inputs/physical_m8_cube9.json problems/cyclotomic-prime-arrays/inputs/physical_m12_cube9.json
    python -B problems/cyclotomic-prime-arrays/code/local_audit.py verify problems/cyclotomic-prime-arrays/inputs/local_ledger.json --negative-controls

Observed physical results:

| m | Pool entries | Norm cutoff | Required lines | Actual pairs | Orientations | Index | Rejected mutations |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 729 | 5531 | 301 | 16 | 16 | 16 | 10 |
| 8 | 729 | 5449 | 301 | 16 | 16 | 16 | 10 |
| 12 | 729 | 5653 | 301 | 16 | 16 | 16 | 10 |

Each result explicitly reports all_prime_line_claim=false.
The ledger reports 21 certified prefixes, 49 certified histograms,
six complete order-two obstructions, and five rejected mutations.

To remove reliance on the shared build_array implementation, the
reviewer also ran this independent vertex reconstruction:

    python -B - <<'PY'
    import sys, json, hashlib, itertools, pathlib
    sys.path.insert(0, 'problems/cyclotomic-prime-arrays/code')
    from check_certificate import all_lines
    for path in sorted(pathlib.Path(
            'problems/cyclotomic-prime-arrays/inputs'
            ).glob('physical_m*_cube9.json')):
        d = json.loads(path.read_text())
        n = d['side']; pool = list(map(tuple, d['pool']))
        ls = all_lines(n, 3)
        for mask in range(16):
            placed = {}
            for j, s in enumerate(d['stages']):
                assert s['gap'] == [2*int(j == k) for k in range(4)]
                for u, v, w in itertools.product((0, 1), repeat=3):
                    p = (s['axes'][0][u], s['axes'][1][v], s['axes'][2][w])
                    index = p[0]*n*n + p[1]*n + p[2]
                    assert index not in placed
                    pick = ((u+v+w) & 1) ^ ((mask >> j) & 1)
                    placed[index] = tuple(s['pairs'][2*v+w][pick])
            assert len(placed) == len(set(placed.values())) == 32
            rest = [x for x in pool if x not in set(placed.values())]
            empty = [i for i in range(n**3) if i not in placed]
            assert len(rest) == len(empty)
            placed.update(zip(empty, rest))
            a = [placed[i] for i in range(n**3)]
            assert sorted(a) == sorted(pool)
            sums = [[sum(a[i][c] for i in line) for c in range(4)]
                    for line in ls]
            for key, obj in [('array_sha256', a), ('line_sums_sha256', sums)]:
                got = hashlib.sha256(json.dumps(
                    obj, separators=(',', ':')).encode()).hexdigest()
                assert got == d['orientations'][mask][key]
    PY

All 48 full vertex reconstructions and their 301-line digest lists
matched the retained certificates. No producer arithmetic, producer
line enumeration, or shared build_array function is used by that check.

## Exact content bindings

Paths are relative to problems/cyclotomic-prime-arrays/.

| Path | SHA256 |
|---|---|
| code/vector_fixture.py | 38c096e401006779a11911dff06e9c850a4347d2450f2306b1a9f53c81bd230b |
| code/local_audit.py | 0a113baf870d8cb229cbffcdc4b5fc4478dc8a64ec7833fe05ae874ef5f3e491 |
| manuscripts/finite_controls.md | 43bacee8d506fbd577264d43708bfa629897d8b69f48ec262f308b298d80a7d0 |
| inputs/local_ledger.json | ceb8b61e3d5b5a69d6722b6084d2cd0f5f81f7357cbede4cee4b0013cd4d5dde |
| inputs/physical_m5_cube9.json | adbd7cd942620ca705babe30f822462c63bd6edd2562563f02cb7da42d3679f0 |
| inputs/physical_m8_cube9.json | 00f59b556bf7336744999fe330d4333c33d257e3aa0bd74faee8121ea031a79d |
| inputs/physical_m12_cube9.json | 67a2ee93e239c508848f246dd41dfa7fa3dc5d4c04391b394e45660973b4e787 |
